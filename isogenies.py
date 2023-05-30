"""
TODO: better doc string

Helper functions for the isogeny computations in FESTA
"""

# Sage Imports
from sage.all import (
    ZZ,
    cached_function,
    EllipticCurveIsogeny,
    factor,
    set_random_seed,
    matrix,
    identity_matrix,
    Zmod,
    gcd,
    inverse_mod,
    CRT
)
from sage.structure.element import RingElement
from sage.schemes.elliptic_curves.ell_point import EllipticCurvePoint_finite_field
from sage.schemes.elliptic_curves.hom_velusqrt import EllipticCurveHom_velusqrt
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite

# Local imports
from utilities import has_order_D
from pari_interface import discrete_log_pari

# =========================================== #
# Compute points of order D and Torsion Bases #
# =========================================== #

def generate_random_point(E, seed=None):
    """
    E0.random_point() returns either P
    or -P with equal probability.

    We always select the element with
    smaller y-coordinate to make this
    deterministic.
    """
    # Allow a setting of the seed to
    # ensure the same point is always returned
    if seed is not None:
        set_random_seed(seed)

    P = E.random_element()
    return min(P, -P)


def generate_point_order_D(E, D):
    """
    Input:  An elliptic curve E / Fp2
            An integer D dividing (p +1)
    Output: A point P of order D.
    """
    p = E.base().characteristic()
    n = (p + 1) // D
    for _ in range(1000):
        P = n * generate_random_point(E)

        # Case when we randomly picked
        # a point in the n-torsion
        if P.is_zero():
            continue

        # Check that P has order exactly D
        if has_order_D(P, D):
            P._order = ZZ(D)
            return P

    raise ValueError(f"Never found a point of order D...")


def generate_linearly_independent_point(E, P, D, canonical=False):
    """
    Input:  An elliptic curve E / Fp2
            A point P ∈ E[D]
            An integer D dividing (p +1)
    Output: A point Q such that E[D] = <P, Q>
    """
    # This ensures all random points are deterministically
    # generated
    if canonical:
        set_random_seed(0)

    for _ in range(2000):
        # Generate a random point of order D
        Q = generate_point_order_D(E, D)

        # Make sure the point is linearly independent
        pair = P.weil_pairing(Q, D, algorithm="pari")
        if has_order_D(pair, D, multiplicative=True):
            Q._order = ZZ(D)
            return Q

    raise ValueError(f"Never found a linearly independent point...")


def torsion_basis(E, D, canonical=False):
    """
    Generate basis of E(Fp^4)[D] of supersingular curve

    Optional   canonical: bool
               Makes torsion generation deterministic.
    """
    p = E.base().characteristic()

    # Ensure D divides the curve's order
    if (p + 1) % D != 0:
        print(f"{factor(D) = }")
        print(f"{factor(p+1) = }")
        raise ValueError(f"D must divide the point's order")

    # This ensures all random points are deterministically
    # generated
    if canonical:
        set_random_seed(0)

    P = generate_point_order_D(E, D)
    Q = generate_linearly_independent_point(E, P, D)

    return P, Q

# ================================== #
# Compute composite degree isogenies #
# ================================== #

def EllipticCurveIsogenyFactored(E, P, order=None, velu_bound=800):
    """
    Works similarly to EllipticCurveHom_composite
    but with two main additions:

    Introduces a sparse strategy for prime power
    isogenies, taken from
    https://trac.sagemath.org/ticket/34239
    This should be default soon (9.8 maybe)

    For primes l > 400, we use velusqrt as
    the algorithm. This bound was found by testing
    in tests/test_isogenies.sage

    Additionally, we allow `order` as an optional parameter
    and `velu_bound` controls when sqrtvelu kicks in
    """

    def EllipticCurveHom_velusqrt_setorder(P):
        """
        To speed things up, we manually set the order
        assuming all curves have order (p +1)^2

        I think this is fixed for 9.8, but not everyone
        will be running the latest SageMath version.
        """
        E = P.curve()
        p = E.base().characteristic()
        E._order = ZZ((p + 1)**2)
        return EllipticCurveHom_velusqrt(E, P)

    def evaluate_factored_isogeny(phi_list, P):
        """
        Given a list of isogenies, evaluates the
        point for each isogeny in the list
        """
        for phi in phi_list:
            P = phi(P)
        return P

    def sparse_isogeny_prime_power(P, l, e, split=0.8, velu_bound=2000):
        """
        Compute chain of isogenies quotienting
        out a point P of order l**e
        https://trac.sagemath.org/ticket/34239
        """
        if l > velu_bound:
            isogeny_algorithm = lambda Q, l: EllipticCurveHom_velusqrt_setorder(Q)
        else:
            isogeny_algorithm = lambda Q, l: EllipticCurveIsogeny(
                Q.curve(), Q, degree=l, check=False
            )

        def recursive_sparse_isogeny(Q, k):
            assert k
            if k == 1:  # base case
                return [isogeny_algorithm(Q, l)]

            k1 = int(k * split + 0.5)
            k1 = max(1, min(k - 1, k1))  # clamp to [1, k-1]

            Q1 = l**k1 * Q
            L = recursive_sparse_isogeny(Q1, k - k1)

            Q2 = evaluate_factored_isogeny(L, Q)
            R = recursive_sparse_isogeny(Q2, k1)

            return L + R

        return recursive_sparse_isogeny(P, e)

    # Ensure P is a point on E
    if P.curve() != E:
        raise ValueError(f"The supplied kernel must be a point on the curve E")

    if order:
        P._order = ZZ(order)
    cofactor = P.order()

    # Deal with isomorphisms
    if cofactor == 1:
        return EllipticCurveIsogeny(P.curve(), P)

    ϕ_list = []
    for l, e in cofactor.factor():
        # Compute point Q of order l^e
        D = ZZ(l**e)
        cofactor //= D
        Q = cofactor * P

        # Manually setting the order means 
        # Sage won't try and do it for each
        # l-isogeny in the iteration
        Q._order = D

        # Use Q as kernel of degree l^e isogeny
        ψ_list = sparse_isogeny_prime_power(Q, l, e, velu_bound=velu_bound)

        # Map P through chain length e of l-isogenies
        P = evaluate_factored_isogeny(ψ_list, P)
        ϕ_list += ψ_list

    return EllipticCurveHom_composite.from_factors(ϕ_list)

# ===================================== #
#  Fast computation of random isogeny   #
# ===================================== #

def random_isogeny(E, D, independent_from=None, return_dual=False):
    """
    TODO
    """
    # TODO: is this ever used?
    if isinstance(independent_from, EllipticCurvePoint_finite_field):
        K = generate_linearly_independent_point(E, independent_from, D)
    else:
        K = generate_point_order_D(E, D)

    phi = EllipticCurveIsogenyFactored(E, K, order=D)
    codomain = phi.codomain()

    p = E.base_field().characteristic()
    codomain.set_order((p+1)**2, num_checks=0)
    
    return phi, codomain

def eval_random_isogeny(E, D, points):
    """
    TODO, it supports irrational isogenies
    """
    deg = 1
    dualK = None
    phi_list = []

    p = E.base_field().characteristic()
    while deg != D:
        next_deg = gcd(D // deg, p+1)
        if dualK == None:
            phi, E = random_isogeny(E, next_deg)
        else:
            # FIXME: this should ensure that isogenies don't backtrack
            phi, E = random_isogeny(E, next_deg)

        points = [phi(X) for X in points]

        deg *= next_deg

        phi_list.append(phi)
    
    phi = EllipticCurveHom_composite.from_factors(phi_list)
    return E, phi, points

def isogeny_from_scalar(E, D, m, basis=None):
    """
    TODO
    """
    # Allow a precomputed basis
    if not basis:
        P, Q = torsion_basis(E, D, canonical=True)
    else:
        P, Q = basis

    # Allow either an integer or tuple of integers
    if isinstance(m, RingElement) or isinstance(m, int):
        K = P + m*Q
    else:
        assert len(m) == 2
        K = m[0]*P + m[1]*Q    

    # Compute isogeny from K
    phi = EllipticCurveIsogenyFactored(E, K, order=D)
    codomain = phi.codomain()

    # Help Sage be fast by setting the order manually
    p = E.base_field().characteristic()
    codomain.set_order((p+1)**2, num_checks=0)

    return phi, codomain

# ===================================== #
#  Fast DLP solving using Weil pairing  #
# ===================================== #

def DLP(P, G, D):
    """
    Given two elliptic curve points G, P
    such that P = [x]G find x by using
    Weil pairings to allow the dlog to
    be performed over Fp2

    This can be between 30-100% faster than
    calling P.discrete_log(Q).

    TODO:
    Only supported for prime powers.
    """
    # Find a linearly independent point for
    # Weil pairing
    Q = generate_linearly_independent_point(G.curve(), G, D)

    # Map from elliptic curves to Fp2
    g = G.weil_pairing(Q, D, algorithm="pari")
    p = P.weil_pairing(Q, D, algorithm="pari")

    return discrete_log_pari(p, g, D)


def BiDLP(R, P, Q, D):
    """
    Given a basis P,Q of E[D] finds
    a,b such that R = [a]P + [b]Q.

    Uses the fact that 
        e([a]P + [b]Q, [c]P + [d]Q) = e(P,Q)^(ad-bc)
    """
    # e(P,Q)
    pair_PQ = P.weil_pairing(Q, D, algorithm="pari")

    # Write R = aP + bQ for unknown a,b
    # e(R, Q) = e(P, Q)^a
    pair_a = R.weil_pairing(Q, D, algorithm="pari")

    # e(R,-P) = e(P, Q)^b
    pair_b = R.weil_pairing(-P, D, algorithm="pari")

    # Now solve the dlog on Fq
    a = discrete_log_pari(pair_a, pair_PQ, D)
    b = discrete_log_pari(pair_b, pair_PQ, D)

    return a, b

# =============================================== #
#   Compute canonical representation for kernel   #
# =============================================== #

def compute_canonical_kernel(imP, imQ, D):
    """
    """
    E = imP.curve()
    assert E == imQ.curve()

    P, Q = torsion_basis(E, D, canonical=True)

    a1, b1 = BiDLP(imP, P, Q, D)
    a2, b2 = BiDLP(imQ, P, Q, D)

    t1_list = []
    t2_list = []
    di_list = []

    # CRT recovery of t1, t2
    for pi, ei in D.factor():
        di = pi**ei
        di_list.append(di)

        if a1 % pi == 0:
            t1, t2 = 0, inverse_mod(a2, di)
        else:
            t1, t2 = inverse_mod(a1, di), 0

        t1_list.append(t1)
        t2_list.append(t2)

    t1 = CRT(t1_list, di_list)
    t2 = CRT(t2_list, di_list)

    return (t1*b1 + t2*b2) % D

# ============================================= #
#         Map from Mont. to Weierstrass         #
# ============================================= #

def montgomery_to_weierstrass_model(E, points):
    """
    """
    Ew = E.short_weierstrass_model()
    iso = E.isomorphism_to(Ew)
    images = (iso(P) for P in points)
    return Ew, images

# =========================== #
#         Dead Code ?         #
# =========================== #

def canonical_repr(a, b, D):
    """
    Given a,b such that a kernel
    K = [a]P + [b]Q find the non-zero
    integer of the canonical basis
    """
    aD = gcd(a, D)
    bD = gcd(b, D)

    if aD == 1:
        return b/a % D
    elif bD == 1:
        return a/b % D
    else:
        for i in range(D):
            if gcd(a + b*i, D) == 1:
                aa = a + b*i
                break
        
        return b/aa % D

def canonical_mask_from_kernel(K, D):
    """
    TODO
    """
    E = K.curve()
    P1, Q1 = torsion_basis(E, D, canonical=True)
    a, b = BiDLP(K, P1, Q1, D)
    mask = canonical_repr(a, b, D)
    return mask



# =========================== #
#         Dead Code           #
# =========================== #

# ===================================== #
# Fast computation of dual given kernel #
# ===================================== #

def dual_isogeny_and_kernel(ϕ, R, order=None):
    """
    Compute the dual isogeny given an
    isogeny and its kernel.
    Inspired by ia.cr/2019/499

    Input: An isogeny ϕ : E -> E / <R> of degree D
           The generator R of the ker(ϕ)

    Output: The dual of ϕ and its kernel
    """
    E1 = ϕ.domain()
    E2 = ϕ.codomain()

    if not order:
        D = ZZ(ϕ.degree())
    else:
        D = ZZ(order)

    S = generate_linearly_independent_point(E1, R, D)

    ker_phi_dual = ϕ(S)
    ϕ_dual = EllipticCurveIsogenyFactored(E2, ker_phi_dual, order=D)
    Eϕ = ϕ_dual.codomain()

    # Correcting isomorphism
    if Eϕ != E1:
        iso = Eϕ.isomorphism_to(E1)
        ϕ_dual = iso * ϕ_dual

    return ϕ_dual, ker_phi_dual


def dual_isogeny(ϕ, R, order=None):
    """
    Wrapper function for when we only want the
    dual isogeny but not the dual isogeny's
    kernel
    """
    ϕ_dual, _ = dual_isogeny_and_kernel(ϕ, R, order=order)
    return ϕ_dual

# ===================================== #
#   Compute a kernel from an isogeny    #
# ===================================== #

def kernel_from_isogeny_prime_power(ϕ):
    """
    Given a prime-power degree isogeny ϕ
    computes a generator of its kernel
    """
    E = ϕ.domain()
    D = ϕ.degree()

    # Deal with isomorphisms
    if D == 1:
        return E(0)

    # Generate a torsion basis of E[D]
    P, Q = torsion_basis(E, D)

    # Compute the image of P,Q
    imP, imQ = ϕ(P), ϕ(Q)

    # Ensure we can use Q as a base
    # for the discrete log
    # TODO:
    # Here we assume D is a prime power,
    # this could fail for the general case
    if not has_order_D(imQ, D):
        P, Q = Q, P
        imP, imQ = imQ, imP

    # Solve the discrete log such that
    # imP = -[x]imQ. `DLP` uses Weil 
    # pairing to shift the dlog to Fp2.
    x = DLP(-imP, imQ, D)

    return P + x * Q

# ========================================== #
#   Compute kernel generator from a basis    #
# ========================================== #

def derive_cyclic_generator(P, Q, D):
    """
    Given generators <P,Q> of a cyclic group
    of order D, find K such that G = <K>
    
    Heuristically, it seems easy to randomly
    find a K this way, and is about 10x faster
    than the deterministic method as we do not
    need to compute the order of P or Q.
    """
    if has_order_D(P, D):
        return P

    if has_order_D(Q, D):
        return Q

    K = P + Q
    for _ in range(1000):
        if has_order_D(K, D):
            return K
        K += Q
    raise ValueError(f"Never found a cyclic generator!")


def dual_secret_kernel(P_Phi, Q_Phi, Pd1, Qd1, d1):
    """
    TODO
    """
    # Find the kernel of the dual
    C = P_Phi.curve()
    p = C.base_field().characteristic()
    C.set_order((p + 1)**2, num_checks=0)

    # Compute torsion basis C[d1]
    R, S = torsion_basis(C, d1)

    # Write P_Phi and Q_Phi as
    # P_Phi = [x1] R + [y1] S
    # Q_Phi = [x2] R + [y2] S
    x1, y1 = BiDLP(P_Phi, R, S, d1)
    x2, y2 = BiDLP(Q_Phi, R, S, d1)

    # matrix of α on d1-torsion w.r.t. basis (R, S)
    mat = matrix([(x1, y1), (x2, y2)])

    # Thanks to Lorenz Panny for the following Sage
    # Hack to find kernel of a matrix over ZZ/DZZ
    # See: https://trac.sagemath.org/ticket/34862
    ker = mat.stack(d1*identity_matrix(2)).left_kernel().basis_matrix()[:,:2].change_ring(Zmod(d1))

    # Find kernel generators, as d1 is composite, neither
    # may have full order
    K1, K2 = [u*Pd1 + v*Qd1 for u,v in ker]
    return derive_cyclic_generator(K1, K2, d1)