import random
import time

from isogenies import torsion_basis
from montgomery_xz import KummerLine
from montgomery_isogeny import KummerLineIsogenyComposite

proof.all(False)

lam = 128
ternary = True

for arg in sys.argv[1:]:
    if arg.lower() in ["--192"]:
        lam = 192
    elif  arg.lower() in ["--256"]:
        lam = 256
    else:
        lam = 128


for arg in sys.argv[1:]:
    if arg.lower() in ["--bin", "--binary"]:
        ternary = False
    else:
        ternary = True

params_binSIDH = [203, 296, 387]
params_terSIDH = [156, 226, 293]

if ternary:
    params = params_terSIDH
    sk_choices = [0, 1, 2]
else:
    params = params_binSIDH
    sk_choices = [1, 2]

if lam == 128:
    t = params[0]
elif lam == 192:
    t = params[1]
elif lam == 256:
    t = params[2]
else:
    raise Exception("The security parameter needs to be 128, 192, or 256.")




def make_prime(p):
    '''
    Given a value `p`, finds a cofactor `f`
    such that p*f - 1 is prime.
    '''
    for i in range(1000):
        if (p*i - 1).is_prime():
            return p*i - 1, i

def compute_kernel_scalars(s):
    """ 
    Given a ternary secret `s`, returns scalars `B0` and `B1`
    such that the isogeny associated with `s` and orientation (P, Q)
    has kernel <[B0]*P + [B1]*Q>.
    The function also returns `order0` and `order1`, the orders
    of points [B0]*P and [B1]*Q, which is used in the isogeny computations.
    """
    B0 = 1
    B1 = 1
    order0 = 1
    order1 = 1

    t = len(s)

    for i, p in enumerate(Primes()[1:t+1]):
        if s[i] == 1:
            B1 *= p
            order0 *= p
        elif s[i] == 2:
            B0 *= p
            order1 *= p
        else:
            B0 *= p
            B1 *= p
    
    return B0, B1, order0, order1




##### Setup ############################
A = 2^(2*lam)
B = prod(Primes()[1:t+1])

p, f = make_prime(A*B)

FF.<x> = GF(p)[]
F.<i> = GF(p^2, modulus=x^2+1) 
E0 = EllipticCurve(F, [0, 6, 0, 1, 0])
E0.set_order((p+1)**2) 

PA, QA = torsion_basis(E0, A)
PB, QB = torsion_basis(E0, B)


## Ensures that 2^(n-1)*PA != (0,0) and
## 2^(n-1)*QA != (0,0), which causes problems
if A//2 * PA == E0(0, 0):
    PA = PA + QA
elif A//2 * (PA+QA) == E0(0, 0):
    QA = PA + QA 

if A//2 * PA == E0(0, 0):
    PA = PA + QA
elif A//2 * (PA+QA) == E0(0, 0):
    QA = PA + QA 

assert A//2 * PA != E0(0, 0) and A//2 * (PA+QA) != E0(0, 0)

PQA = PA - QA
PQB = PB - QB

E0 = KummerLine(E0)
xPA, xQA, xPQA = E0(PA[0]), E0(QA[0]), E0(PQA[0])
xPB, xQB, xPQB = E0(PB[0]), E0(QB[0]), E0(PQB[0])


def keygenA():
    skA = random.randint(0, A - 1)

    xK = xQA.ladder_3_pt(xPA, xPQA, skA)

    phiA = KummerLineIsogenyComposite(E0, xK, A)
    EA = phiA.codomain()

    return skA, (EA, phiA(xPB), phiA(xQB), phiA(xPQB))

def keygenB():
    sk = random.choices(sk_choices, k=t)
    B0, B1, order0, order1 = compute_kernel_scalars(sk)
    sk = (B0, B1, order0, order1)
    
    xK0 = xPB * B0
    xK1 = xQB * B1

    phiB0 = KummerLineIsogenyComposite(E0, xK0, order0)
    xK1 = phiB0(xK1)
    xPA0 = phiB0(xPA)
    xQA0 = phiB0(xQA)
    xPQA0 = phiB0(xPQA)

    EA0 = phiB0.codomain()
    phiB1 = KummerLineIsogenyComposite(EA0, xK1, order1)

    pk = phiB1.codomain(), phiB1(xPA0), phiB1(xQA0), phiB1(xPQA0)

    return sk, pk

def sharedA(skA, pkB):
    EB, RA, SA, RSA = pkB
    xK = SA.ladder_3_pt(RA, RSA, skA)

    phiAdash = KummerLineIsogenyComposite(EB, xK, A)
    
    EAB = phiAdash.codomain().curve()
    return EAB.j_invariant()

def sharedB(skB, pkA):
    (EA, RB, SB, RSB) = pkA
    (B0, B1, order0, order1) = skB
    
    xK0 = RB * B0
    xK1 = SB * B1

    phiBdash0 = KummerLineIsogenyComposite(EA, xK0, order0)
    xK1 = phiBdash0(xK1)

    EAB0 = phiBdash0.codomain()
    phiBdash1 = KummerLineIsogenyComposite(EAB0, xK1, order1)

    EAB = phiBdash1.codomain().curve()
    return EAB.j_invariant()


N = 1
tt = [0, 0, 0, 0]

for _ in range(N):
    t0 = time.time_ns()
    skA, pkA = keygenA()
    tt[0] += time.time_ns() - t0

    t0 = time.time_ns()
    skB, pkB = keygenB()
    tt[1] += time.time_ns() - t0

    t0 = time.time_ns()
    ssA = sharedA(skA, pkB)
    tt[2] += time.time_ns() - t0

    t0 = time.time_ns()
    ssB = sharedB(skB, pkA)
    tt[3] += time.time_ns() - t0

    assert ssA == ssB

tt = [float(t) / N / 10^6 for t in tt]

print(f"KeyGen_A took {(tt[0]):.1f} ms")
print(f"KeyGen_B took {(tt[1]):.1f} ms")
print(f"shared_A took {(tt[2]):.1f} ms")
print(f"shared_B took {(tt[3]):.1f} ms")