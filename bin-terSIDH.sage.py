

# This file was *autogenerated* from the file bin-terSIDH.sage
from sage.all_cmdline import *   # import sage library

_sage_const_128 = Integer(128); _sage_const_1 = Integer(1); _sage_const_192 = Integer(192); _sage_const_256 = Integer(256); _sage_const_134 = Integer(134); _sage_const_93 = Integer(93); _sage_const_162 = Integer(162); _sage_const_0 = Integer(0); _sage_const_2 = Integer(2); _sage_const_1000 = Integer(1000); _sage_const_4 = Integer(4); _sage_const_6 = Integer(6); _sage_const_3 = Integer(3); _sage_const_10 = Integer(10)
import sys
import random
import time

from isogenies import torsion_basis
from montgomery_xz import KummerLine
from montgomery_isogeny import KummerLineIsogenyComposite

proof.all(False)

lam = _sage_const_128 
ternary = True

for arg in sys.argv[_sage_const_1 :]:
    if arg.lower() in ["--192"]:
        lam = _sage_const_192 
    elif  arg.lower() in ["--256"]:
        lam = _sage_const_256 
    else:
        lam = _sage_const_128 

for arg in sys.argv[_sage_const_1 :]:
    if arg.lower() in ["--bin", "--binary"]:
        ternary = False
    else:
        ternary = True


params_binSIDH = [_sage_const_134 , _sage_const_192 , _sage_const_256 ]
params_terSIDH = [_sage_const_93 , _sage_const_128 , _sage_const_162 ]

if ternary:
    params = params_terSIDH
    sk_choices = [_sage_const_0 , _sage_const_1 , _sage_const_2 ]
else:
    params = params_binSIDH
    sk_choices = [_sage_const_1 , _sage_const_2 ]

if lam == _sage_const_128 :
    t = params[_sage_const_0 ]
elif lam == _sage_const_192 :
    t = params[_sage_const_1 ]
elif lam == _sage_const_256 :
    t = params[_sage_const_2 ]
else:
    raise Exception("The security parameter needs to be 128, 192, or 256.")




def make_prime(p):
    '''
    Given a value `p`, finds a cofactor `f`
    such that p*f - 1 is prime.
    '''
    for i in range(_sage_const_1000 ):
        if (p*i - _sage_const_1 ).is_prime():
            return p*i - _sage_const_1 , i

def compute_kernel_scalars(s, Alice=True):
    """ 
    Given a ternary secret `s`, returns scalars `B0` and `B1`
    such that the isogeny associated with `s` and orientation (P, Q)
    has kernel <[B0]*P + [B1]*Q>.
    The function also returns `order0` and `order1`, the orders
    of points [B0]*P and [B1]*Q, which is used in the isogeny computations.
    """
    B0 = _sage_const_1 
    B1 = _sage_const_1 
    order0 = _sage_const_1 
    order1 = _sage_const_1 

    t = len(s)

    if Alice:
        P = Primes()[:_sage_const_2 *t:_sage_const_2 ]
    else:
        P = Primes()[_sage_const_1 :_sage_const_2 *t:_sage_const_2 ]

    for i, p in enumerate(P):
        if Alice and i == _sage_const_0 :
            p = _sage_const_4 

        if s[i] == _sage_const_2 :
            B1 *= p
            order0 *= p
        elif s[i] == _sage_const_1 :
            B0 *= p
            order1 *= p
        else:
            B0 *= p
            B1 *= p
    
    return B0, B1, order0, order1


##### Setup ############################

A = _sage_const_2 *prod(Primes()[:_sage_const_2 *t:_sage_const_2 ]) # The 2* ensures that p \equiv 3 mod 4
B = prod(Primes()[_sage_const_1 :_sage_const_2 *t:_sage_const_2 ])

p, f = make_prime(A*B)


FF = GF(p)['x']; (x,) = FF._first_ngens(1)
F = GF(p**_sage_const_2 , modulus=x**_sage_const_2 +_sage_const_1 , names=('i',)); (i,) = F._first_ngens(1)
E0 = EllipticCurve(F, [_sage_const_0 , _sage_const_6 , _sage_const_0 , _sage_const_1 , _sage_const_0 ])
E0.set_order((p+_sage_const_1 )**_sage_const_2 ) 

PA, QA = torsion_basis(E0, A)
PB, QB = torsion_basis(E0, B)

## Ensures that 2*PA != (0,0) and
## 2^*QA != (0,0), which causes problems
if _sage_const_2  * PA == E0(_sage_const_0 , _sage_const_0 ):
    PA = PA + QA
elif _sage_const_2  * (PA+QA) == E0(_sage_const_0 , _sage_const_0 ):
    QA = PA + QA 

if _sage_const_2  * PA == E0(_sage_const_0 , _sage_const_0 ):
    PA = PA + QA
elif _sage_const_2  * (PA+QA) == E0(_sage_const_0 , _sage_const_0 ):
    QA = PA + QA 

assert _sage_const_2  * PA != E0(_sage_const_0 , _sage_const_0 ) and _sage_const_2  * (PA+QA) != E0(_sage_const_0 , _sage_const_0 )

PQA = PA - QA
PQB = PB - QB

E0 = KummerLine(E0)
xPA, xQA, xPQA = E0(PA[_sage_const_0 ]), E0(QA[_sage_const_0 ]), E0(PQA[_sage_const_0 ])
xPB, xQB, xPQB = E0(PB[_sage_const_0 ]), E0(QB[_sage_const_0 ]), E0(PQB[_sage_const_0 ])



def keygenA():
    sk = random.choices(sk_choices, k=t)
    B0, B1, order0, order1 = compute_kernel_scalars(sk, Alice=True)
    sk = (B0, B1, order0, order1)
    
    xK0 = xPA * B0
    xK1 = xQA * B1

    phia0 = KummerLineIsogenyComposite(E0, xK0, order0)
    xK1 = phia0(xK1)
    xPB0 = phia0(xPB)
    xQB0 = phia0(xQB)
    xPQB0 = phia0(xPQB)

    EA0 = phia0.codomain()
    phiA1 = KummerLineIsogenyComposite(EA0, xK1, order1)

    pk = phiA1.codomain(), phiA1(xPB0), phiA1(xQB0), phiA1(xPQB0)

    return sk, pk


def keygenB():
    sk = random.choices(sk_choices, k=t)
    B0, B1, order0, order1 = compute_kernel_scalars(sk, Alice=False)
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
    (EA, RB, SB, RSB) = pkB
    (B0, B1, order0, order1) = skA
    
    xK0 = RB * B0
    xK1 = SB * B1

    phiBdash0 = KummerLineIsogenyComposite(EA, xK0, order0)
    xK1 = phiBdash0(xK1)

    EAB0 = phiBdash0.codomain()
    phiBdash1 = KummerLineIsogenyComposite(EAB0, xK1, order1)

    EAB = phiBdash1.codomain().curve()
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


N = _sage_const_1 
tt = [_sage_const_0 , _sage_const_0 , _sage_const_0 , _sage_const_0 ]

for _ in range(N):
    t0 = time.time_ns()
    skA, pkA = keygenA()
    tt[_sage_const_0 ] += time.time_ns() - t0

    t0 = time.time_ns()
    skB, pkB = keygenB()
    tt[_sage_const_1 ] += time.time_ns() - t0

    t0 = time.time_ns()
    ssA = sharedA(skA, pkB)
    tt[_sage_const_2 ] += time.time_ns() - t0

    t0 = time.time_ns()
    ssB = sharedB(skB, pkA)
    tt[_sage_const_3 ] += time.time_ns() - t0

    assert ssA == ssB

tt = [float(t) / N / _sage_const_10 **_sage_const_6  for t in tt]

print(f"KeyGen_A took {(tt[_sage_const_0 ]):.1f} ms")
print(f"KeyGen_B took {(tt[_sage_const_1 ]):.1f} ms")
print(f"shared_A took {(tt[_sage_const_2 ]):.1f} ms")
print(f"shared_B took {(tt[_sage_const_3 ]):.1f} ms")
