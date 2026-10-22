# SZ: first contact for the actual nonlinear prime moment

- **ID:** SZ-PRIME-MOMENT-FIRST-CONTACT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1:sz-nonlinear-prime-forcing-sign; `CCMPrimeMomentFirstContact`.
- **Statement:** For every real A, a strict potential descent below A-1 forces a later actual nonlinear prime discrepancy below A; any fixed lower forcing bound therefore enforces an exact tail minimum principle.

## Actual source and theorem

Write M_n=primeMassHalf(n), m_n=1+M_n/2, and w_n=Lambda(n)/sqrt(n).
All prime powers are retained. Define

    U_n=sqrt(n)*(M_n+2)-n-psi(n)-1,
    D_n=M_n+M_n^2/4-psi(n)=m_n^2-psi(n)-1.

The following statements are proved without an RH assumption:

1. D_n=U_n+(m_n-sqrt(n))^2.
2. U_(n+1)-U_n=(sqrt(n+1)-sqrt(n))*(2*m_n-sqrt(n+1)-sqrt(n)).
3. If U_(n+1) is no larger than either neighbor, n+1 is a prime power and
   D_(n+1)<U_(n+1)+w_(n+1)^2/4.
4. If U_(n+1)<U_n and U_(n+1)<-1, some k>=n+1 has D_k<0.
5. If D_k>=0 for every k>=N, then U_k>=min(U_N,-1) for every k>=N.

These are source-specific contact and propagation laws. They do not assert
the descent premises hold cofinally, eventual negative forcing, or RH.

## Dependency-closed paper proof

Finite summation gives M_(n+1)=M_n+w_(n+1) and
psi(n+1)=psi(n)+sqrt(n+1)*w_(n+1). Their jumps cancel in U.
The square identity and increment formula follow by expansion.

At a valley, the positive square-root increments force

    2*m_n <= sqrt(n+1)+sqrt(n),
    sqrt(n+2)+sqrt(n+1) <= 2*m_(n+1).

These inequalities imply 0<m_(n+1)-sqrt(n+1)<w_(n+1)/2.
Thus the entry weight is positive, its index is a prime power, and the
valley square is smaller than w_(n+1)^2/4.

Suppose a descent below -1 has no later negative D. A subsequent turn
upward would be a valley below -1. The source bound 0<=w_n<=2 and the
valley inequality contradict D>=0 there. Induction therefore forces U
to descend forever below -1. From D=U+y^2>=0 obtain |y|>1. The strict
descent formula and sqrt(n+1)-sqrt(n)<=1 imply y<1/2, hence y<-1.

At the next entry,

    D_(j+1)-D_j=w_(j+1)*(m_j-sqrt(j+1))+w_(j+1)^2/4
                <= -w_(j+1)/2.

Consequently D_j+M_j/2 is nonincreasing on this tail. D_j>=0 would bound
M_j, contradicting the unconditional Chebyshev lower bound M_j->infinity.
This proves statement4. For statement5, the first crossing below
min(U_N,-1) is a deep descent, contradicting statement4.

## Audit

- Leaf: `formal/GaloisForLFunctions/RHTower/CCM/CCMPrimeMomentFirstContact.lean`.
- Final foreground audit57414: `lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMPrimeMomentFirstContact.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCM/CCMPrimeMomentFirstContact.olean`, exit0, no diagnostics.
- Axiom audit24541: all9 public declarations; only `propext`, `Classical.choice`, `Quot.sound`; exit0.
- One import in `RHTower.lean`; no umbrella build. No custom axioms,
  admissions, numerical experiments, or heartbeat changes.
- Global lint89088 exited1 on16 other modules unreachable from their
  umbrellas; no error named this leaf. Global lint is not claimed green.
- Search1221540,1221567,1221621 and1221798 were partial/source-only or
  pending compiler coverage; source candidates were inspected directly.
  No search miss is used as an absence or novelty claim.

## Frontier effect

The positive square can be controlled at actual prime-power contact, and
a permanently descending potential below the barrier cannot coexist
with nonnegative forcing. The formerly missing potential-escape producer is now closed in
P3:sz-prime-moment-potential-escape. Even unbounded negative D does not
establish eventual negative forcing or the full canonical-head
Gamma--prime--polar sign.

## Arbitrary-level strengthening (2026-10-04)

`ccmPrimeMoment_forcing_lt_of_deep_descent A n` replaces the zero-level
conclusion by D_k<A and its potential barrier by A-1. The source proof
is unchanged except for this translation: D>=A and U<A-1 still force
the displacement square above1; the permanently descending tail still
makes D+M/2 nonincreasing. Divergence of M contradicts any fixed lower
bound A on D. `ccmPrimeMomentPotential_lower_of_forcing_lower` therefore
proves U_k>=min(U_N,A-1) on any tail with D_k>=A. The original zero-level
statements remain as specializations.

Scratch89827 checked both generalized statements with only the standard
axioms. Final leaf audit37824 exited0 with no diagnostics. The subsequent
full24-declaration audit covers this leaf and both potential-escape leaves;
its result is recorded on P3:sz-prime-moment-potential-escape.
