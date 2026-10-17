# Exact energy continuity and concentration at the singular origin

Let f_n belong to the certified actual-source class S_K, K>=0. Thus f_n is real,
compactly supported, C², has positive mass R_n=h_n(0), satisfies every grid zero
h_n(log k)=0 for k>=2, and has normalized energy E_n<=K. Suppose H_n=h_n/R_n
converges uniformly on the real line to H. Set

    w(x)=exp(x/2)/sinh x,
    q_G(x)=(1-G(x))w(x),
    C_G(a)=integral_(0,a] q_G,
    T_G(a)=integral_(a,infinity) q_G,
    E_H=integral_(0,infinity) q_H.

Package 8 proves continuity of H, |H|<=1, and actual integrability and nonnegativity
of q_H on (0,infinity), with E_H<=K. For every n, q_Hn is also nonnegative and
integrable, and its integral equals E_n. These are derived source facts, not new
analytic assumptions. All assertions below concern this domain.

## Tail stability [PAPER PROOF]

For a>0 and any two such kernels G,H with |G(x)-H(x)|<=epsilon for x>a,

    |T_G(a)-T_H(a)| <= epsilon integral_(a,infinity) w.

Indeed q_G-q_H=(H-G)w. The weight is positive on this interval and integrable
there by the certified exact tail formula. Integrate the absolute-value bound.
Consequently T_Hn(a) tends to T_H(a) for every a>0. In fact pointwise convergence
already suffices: |q_Hn|<=2w on (a,infinity), so dominated convergence applies.
Thus energy loss cannot occur on any interval bounded away from zero, including
the entire infinite tail. No polar moment bound is being asserted.

## Shrinking core and monotonicity [PAPER PROOF]

For every kernel G here, C_G(a)>=0, C_G(a)<=C_G(b) when a<=b, and C_G(a) tends
to zero as a decreases to zero. To prove the last assertion, use radii 1/(m+1).
The sets (0,1/(m+1)] decrease to the empty set. Their indicators times q_G
converge pointwise to zero and are dominated by the integrable q_G on (0,1].
Dominated convergence gives the limit along these radii. Monotonicity then gives
arbitrarily small core energy at a positive radius, and the full one-sided limit.
For any finite family of kernels, choose one such radius for each and take the
minimum. This gives one positive radius controlling the whole finite family.

The exact disjoint splitting identity is

    E_G = C_G(a) + T_G(a),   a>0.

It follows by additivity of integrals of integrable functions over (0,a] and
(a,infinity). The endpoint convention avoids overlap and loses no contribution.

## Exact continuity criterion [PAPER PROOF]

The following are equivalent:

1. E_n tends to E_H.
2. For every epsilon>0 there is a>0 such that C_Hn(a)<epsilon for every n.
3. For every epsilon>0 there are a>0 and N such that C_Hn(a)<epsilon for n>=N.

For 1=>2, fix epsilon>0. Choose b>0 with C_H(b)<epsilon/3. Tail convergence and
the splitting identity give C_Hn(b)=E_n-T_Hn(b) tending to C_H(b). Hence all
n>=N have C_Hn(b)<2epsilon/3. Control the finite prefix n<N at epsilon by a
positive radius c, using the finite-family fact above. At a=min(b,c), positivity
and core monotonicity preserve both bounds. Thus every n has C_Hn(a)<epsilon.
Clearly 2=>3.

For 3=>1, fix epsilon>0 and choose a>0 and N controlling eventual source core
energies by epsilon/3. Decrease a if necessary so C_H(a)<epsilon/3; monotonicity
preserves the source bounds. Tail convergence supplies N' with
|T_Hn(a)-T_H(a)|<epsilon/3 for n>=N'. The exact split and nonnegativity imply

    |E_n-E_H| <= C_Hn(a)+C_H(a)+|T_Hn(a)-T_H(a)| < epsilon

for n>=max(N,N'). This proves the criterion without assuming uniform
integrability as an interface. It is a necessary and sufficient property of
actual source families, with its analytic prerequisites already derived.

## Complete localization of a convergent energy defect [PAPER PROOF]

Suppose additionally E_n tends to L. Then L>=E_H by Fatou, and for every a>0,

    C_Hn(a) tends to (L-E_H)+C_H(a).

Subtract the already convergent tail from E_n and use the limiting kernel's split:
L-T_H(a)=L-E_H+C_H(a). The defect D=L-E_H is nonnegative. Sending a down to zero
in this expression gives D. Thus every fixed origin interval retains the entire
defect, while every tail away from zero has none. D=0 exactly in the continuity
criterion above. This statement classifies the location and size of any defect;
it does not assert existence of a strict positive defect.

Every bounded-energy actual-source sequence admits this complete description along
a subsequence. First extract a globally uniform correlation subsequence by package 8.
Its normalized energies lie in the compact real interval [0,K]; extract a further
subsequence along which they converge to L. Strictly increasing subsequence maps
preserve the first uniform limit. Apply the defect formula above to the resulting
actual-source sequence. This proves existence of H, L and D>=0 together, rather
than postulating an energy-convergence interface.

## Significance and boundary

The compact correlation relaxation from package 8 now has an exact test for when
its singular energy is continuous. Its sole possible failure mechanism is
concentration at zero; neither large physical distance nor any positive lag can
carry a lost energy contribution. Dominated convergence and absolute continuity
of integrals are standard tools reused here. The connected contribution is their
complete application to the actual infinite-grid source class and the resulting
defect classification. Strict-loss source construction remains separate work.

## Formal status

Dependency-closed paper proof complete. Lean formalization in progress; no package
count increment until direct leaf and full endpoint audits pass.
