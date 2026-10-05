# BAG complete critical Mellin deformation

Continuation01an. This card proves the exact one-balanced deformation and
its sharp vertical norm bound. It does not claim the growing two-variable
limit or the physical signed cubic saving.

Write A=product_p(1-1/p), w_p=log(p)/p, b_p=log(p)/(p-1),
R_r=sum_(p!=r)w_p, and a_p(s)=p^(1-s). For every finite prime set P and
Re(s)>0, the actual weighted source satisfies

    F_P(s,1) = -A sum_r [b_r/a_r(s)] R_r sum_(q!=r) w_q a_q(s).

Both actual label exclusions remain. In particular, p=q is allowed; its
local response is accounted for exactly, not discarded as an error.
At s=1+i*tau, for every real tau and finite P without extra hypotheses,

    norm F_P(1+i*tau,1) <= A sum_r b_r R_r^2 = norm F_P(1,1).

Equality occurs at tau=0. This is uniform in the entire vertical frequency,
with the exact growing-prime mass still present. It supplies no saving in P.

Proof. At one prime put z=1/p and x=p^(-s). The corpus's four exact local
Euler offsets reduce to E_0=(1-z)^(-2), E_-1=x E_0,
E_-2=x^2 E_0 and E_1=-z/[x(1-z)] E_0. These follow by clearing the
nonzero denominators in the actual rational formulas. The first label has
relative response 1, the second x/z=a_p, the third -1/[a_p(1-z)]. The
coincident first/second response is their product. Multiplying all primes
and the original three label weights gives the balanced labelled term
times a_q/a_r. Summing every allowed label triple gives the displayed row
formula. On the vertical line each a_p has modulus one. The triangle
inequality bounds each tilted excluded row by R_r; all w_p,b_p,R_r and A
are nonnegative. Applying this to the complete row formula gives the sharp
bound, and the corpus's balanced signed trace identifies its attained value.

For the two-moving-variable problem, set x=za,y=zb. Four exact normalized
identities are also proved in the same leaf. With
F=(a+b-a^2-b^2)/(ab), G=a+b-1-b/a-a/b+b^2/a+a^2/b:

    (1-za)(1-zb) E_0 = 1 + [z F+z^2(a+b-2)]/(1-z)^2;
    (1-za)(1-zb) (za)^(-1) E_-1
      = [a+b-1+z((a+b)F-ab-1)+z^2(ab-a-b+a^2+b^2)]/[a(1-z)^2];
    (1-za)(1-zb) E_1
      = [ab-a-b+z(2(a+b)-ab-1)-z^2 ab]/[ab(1-z)^3];
    (1-za)(1-zb) (za)^(-1)(zb)^(-1) E_-2
      = [a^2+b^2+ab-a-b+z(ab(2-F-a-b)-(a+b)G)+z^2 ab G]/[ab(1-z)^2].

Domain conditions only exclude the displayed rational denominators' zeros.
These are symbolic identities, checked by Lean; no numerical experiments.
They expose the full allowed local responses needed for the joint limit.

Novelty check: the corpus provided the doubly balanced signed trace, its
fixed-prime double residue, the weighted local Euler offsets, and normal
convergence of the regular cubic factor. It did not supply the actual
one-balanced labelled deformation or this complete-source vertical maximum.
The existing regularized cubic source is not substituted for the actual
distinguished source. Deep and lexical searches are recorded in the P1 card.

Open hard task: formalize the actual growing-prime two-variable near-pole
profile in P1 bag-growing-near-pole-source, then control the physical Mellin
pairing including its noncompact frequencies and tails. Neither this
one-boundary bound nor a compact near-pole limit alone proves axes saving,
growing moments or common-height self-return. RH remains open.
