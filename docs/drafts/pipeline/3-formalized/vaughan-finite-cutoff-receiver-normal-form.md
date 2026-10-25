# Fixed-cutoff Vaughan packets modulo bounded pronic energy

- **ID:** vaughan-finite-cutoff-receiver-normal-form
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** Classify fixed linear combinations of the five Vaughan pieces after separating their linear mean, smooth-power term, and the original interior receiver.

## Exact classification

Fix `0<ε<1/2`, cutoffs `U,V`, and real coefficients `w_i`. Write
`P_w(n)=Σ_i w_i p_i(n)`, `H_U=Σ_(a≤U)μ(a)/a`,
`L_w=Σ_i w_i c_i(U,V)`, and
`Q_w=c_ε H_U H_V (w_3-w_2)`, where `c_ε=Re ζ(1-ε)/(1-ε)≠0`.
Let `B(f)` mean bounded pronic partial energy of the sequence `f`.

The exact classification is

`B(P_w) ↔ L_w=0 ∧ Q_w=0 ∧ (w_3=0 ∨ B(I_ε))`.

In particular, packets omitting the both-large component are fully decided by
the two explicit scalar conditions. Packets with both explicit terms removed retain
exactly the original receiver direction. This is a restricted-family classification,
not an estimate proving `B(I_ε)`.

## Normal-form argument

The exact small-small expansion already proved in the new budget module gives

`p_2(n)=-Z L_(U,V)(n)-c_ε n^(1-ε)P_(U,V)(n)-R_(U,V)(n)`.

At fixed cutoffs, `R_(U,V)` has bounded pronic norm by the finite atomic bound.
The floor estimate `|floor(n/d)-n/d|≤1` makes the two small pieces minus their linear
means uniformly bounded. It also makes `L_(U,V)(n)-A_U A_V n` uniformly bounded.
For `n≥UV`, the partial pole sum is exactly `H_U H_V`; replacing it by that constant
changes the smooth-power sequence only on a finite prefix. The pole component minus
`-ρn` is uniformly bounded by the active-correction estimate. Hence

`p_2(n)=-Z A_U A_V n-c_ε H_U H_V n^(1-ε)+r_2(n)`, with `B(r_2)`.

The exact five-piece identity then gives the general normal form

`P_w(n)=w_3 I_ε(n)+L_w n+Q_w n^(1-ε)+r_w(n)`, with `B(r_w)`.

This argument uses only the already proved atom estimates, finite sums, and finite
prefix corrections. The formalization retains the fixed-cutoff quantifiers:
the bounds depend on `U,V` and cannot be inserted at moving cutoffs without estimates.

## Proof of the classification

The fixed-cutoff Gram theorem gives `E(P_w;T)/T→L_w²`. Bounded energy forces this
limit to be zero, so `L_w=0`. Put `β=1-2ε>0`. The existing actual-source bound gives
`E_int(T)/T^β→0`. The smooth-power norm obeys
`‖n^(1-ε)‖_T/T^(β/2)→1/sqrt(β)`. To see the latter, its squared norm is
`Σ_(1≤n≤T)n^β/(n+1)`. The existing `norm_sum_cpow_div_succ_sub_le` in
`TheProbeReceiverEnergyMeasuresTheModulusOfZeta.lean`, specialized to real `β`,
puts that sum within a constant of `T^β/β`.

The reverse triangle inequality applied to the normal form now gives

`|‖P_w‖_T-|Q_w|‖n^(1-ε)‖_T| ≤ |w_3|‖I_ε‖_T+‖r_w‖_T`

when `L_w=0`. Divide by `T^(β/2)`. The right side tends to zero, while the
smooth-power quotient tends to `|Q_w|/sqrt(β)`. If `B(P_w)` holds, the left norm
quotient tends to zero, forcing `Q_w=0`. For `w_3=0`, this argument needs no
actual-source estimate.

After both coefficients vanish, boundedness is equivalent to `B(w_3 I_ε)` because
the normal-form remainder is bounded. This is equivalent to
`w_3=0 ∨ B(I_ε)`. No receiver bound is added as an assumption to the classification.

The actual-source input has been checked in source:
`eventually_interiorPronic_le_growth_of_pos` in
`AllDampingVinogradovKorobovBandAndInteriorGrowth.lean` bounds the energy by
`C T^(1-2ε) exp(-κ vkScale(T)/270)`. Since `vkScale(T)→∞`, it supplies precisely
`E_int(T)/T^(1-2ε)→0`. It supplies no fixed power saving. All ingredients of the
paper proof are dependency-closed, and their specialized combination is formalized.

## Further consequences exposed by the normal form

After subtracting each linear mean, the fixed-cutoff Gram at scale `T^(1-2ε)` again
has rank one: its vector is `(0,0,-1,1,0)`, multiplied by
`c_ε² H_U² H_V²/(1-2ε)`. The bounded-energy remainder and the actual receiver contribute
zero at this scale, by the triangle inequality and the preceding existing source estimate.
This gives a second explicit scale before the remaining receiver direction.

A further arithmetic paper proof simplifies the scalar condition at positive cutoffs:
`H_N≠0` for every `N≥1`. A prime `N/2<p≤N` appears in exactly one denominator with
nonzero Möbius coefficient. Multiplication by the product of primes up to `N` leaves
that term nonzero modulo `p`, while all others vanish. Bertrand's theorem supplies the
prime. The existing prime-supply theorem has now been checked. The stronger denominator
law and its complete paper proof are in
`../3-formalized/finite-mobius-harmonic-sums-never-vanish.md`.
The harmonic theorem's eight public declarations now pass Lean with standard axioms;
the final direct repository audit passed. Positive `U,V` force `Q_w=0 ↔ w_2=w_3`.

## Explicit paid basis at positive cutoffs

Assume `U,V≥1`. Once `w_2=w_3`, the exact five-piece identity gives

`P_w-w_3 I_ε=(w_0-w_3)p_0+(w_1-w_3)p_1+(w_4-w_3)p_4`.

The remaining linear coefficient is
`L_w=(w_0-w_3)A_U+(w_1-w_3)A_V+(w_3-w_4)ρ`.
If it vanishes, the right side is uniformly bounded pointwise, with bound

`|w_0-w_3| Σ_(d≤U)|μ(d)|d^(-ε)`
`+|w_1-w_3| Σ_(d≤V)|μ(d)|d^(-ε)+|w_4-w_3|/2`.

Thus the bounded-energy remainder can be strengthened to a bounded sequence on this
subspace. Two always-admitted coefficient vectors are

`b_U=(1,0,0,0,A_U/ρ)`, `b_V=(0,1,0,0,A_V/ρ)`.

Every admitted coefficient vector has the unique form
`α b_U+β b_V+γ(1,1,1,1,1)`, with `γ=0` unless `B(I_ε)` holds. Uniqueness follows
from coordinates 0, 1, and 3. The admitted subspace in `ℝ^5` therefore has dimension
`2` when the receiver is not admitted and `3` when it is admitted. Its quotient has
dimension `3` or `2`, respectively: linear drift, smooth power, and possibly the
original receiver are the only remaining directions. This is an exact finite-family
application to the corpus's payment-index viewpoint, not a proof of receiver admission.

The endpoint and upper-half analogues are separate extensions to audit: the smooth
power remains unpaid at `ε=1/2`, while it becomes paid for `ε>1/2`. The present
classified statement retains `0<ε<1/2`; no unchecked phase extension is claimed.

## Corpus and novelty audit

Initial Vaughan-specific search did not surface this normal form. The existing THIM
finite-kernel pole-vanishing laws likely supply much of its restricted-family content;
their exact statements must be checked before claiming any novelty. The actual signed
Vaughan specialization, not a new unsigned smooth-power asymptotic, is the proposed work.

Checked inputs now include `abs_weightCenteredPrefix_finiteKernel_le`, which bounds
every finite kernel's centered floor prefix by its absolute coefficient mass, and
`receiverBounded_dirichletConv_unit_iff_critical`, which decides smooth-power convolutions
on the critical Wiener class by their pole value. These already explain the finite
small-small admission criterion. The normal form must be presented as an application
and exact decomposition, without claiming a new general finite-kernel theorem.

Draft `FixedVaughanPacketsHaveTwoExplicitObstructions.lean` now contains the actual packet,
both scalar coefficients, complete bounded-norm normal form, explicit pointwise floor
correction, admission after both cancellations, linear-mean necessity, two always-admitted
coefficient vectors, and their spanning identity. Its first scratch check found five
finite-sum/indexing script errors, now corrected. The second check passed all twenty-one
public transitive-axiom reports with only standard axioms. Its sole remaining diagnostic
was a redundant tactic after a solved goal, now removed. The repository olean-producing
check passed for the residual-density importer. Its umbrella import is present;
the final direct no-olean audit passed.
`VaughanPacketsHaveAnExactResidualEnergyDensity.lean` passed its full scratch check and
all nineteen public transitive-axiom reports, using only standard axioms. It includes
the four source/smooth-power limits, smooth-mean necessity, second-scale quadratic and
polarized matrix laws, complete admission equivalence, positive-cutoff equality of the
convolution coefficients, the test omitting the both-large component, and positivity
of the fixed second-scale density. Its umbrella import is present; the producing check
passed for the coefficient-space importer, and the final direct audit passed.
The coefficient submodule, explicit spans, independent frames, dimensions two/three,
quotient dimension test, and unique coordinates passed all ten scratch axiom reports
with standard axioms. The checked source is now
`TheAdmittedVaughanCoefficientSpace.lean`, wired into the umbrella; its olean check passed
for the written zero-cutoff and endpoint importers. Its final direct audit passed.
No route retired. Full Q-I remains open.

## Log

- 2026-10-25 — Extracted the candidate classification from the exact retained floor/pole/remainder identity.
