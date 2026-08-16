# Source Selector Repair Obligation Ledger

- **ID:** source-selector-repair-obligation-ledger
- **Stage:** 0-backlog
- **Type:** route audit / source-theorem specification
- **Source:** `no-boundary-selection-of-zeta.md`,
  `finite-rank-one-selector-no-free-lunch.md`,
  `rank-one-scalar-shadow-needs-kernel-exhaustion.md`,
  `uvarov-kernel-pregate-rh-equivalence.md`
- **Statement:** A source selector for the RH route must select a repair/index
  theorem, not merely the function `zeta`. Every proposed source axiom must say
  exactly which fake it excludes and must not include the Schur sign, the
  kernel positivity, or zero localization in disguised form.

## Purpose

This ledger implements the required artifact named in
`no-boundary-selection-of-zeta.md`:

`A_i | source-only data | known classification risk | fake excluded exactly | circularity risk | downstream residue`

The point is not to collect more conditions. The point is to prevent a source
route from smuggling in the repair theorem under source language.

## Ledger

| ID | Source-only data | Known classification risk | Fake excluded exactly | Circularity risk | Downstream residue |
|---|---|---|---|---|---|
| A1 | Completed scalar object of order one, canonical `xi` gauge, pole normalization. | With standard analytic hypotheses this is close to degree-one Selberg / converse-theorem classification. | Generic Hurwitz/Lerch-type objects fail scalar self-dual completion or Euler-product source. | If A1 is used to infer zero localization, it has silently become RH. | A1 can identify the object class; it does not prove the repair/index sign. |
| A2 | Rank-one `Q` Gamma boundary datum: first exterior atom `y_*=-4/25`, mass `a_*=4/25`, with canonical gauge extraction. | Trivial-zero bookkeeping and Uvarov/Krein algebra are classical. | Dedekind/automorphic objects with different archimedean signature fail the `Q` boundary datum, not because of their zeros. | Defining the boundary datum by the Weyl threshold side is circular. | Supplies the boundary parameter and channel; does not prove it lands on the positive side. |
| A3 | Euler/local-factor orientation: prime finite-part form `R^P_d` built from positive local factors before reading zeros. | If reduced to "has an Euler product", this is Selberg-search and too weak. | Davenport-Heilbronn fails because it lacks the required positive Euler/local-factor orientation. | If "orientation" means `R^P_d` has the sign needed for `N_0`, it is the conclusion. | Must yield a source-side theorem controlling the finite-place demand. |
| A4 | Reversed-prime/sign-fake rejection: the source construction distinguishes the sign of the prime residual. | A scalar moment or coefficient test may miss this fake. | The sign-fake fails because its prime residual has the wrong source orientation. | If rejection is detected only by `kappa_-`, `s_d`, or Hankel negativity, the fake was graded by the target. | Forces the theorem onto the integer index, not the rank-one scalar shadow. |
| A5 | One-dimensional seam boundary scaffold: unrepaired carrier has one active boundary channel before repair. | Already present as the deficiency-one / `N_1` scaffold; not new by itself. | None; Davenport-Heilbronn can share the scaffold. | Treating `N_1 -> N_0` as part of admissibility includes the repair theorem. | Leaves the threshold-side theorem open. |
| A6 | Kernel and omitted-channel exhaustion from source data. | All-order kernel positivity on finite exterior ideals is RH-equivalent by existing cards. | A fake with a negative invisible direction must fail here by source data, not by later positivity testing. | If stated as `A|_{ker beta}>=0`, it is already an RH-equivalent cone unless derived from source. | Needed before any scalar `s_d>0` can certify the full index. |
| A7 | Full Schur/index sign for the completed semilocal carrier. | Finite Schur algebra is classical; finite channel truncations are height-limited. | Sign-fake and high-height off-line defects must fail by the completed channel system. | Defining admissibility as `kappa_-=0`, `s_d>0`, Stieltjes positivity, Herglotz positivity, or zero localization is circular. | This is the live repair theorem. |

## Immediate Verdict

Rows A1--A5 are scaffold and source typing. They may select the function and the
rank-one boundary family, but they do not prove RH.

Rows A6--A7 contain the RH-bearing content:

`source data => kernel/omitted-channel exhaustion + full Schur/index sign`.

If A6 is assumed as all-order positivity on a boundary ideal, it is already
RH-equivalent. If A7 is assumed as `kappa_-=0`, `s_d>0`, Stieltjes positivity,
Herglotz positivity, or zero localization, it is circular. Therefore the only
non-mirror source theorem left is:

`Euler/Gamma/FE source construction forces A6 and A7 before the reciprocal divisor is used.`

No current card proves this theorem.

## Kill Conditions

Kill a proposed `L_src` route immediately if any of the following happens:

1. It stops after selecting `zeta` by degree-one Selberg or conductor-one
   classification.
2. It defines admissibility by the desired repaired positivity or by the Weyl
   threshold side.
3. It rejects Davenport-Heilbronn only by observing off-line zeros.
4. It rejects the sign-fake only by a scalar or Hankel test after the target cone
   has been evaluated.
5. It uses `s_d>0` without proving kernel and omitted-channel exhaustion first.
6. It uses a finite prolate/channel truncation as if it were the all-channel
   semilocal carrier.

## Workable Next Theorem Shape

The next theorem must not be "zeta is the unique source object." It must have the
form

`For the source-built semilocal carrier H_src,d, Euler/local-factor orientation plus the canonical Gamma boundary imply the full boundary Schur matrix has no negative direction, uniformly in degree and channel scale.`

Equivalently, it must prove the completed integer index from source data before
atom-local or reciprocal-divisor positivity is evaluated.

## Status

- A1--A5: scaffold / classification / source typing.
- A6: RH-equivalent if assumed; open only if source-derived.
- A7: live repair theorem; no proof in the current corpus.

## Log

- 2026-06-24 -- Codex: created to satisfy the `L_src` ledger requirement and
  to prevent function-selection or scalar-shadow arguments from posing as the
  repair theorem.

## 2026-06-24 Euler orientation has category width

`euler-orientation-category-width-audit.md` adds the scope condition for rows A3--A7. A broad Euler/local-factor orientation theorem is a broad GRH-style theorem for every object satisfying the same source axioms. A narrow conductor-one `Q` theorem may identify `zeta`, but it still leaves the repair/index sign to prove.

Thus row A3 must declare its category width before it can feed A6--A7. It cannot act as a zeta-specific repair theorem by slogan.

## 2026-06-24 axis positivity is not the Euler transfer

`../2-fully-proven/axis-positivity-does-not-imply-hankel-positivity.md` sharpens rows A3--A7. The Euler-product input may give coordinatewise positivity such as `Lambda(n)>=0`, but the repair rows require nonlinear Hankel/Schur positivity. Positive axis coordinates can already fail the first Hankel determinant.

Thus A3 feeds A6--A7 only if a source theorem transfers axis-mode Euler data into combination-mode Schur/Hankel inequalities. Listing positive coefficients is not that theorem.

## 2026-06-24 positive weights require pointwise source kernels

`../2-fully-proven/positive-source-weights-require-pointwise-hankel-kernels.md` gives the exact condition under which row A3 can feed A6--A7 by positivity alone. If the target Hankel/Schur matrix is a positive-weighted sum of source kernels and the proof is meant to work for every positive source weighting, each pointwise source kernel must be positive semidefinite.

If the pointwise kernels are not PSD, the repair theorem must use more than Euler coefficient positivity: exact arithmetic weights, multiplicativity, archimedean cancellation, or another completed source constraint.

## 2026-06-24 Loewner budget is not sign positivity

`../3-formalized/not_new_scientific_knowledge/positive-source-weights-do-not-bound-loewner-budget.md` sharpens row A3 against rows A6--A7. Even if Euler/local-factor orientation supplies positive weights and pointwise PSD kernels, that only puts the finite-place contribution in a cone. It does not prove the fixed domination `-R^P_d <= M_{triv,d}`.

The scaling test is decisive: if the same sign argument survives multiplying the positive weights by `t`, it cannot be a budget proof. A3 can feed A6--A7 only through exact weight magnitudes, normalization, multiplicativity, archimedean cancellation, or a completed explicit-formula identity.

## 2026-06-24 atom-motion source kernels are indefinite

`../2-fully-proven/hankel-atom-displacement-tangent-indefinite.md` sharpens rows A3--A7 for the Jensen/Hankel chart. A moved moment atom contributes the tangent form `2m q(r)q'(r)`, which is indefinite. Therefore positive Euler amplitudes attached to root or atom displacements cannot be the pointwise PSD kernels required for a positive-weight proof.

For this chart, A3 can feed A6--A7 only through nonlinear full-matrix comparison, completed explicit-formula coupling, or a source-built boundary/index theorem. Linear positive summation of displacement kernels is ruled out.

## 2026-06-24 finite Markov prefixes do not discharge A6--A7

`../2-fully-proven/finite-markov-prefix-nonselection.md` applies the all-order warning directly to the seam-log Markov coordinate. A finite prefix of shifted moments can be compatible with a positive Stieltjes continuation and with a later failed square test.

Thus rows A6--A7 cannot be discharged by finite Markov/Pick interpolation, finite continued fractions, finite Hankel minors, or finite Cholesky certificates. The source proof must control every later square test or provide a source-rigidity theorem that does so.

## 2026-06-24 carrier language must survive seam division

`../2-fully-proven/seam-log-derivative-weld-identity.md` adds a normalization constraint to rows A6--A7. The seam-log Markov candidate is not separate from the completed carrier data:

`G_src(-w^2)=Xi'(w)/(w Xi(w))`.

Therefore any proposed source theorem phrased in carrier language must prove the Stieltjes square-test cone after the exact division by `w` and square-coordinate change. If it only proves a broad analytic property of the raw carrier, it has not discharged A6--A7.

## 2026-06-24 contraction language is not a second selector

`../2-fully-proven/loewner-contraction-congruence-normalization.md` normalizes rows A6--A7 on the operator face. For any positive finite budget `M`,

`M+R>=0 <=> M^(-1/2)(-R)M^(-1/2)<=I`.

Thus `K_d<=I` is not an additional source selector after `Q_0,d` has been formed. A6--A7 require a proof that Euler/Gamma/FE source data construct `K` and force the contraction bound before zero-divisor positivity is read.

## 2026-06-24 source orientation must fix scale

`../3-formalized/not_new_scientific_knowledge/scale-invariant-source-orientation-cannot-pay-budget.md` adds a scale test to rows A3--A7. If a source-orientation predicate is unchanged under `R -> tR` for every `t>0`, then it can imply a fixed budget `B+R>=0` only when every admissible residual is already PSD.

Thus an Euler/Gamma source theorem for `-R^P<=M_triv` must identify the source datum that fixes the actual scale of `R^P`: exact weights, normalization, multiplicativity at the correct magnitude, archimedean cancellation, or a completed explicit-formula identity. Orientation without scale does not discharge A6--A7.

## 2026-06-24 finite source normalizations leave recession directions

`../3-formalized/not_new_scientific_knowledge/finite-source-normalizations-leave-budget-recession.md` adds the affine version of the scale test. A finite list of linear source normalizations can imply a fixed budget `B+R>=0` only if every remaining recession direction is already nonnegative, or absent in the two-sided case.

Thus adding conductor, pole, Gamma-boundary, finite Euler, or finite finite-part constraints does not by itself discharge A6--A7. The proof must audit the residual recession space and show it contains no budget-negative direction, or replace the finite data with an all-order source identity or boundary/index theorem.

## 2026-06-24 protector tail does not discharge A6--A7

`../2-fully-proven/tail-e-zero-support-nonselector.md` adds the tail audit to rows A6--A7. Once the protector Hankel tail is represented by a finite signed measure on the shifted reciprocal zero support, the full tail sequence determines that signed measure.

Thus `E=mu_E` is a source finite-part identification and a zero-side coordinate transfer, not the repair theorem. A proof may use the tail only after it separately derives kernel/channel exhaustion and the completed boundary/index sign from source data.

## 2026-06-24 source functors must be non-finite-type

`../2-fully-proven/finite-type-source-functor-rh-nonselection.md` adds a functor-level version of the finite-probe obstruction. If the source functor deciding rows A6--A7 factors through finitely many local observables, it gives the same output to a polynomial-tail fake with a non-real zero quartet.

Thus the repair rows require an all-order source object before the threshold side is evaluated. A finite linear source feature vector, finite boundary matrix family at checked degrees with entries factoring through finite probes, or finite symbolic audit of that kind is a passport, not the source selector.

## 2026-06-24 nonlinear finite selectors need an anti-oracle gate

`../2-fully-proven/nonlinear-finite-selector-oracle-vacuity.md` adds the boundary condition for nonlinear source functors. A finite-valued nonlinear selector can always select rows A6--A7 by using the target property as its characteristic function.

Thus a proposed nonlinear selector does not discharge the repair rows unless its definition is source-built and avoids `kappa_-=0`, `s_d>0`, Stieltjes/Herglotz positivity, zero localization, or an equivalent repaired-index predicate. The required theorem is still a transfer from source construction to full Schur/index sign.

## 2026-06-24 Turan/log-convex transfer does not discharge A6--A7

`../2-fully-proven/all-order-log-convexity-does-not-imply-stieltjes.md` blocks a weak all-order positivity transfer. Even every adjacent `2 x 2` Hankel minor can be nonnegative while a `3 x 3` Hankel block is indefinite.

Thus rows A6--A7 cannot be discharged by coefficient signs, complete monotonicity, or all adjacent Turan/log-convex inequalities. The source theorem must reach the full Schur/Hankel cone or prove an independent upgrade theorem.

## 2026-06-24 fixed-rank Hankel control does not discharge A6--A7

`../2-fully-proven/fixed-rank-hankel-tests-do-not-imply-stieltjes.md` blocks another weak positivity transfer. For every fixed `r`, the shifted Hankel tests up to size `r` can all pass at every shift while a size `r+1` square test fails.

Thus rows A6--A7 cannot be discharged by proving a bounded-rank family of Hankel inequalities. The repair theorem must control arbitrary-degree square tests or include a source upgrade that makes bounded-rank data equivalent to the full Schur/Hankel cone.

## 2026-06-24 boundary monotonicity does not discharge A6--A7

`../2-fully-proven/boundary-weyl-thresholds-have-no-formal-monotonicity.md` blocks a monotone pole-to-Uvarov shortcut. For two independent boundary functionals, the positive bulk form can make either Schur threshold larger, so exterior boundary location alone does not order the repair costs.

Thus rows A6--A7 cannot be discharged by saying that the first-trivial-zero channel inherits the pole-channel budget monotonically. The source theorem must prove the comparison for the actual Euler/Gamma/FE carrier, or work directly with the first-trivial-zero channel.

## 2026-06-24 Christoffel monotonicity does not replace A6--A7

`../2-fully-proven/stieltjes-bulk-exterior-christoffel-monotonicity.md` gives the valid exterior-threshold comparison for positive moment bulks. The comparison requires the Gram form to be a positive Stieltjes bulk with support on one side of the boundary interval.

Thus rows A6--A7 cannot cite Christoffel monotonicity until the positive bulk has been built from Euler/Gamma/FE source data. The monotonicity lemma can propagate a source positivity theorem; it cannot supply that theorem.

## 2026-06-24 N1 anatomy does not discharge A6--A7

`../3-formalized/not_new_scientific_knowledge/n1-signed-bulk-exterior-monotonicity-fails.md` blocks a signed-bulk monotonicity shortcut. A one-negative-square signed moment form can have support to the right of the pole and first-trivial-zero boundary points while reversing their repair-threshold order.

Thus rows A6--A7 cannot be discharged by proving only `H^- in N_1`. The repair theorem also needs kernel exhaustion, the full Schur/index sign, or a source-specific monotonicity law for the actual Euler/Gamma/FE carrier.

## 2026-06-24 positive Stieltjes bulk plus archimedean atoms does not discharge A6--A7

`../3-formalized/not_new_scientific_knowledge/positive-stieltjes-pole-plus-first-atom-insufficient.md` blocks the shortcut that keeps only positive bulk support, pole mass, and first-trivial-zero mass. The displayed positive atomic bulk produces an unrepaired one-negative-square form, but the first atom does not repair it.

Thus rows A6--A7 require the actual Euler/Gamma/FE carrier. Archimedean atom bookkeeping and a generic positive Stieltjes bulk do not prove the full repair/index sign.

## 2026-06-24 `nu'` positivity is RH-loaded

`docs/consolidated/revision01/big-picture.md` has been corrected so `nu'=sum_rho 2 y_rho delta_{y_rho}` is not called a positive reciprocal zero measure before the repair theorem is proved. In the reciprocal chart, positivity of this shifted divisor measure on `R_+` is exactly the all-order RH content recorded in `../2-fully-proven/seam-log-markov-pick-rh-equivalence.md` and `../2-fully-proven/source-aware-q0-alone-reciprocal-positivity.md`.

Thus rows A6--A7 cannot use a positive `nu'` as a feeder object. A valid source theorem must construct the shifted tower or the equivalent Markov/Pick transform from Euler/Gamma/FE data and then prove positivity. If `nu'` is introduced as already positive, the route has moved the target statement into the input vocabulary.

## 2026-06-24 real-axis kernel positivity does not discharge A6--A7

`../3-formalized/not_new_scientific_knowledge/real-axis-kernel-positivity-nonselector.md` gives an exact finite model: an indefinite form `H` can have `e(t)^T H^{-1} e(t)>0` for every real evaluation point `t`. The moment curve can miss negative directions.

Thus rows A6--A7 cannot be discharged by proving positivity of a Christoffel/reproducing kernel only as a real-axis scalar function. The source theorem must prove the full form positivity, the full Pick/Nevanlinna condition, or an equivalent completed Schur/index statement.

## 2026-06-24 divided source pieces are not separate Markov objects

`../2-fully-proven/seam-division-source-split-cancellation.md` records the local source-split obstruction. In the seam variable `w`, the completed quotient `Xi'(w)/(w Xi(w))` is holomorphic, but the divided summands `A(w)/w` and `P(w)/w` each have a nonzero simple pole at `w=0`; their residues cancel by the functional equation.

Thus rows A3--A7 cannot be discharged by assigning separate Markov/Pick/Stieltjes positivity to the divided archimedean and prime pieces. Any source theorem must keep the FE cancellation inside the completed boundary object, or prove positivity directly for the completed sum after division.

## 2026-06-24 discriminant bulk domination needs a real estimate

`../2-fully-proven/discriminant-bulk-cross-sign-needs-scale-separation.md` audits the degree-one Gram-Heine route. A positive-real-part off-axis reciprocal atom can have a negative cross term with a positive real bulk atom; at `x=Re y`, `Re(y(y-x)^2)<0`.

Thus rows A6--A7 cannot cite termwise discriminant positivity without a summed source estimate. The discriminant expansion is useful, but the repair theorem still needs a genuine domination argument across the actual divisor or a scale-separated finite-range theorem.

## 2026-06-24 discriminant scale separation made exact

`../2-fully-proven/discriminant-cross-positive-interval.md` supplies the exact
positive range for the cross term `Re(y(y-x)^2)`. For `y=u+iv`, `a=|v|`, and
`r=|y|`, the upper bad endpoint is `x_+(y)=(u^2-a^2+ar)/u`, and `x>=1.18|y|`
is a sufficient condition for positivity.

This does not discharge rows A6--A7. It only defines what a legitimate
scale-separated termwise proof would have to show. The live source obligation
remains a full summed domination estimate or another completed-boundary
identity proving positivity directly.

## 2026-06-24 degree-one discriminant repair is a tail-margin test

`../3-formalized/not_new_scientific_knowledge/degree-one-discriminant-tail-stability.md` gives the
summed replacement for the deleted `det H_1` termwise proof. If a positive real
bulk has moments `L_k` and determinant margin `Delta_B=L_1L_3-L_2^2`, and the
remaining tail has absolute moment bounds `eta_k`, then the sufficient condition
is

`Delta_B > L_1 eta_3 + L_3 eta_1 + 2 L_2 eta_2 + eta_1 eta_3 + eta_2^2`.

Thus rows A6--A7 may use a finite-height `d=1` discriminant proof only after
checking this exact inequality, or a stronger source identity. The phrase
"bulk domination" is not a proof unless it supplies the determinant margin and
tail bounds.

## 2026-06-24 finite-degree discriminant domination has a matrix gate

`../3-formalized/not_new_scientific_knowledge/finite-degree-shifted-hankel-tail-stability.md` gives the
all-degree finite-height replacement for informal `d~H` bulk domination. For a
split `H_d=B_d+R_d`, positivity follows from

`lambda_min(B_d) > ||R_d||_op`,

with checkable sufficient bounds from the tail absolute moments `eta_k` via
Frobenius or row-sum estimates.

Thus rows A6--A7 cannot claim a finite determinant range from height separation
alone. They must provide the verified bulk eigenvalue margin, the tail moment
bounds through `2d+1`, and the resulting matrix inequality.

## 2026-06-24 monomial absolute-tail gate cannot give `d~H`

`../2-fully-proven/monomial-tail-gate-height-linear-no-go.md` audits the
finite-degree matrix gate. In the monomial basis,

`lambda_min(B_d) <= L_{2d+1} <= L_1 R^(2d)`,

while the first reciprocal hard-edge tail moment beyond height `H` has the sharp
scale `log H / H`. Thus raw absolute-tail bounds can support at most logarithmic
degree in `H`, not a height-linear determinant range.

Rows A6--A7 must therefore use a relative Loewner/source-Weyl estimate,
orthogonal-polynomial normalization, or a completed sign identity. A monomial
entrywise tail estimate is a sufficient finite check only at very low degree.

## 2026-06-24 finite reciprocal Hankel tests are height-limited

`../2-fully-proven/finite-degree-reciprocal-tests-height-limited.md` records the
native reciprocal version of finite-prefix blindness. For any fixed degree `d`,
positive shifted blocks remain positive after adding a sufficiently small
non-real reciprocal conjugate pair. In seam variables this is a sufficiently
high off-line defect.

Thus rows A6--A7 cannot be discharged by any fixed finite determinant ladder,
no matter how clean the checked minors are. The proof must include a uniform
degree-to-height theorem or an all-order source-built sign transfer.

## 2026-06-24 relative contraction requires completion, not only compressions

`../2-fully-proven/relative-contraction-compression-exhaustion.md` records the
operator-route target. If a bounded self-adjoint source operator `K` is already
constructed on the `M_triv` completion, then `K<=I` is equivalent to all finite
compression inequalities on the dense polynomial subspaces. But finite
compressions alone do not construct `K` and do not prove boundedness or closure.

Thus rows A6--A7 require three source-side deliverables: construct the completed
relative operator from Euler/Gamma/FE data, prove its bounded/closed
self-adjoint form status, and prove the contraction. Matrix checks are only
compressions after those deliverables exist.

## 2026-06-24 one-sided compression bounds do not construct the operator

`../3-formalized/not_new_scientific_knowledge/one-sided-compression-bound-not-bounded-operator.md` adds
the domain caveat to the operator route. A dense-domain inequality
`k[v]<=||v||^2` on every finite compression can hold for an unbounded-below
diagonal form, so it does not produce a bounded self-adjoint contraction.

Thus rows A6--A7 must specify whether the source object is a bounded
self-adjoint `K`, a closed semibounded form `I-K`, or another completed boundary
object. One-sided finite compression bounds alone do not discharge the operator
construction.

## 2026-06-24 triangular coordinates are not repair selectors

`../2-fully-proven/triangular-seam-coordinates-function-complete.md` sharpens rows A6--A7. A full all-order coordinate sequence that is triangularly invertible over the seam-log jet is function-complete, so it cannot be the missing repair selector merely because it is a continued fraction, Jacobi parameter string, cumulant string, Hankel-ratio string, or Pade table.

A proposed selector in such coordinates must identify the source theorem that forces the repaired index or Stieltjes/Markov positivity before the coordinate is inverted back to the completed function or reciprocal divisor.

## 2026-06-24 single even frequency fails the Stieltjes cone

`../2-fully-proven/single-even-frequency-not-stieltjes.md` sharpens row A3 against rows A6--A7. A positive FE-even frequency `B(cosh(lambda w)-1)` contributes shifted seam moments

`T_k=B(-1)^(k+1)lambda^(2k)/(2k-1)!`,

so the first `2 x 2` shifted Hankel block has determinant `-7B^2lambda^8/360<0`.

Thus Euler positivity cannot be transferred termwise through positive even frequencies. A source proof must use completed interaction: FE cancellation, archimedean coupling, multiplicative correlation among the actual weights, or a closed boundary/index theorem.

## 2026-06-24 positive FE-even frequency cone is anti-Markov

`../2-fully-proven/positive-even-frequency-cone-not-markov.md` upgrades the one-frequency obstruction to the full positive cone generated by FE-even frequencies. For a positive measure `mu` on frequencies, the shifted seam moments satisfy

`T_k=(-1)^(k+1) int lambda^(2k)dmu(lambda)/(2k-1)!`,

so every nonzero positive mixture has `T_2<0` and cannot be a positive Markov/Stieltjes moment sequence on `R_+`.

Thus row A3 cannot feed A6--A7 by positive frequency summation, even after FE-even symmetrization. The repair theorem must use completed interaction outside that positive cone.

## 2026-06-24 finite signed FE-even atoms are still anti-Markov

`../2-fully-proven/finite-signed-even-frequency-atoms-not-markov.md` extends the positive frequency-cone obstruction. A nonzero finite signed sum of real FE-even frequency atoms has shifted moments

`T_k=(-1)^(k+1) S_k/(2k-1)!`, with `S_k=sum_j c_j lambda_j^(2k)`.

After equal frequencies are combined, the largest remaining real frequency dominates `S_k`, so `T_k` is negative on one tail parity. Thus rows A3--A7 cannot be discharged by adding finitely many signed real-frequency counterterms to the positive cone. A viable source correction must be infinite/nonlocal, multiplicative, archimedean-prime completed, or boundary-index based.

## 2026-06-24 finite-order local frequency operators are still anti-Markov

`../2-fully-proven/finite-order-local-frequency-operators-not-markov.md` closes the coefficient-local variant of the positive frequency route. If a finite-order local operator acts on the `z^k` coefficient by a nonzero real polynomial `q(k)`, then a nonzero positive FE-even frequency mixture gives

`T_k^{q,mu}=(-1)^(k+1) q(k) M_k/(2k-1)!`, with `M_k>0`.

Since `q(k)` has an eventual constant sign, one tail parity of `T_k^{q,mu}` is negative. Thus rows A3--A7 cannot be discharged by applying a finite-order local differential, finite-part, or degree-polynomial correction to the positive frequency source. The correction must be all-order/nonlocal, multiplicative, archimedean-prime completed, or boundary-index based.

## 2026-06-24 parity correction is a nonlocal half-turn

`../2-fully-proven/seam-parity-correction-is-nonlocal-half-turn.md` identifies the operation that finite-order local corrections cannot supply. On degree `k`, the seam parity operator has eigenvalue `(-1)^k`; it is the half-turn pullback `Hf(z)=f(-z)`. No real polynomial `q(D)` in `D=z d/dz` can equal it, since `q(2n)=1` for all `n` would force `q=1`, contradicting `q(2n+1)=-1`.

Thus rows A3--A7 cannot hide the parity repair inside finite local `D`-operator language. A source proof must either construct the nonlocal FE half-turn from the completed Euler-Gamma source or leave the coefficient-diagonal model for a multiplicative/all-order/boundary-index proof.

## 2026-06-24 half-turn parity repair is still not Markov positivity

`../2-fully-proven/half-turn-repaired-frequency-not-markov.md` closes the next loophole after the nonlocal half-turn was identified. For a single positive FE-even frequency, the repaired moments are

`U_1=B lambda^2`, `U_2=B lambda^4/6`, `U_3=B lambda^6/120`,

but the first shifted Hankel determinant is still

`U_1 U_3-U_2^2=-7 B^2 lambda^8/360<0`.

Thus rows A3--A7 cannot be discharged by decomposing into positive FE-even frequencies, applying the half-turn to fix parity, and summing repaired atoms with positive weights. The missing source interaction must also change the factorial Hankel geometry or leave the pointwise frequency-kernel model.

## 2026-06-24 bounded half-turn packets still fail the first Hankel gate

`../2-fully-proven/bounded-half-turn-frequency-packets-fail-hankel.md` quantifies the post-half-turn obstruction. For a finite positive repaired packet with squared frequencies `x_i`, the first determinant is controlled by

`U_1 U_3-U_2^2=(3 M_1 M_3-10 M_2^2)/360`.

The Kantorovich moment bound gives `M_1 M_3/M_2^2 <= (a+b)^2/(4ab)` when the squared-frequency support lies in `[a,b]`.

If `b/a < (17+2 sqrt(70))/3`, then `U_1 U_3-U_2^2<0`. Thus rows A3--A7 cannot be discharged by local positive repaired packets. A viable source proof must force broader cross-scale interaction or leave the positive repaired-packet model.

## 2026-06-24 first-gate threshold is sharp but not all-order

`../3-formalized/not_new_scientific_knowledge/half-turn-first-gate-threshold-sharp.md` shows that the half-turn repaired spread threshold `(17+2 sqrt(70))/3` is exact for the first shifted Hankel gate. With squared endpoints `x,y` and balanced weights `c_x=y^2`, `c_y=x^2`, the determinant is

`x^3 y^3(3x^2-34xy+3y^2)/360`.

Thus broad positive repaired packets can pass gate one. Rows A3--A7 must now explain either why the completed source forces such broad spread and all higher Hankel gates, or why the proof leaves the repaired-packet model entirely.

## 2026-06-24 finite repaired packets closed; infinite repaired sources split

`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/finite-half-turn-repaired-packets-not-markov.md` closes the finite positive half-turn repaired packet route. Broad finite packets can pass the first shifted Hankel gate, but finite support eventually has a top frequency, so `M_kM_(k+2)/M_(k+1)^2 -> 1` while the factorial repair requires a ratio above `1`; an adjacent shifted Hankel determinant is eventually negative.

`../2-fully-proven/infinite-half-turn-frequency-source-admissibility-split.md` records the infinite counterpart. Unrestricted sigma-finite mass accumulating at zero frequency can realize any Stieltjes target, hence has no selecting power. `../2-fully-proven/locally-infinite-repaired-frequency-source-for-compact-markov.md` shows that for compact Markov targets not supported only at `0`, every realizing positive repaired source is forced to have infinite mass in every zero-frequency neighborhood; equivalently, finite or locally finite border sources cannot realize the target through this model.

Thus rows A3--A7 cannot be discharged by "make the repaired packet infinite". A proof must supply a source-admissibility theorem: the actual Euler/Gamma/FE source must provide the required factorial curvature and higher Hankel gates without an arbitrary zero-frequency reservoir.

## 2026-06-24 finite-normalization recession gate formalized

`../3-formalized/not_new_scientific_knowledge/source-budget-recession-gates.md` formalizes the core of
`../3-formalized/not_new_scientific_knowledge/finite-source-normalizations-leave-budget-recession.md` in
Lean. A one-sided source-normalization ray can preserve a fixed budget only if
its recession direction is nonnegative on every test vector; a two-sided affine
line can preserve the budget only if its direction vanishes.

Thus rows A3--A7 have a formal audit condition for any proposed finite source
normalization: list the remaining recession directions and prove they are
already nonnegative or absent. Otherwise finite source data have not constructed
the rank-one boundary-Weyl object or paid the Loewner budget.

## 2026-06-24 compact repaired targets force local zero-frequency infinity

`../2-fully-proven/locally-infinite-repaired-frequency-source-for-compact-markov.md` strengthens the infinite repaired-source split: for a compact Markov target not supported only at `0`, every positive repaired-frequency source realizing the positive moments has infinite mass in every interval `(0,delta)` at frequency `0`.

Thus rows A3--A7 cannot replace the zero-frequency reservoir by a finite border counterterm, local finite source measure, or unstated renormalized mass. A viable source-admissibility theorem must either explain why the actual Euler/Gamma/FE source law permits and selects this locally infinite border behavior, or abandon the additive positive repaired-frequency model for the completed boundary/index object.

## 2026-06-24 positive Mellin finiteness does not select the reservoir

`../2-fully-proven/zero-frequency-repaired-source-mellin-threshold.md` sharpens the zero-frequency reservoir audit. For compact Markov targets not supported only at `0`, every positive repaired-frequency source has exact local Mellin threshold `0`: all positive powers `int_(0,delta) x^q dmu` with `q>0` are finite, while `q<=0` is locally infinite.

Thus rows A6--A7 cannot be discharged by requiring finite positive fractional moments, finite positive Mellin energy, or any local integrability condition above exponent `0`. Such conditions are already satisfied by the arbitrary zero-frequency reservoir. Requiring local finiteness or a nonpositive Mellin threshold goes the other way and excludes compact Markov targets in this additive repaired-frequency model. The source law must either select the locally infinite reservoir noncircularly or move to the completed boundary/index object.

## 2026-06-24 local weighted finiteness is exactly `dx/x`

`../2-fully-proven/zero-frequency-repaired-source-dx-over-x-law.md` strengthens the Mellin-threshold audit. For compact Markov targets not supported only at `0`, the forced positive repaired-frequency source satisfies

`int_(0,delta) w dmu < infinity <=> int_0^delta w(x) dx/x < infinity`

for every nonnegative local weight `w`. Thus rows A6--A7 cannot be discharged by any local weighted-finiteness condition at zero frequency. If the weight is `dx/x`-integrable, the arbitrary reservoir already passes it; if not, the condition rejects the compact Markov targets themselves.

The admissibility law must therefore use source structure beyond local weighted integrability: exact Euler/Gamma/FE selection of a locally infinite reservoir, or a completed boundary/index object.

## 2026-06-24 local measure class is not a selector

`../2-fully-proven/zero-frequency-repaired-source-dx-over-x-law.md` now records the bounded-equivalence corollary. Any two compact Markov targets not supported only at `0` have repaired zero-frequency reservoirs that are mutually comparable on every `(0,delta)`: each is bounded above and below by a constant multiple of the other.

Thus rows A6--A7 cannot be discharged by a predicate depending only on local null sets, absolute continuity, bounded-density class, or local regularity of the zero-frequency measure. Such a predicate sees the same local object for all compact targets. A viable source selector must use nonlocal source structure, exact Euler/Gamma/FE coupling, global moment constraints, or the completed boundary/index carrier.

## 2026-06-24 reservoir density is target-equivalent

`../2-fully-proven/zero-frequency-reservoir-density-laplace-equivalence.md` changes representation from local measure class to density against `dx/x`. The leading logarithmic blowup of the zero-frequency reservoir is only `nu_+((0,R])/2`, while the full density `h(x)` is Laplace-equivalent to the positive target measure after `y->y^(-1/2)`.

Thus rows A6--A7 cannot be discharged by the leading local blowup rate, except for a scalar normalization. Conversely, using the full reservoir density as an admissibility input is target-equivalent unless a source theorem constructs that density from Euler/Gamma/FE data before Markov/Pick positivity is read.

## 2026-06-24 complete monotonicity of the reservoir is target positivity

`../2-fully-proven/reservoir-density-complete-monotonicity-markov-equivalence.md` proves the Bernstein/Laplace characterization of reservoir profiles. For `H(t)=2h(t^2)`, being a finite Laplace transform supported away from `0` is equivalent to coming from a compact positive Markov target; in intrinsic terms, `H` is completely monotone with finite `H(0+)` and `exp(a t)H(t)` completely monotone for some `a>0`.

Thus rows A6--A7 cannot be discharged by assuming complete monotonicity of the zero-frequency reservoir profile. That condition is the positive Markov cone after the reservoir change of variables unless it is derived from Euler/Gamma/FE source data.

## 2026-06-24 finite Schur singularity is not an admissibility law

`../2-fully-proven/shifted-stieltjes-hankel-strictness-infinite-support.md` records the strictness side of the shifted Stieltjes target. Once a positive infinite-support Stieltjes representation is available, every finite shifted Hankel block is positive definite. Singular finite blocks occur only in finite-support or flat-extension cases, where the moment generating function is rational.

Thus rows A6--A7 cannot use singular Schur branches, Moore-Penrose range conditions, or flat finite extensions as a landscape admissibility law. Those are finite model artifacts unless the source object itself is finite-support, which would be incompatible with the reciprocal zero-divisor tower. The source law must still construct the positive infinite-support carrier or leave the shifted Stieltjes model.
