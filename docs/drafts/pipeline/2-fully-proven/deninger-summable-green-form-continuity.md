# Summable local Green forms give continuous global energy

- **ID:** `deninger-summable-green-form-continuity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Labels:** `DAC_LOCAL_GREEN_ENERGY_SUMMABLE_MAJORANT`,
  `DAC_SUMMABLE_GREEN_FORM_CONTINUITY`
- **Parent:** `deninger-global-green-energy-radical`
- **Statement:** a summable family of continuous local Green bilinear
  forms has a continuous global sum; its diagonal is the sum of local
  energies and is nonnegative when every local energy is nonnegative.

## Theorem

Let \(E\) be a real normed space and
\[
 G_\alpha:E\times E\longrightarrow\mathbb R
\]
continuous bilinear forms.  Suppose
\[
 \sum_\alpha G_\alpha
\]
converges in the normed space
\(\mathcal L(E,\mathcal L(E,\mathbb R))\).  Define
\[
 G=\sum_\alpha G_\alpha,\qquad
 \mathcal E(x)=G(x,x).
\]
Then
\[
 G(x,y)=\sum_\alpha G_\alpha(x,y)
\]
for all \(x,y\), and \(\mathcal E:E\to\mathbb R\) is continuous.  If
\(G_\alpha(x,x)\ge0\) for every \(\alpha,x\), then
\(\mathcal E(x)\ge0\).

More generally, if nonnegative scalar local energies satisfy
\[
 0\le \mathcal E_\alpha(x)\le a_\alpha p(x)
\]
for a summable family \(a_\alpha\), then
\(\sum_\alpha\mathcal E_\alpha(x)\) converges for every \(x\).

## Proof

Evaluation at a fixed \(x\) is a continuous linear map from
\(\mathcal L(E,\mathcal L(E,\mathbb R))\) to
\(\mathcal L(E,\mathbb R)\).  Evaluation at \(y\) is again continuous
linear.  Applying these two maps to the convergent form series proves
the pointwise identity.  The summed form is continuous bilinear, so
the diagonal map \(x\mapsto G(x,x)\) is continuous.  Nonnegativity
follows from nonnegativity of each summand.  The scalar majorant claim
is the comparison test applied to
\(a_\alpha p(x)\).

## Arithmetic consequence

For `DAC_GLOBAL_GREEN_ENERGY_RADICAL`, it is enough to prove, on every
defining Banach disk of the mixed restricted \(L^1/L^2\) source
topology, summability of the local Green forms in the corresponding
continuous-bilinear-map space.  Pointwise convergence and continuity
of global energy then require no separate all-place argument.

This does not prove the arithmetic form-summability estimate.  It
isolates that estimate as
`DAC_ALL_PLACE_GREEN_FORM_NUCLEAR_SUMMABILITY`.

## Lean

Formalized in
`formal/GaloisForLFunctions/RHTower/DeningerArithmeticPositiveCalderonKoszul.lean`:

- `deningerLocalEnergy_summable_of_summable_majorant`;
- `deningerSummedGreenForm`;
- `deningerSummedGreenForm_hasSum_apply_apply`;
- `deningerSummedGreenForm_apply_apply`;
- `deningerSummedGreenEnergy_continuous`;
- `deningerSummedGreenEnergy_nonnegative`.

Direct foreground check with `lake env lean` passes.  Final cached
module and declaration-axiom audit remain the stage-3 gate.

## Falsifiers

- Pointwise scalar summability alone does not imply continuity of the
  summed form.
- A uniform positive lower bound is neither assumed nor needed.
- No zero divisor, RH premise, CCM object, or numerical calculation is
  used.
