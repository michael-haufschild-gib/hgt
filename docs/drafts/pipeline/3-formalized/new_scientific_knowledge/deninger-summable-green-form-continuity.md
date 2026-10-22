# Summable local Green forms give continuous global energy

- **ID:** `deninger-summable-green-form-continuity`
- **Stage:** 3-formalized
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
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticPositiveCalderonKoszul.lean`:

- `deningerLocalEnergy_summable_of_summable_majorant`;
- `deningerSummedGreenForm`;
- `deningerSummedGreenForm_hasSum_apply_apply`;
- `deningerSummedGreenForm_apply_apply`;
- `deningerSummedGreenEnergy_continuous`;
- `deningerSummedGreenEnergy_nonnegative`.

Each declaration matches a clause of the theorem: `_hasSum_apply_apply`
and `_apply_apply` give `G(x,y) = ∑_α G_α(x,y)`,
`_continuous` gives continuity of the diagonal energy,
`_nonnegative` gives `𝓔(x) ≥ 0` from nonnegative local energies, and
`deningerLocalEnergy_summable_of_summable_majorant` is the scalar
majorant claim.

### Verification

- Direct command: `lake env lean` on the module — passes with no errors
  and no warnings.
- Cached module build: `lake build
  GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPositiveCalderonKoszul`
  completes (3084 jobs).
- Scratch `#print axioms` on all six declarations: only `propext`,
  `Classical.choice`, `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: statement isolated
- [x] 1 → 2 fully-proven: pointwise identity, continuity, nonnegativity,
      and the majorant claim proved
- [x] 2 → 3 formalized: all four clauses, with cached build and
      declaration-axiom audit
- [ ] 3 → 4 publication-ready: blocked on
      `DAC_ALL_PLACE_GREEN_FORM_NUCLEAR_SUMMABILITY`, which this card
      explicitly does not prove

## Falsifiers

- Pointwise scalar summability alone does not imply continuity of the
  summed form.
- A uniform positive lower bound is neither assumed nor needed.
- No zero divisor, RH premise, CCM object, or numerical calculation is
  used.

## Log

- 2026-08-01 — Closed the stage-3 gate.  Verified that the six named
  declarations state exactly the card's four clauses over an arbitrary
  real normed space, then ran the cached module build and the
  declaration-axiom audit.  No new Lean was needed.  Card moved to
  `3-formalized`.
