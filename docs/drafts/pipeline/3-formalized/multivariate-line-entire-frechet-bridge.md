# Continuous line-entire implies Frechet entire

- **ID:** multivariate-line-entire-frechet-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** premise-interface audit of `MultivariateEntireFrechetJet.lean`
- **Statement:** Every `f : MultivariateEntire d` is `ContDiff ℂ ⊤ f.1`.

## Goal

Remove the three explicit `ContDiff` premises from the directional, polarized, and ordered-partial
jet comparison theorems.  This is a source-pure regularity bridge: `MultivariateEntire d` already
bundles continuity and holomorphy on every affine complex line.

## Gates

- [x] 0 → 1  in-progress: exact statement, existing source definition, and hostile attack identified
- [x] 1 → 2  fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: not applicable; classical bridge, no novelty claim

## Frontier

- `[CORPUS]` `LineEntire` in
  `formal/GaloisForLFunctions/HTGeometry/MultivariateEntireCompactOpen.lean` says every affine-line
  restriction is complex differentiable; `MultivariateEntire` additionally carries continuity.
- `[CORPUS]` `lineEntire_of_differentiable` proves only the forward implication.
- `[LOCAL-RESEARCH]` `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/clocks/two-species-conformal-clock-scale-law.md`
  explicitly records Hartogs as absent from the project mathlib and changes representation to
  coordinate-slice holomorphy rather than proving the bridge.
- `[LITERATURE]` J. Bochnak and J. Siciak, *Analytic functions in topological vector spaces*,
  Studia Mathematica 39 (1971), 77–112, DOI `10.4064/sm-39-1-77-112`, gives the classical
  locally-bounded Gâteaux-holomorphic-to-holomorphic mechanism.  In finite dimension, continuity
  supplies local boundedness.
- `[REDISCOVERED]` The desired theorem is classical Hartogs/Bochnak–Siciak regularity, not new
  scientific knowledge.

## Paper proof

`[PAPER-PROVED]` Use the following Banach-valued statement, which strictly subsumes the scalar
`MultivariateEntire` application.  Let `E` be a complete complex normed space and let
`f : ℂ^n → E` be continuous.  Assume that for every `x,v : ℂ^n`, the map
`z ↦ f (x + z v)` is complex differentiable on `ℂ`.  Then `f` is analytic, hence `C^∞`, on `ℂ^n`.

1. Fix a centre `c`, positive polyradius `R`, and an interior point `z`.  Prove the polydisc Cauchy
   formula by induction on `n`.  The zero-dimensional case is immediate.
2. For the induction step, write `ℂ^(m+1) = ℂ × ℂ^m`.  Continuity of `f` makes the Cauchy-kernel
   integrand continuous on the compact distinguished torus, hence integrable.  For fixed first
   coordinate `w`, the tail map `y ↦ f(w,y)` is continuous and remains affine-line entire: an affine
   line in the tail is the ambient affine line with direction `(0,v)`.  Apply the induction
   hypothesis to its `m` tail coordinates.
3. The remaining outer integral is one-dimensional.  The map `w ↦ f(w,z_tail)` is the ambient
   affine-line restriction with direction `(1,0)`, hence entire.  The ordinary Banach-valued Cauchy
   formula evaluates that circle integral.  This proves the `n`-dimensional polydisc formula using
   only the stated hypotheses.
4. Define the multi-index Cauchy coefficients and homogeneous multilinear terms exactly as in
   `PolydiscSeriesCoefficients.lean`.  Their torus integrands are continuous because `f` is
   continuous; differentiability is not used.  Compactness bounds `f` on the torus.
5. Expand each coordinate Cauchy kernel geometrically, regroup by total degree, and interchange the
   dominated series with the torus integral.  The existing estimate
   `card (antidiagonalTuple n k) ≤ (k+1)^n` and a geometric majorant give positive convergence radius.
   The generalized polydisc Cauchy formula identifies the sum with `f(c+y)` on a ball about `c`.
6. Thus the existing formal multilinear series is a `HasFPowerSeriesOnBall` witness at every `c`, so
   `f` is `AnalyticAt ℂ` everywhere.  Standard analytic regularity gives
   `ContDiff ℂ ⊤ f`.

Every analytic step above is already formalized locally for a globally `Differentiable` source;
inspection of those proofs shows the stronger premise is used only (i) to obtain continuity and
(ii) to supply the coordinate-slice hypotheses in the Cauchy induction.  The two explicit
hypotheses supply exactly those uses, so no unproved several-variable theorem remains.

## Hostile audit

- The implication is not definitional: existence of all directional derivatives does not by itself
  make the directional derivative additive or continuous.
- Continuity is essential as the local-boundedness input in the general Gâteaux theorem.
- Proving only coordinatewise differentiability or only the first Fréchet derivative would not
  justify the all-orders `ContDiff` conclusion consumed by iterated jets.
- `[PAPER-PROVED]` The local polydisc expansion follows by generalizing the already formalized
  `polydiscCauchyFormula`, `polydiscSeries_hasSum`, and `polydiscHasFPowerSeriesOnBall` proofs as
  detailed above.  No paper-level open core remains.

## Log

- 2026-08-05 — created in Stage 1 from exhaustive premise-interface audit; classified as a
  classical `[BRIDGE]`, with exact Hartogs formalization core still open.
- 2026-08-05 — corpus audit found the complete polydisc Cauchy/power-series mechanism already
  formalized under an unnecessarily strong differentiability premise; generalized proof closed on
  paper and promoted to Stage 2.
- 2026-08-05 — formalized the Banach-valued universal law as
  `polydiscCauchyFormula_of_affineLineEntire`,
  `polydiscHasFPowerSeriesOnBall_of_affineLineEntire`, and
  `contDiff_of_continuous_affineLineEntire`; derived `MultivariateEntire.contDiff`; removed all
  three jet-comparison `ContDiff` premises.  Targeted Lean checks passed.  Axiom audit reports only
  standard mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.  Promoted to Stage 3.
