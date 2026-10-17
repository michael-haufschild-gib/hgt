# Actual box averaging and quantitative affine regularity

- **ID:** physical-box-average-affine-regularity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** continuum-coprime-shear; physical-affine-commutator-producers
- **Statement:** Actual physical L² box producers have a constructed derivative, exact variance loss, unconditional affine gap control and compact-source graph approximation.

## Exact theorem and significance

For arbitrary q∈V=L²(ℝ) and s∈ℝ, put h=exp(s). The actual translation
orbit is norm-continuous. Its Bochner average and finite difference define
bounded linear operators

    M_s q=h⁻¹∫₀ʰτ_uq du,     D_s q=h⁻¹(τ_hq−q),
    ‖M_s q‖≤‖q‖,             ‖D_s q‖≤2h⁻¹‖q‖.

Primitive evaluation is a bounded inner-product functional represented by
1_(0,t]−1_(t,0]. Passing it through the Bochner integral identifies the
actual continuous representative m_(s,q)(t)=h⁻¹(F_q(t+h)−F_q(t)).
It equals F_(D_s q)(t)+h⁻¹F_q(h); hence it is locally absolutely
continuous, and both m and its actual a.e. derivative D_s q lie in L².
The strong translation orbit has derivative τ_cD_s q at every real c.

Exact Gram expansion retains every cross-shift term:

    ∫₀ʰ‖τ_uq−M_s q‖²du=h(‖q‖²−‖M_s q‖²),
    ∫₀ʰ∫₀ʰ‖τ_uq−τ_vq‖²dvdu=2h²(‖q‖²−‖M_s q‖²).

Oriented interval cancellation gives
τ_cM_s q−M_s q=h⁻¹∫₀ᶜ(τ_(u+h)q−τ_uq)du, for every real c.
Together with contraction, this proves

    ‖τ_cM_s q−M_s q‖≤2 min(1,|c|/h)‖q‖,
    ‖C_(a,b)M_s q‖≤2√|a| min(1,|b(a−1)|/h)‖q‖.

The squared and operator-composition bounds also hold, including zero and
negative affine parameters. Thus the explicit regularized range restores
small-gap control despite the maximal unrestricted commutator norm.

The derivative at zero of the orbit primitive proves M_s q→q strongly
as s→−∞; the exact averaging loss tends to zero. Compact source Dirichlet
mass is bounded by ofReal(‖q‖²). For every compact source ψ and nonnegative
line-weight sequence, its already constructed finite resistance R_ψ gives

    E_ψ(q)≤R_ψ ofReal(‖q‖²),
    E_ψ(C_(a,b)M_s q)
      ≤R_ψ ofReal(4|a| min(1,|b(a−1)|/h)²‖q‖²),
    E_ψ(M_s q−q)→0.

Thus the actual regular producers approximate every input in physical norm
and each compact-source jump energy. No regularity or analytic admission
premise on q is used. Classical Steklov averaging, FTC and Hilbert variance
are parents; the contribution is their actual affine/graph realization.
No optimality of the gap coefficient, operator-norm approximation, full
uncut SourceGraph closure, completed divisor-domain invariance, unweighted
logarithmic H1 or RH conclusion is claimed. Trap10 is addressed through
explicit unconditional producers and exact errors. No pre-floor subtraction.

## Proof gates

- [x] Corpus and primary-source audit, with coverage limits below.
- [x] Dependency-closed paper proof before field Lean.
- [x] Six serial direct leaf checks and all61 public axiom checks.
- [x] 28 principal signatures and73 mathlib API probes.
- [x] Six unique umbrella imports and61 exact catalog locations.
- [x] Scoped artifact/whitespace checks and unchanged read-only README.
- [x] Global lint run; unrelated failures recorded explicitly below.

## Formal modules and evidence

| Module | Lines | Public declarations |
|---|---:|---:|
| PhysicalTranslationContinuity | 78 | 12 |
| PhysicalBoxAverage | 116 | 13 |
| PhysicalBoxProfile | 117 | 16 |
| PhysicalBoxVariance | 88 | 6 |
| PhysicalBoxAffineRegularity | 115 | 9 |
| PhysicalBoxGraphControl | 85 | 5 |

Six serial direct leaf checks pass without diagnostics; all normal outputs
are current. All61 public axiom checks use only propext,Classical.choice,
Quot.sound.28 principal signatures and73 mathlib API probes pass. Six unique
umbrella imports and61 exact catalog locations verified.599lines total,
53theorems+8definitions. Paper proof preceded field Lean. README remains
unchanged, SHA256 dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933.
No full/umbrella build, heartbeat increase or numerical experiment.

Global lint --check-generated exits1 for seven unrelated unreachable modules:
ConfinedCoherentPlasticGap, ForcedFirstCollar, SignedLcmFractionalDefectAndCompleteFibreCollapse, SignedPrimePolarClampedPrimeSum, SignedPrimePolarRealFactorialStencil, StrictPairedCollarLimit, UniformPairedCollarGain.
There are381 existing large-file warnings; no own, proof-debt or generated
index errors. Repository-wide green is not claimed. Concurrent files preserved.

Evidence: /tmp/physical-box-axioms.log, /tmp/physical_box_axioms.lean,
/tmp/physical-box-{audit-names,manifest-report,leaf-checks,lint-errors}.json,
/tmp/physical-box-api-entries.txt, /tmp/physical-box-index.log and
/tmp/physical-box-lint-final.log. Paper:
docs/reports/BiScaleUncertainty/PhysicalBoxAverageAffineRegularity.md.
Card: docs/drafts/pipeline/3-formalized/physical-box-average-affine-regularity.md.
One connected contribution, certified19/100; overall goal remains active.

## Corpus and boundaries

Current corpus audit inspected all20 candidate statements; no source
arguments, proof ideas or ingredient sets returned. Search partial=true,
text/source interrupted, deadline/vector-proof stage incomplete,
generation1447551 pending, refresh incomplete/background indexer.
Earlier candidate audit inspected20 candidates and20 source arguments.
Own drafts found in later searches are not independent certification.
Primary mathlib continuous-pullback and Demkowicz Energy Spaces references
are linked in the paper. No absence or external novelty claim.

Lean lessons: use MemLp.ae_eq for a.e. replacement and le_min to prove
nonnegativity of a minimum. zero_le has an implicit ENNReal argument.
Use mul_le_mul_right instead of deprecated mul_le_mul_left'. Give shifted
interval rewrites explicit integrands and endpoints. Beta-reduce integrands
before norm rewrites; expose pointwise functions before derivative/AC rewrites.
Simplify the orbit primitive at zero before unfolding its integral definition.
Type constant limits explicitly. innerSL and its apply lemmas have two
universe parameters even when the printed signature lacks a leading @.
