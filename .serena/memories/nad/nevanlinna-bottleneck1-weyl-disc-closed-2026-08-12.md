# nad Bottleneck 1 — Weyl-disc closed form PROVED; `upperMap` refuted; M. Riesz isolated

Session 2026-08-12.  Everything below is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`),
wired into `GaloisForLFunctions.HTGeometry`, and rests only on `PositiveMomentForm s`,
`BoundedKernel s 0`, `s 0 = 1`.

## 1. `HTGeometry/NevLeafCauchyMoebius.lean` — the Weyl-disc closed form

- `nevTrunc_cauchy_identity` — finite stage, cleared:
  `(Bₙ(z)τ − Dₙ(z))·∫(x−z)⁻¹dμₙ = −s₀·(Aₙ(z)τ − Cₙ(z))` for
  `μₙ = quasiMeasure s n (nevBeta s n τ / nevAlpha s n τ)`.  Multiply
  `quasiMeasure_cauchy_identity_of_im_ne_zero` by `(h₀/hₙ)·nevAlpha` using
  `nevTruncNumeratorC_eq_quasi` / `nevTruncDenominatorC_eq_quasi`.
- `nevInf_cauchy_identity` — the limit.  `exists_tendsto_quasiProbMeasure_nevLeaf` +
  `tendsto_cauchyTransform_of_tendsto` + `tendsto_nev{A,B,C,D}truncC ∘ (goodLevel h τ ∘ φ)` +
  `tendsto_nhds_unique`.
- `nevInf_denominator_ne_zero`; **`cauchyTransform_nevLeaf_eq_moebius`**
  `∫(x−z)⁻¹dν_τ = −(A τ − C)/(B τ − D)`.

## 2. `HTGeometry/NevLeafInfinityCauchyMoebius.lean` — the `∞` parameter

`nevLeaf_infinity_eq_fiberMeasure`, `exists_tendsto_quasiProbMeasure_nevLeafInf`,
`ofReal_nevAlphaInf/BetaInf`, `nevAtruncC_closedInf`, `nevBtruncC_closedInf`,
`nevAtruncC_eq_quasiInf`, `nevBtruncC_eq_quasiInf`, `nevTruncInf_cauchy_identity`,
`nevInf_cauchy_identity_infty`, `nevBinf_ne_zero`,
**`cauchyTransform_nevLeafInf_eq_ratio`** `∫(x−z)⁻¹dν_∞ = −A/B`.

## 3. `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean` — Bottleneck 1 item 1 CLOSED

**`analyticNevCarrierFamily h h0b h0 : ClassicalAnalyticNevanlinnaCarrierFamily s`**,
`exists_classicalAnalyticNevanlinnaCarrierFamily`.  Carrier convention `(a,b,c,d) = (−A, C, B, −D)`.

## 4. `HTGeometry/NevanlinnaCarrierDenominatorRow.lean` — three of six `MaximalTranslationInputs`

`nevInf_no_common_zero`, `exists_nevBrealInf_eq_zero`, `exists_nevBinf_eq_zero`,
`nevBinf_I_ne_zero`, and the carrier-convention wrappers, plus
`analyticNevCarrierFamily_quotient : F.quotient z = D(z)/B(z)`.

## 5. `HTGeometry/NevanlinnaWeylDiscPole.lean` — `upperMap` is REFUTED

`MaximalTranslationInputs.upperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im` is **false**.

- `im_cauchyTransform_pos` — Cauchy transform of a probability measure has `Im > 0` on the UHP.
- `weylForm s z t = Im((−A t + C)·conj(B t − D))`; `weylForm_expand` gives the real quadratic
  `weylLead·normSq t + p·Re t + weylTilt·Im t + c`; `weylForm_eq_im_mul_normSq` ties it to the
  Möbius image; `weylForm_pos_ofReal`; `weylLead_pos`.
- `weylTilt = Re(A·conj D − C·conj B)`: `weylTilt_ofReal = 1`, `continuous_weylTilt`,
  `weylTilt_ne_zero`, `weylTilt_pos` (convexity of the half-plane + IVT).
- **`nevInf_quotient_im_neg`**: `0 < z.im ⟹ (D(z)/B(z)).im < 0`.
- **`analyticNevCarrierFamily_quotient_im_neg`**.

Repair needed: the jet-pole half-plane in the transversality chain must be the LOWER one.  Genuine
uses of positivity: `NormalizedProjectiveCauchyDensityControl` (separating poles from their own
conjugates and from `ℝ` — survives a uniform sign flip); everywhere else it is consumed as
`(hupper i).ne'`; the one quantitative use is `AnalyticNevanlinnaCarrierBridge`'s
`compact_finite_strictPositive_uniformLowerBound` feeding
`projectiveNevanlinnaJetExpansionSmoothControl_coordinate_eq_singleton_last`, which drags
`NevanlinnaJetTriangular` / `LocalNevanlinnaJetTriangular` along.  **Cheaper alternative not yet
tried**: conjugation transport — for real `t`, `((t − conj q)⁻¹)^{k+1} = conj(((t − q)⁻¹)^{k+1})`,
so the packet-value matrix at conjugated poles is the entrywise conjugate and `mulVec` injectivity is
preserved; instantiate the abstract lemmas at `conj ∘ F.quotient` (which is in the UHP) and conjugate
back, leaving the abstract modules untouched.

## 6. `HTGeometry/NevanlinnaEntryMinimalType.lean` — M. Riesz reduced to one Prop

`norm_nevBinf_le`, `norm_nevCinf_le` complete the corpus's `norm_nevAinf_le` / `norm_nevDinf_le`.
`KernelMinimalExponentialType s` := for every `A > 0` some `C ≥ 1` bounds both kernel roots by
`C·exp(A‖z‖)` uniformly in the truncation.  `norm_mul_exp_half_le` / `entry_bound_absorb` absorb the
linear factor.  **`hasMinimalExponentialType_nev{A,B,C,D}inf`** derive minimal exponential type of
all four entries from it.

**Route audit (do not re-attempt).**  Volterra/Gronwall cannot prove
`KernelMinimalExponentialType`: the comparison identity is a Volterra equation with a
Hilbert–Schmidt kernel, `‖V^m‖ ≤ ‖V‖_HS^m/√(m!)`, generating `exp(c‖z‖²)` — order two.  Splitting a
small tail only improves the constant; the tail estimate holds on `‖z‖ < 1/(2ε)` and iterating past
that radius restores `exp(ε²‖z‖²)`.  The real route is entire-function theory: the zeros of `B` are
real with `∑ 1/|x_k| < ∞`, and a genus-zero Hadamard product gives minimal type (for each `A > 0`
split off the finitely many zeros with `|x_k| ≤ R`).  Mathlib has `Analysis/Complex/JensenFormula`
and `Analysis/Complex/ValueDistribution/*` but **no Weierstrass/Hadamard factorization** — that has
to be built.

## Remaining for the ten Bottleneck-1 cards

1. `KernelMinimalExponentialType s` (M. Riesz) — the big one;
2. the `upperMap` sign repair (or the conjugation transport);
3. `phase_isGδ : IsGδ {ν | MaximalTranslationDifferentialFree ν}`;
4. leaf/label covariance under an arbitrary normalization change, for
   `carrierProjector_eq_of_leaf_label_covariance`.

## Repo note

Another Claude session is building in this repo concurrently (RHTower modules); the ~148
`formal_tools.py lint` "owned module unreachable" errors come from its unwired files, not from this
work.  Re-read `GaloisForLFunctions/HTGeometry.lean` before editing it.
