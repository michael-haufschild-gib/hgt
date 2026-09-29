import GaloisForLFunctions.HTGeometry.PrimePairCollisionSection

/-!
# Trace-norm wall landing of the prime-pair collision record

The product quantile map `(u, v) ↦ (Q_μ u, Q_μ v)` pushes the uniform law of the unit square to
`μ ⊗ μ`, so `W_μ f = f ∘ (Q_μ × Q_μ)` is an isometry `L²(μ ⊗ μ) → L²((0, 1)²)`.  Charting the
literal record by `W_{μ_d} J_d` and the continuum record by `W_μ`:

`‖(1 ⊗ W_{μ_d} J_d) 𝖳_d (1 ⊗ W_{μ_d} J_d)* - (1 ⊗ W_μ) 𝖳 (1 ⊗ W_μ)*‖₁ → 0`  as `d → 0⁺`.

Every charted exit vector is `Z^{-1/2} Φ_n(δ(Q u, Q v))` with a bounded continuous `Φ_n`, and
`Q_{μ_d} → Q_μ` pointwise on `(0, 1)` while `Z_d → 8/105`, so each grade converges in `L²` by
dominated convergence.  Both records have unit total exit mass and the continuum exit norms
`√w_n` are summable, so `∑ₙ ‖a_n - b_n‖² = 2 - 2 Re ∑ₙ ⟪a_n, b_n⟫ → 0` by dominated summation,
and the Gram estimate `‖𝖳_a - 𝖳_b‖₁ ≤ 2 ‖a - b‖` lands the records in trace norm.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_pairLanding :
    IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-! ## Dominated summation of unit records -/

section Summation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type*} {l : Filter ι}

omit [InnerProductSpace ℂ H] in
theorem norm_le_one_of_hasSum {a : ℕ → H} (ha : HasSum (fun n => ‖a n‖ ^ 2) 1) (n : ℕ) :
    ‖a n‖ ≤ 1 := by
  have h := ha.summable.le_tsum n (fun k _ => sq_nonneg ‖a k‖)
  rw [ha.tsum_eq] at h
  nlinarith [norm_nonneg (a n)]

/-- **Unit records converge in `ℓ²`.**  If `∑ ‖a_n‖² = ∑ ‖b_n‖² = 1`, `∑ ‖b_n‖ < ∞` and every
`a_n → b_n`, then `∑ ‖a_n - b_n‖² → 0`. -/
theorem tendsto_tsum_norm_sub_sq {a : ι → ℕ → H} {b : ℕ → H}
    (ha : ∀ t, HasSum (fun n => ‖a t n‖ ^ 2) 1) (hb : HasSum (fun n => ‖b n‖ ^ 2) 1)
    (hbs : Summable fun n => ‖b n‖) (hconv : ∀ n, Tendsto (fun t => a t n) l (𝓝 (b n))) :
    Tendsto (fun t => ∑' n, ‖a t n - b n‖ ^ 2) l (𝓝 0) := by
  have hre : ∀ t, Summable fun n => RCLike.re ⟪a t n, b n⟫_ℂ := fun t =>
    hbs.of_norm_bounded fun n => by
      rw [Real.norm_eq_abs]
      refine (RCLike.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_hasSum (ha t) n)
  have hsplit : ∀ t, ∑' n, ‖a t n - b n‖ ^ 2 = 2 - 2 * ∑' n, RCLike.re ⟪a t n, b n⟫_ℂ := by
    intro t
    have h1 : ∀ n, ‖a t n - b n‖ ^ 2
        = (‖a t n‖ ^ 2 + ‖b n‖ ^ 2) - 2 * RCLike.re ⟪a t n, b n⟫_ℂ := fun n => by
      rw [@norm_sub_sq ℂ]
      ring
    simp_rw [h1]
    rw [Summable.tsum_sub ((ha t).summable.add hb.summable) ((hre t).mul_left 2),
      Summable.tsum_add (ha t).summable hb.summable, (ha t).tsum_eq, hb.tsum_eq, tsum_mul_left]
    ring
  have hlim : Tendsto (fun t => ∑' n, RCLike.re ⟪a t n, b n⟫_ℂ) l (𝓝 (∑' n, ‖b n‖ ^ 2)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖b n‖) hbs (fun n => ?_)
      (Eventually.of_forall fun t n => ?_)
    · have h := (RCLike.continuous_re.tendsto _).comp
        ((hconv n).inner (𝕜 := ℂ) (tendsto_const_nhds (x := b n)))
      have hbb : RCLike.re ⟪b n, b n⟫_ℂ = ‖b n‖ ^ 2 := inner_self_eq_norm_sq (b n)
      rw [hbb] at h
      exact h
    · rw [Real.norm_eq_abs]
      refine (RCLike.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_hasSum (ha t) n)
  rw [hb.tsum_eq] at hlim
  simp_rw [hsplit]
  have := (tendsto_const_nhds (x := (2 : ℝ))).sub (hlim.const_mul 2)
  simpa using this

end Summation

/-! ## Quantile charts of pair laws -/

/-- The uniform law of the unit square. -/
abbrev unitSquareLaw : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))

/-- `(u, v) ↦ (Q_μ u, Q_μ v)` pushes the uniform square to `μ ⊗ μ`. -/
theorem measurePreserving_pairQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (Prod.map (quantile μ) (quantile μ)) unitSquareLaw (μ.prod μ) :=
  (measurePreserving_quantile μ).prod (measurePreserving_quantile μ)

/-- The pair quantile chart `W_μ f = f ∘ (Q_μ × Q_μ)`. -/
def pairQuantileChart (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Lp ℂ 2 (μ.prod μ) →L[ℂ] Lp ℂ 2 unitSquareLaw :=
  compL2 (measurePreserving_pairQuantile μ)

theorem norm_pairQuantileChart_apply (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : Lp ℂ 2 (μ.prod μ)) : ‖pairQuantileChart μ f‖ = ‖f‖ :=
  norm_compL2_apply _ f

theorem pairQuantileChart_coeFn_of_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : Lp ℂ 2 (μ.prod μ)} {F : ℝ × ℝ → ℂ} (h : (f : ℝ × ℝ → ℂ) =ᵐ[μ.prod μ] F) :
    (pairQuantileChart μ f : ℝ × ℝ → ℂ) =ᵐ[unitSquareLaw]
      fun w => F (quantile μ w.1, quantile μ w.2) :=
  (compL2_coeFn _ f).trans
    (h.comp_tendsto (measurePreserving_pairQuantile μ).quasiMeasurePreserving.tendsto_ae)

/-! ## The charted records -/

theorem summable_norm_pairQuantileChart_exit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hν : ∀ᵐ z ∂μ.prod μ, 0 < z.1 ∧ 0 < z.2) :
    Summable fun n => ‖pairQuantileChart μ (collisionExitVector (μ.prod μ) n)‖ ^ 2 :=
  (summable_norm_collisionExitVector_sq (μ.prod μ) hν).congr fun n => by
    rw [norm_pairQuantileChart_apply]

/-- The atomic landing record `(1 ⊗ W_{μ_d}) 𝖳_{ν_d} (1 ⊗ W_{μ_d})*`. -/
def pairLandingRecord (d : ℝ) :
    HistoryL2 (Lp ℂ 2 unitSquareLaw) →L[ℂ] HistoryL2 (Lp ℂ 2 unitSquareLaw) :=
  recordOp (fun n => pairQuantileChart (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      (collisionExitVector (pairWallLaw d) n))
    (summable_norm_pairQuantileChart_exit _ (ae_pos_pairWallLaw d))

/-- The continuum landing record `(1 ⊗ W_μ) 𝖳 (1 ⊗ W_μ)*`. -/
def wallCollisionRecord :
    HistoryL2 (Lp ℂ 2 unitSquareLaw) →L[ℂ] HistoryL2 (Lp ℂ 2 unitSquareLaw) :=
  recordOp (fun n => pairQuantileChart (expMeasure 1) (collisionExitVector expPairLaw n))
    (summable_norm_pairQuantileChart_exit _ hν_expPair)

/-- The literal prime-pair chart `W_{μ_d} J_d : ℓ²(Primes × Primes) → L²((0, 1)²)`. -/
def primePairQuantileChart {d : ℝ} (hd : 0 < d) : PrimePairHilbert →L[ℂ] Lp ℂ 2 unitSquareLaw :=
  pairQuantileChart (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) ∘L pairAtomChart hd

theorem norm_primePairQuantileChart_apply {d : ℝ} (hd : 0 < d) (a : PrimePairHilbert) :
    ‖primePairQuantileChart hd a‖ = ‖a‖ := by
  rw [primePairQuantileChart, comp_apply, norm_pairQuantileChart_apply, pairAtomChart]
  exact (pairAtomBasis hd).repr.symm.norm_map a

/-- The charted literal record is the atomic landing record. -/
theorem primePairRecord_charted {d : ℝ} (hd : 0 < d) :
    historyMap (fun _ => 1) (fun _ => norm_one.le) (primePairQuantileChart hd) ∘L
        primePairRecord hd ∘L
          adjoint (historyMap (fun _ => 1) (fun _ => norm_one.le) (primePairQuantileChart hd))
      = pairLandingRecord d := by
  have hsum : Summable fun n => ‖primePairQuantileChart hd (primePairExitVector hd n)‖ ^ 2 :=
    (summable_norm_primePairExitVector_sq hd).congr fun n => by
      rw [norm_primePairQuantileChart_apply]
  rw [primePairRecord, recordOp_conj_historyMap _ _ _ hsum, pairLandingRecord]
  refine recordOp_congr _ _ _ (funext fun n => ?_)
  rw [primePairQuantileChart, comp_apply, primePairExitVector, pairAtomChart_adjoint_apply]

/-- The charted continuum record is the continuum landing record. -/
theorem hodgeCollisionRecord_charted :
    historyMap (fun _ => 1) (fun _ => norm_one.le) (pairQuantileChart (expMeasure 1)) ∘L
        hodgeCollisionRecord ∘L
          adjoint (historyMap (fun _ => 1) (fun _ => norm_one.le)
            (pairQuantileChart (expMeasure 1)))
      = wallCollisionRecord :=
  recordOp_conj_historyMap _ _ _ _

/-! ## Grade-wise convergence -/

/-- The exit profile `Φ_n(v) = √(1 - v²) vⁿ v(1 - v²)`. -/
def exitProfile (n : ℕ) (v : ℝ) : ℝ := Real.sqrt (1 - v ^ 2) * v ^ n * (v * (1 - v ^ 2))

theorem continuous_exitProfile (n : ℕ) : Continuous (exitProfile n) := by
  unfold exitProfile
  fun_prop

theorem abs_exitProfile_le_one (n : ℕ) {v : ℝ} (hv : |v| ≤ 1) : |exitProfile n v| ≤ 1 := by
  have h2 : v ^ 2 ≤ 1 := by nlinarith [abs_nonneg v, sq_abs v]
  have h3 : 0 ≤ 1 - v ^ 2 := by linarith
  rw [exitProfile, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h3,
    abs_pow]
  have hs : Real.sqrt (1 - v ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [sq_nonneg v])
  have hp : |v| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hv
  have hq : 1 - v ^ 2 ≤ 1 := by linarith [sq_nonneg v]
  calc Real.sqrt (1 - v ^ 2) * |v| ^ n * (|v| * (1 - v ^ 2)) ≤ 1 * 1 * (1 * 1) := by gcongr
    _ = 1 := by norm_num

theorem collisionExitVector_coeFn_profile (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν] (n : ℕ) :
    (collisionExitVector ν n : ℝ × ℝ → ℂ) =ᵐ[ν]
      fun z => (((Real.sqrt (collisionMass ν))⁻¹ * exitProfile n (pairContrast z) : ℝ) : ℂ) := by
  filter_upwards [collisionExitVector_coeFn ν n] with z hz
  rw [hz, collisionAmplitude, collisionProfile, pairCoherence, exitProfile]
  push_cast
  ring

theorem collisionProfile_sq_eq_profile (z : ℝ × ℝ) :
    collisionProfile z ^ 2 = (pairContrast z * (1 - pairContrast z ^ 2)) ^ 2 := rfl

theorem continuousAt_pairContrast {z : ℝ × ℝ} (hz : 0 < z.1) (hz' : 0 < z.2) :
    ContinuousAt pairContrast z := by
  unfold pairContrast
  refine ((continuous_fst.sub continuous_snd).continuousAt).div
    ((continuous_fst.abs.add continuous_snd.abs).continuousAt) ?_
  rw [abs_of_pos hz, abs_of_pos hz']
  linarith

theorem quantile_expMeasure_one_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < quantile (expMeasure 1) u := by
  rw [quantile_expMeasure_one hu.1 hu.2]
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hu.2) (by linarith [hu.1]))

/-- The charted contrast converges pointwise on the open square. -/
theorem tendsto_comp_pairContrast_quantile {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {w : ℝ × ℝ}
    (hw : w ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    Tendsto (fun d => Φ (pairContrast
        (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.1,
          quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.2)))
      (𝓝[>] 0) (𝓝 (Φ (pairContrast (quantile (expMeasure 1) w.1,
        quantile (expMeasure 1) w.2)))) := by
  have h1 := tendsto_wallHalfLineQuantile_nhdsGT_zero hw.1.1 hw.1.2
  have h2 := tendsto_wallHalfLineQuantile_nhdsGT_zero hw.2.1 hw.2.2
  have hc := continuousAt_pairContrast
    (z := (quantile (expMeasure 1) w.1, quantile (expMeasure 1) w.2))
    (quantile_expMeasure_one_pos hw.1) (quantile_expMeasure_one_pos hw.2)
  exact (hΦ.continuousAt.comp hc).tendsto.comp (h1.prodMk_nhds h2)

theorem ae_mem_unitSquare : ∀ᵐ w ∂unitSquareLaw, w ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [unitSquareLaw, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

/-- `Z_d → 8/105` as `d → 0⁺`. -/
theorem tendsto_collisionMass_pairWallLaw :
    Tendsto (fun d => collisionMass (pairWallLaw d)) (𝓝[>] 0)
      (𝓝 (collisionMass expPairLaw)) := by
  have hψ : Continuous fun v : ℝ => (v * (1 - v ^ 2)) ^ 2 := by fun_prop
  have hrepr : ∀ μ : Measure ℝ, [IsProbabilityMeasure μ] → collisionMass (μ.prod μ)
      = ∫ w, (pairContrast (quantile μ w.1, quantile μ w.2) *
          (1 - pairContrast (quantile μ w.1, quantile μ w.2) ^ 2)) ^ 2 ∂unitSquareLaw := by
    intro μ _
    rw [collisionMass, ← (measurePreserving_pairQuantile μ).map_eq,
      integral_map (measurePreserving_pairQuantile μ).measurable.aemeasurable
        (measurable_collisionProfile.pow_const 2).aestronglyMeasurable]
    rfl
  simp_rw [pairWallLaw]
  rw [hrepr]
  simp_rw [hrepr]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun d => ((hψ.measurable.comp (measurable_pairContrast.comp
      ((measurable_quantile _).prodMap (measurable_quantile _)))).aestronglyMeasurable))
    (Eventually.of_forall fun d => Eventually.of_forall fun w => ?_) (integrable_const _) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := abs_collisionProfile_le_one (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      w.1, quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.2)
    rw [collisionProfile] at this
    nlinarith [abs_nonneg (pairContrast (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      w.1, quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.2) *
      (1 - pairContrast (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.1,
        quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.2) ^ 2)),
      sq_abs (pairContrast (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.1,
        quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.2) *
      (1 - pairContrast (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.1,
        quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.2) ^ 2))]
  · filter_upwards [ae_mem_unitSquare] with w hw
    exact tendsto_comp_pairContrast_quantile hψ hw

theorem measurable_exitProfile_quantile (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable fun w : ℝ × ℝ => exitProfile n (pairContrast (quantile μ w.1, quantile μ w.2)) :=
  (continuous_exitProfile n).measurable.comp
    (measurable_pairContrast.comp ((measurable_quantile μ).prodMap (measurable_quantile μ)))

/-- **Grade-wise landing.**  `W_{μ_d} e_n(ν_d) → W_μ e_n` in `L²((0, 1)²)`. -/
theorem tendsto_pairQuantileChart_exit (n : ℕ) :
    Tendsto (fun d => pairQuantileChart (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
        (collisionExitVector (pairWallLaw d) n)) (𝓝[>] 0)
      (𝓝 (pairQuantileChart (expMeasure 1) (collisionExitVector expPairLaw n))) := by
  set c : ℝ → ℝ := fun d => (Real.sqrt (collisionMass (pairWallLaw d)))⁻¹ with hc_def
  set c0 : ℝ := (Real.sqrt (collisionMass expPairLaw))⁻¹ with hc0_def
  have hc : Tendsto c (𝓝[>] 0) (𝓝 c0) :=
    ((Real.continuous_sqrt.tendsto _).comp tendsto_collisionMass_pairWallLaw).inv₀
      (Real.sqrt_pos.mpr collisionMass_expPair_pos).ne'
  have hc0 : 0 ≤ c0 := inv_nonneg.mpr (Real.sqrt_nonneg _)
  set Φd : ℝ → ℝ × ℝ → ℝ := fun d w => exitProfile n (pairContrast
    (quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.1,
      quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) w.2)) with hΦd
  set Φ0 : ℝ × ℝ → ℝ := fun w => exitProfile n (pairContrast
    (quantile (expMeasure 1) w.1, quantile (expMeasure 1) w.2)) with hΦ0
  have hrepr : ∀ d, ‖pairQuantileChart (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
        (collisionExitVector (pairWallLaw d) n)
        - pairQuantileChart (expMeasure 1) (collisionExitVector expPairLaw n)‖ ^ 2
      = ∫ w, ‖((c d * Φd d w : ℝ) : ℂ) - ((c0 * Φ0 w : ℝ) : ℂ)‖ ^ 2 ∂unitSquareLaw := by
    intro d
    rw [norm_sq_Lp_two_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub
        (pairQuantileChart (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
          (collisionExitVector (pairWallLaw d) n))
        (pairQuantileChart (expMeasure 1) (collisionExitVector expPairLaw n)),
      pairQuantileChart_coeFn_of_ae _ (collisionExitVector_coeFn_profile (pairWallLaw d) n),
      pairQuantileChart_coeFn_of_ae _ (collisionExitVector_coeFn_profile expPairLaw n)]
      with w h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hbd : ∀ d w, |Φd d w| ≤ 1 := fun d w => abs_exitProfile_le_one n (abs_pairContrast_le_one _)
  have hb0 : ∀ w, |Φ0 w| ≤ 1 := fun w => abs_exitProfile_le_one n (abs_pairContrast_le_one _)
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), c d < c0 + 1 := hc.eventually (Iio_mem_nhds (lt_add_one c0))
  have hsq : Tendsto (fun d => ‖pairQuantileChart (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
        (collisionExitVector (pairWallLaw d) n)
        - pairQuantileChart (expMeasure 1) (collisionExitVector expPairLaw n)‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simp_rw [hrepr]
    have h := tendsto_integral_filter_of_dominated_convergence (μ := unitSquareLaw)
      (l := 𝓝[>] (0 : ℝ))
      (F := fun d w => ‖((c d * Φd d w : ℝ) : ℂ) - ((c0 * Φ0 w : ℝ) : ℂ)‖ ^ 2)
      (f := fun _ => 0) (fun _ => (c0 + 1 + c0) ^ 2)
      (Eventually.of_forall fun d => ((Complex.measurable_ofReal.comp (measurable_const.mul
        (measurable_exitProfile_quantile n _))).sub (Complex.measurable_ofReal.comp
          (measurable_const.mul (measurable_exitProfile_quantile n _)))).norm.pow_const 2
            |>.aestronglyMeasurable)
      (by
        filter_upwards [hev] with d hd
        refine Eventually.of_forall fun w => ?_
        have hcd : 0 ≤ c d := inv_nonneg.mpr (Real.sqrt_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hcd, abs_of_nonneg hc0]
        have h1 : c d * |Φd d w| ≤ c0 + 1 :=
          (mul_le_of_le_one_right hcd (hbd d w)).trans hd.le
        have h2 : c0 * |Φ0 w| ≤ c0 := mul_le_of_le_one_right hc0 (hb0 w)
        linarith)
      (integrable_const _)
      (by
        filter_upwards [ae_mem_unitSquare] with w hw
        have h1 : Tendsto (fun d => c d * Φd d w) (𝓝[>] 0) (𝓝 (c0 * Φ0 w)) :=
          hc.mul (tendsto_comp_pairContrast_quantile (continuous_exitProfile n) hw)
        have h2 := ((Complex.continuous_ofReal.tendsto _).comp h1).sub
          (tendsto_const_nhds (x := ((c0 * Φ0 w : ℝ) : ℂ)))
        have h3 : Tendsto (fun d => ‖((c d * Φd d w : ℝ) : ℂ) - ((c0 * Φ0 w : ℝ) : ℂ)‖ ^ 2)
            (𝓝[>] 0) (𝓝 (‖((c0 * Φ0 w : ℝ) : ℂ) - ((c0 * Φ0 w : ℝ) : ℂ)‖ ^ 2)) := h2.norm.pow 2
        rw [sub_self, norm_zero, zero_pow two_ne_zero] at h3
        exact h3)
    simpa using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := hsq.sqrt
  simp only [Real.sqrt_zero] at h
  exact h.congr fun d => Real.sqrt_sq (norm_nonneg _)

/-- The continuum exit norms `√w_n ≤ 26/(n + 1)²` are summable. -/
theorem summable_norm_hodgeExitVector :
    Summable fun n => ‖collisionExitVector expPairLaw n‖ := by
  have hle : ∀ n : ℕ, ‖collisionExitVector expPairLaw n‖ ≤ 26 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro n
    have hw := norm_hodgeExitVector_sq n
    rw [PrimeHodgeHistory.w_formula] at hw
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hD : ((n : ℝ) + 1) ^ 4 ≤ ((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 5 : ℕ) : ℝ) *
        ((2 * n + 7 : ℕ) : ℝ) * ((2 * n + 9 : ℕ) : ℝ) := by
      push_cast
      calc ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 1) := by
            ring
        _ ≤ (2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7) * (2 * n + 9) := by
            gcongr <;> linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsq : ‖collisionExitVector expPairLaw n‖ ^ 2 ≤ (26 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2 := by
      rw [hw]
      push_cast
      rw [mul_pow, inv_pow, ← pow_mul]
      calc (630 : ℝ) / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7) * (2 * n + 9))
          ≤ 630 / ((n : ℝ) + 1) ^ 4 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact_mod_cast hD
        _ ≤ 26 ^ 2 * (((n : ℝ) + 1) ^ (2 * 2))⁻¹ := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle ?_
  exact ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)).mul_left 26

theorem hasSum_norm_pairLanding_exit_sq (d : ℝ) :
    HasSum (fun n => ‖pairQuantileChart (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      (collisionExitVector (pairWallLaw d) n)‖ ^ 2) 1 := by
  have h := hasSum_norm_collisionExitVector_sq (pairWallLaw d) (ae_pos_pairWallLaw d)
  rw [norm_collisionState _ (collisionMass_pairWallLaw_pos d), one_pow] at h
  exact h.congr_fun fun n => by rw [norm_pairQuantileChart_apply]

theorem hasSum_norm_wallLanding_exit_sq :
    HasSum (fun n => ‖pairQuantileChart (expMeasure 1)
      (collisionExitVector expPairLaw n)‖ ^ 2) 1 := by
  have h := hasSum_norm_collisionExitVector_sq expPairLaw hν_expPair
  rw [norm_collisionState _ collisionMass_expPair_pos, one_pow] at h
  exact h.congr_fun fun n => by rw [norm_pairQuantileChart_apply]

/-- **Theorem CCRHD-D, wall landing.**  Under the quantile charts the literal prime-pair record
lands on the continuum Hodge collision record in trace norm:
`‖(1 ⊗ W_{μ_d} J_d) 𝖳_d (1 ⊗ W_{μ_d} J_d)* - (1 ⊗ W_μ) 𝖳 (1 ⊗ W_μ)*‖₁ → 0`. -/
theorem tendsto_traceNorm_pairLandingRecord_sub :
    Tendsto (fun d => traceNorm (HistoryL2 (Lp ℂ 2 unitSquareLaw))
      (pairLandingRecord d - wallCollisionRecord)) (𝓝[>] 0) (𝓝 0) := by
  have hbs : Summable fun n => ‖pairQuantileChart (expMeasure 1)
      (collisionExitVector expPairLaw n)‖ :=
    summable_norm_hodgeExitVector.congr fun n => by rw [norm_pairQuantileChart_apply]
  have hlim := tendsto_tsum_norm_sub_sq (fun d => hasSum_norm_pairLanding_exit_sq d)
    hasSum_norm_wallLanding_exit_sq hbs tendsto_pairQuantileChart_exit
  have hup := ((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul 2
  rw [Real.sqrt_zero, mul_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => traceNorm_nonneg _) fun d => ?_
  have h := traceNorm_recordOp_sub_le
    (summable_norm_pairQuantileChart_exit _ (ae_pos_pairWallLaw d))
    (summable_norm_pairQuantileChart_exit _ hν_expPair)
  rw [(hasSum_norm_pairLanding_exit_sq d).tsum_eq, hasSum_norm_wallLanding_exit_sq.tsum_eq,
    Real.sqrt_one] at h
  refine h.trans (le_of_eq ?_)
  simp only [Function.comp_apply]
  ring

/-- **Theorem CCRHD-D, charted form.**  For `d > 0` the literal record charted by `W_{μ_d} J_d`
converges in trace norm to the continuum record charted by `W_μ`. -/
theorem tendsto_traceNorm_primePairRecord_charted :
    ∀ ε > 0, ∀ᶠ d in 𝓝[>] (0 : ℝ), ∀ hd : 0 < d,
      traceNorm (HistoryL2 (Lp ℂ 2 unitSquareLaw))
        (historyMap (fun _ => 1) (fun _ => norm_one.le) (primePairQuantileChart hd) ∘L
            primePairRecord hd ∘L
              adjoint (historyMap (fun _ => 1) (fun _ => norm_one.le) (primePairQuantileChart hd))
          - historyMap (fun _ => 1) (fun _ => norm_one.le) (pairQuantileChart (expMeasure 1)) ∘L
            hodgeCollisionRecord ∘L
              adjoint (historyMap (fun _ => 1) (fun _ => norm_one.le)
                (pairQuantileChart (expMeasure 1)))) < ε := by
  intro ε hε
  filter_upwards [(tendsto_order.mp tendsto_traceNorm_pairLandingRecord_sub).2 ε hε] with d hd hd'
  rw [primePairRecord_charted hd', hodgeCollisionRecord_charted]
  exact hd

/-! ## Zero residual and the certificate -/

/-- **(CCRHD.21), transport of zero residual.**  A bounded intertwiner `U S = S' U` carries a zero
survival residual `Sᴺ Ω → 0` to `S'ᴺ (U Ω) → 0`; no bounded intertwiner of the source colligation
reaches a state of nonvanishing residual. -/
theorem tendsto_residual_of_intertwiner {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {S : E →L[ℂ] E} {S' : F →L[ℂ] F} {U : E →L[ℂ] F} (hU : U ∘L S = S' ∘L U) {Ω : E}
    (hΩ : Tendsto (fun N => (S ^ N) Ω) atTop (𝓝 0)) :
    Tendsto (fun N => (S' ^ N) (U Ω)) atTop (𝓝 0) := by
  have hc : ∀ x, U (S x) = S' (U x) := fun x => by
    have := congrArg (fun A : E →L[ℂ] F => A x) hU
    simpa using this
  have h : ∀ N, (S' ^ N) (U Ω) = U ((S ^ N) Ω) := by
    intro N
    induction N with
    | zero => simp [one_def]
    | succ N ih =>
      rw [pow_succ' S' N, mul_def, comp_apply, ih, pow_succ' S N, mul_def, comp_apply, hc]
  simp_rw [h]
  have := (U.continuous.tendsto 0).comp hΩ
  rw [map_zero] at this
  exact this

/-- **ULF-CCRHD-001.**  The Hodge collision state `Ω_H = √(105/8) δ(1 - δ²)` is a unit vector whose
contrast law is `Beta(3/2, 3)`; its survival/exit colligation has an isometric observability map,
survival masses `m_n` and exit masses `w_n`; the dephased record `𝖳 = ⊕ₙ |e_n⟩⟨e_n|` is a positive
nuclear operator with `tr 𝖳 = ‖𝖳‖₁ = 1` and `‖𝖳‖ = 2/3`, the trace-norm dephasing of the lifted
pure state, invariant under the swap; every literal prime-pair record `𝖳_d` is nuclear with unit
trace and norm below one, and lands on `𝖳` in trace norm under the quantile charts. -/
theorem cayley_collision_record_homotopy_defect :
    ‖hodgeCollisionState‖ = 1 ∧
      Measure.map (fun z : ℝ × ℝ => cayleyContrast z.1 z.2 ^ 2)
        (expPairLaw.withDensity fun z =>
          ENNReal.ofReal (hodgeCollisionAmplitude (cayleyContrast z.1 z.2) ^ 2)) = phaseBetaLaw ∧
      (∀ f, ‖collisionObservability expPairLaw hν_expPair f‖ = ‖f‖) ∧
      (∀ n, ‖(collisionSurvival expPairLaw ^ n) hodgeCollisionState‖ ^ 2 = PrimeHodgeHistory.m n ∧
        ‖collisionExitVector expPairLaw n‖ ^ 2 = PrimeHodgeHistory.w n) ∧
      hodgeCollisionRecord.IsPositive ∧ MemSchattenClass 1 hodgeCollisionRecord ∧
      opTrace hodgeCollisionRecord = 1 ∧
      traceNorm (HistoryL2 (Lp ℂ 2 expPairLaw)) hodgeCollisionRecord = 1 ∧
      ‖hodgeCollisionRecord‖ = 2 / 3 ∧
      Tendsto (fun N => traceNorm (HistoryL2 (Lp ℂ 2 expPairLaw)) (hodgeCollisionRecord -
        ∑ n ∈ Finset.range N, historyGrade n ∘L
          historyRankOne (collisionObservability expPairLaw hν_expPair hodgeCollisionState) ∘L
            historyGrade n)) atTop (𝓝 0) ∧
      historySwap measurePreserving_swap_expPair ∘L hodgeCollisionRecord ∘L
        historySwap measurePreserving_swap_expPair = hodgeCollisionRecord ∧
      (∀ d (hd : 0 < d), (primePairRecord hd).IsPositive ∧ MemSchattenClass 1 (primePairRecord hd) ∧
        opTrace (primePairRecord hd) = 1 ∧ ‖primePairRecord hd‖ < 1) ∧
      Tendsto (fun d => traceNorm (HistoryL2 (Lp ℂ 2 unitSquareLaw))
        (pairLandingRecord d - wallCollisionRecord)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨h1, h2, -, h4, h5, h6, -⟩ := hodgeCollisionRecord_nuclear
  refine ⟨norm_hodgeCollisionState, map_hodgeCollision_eq_phaseBetaLaw,
    (collisionObservability_isometry expPairLaw hν_expPair).1,
    fun n => ⟨norm_survival_pow_hodgeCollisionState_sq n, norm_hodgeExitVector_sq n⟩,
    h1, h2, h4, h5, h6, tendsto_traceNorm_collisionRecord_sub expPairLaw hν_expPair,
    historySwap_conj_collisionRecord measurePreserving_swap_expPair hν_expPair,
    fun d hd => ?_, tendsto_traceNorm_pairLandingRecord_sub⟩
  obtain ⟨g1, g2, g3, -, -, g6, -⟩ := primePairRecord_nuclear hd
  exact ⟨g1, g2, g3, g6⟩

end GaloisForLFunctions.HTGeometry
