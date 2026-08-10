import GaloisForLFunctions.RHTower.GaussSandwich

/-!
# The relative form of the Fourier diagonal

Folding `G = p B D B^(-2) D* B` puts the whole scalar `p |d_n|²` outside a quadratic form in the
single vector `S*(b_p)`, so the moving-translation error enters *multiplied* by `p |d_n|²` rather
than divided by `|d_n|`.  The period average of the exact target is

`⟪T_δ b, B^(-2) T_δ b⟫ = ∫ b^(-2)(z) b(z-δ)² dz = ∫ a_δ(z-δ) dz = ∫ a_δ = A_1(δ)`,

the last step by translation invariance of Haar measure on the circle.  The result is an explicit
bound in which the vanishing factor multiplies the main term, which is what a logarithmic mean of
the diagonal consumes.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The period average of the moving amplitude -/

theorem fourierCoeff_zero_eq_integral (f : AddCircle (1 : ℝ) → ℂ) :
    fourierCoeff f 0 = ∫ z, f z ∂AddCircle.haarAddCircle := by
  rw [fourierCoeff]
  simp

theorem integral_gaussMovingAmplitudeCircle {p s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ z, gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)) z ∂AddCircle.haarAddCircle)
      = ((gaussAmplitudeSegment p 1 s : ℝ) : ℂ) := by
  rw [← fourierCoeff_zero_eq_integral]
  simpa using fourierCoeff_gaussAmplitudePow_zero (p := p) hs0 hs1 1

/-! ## The exact target of the quadratic form -/

theorem inner_translate_gaussPrimeScale {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) :
    (inner ℂ (gaussTranslationBlock δ (gaussPrimeScaleBlock hp (fourierLp 2 0)))
        (gaussPrimeScaleInvSqBlock hp
          (gaussTranslationBlock δ (gaussPrimeScaleBlock hp (fourierLp 2 0)))) : ℂ)
      = ∫ z, gaussMovingAmplitudeCircle p δ z ∂AddCircle.haarAddCircle := by
  have hb : ((gaussPrimeScaleBlock hp (fourierLp 2 0) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => gaussPrimeScaleCircle p z := by
    refine (gaussPrimeScaleBlock_coeFn hp _).trans ?_
    filter_upwards [coeFn_fourierLp_zero] with z hz
    rw [hz, mul_one]
  have hTb : ((gaussTranslationBlock δ (gaussPrimeScaleBlock hp (fourierLp 2 0)) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => gaussPrimeScaleCircle p (z - δ) := by
    refine (coeFn_gaussTranslationBlock δ _).trans ?_
    filter_upwards [ae_eq_comp_sub δ hb] with z hz
    exact hz
  have hPTb : ((gaussPrimeScaleInvSqBlock hp
        (gaussTranslationBlock δ (gaussPrimeScaleBlock hp (fourierLp 2 0))) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleInvSqCircle p z * gaussPrimeScaleCircle p (z - δ) := by
    refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ _).trans ?_
    filter_upwards [hTb] with z hz
    rw [hz]
  rw [MeasureTheory.L2.inner_def]
  rw [← integral_sub_right_eq_self
    (fun z => gaussMovingAmplitudeCircle p δ z) δ]
  refine integral_congr_ae ?_
  filter_upwards [hTb, hPTb] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', gaussPrimeScaleCircle_real,
    gaussMovingAmplitudeCircle, sub_add_cancel]
  ring

/-! ## The folded diagonal at a lattice frequency -/

theorem inner_fourierLp_gaussQuasiInnerG_fold {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {n : ℤ} (hn : n ≠ 0) :
    (inner ℂ (fourierLp 2 n) (gaussQuasiInnerG hm k p (fourierLp 2 n)) : ℂ)
      = (((p : ℝ) : ℂ) *
          (gaussSampleValue k p n * starRingEnd ℂ (gaussSampleValue k p n))) *
        inner ℂ (gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp (fourierLp 2 0)))
          (gaussPrimeScaleInvSqBlock hp
            (gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp (fourierLp 2 0)))) := by
  have hBe : gaussPrimeScaleBlock hp (fourierLp 2 n)
      = fourierMulBlock n (gaussPrimeScaleBlock hp (fourierLp 2 0)) := by
    rw [← fourierMulBlock_fourierLp_zero n, gaussPrimeScaleBlock_comm]
  have hDs : gaussDiagonalBlockStar hm k p (gaussPrimeScaleBlock hp (fourierLp 2 n))
      = starRingEnd ℂ (gaussSampleValue k p n) •
        fourierMulBlock n
          (gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp (fourierLp 2 0))) := by
    rw [hBe, gaussDiagonalBlockStar_fourierMulBlock hm k p hn]
  rw [inner_fourierLp_gaussQuasiInnerG hm k p hp, hDs, map_smul,
    gaussPrimeScaleInvSqBlock_comm, inner_smul_left, inner_smul_right,
    fourierMulBlock_inner, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-! ## The quadratic form is stable -/

theorem norm_inner_gaussPrimeScaleInvSq_sub_le {p : ℝ} (hp : 1 < p)
    (w b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖(inner ℂ w (gaussPrimeScaleInvSqBlock hp w) : ℂ) -
        inner ℂ b (gaussPrimeScaleInvSqBlock hp b)‖
      ≤ ‖w - b‖ * (‖w‖ + ‖b‖) := by
  have hP : ∀ v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      ‖gaussPrimeScaleInvSqBlock hp v‖ ≤ ‖v‖ := by
    intro v
    refine (gaussPrimeScaleInvSqBlock hp).le_opNorm v |>.trans ?_
    exact mul_le_of_le_one_left (norm_nonneg v) (norm_gaussPrimeScaleInvSqBlock_le hp)
  have hsplit : (inner ℂ w (gaussPrimeScaleInvSqBlock hp w) : ℂ) -
      inner ℂ b (gaussPrimeScaleInvSqBlock hp b)
      = inner ℂ (w - b) (gaussPrimeScaleInvSqBlock hp w) +
        inner ℂ b (gaussPrimeScaleInvSqBlock hp (w - b)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(inner ℂ (w - b) (gaussPrimeScaleInvSqBlock hp w) : ℂ)‖ ≤ ‖w - b‖ * ‖w‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hP w) (norm_nonneg _))
  have h2 : ‖(inner ℂ b (gaussPrimeScaleInvSqBlock hp (w - b)) : ℂ)‖ ≤ ‖b‖ * ‖w - b‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hP (w - b)) (norm_nonneg _))
  calc ‖(inner ℂ (w - b) (gaussPrimeScaleInvSqBlock hp w) : ℂ)‖ +
      ‖(inner ℂ b (gaussPrimeScaleInvSqBlock hp (w - b)) : ℂ)‖
      ≤ ‖w - b‖ * ‖w‖ + ‖b‖ * ‖w - b‖ := add_le_add h1 h2
    _ = ‖w - b‖ * (‖w‖ + ‖b‖) := by ring

/-! ## The relative diagonal -/

/-- The `L²` defect of the moving translation at the lattice frequency `n`. -/
def gaussFoldDefect {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (n : ℤ) : ℝ :=
  ‖gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp (fourierLp 2 0)) -
    gaussTranslationBlock ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
      (gaussPrimeScaleBlock hp (fourierLp 2 0))‖

/-- **The relative form of the diagonal.**  The deviation of `⟪e_n, G e_n⟫` from
`p |d_n|² A_1(δ_n)` is bounded by the step scalar times a factor built only from the moving
translation defect. -/
theorem norm_inner_gaussQuasiInnerG_sub_amplitude_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {n : ℤ} (hn : n ≠ 0) :
    ‖(inner ℂ (fourierLp 2 n) (gaussQuasiInnerG hm k p (fourierLp 2 n)) : ℂ) -
        (((p : ℝ) : ℂ) *
            (gaussSampleValue k p n * starRingEnd ℂ (gaussSampleValue k p n))) *
          ((gaussAmplitudeSegment (p : ℝ) 1
            (Int.fract (gaussSamplePhase m p n)) : ℝ) : ℂ)‖
      ≤ ‖((p : ℝ) : ℂ) *
            (gaussSampleValue k p n * starRingEnd ℂ (gaussSampleValue k p n))‖ *
          (gaussFoldDefect hm k p hp n *
            (gaussFoldDefect hm k p hp n +
              2 * ‖gaussPrimeScaleBlock hp
                (fourierLp 2 (0 : ℤ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)) := by
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (fourierLp 2 0) with hbdef
  set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) with hδ
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockOf hm k p n b with hw
  set σ : ℂ := ((p : ℝ) : ℂ) *
    (gaussSampleValue k p n * starRingEnd ℂ (gaussSampleValue k p n)) with hσ
  have hs0 : 0 ≤ Int.fract (gaussSamplePhase m p n) := Int.fract_nonneg _
  have hs1 : Int.fract (gaussSamplePhase m p n) < 1 := Int.fract_lt_one _
  have hδfract : δ = ((Int.fract (gaussSamplePhase m p n) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [hδ, coe_fract_eq]
  have htarget : (inner ℂ (gaussTranslationBlock δ b)
      (gaussPrimeScaleInvSqBlock hp (gaussTranslationBlock δ b)) : ℂ)
      = ((gaussAmplitudeSegment (p : ℝ) 1
          (Int.fract (gaussSamplePhase m p n)) : ℝ) : ℂ) := by
    rw [hbdef, inner_translate_gaussPrimeScale hp δ, hδfract,
      integral_gaussMovingAmplitudeCircle hs0 hs1]
  have hnormT : ‖gaussTranslationBlock δ b‖ = ‖b‖ := (gaussTranslationBlock δ).norm_map b
  have hdef : gaussFoldDefect hm k p hp n = ‖w - gaussTranslationBlock δ b‖ := rfl
  have hwnorm : ‖w‖ ≤ gaussFoldDefect hm k p hp n + ‖b‖ := by
    have h : ‖w - gaussTranslationBlock δ b + gaussTranslationBlock δ b‖
        ≤ ‖w - gaussTranslationBlock δ b‖ + ‖gaussTranslationBlock δ b‖ := norm_add_le _ _
    rw [sub_add_cancel, hnormT] at h
    rw [hdef]
    exact h
  rw [inner_fourierLp_gaussQuasiInnerG_fold hm k p hp hn, ← hσ, ← hw, ← htarget,
    ← mul_sub, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_inner_gaussPrimeScaleInvSq_sub_le hp w (gaussTranslationBlock δ b)).trans ?_
  rw [← hdef, hnormT]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  linarith

/-! ## The defect vanishes -/

/-- **The moving-translation defect of the folded diagonal vanishes** along every escaping
frequency sequence. -/
theorem tendsto_gaussFoldDefect {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ => gaussFoldDefect hm k p hp (ι n)) atTop (nhds 0) := by
  have hdecay : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff (((gaussPrimeScaleBlock hp (fourierLp 2 0) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ 4 * (p : ℝ) ^ (0 + 1) / (1 + (j.natAbs : ℝ)) := by
    intro n j
    have hb := norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow hp
      (Int.fract_nonneg (gaussSamplePhase m p (ι n)))
      (Int.fract_lt_one (gaussSamplePhase m p (ι n))) 0 j
    have hzero : (gaussMovingAmplitudeBlock hp
        ((Int.fract (gaussSamplePhase m p (ι n)) : ℝ) : AddCircle (1 : ℝ)) ^ 0)
          (fourierLp 2 0)
        = (fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
      rw [pow_zero]
      rfl
    rwa [hzero] at hb
  have h := tendsto_norm_gaussShiftedBlockOf_sub_rotation_family hm k p hι
    (fun _ => gaussPrimeScaleBlock hp (fourierLp 2 0)) hdecay
  refine h.congr fun n => ?_
  rw [gaussFoldDefect, gaussRotationBlock_eq_translation]

/-- The whole vanishing cofactor of the relative diagonal. -/
theorem tendsto_gaussRelativeDiagonalFactor {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      gaussFoldDefect hm k p hp (ι n) *
        (gaussFoldDefect hm k p hp (ι n) +
          2 * ‖gaussPrimeScaleBlock hp
            (fourierLp 2 (0 : ℤ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖))
      atTop (nhds 0) := by
  have hd := tendsto_gaussFoldDefect hm k p hp hι
  have hsum := hd.add (tendsto_const_nhds (x :=
    2 * ‖gaussPrimeScaleBlock hp
      (fourierLp 2 (0 : ℤ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)
    (f := (atTop : Filter ℕ)))
  have := hd.mul hsum
  simpa using this

end

end RHTower