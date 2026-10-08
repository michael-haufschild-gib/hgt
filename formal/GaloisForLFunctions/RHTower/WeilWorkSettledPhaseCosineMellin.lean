import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellin
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialGaussian

/-!
# Mellin transforms of the actual source cosine twists

Absolute convergence comes from the source coefficient majorant. No positivity
of a filtered source, and no sign of its Dirichlet coefficients, is assumed.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceCosineCoeff (lam : ℕ → ℝ) (r : ℝ) (n : ℕ) : ℂ :=
  sourceSquareCoeff lam n * (Real.cos (2 * Real.pi * (n * r)) : ℂ)

def sourceCosineSeries (lam : ℕ → ℝ) (r : ℝ) (s : ℂ) : ℂ :=
  LSeries (sourceCosineCoeff lam r) s

def sourceCosineProfile (lam : ℕ → ℝ) (r t : ℝ) : ℂ :=
  ∑' n : ℕ, sourceCosineCoeff lam r n *
    (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ)

def sourceScaledCosineProfile (lam : ℕ → ℝ) (r t : ℝ) : ℂ :=
  sourceCosineProfile lam r (r ^ 2 * t)

@[simp] theorem sourceCosineCoeff_zero (lam : ℕ → ℝ) (r : ℝ) :
    sourceCosineCoeff lam r 0 = 0 := by simp [sourceCosineCoeff]

theorem norm_sourceCosineCoeff_le (lam : ℕ → ℝ) (r : ℝ) (n : ℕ) :
    ‖sourceCosineCoeff lam r n‖ ≤ ‖sourceSquareCoeff lam n‖ := by
  simp only [sourceCosineCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg (sourceSquareCoeff lam n))
    (Real.abs_cos_le_one (2 * Real.pi * (n * r)))

theorem sourceCosine_norm_div_summable {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (r : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖sourceCosineCoeff lam r n‖ / (n : ℝ) ^ s.re) :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => div_le_div_of_nonneg_right (norm_sourceCosineCoeff_le lam r n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (source_norm_div_summable hW hs)

theorem hasSum_sourceCosineProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => sourceCosineCoeff lam r n *
      (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ)) (sourceCosineProfile lam r t) := by
  apply Summable.hasSum
  refine (hasSum_sourceGaussianProfile hW ht).summable.norm.of_norm_bounded fun n => ?_
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_sourceCosineCoeff_le lam r n) (norm_nonneg _)

theorem mellinConvergent_sourceCosineProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (r : ℝ) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (sourceCosineProfile lam r) (s / 2) := by
  apply mellinConvergent_of_exponential_series
    (a := sourceCosineCoeff lam r) (p := fun n : ℕ => Real.pi * (n : ℝ) ^ 2)
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl (sourceCosineCoeff_zero lam r)
    · exact Or.inr (mul_pos Real.pi_pos (sq_pos_of_pos (by exact_mod_cast hn)))
  · rw [div_ofNat_re]
    linarith
  · intro t ht
    simpa only [neg_mul] using hasSum_sourceCosineProfile hW r ht
  · refine ((sourceCosine_norm_div_summable hW r hs).div_const
      (Real.pi ^ (s.re / 2))).congr fun n => ?_
    rw [div_ofNat_re, Real.mul_rpow Real.pi_pos.le (sq_nonneg _),
      ← Real.rpow_natCast_mul (Nat.cast_nonneg n), Nat.cast_ofNat,
      mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

theorem mellin_sourceCosineProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (r : ℝ) {s : ℂ} (hs : 1 < s.re) :
    mellin (sourceCosineProfile lam r) (s / 2) = Gammaℝ s * sourceCosineSeries lam r s := by
  have hn : Summable (fun n : ℕ => ‖sourceCosineCoeff lam r n‖ / |(n : ℝ)| ^ s.re) := by
    simpa only [Nat.abs_cast] using sourceCosine_norm_div_summable hW r hs
  have hF (t : ℝ) (ht : t ∈ Ioi 0) :
      HasSum (fun n : ℕ => if (n : ℝ) = 0 then 0 else sourceCosineCoeff lam r n *
        (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ)) (sourceCosineProfile lam r t) := by
    convert hasSum_sourceCosineProfile hW r ht using 1
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne']
  have h := hasSum_mellin_pi_mul_sq (lt_trans (by norm_num) hs) hF hn
  have he (n : ℕ) : Gammaℝ s * sourceCosineCoeff lam r n / ((|(n : ℝ)| : ℝ) : ℂ) ^ s =
      Gammaℝ s * LSeries.term (sourceCosineCoeff lam r) s n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [LSeries.term, hn.ne', Nat.abs_cast, mul_div_assoc]
  simp_rw [he] at h
  rw [← h.tsum_eq, tsum_mul_left]
  rfl

theorem sourceScaledCosineProfile_eq_twisted {lam : ℕ → ℝ} {r t : ℝ} (ht : 0 < t) :
    sourceScaledCosineProfile lam r t =
      sourceTwistedGaussianSum lam (Real.sqrt (4 * Real.pi / t)) r := by
  unfold sourceScaledCosineProfile sourceCosineProfile sourceCosineCoeff sourceTwistedGaussianSum
  apply tsum_congr
  intro n
  have he : GaussZeroSum.gaussW (Real.sqrt (4 * Real.pi / t)) (n * r) =
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * (r ^ 2 * t)) := by
    unfold GaussZeroSum.gaussW
    rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * Real.pi / t)]
    congr 1
    field_simp
  rw [he]
  push_cast
  ring

theorem mellinConvergent_sourceScaledCosineProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (sourceScaledCosineProfile lam r) (s / 2) :=
  (MellinConvergent.comp_mul_left (sq_pos_of_pos hr)).mpr
    (mellinConvergent_sourceCosineProfile hW r hs)

theorem re_mellin_sourceScaledCosineProfile (lam : ℕ → ℝ) {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    (mellin (sourceScaledCosineProfile lam r) ((σ : ℂ) / 2)).re =
      (r ^ 2) ^ (-(σ / 2)) * (mellin (sourceCosineProfile lam r) ((σ : ℂ) / 2)).re := by
  change (mellin (fun t => sourceCosineProfile lam r (r ^ 2 * t)) ((σ : ℂ) / 2)).re = _
  rw [mellin_comp_mul_left _ _ (sq_pos_of_pos hr)]
  have he : -((σ : ℂ) / 2) = ((-(σ / 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_cpow (sq_nonneg r)]
  simp

theorem exists_norm_sourceScaledCosineProfile_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖sourceScaledCosineProfile lam r t‖ ≤ C / t := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_source_twisted_gaussW_le hW hr
  refine ⟨C * (4 * Real.pi), by positivity, fun t ht => ?_⟩
  rw [sourceScaledCosineProfile_eq_twisted ht]
  have h := (hC (Real.sqrt (4 * Real.pi / t)) (Real.sqrt_pos.mpr (by positivity))).2
  simpa only [sourceTwistedGaussianSum, Real.sq_sqrt (by positivity : 0 ≤ 4 * Real.pi / t),
    ← mul_div_assoc] using h

end RHTower.WeilSingularArithmetic
