import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Extremal
import GaloisForLFunctions.HTGeometry.ArithmeticWindowPhase

open Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

noncomputable section

variable {n : ℕ}

/-- Multiplicative linear-form approximants at exponent `eps`. -/
def multiplicativeLinearFormBadSet (y : Fin n → ℝ) (eps : ℝ) :
    Set (Fin n → ℤ) :=
  {q | ∃ p : ℤ,
    |dotProd q y + (p : ℝ)| * PiPlus q ≤ PiPlus q ^ (-eps)}

/-- Outside the very-well-multiplicatively-approximable locus, every
strict product-height improvement has only finitely many characters. -/
theorem finite_multiplicativeLinearFormBadSet_of_not_vwma
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    (multiplicativeLinearFormBadSet y eps).Finite := by
  by_contra hinfinite
  apply hy
  exact ⟨eps, heps, by
    simpa [multiplicativeLinearFormBadSet] using hinfinite⟩

/-- A finite exceptional character set can be absorbed into one product-
height threshold.  Above it every inhomogeneous integer linear form obeys
the sharp strong-extremality lower bound. -/
theorem exists_eventual_multiplicativeLinearForm_lower
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ q : Fin n → ℤ, R < PiPlus q → ∀ p : ℤ,
      PiPlus q ^ (-eps) < |dotProd q y + (p : ℝ)| * PiPlus q := by
  have hfinite := finite_multiplicativeLinearFormBadSet_of_not_vwma hy heps
  obtain ⟨R₀, hR₀⟩ :=
    (hfinite.image PiPlus).exists_le
  refine ⟨max 1 R₀, le_max_left _ _, ?_⟩
  intro q hq p
  by_contra hnot
  have hbad : q ∈ multiplicativeLinearFormBadSet y eps := by
    exact ⟨p, le_of_not_gt hnot⟩
  have hbound : PiPlus q ≤ R₀ := hR₀ (PiPlus q) ⟨q, hbad, rfl⟩
  exact (not_le_of_gt hq) (hbound.trans (le_max_right _ _))

/-- **Quantitative moving-window character suppression.**  For every
strongly extremal frequency packet, all sufficiently high multiplicative-
height Fourier characters have uniformly small mean on every translated
time window.  No minimum coordinate gap occurs; the invariant is the full
integer-character product height. -/
theorem exists_eventual_characterWindowSuppression
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ q : Fin n → ℤ, R < PiPlus q →
      ∀ u T : ℝ, 0 < T →
        ‖(1 / (T : ℂ)) *
            ∫ t in u..(u + T),
              Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
            PiPlus q ^ (-eps) ≤
          2 * PiPlus q / T := by
  obtain ⟨R, hR, hlower⟩ :=
    exists_eventual_multiplicativeLinearForm_lower hy heps
  refine ⟨R, hR, ?_⟩
  intro q hq u T hT
  have hprod := hlower q hq 0
  simp only [Int.cast_zero, add_zero] at hprod
  have hpowpos : 0 < PiPlus q ^ (-eps) :=
    Real.rpow_pos_of_pos (PiPlus_pos q) _
  have hbeta : dotProd q y ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero, zero_mul] at hprod
    exact (not_lt_of_ge hpowpos.le) hprod
  have habs : 0 < |dotProd q y| := abs_pos.mpr hbeta
  have hosc := norm_integral_exp_window_le hbeta u T
  have hoscMul :
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          |dotProd q y| ≤ 2 := by
    exact (le_div_iff₀ habs).mp hosc
  have hweighted :
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          PiPlus q ^ (-eps) ≤ 2 * PiPlus q := by
    calc
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          PiPlus q ^ (-eps) ≤
        ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          (|dotProd q y| * PiPlus q) :=
        mul_le_mul_of_nonneg_left hprod.le (norm_nonneg _)
      _ =
        (‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
            |dotProd q y|) * PiPlus q := by ring
      _ ≤ 2 * PiPlus q :=
        mul_le_mul_of_nonneg_right hoscMul (le_trans zero_le_one (one_le_PiPlus q))
  rw [norm_mul, norm_div, norm_one, Complex.norm_real,
    Real.norm_of_nonneg hT.le]
  calc
    (1 / T *
        ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖) *
          PiPlus q ^ (-eps) =
      (1 / T) *
        (‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
            PiPlus q ^ (-eps)) := by ring
    _ ≤ (1 / T) * (2 * PiPlus q) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = 2 * PiPlus q / T := by field_simp

/-- **Strong-extremality spectral-action dichotomy.**  Every real frequency
packet is either very well multiplicatively approximable, or every
strict exponent admits a uniform translated-window suppression law for all
sufficiently high Fourier characters. -/
theorem vwma_or_eventual_characterWindowSuppression (y : Fin n → ℝ) :
    VWMA y ∨
      ∀ eps : ℝ, 0 < eps →
        ∃ R : ℝ, 1 ≤ R ∧ ∀ q : Fin n → ℤ, R < PiPlus q →
          ∀ u T : ℝ, 0 < T →
            ‖(1 / (T : ℂ)) *
                ∫ t in u..(u + T),
                  Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
                PiPlus q ^ (-eps) ≤
              2 * PiPlus q / T := by
  by_cases hy : VWMA y
  · exact Or.inl hy
  · exact Or.inr fun eps heps =>
      exists_eventual_characterWindowSuppression hy heps

end

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
