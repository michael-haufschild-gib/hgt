import GaloisForLFunctions.RHTower.InfiniteMobiusCausalShift
import GaloisForLFunctions.RHTower.XiThetaSquareRateLaplace

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators LSeries.notation Moebius

noncomputable section
namespace RHTower

theorem causalLaplaceIntegral_sub_shift
    (x h : ℝ) (f : ℝ → ℂ) :
    causalLaplaceIntegral x (fun y => f (y - h)) =
      Complex.exp (-(Real.pi * x * h : ℝ)) * causalLaplaceIntegral x f := by
  unfold causalLaplaceIntegral
  have hweighted :
      causalLaplaceWeighted x (fun y => f (y - h)) =
        fun y => Complex.exp (-(Real.pi * x * h : ℝ)) *
          causalLaplaceWeighted x f (y - h) := by
    funext y
    unfold causalLaplaceWeighted
    change Complex.exp (-(Real.pi * x * y : ℝ)) * f (y - h) = _
    calc
      Complex.exp (-(Real.pi * x * y : ℝ)) * f (y - h) =
          (Complex.exp (-(Real.pi * x * h : ℝ)) *
            Complex.exp (-(Real.pi * x * (y - h) : ℝ))) * f (y - h) := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        ring
      _ = Complex.exp (-(Real.pi * x * h : ℝ)) *
          (Complex.exp (-(Real.pi * x * (y - h) : ℝ)) * f (y - h)) := by ring
  rw [hweighted, integral_const_mul]
  congr 1
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self (fun y : ℝ => causalLaplaceWeighted x f y) (-h))

theorem additiveTranslationUnitary_neg_ae
    (h : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun t : ℝ => MellinL2.additiveTranslationUnitary (-h) f t) =ᵐ[volume]
      fun t : ℝ => f (t - h) := by
  simpa [MellinL2.additiveTranslationUnitary,
    MellinL2.lpCompMeasurePreservingEquiv, Function.comp_apply,
    MellinL2.realTranslationEquiv] using
    (Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving (-h)))

theorem causalLaplacePairing_additiveTranslationUnitary_neg
    {x : ℝ} (hx : 0 < x) {h : ℝ} (hh : 0 ≤ h)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    causalLaplacePairing x hx
        (MellinL2.additiveTranslationUnitary (-h) f) =
      Complex.exp (-(Real.pi * x * h : ℝ)) * causalLaplacePairing x hx f := by
  rw [causalLaplacePairing_eq_integral_of_lowerSupport hx _
    (additiveTranslationUnitary_hasAELowerSupport_zero hh f hf)]
  rw [causalLaplaceIntegral_congr_ae x
    (additiveTranslationUnitary_neg_ae h f)]
  rw [causalLaplaceIntegral_sub_shift]
  rw [← causalLaplacePairing_eq_integral_of_lowerSupport hx f hf]

def infiniteMobiusLaplaceMultiplierTerm (sigma x : ℝ) (n : ℕ) : ℂ :=
  signedMobiusProbability sigma n *
    Complex.exp (-(Real.pi * x * Real.log n : ℝ))

def infiniteMobiusLaplaceMultiplier (sigma x : ℝ) : ℂ :=
  ∑' n : ℕ, infiniteMobiusLaplaceMultiplierTerm sigma x n

theorem ofReal_squarefreeMobiusTotal_eq_zetaRatio
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (squarefreeMobiusTotal sigma : ℂ) =
      riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ)) := by
  have hmap := Complex.ofRealCLM.map_tsum (summable_squarefreeMobiusMass hsigma)
  simp only [Complex.ofRealCLM_apply] at hmap
  calc
    (squarefreeMobiusTotal sigma : ℂ) =
        ∑' n : ℕ, (squarefreeMobiusMass sigma n : ℂ) := by
      rw [squarefreeMobiusTotal]
      exact hmap
    _ = ∑' n : ℕ,
        (if Squarefree n then 1 / (n : ℂ) ^ (sigma : ℂ) else 0) := by
      apply tsum_congr
      exact ofReal_squarefreeMobiusMass_eq sigma
    _ = riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ)) :=
      tsum_squarefree_cpow (by simpa using hsigma)

theorem summable_infiniteMobiusLaplaceMultiplierTerm
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    Summable (infiniteMobiusLaplaceMultiplierTerm sigma x) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_squarefreeMobiusProbability hsigma)
  rw [infiniteMobiusLaplaceMultiplierTerm, norm_mul,
    norm_signedMobiusProbability hsigma, Complex.norm_exp]
  have hlog : 0 ≤ Real.log n := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have hexp : Real.exp (-(Real.pi * x * Real.log n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg Real.pi_pos.le hx) hlog)
  exact mul_le_of_le_one_right
    (squarefreeMobiusProbability_nonneg hsigma n) hexp

theorem causalLaplacePairing_infiniteMobiusShiftTerm
    {sigma x : ℝ} (hx : 0 < x) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    causalLaplacePairing x hx (infiniteMobiusShiftTerm sigma n f) =
      infiniteMobiusLaplaceMultiplierTerm sigma x n * causalLaplacePairing x hx f := by
  by_cases hn : n = 0
  · subst n
    simp [infiniteMobiusShiftTerm, infiniteMobiusLaplaceMultiplierTerm,
      signedMobiusProbability, causalLaplacePairing]
  · have hlog : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn)
    rw [infiniteMobiusShiftTerm, causalLaplacePairing]
    rw [inner_smul_right]
    rw [show inner ℂ (causalLaplaceWeightL2 x hx)
          (MellinL2.additiveTranslationUnitary (-Real.log n) f) =
        causalLaplacePairing x hx
          (MellinL2.additiveTranslationUnitary (-Real.log n) f) by rfl]
    rw [causalLaplacePairing_additiveTranslationUnitary_neg hx hlog f hf]
    unfold infiniteMobiusLaplaceMultiplierTerm
    ring

theorem causalLaplacePairing_infiniteMobiusShiftAverage
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 < x)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    causalLaplacePairing x hx (infiniteMobiusShiftAverage sigma f) =
      infiniteMobiusLaplaceMultiplier sigma x * causalLaplacePairing x hx f := by
  rw [infiniteMobiusShiftAverage, causalLaplacePairing]
  change (innerSL ℂ (causalLaplaceWeightL2 x hx))
      (∑' n : ℕ, infiniteMobiusShiftTerm sigma n f) = _
  rw [(innerSL ℂ (causalLaplaceWeightL2 x hx)).map_tsum
    (summable_infiniteMobiusShiftTerm hsigma f)]
  simp only [innerSL_apply_apply]
  rw [show (∑' n : ℕ,
        inner ℂ (causalLaplaceWeightL2 x hx) (infiniteMobiusShiftTerm sigma n f)) =
      ∑' n : ℕ, infiniteMobiusLaplaceMultiplierTerm sigma x n *
        causalLaplacePairing x hx f by
    apply tsum_congr
    intro n
    exact causalLaplacePairing_infiniteMobiusShiftTerm hx n f hf]
  rw [tsum_mul_right]
  rfl

theorem infiniteMobiusLaplaceMultiplierTerm_eq_LSeries_term
    (sigma x : ℝ) (n : ℕ) :
    infiniteMobiusLaplaceMultiplierTerm sigma x n =
      (squarefreeMobiusTotal sigma : ℂ)⁻¹ *
        LSeries.term (↗μ)
          ((sigma + Real.pi * x : ℝ) : ℂ) n := by
  by_cases hn0 : n = 0
  · subst n
    simp [infiniteMobiusLaplaceMultiplierTerm, signedMobiusProbability]
  · by_cases hsq : Squarefree n
    · rw [infiniteMobiusLaplaceMultiplierTerm, signedMobiusProbability,
        squarefreeMobiusProbability, squarefreeMobiusMass, if_pos hsq,
        LSeries.term_of_ne_zero hn0]
      rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [show ((-sigma : ℝ) : ℂ) = -(sigma : ℂ) by norm_cast,
        Complex.cpow_neg]
      rw [show ((sigma + Real.pi * x : ℝ) : ℂ) =
          (sigma : ℂ) + ((Real.pi * x : ℝ) : ℂ) by push_cast; ring,
        Complex.cpow_add (sigma : ℂ) ((Real.pi * x : ℝ) : ℂ)
        (Nat.cast_ne_zero.mpr hn0)]
      have hexp : Complex.exp (-(Real.pi * x * Real.log n : ℝ)) =
          ((n : ℂ) ^ ((Real.pi * x : ℝ) : ℂ))⁻¹ := by
        rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn0)]
        rw [← Complex.ofReal_natCast,
          ← Complex.ofReal_log (Nat.cast_nonneg n)]
        rw [← Complex.exp_neg]
        congr 1
        push_cast
        ring
      rw [hexp]
      rw [show (((n : ℕ) : ℝ) : ℂ) = (n : ℂ) by norm_cast]
      ring
    · rw [infiniteMobiusLaplaceMultiplierTerm, signedMobiusProbability,
        squarefreeMobiusProbability, squarefreeMobiusMass, if_neg hsq,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq,
        LSeries.term_of_ne_zero hn0]
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

theorem infiniteMobiusLaplaceMultiplier_eq_invTotal_mul_invZeta
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    infiniteMobiusLaplaceMultiplier sigma x =
      (squarefreeMobiusTotal sigma : ℂ)⁻¹ *
        (riemannZeta ((sigma + Real.pi * x : ℝ) : ℂ))⁻¹ := by
  unfold infiniteMobiusLaplaceMultiplier
  rw [show (∑' n : ℕ, infiniteMobiusLaplaceMultiplierTerm sigma x n) =
      ∑' n : ℕ, (squarefreeMobiusTotal sigma : ℂ)⁻¹ *
        LSeries.term (↗μ) ((sigma + Real.pi * x : ℝ) : ℂ) n by
    apply tsum_congr
    intro n
    exact infiniteMobiusLaplaceMultiplierTerm_eq_LSeries_term sigma x n]
  rw [tsum_mul_left]
  change (squarefreeMobiusTotal sigma : ℂ)⁻¹ *
      L ↗μ ((sigma + Real.pi * x : ℝ) : ℂ) = _
  rw [LSeries_moebius_eq_inv_riemannZeta]
  simp
  exact lt_of_lt_of_le hsigma
    (le_add_of_nonneg_right (mul_nonneg Real.pi_pos.le hx))

theorem infiniteMobiusLaplaceMultiplier_eq_zetaRatio
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    infiniteMobiusLaplaceMultiplier sigma x =
      riemannZeta (2 * (sigma : ℂ)) /
        (riemannZeta (sigma : ℂ) *
          riemannZeta ((sigma + Real.pi * x : ℝ) : ℂ)) := by
  rw [infiniteMobiusLaplaceMultiplier_eq_invTotal_mul_invZeta hsigma hx,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
  have hsig : 1 < ((sigma : ℂ)).re := by simpa using hsigma
  have htwo : 1 < (2 * (sigma : ℂ)).re := by
    simp
    linarith
  have hshift : 1 < (((sigma + Real.pi * x : ℝ) : ℂ)).re := by
    simp
    exact lt_of_lt_of_le hsigma
      (le_add_of_nonneg_right (mul_nonneg Real.pi_pos.le hx))
  field_simp [riemannZeta_ne_zero_of_one_lt_re hsig,
    riemannZeta_ne_zero_of_one_lt_re htwo,
    riemannZeta_ne_zero_of_one_lt_re hshift]

end RHTower
