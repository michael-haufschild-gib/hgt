import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsHilbertSchmidtAboveHalfDamping
import GaloisForLFunctions.RHTower.Sieve.InvZetaUniformStrip
import GaloisForLFunctions.RHTower.Sieve.InvZetaStripBound
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# The source on the critical line is zeta over zeta

For `η > ½` the Möbius coefficients of the source sum to `−1/ζ(η − s)` (`tsum_sourceCoeff_cpow`),
so on `Re s = −½` the Mellin transform of the source is exactly

`M P_η(s) = −ζ(−s) / (s ζ(η − s))`   (`mellin_sourceProfile_eq`),

with `−s = ½ − it` on the critical line and `η − s = ½ + η − it` to the right of the `1`-line.
The modulus is controlled uniformly in `½ < η < 1` (`norm_mellin_sourceProfile_sq_le`): only
`1/ζ` on `1 < Re ≤ 2` enters, which is `≪ log²|t|` at large height (`exists_norm_inv_zeta_right_le`,
from the zero-free strip) and bounded at bounded height (`exists_norm_inv_zeta_box_le`), while
`ζ(½ + it) ≪ |t|^{3/8}` by convexity (`exists_norm_zeta_half_le`).  The signs of `μ` enter only
through `1/ζ` near the `1`-line, i.e. at prime-number-theorem strength.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The Möbius series of the source -/

/-- **The source coefficients sum to `−1/ζ`**: `Σ_d a_d (d+1)^s = −1/ζ(η − s)` for
`Re(η − s) > 1`, `a_d = −μ(d+1)(d+1)^{−η}`. -/
theorem tsum_sourceCoeff_cpow {η : ℝ} {s : ℂ} (h : 1 < η - s.re) :
    ∑' d : ℕ, (sourceCoeff η d : ℂ) * ((((d + 1 : ℕ) : ℝ) : ℂ)) ^ s =
      -(riemannZeta ((η : ℂ) - s))⁻¹ := by
  set w : ℂ := (η : ℂ) - s with hw
  have hwre : 1 < w.re := by rw [hw]; simpa using h
  set f : ℕ → ℂ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) with hf
  have hL : LSeries f w = (riemannZeta w)⁻¹ := by
    have h1 : LSeries f w * riemannZeta w = 1 := by
      rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hwre, mul_comm]
      exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hwre
    exact eq_inv_of_mul_eq_one_left h1
  have hsum : LSeriesSummable f w := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hwre
  have hshift : LSeries f w = ∑' d : ℕ, LSeries.term f w (d + 1) := by
    rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  have hterm : ∀ d : ℕ, (sourceCoeff η d : ℂ) * ((((d + 1 : ℕ) : ℝ) : ℂ)) ^ s =
      -LSeries.term f w (d + 1) := by
    intro d
    have hd : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hx : ((((d + 1 : ℕ) : ℝ) : ℂ)) = (((d + 1 : ℕ) : ℂ)) := Complex.ofReal_natCast _
    have hx0 : (((d + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero d)]
    simp only [sourceCoeff, hf]
    rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_cpow hd.le, hx,
      Complex.ofReal_intCast, mul_assoc, ← Complex.cpow_add _ _ hx0,
      show ((-η : ℝ) : ℂ) + s = -w by rw [hw]; push_cast; ring, Complex.cpow_neg]
    ring
  rw [tsum_congr hterm, tsum_neg, ← hshift, hL]

/-- `|a_d| (d+1)^{−½} ≤ (d+1)^{−(η+½)}`. -/
theorem abs_sourceCoeff_mul_rpow_le (η : ℝ) (d : ℕ) :
    |sourceCoeff η d| * ((d + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ ((d : ℝ) + 1) ^ (-(η + 1 / 2)) := by
  have hd : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  calc |sourceCoeff η d| * ((d + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤
        ((d + 1 : ℕ) : ℝ) ^ (-η) * ((d + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (abs_sourceCoeff_le η d) (Real.rpow_nonneg hd.le _)
    _ = ((d : ℝ) + 1) ^ (-(η + 1 / 2)) := by
        rw [← Real.rpow_add hd, show -η + -1 / 2 = -(η + 1 / 2) by ring, Nat.cast_succ]

/-- **The source on the critical line is zeta over zeta**:
`M P_η(−½ + it) = −ζ(η − s)⁻¹ · ζ(−s)/s` for `η > ½`. -/
theorem mellin_sourceProfile_eq {η : ℝ} (h0 : 1 / 2 < η) (t : ℝ) :
    mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) =
      -(riemannZeta ((η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)))⁻¹ *
        (riemannZeta (-(((-1 / 2 : ℝ) : ℂ) + t * I)) / (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hre : s.re = -1 / 2 := by rw [hs]; simp
  have hη0 : 0 < η := by linarith
  have hzs : Summable fun d : ℕ => ((d : ℝ) + 1) ^ (-(η + 1 / 2)) :=
    RHTower.summable_realZetaTerm (by linarith)
  have hsum : Summable fun d : ℕ => |sourceCoeff η d| * ((d + 1 : ℕ) : ℝ) ^ s.re := by
    refine Summable.of_nonneg_of_le (fun d => by positivity) (fun d => ?_) hzs
    rw [hre]
    exact abs_sourceCoeff_mul_rpow_le η d
  rw [mellin_fractSeries (s := s) (by rw [hre]; norm_num) (by rw [hre]; norm_num) hsum
    (F := sourceProfile η) (fun x hx => sourceProfile_eq_tsum hη0 hx.le),
    tsum_sourceCoeff_cpow (by rw [hre]; linarith)]

/-! ### Uniform bounds on the weight -/

/-- **`1/ζ` to the right of the `1`-line at large height**: `‖ζ(σ + iτ)⁻¹‖ ≤ C log²|τ|` for
`σ > 1`, `|τ| ≥ T`, uniformly in `σ`. -/
theorem exists_norm_inv_zeta_right_le :
    ∃ C T : ℝ, 0 ≤ C ∧ 4 ≤ T ∧ ∀ σ τ : ℝ, 1 < σ → T ≤ |τ| →
      ‖(riemannZeta ((σ : ℂ) + (τ : ℂ) * I))⁻¹‖ ≤ C * Real.log |τ| ^ 2 := by
  obtain ⟨C, T, hC, hT4, hstrip⟩ := RHTower.Sieve.exists_norm_invZeta_strip_le
  refine ⟨C + 2, T, by linarith, hT4, fun σ τ hσ hτ => ?_⟩
  have habs : (4 : ℝ) ≤ |τ| := le_trans hT4 hτ
  have hL1 : (1 : ℝ) ≤ Real.log |τ| := RHTower.Sieve.one_le_log_abs habs
  have hL2 : (1 : ℝ) ≤ Real.log |τ| ^ 2 := one_le_pow₀ hL1
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, abs_zero] at habs; linarith
  have hne : ((σ : ℂ) + (τ : ℂ) * I) ≠ 1 := RHTower.Sieve.strip_pt_ne_one hτ0
  have hpos : 0 < 1 / Real.log |τ| ^ 2 := by positivity
  by_cases hσ' : σ ≤ 1 + 1 / Real.log |τ| ^ 2
  · have h := hstrip σ τ hτ (by linarith) hσ'
    rw [RHTower.Sieve.invZeta_eq_inv hne] at h
    calc _ ≤ C * Real.log |τ| ^ 2 := h
      _ ≤ (C + 2) * Real.log |τ| ^ 2 := by nlinarith
  · have hσ'' := (not_le.mp hσ').le
    have hσ1 : 1 < 1 + 1 / Real.log |τ| ^ 2 := by linarith
    have hre : ((σ : ℂ) + (τ : ℂ) * I).re = σ := by simp
    have h := RHTower.norm_inv_riemannZeta_le_of_le_re hσ1 (s := (σ : ℂ) + (τ : ℂ) * I)
      (by rw [hre]; exact hσ'')
    have e : 1 + 1 / (1 + 1 / Real.log |τ| ^ 2 - 1) = 1 + Real.log |τ| ^ 2 := by
      rw [add_sub_cancel_left, one_div_one_div]
    rw [e] at h
    calc _ ≤ 1 + Real.log |τ| ^ 2 := h
      _ ≤ (C + 2) * Real.log |τ| ^ 2 := by nlinarith

/-- **`1/ζ` to the right of the `1`-line at bounded height**: bounded on `1 < σ ≤ 2`, `|τ| ≤ T`. -/
theorem exists_norm_inv_zeta_box_le (T : ℝ) (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 → |τ| ≤ T →
      ‖(riemannZeta ((σ : ℂ) + (τ : ℂ) * I))⁻¹‖ ≤ M := by
  obtain ⟨δ, hδ, M, hM, hbox⟩ := RHTower.Sieve.exists_bound_invZeta_box 2 T (by norm_num) hT
  refine ⟨M, hM, fun σ τ hσ hσ2 hτ => ?_⟩
  have hne : ((σ : ℂ) + (τ : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h := hbox ((σ : ℂ) + (τ : ℂ) * I) (by simp; linarith) (by simp; linarith) (by simpa using hτ)
  rwa [RHTower.Sieve.invZeta_eq_inv hne] at h

/-- `‖ζ(½ − it)‖ = ‖ζ(½ + it)‖`. -/
theorem norm_zeta_half_neg (t : ℝ) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hconj : ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I =
      (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [hconj, riemannZeta_conj, Complex.norm_conj]

/-- **Convexity on the critical line**: `‖ζ(½ + it)‖ ≤ C |t|^{3/8}` for `|t| ≥ 8`. -/
theorem exists_norm_zeta_half_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 8 ≤ |t| →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ (3 / 8 : ℝ) := by
  obtain ⟨C, hC, hconv⟩ := RHTower.exists_norm_riemannZeta_le_convexity (η := 1 / 4)
    (by norm_num) (by norm_num)
  refine ⟨C, hC, fun t ht => ?_⟩
  have key : ∀ u : ℝ, 8 ≤ u →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ C * u ^ (3 / 8 : ℝ) := by
    intro u hu
    have h := hconv (1 / 2) u (by norm_num) (by norm_num) hu
    rwa [show (1 + 1 / 4 - 1 / 2) / 2 = (3 / 8 : ℝ) by norm_num] at h
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ⊢
    exact key t ht
  · rw [abs_of_nonpos h0] at ht ⊢
    have h := key (-t) ht
    rwa [← norm_zeta_half_neg, neg_neg] at h

/-- `ζ(½ + it)` is bounded at bounded height. -/
theorem exists_norm_zeta_half_box_le (T : ℝ) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ t : ℝ, |t| ≤ T → ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Z := by
  have hcont := RHTower.WeilSingularArithmetic.continuous_norm_zeta_line (σ := 1 / 2)
    (by norm_num)
  obtain ⟨Z, hZ⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max Z 0, le_max_right _ _, fun t ht => ?_⟩
  have h := hZ t (by rw [mem_Icc]; constructor <;> linarith [abs_le.mp ht])
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  exact le_trans h (le_max_left _ _)

/-- **The weight on the critical line, uniformly in `½ < η < 1`.**  There are `T₀ ≥ 8` and
constants such that `‖M P_η(−½ + it)‖² ≤ C₁` for `|t| ≤ T₀` and
`‖M P_η(−½ + it)‖² ≤ C₂ |t|^{3/4} log⁴|t| / t²` for `|t| ≥ T₀`. -/
theorem exists_norm_mellin_sourceProfile_sq_le :
    ∃ T₀ C₁ C₂ : ℝ, 8 ≤ T₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ η : ℝ, 1 / 2 < η → η < 1 → ∀ t : ℝ,
      (|t| ≤ T₀ →
        ‖mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ C₁) ∧
      (T₀ ≤ |t| →
        ‖mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
          C₂ * (|t| ^ (3 / 4 : ℝ) * Real.log |t| ^ 4 / t ^ 2)) := by
  obtain ⟨Cr, Tr, hCr, hTr4, hright⟩ := exists_norm_inv_zeta_right_le
  obtain ⟨Cz, hCz, hhalf⟩ := exists_norm_zeta_half_le
  set T₀ : ℝ := max Tr 8 with hT₀
  have hT₀8 : 8 ≤ T₀ := le_max_right _ _
  obtain ⟨Mb, hMb, hbox⟩ := exists_norm_inv_zeta_box_le T₀ (by linarith)
  obtain ⟨Z, hZ, hZbox⟩ := exists_norm_zeta_half_box_le T₀
  refine ⟨T₀, (Mb * Z / (1 / 2)) ^ 2, (Cr * Cz) ^ 2, hT₀8, by positivity, by positivity,
    fun η h0 h1 t => ?_⟩
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hM := mellin_sourceProfile_eq h0 t
  rw [← hs] at hM
  have hσ : (η : ℂ) - s = ((η + 1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hneg : -s = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hsn : 1 / 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [show s.re = -1 / 2 by rw [hs]; simp, abs_of_neg (by norm_num)] at this
    linarith
  have htn : |t| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    rwa [show s.im = t by rw [hs]; simp] at this
  have hnorm : ‖mellin (fun x => (sourceProfile η x : ℂ)) s‖ =
      ‖(riemannZeta (((η + 1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))⁻¹‖ *
        (‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / ‖s‖) := by
    rw [hM, norm_mul, norm_neg, hσ, norm_div, hneg, norm_zeta_half_neg]
  have hs0 : 0 < ‖s‖ := by linarith
  constructor
  · intro ht
    have hi := hbox (η + 1 / 2) (-t) (by linarith) (by linarith) (by rwa [abs_neg])
    have hz := hZbox t ht
    rw [hnorm]
    have hq : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / ‖s‖ ≤ Z / (1 / 2) :=
      div_le_div₀ hZ hz (by norm_num) hsn
    have hprod : ‖(riemannZeta (((η + 1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))⁻¹‖ *
        (‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / ‖s‖) ≤ Mb * (Z / (1 / 2)) :=
      mul_le_mul hi hq (by positivity) hMb
    calc _ ≤ (Mb * (Z / (1 / 2))) ^ 2 := pow_le_pow_left₀ (by positivity) hprod 2
      _ = (Mb * Z / (1 / 2)) ^ 2 := by ring
  · intro ht
    have hTr : Tr ≤ |t| := le_trans (le_max_left _ _) ht
    have h8 : 8 ≤ |t| := le_trans hT₀8 ht
    have hi := hright (η + 1 / 2) (-t) (by linarith) (by rwa [abs_neg])
    rw [abs_neg] at hi
    have hz := hhalf t h8
    have ht0 : 0 < |t| := by linarith
    have hq : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / ‖s‖ ≤ Cz * |t| ^ (3 / 8 : ℝ) / |t| :=
      div_le_div₀ (by positivity) hz ht0 htn
    rw [hnorm]
    have hprod : ‖(riemannZeta (((η + 1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))⁻¹‖ *
        (‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / ‖s‖) ≤
        Cr * Real.log |t| ^ 2 * (Cz * |t| ^ (3 / 8 : ℝ) / |t|) :=
      mul_le_mul hi hq (by positivity) (by positivity)
    calc _ ≤ (Cr * Real.log |t| ^ 2 * (Cz * |t| ^ (3 / 8 : ℝ) / |t|)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hprod 2
      _ = (Cr * Cz) ^ 2 * ((|t| ^ (3 / 8 : ℝ)) ^ 2 * Real.log |t| ^ 4 / |t| ^ 2) := by ring
      _ = (Cr * Cz) ^ 2 * (|t| ^ (3 / 4 : ℝ) * Real.log |t| ^ 4 / t ^ 2) := by
          rw [sq_rpow_eq ht0, sq_abs, show 2 * (3 / 8 : ℝ) = 3 / 4 by norm_num]

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
