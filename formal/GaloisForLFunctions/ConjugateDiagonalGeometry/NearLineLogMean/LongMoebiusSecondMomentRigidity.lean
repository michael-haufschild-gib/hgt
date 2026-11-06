import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TwoSidedThetaMollifierTrap
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheExponentOfTheMollifiedErrorIsRigid
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLineIsAShiftOfTheField
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.ArithmeticProduction.LongIntegerPolynomialsSeeParity

/-!
# Exact slope rigidity, quantifier collapse, and pure-Möbius equivalence for long moments

For the truncated Möbius polynomial `M_X(s) = ∑_{1 ≤ n ≤ X} μ(n) n^{-s}` at polynomial length
`X = ⌊T^θ⌋₊` on the critical line, write `w = zetaZeroWidth ∈ [0, 1/2]`. This module establishes
the exact two-sided `θ`-slope law, total quantifier and exponent collapse, pure-Möbius reduction,
and `θ`-nonuniformity of the coupled `[1, T]` second moments:

1. **Unconditional upper slope (`2 w θ`) without zero-simplicity assumptions:**
   Applying Abel summation on `Re s = 1/2 + w + 1/(2θ)` (`exists_norm_moebiusPoly_line_le`) and
   pointwise convexity (`norm_zeta_linePoint_le`) gives, for every `θ > 0` and every `T ≥ 1`,
   `∫_1^T ‖M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C_θ^{(0)} T^{4 + 2wθ}` and
   `∫_1^T ‖ζ(½ + it) M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C_θ T^{6 + 2wθ}`,
   with no simplicity hypothesis on zeta zeros and no discrete residue sum `J_{-1}(T)`.

2. **Sharp `2 β θ` converse for both mollified and pure Möbius moments:**
   Every off-line zero `ρ` of `ζ` satisfies `|Im ρ| > 9/2` (`xi_ne_zero_of_abs_im_le_nine_halves`),
   so after complex conjugation `[Im ρ - 1, Im ρ + 1] ⊆ [1, T]` for all `T ≥ Im ρ + 1`. Bounding
   `‖ζ M_X - 1‖²` on `[Im ρ - 1, Im ρ + 1]` either by `2 ‖ζ M_X‖² + 2` or by
   `648 (2 + Im ρ)² ‖M_X‖² + 2` feeds into the Poisson low-value measure bound
   (`eventually_poissonMass_lowSet_le`), forcing `zetaZeroWidth ≤ β` from any cofinal-`θ`,
   sparse-`T` bound of growth `C_θ T^{K + 2βθ}`.

3. **Quantifier collapse, width bootstrap, pure-Möbius equivalence, and `θ`-nonuniformity:**
   * At every `β ≥ 0`, cofinal-`θ`, sparse-`T`, existential-`K` growth `C_θ T^{K + 2βθ}` is
     equivalent (`↔`) to universal growth `C_θ T^{6 + 2βθ}` across all `θ > 0` and all `T ≥ 1`.
   * Any strict saving `2w - Δ` (`Δ > 0`) below the tautological slope `2w` forces `w = 0`, hence
     `RiemannHypothesis`.
   * Cofinal polynomial boundedness of `∫_1^T ‖ζ M_{⌊T^θ⌋}‖²` (`K = 6`) is unconditionally
     equivalent to cofinal polynomial boundedness of `∫_1^T ‖M_{⌊T^θ⌋}‖²` (`K = 4`) and to
     `RiemannHypothesis`.
   * No `θ`-independent constant `C` can satisfy `∫_1^T ‖M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C T^K` across all
     `θ > 0` and large `T`: choosing `θ = log(m + 1/2) / log(2 T₀)` realizes every integer cutoff
     `m ≥ 1` at a fixed height `2 T₀`, contradicting `eventually_not_uniform_moebius`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ArithmeticFunction.Moebius BigOperators ComplexConjugate

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_eq_zetaZeroAbscissa_sub_half zetaZeroWidth_le_iff_xiZeroHalfPlaneBound)

/-! ## §1. Dictionary between `edPoly moebiusMollifierCoeff` and `moebiusPoly` -/

/-- Critical-line point `½ + it` written with real cast `((1 / 2 : ℝ) : ℂ)`. -/
private theorem half_add_mul_I_eq_linePoint (t : ℝ) :
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = linePoint t := by
  unfold linePoint
  norm_num

/-- `edPoly moebiusMollifierCoeff (Icc 1 X)` on the critical line agrees identically with
`moebiusPoly X (linePoint t)`. -/
theorem edPoly_moebiusMollifierCoeff_eq_moebiusPoly (X : ℕ) (t : ℝ) :
    RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      moebiusPoly X (linePoint t) := by
  rw [half_add_mul_I_eq_linePoint]
  show RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X) (linePoint t) =
    RHTower.edPoly RHTower.mobCoeff (Finset.Icc 1 X) (linePoint t)
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [moebiusMollifierCoeff, RHTower.mobCoeff]

private theorem continuous_normSq_pure_moebius (X : ℕ) :
    Continuous fun t : ℝ =>
      ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have heq : (fun t : ℝ =>
      ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      fun t : ℝ => ‖moebiusPoly X (linePoint t)‖ ^ 2 := by
    ext t
    rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
  rw [heq]
  exact ((differentiable_moebiusPoly X).continuous.comp continuous_linePoint).norm.pow 2

private theorem continuous_normSq_zeta_moebius (X : ℕ) :
    Continuous fun t : ℝ =>
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have heq : (fun t : ℝ =>
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      fun t : ℝ => ‖riemannZeta (linePoint t) * moebiusPoly X (linePoint t)‖ ^ 2 := by
    ext t
    rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly, half_add_mul_I_eq_linePoint]
  rw [heq]
  have hcζ : Continuous fun u : ℝ => riemannZeta (linePoint u) :=
    continuous_iff_continuousAt.mpr fun u =>
      (differentiableAt_riemannZeta (linePoint_ne_one u)).continuousAt.comp
        continuous_linePoint.continuousAt
  exact (hcζ.mul ((differentiable_moebiusPoly X).continuous.comp continuous_linePoint)).norm.pow 2

/-! ## §2. Unconditional upper slope `2 · zetaZeroWidth` for all `θ > 0` and `T ≥ 1` -/

/-- **Unconditional pure-Möbius second-moment slope law.**
For every `θ > 0`, some `C ≥ 0` bounds `∫_1^T ‖M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C · T^{4 + 2 w θ}`
for all `T ≥ 1`, where `w = zetaZeroWidth`. -/
theorem exists_pure_moebius_moment_le_zetaZeroWidth {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (4 + 2 * zetaZeroWidth * θ) := by
  have hε : 0 < 1 / (2 * θ) := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_norm_moebiusPoly_line_le hε
  refine ⟨16 * K ^ 2, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTθ1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ.le
  have hX1 : 1 ≤ ⌊T ^ θ⌋₊ := (Nat.one_le_floor_iff (T ^ θ)).mpr hTθ1
  have hX_le : (⌊T ^ θ⌋₊ : ℝ) ≤ T ^ θ := Nat.floor_le (by positivity)
  set r : ℝ := zetaZeroWidth + 1 / (2 * θ)
  have hr0 : 0 ≤ r := add_nonneg zetaZeroWidth_nonneg hε.le
  have hXr : (⌊T ^ θ⌋₊ : ℝ) ^ r ≤ T ^ (zetaZeroWidth * θ + 1 / 2) := by
    calc (⌊T ^ θ⌋₊ : ℝ) ^ r ≤ (T ^ θ) ^ r :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hX_le hr0
      _ = T ^ (θ * r) := (Real.rpow_mul hT0.le θ r).symm
      _ = T ^ (zetaZeroWidth * θ + 1 / 2) := by
          congr 1
          dsimp [r]
          field_simp [hθ.ne']
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T,
      ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        16 * K ^ 2 * T ^ (3 + 2 * zetaZeroWidth * θ) := by
    intro t ht
    rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
    have ht_abs : 1 + |t| ≤ 2 * T := by
      rw [abs_of_pos (lt_of_lt_of_le zero_lt_one ht.1)]
      linarith [ht.2]
    have hM := hK ⌊T ^ θ⌋₊ t hX1
    have hM_T : ‖moebiusPoly ⌊T ^ θ⌋₊ (linePoint t)‖ ≤
        4 * K * T * T ^ (zetaZeroWidth * θ + 1 / 2) := by
      calc ‖moebiusPoly ⌊T ^ θ⌋₊ (linePoint t)‖
          ≤ 2 * (⌊T ^ θ⌋₊ : ℝ) ^ r * (K * (1 + |t|)) := hM
        _ ≤ 2 * T ^ (zetaZeroWidth * θ + 1 / 2) * (K * (2 * T)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hXr zero_le_two)
              (mul_le_mul_of_nonneg_left ht_abs hK0) (by positivity) (by positivity)
        _ = 4 * K * T * T ^ (zetaZeroWidth * θ + 1 / 2) := by ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hM_T 2
    refine hsq.trans_eq ?_
    have hrpow_sq : (T ^ (zetaZeroWidth * θ + 1 / 2)) ^ 2 = T ^ (2 * zetaZeroWidth * θ + 1) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hT0.le]
      congr 1
      push_cast
      ring
    calc (4 * K * T * T ^ (zetaZeroWidth * θ + 1 / 2)) ^ 2
        = 16 * K ^ 2 * (T ^ (2 : ℝ) * (T ^ (zetaZeroWidth * θ + 1 / 2)) ^ 2) := by
          rw [Real.rpow_two]
          ring
      _ = 16 * K ^ 2 * (T ^ (2 : ℝ) * T ^ (2 * zetaZeroWidth * θ + 1)) := by rw [hrpow_sq]
      _ = 16 * K ^ 2 * T ^ (3 + 2 * zetaZeroWidth * θ) := by
          rw [← Real.rpow_add hT0]
          congr 2
          ring
  have hmono : (∫ t in (1 : ℝ)..T,
      ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      ∫ _t in (1 : ℝ)..T, 16 * K ^ 2 * T ^ (3 + 2 * zetaZeroWidth * θ) :=
    intervalIntegral.integral_mono_on hT
      ((continuous_normSq_pure_moebius ⌊T ^ θ⌋₊).intervalIntegrable 1 T)
      intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine hmono.trans ?_
  have hlen : T - 1 ≤ T := by linarith
  have hnn : 0 ≤ 16 * K ^ 2 * T ^ (3 + 2 * zetaZeroWidth * θ) := by positivity
  calc (T - 1) * (16 * K ^ 2 * T ^ (3 + 2 * zetaZeroWidth * θ))
      ≤ T * (16 * K ^ 2 * T ^ (3 + 2 * zetaZeroWidth * θ)) :=
        mul_le_mul_of_nonneg_right hlen hnn
    _ = 16 * K ^ 2 * (T ^ (1 : ℝ) * T ^ (3 + 2 * zetaZeroWidth * θ)) := by
        rw [Real.rpow_one]
        ring
    _ = 16 * K ^ 2 * T ^ (4 + 2 * zetaZeroWidth * θ) := by
        rw [← Real.rpow_add hT0]
        congr 2
        ring

/-- **Unconditional mollified-zeta second-moment slope law.**
For every `θ > 0`, some `C ≥ 0` bounds
`∫_1^T ‖ζ(½ + it) M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C · T^{6 + 2 w θ}` for all `T ≥ 1`, where
`w = zetaZeroWidth`, without assuming simplicity of zeta zeros. -/
theorem exists_moebius_mollifier_moment_le_zetaZeroWidth {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (6 + 2 * zetaZeroWidth * θ) := by
  obtain ⟨C₀, hC₀, hM⟩ := exists_pure_moebius_moment_le_zetaZeroWidth hθ
  refine ⟨1296 * C₀, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T,
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        1296 * T ^ 2 *
          ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t ht
    rw [norm_mul, mul_pow, half_add_mul_I_eq_linePoint]
    have hζ := norm_zeta_linePoint_le t
    have ht_abs : 1 + |t| ≤ 2 * T := by
      rw [abs_of_pos (lt_of_lt_of_le zero_lt_one ht.1)]
      linarith [ht.2]
    have hζT : ‖riemannZeta (linePoint t)‖ ≤ 36 * T := by linarith
    have hζsq : ‖riemannZeta (linePoint t)‖ ^ 2 ≤ 1296 * T ^ 2 := by
      calc ‖riemannZeta (linePoint t)‖ ^ 2 ≤ (36 * T) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hζT 2
        _ = 1296 * T ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right hζsq (sq_nonneg _)
  have hmono : (∫ t in (1 : ℝ)..T,
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      ∫ t in (1 : ℝ)..T, 1296 * T ^ 2 *
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_mono_on hT
      ((continuous_normSq_zeta_moebius ⌊T ^ θ⌋₊).intervalIntegrable 1 T)
      (((continuous_normSq_pure_moebius ⌊T ^ θ⌋₊).const_mul _).intervalIntegrable 1 T)
      hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  refine hmono.trans ?_
  calc 1296 * T ^ 2 *
        (∫ t in (1 : ℝ)..T,
          ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 1296 * T ^ 2 * (C₀ * T ^ (4 + 2 * zetaZeroWidth * θ)) :=
        mul_le_mul_of_nonneg_left (hM T hT) (by positivity)
    _ = 1296 * C₀ * (T ^ (2 : ℝ) * T ^ (4 + 2 * zetaZeroWidth * θ)) := by
        rw [Real.rpow_two]
        ring
    _ = 1296 * C₀ * T ^ (6 + 2 * zetaZeroWidth * θ) := by
        rw [← Real.rpow_add hT0]
        congr 2
        ring

/-- Upper slope bound specialized to any zero-free half-plane width `β ≥ zetaZeroWidth`. -/
theorem exists_moebius_mollifier_moment_le_of_width_le {β θ : ℝ}
    (hw : zetaZeroWidth ≤ β) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (6 + 2 * β * θ) := by
  obtain ⟨C, hC0, hC⟩ := exists_moebius_mollifier_moment_le_zetaZeroWidth hθ
  refine ⟨C, hC0, fun T hT => (hC T hT).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT ?_) hC0
  nlinarith

/-! ## §3. Sharp `2 β θ` converse via height-gapped Poisson low-value rigidity -/

/-- Every nontrivial zero `ρ` of `riemannZeta` in `(1/2, 1)` near `1/2 + zetaZeroWidth` has a
conjugate-reflected partner in the upper half-plane with `Im ρ' > 9/2`. -/
private theorem exists_upper_zetaZero_near_width {t : ℝ} (ht0 : 0 < t)
    (ht_le : t ≤ zetaZeroWidth) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 ∧
      1 / 2 + zetaZeroWidth - t < ρ.re ∧ 9 / 2 < ρ.im := by
  have habs : RHTower.zetaZeroAbscissa = 1 / 2 + zetaZeroWidth := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    ring
  obtain ⟨ρ₀, hζ₀, hre1₀, hb₀⟩ := RHTower.exists_zetaZero_mem_openStrip_lt_re
    (b := 1 / 2 + zetaZeroWidth - t) (by rw [habs]; linarith)
  have hre_half₀ : 1 / 2 < ρ₀.re := by linarith
  have hre_pos₀ : 0 < ρ₀.re := by linarith
  have hne1₀ : ρ₀ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hre1₀
    linarith
  have hxi₀ : RHTower.xi ρ₀ = 0 := by
    by_contra hne
    exact riemannZeta_ne_zero_of_xi_ne_zero hre_pos₀ hne1₀ hne hζ₀
  have him_abs : 9 / 2 < |ρ₀.im| := by
    by_contra hle
    exact RHTower.xi_ne_zero_of_abs_im_le_nine_halves (not_lt.mp hle) hxi₀
  rcases le_or_gt 0 ρ₀.im with him_nn | him_neg
  · rw [abs_of_nonneg him_nn] at him_abs
    exact ⟨ρ₀, hζ₀, hre_half₀, hre1₀, hb₀, him_abs⟩
  · rw [abs_of_neg him_neg] at him_abs
    exact ⟨conj ρ₀, by rw [riemannZeta_conj, hζ₀, map_zero],
      by simpa using hre_half₀, by simpa using hre1₀,
      by simpa using hb₀, by simpa using him_abs⟩

private def highWindowSet (X : ℕ) (γ b : ℝ) : Set ℝ :=
  Set.Icc (γ - 1) (γ + 1) \ lowSet X b

/-- Markov measure lower bound on `[γ - 1, γ + 1]`: if the window `L²` norm squared is at most
`X^{2a}` for `a ≤ b` and `X ≥ 1`, then `lowSet X b ∩ [γ - 1, γ + 1]` has measure at least `1`. -/
private theorem one_le_volume_lowSet_inter_Icc {X : ℕ} (hX1 : 1 ≤ X) {γ a b : ℝ} (hab : a ≤ b)
    (hmom : (∫ u in Set.Icc (γ - 1) (γ + 1), ‖lineError (moebiusPoly X) u‖ ^ 2) ≤
      (X : ℝ) ^ (2 * a)) :
    1 ≤ volume.real (lowSet X b ∩ Set.Icc (γ - 1) (γ + 1)) := by
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX1R
  have hcontE : Continuous fun u : ℝ => ‖lineError (moebiusPoly X) u‖ ^ 2 :=
    (continuous_lineError (differentiable_moebiusPoly X)).norm.pow 2
  have hintW : IntegrableOn (fun u : ℝ => ‖lineError (moebiusPoly X) u‖ ^ 2)
      (Set.Icc (γ - 1) (γ + 1)) := hcontE.integrableOn_Icc
  have hBmeas : MeasurableSet (highWindowSet X γ b) :=
    measurableSet_Icc.diff (measurableSet_lowSet X b)
  have hBW : highWindowSet X γ b ⊆ Set.Icc (γ - 1) (γ + 1) := sdiff_subset
  have hBfin : volume (highWindowSet X γ b) ≠ ⊤ :=
    ((measure_mono hBW).trans_lt (by simp [Real.volume_Icc])).ne
  have hmarkov : (X : ℝ) ^ (2 * b) * volume.real (highWindowSet X γ b) ≤
      ∫ u in Set.Icc (γ - 1) (γ + 1), ‖lineError (moebiusPoly X) u‖ ^ 2 := by
    have h1 : (∫ _u in highWindowSet X γ b, (X : ℝ) ^ (2 * b)) ≤
        ∫ u in highWindowSet X γ b, ‖lineError (moebiusPoly X) u‖ ^ 2 := by
      refine setIntegral_mono_on (integrableOn_const hBfin) (hintW.mono_set hBW) hBmeas ?_
      intro u hu
      have hnot : (X : ℝ) ^ b < ‖lineError (moebiusPoly X) u‖ := not_le.mp hu.2
      calc (X : ℝ) ^ (2 * b)
          = ((X : ℝ) ^ b) ^ 2 := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hX0.le]
            congr 1; push_cast; ring
        _ ≤ ‖lineError (moebiusPoly X) u‖ ^ 2 :=
            pow_le_pow_left₀ (Real.rpow_nonneg hX0.le b) hnot.le 2
    rw [setIntegral_const, smul_eq_mul, mul_comm] at h1
    exact h1.trans (setIntegral_mono_set hintW (Eventually.of_forall fun _ => sq_nonneg _)
      (LE.le.eventuallyLE hBW))
  have hvolB : volume.real (highWindowSet X γ b) ≤ 1 := by
    have hpos : 0 < (X : ℝ) ^ (2 * a) := Real.rpow_pos_of_pos hX0 _
    have hexp : (X : ℝ) ^ (2 * a) ≤ (X : ℝ) ^ (2 * b) :=
      Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
    have hle1 : (X : ℝ) ^ (2 * a) * volume.real (highWindowSet X γ b) ≤
        (X : ℝ) ^ (2 * a) * 1 := by
      rw [mul_one]
      exact (mul_le_mul_of_nonneg_right hexp measureReal_nonneg).trans (hmarkov.trans hmom)
    exact le_of_mul_le_mul_left hle1 hpos
  have hcover : Set.Icc (γ - 1) (γ + 1) ⊆
      (lowSet X b ∩ Set.Icc (γ - 1) (γ + 1)) ∪ highWindowSet X γ b := by
    intro u hu
    by_cases hl : u ∈ lowSet X b
    · exact Or.inl ⟨hl, hu⟩
    · exact Or.inr ⟨hu, hl⟩
  have hfinI : volume (lowSet X b ∩ Set.Icc (γ - 1) (γ + 1)) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_right).trans_lt (by simp [Real.volume_Icc])).ne
  have hmeas_sum := (measureReal_mono hcover (measure_union_ne_top hfinI hBfin)).trans
    (measureReal_union_le (lowSet X b ∩ Set.Icc (γ - 1) (γ + 1)) (highWindowSet X γ b))
  rw [Real.volume_real_Icc_of_le (by linarith)] at hmeas_sum
  linarith

/-- Algebraic conversion from `A * T ^ (K + 2 * β * θ) + 4` to `X ^ (2 * (β + g / 3))` at large
cutoff `X = ⌊T ^ θ⌋₊`. -/
private theorem scale_bound_le_rpow {A K β θ g T : ℝ} {X : ℕ}
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hβ0 : 0 ≤ β) (hg0 : 0 ≤ g) (hθ0 : 0 < θ) (hT0 : 0 < T)
    (hX2 : 2 ≤ X) (hKθ : K / θ ≤ g / 4)
    (hTθ_le : T ^ θ ≤ 2 * (X : ℝ))
    (hC_X : (A + 4) * (2 : ℝ) ^ (K / θ + 2 * β) ≤ (X : ℝ) ^ (g / 6)) :
    A * T ^ (K + 2 * β * θ) + 4 ≤ (X : ℝ) ^ (2 * (β + g / 3)) := by
  have hX1R : (1 : ℝ) ≤ X := by
    have : (2 : ℝ) ≤ X := by exact_mod_cast hX2
    linarith
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX1R
  have hα_nn : 0 ≤ K / θ + 2 * β := by positivity
  have hexp_eq : T ^ (K + 2 * β * θ) = (T ^ θ) ^ (K / θ + 2 * β) := by
    rw [← Real.rpow_mul hT0.le]
    congr 1
    field_simp [hθ0.ne']
  have hrpow_le : (T ^ θ) ^ (K / θ + 2 * β) ≤
      (2 : ℝ) ^ (K / θ + 2 * β) * (X : ℝ) ^ (K / θ + 2 * β) := by
    rw [← Real.mul_rpow zero_le_two hX0.le]
    exact Real.rpow_le_rpow (by positivity) hTθ_le hα_nn
  have h1_le : 1 ≤ (2 : ℝ) ^ (K / θ + 2 * β) * (X : ℝ) ^ (K / θ + 2 * β) :=
    one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hα_nn)
      (Real.one_le_rpow hX1R hα_nn)
  have hstep1 : A * T ^ (K + 2 * β * θ) + 4 ≤
      ((A + 4) * (2 : ℝ) ^ (K / θ + 2 * β)) * (X : ℝ) ^ (K / θ + 2 * β) := by
    rw [hexp_eq]
    have hA_mul := mul_le_mul_of_nonneg_left hrpow_le hA0
    have h4_mul : (4 : ℝ) ≤ 4 * ((2 : ℝ) ^ (K / θ + 2 * β) * (X : ℝ) ^ (K / θ + 2 * β)) := by
      linarith
    linarith
  calc A * T ^ (K + 2 * β * θ) + 4
      ≤ ((A + 4) * (2 : ℝ) ^ (K / θ + 2 * β)) * (X : ℝ) ^ (K / θ + 2 * β) := hstep1
    _ ≤ (X : ℝ) ^ (g / 6) * (X : ℝ) ^ (K / θ + 2 * β) :=
        mul_le_mul_of_nonneg_right hC_X (Real.rpow_nonneg hX0.le _)
    _ = (X : ℝ) ^ (g / 6 + (K / θ + 2 * β)) := (Real.rpow_add hX0 _ _).symm
    _ ≤ (X : ℝ) ^ (2 * (β + g / 3)) :=
        Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)

/-- If along cofinal `θ` and unbounded `T`, the `[γ - 1, γ + 1]` window second moment of
`lineError (moebiusPoly ⌊T^θ⌋₊)` is bounded by `A_θ T^{K + 2βθ} + 4` at every height `γ > 9/2`,
then `zetaZeroWidth ≤ β`. -/
private theorem zetaZeroWidth_le_of_window_lineError_slope {β K : ℝ} (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hwin : ∀ γ : ℝ, 9 / 2 < γ → ∀ θ₀ : ℝ, 0 < θ₀ →
      ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ᶠ T : ℝ in atTop,
        (∫ u in Set.Icc (γ - 1) (γ + 1), ‖lineError (moebiusPoly ⌊T ^ θ⌋₊) u‖ ^ 2) ≤
          A * T ^ (K + 2 * β * θ) + 4) :
    zetaZeroWidth ≤ β := by
  by_contra hlt
  rw [not_le] at hlt
  have hw0 : 0 < zetaZeroWidth := lt_of_le_of_lt hβ hlt
  obtain ⟨g, hg_def⟩ : ∃ g : ℝ, g = zetaZeroWidth - β := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg_def]; linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨p₀, hp₀_def⟩ : ∃ p₀ : ℝ, p₀ = (zetaZeroWidth / 2) / (Real.pi * (1 / 4 + 1)) := ⟨_, rfl⟩
  have hp₀0 : 0 < p₀ := by rw [hp₀_def]; positivity
  obtain ⟨t₀, ht₀_def⟩ : ∃ t₀ : ℝ, t₀ = min (zetaZeroWidth / 2) (p₀ * g / 8) := ⟨_, rfl⟩
  have ht₀0 : 0 < t₀ := by rw [ht₀_def]; exact lt_min (by positivity) (by positivity)
  have ht₀_half : t₀ ≤ zetaZeroWidth / 2 := by rw [ht₀_def]; exact min_le_left _ _
  have ht₀_pg : t₀ ≤ p₀ * g / 8 := by rw [ht₀_def]; exact min_le_right _ _
  obtain ⟨ρ, hζ, hre, hre1, hbρ, hγ⟩ :=
    exists_upper_zetaZero_near_width ht₀0 (ht₀_half.trans (by linarith))
  have hδ : 0 < ρ.re - 1 / 2 := by linarith
  have hδw : zetaZeroWidth / 2 ≤ ρ.re - 1 / 2 := by linarith
  have hdt : zetaZeroWidth - (ρ.re - 1 / 2) ≤ t₀ := by linarith
  have hplow : ∀ u ∈ Set.Icc (ρ.im - 1) (ρ.im + 1), p₀ ≤ zeroPoisson ρ u := by
    intro u hu
    have habsu : |u - ρ.im| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    refine le_trans ?_ (poisson_lower_bound hδ habsu)
    rw [hp₀_def]
    have hδsq : (ρ.re - 1 / 2) ^ 2 ≤ 1 / 4 := by
      have hle : ρ.re - 1 / 2 ≤ 1 / 2 := by linarith
      nlinarith
    exact div_le_div₀ hδ.le hδw (mul_pos hπ (by positivity))
      (mul_le_mul_of_nonneg_left (by linarith) hπ.le)
  have hκ0 : 0 ≤ β + g / 2 := by positivity
  have hκw : β + g / 2 < zetaZeroWidth := by rw [hg_def]; linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_poissonMass_lowSet_le hζ hre hre1 hκ0 hκw (η := p₀ / 4) (by positivity))
  obtain ⟨θ, hθ_ge, A, hA0, hfreqT⟩ := hwin ρ.im hγ (max 1 (4 * (K + 1) / g))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hθ1 : 1 ≤ θ := (le_max_left _ _).trans hθ_ge
  have hθ_pos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ1
  have hKθ : K / θ ≤ g / 4 := by
    have h1 : 4 * (K + 1) / g ≤ θ := (le_max_right _ _).trans hθ_ge
    rw [div_le_iff₀ hg0] at h1
    rw [div_le_div_iff₀ hθ_pos (by norm_num)]
    nlinarith
  have hgrowX : Tendsto (fun X : ℕ => (X : ℝ) ^ (g / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hgrowX.eventually_ge_atTop ((A + 4) * (2 : ℝ) ^ (K / θ + 2 * β)))
  obtain ⟨N_big, hN_big_def⟩ : ∃ N_big : ℕ, N_big = max (max N₀ N₁) 2 := ⟨_, rfl⟩
  have hevT : ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ ((N_big : ℝ) + 1 ≤ T ^ θ) :=
    (eventually_ge_atTop (2 : ℝ)).and
      ((tendsto_rpow_atTop hθ_pos).eventually_ge_atTop ((N_big : ℝ) + 1))
  obtain ⟨T, hwinT, hT2, hT_big⟩ := (hfreqT.and_eventually hevT).exists
  obtain ⟨X, hX_def⟩ : ∃ X : ℕ, X = ⌊T ^ θ⌋₊ := ⟨_, rfl⟩
  rw [← hX_def] at hwinT
  have hX_ge_big : N_big ≤ X := by
    have hfl := Nat.lt_floor_add_one (T ^ θ)
    rw [← hX_def] at hfl
    have hcast : (N_big : ℝ) ≤ (X : ℝ) := by linarith
    exact_mod_cast hcast
  have hX_N₀ : N₀ ≤ X :=
    (le_trans (le_max_left _ _) (le_max_left _ _)).trans (hN_big_def ▸ hX_ge_big)
  have hX_N₁ : N₁ ≤ X :=
    (le_trans (le_max_right _ _) (le_max_left _ _)).trans (hN_big_def ▸ hX_ge_big)
  have hX2 : 2 ≤ X := (le_max_right _ _).trans (hN_big_def ▸ hX_ge_big)
  have hTθ_le : T ^ θ ≤ 2 * (X : ℝ) := by
    have hfl := (Nat.lt_floor_add_one (T ^ θ)).le
    rw [← hX_def] at hfl
    have hX2R : (2 : ℝ) ≤ X := by exact_mod_cast hX2
    linarith
  have hmom : (∫ u in Set.Icc (ρ.im - 1) (ρ.im + 1), ‖lineError (moebiusPoly X) u‖ ^ 2) ≤
      (X : ℝ) ^ (2 * (β + g / 3)) :=
    hwinT.trans (scale_bound_le_rpow hA0 hK hβ hg0.le hθ_pos (by linarith) hX2 hKθ hTθ_le
      (hN₁ X hX_N₁))
  have hvol_low := one_le_volume_lowSet_inter_Icc (by omega : 1 ≤ X)
    (a := β + g / 3) (b := β + g / 2) (by linarith) hmom
  have hP_low := mul_volume_le_setIntegral (integrable_zeroPoisson hre) (zeroPoisson_nonneg hre)
    (measurableSet_lowSet X (β + g / 2)) hplow
  have hp₀_le_int : p₀ ≤ ∫ u in lowSet X (β + g / 2), zeroPoisson ρ u := by
    calc p₀ = p₀ * 1 := (mul_one p₀).symm
      _ ≤ p₀ * volume.real (lowSet X (β + g / 2) ∩ Set.Icc (ρ.im - 1) (ρ.im + 1)) :=
          mul_le_mul_of_nonneg_left hvol_low hp₀0.le
      _ ≤ ∫ u in lowSet X (β + g / 2), zeroPoisson ρ u := hP_low
  have hint_le := hN₀ X hX_N₀
  have hquot : (zetaZeroWidth - (ρ.re - 1 / 2)) / (zetaZeroWidth - (β + g / 2)) ≤ p₀ / 4 := by
    have hwκ : zetaZeroWidth - (β + g / 2) = g / 2 := by rw [hg_def]; ring
    rw [hwκ, div_le_iff₀ (by positivity)]
    have hpg : p₀ * g / 8 = (p₀ / 4) * (g / 2) := by ring
    linarith [hdt, ht₀_pg, hpg]
  linarith

/-- **Sharp `2 β θ` converse for mollified zeta moments.**
If `β ≥ 0` and for some `K ≥ 0`, arbitrarily large `θ > 0` admit `C_θ ≥ 0` and unboundedly many
heights `T` with `∫_1^T ‖ζ(½ + it) M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C_θ T^{K + 2βθ}`, then
`zetaZeroWidth ≤ β`. -/
theorem zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope {β K : ℝ} (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hcofinal : ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ (K + 2 * β * θ)) :
    zetaZeroWidth ≤ β := by
  refine zetaZeroWidth_le_of_window_lineError_slope hβ hK fun γ hγ θ₀ hθ₀ => ?_
  obtain ⟨θ, hθ_ge, C, hC0, hfreq⟩ := hcofinal θ₀ hθ₀
  refine ⟨θ, hθ_ge, 2 * C, by positivity, ?_⟩
  refine (hfreq.and_eventually (eventually_ge_atTop (γ + 1))).mono fun T ⟨hmom, hTγ⟩ => ?_
  set X : ℕ := ⌊T ^ θ⌋₊
  have h1γ : 1 ≤ γ - 1 := by linarith
  have hγ_le : γ - 1 ≤ γ + 1 := by linarith
  have hcontE : Continuous fun u : ℝ => ‖lineError (moebiusPoly X) u‖ ^ 2 :=
    (continuous_lineError (differentiable_moebiusPoly X)).norm.pow 2
  have hcontZ := continuous_normSq_zeta_moebius X
  have hpt : ∀ u : ℝ, ‖lineError (moebiusPoly X) u‖ ^ 2 ≤
      2 * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 + 2 := by
    intro u
    rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly, half_add_mul_I_eq_linePoint]
    unfold lineError
    set z : ℂ := riemannZeta (linePoint u) * moebiusPoly X (linePoint u)
    have htri : ‖z - 1‖ ≤ ‖z‖ + 1 := by
      simpa using norm_sub_le z 1
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hsub_int : (∫ u in (γ - 1)..(γ + 1),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2) ≤
      ∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hcontZ.intervalIntegrable volume 1 (γ - 1))
      (hcontZ.intervalIntegrable volume (γ - 1) (γ + 1))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hcontZ.intervalIntegrable volume 1 (γ + 1))
      (hcontZ.intervalIntegrable volume (γ + 1) T)
    have hnn1 : 0 ≤ ∫ u in (1 : ℝ)..(γ - 1),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
          RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
            (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
      intervalIntegral.integral_nonneg h1γ fun _ _ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ u in (γ + 1)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
          RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
            (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hTγ fun _ _ => sq_nonneg _
    linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hγ_le]
  calc (∫ u in (γ - 1)..(γ + 1), ‖lineError (moebiusPoly X) u‖ ^ 2)
      ≤ ∫ u in (γ - 1)..(γ + 1),
          (2 * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
              (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 + 2) :=
        intervalIntegral.integral_mono_on hγ_le (hcontE.intervalIntegrable _ _)
          (((hcontZ.const_mul 2).add continuous_const).intervalIntegrable _ _)
          (fun u _ => hpt u)
    _ = 2 * (∫ u in (γ - 1)..(γ + 1),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
              (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2) + 4 := by
        rw [intervalIntegral.integral_add ((hcontZ.const_mul 2).intervalIntegrable _ _)
            intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ 2 * C * T ^ (K + 2 * β * θ) + 4 := by linarith [hsub_int, hmom]

/-- **Sharp `2 β θ` converse for pure Möbius moments.**
If `β ≥ 0` and for some `K ≥ 0`, arbitrarily large `θ > 0` admit `C_θ ≥ 0` and unboundedly many
heights `T` with `∫_1^T ‖M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C_θ T^{K + 2βθ}`, then `zetaZeroWidth ≤ β`. -/
theorem zetaZeroWidth_le_of_cofinal_pure_moebius_slope {β K : ℝ} (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hcofinal : ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ (K + 2 * β * θ)) :
    zetaZeroWidth ≤ β := by
  refine zetaZeroWidth_le_of_window_lineError_slope hβ hK fun γ hγ θ₀ hθ₀ => ?_
  obtain ⟨θ, hθ_ge, C, hC0, hfreq⟩ := hcofinal θ₀ hθ₀
  set W : ℝ := 648 * (2 + γ) ^ 2
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨θ, hθ_ge, W * C, by positivity, ?_⟩
  refine (hfreq.and_eventually (eventually_ge_atTop (γ + 1))).mono fun T ⟨hmom, hTγ⟩ => ?_
  set X : ℕ := ⌊T ^ θ⌋₊
  have h1γ : 1 ≤ γ - 1 := by linarith
  have hγ_le : γ - 1 ≤ γ + 1 := by linarith
  have hcontE : Continuous fun u : ℝ => ‖lineError (moebiusPoly X) u‖ ^ 2 :=
    (continuous_lineError (differentiable_moebiusPoly X)).norm.pow 2
  have hcontM := continuous_normSq_pure_moebius X
  have hpt : ∀ u ∈ Set.Icc (γ - 1) (γ + 1), ‖lineError (moebiusPoly X) u‖ ^ 2 ≤
      W * ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
        (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 + 2 := by
    intro u hu
    rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
    unfold lineError
    have hu_abs : 1 + |u| ≤ 2 + γ := by
      rw [abs_of_pos (by linarith [hu.1])]
      linarith [hu.2]
    have hζ : ‖riemannZeta (linePoint u)‖ ≤ 18 * (2 + γ) :=
      (norm_zeta_linePoint_le u).trans (by linarith)
    set m : ℝ := ‖moebiusPoly X (linePoint u)‖
    have hprod : ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ≤ 18 * (2 + γ) * m := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
    have htri : ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u) - 1‖ ≤
        18 * (2 + γ) * m + 1 :=
      (norm_sub_le _ 1).trans (by rw [norm_one]; linarith)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have h2 : (18 * (2 + γ) * m + 1) ^ 2 ≤ 2 * (18 * (2 + γ) * m) ^ 2 + 2 := by
      nlinarith [sq_nonneg (18 * (2 + γ) * m - 1)]
    refine hsq.trans (h2.trans_eq ?_)
    dsimp [W]
    ring
  have hsub_int : (∫ u in (γ - 1)..(γ + 1),
      ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
        (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2) ≤
      ∫ t in (1 : ℝ)..T,
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hcontM.intervalIntegrable volume 1 (γ - 1))
      (hcontM.intervalIntegrable volume (γ - 1) (γ + 1))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hcontM.intervalIntegrable volume 1 (γ + 1))
      (hcontM.intervalIntegrable volume (γ + 1) T)
    have hnn1 : 0 ≤ ∫ u in (1 : ℝ)..(γ - 1),
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
      intervalIntegral.integral_nonneg h1γ fun _ _ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ u in (γ + 1)..T,
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hTγ fun _ _ => sq_nonneg _
    linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hγ_le]
  calc (∫ u in (γ - 1)..(γ + 1), ‖lineError (moebiusPoly X) u‖ ^ 2)
      ≤ ∫ u in (γ - 1)..(γ + 1),
          (W * ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
            (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 + 2) :=
        intervalIntegral.integral_mono_on hγ_le (hcontE.intervalIntegrable _ _)
          (((hcontM.const_mul W).add continuous_const).intervalIntegrable _ _) hpt
    _ = W * (∫ u in (γ - 1)..(γ + 1),
          ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 X)
            (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2) + 4 := by
        rw [intervalIntegral.integral_add ((hcontM.const_mul W).intervalIntegrable _ _)
            intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ W * C * T ^ (K + 2 * β * θ) + 4 := by
        have hmul := mul_le_mul_of_nonneg_left (hsub_int.trans hmom) hW0
        linarith

/-! ## §4. Two-sided equivalences, quantifier/exponent collapse, bootstrap, and `θ`-nonuniformity -/

/-- **Two-sided slope characterization of `zetaZeroWidth ≤ β`.** -/
theorem zetaZeroWidth_le_iff_cofinal_moebius_mollifier_slope {β : ℝ} (hβ : 0 ≤ β) :
    zetaZeroWidth ≤ β ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∃ᶠ T : ℝ in atTop,
          (∫ t in (1 : ℝ)..T,
            ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
                (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
            C * T ^ (K + 2 * β * θ) := by
  constructor
  · intro hw
    refine ⟨6, by norm_num, fun θ₀ hθ₀ => ⟨θ₀, le_rfl, ?_⟩⟩
    obtain ⟨C, hC0, hC⟩ := exists_moebius_mollifier_moment_le_of_width_le hw hθ₀
    exact ⟨C, hC0, (eventually_ge_atTop (1 : ℝ)).frequently.mono fun T hT => hC T hT⟩
  · rintro ⟨K, hK, hcofinal⟩
    exact zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope hβ hK hcofinal

/-- **Total quantifier and `K`-collapse at every slope `2 β`.**
Cofinal-`θ`, sparse-`T` boundedness with some fixed `K ≥ 0` is unconditionally equivalent to
universal boundedness with `K = 6` across all `θ > 0` and all `T ≥ 1`. -/
theorem cofinal_moebius_mollifier_slope_iff_forall {β : ℝ} (hβ : 0 ≤ β) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ (K + 2 * β * θ)) ↔
      (∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ (6 + 2 * β * θ)) := by
  constructor
  · rintro ⟨K, hK, hcofinal⟩ θ hθ
    have hw := zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope hβ hK hcofinal
    exact exists_moebius_mollifier_moment_le_of_width_le hw hθ
  · intro hforall
    refine ⟨6, by norm_num, fun θ₀ hθ₀ => ⟨θ₀, le_rfl, ?_⟩⟩
    obtain ⟨C, hC0, hC⟩ := hforall θ₀ hθ₀
    exact ⟨C, hC0, (eventually_ge_atTop (1 : ℝ)).frequently.mono fun T hT => hC T hT⟩

/-- **Exact two-sided equivalence between `RiemannHypothesis` and cofinal polynomial boundedness
of long Möbius-mollified second moments.** -/
theorem riemannHypothesis_iff_cofinal_moebius_mollifier :
    RiemannHypothesis ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∃ᶠ T : ℝ in atTop,
          (∫ t in (1 : ℝ)..T,
            ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
                (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
            C * T ^ K := by
  rw [RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl,
    zetaZeroWidth_le_iff_cofinal_moebius_mollifier_slope le_rfl]
  simp only [mul_zero, zero_mul, add_zero]

/-- **Self-improvement of the `route-wd` §1 condition.**
Any cofinal-`θ`, sparse-`T` bound with any fixed `K ≥ 0` automatically upgrades to universal
`K = 6` across every `θ > 0` and every `T ≥ 1`. -/
theorem cofinal_moebius_mollifier_self_improves_to_all {K : ℝ} (hK : 0 ≤ K)
    (hcofinal : ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ K) :
    ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (6 : ℝ) := by
  have h := (cofinal_moebius_mollifier_slope_iff_forall (β := 0) le_rfl).mp
    ⟨K, hK, by simpa using hcofinal⟩
  simpa using h

/-- **Strict slope-saving bootstrap.**
Because the unconditional upper slope is `2 · zetaZeroWidth`, any strict saving `2 · zetaZeroWidth - Δ`
(`Δ > 0`) forces `zetaZeroWidth = 0` and therefore `RiemannHypothesis`. -/
theorem riemannHypothesis_of_width_slope_saving {K Δ : ℝ} (hK : 0 ≤ K) (hΔ : 0 < Δ)
    (hsaving : ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ (K + max 0 (2 * zetaZeroWidth - Δ) * θ)) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl]
  set β : ℝ := max 0 (zetaZeroWidth - Δ / 2)
  have hβ0 : 0 ≤ β := le_max_left _ _
  have h2β : max 0 (2 * zetaZeroWidth - Δ) = 2 * β := by
    dsimp [β]
    rcases le_or_gt (zetaZeroWidth - Δ / 2) 0 with hle | hgt
    · rw [max_eq_left hle, max_eq_left (by linarith), mul_zero]
    · rw [max_eq_right hgt.le, max_eq_right (by linarith)]
      ring
  have hw_le : zetaZeroWidth ≤ β := by
    refine zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope hβ0 hK fun θ₀ hθ₀ => ?_
    obtain ⟨θ, hθ_ge, C, hC0, hfreq⟩ := hsaving θ₀ hθ₀
    rw [h2β] at hfreq
    exact ⟨θ, hθ_ge, C, hC0, hfreq⟩
  dsimp [β] at hw_le
  rcases le_or_gt (zetaZeroWidth - Δ / 2) 0 with hle | hgt
  · rwa [max_eq_left hle] at hw_le
  · rw [max_eq_right hgt.le] at hw_le
    linarith

/-- **Pure-Möbius `[1, T]` equivalence for `RiemannHypothesis`.**
`RiemannHypothesis` holds iff the pure (unmollified) long Möbius second moment
`∫_1^T ‖M_{⌊T^θ⌋}(½ + it)‖² dt` has polynomial growth in `T` with a `θ`-independent exponent `K₀`
along cofinal `θ` and sparse `T`. -/
theorem riemannHypothesis_iff_cofinal_pure_moebius_moment :
    RiemannHypothesis ↔
      ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∃ᶠ T : ℝ in atTop,
          (∫ t in (1 : ℝ)..T,
            ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
            C * T ^ K₀ := by
  rw [RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl]
  constructor
  · intro hw0
    have hw_eq : zetaZeroWidth = 0 := le_antisymm hw0 zetaZeroWidth_nonneg
    refine ⟨4, by norm_num, fun θ₀ hθ₀ => ⟨θ₀, le_rfl, ?_⟩⟩
    obtain ⟨C, hC0, hC⟩ := exists_pure_moebius_moment_le_zetaZeroWidth hθ₀
    refine ⟨C, hC0, (eventually_ge_atTop (1 : ℝ)).frequently.mono fun T hT => ?_⟩
    simpa [hw_eq] using hC T hT
  · rintro ⟨K₀, hK₀, hcofinal⟩
    exact zetaZeroWidth_le_of_cofinal_pure_moebius_slope le_rfl hK₀ (by simpa using hcofinal)

/-- Direct equivalence between pure-Möbius and mollified-zeta cofinal polynomial growth. -/
theorem cofinal_pure_moebius_moment_iff_cofinal_moebius_mollifier :
    (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ K₀) ↔
    (∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C * T ^ K) :=
  riemannHypothesis_iff_cofinal_pure_moebius_moment.symm.trans
    riemannHypothesis_iff_cofinal_moebius_mollifier

/-- **Unconditional unboundedness in `θ` at every large height `T`.**
For every height-only bound `f : ℝ → ℝ`, all sufficiently large heights `T` admit an exponent
`θ > 0` with `f T < ∫_1^T ‖M_{⌊T^θ⌋}(½ + it)‖² dt`. -/
theorem eventually_exists_theta_pure_moebius_moment_gt (f : ℝ → ℝ) :
    ∀ᶠ T : ℝ in atTop, ∃ θ : ℝ, 0 < θ ∧
      f T < (∫ t in (1 : ℝ)..T,
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  have htend : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
    tendsto_id.atTop_div_const two_pos
  have hev := (htend.eventually ArithmeticProduction.eventually_not_uniform_moebius).and
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hev] with T ⟨hunb, hT2⟩
  have hnot_all : ¬ ∀ m : ℕ, 1 ≤ m →
      (∫ t in (T / 2)..(2 * (T / 2)),
        ‖ArithmeticProduction.linePoly
          (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) m t‖ ^ 2) ≤ f T :=
    fun hall => hunb ⟨f T, hall⟩
  push Not at hnot_all
  obtain ⟨m, hm1, hgt⟩ := hnot_all
  have h2div : 2 * (T / 2) = T := by ring
  rw [h2div] at hgt
  have hT_pos : 0 < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hm_half_gt1 : (1 : ℝ) < (m : ℝ) + 1 / 2 := by
    have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hm_half_pos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by linarith
  set θ : ℝ := Real.log ((m : ℝ) + 1 / 2) / Real.log T
  have hθ_pos : 0 < θ := div_pos (Real.log_pos hm_half_gt1) hlogT_pos
  have hTθ_eq : T ^ θ = (m : ℝ) + 1 / 2 := by
    rw [Real.rpow_def_of_pos hT_pos]
    have hmul : Real.log T * θ = Real.log ((m : ℝ) + 1 / 2) := by
      dsimp [θ]
      exact mul_div_cancel₀ _ hlogT_pos.ne'
    rw [hmul, Real.exp_log hm_half_pos]
  have hfl_eq : ⌊T ^ θ⌋₊ = m := by
    rw [hTθ_eq, Nat.floor_eq_iff hm_half_pos.le]
    exact ⟨by linarith, by linarith⟩
  refine ⟨θ, hθ_pos, hgt.trans_le ?_⟩
  rw [hfl_eq]
  have hline_eq : (fun t : ℝ =>
      ‖ArithmeticProduction.linePoly
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) m t‖ ^ 2) =
      fun t : ℝ =>
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 m)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    ext t
    rfl
  rw [hline_eq]
  have hcont := continuous_normSq_pure_moebius m
  have h1_half : 1 ≤ T / 2 := by linarith
  have hhalf_T : T / 2 ≤ T := by linarith
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable volume 1 (T / 2)) (hcont.intervalIntegrable volume (T / 2) T)
  have hnn : 0 ≤ ∫ t in (1 : ℝ)..(T / 2),
      ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 m)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg h1_half fun _ _ => sq_nonneg _
  linarith

/-- **Unconditional `θ`-nonuniformity (`C_θ → ∞` necessity).**
No `θ`-independent constant `C` can satisfy `∫_1^T ‖M_{⌊T^θ⌋}(½ + it)‖² dt ≤ C T^K` across all
`θ > 0` and `T ≥ 1`. -/
theorem not_exists_theta_uniform_pure_moebius_moment :
    ¬ ∃ K C : ℝ, ∀ θ : ℝ, 0 < θ → ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ K := by
  rintro ⟨K, C, hunif⟩
  obtain ⟨T, hT1, θ, hθ, hgt⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and
      (eventually_exists_theta_pure_moebius_moment_gt (fun T => C * T ^ K))).exists
  linarith [hunif θ hθ T hT1]

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

