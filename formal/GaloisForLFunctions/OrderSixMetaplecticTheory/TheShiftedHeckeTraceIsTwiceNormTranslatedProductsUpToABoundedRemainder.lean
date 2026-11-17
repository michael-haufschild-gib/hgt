import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheShiftedHeckeTraceCarriesTheShiftPhase
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsTwiceNormThetaSquaresUpToABoundedRemainder
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheShiftedFractionalTraceIsAJacobiMultipleOfTheTranslatedProduct

/-!
# The shifted Hecke trace is `2N(p)` translated products up to a bounded remainder

For a primary prime `p` and the shift `ω`,

`R^ω_p = Tr_pF^ω − 2N(p) F_ω`,   `F_ω(w) = θ_s(T_ωw)θ_s(T_{−ω}w)`   (`PrimaryPrime.heckeShiftRemainder`),

is a bounded remainder of multiplier `κ⁻¹` (`heckeShiftRemainder_remainderData`):

* on the standard strip the shifted Hecke points have heights `|p|v` and `v/|p|`, where `θ_s = cv^{2/3} + O(v^{−3})`;
  the constant parts cancel as for the unshifted trace (`c(|p|v)^{2/3}·c(v/|p|)^{2/3} = c²v^{4/3}`,
  `Σ_{y≢0}(3y/p)₃ = 0`; `norm_heckeShiftRemainder_strip`);
* at a point `Mx` the Hecke points are `N'Ux` with first column `(pM₀₀, M₁₀)/g` resp. `(M₀₀, pM₁₀)/g`, `g ∣ p`. As
  `p ≡ 1 mod 3`, after the shifts `±ω` the column determinants are `D(M) ∓ N(M₁₀)` up to the factor `N(g)`
  (`theta_shiftHigh_decay`, `theta_shiftLow_decay`): unless `M` lies over `∞` (`D(M) = N(M₁₀) = 0` mod `3`), one point of
  every pair is ramified and decays exponentially, against linear growth of the other (`norm_heckeShiftRemainder_off`).
  Over `∞` the point is a level-three translate of a point of the strip.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- **`θ_s` grows at most linearly above any height**, at every integral point. -/
theorem sourceTheta_integral_growth (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : SL(2, O)) (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖sourceTheta (integralComplexMatrix N • upperPoint z v hv)‖ ≤ C * (1 + v) := by
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height a ha
  obtain ⟨C₂, β, hC₂, hβ, hram⟩ := sourceTheta_ramified_decay a ha
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue
  refine ⟨‖c‖ + C₁ / a ^ 3 + C₂, by positivity, fun N z v hv hav => ?_⟩
  obtain ⟨G, j, T, hT, -, hu1, hdec'⟩ := three_cusp_decomposition N
  obtain ⟨z₃, v₃, hv₃, hpt₃⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hv₃e : v₃ = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hpt₃, hyperbolicHeight_upperPoint] at h
    exact h
  subst hv₃e
  rw [hdec', map_mul, map_mul, mul_smul, mul_smul, ← hpt₃]
  change ‖cubicSourceResidualFunction _‖ ≤ _
  rw [cubicSourceResidualFunction_automorphy, norm_mul, norm_extendedComplexCharacter, one_mul]
  by_cases hj : j = 0
  · subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    rw [hc1, map_one, one_smul]
    have hd := hdec v₃ hv₃ hav z₃
    have hcv : ‖c * (v₃ : ℂ) ^ (2 / 3 : ℂ)‖ ≤ ‖c‖ * (1 + v₃) := by
      rw [norm_mul, norm_cpow_two_thirds hv₃]
      exact mul_le_mul_of_nonneg_left (PrimaryPrime.rpow_two_thirds_le v₃ hv₃.le) (norm_nonneg _)
    have hC1 : C₁ / v₃ ^ 3 ≤ C₁ / a ^ 3 :=
      div_le_div_of_nonneg_left hC₁ (by positivity) (pow_le_pow_left₀ ha.le hav 3)
    have htot : ‖cubicSourceResidualFunction (upperPoint z₃ v₃ hv₃)‖ ≤ ‖c‖ * (1 + v₃) + C₁ / a ^ 3 := by
      have := norm_le_insert' (cubicSourceResidualFunction (upperPoint z₃ v₃ hv₃)) (c * (v₃ : ℂ) ^ (2 / 3 : ℂ))
      linarith
    refine htot.trans ?_
    nlinarith [norm_nonneg c, mul_nonneg (div_nonneg hC₁ (pow_nonneg ha.le 3)) hv₃.le, mul_nonneg hC₂ hv₃.le]
  · have hr := hram (cuspRepresentative j) (colRes_cuspRepresentative j hj) z₃ v₃ hv₃ hav
    have he : Real.exp (-β * v₃) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    change ‖sourceTheta _‖ ≤ _
    refine hr.trans ((mul_le_of_le_one_right hC₂ he).trans ?_)
    nlinarith [norm_nonneg c, mul_nonneg (norm_nonneg c) hv₃.le, div_nonneg hC₁ (pow_nonneg ha.le 3),
      mul_nonneg (div_nonneg hC₁ (pow_nonneg ha.le 3)) hv₃.le, mul_nonneg hC₂ hv₃.le]

theorem integralTranslation_mul_col (b : O) (N : SL(2, O)) :
    (integralTranslation b * N) 0 0 = N 0 0 + b * N 1 0 ∧ (integralTranslation b * N) 1 0 = N 1 0 := by
  constructor <;> simp [integralTranslation, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `R^ω_p = Tr_pF^ω − 2N(p) F_ω`. -/
def heckeShiftRemainder (w : HyperbolicSpace) : ℂ :=
  P.heckeShiftTrace sourceTheta omega w - 2 * (Fintype.card P.Res : ℂ) * translatedThetaProduct w

theorem heckeShiftRemainder_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.heckeShiftRemainder (complexMatrix M • w) = (complexCharacter M)⁻¹ * P.heckeShiftRemainder w := by
  rw [heckeShiftRemainder, heckeShiftRemainder, P.heckeShiftTrace_automorphy sourceTheta sourceTheta_automorphy,
    complexCharacter_sq_eq_inv, translatedThetaProduct_automorphy]
  ring

theorem norm_heckeShiftRemainder_levelThree (M : levelThree) (w : HyperbolicSpace) :
    ‖P.heckeShiftRemainder (complexMatrix M • w)‖ = ‖P.heckeShiftRemainder w‖ := by
  rw [P.heckeShiftRemainder_automorphy, norm_mul, norm_inv, norm_complexCharacter, inv_one, one_mul]

/-! ### The standard strip -/

theorem heckeHigh_shift_point (b : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeHigh (fun y => sourceTheta (integralComplexMatrix (integralTranslation b) • y)) (upperPoint z v hv) =
      sourceTheta (upperPoint (ringComplex P.p * z + ringComplex b) (‖ringComplex P.p‖ * v) (mul_pos P.norm_pos hv)) := by
  simp only [heckeHigh]
  rw [P.dilation_upperPoint, integralTranslation_action]

/-- **`R^ω_p = O(v^{−7/3})` on the standard strip above any fixed height.** -/
theorem norm_heckeShiftRemainder_strip (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.heckeShiftRemainder (upperPoint z v hv)‖ ≤ K * v ^ (-(7 : ℝ) / 3) := by
  have hn := P.norm_pos
  have hρ1 := P.one_le_norm
  set ρ := ‖ringComplex P.p‖ with hρdef
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height (a / ρ) (div_pos ha hn)
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue with hcdef
  set N : ℝ := (Fintype.card P.Res : ℝ) with hNdef
  have hN0 : 0 ≤ N := by positivity
  refine ⟨N * (N + 4) * (2 * ‖c‖ * ρ ^ ((2 : ℝ) / 3) * (C₁ * ρ ^ 3) + (C₁ * ρ ^ 3) ^ 2 * a ^ (-(11 : ℝ) / 3)),
    by positivity, fun z v hv hav => ?_⟩
  have hvA : 0 < ρ * v := mul_pos hn hv
  have hvB : 0 < v / ρ := div_pos hv hn
  set PP := c * ((ρ * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) with hPPdef
  set Q := c * ((v / ρ : ℝ) : ℂ) ^ (2 / 3 : ℂ) with hQdef
  set R := c * (v : ℂ) ^ (2 / 3 : ℂ) with hRdef
  have hPQ : PP * Q = R * R := by
    rw [hPPdef, hQdef, hRdef, show c * ((ρ * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) * (c * ((v / ρ : ℝ) : ℂ) ^ (2 / 3 : ℂ)) =
      c ^ 2 * (((ρ * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) * ((v / ρ : ℝ) : ℂ) ^ (2 / 3 : ℂ)) by ring,
      cpow_mul_mul_cpow_div _ _ hn hv]
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    rw [show (4 / 3 : ℂ) = 2 / 3 + 2 / 3 by norm_num, Complex.cpow_add _ _ hv0]
    ring
  set M := ‖c‖ * ρ ^ ((2 : ℝ) / 3) * v ^ ((2 : ℝ) / 3) with hMdef
  set D := C₁ * ρ ^ 3 / v ^ 3 with hDdef
  have hρ23 : 1 ≤ ρ ^ ((2 : ℝ) / 3) := Real.one_le_rpow hρ1 (by norm_num)
  have hv23 : 0 ≤ v ^ ((2 : ℝ) / 3) := by positivity
  have hcv : ‖c‖ * v ^ ((2 : ℝ) / 3) ≤ M := by
    rw [hMdef]
    have := mul_le_mul_of_nonneg_left hρ23 (mul_nonneg (norm_nonneg c) hv23)
    nlinarith
  have hPM : ‖PP‖ ≤ M := by
    rw [hPPdef, norm_mul, norm_cpow_two_thirds hvA, Real.mul_rpow hn.le hv.le, hMdef]
    ring_nf
    rfl
  have hQM : ‖Q‖ ≤ M := by
    rw [hQdef, norm_mul, norm_cpow_two_thirds hvB]
    have h1 : (v / ρ) ^ ((2 : ℝ) / 3) ≤ v ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow hvB.le (div_le_self hv.le hρ1) (by norm_num)
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans hcv
  have hRM : ‖R‖ ≤ M := by
    rw [hRdef, norm_mul, norm_cpow_two_thirds hv]
    exact hcv
  have hcube : ∀ (ζ : ℂ) (h : ℝ) (hh : 0 < h), v / ρ ≤ h →
      ‖sourceTheta (upperPoint ζ h hh) - c * (h : ℂ) ^ (2 / 3 : ℂ)‖ ≤ D := by
    intro ζ h hh hle
    have hd := hdec h hh (le_trans (div_le_div_of_nonneg_right hav hn.le) hle) ζ
    refine hd.trans ?_
    rw [hDdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (v / ρ) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hvB.le hle 3
    have e : (v / ρ) ^ 3 * ρ ^ 3 = v ^ 3 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ C₁ * ρ ^ 3)]
  have hle1 : v / ρ ≤ ρ * v := le_trans (div_le_self hv.le hρ1) (le_mul_of_one_le_left hv.le hρ1)
  have hA : ∀ b : O, ‖sourceTheta (upperPoint (ringComplex P.p * z + ringComplex b) (ρ * v) hvA) - PP‖ ≤ D :=
    fun b => hcube _ _ hvA hle1
  have hB : ∀ b s : O, ‖sourceTheta (upperPoint ((z + 3 * ringComplex s) / ringComplex P.p + ringComplex b) (v / ρ) hvB) -
      Q‖ ≤ D := fun b s => hcube _ _ hvB le_rfl
  have h0 : ∀ b : O, ‖sourceTheta (upperPoint (z + ringComplex b) v hv) - R‖ ≤ D :=
    fun b => hcube _ _ hv (div_le_self hv.le hρ1)
  set θA : O → ℂ := fun b => sourceTheta (upperPoint (ringComplex P.p * z + ringComplex b) (ρ * v) hvA)
  set θB : O → O → ℂ := fun b s =>
    sourceTheta (upperPoint ((z + 3 * ringComplex s) / ringComplex P.p + ringComplex b) (v / ρ) hvB)
  set θ0 : O → ℂ := fun b => sourceTheta (upperPoint (z + ringComplex b) v hv)
  set χ : {y : P.Res // y ≠ 0} → ℂ := fun y => ringComplex (symbol (3 * P.lift y.1) P.p)
  have htr : P.heckeShiftTrace sourceTheta omega (upperPoint z v hv) =
      (∑ x : P.Res, θA omega * θB (-omega) (P.lift x)) + ((∑ x : P.Res, θB omega (P.wShift + P.lift x) * θA (-omega)) +
        ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
          θB (-omega) (P.lift x)) := by
    rw [P.heckeShiftTrace_eq_hecke sourceTheta sourceTheta_automorphy]
    simp only [P.heckeHigh_shift_point, P.heckeLow_shift_point]
    rfl
  have hF : translatedThetaProduct (upperPoint z v hv) = θ0 omega * θ0 (-omega) := by
    simp only [translatedThetaProduct, integralTranslation_action]
    rfl
  have hident : P.heckeShiftRemainder (upperPoint z v hv) =
      (∑ x : P.Res, (θA omega * θB (-omega) (P.lift x) - PP * Q)) +
        (∑ x : P.Res, (θB omega (P.wShift + P.lift x) * θA (-omega) - Q * PP)) +
        (∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
          θB (-omega) (P.lift x) - Q * Q)) - 2 * (Fintype.card P.Res : ℂ) * (θ0 omega * θ0 (-omega) - R * R) := by
    have hχ : ∑ y : {y : P.Res // y ≠ 0}, χ y = 0 := P.sum_symbol_eq_zero
    have e3 : ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
        θB (-omega) (P.lift x) - Q * Q) =
        ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
          θB (-omega) (P.lift x) - ∑ _x : P.Res, Q * Q * ∑ y : {y : P.Res // y ≠ 0}, χ y := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [heckeShiftRemainder, htr, hF, Finset.sum_sub_distrib, Finset.sum_sub_distrib, e3, hχ]
    simp only [mul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_zero]
    linear_combination (2 * (Fintype.card P.Res : ℂ)) * hPQ
  set Eb := 2 * M * D + D ^ 2 with hEbdef
  have hEb : ∀ X Y PP' QQ : ℂ, ‖PP'‖ ≤ M → ‖QQ‖ ≤ M → ‖X - PP'‖ ≤ D → ‖Y - QQ‖ ≤ D →
      ‖X * Y - PP' * QQ‖ ≤ Eb := fun X Y PP' QQ h1 h2 h3 h4 => norm_mul_sub_mul_le h1 h2 h3 h4
  have hEb0 : 0 ≤ Eb := (norm_nonneg _).trans (hEb _ _ _ _ hPM hQM (hA omega) (hB omega 0))
  have hcardS : (Fintype.card {y : P.Res // y ≠ 0} : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_subtype_le _
  have hs1 : ‖∑ x : P.Res, (θA omega * θB (-omega) (P.lift x) - PP * Q)‖ ≤ N * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖θA omega * θB (-omega) (P.lift x) - PP * Q‖ ≤ ∑ _x : P.Res, Eb :=
          Finset.sum_le_sum fun x _ => hEb _ _ _ _ hPM hQM (hA _) (hB _ _)
      _ = N * Eb := by simp [hNdef]
  have hs2 : ‖∑ x : P.Res, (θB omega (P.wShift + P.lift x) * θA (-omega) - Q * PP)‖ ≤ N * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖θB omega (P.wShift + P.lift x) * θA (-omega) - Q * PP‖ ≤ ∑ _x : P.Res, Eb :=
          Finset.sum_le_sum fun x _ => hEb _ _ _ _ hQM hPM (hB _ _) (hA _)
      _ = N * Eb := by simp [hNdef]
  have hs3 : ‖∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
      θB (-omega) (P.lift x) - Q * Q)‖ ≤ N * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖∑ y : {y : P.Res // y ≠ 0}, χ y * (θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
          θB (-omega) (P.lift x) - Q * Q)‖ ≤ ∑ _x : P.Res, N * Eb := by
          refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
          calc ∑ y : {y : P.Res // y ≠ 0}, ‖χ y * (θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
                θB (-omega) (P.lift x) - Q * Q)‖
              ≤ ∑ _y : {y : P.Res // y ≠ 0}, Eb := Finset.sum_le_sum fun y _ => by
                rw [norm_mul]
                exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_symbol_le y)).trans
                  (hEb _ _ _ _ hQM hQM (hB _ _) (hB _ _))
            _ = (Fintype.card {y : P.Res // y ≠ 0} : ℝ) * Eb := by simp
            _ ≤ N * Eb := mul_le_mul_of_nonneg_right hcardS hEb0
      _ = N * (N * Eb) := by simp [hNdef]
  have hs4 : ‖2 * (Fintype.card P.Res : ℂ) * (θ0 omega * θ0 (-omega) - R * R)‖ ≤ 2 * N * Eb := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (hEb _ _ _ _ hRM hRM (h0 _) (h0 _)) (by positivity)
  have htotal : ‖P.heckeShiftRemainder (upperPoint z v hv)‖ ≤ N * (N + 4) * Eb := by
    rw [hident]
    calc _ ≤ ‖(∑ x : P.Res, (θA omega * θB (-omega) (P.lift x) - PP * Q)) +
            (∑ x : P.Res, (θB omega (P.wShift + P.lift x) * θA (-omega) - Q * PP)) +
            (∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB omega (P.lift x - P.lowBeta (P.lift y.1)) *
              θB (-omega) (P.lift x) - Q * Q))‖ +
            ‖2 * (Fintype.card P.Res : ℂ) * (θ0 omega * θ0 (-omega) - R * R)‖ := norm_sub_le _ _
      _ ≤ (N * Eb + N * Eb + N * (N * Eb)) + 2 * N * Eb := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hs1 hs2)) hs3)
      _ = N * (N + 4) * Eb := by ring
  refine htotal.trans ?_
  have hv3 : v ^ ((2 : ℝ) / 3) / v ^ 3 = v ^ (-(7 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hv]
    norm_num
  have hv6 : 1 / v ^ 6 ≤ a ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
    have hsplit : 1 / v ^ 6 = v ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
      rw [← Real.rpow_add hv, one_div, ← Real.rpow_natCast, ← Real.rpow_neg hv.le]
      norm_num
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hav (by norm_num)) (by positivity)
  have hEbv : Eb = 2 * ‖c‖ * ρ ^ ((2 : ℝ) / 3) * (C₁ * ρ ^ 3) * (v ^ ((2 : ℝ) / 3) / v ^ 3) +
      (C₁ * ρ ^ 3) ^ 2 * (1 / v ^ 6) := by
    rw [hEbdef, hMdef, hDdef]
    field_simp
  rw [hEbv, hv3]
  have h6 := mul_le_mul_of_nonneg_left hv6 (by positivity : (0 : ℝ) ≤ (C₁ * ρ ^ 3) ^ 2)
  have hNN : 0 ≤ N * (N + 4) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 hNN, norm_nonneg c, Real.rpow_nonneg hv.le (-(7 : ℝ) / 3),
    Real.rpow_nonneg hn.le ((2 : ℝ) / 3)]

/-! ### Points away from `∞` -/

theorem dilation_point (b : O) (M N' : SL(2, O)) (U : SL(2, ℂ))
    (hfac : P.dilation * integralComplexMatrix M = integralComplexMatrix N' * U) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (z' : ℂ) (v' : ℝ) (hv' : 0 < v') (hpt : upperPoint z' v' hv' = U • upperPoint z v hv) :
    integralComplexMatrix (integralTranslation b) • P.dilation • integralComplexMatrix M • upperPoint z v hv =
      integralComplexMatrix (integralTranslation b * N') • upperPoint z' v' hv' := by
  rw [← mul_smul P.dilation, hfac, mul_smul, ← hpt, ← mul_smul, ← map_mul]

theorem contraction_point (b : O) (M N' : SL(2, O)) (U : SL(2, ℂ))
    (hfac : P.contraction * integralComplexMatrix M = integralComplexMatrix N' * U) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (z' : ℂ) (v' : ℝ) (hv' : 0 < v') (hpt : upperPoint z' v' hv' = U • upperPoint z v hv) :
    integralComplexMatrix (integralTranslation b) • P.contraction • integralComplexMatrix M • upperPoint z v hv =
      integralComplexMatrix (integralTranslation b * N') • upperPoint z' v' hv' := by
  rw [← mul_smul P.contraction, hfac, mul_smul, ← hpt, ← mul_smul, ← map_mul]

/-- The height `v|g|²/|p|` of a Hecke point lies in `[v/|p|, |p|v]`. -/
theorem hecke_height_bounds {g : O} (hg0 : g ≠ 0) (hgp : g ∣ P.p) (U : SL(2, ℂ)) (hU10 : U 1 0 = 0)
    (hU00 : ‖U 0 0‖ ^ 2 = ‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (z' : ℂ) (v' : ℝ) (hv' : 0 < v') (hpt : upperPoint z' v' hv' = U • upperPoint z v hv) :
    v / ‖ringComplex P.p‖ ≤ v' ∧ v' ≤ ‖ringComplex P.p‖ * v := by
  have hn := P.norm_pos
  have hvv : v' = v * (‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖) := by
    have h := height_upper_triangular_complex U hU10 z v hv
    rw [← hpt, hyperbolicHeight_upperPoint, hU00] at h
    exact h
  have hg1 := one_le_norm_sq_ringComplex hg0
  have hgle := norm_sq_le_of_dvd P.ne_zero hgp
  rw [hvv, mul_div_assoc']
  constructor
  · exact div_le_div_of_nonneg_right (by nlinarith) hn.le
  · rw [div_le_iff₀ hn]
    nlinarith [mul_le_mul_of_nonneg_left hgle hv.le]

theorem dilation_factor_dvd (M N' : SL(2, O)) {g : O} (hp : P.p * M 0 0 = g * N' 0 0) (hq : M 1 0 = g * N' 1 0) :
    g ∣ P.p := by
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
  exact ⟨N' 0 0 * M 1 1 - P.p * M 0 1 * N' 1 0,
    by linear_combination (-P.p) * hM + M 1 1 * hp - P.p * M 0 1 * hq⟩

theorem contraction_factor_dvd (M N' : SL(2, O)) {g : O} (hp : M 0 0 = g * N' 0 0) (hq : P.p * M 1 0 = g * N' 1 0) :
    g ∣ P.p := by
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
  exact ⟨P.p * N' 0 0 * M 1 1 - M 0 1 * N' 1 0,
    by linear_combination (-P.p) * hM + P.p * M 1 1 * hp - M 0 1 * hq⟩

/-- **Exponential decay at the shifted dilate point** when `D(M) − N(M₁₀) ≢ 0 mod 3`. -/
theorem theta_shiftHigh_decay (a : ℝ) (ha : 0 < a) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ (M : SL(2, O)), colRes (M 0 0) (M 1 0) - normRes (M 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (integralComplexMatrix (integralTranslation omega) • P.dilation • integralComplexMatrix M •
          upperPoint z v hv)‖ ≤ C * Real.exp (-(β / ‖ringComplex P.p‖) * v) := by
  have hn := P.norm_pos
  obtain ⟨C, β, hC, hβ, hdec⟩ := sourceTheta_ramified_decay (a / ‖ringComplex P.p‖) (div_pos ha hn)
  refine ⟨C, β, hC, hβ, fun M hcol z v hv hav => ?_⟩
  obtain ⟨N', g, hg0, hp, hq, U, hU10, hU00, hfac⟩ := P.dilation_factor M
  obtain ⟨e0, e1⟩ := integralTranslation_mul_col omega N'
  have hc : colRes ((integralTranslation omega * N') 0 0) ((integralTranslation omega * N') 1 0) ≠ 0 := by
    rw [e0, e1]
    refine colRes_ne_zero_of_factor (p := P.p * M 0 0 + omega * M 1 0) (by rw [hp, hq]; ring) hq ?_
    have hx : colRes (P.p * M 0 0 + omega * M 1 0) (M 1 0) = colRes (M 0 0 + omega * M 1 0) (M 1 0) := by
      unfold colRes
      rw [cuspResidue_congr (show (3 : O) ∣ P.p * M 0 0 + omega * M 1 0 - (M 0 0 + omega * M 1 0) from by
        obtain ⟨t, ht⟩ := P.three_dvd_sub_one
        exact ⟨t * M 0 0, by linear_combination M 0 0 * ht⟩)]
    rw [hx, colRes_add_omega]
    exact hcol
  obtain ⟨z', v', hv', hpt'⟩ := upperPoint_surjective (U • upperPoint z v hv)
  have hvlow := (P.hecke_height_bounds hg0 (P.dilation_factor_dvd M N' hp hq) U hU10 hU00 z v hv z' v' hv' hpt').1
  have hav' : a / ‖ringComplex P.p‖ ≤ v' := le_trans (div_le_div_of_nonneg_right hav hn.le) hvlow
  rw [P.dilation_point omega M N' U hfac z v hv z' v' hv' hpt']
  refine (hdec _ hc z' v' hv' hav').trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have : β * (v / ‖ringComplex P.p‖) ≤ β * v' := mul_le_mul_of_nonneg_left hvlow hβ.le
  rw [show -(β / ‖ringComplex P.p‖) * v = -(β * (v / ‖ringComplex P.p‖)) by ring]
  linarith

/-- **Exponential decay at the shifted contracted point** when `D(M) + N(M₁₀) ≢ 0 mod 3`. -/
theorem theta_shiftLow_decay (a : ℝ) (ha : 0 < a) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ (M : SL(2, O)), colRes (M 0 0) (M 1 0) + normRes (M 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • P.contraction • integralComplexMatrix M •
          upperPoint z v hv)‖ ≤ C * Real.exp (-(β / ‖ringComplex P.p‖) * v) := by
  have hn := P.norm_pos
  obtain ⟨C, β, hC, hβ, hdec⟩ := sourceTheta_ramified_decay (a / ‖ringComplex P.p‖) (div_pos ha hn)
  refine ⟨C, β, hC, hβ, fun M hcol z v hv hav => ?_⟩
  obtain ⟨N', g, hg0, hp, hq, U, hU10, hU00, hfac⟩ := P.contraction_factor M
  obtain ⟨e0, e1⟩ := integralTranslation_mul_col (-omega) N'
  have hc : colRes ((integralTranslation (-omega) * N') 0 0) ((integralTranslation (-omega) * N') 1 0) ≠ 0 := by
    rw [e0, e1]
    refine colRes_ne_zero_of_factor (p := M 0 0 + -omega * (P.p * M 1 0)) (by rw [hp, hq]; ring) hq ?_
    have hnr : normRes (P.p * M 1 0) = normRes (M 1 0) := by
      unfold normRes
      rw [cuspResidue_congr (show (3 : O) ∣ P.p * M 1 0 - M 1 0 from by
        obtain ⟨t, ht⟩ := P.three_dvd_sub_one
        exact ⟨t * M 1 0, by linear_combination M 1 0 * ht⟩)]
    rw [colRes_add_neg_omega, P.colRes_p_right, hnr]
    exact hcol
  obtain ⟨z', v', hv', hpt'⟩ := upperPoint_surjective (U • upperPoint z v hv)
  have hvlow :=
    (P.hecke_height_bounds hg0 (P.contraction_factor_dvd M N' hp hq) U hU10 hU00 z v hv z' v' hv' hpt').1
  have hav' : a / ‖ringComplex P.p‖ ≤ v' := le_trans (div_le_div_of_nonneg_right hav hn.le) hvlow
  rw [P.contraction_point (-omega) M N' U hfac z v hv z' v' hv' hpt']
  refine (hdec _ hc z' v' hv' hav').trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have : β * (v / ‖ringComplex P.p‖) ≤ β * v' := mul_le_mul_of_nonneg_left hvlow hβ.le
  rw [show -(β / ‖ringComplex P.p‖) * v = -(β * (v / ‖ringComplex P.p‖)) by ring]
  linarith

/-- **Linear growth at the shifted Hecke points.** -/
theorem theta_shiftHecke_growth (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : O) (M : SL(2, O)) (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖sourceTheta (integralComplexMatrix (integralTranslation b) • P.dilation • integralComplexMatrix M •
          upperPoint z v hv)‖ ≤ C * (1 + v) ∧
      ‖sourceTheta (integralComplexMatrix (integralTranslation b) • P.contraction • integralComplexMatrix M •
          upperPoint z v hv)‖ ≤ C * (1 + v) := by
  have hn := P.norm_pos
  have hρ1 := P.one_le_norm
  obtain ⟨C, hC, hg⟩ := sourceTheta_integral_growth (a / ‖ringComplex P.p‖) (div_pos ha hn)
  refine ⟨C * ‖ringComplex P.p‖, by positivity, fun b M z v hv hav => ⟨?_, ?_⟩⟩
  · obtain ⟨N', g, hg0, hp, hq, U, hU10, hU00, hfac⟩ := P.dilation_factor M
    obtain ⟨z', v', hv', hpt'⟩ := upperPoint_surjective (U • upperPoint z v hv)
    obtain ⟨hlo, hhi⟩ :=
      P.hecke_height_bounds hg0 (P.dilation_factor_dvd M N' hp hq) U hU10 hU00 z v hv z' v' hv' hpt'
    rw [P.dilation_point b M N' U hfac z v hv z' v' hv' hpt']
    refine (hg _ z' v' hv' (le_trans (div_le_div_of_nonneg_right hav hn.le) hlo)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hhi hC, mul_nonneg hC hv.le]
  · obtain ⟨N', g, hg0, hp, hq, U, hU10, hU00, hfac⟩ := P.contraction_factor M
    obtain ⟨z', v', hv', hpt'⟩ := upperPoint_surjective (U • upperPoint z v hv)
    obtain ⟨hlo, hhi⟩ :=
      P.hecke_height_bounds hg0 (P.contraction_factor_dvd M N' hp hq) U hU10 hU00 z v hv z' v' hv' hpt'
    rw [P.contraction_point b M N' U hfac z v hv z' v' hv' hpt']
    refine (hg _ z' v' hv' (le_trans (div_le_div_of_nonneg_right hav hn.le) hlo)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hhi hC, mul_nonneg hC hv.le]

/-- **The translated product is bounded away from `∞`.** -/
theorem norm_translatedThetaProduct_off (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : SL(2, O)), (colRes (M 0 0) (M 1 0) ≠ 0 ∨ normRes (M 1 0) ≠ 0) →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖translatedThetaProduct (integralComplexMatrix M • upperPoint z v hv)‖ ≤ K := by
  obtain ⟨C₁, β, hC₁, hβ, hdec⟩ := sourceTheta_ramified_decay a ha
  obtain ⟨C₂, hC₂, hgr⟩ := sourceTheta_integral_growth a ha
  refine ⟨C₁ * C₂ * (1 + 1 / β), by positivity, fun M hM z v hv hav => ?_⟩
  have hk := one_add_mul_exp_le β v hβ hv.le
  have hpt : ∀ b : O, integralComplexMatrix (integralTranslation b) • integralComplexMatrix M • upperPoint z v hv =
      integralComplexMatrix (integralTranslation b * M) • upperPoint z v hv := fun b => by
    rw [← mul_smul, ← map_mul]
  obtain ⟨eP0, eP1⟩ := integralTranslation_mul_col omega M
  obtain ⟨eN0, eN1⟩ := integralTranslation_mul_col (-omega) M
  unfold translatedThetaProduct
  rw [hpt, hpt, norm_mul]
  by_cases hP0 : colRes (M 0 0) (M 1 0) - normRes (M 1 0) = 0
  · have hN0 : colRes (M 0 0) (M 1 0) + normRes (M 1 0) ≠ 0 := by
      intro hN0
      obtain ⟨hA, hB⟩ := zmod3_shift_cases _ _ hP0 hN0
      rcases hM with hM | hM
      · exact hM hA
      · exact hM hB
    have d := hdec (integralTranslation (-omega) * M) (by rw [eN0, eN1, colRes_add_neg_omega]; exact hN0) z v hv hav
    have g := hgr (integralTranslation omega * M) z v hv hav
    calc _ ≤ (C₂ * (1 + v)) * (C₁ * Real.exp (-β * v)) := mul_le_mul g d (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * ((1 + v) * Real.exp (-β * v)) := by ring
      _ ≤ C₁ * C₂ * (1 + 1 / β) := mul_le_mul_of_nonneg_left hk (by positivity)
  · have d := hdec (integralTranslation omega * M) (by rw [eP0, eP1, colRes_add_omega]; exact hP0) z v hv hav
    have g := hgr (integralTranslation (-omega) * M) z v hv hav
    calc _ ≤ (C₁ * Real.exp (-β * v)) * (C₂ * (1 + v)) := mul_le_mul d g (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * ((1 + v) * Real.exp (-β * v)) := by ring
      _ ≤ C₁ * C₂ * (1 + 1 / β) := mul_le_mul_of_nonneg_left hk (by positivity)

/-- **Away from `∞` the shifted Hecke remainder is bounded**: one point of every pair is ramified. -/
theorem norm_heckeShiftRemainder_off (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : SL(2, O)), (colRes (M 0 0) (M 1 0) ≠ 0 ∨ normRes (M 1 0) ≠ 0) →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖P.heckeShiftRemainder (integralComplexMatrix M • upperPoint z v hv)‖ ≤ K := by
  have hn := P.norm_pos
  obtain ⟨C₁, β₁, hC₁, hβ₁, hdH⟩ := P.theta_shiftHigh_decay a ha
  obtain ⟨C₂, β₂, hC₂, hβ₂, hdL⟩ := P.theta_shiftLow_decay a ha
  obtain ⟨C₃, hC₃, hgr⟩ := P.theta_shiftHecke_growth a ha
  obtain ⟨K₂, hK₂, hF⟩ := norm_translatedThetaProduct_off a ha
  have hγ₁ : 0 < β₁ / ‖ringComplex P.p‖ := div_pos hβ₁ hn
  have hγ₂ : 0 < β₂ / ‖ringComplex P.p‖ := div_pos hβ₂ hn
  set E : ℝ := C₁ * C₃ * (1 + 1 / (β₁ / ‖ringComplex P.p‖)) + C₂ * C₃ * (1 + 1 / (β₂ / ‖ringComplex P.p‖)) with hEdef
  have hE1 : 0 ≤ C₁ * C₃ * (1 + 1 / (β₁ / ‖ringComplex P.p‖)) := by positivity
  have hE2 : 0 ≤ C₂ * C₃ * (1 + 1 / (β₂ / ‖ringComplex P.p‖)) := by positivity
  refine ⟨(Fintype.card P.Index : ℝ) * E + 2 * (Fintype.card P.Res : ℝ) * K₂, by positivity,
    fun M hM z v hv hav => ?_⟩
  have hpair : ∀ N : SL(2, O), colRes (N 0 0) (N 1 0) = colRes (M 0 0) (M 1 0) → normRes (N 1 0) = normRes (M 1 0) →
      ‖sourceTheta (integralComplexMatrix (integralTranslation omega) • P.dilation • integralComplexMatrix N •
          upperPoint z v hv) *
        sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • P.contraction • integralComplexMatrix N •
          upperPoint z v hv)‖ ≤ E := by
    intro N hcN hnN
    rw [norm_mul]
    by_cases hP0 : colRes (N 0 0) (N 1 0) - normRes (N 1 0) = 0
    · have hN0 : colRes (N 0 0) (N 1 0) + normRes (N 1 0) ≠ 0 := by
        intro hN0
        obtain ⟨hA, hB⟩ := zmod3_shift_cases _ _ hP0 hN0
        rcases hM with hM | hM
        · exact hM (by rw [← hcN]; exact hA)
        · exact hM (by rw [← hnN]; exact hB)
      have d := hdL N hN0 z v hv hav
      have g := (hgr omega N z v hv hav).1
      have hk := one_add_mul_exp_le _ v hγ₂ hv.le
      calc _ ≤ (C₃ * (1 + v)) * (C₂ * Real.exp (-(β₂ / ‖ringComplex P.p‖) * v)) :=
            mul_le_mul g d (norm_nonneg _) (by positivity)
        _ = C₂ * C₃ * ((1 + v) * Real.exp (-(β₂ / ‖ringComplex P.p‖) * v)) := by ring
        _ ≤ C₂ * C₃ * (1 + 1 / (β₂ / ‖ringComplex P.p‖)) := mul_le_mul_of_nonneg_left hk (by positivity)
        _ ≤ E := by rw [hEdef]; linarith
    · have d := hdH N hP0 z v hv hav
      have g := (hgr (-omega) N z v hv hav).2
      have hk := one_add_mul_exp_le _ v hγ₁ hv.le
      calc _ ≤ (C₁ * Real.exp (-(β₁ / ‖ringComplex P.p‖) * v)) * (C₃ * (1 + v)) :=
            mul_le_mul d g (norm_nonneg _) (by positivity)
        _ = C₁ * C₃ * ((1 + v) * Real.exp (-(β₁ / ‖ringComplex P.p‖) * v)) := by ring
        _ ≤ C₁ * C₃ * (1 + 1 / (β₁ / ‖ringComplex P.p‖)) := mul_le_mul_of_nonneg_left hk (by positivity)
        _ ≤ E := by rw [hEdef]; linarith
  have hTr : ‖P.heckeShiftTrace sourceTheta omega (integralComplexMatrix M • upperPoint z v hv)‖ ≤
      (Fintype.card P.Index : ℝ) * E := by
    rw [P.heckeShiftTrace_eq_sum sourceTheta sourceTheta_automorphy]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : P.Index, E := Finset.sum_le_sum fun i _ => by
          rw [norm_mul, norm_inv, norm_pow, norm_complexCharacter, one_pow, inv_one, one_mul]
          unfold heckeShiftCorrelation
          rw [show complexMatrix (P.rep i) • integralComplexMatrix M • upperPoint z v hv =
              integralComplexMatrix ((P.rep i : SL(2, O)) * M) • upperPoint z v hv by
            rw [complexMatrix_eq, ← mul_smul, ← map_mul]]
          exact hpair _ (colRes_levelThree_mul _ M) (by simp only [normRes, cuspResidue_levelThree_col])
      _ = (Fintype.card P.Index : ℝ) * E := by simp
  have hF' := hF M hM z v hv hav
  rw [heckeShiftRemainder]
  calc _ ≤ ‖P.heckeShiftTrace sourceTheta omega (integralComplexMatrix M • upperPoint z v hv)‖ +
        ‖2 * (Fintype.card P.Res : ℂ) * translatedThetaProduct (integralComplexMatrix M • upperPoint z v hv)‖ :=
        norm_sub_le _ _
    _ ≤ (Fintype.card P.Index : ℝ) * E + 2 * (Fintype.card P.Res : ℝ) * K₂ := by
        refine add_le_add hTr ?_
        rw [norm_mul, norm_mul, Complex.norm_natCast, show ‖(2 : ℂ)‖ = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left hF' (by positivity)

/-! ### The global bound -/

/-- **`R^ω_p` is bounded on `ℍ³`.** -/
theorem heckeShiftRemainder_bounded : ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖P.heckeShiftRemainder w‖ ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨K₀, hK₀, hstrip⟩ := P.norm_heckeShiftRemainder_strip a₀ ha₀
  obtain ⟨K₁, hK₁, hoff⟩ := P.norm_heckeShiftRemainder_off a₀ ha₀
  refine ⟨K₀ * a₀ ^ (-(7 : ℝ) / 3) + K₁, fun w => ?_⟩
  have hK₀' : 0 ≤ K₀ * a₀ ^ (-(7 : ℝ) / 3) := mul_nonneg hK₀ (Real.rpow_nonneg ha₀.le _)
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨G, j, T, hT, hu0, hu1, hdec⟩ := three_cusp_decomposition M⁻¹
  obtain ⟨n, r, hG⟩ := G.2
  set M' : SL(2, O) := rationalEmbedding r * cuspRepresentative j * T with hM'
  have hw : w = complexMatrix n • integralComplexMatrix M' • upperPoint z v hv := by
    have h1 : w = integralComplexMatrix M⁻¹ • upperPoint z v hv := by
      rw [← hMw, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [h1, hdec, ← hG, complexMatrix_eq, ← mul_smul, ← map_mul, hM']
    congr 2
    simp only [mul_assoc]
  rw [hw, P.norm_heckeShiftRemainder_levelThree]
  by_cases hc : colRes (M' 0 0) (M' 1 0) ≠ 0 ∨ normRes (M' 1 0) ≠ 0
  · exact (hoff M' hc z v hv hfloor).trans (by linarith)
  · simp only [not_or, ne_eq, not_not] at hc
    obtain ⟨hc0, hn0⟩ := hc
    have hdec1 := colRes_cuspDecomp 1 r j T hT
    simp only [OneMemClass.coe_one, one_mul] at hdec1
    have hj : j = 0 := by
      by_contra hj
      rw [← hM'] at hdec1
      rw [hdec1] at hc0
      exact mul_ne_zero (normRes_ne_zero_of_isUnit hu0) (colRes_cuspRepresentative j hj) hc0
    subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    have hM'e : M' = rationalEmbedding r * T := by rw [hM', hc1, mul_one]
    have hr10 : (3 : ℤ) ∣ r 1 0 := by
      have e : M' 1 0 = ((r 1 0 : ℤ) : O) * T 0 0 := by
        rw [hM'e]
        simp [rationalEmbedding, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hT]
      rw [e, normRes_mul, normRes_intCast] at hn0
      have h0 := (mul_eq_zero.mp hn0).resolve_right (normRes_ne_zero_of_isUnit hu0)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
    obtain ⟨n', z', he⟩ := exists_strip_of_three_dvd r hr10 T hT hu0 hu1 z v hv
    rw [hM'e, he, P.norm_heckeShiftRemainder_levelThree]
    refine (hstrip z' v hv hfloor).trans ?_
    have : v ^ (-(7 : ℝ) / 3) ≤ a₀ ^ (-(7 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos ha₀ hfloor (by norm_num)
    nlinarith

theorem heckeShiftTrace_source_continuous : Continuous (P.heckeShiftTrace sourceTheta omega) := by
  have h : P.heckeShiftTrace sourceTheta omega = fun w => ∑ i : P.Index,
      (complexCharacter (P.rep i) ^ 2)⁻¹ * P.heckeShiftCorrelation sourceTheta omega (complexMatrix (P.rep i) • w) :=
    funext (P.heckeShiftTrace_eq_sum sourceTheta sourceTheta_automorphy omega)
  rw [h]
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  unfold heckeShiftCorrelation
  exact ((cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _))).mul
    (cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _)))).comp (continuous_hyperbolic_action _)

theorem heckeShiftRemainder_continuous : Continuous P.heckeShiftRemainder :=
  P.heckeShiftTrace_source_continuous.sub (continuous_const.mul translatedThetaProduct_continuous)

theorem heckeShiftRemainder_memLp : MemLp P.heckeShiftRemainder 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := P.heckeShiftRemainder_bounded
  exact MemLp.of_bound P.heckeShiftRemainder_continuous.measurable.aestronglyMeasurable B (Eventually.of_forall hB)

/-- **`R^ω_p` is a bounded remainder.** -/
theorem heckeShiftRemainder_remainderData : RemainderData P.heckeShiftRemainder where
  automorphy := P.heckeShiftRemainder_automorphy
  measurable := P.heckeShiftRemainder_continuous.measurable
  bounded := P.heckeShiftRemainder_bounded
  high := by
    obtain ⟨K, hK, h⟩ := P.norm_heckeShiftRemainder_strip 2 (by norm_num)
    exact ⟨K, hK, fun z v hv hv2 => h z v hv hv2⟩
  memLp := P.heckeShiftRemainder_memLp

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
