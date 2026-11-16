import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckePointsAtAPrimaryPrimeOfARamifiedCuspAreRamified

/-!
# The Hecke trace at a primary prime is `2N(p)` theta squares up to a bounded remainder

`G'_p = Tr_pθ_s − 2N(p)θ_s²` (`PrimaryPrime.remainder`) is a bounded function on `ℍ³` of multiplier `κ⁻¹` with
`G'_p = O(v^{−7/3})` above any height (`remainder_remainderData`):

* in the standard strip every Hecke point has height `|p|v` or `v/|p|`, where `θ_s = cv^{2/3} + O(v^{−3})`. The
  constant parts cancel: `(c(|p|v)^{2/3})(c(v/|p|)^{2/3}) = (cv^{2/3})²` for the `2N(p)` dilate cosets, and the phases
  of the twisted cosets sum to zero, `Σ_{y≢0}(3y/p)₃ = 0` (`sum_symbol_eq_zero`);
* at the ramified cusps both Hecke points are ramified (`sourceTheta_hecke_ramified`) and `θ_s` is bounded;
* the trace and `θ_s²` are invariant under `SL₂(ℤ)`, which moves every point to the strip or a ramified cusp.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `G'_p = Tr_pθ_s − 2N(p)θ_s²`. -/
def remainder (w : HyperbolicSpace) : ℂ :=
  P.sourceHeckeTrace w - 2 * (Fintype.card P.Res : ℂ) * sourceTheta w ^ 2

theorem sourceHeckeTrace_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.sourceHeckeTrace (complexMatrix M • w) = complexCharacter M ^ 2 * P.sourceHeckeTrace w :=
  P.heckeTrace_automorphy sourceTheta sourceTheta_automorphy M w

theorem sourceHeckeTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    P.sourceHeckeTrace (integralComplexMatrix (rationalEmbedding r) • w) = P.sourceHeckeTrace w :=
  P.heckeTrace_rational sourceTheta sourceTheta_automorphy sourceTheta_rational_inv r w

theorem remainder_rationalExtension (G : rationalExtension) (w : HyperbolicSpace) :
    P.remainder (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G ^ 2 * P.remainder w := by
  obtain ⟨n, r, hG⟩ := G.2
  have hρ : extendedComplexCharacter G = complexCharacter n := rationalExtensionValue_of_product G n r hG
  have hw : integralComplexMatrix (G : SL(2, O)) • w =
      complexMatrix n • (integralComplexMatrix (rationalEmbedding r) • w) := by
    rw [← hG, map_mul, mul_smul]
    rfl
  have hθ := cubicSourceResidualFunction_automorphy G w
  unfold remainder
  rw [show sourceTheta (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G * sourceTheta w from hθ,
    hw, P.sourceHeckeTrace_automorphy, P.sourceHeckeTrace_rational, hρ]
  ring

theorem norm_remainder_rational (G : rationalExtension) (w : HyperbolicSpace) :
    ‖P.remainder (integralComplexMatrix (G : SL(2, O)) • w)‖ = ‖P.remainder w‖ := by
  rw [P.remainder_rationalExtension, norm_mul, norm_pow, norm_extendedComplexCharacter, one_pow, one_mul]

/-! ### The phases of the twisted cosets -/

theorem chi_ne_one : P.chi ≠ 1 := by
  intro h
  have := (primeCubicMulChar_pow_eq_one P.p P.prime P.primary 1).mp (by rw [pow_one]; exact h)
  norm_num at this

theorem symbol_eq_chi (y : P.Res) : ringComplex (symbol (3 * P.lift y) P.p) = P.chi (3 * y) := by
  rw [← P.chi_res, map_mul, res_lift, res_three]

theorem sum_symbol_eq_zero : ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) = 0 := by
  simp_rw [P.symbol_eq_chi]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun y : P.Res => y ≠ 0)) (by simp) (fun y => P.chi (3 * y)),
    Finset.sum_filter_of_ne (fun y _ hy => by
      intro h0
      rw [h0, mul_zero, MulChar.map_zero] at hy
      exact hy rfl),
    (mulLeft_bijective₀ (3 : P.Res) P.three_ne_zero').sum_comp (fun u => P.chi u)]
  exact MulChar.sum_eq_zero_of_ne_one P.chi_ne_one

theorem norm_symbol_le (y : {y : P.Res // y ≠ 0}) : ‖ringComplex (symbol (3 * P.lift y.1) P.p)‖ ≤ 1 := by
  rw [P.symbol_eq_chi]
  have h := P.chi_cube _ (mul_ne_zero P.three_ne_zero' y.2)
  have h1 : ‖P.chi (3 * y.1)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (3 : ℕ) ≠ 0)).mp (by rw [← norm_pow, h, norm_one])
  rw [h1]

/-! ### The standard strip -/

theorem heckeHigh_point (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeHigh sourceTheta (upperPoint z v hv) =
      sourceTheta (upperPoint (ringComplex P.p * z) (‖ringComplex P.p‖ * v) (mul_pos P.norm_pos hv)) := by
  rw [heckeHigh, P.dilation_upperPoint]

theorem heckeLow_point (s : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeLow sourceTheta s (upperPoint z v hv) =
      sourceTheta (upperPoint ((z + 3 * ringComplex s) / ringComplex P.p) (v / ‖ringComplex P.p‖)
        (div_pos hv P.norm_pos)) := by
  rw [heckeLow, transThree_smul_upperPoint, P.contraction_upperPoint]

theorem one_le_norm : 1 ≤ ‖ringComplex P.p‖ := by
  have h := one_le_norm_sq_ringComplex P.ne_zero
  nlinarith [norm_nonneg (ringComplex P.p)]

/-- **`G'_p = O(v^{−7/3})` on the standard strip above any fixed height.** -/
theorem norm_remainder_strip (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.remainder (upperPoint z v hv)‖ ≤ K * v ^ (-(7 : ℝ) / 3) := by
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
  have hA : ‖sourceTheta (upperPoint (ringComplex P.p * z) (ρ * v) hvA) - PP‖ ≤ D := hcube _ _ hvA hle1
  have hB : ∀ s : O, ‖sourceTheta (upperPoint ((z + 3 * ringComplex s) / ringComplex P.p) (v / ρ) hvB) - Q‖ ≤ D :=
    fun s => hcube _ _ hvB le_rfl
  have h0 : ‖sourceTheta (upperPoint z v hv) - R‖ ≤ D := hcube _ _ hv (div_le_self hv.le hρ1)
  set θA := sourceTheta (upperPoint (ringComplex P.p * z) (ρ * v) hvA)
  set θB : O → ℂ := fun s => sourceTheta (upperPoint ((z + 3 * ringComplex s) / ringComplex P.p) (v / ρ) hvB)
  set θ0 := sourceTheta (upperPoint z v hv)
  set χ : {y : P.Res // y ≠ 0} → ℂ := fun y => ringComplex (symbol (3 * P.lift y.1) P.p)
  have htr : P.sourceHeckeTrace (upperPoint z v hv) =
      (∑ x : P.Res, θA * θB (P.lift x)) + ((∑ x : P.Res, θB (P.wShift + P.lift x) * θA) +
        ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * θB (P.lift x - P.lowBeta (P.lift y.1)) * θB (P.lift x)) := by
    rw [sourceHeckeTrace, P.heckeTrace_eq_hecke sourceTheta sourceTheta_automorphy]
    simp only [P.heckeHigh_point, P.heckeLow_point]
    rfl
  have hident : P.remainder (upperPoint z v hv) =
      (∑ x : P.Res, (θA * θB (P.lift x) - PP * Q)) + (∑ x : P.Res, (θB (P.wShift + P.lift x) * θA - Q * PP)) +
        (∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB (P.lift x - P.lowBeta (P.lift y.1)) * θB (P.lift x) -
          Q * Q)) - 2 * (Fintype.card P.Res : ℂ) * (θ0 * θ0 - R * R) := by
    have hχ : ∑ y : {y : P.Res // y ≠ 0}, χ y = 0 := P.sum_symbol_eq_zero
    have e3 : ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB (P.lift x - P.lowBeta (P.lift y.1)) *
        θB (P.lift x) - Q * Q) =
        ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * θB (P.lift x - P.lowBeta (P.lift y.1)) * θB (P.lift x) -
          ∑ _x : P.Res, Q * Q * ∑ y : {y : P.Res // y ≠ 0}, χ y := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [remainder, htr, Finset.sum_sub_distrib, Finset.sum_sub_distrib, e3, hχ]
    simp only [mul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_zero]
    linear_combination (2 * (Fintype.card P.Res : ℂ)) * hPQ
  set Eb := 2 * M * D + D ^ 2 with hEbdef
  have hEb : ∀ X Y PP' QQ : ℂ, ‖PP'‖ ≤ M → ‖QQ‖ ≤ M → ‖X - PP'‖ ≤ D → ‖Y - QQ‖ ≤ D →
      ‖X * Y - PP' * QQ‖ ≤ Eb := fun X Y PP' QQ h1 h2 h3 h4 => norm_mul_sub_mul_le h1 h2 h3 h4
  have hEb0 : 0 ≤ Eb := (norm_nonneg _).trans (hEb _ _ _ _ hPM hQM hA (hB 0))
  have hcardS : (Fintype.card {y : P.Res // y ≠ 0} : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_subtype_le _
  have hs1 : ‖∑ x : P.Res, (θA * θB (P.lift x) - PP * Q)‖ ≤ N * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖θA * θB (P.lift x) - PP * Q‖ ≤ ∑ _x : P.Res, Eb :=
          Finset.sum_le_sum fun x _ => hEb _ _ _ _ hPM hQM hA (hB _)
      _ = N * Eb := by simp [hNdef]
  have hs2 : ‖∑ x : P.Res, (θB (P.wShift + P.lift x) * θA - Q * PP)‖ ≤ N * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖θB (P.wShift + P.lift x) * θA - Q * PP‖ ≤ ∑ _x : P.Res, Eb :=
          Finset.sum_le_sum fun x _ => hEb _ _ _ _ hQM hPM (hB _) hA
      _ = N * Eb := by simp [hNdef]
  have hs3 : ‖∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB (P.lift x - P.lowBeta (P.lift y.1)) *
      θB (P.lift x) - Q * Q)‖ ≤ N * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖∑ y : {y : P.Res // y ≠ 0}, χ y * (θB (P.lift x - P.lowBeta (P.lift y.1)) *
          θB (P.lift x) - Q * Q)‖ ≤ ∑ _x : P.Res, N * Eb := by
          refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
          calc ∑ y : {y : P.Res // y ≠ 0}, ‖χ y * (θB (P.lift x - P.lowBeta (P.lift y.1)) * θB (P.lift x) - Q * Q)‖
              ≤ ∑ _y : {y : P.Res // y ≠ 0}, Eb := Finset.sum_le_sum fun y _ => by
                rw [norm_mul]
                exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_symbol_le y)).trans
                  (hEb _ _ _ _ hQM hQM (hB _) (hB _))
            _ = (Fintype.card {y : P.Res // y ≠ 0} : ℝ) * Eb := by simp
            _ ≤ N * Eb := mul_le_mul_of_nonneg_right hcardS hEb0
      _ = N * (N * Eb) := by simp [hNdef]
  have hs4 : ‖2 * (Fintype.card P.Res : ℂ) * (θ0 * θ0 - R * R)‖ ≤ 2 * N * Eb := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (hEb _ _ _ _ hRM hRM h0 h0) (by positivity)
  have htotal : ‖P.remainder (upperPoint z v hv)‖ ≤ N * (N + 4) * Eb := by
    rw [hident]
    calc _ ≤ ‖(∑ x : P.Res, (θA * θB (P.lift x) - PP * Q)) + (∑ x : P.Res, (θB (P.wShift + P.lift x) * θA - Q * PP)) +
            (∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, χ y * (θB (P.lift x - P.lowBeta (P.lift y.1)) * θB (P.lift x) -
              Q * Q))‖ + ‖2 * (Fintype.card P.Res : ℂ) * (θ0 * θ0 - R * R)‖ := norm_sub_le _ _
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
    ring
  rw [hEbv, hv3]
  have h6 := mul_le_mul_of_nonneg_left hv6 (by positivity : (0 : ℝ) ≤ (C₁ * ρ ^ 3) ^ 2)
  have hNN : 0 ≤ N * (N + 4) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 hNN, norm_nonneg c, Real.rpow_nonneg hv.le (-(7 : ℝ) / 3),
    Real.rpow_nonneg hn.le ((2 : ℝ) / 3)]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
