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
  rw [hEbv, hv3]
  have h6 := mul_le_mul_of_nonneg_left hv6 (by positivity : (0 : ℝ) ≤ (C₁ * ρ ^ 3) ^ 2)
  have hNN : 0 ≤ N * (N + 4) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 hNN, norm_nonneg c, Real.rpow_nonneg hv.le (-(7 : ℝ) / 3),
    Real.rpow_nonneg hn.le ((2 : ℝ) / 3)]

end PrimaryPrime


namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The ramified cusps -/

/-- **`G'_p` is bounded at the ramified cusps.** -/
theorem norm_remainder_ramified (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Fin 3), j ≠ 0 → ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.remainder (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ K := by
  have hn := P.norm_pos
  obtain ⟨C, β, hC, hβ, hhecke⟩ := P.sourceTheta_hecke_ramified a ha
  obtain ⟨C', β', hC', hβ', hram⟩ := sourceTheta_ramified_decay a ha
  set N : ℝ := (Fintype.card P.Res : ℝ) with hNdef
  have hN0 : 0 ≤ N := by positivity
  refine ⟨N * (N + 2) * C ^ 2 + 2 * N * C' ^ 2, by positivity, fun j hj z v hv hav => ?_⟩
  set x := upperPoint z v hv
  set w := integralComplexMatrix (cuspRepresentative j) • x
  have hβp : 0 < β / ‖ringComplex P.p‖ := div_pos hβ hn
  have he : Real.exp (-(β / ‖ringComplex P.p‖) * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he' : Real.exp (-β' * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hH : ‖P.heckeHigh sourceTheta w‖ ≤ C := by
    rw [heckeHigh]
    refine ((hhecke _ (colRes_cuspRepresentative j hj) z v hv hav).1).trans ?_
    nlinarith
  have hL : ∀ s : O, ‖P.heckeLow sourceTheta s w‖ ≤ C := by
    intro s
    have hw : complexMatrix (transThree s) • w =
        integralComplexMatrix ((transThree s : SL(2, O)) * cuspRepresentative j) • x := by
      rw [map_mul, mul_smul]
      rfl
    rw [heckeLow, hw]
    refine ((hhecke _ (colRes_trans_cuspRepresentative s j hj) z v hv hav).2).trans ?_
    nlinarith
  have hθ : ‖sourceTheta w‖ ≤ C' := by
    refine (hram _ (colRes_cuspRepresentative j hj) z v hv hav).trans ?_
    nlinarith
  have hprod : ∀ X Y : ℂ, ‖X‖ ≤ C → ‖Y‖ ≤ C → ‖X * Y‖ ≤ C ^ 2 := fun X Y hX hY => by
    rw [norm_mul, sq]
    exact mul_le_mul hX hY (norm_nonneg _) hC
  have hcardS : (Fintype.card {y : P.Res // y ≠ 0} : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_subtype_le _
  have htr : ‖P.sourceHeckeTrace w‖ ≤ N * (N + 2) * C ^ 2 := by
    rw [sourceHeckeTrace, P.heckeTrace_eq_hecke sourceTheta sourceTheta_automorphy]
    have h1 : ‖∑ x : P.Res, P.heckeHigh sourceTheta w * P.heckeLow sourceTheta (P.lift x) w‖ ≤ N * C ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _x : P.Res, C ^ 2 := Finset.sum_le_sum fun x _ => hprod _ _ hH (hL _)
        _ = N * C ^ 2 := by simp [hNdef]
    have h2 : ‖∑ x : P.Res, P.heckeLow sourceTheta (P.wShift + P.lift x) w * P.heckeHigh sourceTheta w‖ ≤
        N * C ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _x : P.Res, C ^ 2 := Finset.sum_le_sum fun x _ => hprod _ _ (hL _) hH
        _ = N * C ^ 2 := by simp [hNdef]
    have h3 : ‖∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
        P.heckeLow sourceTheta (P.lift x - P.lowBeta (P.lift y.1)) w * P.heckeLow sourceTheta (P.lift x) w‖ ≤
        N * (N * C ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _x : P.Res, N * C ^ 2 := by
            refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
            calc _ ≤ ∑ _y : {y : P.Res // y ≠ 0}, C ^ 2 := Finset.sum_le_sum fun y _ => by
                  rw [mul_assoc, norm_mul]
                  exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_symbol_le y)).trans (hprod _ _ (hL _) (hL _))
              _ = (Fintype.card {y : P.Res // y ≠ 0} : ℝ) * C ^ 2 := by simp
              _ ≤ N * C ^ 2 := mul_le_mul_of_nonneg_right hcardS (by positivity)
        _ = N * (N * C ^ 2) := by simp [hNdef]
    calc _ ≤ ‖∑ x : P.Res, P.heckeHigh sourceTheta w * P.heckeLow sourceTheta (P.lift x) w‖ +
          (‖∑ x : P.Res, P.heckeLow sourceTheta (P.wShift + P.lift x) w * P.heckeHigh sourceTheta w‖ +
            ‖∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
              P.heckeLow sourceTheta (P.lift x - P.lowBeta (P.lift y.1)) w * P.heckeLow sourceTheta (P.lift x) w‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ N * C ^ 2 + (N * C ^ 2 + N * (N * C ^ 2)) := by gcongr
      _ = N * (N + 2) * C ^ 2 := by ring
  rw [remainder]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hθ2 : ‖sourceTheta w‖ ^ 2 ≤ C' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hθ 2
  have := mul_le_mul_of_nonneg_left hθ2 (by positivity : (0 : ℝ) ≤ 2 * N)
  linarith

/-! ### Boundedness and square integrability -/

/-- **`G'_p = Tr_pθ_s − 2N(p)θ_s²` is bounded on hyperbolic three-space.** -/
theorem remainder_bounded : ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖P.remainder w‖ ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨K₀, hK₀, hstrip⟩ := P.norm_remainder_strip a₀ ha₀
  obtain ⟨K₁, hK₁, hram⟩ := P.norm_remainder_ramified a₀ ha₀
  refine ⟨K₀ * a₀ ^ (-(7 : ℝ) / 3) + K₁, fun w => ?_⟩
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨G', j, T, hT, -, hu1, hdec'⟩ := three_cusp_decomposition M⁻¹
  have hw : w = integralComplexMatrix (G' : SL(2, O)) •
      (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) := by
    rw [← mul_smul, ← map_mul, ← mul_assoc, ← hdec', ← hMw, ← mul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]
  rw [hw, P.norm_remainder_rational]
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  rw [map_mul, mul_smul, ← hp]
  by_cases hj : j = 0
  · subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    rw [hc1, map_one, one_smul]
    refine (hstrip z' v' hv' hfloor).trans ?_
    have : v' ^ (-(7 : ℝ) / 3) ≤ a₀ ^ (-(7 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos ha₀ hfloor (by norm_num)
    nlinarith
  · exact (hram j hj z' v' hv' hfloor).trans (by nlinarith [Real.rpow_nonneg ha₀.le (-(7 : ℝ) / 3)])

theorem sourceHeckeTrace_continuous : Continuous P.sourceHeckeTrace := by
  have h : P.sourceHeckeTrace = fun w => ∑ i : P.Index,
      (complexCharacter (P.rep i) ^ 2)⁻¹ * P.heckeCorrelation sourceTheta (complexMatrix (P.rep i) • w) :=
    funext (P.heckeTrace_eq_sum sourceTheta sourceTheta_automorphy)
  rw [h]
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  unfold heckeCorrelation
  exact (cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _))).mul
    (cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _)))

theorem remainder_continuous : Continuous P.remainder :=
  P.sourceHeckeTrace_continuous.sub (continuous_const.mul (cubicSourceResidualFunction_continuous.pow 2))

theorem remainder_memLp : MemLp P.remainder 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := P.remainder_bounded
  exact MemLp.of_bound P.remainder_continuous.measurable.aestronglyMeasurable B (Eventually.of_forall hB)

theorem remainder_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.remainder (complexMatrix M • w) = (complexCharacter M)⁻¹ * P.remainder w := by
  rw [remainder, remainder, P.sourceHeckeTrace_automorphy, sourceTheta_automorphy, ← complexCharacter_sq_eq_inv]
  ring

/-- **`G'_p` is a bounded remainder.** -/
theorem remainder_remainderData : RemainderData P.remainder where
  automorphy := P.remainder_automorphy
  measurable := P.remainder_continuous.measurable
  bounded := P.remainder_bounded
  high := P.norm_remainder_strip 2 two_pos
  memLp := P.remainder_memLp

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
