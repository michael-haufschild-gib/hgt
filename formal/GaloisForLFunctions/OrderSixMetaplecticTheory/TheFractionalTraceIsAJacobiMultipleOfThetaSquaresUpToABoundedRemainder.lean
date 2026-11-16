import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalPointsOfARamifiedCuspAreRamified

/-!
# The fractional trace is a Jacobi multiple of θ² up to a bounded remainder

For an odd primary prime q, the remainder

R_q = Tr G − (N² + N + (N − 1)J) θ_s²   (`PrimaryPrime.fracRemainder`),

J = Σ_s χ(1 − s²) the Jacobi sum of the cubic and the quadratic character of O/q, is a bounded function on ℍ³ of
multiplier κ⁻¹ with R_q = O(v^{−7/3}) above any height (`fracRemainder_remainderData`):

* in the standard strip every fractional point has height v, N(q)v or v/N(q), where θ_s = cv^{2/3} + O(v^{−3});
  the constant parts sum to (N + (N − 1)J + N²)(cv^{2/3})²: the middle cusps give the Jacobi count
  Σ_{x ≢ 0} Σ_t χ(1 − (9tx)²) = (N − 1)J, while the high pairs (phases χ(2)χ(3x)⁻¹) and the low pairs (phases
  χ(−9x²)) cancel;
* at the ramified cusps every fractional point is ramified (`norm_sourceFracTrace_ramified`);
* the trace and θ_s² are invariant under SL₂(ℤ), which moves every point to the strip or a ramified cusp.

The main coefficient N² + N + (N − 1)J is complex: the order-six arithmetic of q enters the main term of the
fractional trace through a cubic–quadratic Jacobi sum.
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

/-- The main coefficient N² + N + (N − 1)J. -/
def fracMain : ℂ := P.normC ^ 2 + P.normC + (P.normC - 1) * P.fracJacobi

/-- R_q = Tr G − (N² + N + (N − 1)J)θ_s². -/
def fracRemainder (w : HyperbolicSpace) : ℂ := P.sourceFracTrace w - P.fracMain * sourceTheta w ^ 2

theorem sourceFracTrace_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.sourceFracTrace (complexMatrix M • w) = complexCharacter M ^ 2 * P.sourceFracTrace w :=
  P.fracTrace_automorphy sourceTheta sourceTheta_automorphy M w

theorem sourceFracTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    P.sourceFracTrace (integralComplexMatrix (rationalEmbedding r) • w) = P.sourceFracTrace w :=
  P.fracTrace_rational sourceTheta sourceTheta_automorphy sourceTheta_rational_inv r w

theorem fracRemainder_rationalExtension (G : rationalExtension) (w : HyperbolicSpace) :
    P.fracRemainder (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G ^ 2 * P.fracRemainder w := by
  obtain ⟨n, r, hG⟩ := G.2
  have hρ : extendedComplexCharacter G = complexCharacter n := rationalExtensionValue_of_product G n r hG
  have hw : integralComplexMatrix (G : SL(2, O)) • w =
      complexMatrix n • (integralComplexMatrix (rationalEmbedding r) • w) := by
    rw [← hG, map_mul, mul_smul]
    rfl
  have hθ := cubicSourceResidualFunction_automorphy G w
  unfold fracRemainder
  rw [show sourceTheta (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G * sourceTheta w from hθ,
    hw, P.sourceFracTrace_automorphy, P.sourceFracTrace_rational, hρ]
  ring

theorem norm_fracRemainder_rational (G : rationalExtension) (w : HyperbolicSpace) :
    ‖P.fracRemainder (integralComplexMatrix (G : SL(2, O)) • w)‖ = ‖P.fracRemainder w‖ := by
  rw [P.fracRemainder_rationalExtension, norm_mul, norm_pow, norm_extendedComplexCharacter, one_pow, one_mul]

/-! ### The main terms -/

/-- The main part of a pair over a middle cusp. -/
def middleMain (x : {x : P.Res // x ≠ 0}) (t : P.Res) (A B : ℂ) : ℂ :=
  if 1 + 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A
  else if 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A
  else P.chi (1 - (9 * t * x.1) ^ 2) * B

/-- **The middle-cusp main terms.** The high pairs cancel and the Jacobi count is (N − 1)J. -/
theorem sum_middleMain (A B : ℂ) :
    ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.middleMain x t A B = (P.normC - 1) * P.fracJacobi * B := by
  have h9 := P.nine_ne_zero'
  have hsplit : ∀ x : {x : P.Res // x ≠ 0}, ∀ t : P.Res, P.middleMain x t A B =
      (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A else 0) +
        P.chi (1 - (9 * t * x.1) ^ 2) * B := by
    intro x t
    unfold middleMain
    by_cases h₁ : 1 + 9 * t * x.1 = 0
    · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 - 9 * t * x.1) * h₁
      rw [if_pos h₁, if_pos (Or.inl h₁), hsq, MulChar.map_zero, zero_mul, add_zero]
    · by_cases h₂ : 1 - 9 * t * x.1 = 0
      · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 + 9 * t * x.1) * h₂
        rw [if_neg h₁, if_pos h₂, if_pos (Or.inr h₂), hsq, MulChar.map_zero, zero_mul, add_zero]
      · rw [if_neg h₁, if_neg h₂, if_neg (not_or.mpr ⟨h₁, h₂⟩), zero_add]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hhigh : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res,
      (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A else 0) = 0 := by
    set c0 : ℂ := ∑ s : P.Res, if 1 + s = 0 ∨ 1 - s = 0 then (1 : ℂ) else 0
    have hK : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res,
        (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A else 0) =
        P.chi 2 * A * c0 * (P.chi (3 * x.1))⁻¹ := by
      intro x
      have hbij := (mulRight_bijective₀ (9 * x.1) (mul_ne_zero h9 x.2)).sum_comp
        (fun s => if 1 + s = 0 ∨ 1 - s = 0 then (1 : ℂ) else 0)
      rw [show P.chi 2 * A * c0 * (P.chi (3 * x.1))⁻¹ = P.chi 2 * (P.chi (3 * x.1))⁻¹ * A * c0 by ring,
        show c0 = ∑ i : P.Res, (if 1 + i * (9 * x.1) = 0 ∨ 1 - i * (9 * x.1) = 0 then (1 : ℂ) else 0) from hbij.symm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [show t * (9 * x.1) = 9 * t * x.1 by ring]
      split_ifs <;> ring
    simp_rw [hK]
    rw [← Finset.mul_sum, P.sum_chi_three_inv, mul_zero]
  rw [hhigh, zero_add]
  simp_rw [← Finset.sum_mul]
  rw [P.jacobi_double_count]

end PrimaryPrime

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem norm_chi_eq_one (u : P.Res) (hu : u ≠ 0) : ‖P.chi u‖ = 1 := by
  have h3 : ‖P.chi u‖ ^ 3 = 1 := by rw [← norm_pow, P.chi_cube u hu, norm_one]
  have h0 : 0 ≤ ‖P.chi u‖ := norm_nonneg _
  have := (pow_eq_one_iff_of_nonneg h0 (by norm_num : (3 : ℕ) ≠ 0)).mp h3
  exact this

theorem norm_highPhase_le (x : {x : P.Res // x ≠ 0}) : ‖P.chi 2 * (P.chi (3 * x.1))⁻¹‖ ≤ 1 := by
  rw [norm_mul, norm_inv, P.norm_chi_eq_one _ (mul_ne_zero P.three_ne_zero' x.2), inv_one, mul_one]
  exact P.norm_chi_le _

/-! ### The standard strip -/

/-- **R_q = O(v^{−7/3}) on the standard strip above any fixed height.** -/
theorem norm_fracRemainder_strip (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.fracRemainder (upperPoint z v hv)‖ ≤ K * v ^ (-(7 : ℝ) / 3) := by
  have hn := P.norm_pos
  have hρ1 := P.one_le_norm
  set ρ := ‖ringComplex P.p‖ with hρdef
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height (a / ρ / ρ) (div_pos (div_pos ha hn) hn)
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue with hcdef
  set N : ℝ := (Fintype.card P.Res : ℝ) with hNdef
  have hN0 : 0 ≤ N := by positivity
  set K0 : ℝ := N + N * N + N ^ 2 + N ^ 2 * N with hK0
  refine ⟨K0 * (2 * ‖c‖ * ρ ^ ((4 : ℝ) / 3) * (C₁ * ρ ^ 6) + (C₁ * ρ ^ 6) ^ 2 * a ^ (-(11 : ℝ) / 3)),
    by positivity, fun z v hv hav => ?_⟩
  have hlo : 0 < v / ρ / ρ := div_pos (div_pos hv hn) hn
  have hhi : 0 < ρ * (ρ * v) := mul_pos hn (mul_pos hn hv)
  have hlov : v / ρ / ρ ≤ v := le_trans (div_le_self (div_pos hv hn).le hρ1) (div_le_self hv.le hρ1)
  set R0 : ℂ := c * (v : ℂ) ^ (2 / 3 : ℂ) with hR0def
  set Rhi : ℂ := c * ((ρ * (ρ * v) : ℝ) : ℂ) ^ (2 / 3 : ℂ) with hRhidef
  set Rlo : ℂ := c * ((v / ρ / ρ : ℝ) : ℂ) ^ (2 / 3 : ℂ) with hRlodef
  set M : ℝ := ‖c‖ * ρ ^ ((4 : ℝ) / 3) * v ^ ((2 : ℝ) / 3) with hMdef
  set D : ℝ := C₁ * ρ ^ 6 / v ^ 3 with hDdef
  have hρ43 : 1 ≤ ρ ^ ((4 : ℝ) / 3) := Real.one_le_rpow hρ1 (by norm_num)
  have hv23 : 0 ≤ v ^ ((2 : ℝ) / 3) := by positivity
  have hcv : ‖c‖ * v ^ ((2 : ℝ) / 3) ≤ M := by
    rw [hMdef]
    have := mul_le_mul_of_nonneg_left hρ43 (mul_nonneg (norm_nonneg c) hv23)
    nlinarith
  have hR0M : ‖R0‖ ≤ M := by
    rw [hR0def, norm_mul, norm_cpow_two_thirds hv]
    exact hcv
  have hRhiM : ‖Rhi‖ ≤ M := by
    have e : (ρ * (ρ * v)) ^ ((2 : ℝ) / 3) = ρ ^ ((4 : ℝ) / 3) * v ^ ((2 : ℝ) / 3) := by
      rw [← mul_assoc, Real.mul_rpow (by positivity) hv.le, show ρ * ρ = ρ ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
        ← Real.rpow_mul hn.le]
      norm_num
    rw [hRhidef, norm_mul, norm_cpow_two_thirds hhi, e, hMdef]
    ring_nf
    exact le_rfl
  have hRloM : ‖Rlo‖ ≤ M := by
    rw [hRlodef, norm_mul, norm_cpow_two_thirds hlo]
    refine le_trans ?_ hcv
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlo.le hlov (by norm_num)) (norm_nonneg _)
  have hcube : ∀ (ζ : ℂ) (h : ℝ) (hh : 0 < h), v / ρ / ρ ≤ h →
      ‖sourceTheta (upperPoint ζ h hh) - c * (h : ℂ) ^ (2 / 3 : ℂ)‖ ≤ D := by
    intro ζ h hh hle
    have hd := hdec h hh (le_trans (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hav hn.le) hn.le) hle) ζ
    refine hd.trans ?_
    rw [hDdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (v / ρ / ρ) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hlo.le hle 3
    have e : (v / ρ / ρ) ^ 3 * ρ ^ 6 = v ^ 3 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ C₁ * ρ ^ 6)]
  set Eb : ℝ := 2 * M * D + D ^ 2 with hEbdef
  have hEb : ∀ X Y PP QQ : ℂ, ‖PP‖ ≤ M → ‖QQ‖ ≤ M → ‖X - PP‖ ≤ D → ‖Y - QQ‖ ≤ D →
      ‖X * Y - PP * QQ‖ ≤ Eb := fun X Y PP QQ h1 h2 h3 h4 => norm_mul_sub_mul_le h1 h2 h3 h4
  -- the theta values at the fractional points
  set θfr : O → ℂ := fun u => sourceTheta (P.fracShift u • upperPoint z v hv) with hθfr
  set θhi : ℂ := sourceTheta (P.dilation • P.dilation • upperPoint z v hv) with hθhi
  set θ0 : ℂ := sourceTheta (upperPoint z v hv) with hθ0
  set θlo : O → P.Res × P.Res → ℂ := fun r s =>
    P.heckeLow sourceTheta r (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) with hθlo
  have bfr : ∀ u, ‖θfr u - R0‖ ≤ D := by
    intro u
    simp only [hθfr, fracShift, complexTranslation_action]
    exact hcube _ v hv hlov
  have bhi : ‖θhi - Rhi‖ ≤ D := by
    simp only [hθhi, P.dilation_upperPoint]
    exact hcube _ _ hhi (le_trans hlov (le_trans (le_mul_of_one_le_left hv.le hρ1)
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hv.le hρ1) hn.le)))
  have b0 : ‖θ0 - R0‖ ≤ D := hcube _ v hv hlov
  have blo : ∀ r s, ‖θlo r s - Rlo‖ ≤ D := by
    intro r s
    simp only [hθlo, transThree_smul_upperPoint, P.contraction_upperPoint, P.heckeLow_point]
    exact hcube _ _ _ le_rfl
  have hEb0 : 0 ≤ Eb := (norm_nonneg _).trans (hEb _ _ _ _ hR0M hR0M b0 b0)
  -- the decomposition
  set FC : {x : P.Res // x ≠ 0} → P.Res → ℂ := fun x t =>
    P.fracCorrelation sourceTheta (P.lift t) (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) with hFC
  have hTr : P.sourceFracTrace (upperPoint z v hv) = ∑ x : P.Res, θfr (P.lift x) * θfr (-P.lift x) +
      (∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, FC x t + (P.normC ^ 2 * θ0 ^ 2 +
        ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s))) := by
    rw [sourceFracTrace, P.fracTrace_eq sourceTheta sourceTheta_automorphy sourceTheta_rational_inv,
      P.sum_fracSum_cuspZero sourceTheta sourceTheta_automorphy sourceTheta_rational_inv]
    rfl
  have e1 : ∑ x : P.Res, (θfr (P.lift x) * θfr (-P.lift x) - R0 * R0) =
      ∑ x : P.Res, θfr (P.lift x) * θfr (-P.lift x) - P.normC * (R0 * R0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e2 : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (FC x t - P.middleMain x t (Rhi * R0) (R0 * R0)) =
      ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, FC x t - (P.normC - 1) * P.fracJacobi * (R0 * R0) := by
    simp_rw [Finset.sum_sub_distrib]
    rw [P.sum_middleMain]
  have e4 : ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
      (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s - Rlo * Rlo) =
      ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
        (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, P.sum_chi_low, zero_mul, sub_zero]
  have hident : P.fracRemainder (upperPoint z v hv) =
      ∑ x : P.Res, (θfr (P.lift x) * θfr (-P.lift x) - R0 * R0) +
        ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (FC x t - P.middleMain x t (Rhi * R0) (R0 * R0)) +
          P.normC ^ 2 * (θ0 * θ0 - R0 * R0) +
            ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
              (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s - Rlo * Rlo) := by
    rw [e1, e2, e4, fracRemainder, hTr, fracMain]
    ring
  -- the bounds
  have hcard : (Fintype.card {x : P.Res // x ≠ 0} : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_subtype_le _
  have hs1 : ‖∑ x : P.Res, (θfr (P.lift x) * θfr (-P.lift x) - R0 * R0)‖ ≤ N * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖θfr (P.lift x) * θfr (-P.lift x) - R0 * R0‖ ≤ ∑ _x : P.Res, Eb :=
          Finset.sum_le_sum fun x _ => hEb _ _ _ _ hR0M hR0M (bfr _) (bfr _)
      _ = N * Eb := by simp [hNdef]
  have hterm : ∀ x t, ‖FC x t - P.middleMain x t (Rhi * R0) (R0 * R0)‖ ≤ Eb := by
    intro x t
    simp only [hFC]
    rw [P.fracCorrelation_lowerThree sourceTheta sourceTheta_automorphy h2 x t, middleMain]
    split_ifs
    · rw [← mul_sub]
      refine (norm_mul_le _ _).trans ?_
      exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_highPhase_le x)).trans
        (hEb _ _ _ _ hRhiM hR0M bhi (bfr _))
    · rw [← mul_sub]
      refine (norm_mul_le _ _).trans ?_
      exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_highPhase_le x)).trans
        (hEb _ _ _ _ hRhiM hR0M bhi (bfr _))
    · rw [← mul_sub]
      refine (norm_mul_le _ _).trans ?_
      exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_le _)).trans
        (hEb _ _ _ _ hR0M hR0M (bfr _) (bfr _))
  have hs2 : ‖∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (FC x t - P.middleMain x t (Rhi * R0) (R0 * R0))‖ ≤
      N * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : {x : P.Res // x ≠ 0}, ‖∑ t : P.Res, (FC x t - P.middleMain x t (Rhi * R0) (R0 * R0))‖ ≤
          ∑ _x : {x : P.Res // x ≠ 0}, N * Eb := by
          refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
          calc ∑ t : P.Res, ‖FC x t - P.middleMain x t (Rhi * R0) (R0 * R0)‖ ≤ ∑ _t : P.Res, Eb :=
                Finset.sum_le_sum fun t _ => hterm x t
            _ = N * Eb := by simp [hNdef]
      _ = (Fintype.card {x : P.Res // x ≠ 0} : ℝ) * (N * Eb) := by simp
      _ ≤ N * (N * Eb) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hs3 : ‖P.normC ^ 2 * (θ0 * θ0 - R0 * R0)‖ ≤ N ^ 2 * Eb := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hEb _ _ _ _ hR0M hR0M b0 b0) (by positivity)
  have hs4 : ‖∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
      (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s - Rlo * Rlo)‖ ≤ N ^ 2 * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ s : P.Res × P.Res, ‖∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s - Rlo * Rlo)‖ ≤
          ∑ _s : P.Res × P.Res, N * Eb := by
          refine Finset.sum_le_sum fun s _ => (norm_sum_le _ _).trans ?_
          calc ∑ x : {x : P.Res // x ≠ 0}, ‖P.chi (-9 * x.1 ^ 2) *
                (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s - Rlo * Rlo)‖ ≤
                ∑ _x : {x : P.Res // x ≠ 0}, Eb := by
                refine Finset.sum_le_sum fun x _ => (norm_mul_le _ _).trans ?_
                exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_le _)).trans
                  (hEb _ _ _ _ hRloM hRloM (blo _ _) (blo _ _))
            _ = (Fintype.card {x : P.Res // x ≠ 0} : ℝ) * Eb := by simp
            _ ≤ N * Eb := mul_le_mul_of_nonneg_right hcard hEb0
      _ = N ^ 2 * (N * Eb) := by simp [hNdef, Fintype.card_prod]; ring
  have htotal : ‖P.fracRemainder (upperPoint z v hv)‖ ≤ K0 * Eb := by
    rw [hident]
    calc _ ≤ ‖∑ x : P.Res, (θfr (P.lift x) * θfr (-P.lift x) - R0 * R0)‖ +
          ‖∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (FC x t - P.middleMain x t (Rhi * R0) (R0 * R0))‖ +
          ‖P.normC ^ 2 * (θ0 * θ0 - R0 * R0)‖ +
          ‖∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
              (θlo (-P.lowBeta (-P.lift x.1)) s * θlo (-P.lowBeta (P.lift x.1)) s - Rlo * Rlo)‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ N * Eb + N * (N * Eb) + N ^ 2 * Eb + N ^ 2 * (N * Eb) := by gcongr
      _ = K0 * Eb := by rw [hK0]; ring
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
  have hEbv : Eb = 2 * ‖c‖ * ρ ^ ((4 : ℝ) / 3) * (C₁ * ρ ^ 6) * (v ^ ((2 : ℝ) / 3) / v ^ 3) +
      (C₁ * ρ ^ 6) ^ 2 * (1 / v ^ 6) := by
    rw [hEbdef, hMdef, hDdef]
    field_simp
  rw [hEbv, hv3]
  have h6 := mul_le_mul_of_nonneg_left hv6 (by positivity : (0 : ℝ) ≤ (C₁ * ρ ^ 6) ^ 2)
  have hK00 : 0 ≤ K0 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 hK00, norm_nonneg c, Real.rpow_nonneg hv.le (-(7 : ℝ) / 3),
    Real.rpow_nonneg hn.le ((4 : ℝ) / 3)]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
