import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheColumnsOfTheChainInMellinCoordinates
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticWeightedZeta

/-!
# The chain is Hilbert–Schmidt above half damping

For every `½ < η < 1` the centred damping chain `C_η` is Hilbert–Schmidt in the receiver norm:
`Σ_{k,n} C_η(n,k)² < ∞` (`sum_sum_sq_centeredRow_le_halfDamping`), hence bounded on `ℓ²`
(`centeredOperator_l2_le_of_halfDamping`).  This replaces the floor-jump thresholds `1/√2` and
`(√5 − 1)/2`, which were sharp for pointwise majorants of the kernel, by the sign-blind threshold
`½` of the residue modes.

The proof reads every column in Mellin coordinates (`TheColumnsOfTheChainInMellinCoordinates`):
* column `k` costs at most `8K² ∫_0^∞ Δ_K(x)² x^{−2} dx + 4K^{−2η}`, `K = k + 1`;
* on `Re s = −½`, `M Δ_K(s) = (K^{s−η} − (K+1)^{s−η}) M P(s)` and
  `|M P(s)| ≤ ζ(η + ½) |ζ(½ − it)| / |s|`;
* the dilation symbol obeys `|K^z − (K+1)^z| ≤ 2K^{Re z} (|z|/2K)^θ` (`norm_cpow_sub_cpow_le`);
  with `θ = ¾ − η/2` the column energy is `≲ K^{−½−η} ∫ |ζ(½+it)|² (2+|t|)^{−½−η} dt`;
* the last integral is finite by the dyadic critical-line mean square
  (`integrable_normSq_zeta_criticalLine_mul_weight`), since `½ + η > 1`.

Arithmetic input: `|μ| ≤ 1` and `∫_T^{2T} |ζ(½+it)|² dt ≪ T log³ T`.  The Möbius signs are not
used, so the threshold `½` is the sign-blind one; below it the eigenvalues `d^{−η}` of the residue
modes are not square summable.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The critical-line weight -/

/-- **Weighted critical mean square**: `|ζ(½+it)|² (2+|t|)^{−1−δ}` is integrable for `δ > 0`. -/
theorem integrable_normSq_zeta_criticalLine_mul_weight {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ =>
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (2 + |t|) ^ (-1 - δ)) := by
  obtain ⟨C, hC, hmoment⟩ := RHTower.exists_integral_normSq_zeta_vertical_le
  have hc : ContinuousOn (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (Ici 2) :=
    (RHTower.WeilSingularArithmetic.continuousOn_norm_zeta_positive_line (1 / 2)).pow 2
  have hpos0 : IntegrableOn (fun t : ℝ =>
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * t ^ (-1 - δ)) (Ici 2) :=
    RHTower.WeilSingularArithmetic.integrableOn_mul_rpow_of_dyadic_logCube hc
      (fun _ => by positivity) hC.le hδ (fun T hT => hmoment T hT (1 / 2) le_rfl (by norm_num))
  let F : ℝ → ℝ := fun t =>
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (2 + |t|) ^ (-1 - δ)
  have hF : Continuous F :=
    ((RHTower.WeilSingularArithmetic.continuous_norm_zeta_line (σ := 1 / 2)
      (by norm_num)).pow 2).mul
      ((continuous_const.add continuous_abs).rpow_const fun t => Or.inl (by
        change (2 : ℝ) + |t| ≠ 0
        positivity))
  have hF0 : ∀ t : ℝ, 0 ≤ F t := fun t => by dsimp [F]; positivity
  have hpos : IntegrableOn F (Ici 2) := by
    refine hpos0.mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 t)]
    dsimp [F]
    rw [abs_of_nonneg (by linarith : 0 ≤ t)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)) (by positivity)
  have heven : ∀ t : ℝ, F (-t) = F t := by
    intro t
    have hconj : ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I =
        (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    dsimp [F]
    rw [hconj, riemannZeta_conj, Complex.norm_conj, abs_neg]
  have hneg : IntegrableOn F (Iic (-2)) := by
    have h := IntegrableOn.comp_neg_Iic (c := (-2 : ℝ)) (by simpa using hpos)
    exact h.congr_fun (fun t _ => heven t) measurableSet_Iic
  have hcenter : IntegrableOn F (Icc (-2) 2) := hF.continuousOn.integrableOn_Icc
  apply integrableOn_univ.mp
  apply ((hneg.union hcenter).union hpos).mono_set
  intro t _
  by_cases hleft : t ≤ -2
  · exact Or.inl (Or.inl hleft)
  by_cases hright : 2 ≤ t
  · exact Or.inr hright
  exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)

/-- The weighted critical mass `J_η = ∫ |ζ(½+it)|² (2+|t|)^{−½−η} dt`. -/
def criticalWeightMass (η : ℝ) : ℝ :=
  ∫ t : ℝ, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (2 + |t|) ^ (-1 / 2 - η)

theorem integrable_criticalWeight {η : ℝ} (h0 : 1 / 2 < η) :
    Integrable (fun t : ℝ =>
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (2 + |t|) ^ (-1 / 2 - η)) := by
  have h := integrable_normSq_zeta_criticalLine_mul_weight (δ := η - 1 / 2) (by linarith)
  rwa [show (-1 : ℝ) - (η - 1 / 2) = -1 / 2 - η by ring] at h

theorem criticalWeightMass_nonneg (η : ℝ) : 0 ≤ criticalWeightMass η :=
  integral_nonneg fun t => by positivity

/-! ### The dilation symbol -/

/-- **The dilation symbol**: for `K ≥ 1`, `Re z < 0`, `0 ≤ θ ≤ 1`,
`|K^z − (K+1)^z| ≤ 2K^{Re z} (|z|/(2K))^θ` — the minimum of the size bound `2K^{Re z}` and the
mean-value bound `|z| K^{Re z − 1}`. -/
theorem norm_cpow_sub_cpow_le {K : ℝ} (hK : 1 ≤ K) {z : ℂ} (hz : z.re < 0) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖(K : ℂ) ^ z - ((K + 1 : ℝ) : ℂ) ^ z‖ ≤ 2 * K ^ z.re * (‖z‖ / (2 * K)) ^ θ := by
  have hK0 : 0 < K := by linarith
  have hK10 : (0 : ℝ) < K + 1 := by linarith
  have hA : ‖(K : ℂ) ^ z - ((K + 1 : ℝ) : ℂ) ^ z‖ ≤ 2 * K ^ z.re := by
    have h1 : ‖((K + 1 : ℝ) : ℂ) ^ z‖ ≤ K ^ z.re := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hK10]
      exact Real.rpow_le_rpow_of_nonpos hK0 (by linarith) hz.le
    have h2 : ‖(K : ℂ) ^ z‖ = K ^ z.re := Complex.norm_cpow_eq_rpow_re_of_pos hK0 z
    calc _ ≤ ‖(K : ℂ) ^ z‖ + ‖((K + 1 : ℝ) : ℂ) ^ z‖ := norm_sub_le _ _
      _ ≤ 2 * K ^ z.re := by rw [h2]; linarith
  have hB : ‖(K : ℂ) ^ z - ((K + 1 : ℝ) : ℂ) ^ z‖ ≤ ‖z‖ * K ^ (z.re - 1) := by
    have hderiv : ∀ r ∈ Icc K (K + 1), HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ z)
        (z * (r : ℂ) ^ (z - 1)) (Icc K (K + 1)) r := by
      intro r hr
      have hr0 : 0 < r := by linarith [hr.1]
      exact ((hasStrictDerivAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 hr0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
    have hbd : ∀ r ∈ Icc K (K + 1), ‖z * (r : ℂ) ^ (z - 1)‖ ≤ ‖z‖ * K ^ (z.re - 1) := by
      intro r hr
      have hr0 : 0 < r := by linarith [hr.1]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr0, Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hK0 hr.1 (by linarith)) (norm_nonneg _)
    have h := (convex_Icc K (K + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd
      (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
    rw [norm_sub_rev]
    simpa using h
  set y : ℝ := ‖z‖ / (2 * K) with hy
  have hy0 : 0 ≤ y := div_nonneg (norm_nonneg _) (by linarith)
  have hKz : 0 ≤ K ^ z.re := Real.rpow_nonneg hK0.le _
  rcases le_total y 1 with hy1 | hy1
  · have hyθ : y ≤ y ^ θ := by
      rcases hy0.eq_or_lt with h | h
      · rw [← h]; exact Real.rpow_nonneg le_rfl _
      · simpa using Real.rpow_le_rpow_of_exponent_ge h hy1 hθ1
    calc _ ≤ ‖z‖ * K ^ (z.re - 1) := hB
      _ = 2 * K ^ z.re * y := by
          rw [Real.rpow_sub_one hK0.ne', hy]; field_simp; try ring
      _ ≤ 2 * K ^ z.re * y ^ θ := mul_le_mul_of_nonneg_left hyθ (mul_nonneg (by norm_num) hKz)
  · have h1 : 1 ≤ y ^ θ := Real.one_le_rpow hy1 hθ0
    calc _ ≤ 2 * K ^ z.re := hA
      _ = 2 * K ^ z.re * 1 := (mul_one _).symm
      _ ≤ 2 * K ^ z.re * y ^ θ := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hKz)

/-! ### Column energy -/

/-- `c_η = 2 ζ(η + ½) ((1+2η)/2)^{¾−η/2} 6^{¼+η/2}`. -/
def columnMellinConstant (η : ℝ) : ℝ :=
  2 * RHTower.realZetaSeries (η + 1 / 2) * ((1 + 2 * η) / 2) ^ (3 / 4 - η / 2) *
    6 ^ (1 / 4 + η / 2)

/-- **Pointwise column symbol**: on `Re s = −½`,
`|M Δ_K(−½ + it)| ≤ c_η K^{−5/4−η/2} |ζ(½ − it)| (2+|t|)^{−¼−η/2}`. -/
theorem norm_mellin_columnProfile_le {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) {K : ℝ}
    (hK : 1 ≤ K) (t : ℝ) :
    ‖mellin (fun x => (columnProfile η K x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      columnMellinConstant η * K ^ (-5 / 4 - η / 2) *
        (‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ * (2 + |t|) ^ (-1 / 4 - η / 2)) := by
  have hK0 : 0 < K := by linarith
  have hη0 : 0 < η := by linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 3 / 4 - η / 2 := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hP := norm_mellin_sourceProfile_le h0 t
  rw [mellin_columnProfile_eq h0 h1 hK t, norm_mul]
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ((-1 / 2 : ℝ) : ℂ) + t * I := ⟨_, rfl⟩
  rw [← hs] at hP ⊢
  have hzre : (s - η).re = -1 / 2 - η := by rw [hs]; simp
  have hD := norm_cpow_sub_cpow_le hK (z := s - η) (by rw [hzre]; linarith) hθ0 hθ1
  rw [hzre] at hD
  have hZ0 : 0 ≤ RHTower.realZetaSeries (η + 1 / 2) := by
    have := RHTower.one_le_realZetaSeries (s := η + 1 / 2) (by linarith); linarith
  have hsre : s.re = -1 / 2 := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hXre : 1 / 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hsre, abs_of_neg (by norm_num)] at this
    linarith
  have hXim : |t| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    rwa [hsim] at this
  have hX0 : 0 < ‖s‖ := by linarith
  have hY0 : (0 : ℝ) < 2 + |t| := by positivity
  have hXY : (2 + |t|) / 6 ≤ ‖s‖ := by
    rcases le_total |t| (1 / 2) with ht | ht <;> linarith
  have hzn : ‖s - (η : ℂ)‖ ≤ (1 + 2 * η) * ‖s‖ := by
    have h := norm_sub_le s (η : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0] at h
    nlinarith [mul_le_mul_of_nonneg_left hXre hη0.le]
  -- the dilation factor in terms of `|s|`
  have hzθ : (‖s - (η : ℂ)‖ / (2 * K)) ^ θ ≤ ((1 + 2 * η) / 2) ^ θ * ‖s‖ ^ θ * K ^ (-θ) := by
    have hle : ‖s - (η : ℂ)‖ / (2 * K) ≤ (1 + 2 * η) / 2 * ‖s‖ * K⁻¹ := by
      have e : (1 + 2 * η) / 2 * ‖s‖ * K⁻¹ = (1 + 2 * η) * ‖s‖ / (2 * K) := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right hzn (by linarith)
    calc (‖s - (η : ℂ)‖ / (2 * K)) ^ θ ≤ ((1 + 2 * η) / 2 * ‖s‖ * K⁻¹) ^ θ :=
          Real.rpow_le_rpow (div_nonneg (norm_nonneg _) (by linarith)) hle hθ0
      _ = ((1 + 2 * η) / 2) ^ θ * ‖s‖ ^ θ * K ^ (-θ) := by
          rw [Real.mul_rpow (mul_nonneg (by linarith) hX0.le) (inv_nonneg.2 hK0.le),
            Real.mul_rpow (by linarith) hX0.le, Real.inv_rpow hK0.le,
            ← Real.rpow_neg hK0.le]
  have hXθ : ‖s‖ ^ θ / ‖s‖ ≤ 6 ^ (1 / 4 + η / 2) * (2 + |t|) ^ (-1 / 4 - η / 2) := by
    rw [← Real.rpow_sub_one hX0.ne']
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (2 + |t|) / 6) hXY
      (by rw [hθ]; linarith : θ - 1 ≤ 0)
    have e1 : -(θ - 1) = 1 / 4 + η / 2 := by rw [hθ]; ring
    have e2 : θ - 1 = -1 / 4 - η / 2 := by rw [hθ]; ring
    calc ‖s‖ ^ (θ - 1) ≤ ((2 + |t|) / 6) ^ (θ - 1) := h
      _ = 6 ^ (1 / 4 + η / 2) * (2 + |t|) ^ (-1 / 4 - η / 2) := by
          rw [Real.div_rpow hY0.le (by norm_num), div_eq_mul_inv,
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6), e1, e2, mul_comm]
  have hKe : K ^ (-1 / 2 - η) * K ^ (-θ) = K ^ (-5 / 4 - η / 2) := by
    rw [← Real.rpow_add hK0]; congr 1; rw [hθ]; ring
  have hKa : 0 ≤ K ^ (-1 / 2 - η) := Real.rpow_nonneg hK0.le _
  set ζn := ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ with hζn
  have hζ0 : 0 ≤ ζn := norm_nonneg _
  have hW0 : 0 ≤ RHTower.realZetaSeries (η + 1 / 2) * (ζn / ‖s‖) :=
    mul_nonneg hZ0 (div_nonneg hζ0 hX0.le)
  have hc0 : 0 ≤ 2 * RHTower.realZetaSeries (η + 1 / 2) * ((1 + 2 * η) / 2) ^ θ *
      (K ^ (-1 / 2 - η) * K ^ (-θ)) * ζn :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hZ0)
      (Real.rpow_nonneg (by linarith) _)) (mul_nonneg hKa (Real.rpow_nonneg hK0.le _))) hζ0
  calc ‖(K : ℂ) ^ (s - η) - ((K + 1 : ℝ) : ℂ) ^ (s - η)‖ *
        ‖mellin (fun x => (sourceProfile η x : ℂ)) s‖
      ≤ (2 * K ^ (-1 / 2 - η) * (‖s - (η : ℂ)‖ / (2 * K)) ^ θ) *
          (RHTower.realZetaSeries (η + 1 / 2) * (ζn / ‖s‖)) :=
        mul_le_mul hD hP (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hKa)
            (Real.rpow_nonneg (div_nonneg (norm_nonneg _) (by linarith)) _))
    _ ≤ (2 * K ^ (-1 / 2 - η) * (((1 + 2 * η) / 2) ^ θ * ‖s‖ ^ θ * K ^ (-θ))) *
          (RHTower.realZetaSeries (η + 1 / 2) * (ζn / ‖s‖)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hzθ (mul_nonneg (by norm_num) hKa)) hW0
    _ = 2 * RHTower.realZetaSeries (η + 1 / 2) * ((1 + 2 * η) / 2) ^ θ *
          (K ^ (-1 / 2 - η) * K ^ (-θ)) * ζn * (‖s‖ ^ θ / ‖s‖) := by
        ring
    _ ≤ 2 * RHTower.realZetaSeries (η + 1 / 2) * ((1 + 2 * η) / 2) ^ θ *
          (K ^ (-1 / 2 - η) * K ^ (-θ)) * ζn *
          (6 ^ (1 / 4 + η / 2) * (2 + |t|) ^ (-1 / 4 - η / 2)) :=
        mul_le_mul_of_nonneg_left hXθ hc0
    _ = columnMellinConstant η * K ^ (-5 / 4 - η / 2) * (ζn * (2 + |t|) ^ (-1 / 4 - η / 2)) := by
        rw [hKe, columnMellinConstant, ← hθ]; ring

/-- **Column symbol energy**:
`∫ |M Δ_K(−½ + it)|² dt ≤ c_η² K^{−5/2−η} J_η`. -/
theorem integral_norm_sq_mellin_columnProfile_le {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) {K : ℝ}
    (hK : 1 ≤ K) :
    ∫ t : ℝ, ‖mellin (fun x => (columnProfile η K x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
      columnMellinConstant η ^ 2 * K ^ (-5 / 2 - η) * criticalWeightMass η := by
  have hK0 : 0 < K := by linarith
  set F : ℝ → ℝ := fun t =>
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (2 + |t|) ^ (-1 / 2 - η) with hF
  have hFi : Integrable F := integrable_criticalWeight h0
  have hFneg : Integrable (fun t : ℝ => F (-t)) := hFi.comp_neg
  have hpt : ∀ t : ℝ,
      ‖mellin (fun x => (columnProfile η K x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤
        columnMellinConstant η ^ 2 * K ^ (-5 / 2 - η) * F (-t) := by
    intro t
    have h := norm_mellin_columnProfile_le h0 h1 hK t
    have hb := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hY0 : (0 : ℝ) < 2 + |t| := by positivity
    have hFt : F (-t) = ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ^ 2 *
        (2 + |t|) ^ (-1 / 2 - η) := by
      simp only [hF, abs_neg]
    rw [hFt]
    calc _ ≤ _ := hb
      _ = columnMellinConstant η ^ 2 * (K ^ (-5 / 4 - η / 2)) ^ 2 *
            (‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ^ 2 *
              ((2 + |t|) ^ (-1 / 4 - η / 2)) ^ 2) := by ring
      _ = _ := by
          rw [sq_rpow_eq hK0, sq_rpow_eq hY0, show 2 * (-5 / 4 - η / 2) = -5 / 2 - η by ring,
            show 2 * (-1 / 4 - η / 2) = -1 / 2 - η by ring]
  calc ∫ t : ℝ, ‖mellin (fun x => (columnProfile η K x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      ≤ ∫ t : ℝ, columnMellinConstant η ^ 2 * K ^ (-5 / 2 - η) * F (-t) :=
        integral_mono_of_nonneg (ae_of_all _ fun t => by positivity)
          (hFneg.const_mul _) (ae_of_all _ hpt)
    _ = columnMellinConstant η ^ 2 * K ^ (-5 / 2 - η) * criticalWeightMass η := by
        rw [integral_const_mul, integral_neg_eq_self F volume]
        rfl

/-- The column constant `8 c_η² J_η / (2π)`. -/
def halfColumnConstant (η : ℝ) : ℝ :=
  8 / (2 * Real.pi) * columnMellinConstant η ^ 2 * criticalWeightMass η

theorem halfColumnConstant_nonneg (η : ℝ) : 0 ≤ halfColumnConstant η := by
  unfold halfColumnConstant
  exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (criticalWeightMass_nonneg η)

/-- **Column bound above half damping**: for `½ < η < 1`,
`Σ_{n<T} C_η(n,k)² ≤ M_η K^{−½−η} + 4K^{−2η}`, `K = k + 1`. -/
theorem sum_sq_centeredRow_le_halfDamping {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) (k T : ℕ) :
    ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
      halfColumnConstant η * ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 - η) +
        4 * ((k + 1 : ℕ) : ℝ) ^ (-2 * η) := by
  have hK : 1 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  obtain ⟨hint, heq⟩ := integral_columnProfile_sq_eq h0 h1 hK
  have h := sum_sq_centeredRow_le_integral (by linarith) k T hint
  rw [heq] at h
  have hM := integral_norm_sq_mellin_columnProfile_le h0 h1 hK
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ((k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hKdef] at h hM hK ⊢
  have hK0 : 0 < K := by linarith
  have hKK : K ^ 2 * K ^ (-5 / 2 - η) = K ^ (-1 / 2 - η) := by
    rw [← Real.rpow_two, ← Real.rpow_add hK0]; congr 1; ring
  have hKη : (K ^ (-η)) ^ 2 = K ^ (-2 * η) := by rw [sq_rpow_eq hK0]; congr 1; ring
  calc ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2
      ≤ 8 * K ^ 2 * (1 / (2 * Real.pi) * ∫ t : ℝ,
          ‖mellin (fun x => (columnProfile η K x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) +
          4 * (K ^ (-η)) ^ 2 := h
    _ ≤ 8 * K ^ 2 * (1 / (2 * Real.pi) *
          (columnMellinConstant η ^ 2 * K ^ (-5 / 2 - η) * criticalWeightMass η)) +
          4 * (K ^ (-η)) ^ 2 := by gcongr
    _ = halfColumnConstant η * (K ^ 2 * K ^ (-5 / 2 - η)) + 4 * (K ^ (-η)) ^ 2 := by
        unfold halfColumnConstant; ring
    _ = halfColumnConstant η * K ^ (-1 / 2 - η) + 4 * K ^ (-2 * η) := by rw [hKK, hKη]

/-- The Hilbert–Schmidt constant `M_η ζ(½ + η) + 4 ζ(2η)` above half damping. -/
def halfDampingHSConstant (η : ℝ) : ℝ :=
  halfColumnConstant η * RHTower.realZetaSeries (1 / 2 + η) +
    4 * RHTower.realZetaSeries (2 * η)

/-- **The chain is Hilbert–Schmidt above half damping**: for `½ < η < 1` and all horizons,
`Σ_{k<M} Σ_{n<T} C_η(n,k)² ≤ M_η ζ(½+η) + 4ζ(2η)`. -/
theorem sum_sum_sq_centeredRow_le_halfDamping {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (M T : ℕ) :
    ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
      halfDampingHSConstant η := by
  have hz1 : ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 - η) ≤
      RHTower.realZetaSeries (1 / 2 + η) := by
    have hs := RHTower.summable_realZetaTerm (s := 1 / 2 + η) (by linarith)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      (hs.sum_le_tsum (Finset.range M) fun k _ => Real.rpow_nonneg (by positivity) _)
    rw [Nat.cast_succ, show -(1 / 2 + η) = -1 / 2 - η by ring]
  have hz2 : ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ^ (-2 * η) ≤
      RHTower.realZetaSeries (2 * η) := by
    have hs := RHTower.summable_realZetaTerm (s := 2 * η) (by linarith)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      (hs.sum_le_tsum (Finset.range M) fun k _ => Real.rpow_nonneg (by positivity) _)
    rw [Nat.cast_succ, show -(2 * η) = -2 * η by ring]
  have hC := halfColumnConstant_nonneg η
  calc ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2
      ≤ ∑ k ∈ Finset.range M, (halfColumnConstant η * ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 - η) +
          4 * ((k + 1 : ℕ) : ℝ) ^ (-2 * η)) :=
        Finset.sum_le_sum fun k _ => sum_sq_centeredRow_le_halfDamping h0 h1 k T
    _ = halfColumnConstant η * ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 - η) +
          4 * ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ^ (-2 * η) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ halfDampingHSConstant η :=
        add_le_add (mul_le_mul_of_nonneg_left hz1 hC) (mul_le_mul_of_nonneg_left hz2 (by norm_num))

/-- **The chain is bounded in `ℓ²` above half damping**: for `½ < η < 1`, finitely supported
`b` and every horizon, `Σ_{n<T} (C_η b)(n)² ≤ (M_η ζ(½+η) + 4ζ(2η)) Σ_k b_k²`. -/
theorem centeredOperator_l2_le_of_halfDamping {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (b : C₀(ℕ, ℝ)) {N : ℕ} (hb : ∀ k, N ≤ k → b k = 0) (T : ℕ) :
    ∑ n ∈ Finset.range T,
        arithmeticDampingCenteredOperator (by linarith : (0 : ℝ) < η) b n ^ 2 ≤
      halfDampingHSConstant η * ∑ k ∈ Finset.range N, b k ^ 2 := by
  have hη0 : (0 : ℝ) < η := by linarith
  have happ : ∀ n, arithmeticDampingCenteredOperator hη0 b n =
      ∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k * b k := by
    intro n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by
      rw [hb k (by simpa using hk), mul_zero]
  have hrow : ∀ n, arithmeticDampingCenteredOperator hη0 b n ^ 2 ≤
      (∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k ^ 2) *
        ∑ k ∈ Finset.range N, b k ^ 2 := by
    intro n; rw [happ]; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  calc ∑ n ∈ Finset.range T, arithmeticDampingCenteredOperator hη0 b n ^ 2
      ≤ ∑ n ∈ Finset.range T, (∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_le_sum fun n _ => hrow n
    _ = (∑ k ∈ Finset.range N, ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ Finset.range N, b k ^ 2 := by rw [← Finset.sum_mul, Finset.sum_comm]
    _ ≤ halfDampingHSConstant η * ∑ k ∈ Finset.range N, b k ^ 2 :=
        mul_le_mul_of_nonneg_right (sum_sum_sq_centeredRow_le_halfDamping h0 h1 N T) hb0

/-! ### The threshold is sharp -/

/-- `ρ_η < 1`: the density `1/ζ(1+η)` lies strictly below one. -/
theorem density_re_lt_one {η : ℝ} (hη : 0 < η) : (pmPowerDampedDivisorDensity η).re < 1 := by
  rw [pmPowerDampedDivisorDensity_re_eq hη]
  have hs := RHTower.summable_realZetaTerm (s := 1 + η) (by linarith)
  have h2 : (1 : ℝ) + (2 : ℝ) ^ (-(1 + η)) ≤ RHTower.realZetaSeries (1 + η) := by
    have := sum_le_tsum (Finset.range 2) (fun j _ => Real.rpow_nonneg (by positivity) _) hs
    simpa [Finset.sum_range_succ, RHTower.realZetaSeries, one_add_one_eq_two] using this
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 + η)) := Real.rpow_pos_of_pos (by norm_num) _
  rw [div_lt_one (by linarith)]
  linarith

/-- **The diagonal of the chain**: `C_η(k, k) ≥ (1 − ρ_η) (k+1)^{−η}`.  The transition is lower
triangular with diagonal `(k+1)^{−η}`, and the entrance mass is at most `ρ_η (k+1)^{−η}`. -/
theorem centeredRow_diag_ge {η : ℝ} (hη : 0 < η) (k : ℕ) :
    (1 - (pmPowerDampedDivisorDensity η).re) * ((k + 1 : ℕ) : ℝ) ^ (-η) ≤
      arithmeticDampingCenteredRow η k k := by
  unfold arithmeticDampingCenteredRow
  rw [arithmeticDampingTransition_diagonal η (Nat.succ_pos k)]
  have := entrance_le hη k
  linarith

/-- **No Hilbert–Schmidt bound at or below half damping**: for `0 < η ≤ ½` the squared entries of
the centred chain have no uniform bound, already on the diagonal.  With
`sum_sum_sq_centeredRow_le_halfDamping`, `C_η` is Hilbert–Schmidt in the receiver norm exactly
when `η > ½` (for `η < 1`). -/
theorem not_bounded_sum_sum_sq_centeredRow_of_le_half {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) :
    ¬ ∃ M : ℝ, ∀ K T : ℕ,
      ∑ k ∈ Finset.range K, ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2 ≤ M := by
  rintro ⟨M, hM⟩
  set ρ := (pmPowerDampedDivisorDensity η).re with hρ
  have hρ1 : ρ < 1 := density_re_lt_one h0
  have hc : 0 < (1 - ρ) ^ 2 := pow_pos (by linarith) 2
  have hdiag : ∀ k : ℕ, (1 - ρ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-2 * η) ≤
      arithmeticDampingCenteredRow η k k ^ 2 := by
    intro k
    have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h := centeredRow_diag_ge h0 k
    have hl : 0 ≤ (1 - ρ) * ((k + 1 : ℕ) : ℝ) ^ (-η) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hK0.le _)
    calc (1 - ρ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-2 * η) =
          ((1 - ρ) * ((k + 1 : ℕ) : ℝ) ^ (-η)) ^ 2 := by
          rw [mul_pow, sq_rpow_eq hK0, show 2 * -η = -2 * η by ring]
      _ ≤ _ := pow_le_pow_left₀ hl h 2
  have hpart : ∀ K : ℕ, ∑ k ∈ Finset.range K, (1 - ρ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-2 * η) ≤ M := by
    intro K
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) (hM K K)
    refine le_trans (hdiag k) ?_
    exact Finset.single_le_sum (f := fun n => arithmeticDampingCenteredRow η n k ^ 2)
      (fun n _ => sq_nonneg _) hk
  have hsum : Summable fun k : ℕ => (1 - ρ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-2 * η) :=
    summable_of_sum_range_le (fun k => by positivity) hpart
  have hsum' : Summable fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (2 * η))⁻¹ := by
    refine (hsum.mul_left ((1 - ρ) ^ 2)⁻¹).congr fun k => ?_
    have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, show -2 * η = -(2 * η) by ring,
      Real.rpow_neg hK0.le]
  have hs := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (2 * η))⁻¹) 1).mp hsum'
  have := Real.summable_nat_rpow_inv.mp hs
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
