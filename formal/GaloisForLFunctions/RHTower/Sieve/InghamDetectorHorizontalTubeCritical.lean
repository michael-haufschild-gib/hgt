import GaloisForLFunctions.RHTower.Sieve.InghamDetectorHorizontalTube

/-!
# Horizontal-tube control for the Ingham detector down to the critical line

The tube of `InghamDetectorHorizontalTube` is the Jensen disc of radius `4` centred at `4 + iτ`; with
the radii `17/5 < 7/2 < 15/4 < 4` it controls the logarithmic derivative of the detector on the
horizontal segments `[699/1000, 4] + iT`, `|T − τ| ≤ 1/2`. Centring the same disc at `19/5 + iτ`
keeps it inside `Re z ≥ −1/5`, where the detector is still polynomially bounded
(`exists_norm_inghamDetector_criticalTube_le`), while `|detector(19/5 + iτ)| ≥ 1/2`
(`one_half_le_norm_inghamDetector_nineteen_fifths`, from `‖ζM_X − 1‖ ≤ (5/9) X^{−9/5}` on
`Re s = 19/5`). Since `(33/10)² + (1/2)² ≤ (17/5)²`, the unchanged radii now cover the segments
`[1/2, 4] + iT`: zero-free horizontal segments with `‖logDeriv detector‖ ≪ (log X)²` exist at both
ends of `[−X, X]` (`exists_inghamDetector_two_horizontal_edges_critical_polylog`).
-/

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- The absolute tail of `ζM_X − 1` on `Re s = 19/5`. -/
theorem inghamRightEdgeAbsoluteTail_nineteen_fifths_le {X : ℕ} (hX : 1 ≤ X) :
    inghamRightEdgeAbsoluteTail (19 / 5) X ≤ (X : ℝ) ^ (-(9 / 5 : ℝ)) / (9 / 5) := by
  let major : ℕ → ℝ := fun n => (n.divisors.card : ℝ) * (n : ℝ) ^ (-(19 / 5 : ℝ))
  have hmajor : Summable major := summable_card_divisors_mul_rpow (by norm_num)
  have hterm : ∀ k : ℕ,
      major (k + X + 1) ≤ (((k + X + 1 : ℕ) : ℝ)) ^ (-(14 / 5 : ℝ)) := by
    intro k
    have hn : (0 : ℕ) < k + X + 1 := by omega
    have hnR : (0 : ℝ) < ((k + X + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    have hd : ((((k + X + 1 : ℕ)).divisors.card : ℕ) : ℝ) ≤ ((k + X + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self (k + X + 1)
    calc major (k + X + 1)
        ≤ ((k + X + 1 : ℕ) : ℝ) * ((k + X + 1 : ℕ) : ℝ) ^ (-(19 / 5 : ℝ)) :=
          mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hnR.le _)
      _ = ((k + X + 1 : ℕ) : ℝ) ^ (-(14 / 5 : ℝ)) := by
          rw [show ((k + X + 1 : ℕ) : ℝ) * ((k + X + 1 : ℕ) : ℝ) ^ (-(19 / 5 : ℝ)) =
              ((k + X + 1 : ℕ) : ℝ) ^ (1 : ℝ) * ((k + X + 1 : ℕ) : ℝ) ^ (-(19 / 5 : ℝ)) by
                rw [Real.rpow_one], ← Real.rpow_add hnR]
          norm_num
  have hmajorShift : Summable (fun k => major (k + X + 1)) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hmajor
  have hp : Summable (fun k : ℕ => (((k + X + 1 : ℕ) : ℝ)) ^ (-(14 / 5 : ℝ))) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (X + 1)).mpr
        (summable_nat_rpow_neg (by norm_num : (1 : ℝ) < 14 / 5))
  calc inghamRightEdgeAbsoluteTail (19 / 5) X = ∑' k : ℕ, major (k + X + 1) := rfl
    _ ≤ ∑' k : ℕ, (((k + X + 1 : ℕ) : ℝ)) ^ (-(14 / 5 : ℝ)) :=
      Summable.tsum_le_tsum hterm hmajorShift hp
    _ ≤ (X : ℝ) ^ (1 - (14 / 5 : ℝ)) / ((14 / 5 : ℝ) - 1) :=
      tsum_tail_rpow_neg_le (by norm_num) hX
    _ = (X : ℝ) ^ (-(9 / 5 : ℝ)) / (9 / 5) := by norm_num

/-- On `Re s = 19/5` the detector is at least `1/2` once `|Im s| ≥ X/2`, `X ≥ 10`. -/
theorem one_half_le_norm_inghamDetector_nineteen_fifths
    {X : ℕ} {tau : ℝ} (hX : 10 ≤ X) (htlow : (X : ℝ) / 2 ≤ |tau|) :
    (1 : ℝ) / 2 ≤ ‖inghamDetector X ((19 / 5 : ℂ) + (tau : ℂ) * I)‖ := by
  let s : ℂ := (19 / 5 : ℂ) + (tau : ℂ) * I
  let e : ℂ := riemannZeta s * inghamMollifier X s - 1
  have hX1N : 1 ≤ X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX1N
  have he0 : ‖e‖ ≤ (X : ℝ) ^ (-(9 / 5 : ℝ)) / (9 / 5) := by
    have h := (norm_inghamMollifiedError_right_le_absoluteTail (beta := 19 / 5) (by norm_num)
      hX1N tau).trans (inghamRightEdgeAbsoluteTail_nineteen_fifths_le hX1N)
    have hcast : ((19 / 5 : ℝ) : ℂ) = (19 / 5 : ℂ) := by push_cast; ring
    rw [hcast] at h
    simpa only [s, e] using h
  have hpow : (X : ℝ) ^ (-(9 / 5 : ℝ)) ≤ 1 / 10 := by
    have h1 : (X : ℝ) ^ (-(9 / 5 : ℝ)) ≤ (X : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    have hX10 : (10 : ℝ) ≤ X := by exact_mod_cast hX
    rw [Real.rpow_neg_one] at h1
    have h2 : (X : ℝ)⁻¹ ≤ 1 / 10 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have he : ‖e‖ ≤ (1 : ℝ) / 2 := by
    have : (X : ℝ) ^ (-(9 / 5 : ℝ)) / (9 / 5) ≤ 1 / 18 := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  have hepow : ‖e ^ 2‖ ≤ (1 : ℝ) / 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg e]
  have hclassical : (3 : ℝ) / 4 ≤ ‖1 - e ^ 2‖ := by
    have hone : (1 : ℝ) ≤ ‖1 - e ^ 2‖ + ‖e ^ 2‖ := by
      calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
        _ = ‖(1 - e ^ 2) + e ^ 2‖ := by ring_nf
        _ ≤ ‖1 - e ^ 2‖ + ‖e ^ 2‖ := norm_add_le _ _
    linarith
  have htau1 : (1 : ℝ) ≤ |tau| := by
    have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hsub : (1 : ℝ) ≤ ‖s - 1‖ := by
    have him := Complex.abs_im_le_norm (s - 1)
    have himEq : (s - 1).im = tau := by simp [s]
    rw [himEq] at him
    exact htau1.trans him
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    rw [him] at htau1
    norm_num at htau1
  rw [inghamDetector_eq_poleCleared X hs1, norm_mul]
  change (1 : ℝ) / 2 ≤ ‖(s - 1) ^ 2‖ * ‖1 - e ^ 2‖
  have hgauge : (1 : ℝ) ≤ ‖(s - 1) ^ 2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg (s - 1)]
  nlinarith [norm_nonneg (1 - e ^ 2)]

/-- `‖M_X(z)‖ ≤ X²` on `Re z ≥ −1/5`. -/
theorem norm_inghamMollifier_le_sq_of_neg_fifth_le (X : ℕ) {s : ℂ} (hs : -(1 / 5 : ℝ) ≤ s.re) :
    ‖inghamMollifier X s‖ ≤ (X : ℝ) ^ 2 := by
  rw [inghamMollifier]
  calc ‖∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 X, ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (X : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
        have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        rw [norm_mul]
        have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hpow : ‖(n : ℂ) ^ (-s)‖ ≤ (n : ℝ) := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnR]
          calc (n : ℝ) ^ (-s).re ≤ (n : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hn1R (by simp; linarith)
            _ = n := Real.rpow_one _
        calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * ‖(n : ℂ) ^ (-s)‖ ≤ 1 * (n : ℝ) :=
              mul_le_mul hμ hpow (norm_nonneg _) zero_le_one
          _ ≤ X := by linarith
    _ = (X : ℝ) ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring

private theorem criticalTube_geometry
    {X : ℕ} {tau : ℝ} (hX : 10 ≤ X)
    (htlow : (X : ℝ) / 2 ≤ |tau|) (hthigh : |tau| ≤ 2 * (X : ℝ))
    {z : ℂ} (hz : z ∈ closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) 4) :
    -(1 / 5 : ℝ) ≤ z.re ∧ z.re ≤ 8 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ 3 * (X : ℝ) ∧
      ‖z - 1‖ ≤ 5 * (X : ℝ) := by
  have hdist : ‖z - ((19 / 5 : ℂ) + (tau : ℂ) * I)‖ ≤ 4 := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hreabs : |z.re - 19 / 5| ≤ 4 := by
    have h := Complex.abs_re_le_norm (z - ((19 / 5 : ℂ) + (tau : ℂ) * I))
    have hre : (z - ((19 / 5 : ℂ) + (tau : ℂ) * I)).re = z.re - 19 / 5 := by
      simp
    rw [hre] at h
    exact h.trans hdist
  have himabs : |z.im - tau| ≤ 4 := by
    have h := Complex.abs_im_le_norm (z - ((19 / 5 : ℂ) + (tau : ℂ) * I))
    have hcim : ((19 / 5 : ℂ) + (tau : ℂ) * I).im = tau := by simp
    rw [sub_im, hcim] at h
    exact h.trans hdist
  have hrelo : -(1 / 5 : ℝ) ≤ z.re := (abs_le.mp hreabs).1 |> fun h => by linarith
  have hrehi : z.re ≤ 8 := (abs_le.mp hreabs).2 |> fun h => by linarith
  have himhi0 : |z.im| ≤ |tau| + 4 := by
    calc |z.im| = |(z.im - tau) + tau| := by ring_nf
      _ ≤ |z.im - tau| + |tau| := abs_add_le _ _
      _ ≤ |tau| + 4 := by linarith
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have himhi : |z.im| ≤ 3 * (X : ℝ) := by linarith
  have himlo0 : |tau| ≤ |z.im| + 4 := by
    calc |tau| = |(tau - z.im) + z.im| := by ring_nf
      _ ≤ |tau - z.im| + |z.im| := abs_add_le _ _
      _ = |z.im - tau| + |z.im| := by rw [abs_sub_comm]
      _ ≤ |z.im| + 4 := by linarith
  have himlo : 1 ≤ |z.im| := by linarith
  have hre1 : |(z - 1).re| ≤ 7 := by
    simp only [sub_re, one_re]
    rw [abs_le]
    constructor <;> linarith
  have hnormsub := Complex.norm_le_abs_re_add_abs_im (z - 1)
  have himsub : |(z - 1).im| = |z.im| := by simp
  rw [himsub] at hnormsub
  have hsub : ‖z - 1‖ ≤ 5 * (X : ℝ) := by linarith
  exact ⟨hrelo, hrehi, himlo, himhi, hsub⟩

/-- The detector is polynomially bounded on the critical tube. -/
theorem exists_norm_inghamDetector_criticalTube_le :
    ∃ (C : ℝ) (Q : ℕ), 0 ≤ C ∧ ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∀ z ∈ closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) 4,
        ‖inghamDetector X z‖ ≤ C * (X : ℝ) ^ Q := by
  obtain ⟨Cz, N, hCz, hzeta⟩ := RHTower.exists_bound_norm_riemannZeta_strip 8
  let K : ℝ := 5 * Cz * 3 ^ N
  let C : ℝ := K * (10 + K)
  let Q : ℕ := 2 * N + 6
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, Q, hC, ?_⟩
  intro X tau hX htlow hthigh z hz
  obtain ⟨hzre0, hzre8, hzim1, hzimX, hzsub⟩ := criticalTube_geometry hX htlow hthigh hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzim1
  have hzetaBound : ‖riemannZeta z‖ ≤ Cz * |z.im| ^ N := by
    have hzrepr : (z.re : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp
    have habs : |z.re| ≤ 8 := abs_le.mpr ⟨by linarith, hzre8⟩
    simpa only [hzrepr] using hzeta z.re z.im habs hzim1
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hzimPow : |z.im| ^ N ≤ (3 * (X : ℝ)) ^ N := pow_le_pow_left₀ (abs_nonneg _) hzimX N
  have hG : ‖zetaResidueUnit z‖ ≤ K * (X : ℝ) ^ (N + 1) := by
    rw [zetaResidueUnit, Function.update_of_ne hz1, norm_mul]
    calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ (5 * (X : ℝ)) * (Cz * |z.im| ^ N) :=
          mul_le_mul hzsub hzetaBound (norm_nonneg _) (by positivity)
      _ ≤ (5 * (X : ℝ)) * (Cz * (3 * (X : ℝ)) ^ N) := by gcongr
      _ = K * (X : ℝ) ^ (N + 1) := by
          rw [mul_pow, pow_succ]
          dsimp [K]
          ring
  have hM := norm_inghamMollifier_le_sq_of_neg_fifth_le X hzre0
  have hA : ‖zetaResidueUnit z * inghamMollifier X z‖ ≤ K * (X : ℝ) ^ (N + 3) := by
    rw [norm_mul]
    calc ‖zetaResidueUnit z‖ * ‖inghamMollifier X z‖ ≤
          (K * (X : ℝ) ^ (N + 1)) * (X : ℝ) ^ 2 :=
          mul_le_mul hG hM (norm_nonneg _) (by positivity)
      _ = K * (X : ℝ) ^ (N + 3) := by rw [show N + 3 = (N + 1) + 2 by omega, pow_add]; ring
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hpowmono : (X : ℝ) ≤ (X : ℝ) ^ (N + 3) := by
    calc (X : ℝ) = (X : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (X : ℝ) ^ (N + 3) := pow_le_pow_right₀ hX1 (by omega)
  have hsecond : ‖2 * (z - 1) - zetaResidueUnit z * inghamMollifier X z‖ ≤
      (10 + K) * (X : ℝ) ^ (N + 3) := by
    have htwo : 2 * ‖z - 1‖ ≤ 10 * (X : ℝ) := by linarith
    have hten : 10 * (X : ℝ) ≤ 10 * (X : ℝ) ^ (N + 3) :=
      mul_le_mul_of_nonneg_left hpowmono (by norm_num)
    calc ‖2 * (z - 1) - zetaResidueUnit z * inghamMollifier X z‖ ≤
          2 * ‖z - 1‖ + ‖zetaResidueUnit z * inghamMollifier X z‖ := by
          calc _ ≤ ‖2 * (z - 1)‖ + ‖zetaResidueUnit z * inghamMollifier X z‖ := norm_sub_le _ _
            _ = 2 * ‖z - 1‖ + ‖zetaResidueUnit z * inghamMollifier X z‖ := by simp
      _ ≤ 10 * (X : ℝ) + K * (X : ℝ) ^ (N + 3) := by linarith
      _ ≤ 10 * (X : ℝ) ^ (N + 3) + K * (X : ℝ) ^ (N + 3) := by linarith
      _ = (10 + K) * (X : ℝ) ^ (N + 3) := by ring
  rw [inghamDetector, norm_mul]
  calc ‖zetaResidueUnit z * inghamMollifier X z‖ *
        ‖2 * (z - 1) - zetaResidueUnit z * inghamMollifier X z‖ ≤
      (K * (X : ℝ) ^ (N + 3)) * ((10 + K) * (X : ℝ) ^ (N + 3)) :=
        mul_le_mul hA hsecond (norm_nonneg _) (by positivity)
    _ = C * (X : ℝ) ^ Q := by
        dsimp [C, Q]
        rw [show 2 * N + 6 = (N + 3) + (N + 3) by omega, pow_add]
        ring

/-- Jensen: the zero mass of the detector in the inner disc of the critical tube. -/
theorem exists_inghamDetector_criticalTube_zeroMass_le_log :
    ∃ (C : ℝ) (Q : ℕ), 1 ≤ C ∧ ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ((∑ᶠ u, MeromorphicOn.divisor (inghamDetector X)
          (closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ)) u : ℤ) : ℝ) ≤
        Real.log ((C * (X : ℝ) ^ Q) / ((1 : ℝ) / 2)) /
          Real.log ((4 : ℝ) / (15 / 4 : ℝ)) := by
  obtain ⟨C0, Q, hC0, henv⟩ := exists_norm_inghamDetector_criticalTube_le
  let C : ℝ := C0 + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, Q, hC, ?_⟩
  intro X tau hX htlow hthigh
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ Q := one_le_pow₀ hX1
  have hM1 : (1 : ℝ) ≤ C * (X : ℝ) ^ Q := by nlinarith
  have hsphere : ∀ z ∈ sphere ((19 / 5 : ℂ) + (tau : ℂ) * I) |(4 : ℝ)|,
      ‖inghamDetector X z‖ ≤ C * (X : ℝ) ^ Q := by
    intro z hz
    have hzball : z ∈ closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) 4 := by
      have := sphere_subset_closedBall hz
      norm_num at this ⊢
      exact this
    have h0 := henv hX htlow hthigh z hzball
    have hmul : C0 * (X : ℝ) ^ Q ≤ C * (X : ℝ) ^ Q :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
    exact h0.trans hmul
  have hana : AnalyticOnNhd ℂ (inghamDetector X)
      (closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) |(4 : ℝ)|) :=
    (inghamDetector_analyticOnNhd_univ X).mono (Set.subset_univ _)
  have hmain := GaloisForLFunctions.HTGeometry.sum_divisor_le_of_bounds
    (c := (19 / 5 : ℂ) + (tau : ℂ) * I) (r := (15 / 4 : ℝ)) (R := 4)
    (M := C * (X : ℝ) ^ Q) (m := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) hM1 (by norm_num) hana
    (one_half_le_norm_inghamDetector_nineteen_fifths hX htlow) hsphere
  have habs : |(15 / 4 : ℝ)| = (15 / 4 : ℝ) := by norm_num
  rw [habs] at hmain
  exact hmain

/-- Factorisation data for the detector on the critical tube. -/
theorem exists_inghamDetector_criticalTube_factor_data :
    ∃ (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj : ℕ), 1 ≤ Ce ∧ 1 ≤ Cj ∧
      ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∃ (T : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g Set.univ ∧
        (∀ z ∈ closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ), g z ≠ 0) ∧
        (∀ a ∈ T, a ∈ closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ)) ∧
        (∀ a ∈ T, 1 ≤ m a) ∧
        (∀ z : ℂ, inghamDetector X z = (∏ a ∈ T, (z - a) ^ (m a)) * g z) ∧
        ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ inghamDetectorTubeJensenBound Cj Qj X ∧
        (∀ z ∈ closedBall ((19 / 5 : ℂ) + (tau : ℂ) * I) 4,
          ‖g z‖ ≤ (Ce * (X : ℝ) ^ Qe) / ((1 : ℝ) / 4) ^ (∑ a ∈ T, m a)) ∧
        ((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ (∑ a ∈ T, m a) ≤
          ‖g ((19 / 5 : ℂ) + (tau : ℂ) * I)‖ := by
  obtain ⟨Ce0, Qe, hCe0, henv⟩ := exists_norm_inghamDetector_criticalTube_le
  obtain ⟨Cj, Qj, hCj, hcount⟩ := exists_inghamDetector_criticalTube_zeroMass_le_log
  let Ce : ℝ := Ce0 + 1
  have hCe : 1 ≤ Ce := by dsimp only [Ce]; linarith
  refine ⟨Ce, Qe, Cj, Qj, hCe, hCj, ?_⟩
  intro X tau hX htlow hthigh
  let c0 : ℂ := (19 / 5 : ℂ) + (tau : ℂ) * I
  have hcenter := one_half_le_norm_inghamDetector_nineteen_fifths hX htlow
  have hneSome : ∃ z : ℂ, inghamDetector X z ≠ 0 := by
    refine ⟨c0, ?_⟩
    exact norm_ne_zero_iff.mp (ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hcenter))
  have hnz : ∀ a : ℂ, ¬ ∀ᶠ z in nhds a, inghamDetector X z = 0 := by
    intro a hevent
    exact (inghamDetector_order_ne_top_of_exists_ne_zero X a hneSome)
      (analyticOrderAt_eq_top.mpr hevent)
  have hsphere : ∀ z ∈ sphere c0 4, ‖inghamDetector X z‖ ≤ Ce * (X : ℝ) ^ Qe := by
    intro z hz
    have h0 := henv hX htlow hthigh z (sphere_subset_closedBall hz)
    exact h0.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [Ce]; linarith) (by positivity))
  have hmass : ((∑ᶠ u, MeromorphicOn.divisor (inghamDetector X)
      (closedBall c0 (15 / 4 : ℝ)) u : ℤ) : ℝ) ≤ inghamDetectorTubeJensenBound Cj Qj X := by
    simpa only [c0, inghamDetectorTubeJensenBound] using hcount hX htlow hthigh
  simpa only [c0] using exists_tube_factor_data
    (inghamDetector_analyticOnNhd_univ X) hnz hsphere hcenter hmass

private theorem critical_segment_norm_le_seventeen_fifths
    {x T tau : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 4) (hT : |T - tau| ≤ 1 / 2) :
    ‖((x : ℂ) + (T : ℂ) * I) - ((19 / 5 : ℂ) + (tau : ℂ) * I)‖ ≤ (17 : ℝ) / 5 := by
  let z : ℂ := (x : ℂ) + (T : ℂ) * I
  let c0 : ℂ := (19 / 5 : ℂ) + (tau : ℂ) * I
  have hre : (z - c0).re = x - 19 / 5 := by simp [z, c0]
  have him : (z - c0).im = T - tau := by simp [z, c0]
  have hxabs : |x - 19 / 5| ≤ 33 / 10 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hsquares : ‖z - c0‖ ^ 2 = (x - 19 / 5) ^ 2 + (T - tau) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hxSq : (x - 19 / 5) ^ 2 ≤ (33 / 10 : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (x - 19 / 5)) (by norm_num : (0 : ℝ) ≤ 33 / 10)).2 hxabs
    simpa only [sq_abs] using h
  have hTSq : (T - tau) ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (T - tau)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hT
    simpa only [sq_abs] using h
  have hn := norm_nonneg (z - c0)
  dsimp only [z, c0] at hsquares hn ⊢
  nlinarith

/-- **Logarithmic-derivative control on `[1/2, 4] + iT`.** -/
theorem exists_inghamDetector_horizontal_logDeriv_control_critical :
    ∃ (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj : ℕ), 1 ≤ Ce ∧ 1 ≤ Cj ∧
      ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∃ T ∈ Ioo (tau - 1 / 2) (tau + 1 / 2), ∃ N : ℕ,
        (N : ℝ) ≤ inghamDetectorTubeJensenBound Cj Qj X ∧
        ∀ x ∈ Icc (1 / 2 : ℝ) 4,
          inghamDetector X ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
            ‖logDeriv (inghamDetector X) ((x : ℂ) + (T : ℂ) * I)‖ ≤
              inghamDetectorHorizontalLogDerivBound Ce Qe Cj Qj X N := by
  classical
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hfactor⟩ := exists_inghamDetector_criticalTube_factor_data
  refine ⟨Ce, Qe, Cj, Qj, hCe, hCj, ?_⟩
  intro X tau hX htlow hthigh
  obtain ⟨Z, m, g, hg, hgfree, hZmem, hmpos, hfac, hNL, hgball, hgcenter⟩ :=
    hfactor hX htlow hthigh
  let L : ℝ := inghamDetectorTubeJensenBound Cj Qj X
  let N : ℕ := ∑ a ∈ Z, m a
  let E : Finset ℝ := Z.image Complex.im
  let delta : ℝ := (4 * (L + 1))⁻¹
  have hL0 : 0 ≤ L :=
    inghamDetectorTubeJensenBound_nonneg (Q := Qj) hCj (show 1 ≤ X by omega)
  have hZN : Z.card ≤ N := by
    calc Z.card = ∑ _a ∈ Z, 1 := by simp
      _ ≤ ∑ a ∈ Z, m a := Finset.sum_le_sum fun a ha => hmpos a ha
      _ = N := rfl
  have hEcard : E.card ≤ Z.card := Finset.card_image_le
  have hEL : (E.card : ℝ) ≤ L := by
    have hEN : E.card ≤ N := hEcard.trans hZN
    exact (Nat.cast_le.mpr hEN).trans (by simpa only [N, L] using hNL)
  have hden : 0 < 4 * (L + 1) := by positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hsmall : 2 * E.card * delta < 1 := by
    have hmul : 2 * (E.card : ℝ) ≤ 2 * L := by linarith
    dsimp only [delta]
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨T, hT, hsepE⟩ :=
    exists_Ioo_add_one_separated_from_finset E (tau - 1 / 2) delta hdelta.le hsmall
  have hTband : T ∈ Ioo (tau - 1 / 2) (tau + 1 / 2) := by
    constructor <;> linarith [hT.1, hT.2]
  refine ⟨T, hTband, N, ?_, ?_⟩
  · simpa only [N, L] using hNL
  · intro x hx
    let z : ℂ := (x : ℂ) + (T : ℂ) * I
    let c0 : ℂ := (19 / 5 : ℂ) + (tau : ℂ) * I
    have hTtau : |T - tau| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hT.1, hT.2]
    have hzrho : ‖z - c0‖ ≤ (17 : ℝ) / 5 := by
      simpa only [z, c0] using critical_segment_norm_le_seventeen_fifths hx hTtau
    have hsepZ : ∀ a ∈ Z, delta ≤ ‖z - a‖ := by
      intro a ha
      have haE : a.im ∈ E := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      have hsepIm := hsepE a.im haE
      have himNorm := Complex.abs_im_le_norm (z - a)
      have him : (z - a).im = T - a.im := by simp [z]
      rw [him] at himNorm
      exact hsepIm.trans himNorm
    have hzK : z ∈ closedBall c0 (15 / 4 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      exact hzrho.trans (by norm_num)
    have hdetne : inghamDetector X z ≠ 0 :=
      ne_zero_of_factor_data (hfac z) (hgfree z (by simpa only [c0] using hzK)) hdelta hsepZ
    have hpoint := norm_logDeriv_le_of_factor_data
      (f := inghamDetector X) (g := g) (c := c0) (z := z)
      (T := Z) (m := m) (Mf := Ce * (X : ℝ) ^ Qe)
      (m0 := (1 : ℝ) / 2) (d := delta)
      hg (by simpa only [c0] using hgfree) hfac
      (by simpa only [c0] using hgball) (by norm_num)
      (by simpa only [c0] using hgcenter) hdelta hsepZ hzrho
    refine ⟨by simpa only [z] using hdetne, ?_⟩
    simpa only [z, N, L, delta, inghamDetectorHorizontalLogDerivBound] using hpoint

/-- **Two zero-free horizontal edges on `[1/2, 4]`** at heights near `±X` with
`‖logDeriv detector‖ ≤ K (1 + log X)²`. -/
theorem exists_inghamDetector_two_horizontal_edges_critical_polylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X : ℕ}, 10 ≤ X →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
      ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
        (∀ x ∈ Icc (1 / 2 : ℝ) 4,
          inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
          ‖logDeriv (inghamDetector X) ((x : ℂ) + (T₁ : ℂ) * I)‖ ≤
            K * (1 + Real.log X) ^ 2) ∧
        (∀ x ∈ Icc (1 / 2 : ℝ) 4,
          inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
          ‖logDeriv (inghamDetector X) ((x : ℂ) + (T₂ : ℂ) * I)‖ ≤
            K * (1 + Real.log X) ^ 2) := by
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hcontrol⟩ :=
    exists_inghamDetector_horizontal_logDeriv_control_critical
  let C : ℝ := inghamDetectorHorizontalPolylogConstant Ce Qe Cj Qj
  let K : ℝ := |C|
  have hK : 0 ≤ K := abs_nonneg C
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  let tau₁ : ℝ := -(X : ℝ) + 1 / 2
  let tau₂ : ℝ := (X : ℝ) - 3 / 2
  have htau₁abs : |tau₁| = (X : ℝ) - 1 / 2 := by
    rw [abs_of_nonpos (by dsimp only [tau₁]; linarith)]
    dsimp only [tau₁]
    ring
  have htau₂abs : |tau₂| = (X : ℝ) - 3 / 2 := by
    rw [abs_of_nonneg (by dsimp only [tau₂]; linarith)]
  have htau₁lo : (X : ℝ) / 2 ≤ |tau₁| := by rw [htau₁abs]; linarith
  have htau₁hi : |tau₁| ≤ 2 * (X : ℝ) := by rw [htau₁abs]; linarith
  have htau₂lo : (X : ℝ) / 2 ≤ |tau₂| := by rw [htau₂abs]; linarith
  have htau₂hi : |tau₂| ≤ 2 * (X : ℝ) := by rw [htau₂abs]; linarith
  obtain ⟨T₁, hT₁, N₁, hN₁, hbound₁⟩ := hcontrol hX htau₁lo htau₁hi
  obtain ⟨T₂, hT₂, N₂, hN₂, hbound₂⟩ := hcontrol hX htau₂lo htau₂hi
  have hT₁' : T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1) := by
    dsimp only [tau₁] at hT₁
    constructor <;> linarith [hT₁.1, hT₁.2]
  have hT₂' : T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1) := by
    dsimp only [tau₂] at hT₂
    constructor <;> linarith [hT₂.1, hT₂.2]
  refine ⟨T₁, hT₁', T₂, hT₂', ?_, ?_⟩
  · intro x hx
    obtain ⟨hne, hraw⟩ := hbound₁ x hx
    refine ⟨hne, hraw.trans ?_⟩
    have hpoly := inghamDetectorHorizontalLogDerivBound_le_polylog
      (Ce := Ce) (Cj := Cj) (Qe := Qe) (Qj := Qj) (X := X) (N := N₁)
      hCe hCj (show 1 ≤ X by omega) hN₁
    have hCabs : C ≤ K := by dsimp only [K]; exact le_abs_self C
    have hsq : 0 ≤ (1 + Real.log X) ^ 2 := sq_nonneg _
    exact hpoly.trans (by simpa only [C] using mul_le_mul_of_nonneg_right hCabs hsq)
  · intro x hx
    obtain ⟨hne, hraw⟩ := hbound₂ x hx
    refine ⟨hne, hraw.trans ?_⟩
    have hpoly := inghamDetectorHorizontalLogDerivBound_le_polylog
      (Ce := Ce) (Cj := Cj) (Qe := Qe) (Qj := Qj) (X := X) (N := N₂)
      hCe hCj (show 1 ≤ X by omega) hN₂
    have hCabs : C ≤ K := by dsimp only [K]; exact le_abs_self C
    have hsq : 0 ≤ (1 + Real.log X) ^ 2 := sq_nonneg _
    exact hpoly.trans (by simpa only [C] using mul_le_mul_of_nonneg_right hCabs hsq)

end

end RHTower.Sieve
