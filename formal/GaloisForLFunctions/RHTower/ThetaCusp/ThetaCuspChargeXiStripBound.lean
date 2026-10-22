import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeSaddleLowerBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilZeroSeries

open Complex Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The corpus strip bound for the `ξ` source with its constant made explicit. -/
theorem norm_thetaCuspStripSource_le_explicit {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) {z : ℂ} (him : |z.im| ≤ δ) (hre : 0 ≤ z.re) :
    ‖thetaCuspStripSource z‖ ≤
      2 * Real.pi * (2 * Real.pi * thetaGaussianPowerSum (Real.pi * Real.cos (2 * δ) / 2) 4 +
        3 * thetaGaussianPowerSum (Real.pi * Real.cos (2 * δ) / 2) 2) *
        (6 * (2 / (Real.pi * Real.cos (2 * δ))) ^ (3 : ℕ)) * Real.exp (-z.re) := by
  have hδle : 2 * δ ≤ Real.pi / 2 := le_of_lt hδ4
  have hcos : 0 < Real.cos (2 * δ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  set c : ℝ := Real.pi * Real.cos (2 * δ) with hc
  have hcpos : 0 < c := by positivity
  have hchalf : 0 < c / 2 := by linarith
  set S4 : ℝ := thetaGaussianPowerSum (c / 2) 4 with hS4
  set S2 : ℝ := thetaGaussianPowerSum (c / 2) 2 with hS2
  have hS4nn : 0 ≤ S4 := thetaGaussianPowerSum_nonneg _ 4
  have hS2nn : 0 ≤ S2 := thetaGaussianPowerSum_nonneg _ 2
  set x : ℝ := z.re with hx
  have hex : (1 : ℝ) ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  set K1 : ℝ := Real.exp (x / 2) * (2 * Real.pi) * (2 * Real.pi * Real.exp (4 * x)) *
    Real.exp (-(c / 2) * Real.exp (2 * x)) with hK1
  set K2 : ℝ := Real.exp (x / 2) * (2 * Real.pi) * (3 * Real.exp (2 * x)) *
    Real.exp (-(c / 2) * Real.exp (2 * x)) with hK2
  set maj : ℕ → ℝ := fun n =>
    K1 * ((n : ℝ) ^ (4 : ℕ) * Real.exp (-(c / 2) * (n : ℝ) ^ (2 : ℕ))) +
    K2 * ((n : ℝ) ^ (2 : ℕ) * Real.exp (-(c / 2) * (n : ℝ) ^ (2 : ℕ))) with hmaj
  have hsum4 := summable_pow_mul_exp_neg_nat_sq 4 hchalf
  have hsum2 := summable_pow_mul_exp_neg_nat_sq 2 hchalf
  have hsummaj : Summable maj := (hsum4.mul_left K1).add (hsum2.mul_left K2)
  -- termwise domination
  have hdom : ∀ n : ℕ, ‖thetaCuspComplexTerm z n‖ ≤ maj n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [thetaCuspComplexTerm_zero, norm_zero, hmaj]
      simp only
      positivity
    · refine le_trans (norm_thetaCuspComplexTerm_le_pointwise hδle him n) ?_
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hsplit : Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x)) ≤
          Real.exp (-(c / 2) * Real.exp (2 * x)) * Real.exp (-(c / 2) * (n : ℝ) ^ (2 : ℕ)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by nlinarith
        have hbase : (0 : ℝ) ≤
            (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x) - Real.exp (2 * x) / 2 - (n : ℝ) ^ (2 : ℕ) / 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hex)
            (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) - 1 / 2), hn2]
        have hkey : c / 2 * Real.exp (2 * x) + c / 2 * (n : ℝ) ^ (2 : ℕ) ≤
            c * (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x) := by
          nlinarith [mul_nonneg hcpos.le hbase]
        rw [← hc]
        linarith [hkey]
      have hposfac : (0 : ℝ) ≤ Real.exp (x / 2) * (2 * Real.pi) *
          (2 * Real.pi * (n : ℝ) ^ (4 : ℕ) * Real.exp (4 * x) +
            3 * (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x)) := by positivity
      calc Real.exp (x / 2) * (2 * Real.pi) *
            (2 * Real.pi * (n : ℝ) ^ (4 : ℕ) * Real.exp (4 * x) +
              3 * (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x)) *
            Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x))
          ≤ Real.exp (x / 2) * (2 * Real.pi) *
              (2 * Real.pi * (n : ℝ) ^ (4 : ℕ) * Real.exp (4 * x) +
                3 * (n : ℝ) ^ (2 : ℕ) * Real.exp (2 * x)) *
              (Real.exp (-(c / 2) * Real.exp (2 * x)) *
                Real.exp (-(c / 2) * (n : ℝ) ^ (2 : ℕ))) :=
            mul_le_mul_of_nonneg_left hsplit hposfac
        _ = maj n := by rw [hmaj, hK1, hK2]; ring
  have hnormsummable : Summable (fun n : ℕ => ‖thetaCuspComplexTerm z n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdom hsummaj
  have hbound : ‖thetaCuspStripSource z‖ ≤ ∑' n : ℕ, maj n := by
    refine le_trans (norm_tsum_le_tsum_norm hnormsummable) ?_
    exact hnormsummable.tsum_le_tsum hdom hsummaj
  have hmajsum : (∑' n : ℕ, maj n) = K1 * S4 + K2 * S2 := by
    rw [hmaj]
    rw [(hsum4.mul_left K1).tsum_add (hsum2.mul_left K2), hsum4.tsum_mul_left,
      hsum2.tsum_mul_left, hS4, hS2, thetaGaussianPowerSum, thetaGaussianPowerSum]
  -- the double-exponential factor beats every power
  have hexpbound : Real.exp (-(c / 2) * Real.exp (2 * x)) ≤ 6 * (2 / c) ^ (3 : ℕ) * Real.exp (-(6 * x)) := by
    have hs : (0 : ℝ) < c / 2 * Real.exp (2 * x) := by positivity
    have hpow := Real.pow_div_factorial_le_exp (c / 2 * Real.exp (2 * x)) hs.le 3
    have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
    rw [hfac] at hpow
    have hcube : (c / 2 * Real.exp (2 * x)) ^ (3 : ℕ) = (c / 2) ^ (3 : ℕ) * Real.exp (6 * x) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [hcube] at hpow
    have hinv : Real.exp (-(c / 2 * Real.exp (2 * x))) =
        (Real.exp (c / 2 * Real.exp (2 * x)))⁻¹ := by
      rw [Real.exp_neg]
    have hkey : Real.exp (-(c / 2) * Real.exp (2 * x)) =
        (Real.exp (c / 2 * Real.exp (2 * x)))⁻¹ := by
      rw [← hinv]
      congr 1
      ring
    rw [hkey]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have hposc : (0 : ℝ) < (c / 2) ^ (3 : ℕ) * Real.exp (6 * x) := by positivity
    have h1 : (c / 2) ^ (3 : ℕ) * Real.exp (6 * x) / 6 ≤ Real.exp (c / 2 * Real.exp (2 * x)) := hpow
    have hrw : 6 * (2 / c) ^ (3 : ℕ) * Real.exp (-(6 * x)) * Real.exp (c / 2 * Real.exp (2 * x)) =
        (6 * (2 / c) ^ (3 : ℕ) * Real.exp (-(6 * x))) * Real.exp (c / 2 * Real.exp (2 * x)) := by ring
    rw [hrw]
    have hfrac : (6 : ℝ) * (2 / c) ^ (3 : ℕ) * Real.exp (-(6 * x)) * ((c / 2) ^ (3 : ℕ) * Real.exp (6 * x) / 6)
        = 1 := by
      field_simp
      rw [← Real.exp_add]
      norm_num
    nlinarith [h1, hfrac, Real.exp_pos (-(6 * x)), Real.exp_pos (6 * x)]
  refine le_trans hbound ?_
  rw [hmajsum, hK1, hK2]
  have hrw : Real.exp (x / 2) * (2 * Real.pi) * (2 * Real.pi * Real.exp (4 * x)) *
        Real.exp (-(c / 2) * Real.exp (2 * x)) * S4 +
      Real.exp (x / 2) * (2 * Real.pi) * (3 * Real.exp (2 * x)) *
        Real.exp (-(c / 2) * Real.exp (2 * x)) * S2 =
      (2 * Real.pi) * Real.exp (-(c / 2) * Real.exp (2 * x)) *
        (2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) + 3 * S2 * Real.exp (x / 2 + 2 * x)) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hrw]
  have hfacnn : (0 : ℝ) ≤ 2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) +
      3 * S2 * Real.exp (x / 2 + 2 * x) := by positivity
  calc (2 * Real.pi) * Real.exp (-(c / 2) * Real.exp (2 * x)) *
        (2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) + 3 * S2 * Real.exp (x / 2 + 2 * x))
      ≤ (2 * Real.pi) * (6 * (2 / c) ^ (3 : ℕ) * Real.exp (-(6 * x))) *
        (2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) + 3 * S2 * Real.exp (x / 2 + 2 * x)) := by
        have := mul_le_mul_of_nonneg_left hexpbound (by positivity : (0:ℝ) ≤ 2 * Real.pi)
        exact mul_le_mul_of_nonneg_right this hfacnn
    _ = 2 * Real.pi * (6 * (2 / c) ^ (3 : ℕ)) *
        (2 * Real.pi * S4 * Real.exp (-(3 * x / 2)) + 3 * S2 * Real.exp (-(7 * x / 2))) := by
        have h1 : Real.exp (-(6 * x)) * Real.exp (x / 2 + 4 * x) = Real.exp (-(3 * x / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have h2 : Real.exp (-(6 * x)) * Real.exp (x / 2 + 2 * x) = Real.exp (-(7 * x / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        linear_combination (2 * Real.pi * (6 * (2 / c) ^ (3 : ℕ)) * (2 * Real.pi * S4)) * h1 +
          (2 * Real.pi * (6 * (2 / c) ^ (3 : ℕ)) * (3 * S2)) * h2
    _ ≤ 2 * Real.pi * (2 * Real.pi * S4 + 3 * S2) * (6 * (2 / c) ^ (3 : ℕ)) * Real.exp (-x) := by
        have e1 : Real.exp (-(3 * x / 2)) ≤ Real.exp (-x) :=
          Real.exp_le_exp.mpr (by linarith)
        have e2 : Real.exp (-(7 * x / 2)) ≤ Real.exp (-x) :=
          Real.exp_le_exp.mpr (by linarith)
        have hA : (0 : ℝ) ≤ 2 * Real.pi * (6 * (2 / c) ^ (3 : ℕ)) := by positivity
        have p1 : (0 : ℝ) ≤ 2 * Real.pi * S4 * (Real.exp (-x) - Real.exp (-(3 * x / 2))) :=
          mul_nonneg (mul_nonneg (by positivity) hS4nn) (by linarith)
        have p2 : (0 : ℝ) ≤ 3 * S2 * (Real.exp (-x) - Real.exp (-(7 * x / 2))) :=
          mul_nonneg (by positivity) (by linarith)
        nlinarith [mul_nonneg hA p1, mul_nonneg hA p2]



/-- The explicit strip constant. -/
def xiStripConst (δ : ℝ) : ℝ :=
  2 * Real.pi * (2 * Real.pi * thetaGaussianPowerSum (Real.pi * Real.cos (2 * δ) / 2) 4 +
    3 * thetaGaussianPowerSum (Real.pi * Real.cos (2 * δ) / 2) 2) *
    (6 * (2 / (Real.pi * Real.cos (2 * δ))) ^ (3 : ℕ))

theorem norm_thetaCuspStripSource_le_abs {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    {z : ℂ} (him : |z.im| ≤ δ) :
    ‖thetaCuspStripSource z‖ ≤ xiStripConst δ * Real.exp (-|z.re|) := by
  rcases le_or_gt 0 z.re with hre | hre
  · rw [abs_of_nonneg hre]; exact norm_thetaCuspStripSource_le_explicit hδ0 hδ4 him hre
  · have hmem : z ∈ thetaCuspStrip := by
      show |z.im| < Real.pi / 4; linarith
    rw [← thetaCuspStripSource_neg hmem, abs_of_neg hre]
    have him' : |(-z).im| ≤ δ := by rw [Complex.neg_im, abs_neg]; exact him
    have := norm_thetaCuspStripSource_le_explicit hδ0 hδ4 him' (by rw [Complex.neg_re]; linarith)
    rwa [Complex.neg_re] at this

theorem xiStripConst_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    0 ≤ xiStripConst δ := by
  have hcos : 0 < Real.cos (2 * δ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  unfold xiStripConst
  have := thetaGaussianPowerSum_nonneg (Real.pi * Real.cos (2 * δ) / 2) 4
  have := thetaGaussianPowerSum_nonneg (Real.pi * Real.cos (2 * δ) / 2) 2
  positivity

/-- **Sharp strip decay of `ξ` along the real axis with explicit constant.** -/
theorem norm_XiC_ofReal_le_strip {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) (u : ℝ) :
    ‖XiC (u : ℂ)‖ ≤ Real.exp (-(u * δ)) * (2 * xiStripConst δ) := by
  have hv : |δ| ≤ δ := by rw [abs_of_nonneg hδ0]
  have h1 : XiC (u : ℂ) = ∫ x : ℝ, thetaStripFourierIntegrand (-u) ((x : ℂ) + (δ : ℂ) * Complex.I) := by
    rw [integral_thetaStripFourierIntegrand_shift hδ0 hδ4 hv hδ0 (-u),
      integral_thetaStripFourierIntegrand_zero_height, ← XiC_neg]
    push_cast; ring_nf
  rw [h1]
  have hC := xiStripConst_nonneg hδ0 hδ4
  have hmaj : Integrable (fun x : ℝ => Real.exp (-(u * δ)) * (xiStripConst δ * Real.exp (-(1 * |x|)))) :=
    ((integrable_exp_neg_mul_abs' one_pos).const_mul _).const_mul _
  calc ‖∫ x : ℝ, thetaStripFourierIntegrand (-u) ((x : ℂ) + (δ : ℂ) * Complex.I)‖
      ≤ ∫ x : ℝ, ‖thetaStripFourierIntegrand (-u) ((x : ℂ) + (δ : ℂ) * Complex.I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, Real.exp (-(u * δ)) * (xiStripConst δ * Real.exp (-(1 * |x|))) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hmaj
        refine Filter.Eventually.of_forall fun x => ?_
        show ‖thetaStripFourierIntegrand (-u) ((x : ℂ) + (δ : ℂ) * Complex.I)‖ ≤
          Real.exp (-(u * δ)) * (xiStripConst δ * Real.exp (-(1 * |x|)))
        rw [norm_thetaStripFourierIntegrand]
        have him : ((x : ℂ) + (δ : ℂ) * Complex.I).im = δ := by simp
        have hre : ((x : ℂ) + (δ : ℂ) * Complex.I).re = x := by simp
        have hb := norm_thetaCuspStripSource_le_abs hδ0 hδ4 (z := (x : ℂ) + (δ : ℂ) * Complex.I)
          (by rw [him, abs_of_nonneg hδ0])
        rw [hre] at hb
        rw [him, one_mul, show -u * δ = -(u * δ) by ring]
        exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Real.exp (-(u * δ)) * (2 * xiStripConst δ) := by
        rw [integral_const_mul, integral_const_mul, integral_exp_neg_mul_abs_eq one_pos]; ring

/-- **Gaussian power sums are polynomial in the inverse rate.** -/
theorem thetaGaussianPowerSum_le {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    thetaGaussianPowerSum γ k ≤ 3 * (k.factorial : ℝ) * 2 ^ k / γ ^ (k + 1) := by
  set r : ℝ := Real.exp (-(γ / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  set g : ℕ → ℝ := fun n => (k.factorial : ℝ) * (2 / γ) ^ k * r ^ n with hg
  have hgs : Summable g := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hfs := summable_pow_mul_exp_neg_nat_sq k hγ
  have hdom : ∀ n : ℕ, (n : ℝ) ^ k * Real.exp (-γ * (n : ℝ) ^ (2 : ℕ)) ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hg, Nat.cast_zero, zero_pow (by omega : k ≠ 0), zero_mul, pow_zero, mul_one]
      positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow := Real.pow_div_factorial_le_exp (γ * n / 2) (by positivity) k
      have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
      have h1 : (n : ℝ) ^ k ≤ (k.factorial : ℝ) * (2 / γ) ^ k * Real.exp (γ * n / 2) := by
        rw [div_le_iff₀ hfac] at hpow
        have e : (γ * n / 2) ^ k = (γ / 2) ^ k * (n : ℝ) ^ k := by ring
        rw [e] at hpow
        have hγk : 0 < (γ / 2) ^ k := by positivity
        have e2 : (2 / γ) ^ k * (γ / 2) ^ k = 1 := by
          rw [← mul_pow]; field_simp; simp
        calc (n : ℝ) ^ k = (2 / γ) ^ k * ((γ / 2) ^ k * (n : ℝ) ^ k) := by
              rw [← mul_assoc, e2, one_mul]
          _ ≤ (2 / γ) ^ k * (Real.exp (γ * n / 2) * k.factorial) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = (k.factorial : ℝ) * (2 / γ) ^ k * Real.exp (γ * n / 2) := by ring
      have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have h2 : Real.exp (-γ * (n : ℝ) ^ (2 : ℕ)) ≤ Real.exp (-(γ * n)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hnn hγ.le])
      have h3 : Real.exp (γ * n / 2) * Real.exp (-(γ * n)) = r ^ n := by
        rw [← Real.exp_add, hr, ← Real.exp_nat_mul]; congr 1; ring
      calc (n : ℝ) ^ k * Real.exp (-γ * (n : ℝ) ^ (2 : ℕ))
          ≤ (k.factorial : ℝ) * (2 / γ) ^ k * Real.exp (γ * n / 2) * Real.exp (-(γ * n)) :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
        _ = g n := by rw [hg]; simp only; rw [mul_assoc, h3]
  have hle : thetaGaussianPowerSum γ k ≤ ∑' n, g n := by
    unfold thetaGaussianPowerSum
    exact hfs.tsum_le_tsum hdom hgs
  have hsum : ∑' n, g n = (k.factorial : ℝ) * (2 / γ) ^ k / (1 - r) := by
    rw [hg, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; ring
  have hgeo : 1 / (1 - r) ≤ 3 / γ := by
    have he : r * (1 + γ / 2) ≤ 1 := by
      have := Real.add_one_le_exp (γ / 2)
      have h4 : r * Real.exp (γ / 2) = 1 := by rw [hr, ← Real.exp_add]; simp
      nlinarith
    rw [div_le_div_iff₀ (by linarith) hγ]
    nlinarith
  rw [hsum] at hle
  refine le_trans hle ?_
  have hfac : (0 : ℝ) ≤ k.factorial := by positivity
  calc (k.factorial : ℝ) * (2 / γ) ^ k / (1 - r) = (k.factorial : ℝ) * (2 / γ) ^ k * (1 / (1 - r)) := by
        ring
    _ ≤ (k.factorial : ℝ) * (2 / γ) ^ k * (3 / γ) := by gcongr
    _ = 3 * (k.factorial : ℝ) * 2 ^ k / γ ^ (k + 1) := by
        rw [div_pow]; field_simp; ring

end RHTower
