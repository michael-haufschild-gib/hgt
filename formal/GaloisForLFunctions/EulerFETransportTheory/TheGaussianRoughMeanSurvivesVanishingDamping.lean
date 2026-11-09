import GaloisForLFunctions.EulerFETransportTheory.TheHeadDoesNotChangeTheInfiniteRoughMean
import GaloisForLFunctions.RHTower.WoldSieveNormalConeVonMangoldtCompletion

/-!
# The infinite rough variance survives joint height and damping limits

Gaussian damping at the observation scale admits every square-summable
arithmetic sequence. Its weighted square mass grows at most as the square root
of the height horizon. The complete rough current therefore retains its exact
diagonal variance under a smooth prime-head probe as damping vanishes.
-/

open Complex Filter Topology MeasureTheory RHTower
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Gaussian damping at the observation horizon. -/
def gaussianHeightCoeff (a : ℕ → ℂ) (T : ℝ) (n : ℕ) : ℂ :=
  a n * (Real.exp (-((n : ℝ) ^ 2 / T)) : ℂ)

/-- The entire Gaussian-damped arithmetic phase current. -/
def gaussianHeightCurrent (a : ℕ → ℂ) (T t : ℝ) : ℂ :=
  integerHeightSeries (gaussianHeightCoeff a T) t

theorem norm_gaussianHeightCoeff (a : ℕ → ℂ) (T : ℝ) (n : ℕ) :
    ‖gaussianHeightCoeff a T n‖ = ‖a n‖ * Real.exp (-((n : ℝ) ^ 2 / T)) := by
  rw [gaussianHeightCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem norm_sq_gaussianHeightCoeff (a : ℕ → ℂ) (T : ℝ) (n : ℕ) :
    ‖gaussianHeightCoeff a T n‖ ^ 2 = ‖a n‖ ^ 2 * Real.exp (-(2 * (n : ℝ) ^ 2 / T)) := by
  rw [norm_gaussianHeightCoeff, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

private theorem mul_gaussian_le_sqrt {H : ℝ} (hH : 0 < H) (n : ℕ) :
    (n : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2 / H)) ≤ Real.sqrt H := by
  let u : ℝ := n / Real.sqrt H
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hquad : u ≤ 2 * u ^ 2 + 1 := by nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg u]
  have hu : u * Real.exp (-(2 * u ^ 2)) ≤ 1 := by
    calc
      _ ≤ Real.exp (2 * u ^ 2) * Real.exp (-(2 * u ^ 2)) :=
        mul_le_mul_of_nonneg_right (hquad.trans (Real.add_one_le_exp _)) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have he : -(2 * (n : ℝ) ^ 2 / H) = -(2 * u ^ 2) := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hH.le]
    ring
  have hn : (n : ℝ) = Real.sqrt H * u := by dsimp [u]; field_simp
  calc
    _ = Real.sqrt H * (u * Real.exp (-(2 * u ^ 2))) := by rw [he, hn]; ring
    _ ≤ Real.sqrt H * 1 := mul_le_mul_of_nonneg_left hu hs.le
    _ = _ := mul_one _

/-- Every square-summable sequence is absolutely admitted at positive Gaussian
damping. The undamped sequence need not be absolutely summable. -/
theorem summable_norm_gaussianHeightCoeff {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖ ^ 2) {H : ℝ} (hH : 0 < H) :
    Summable fun n => ‖gaussianHeightCoeff a H n‖ := by
  let A : ℝ := (∑' n, ‖a n‖ ^ 2) + 1
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : ∀ n, ‖a n‖ ≤ A := by
    intro n
    have h := ha.le_tsum n (fun _ _ => sq_nonneg _)
    have hsum : 0 ≤ ∑' n, ‖a n‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    dsimp [A]
    nlinarith [sq_nonneg (‖a n‖ - 1)]
  have hgeo : Summable fun n : ℕ => Real.exp (-(n : ℝ) / H) := by
    have hneg : -1 / H < 0 := by
      have hh : 0 < 1 / H := by positivity
      simpa only [neg_div] using neg_lt_zero.mpr hh
    have h := summable_geometric_of_lt_one (Real.exp_pos (-1 / H)).le
      (Real.exp_lt_one_iff.mpr hneg)
    refine h.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine (hgeo.mul_left A).of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
  rw [norm_gaussianHeightCoeff]
  apply mul_le_mul (hA n) _ (Real.exp_pos _).le hA0
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_right hn hH.le)

/-- Gaussian damping bounds the whole weighted square mass by `√H` times the
undamped square mass. This supplies the changing-horizon error estimate. -/
theorem gaussianHeight_weightedMass_le {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖ ^ 2) {H : ℝ} (hH : 0 < H) :
    (Summable fun n : ℕ => (n : ℝ) * ‖gaussianHeightCoeff a H n‖ ^ 2) ∧
      (∑' n : ℕ, (n : ℝ) * ‖gaussianHeightCoeff a H n‖ ^ 2) ≤
        Real.sqrt H * ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hb : ∀ n : ℕ, (n : ℝ) * ‖gaussianHeightCoeff a H n‖ ^ 2 ≤
      Real.sqrt H * ‖a n‖ ^ 2 := by
    intro n
    rw [norm_sq_gaussianHeightCoeff]
    calc
      _ = ((n : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2 / H))) * ‖a n‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_gaussian_le_sqrt hH n) (sq_nonneg _)
  have hs := (ha.mul_left (Real.sqrt H)).of_nonneg_of_le (fun n => by positivity) hb
  refine ⟨hs, ?_⟩
  exact (hs.tsum_le_tsum hb (ha.mul_left (Real.sqrt H))).trans_eq tsum_mul_left

/-- The complete Gaussian square mass tends to the undamped square mass. -/
theorem tendsto_gaussianHeight_squareMass {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖ ^ 2) :
    Tendsto (fun H : ℝ => ∑' n : ℕ, ‖gaussianHeightCoeff a H n‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, ‖a n‖ ^ 2)) := by
  refine tendsto_tsum_of_dominated_convergence ha (fun n => ?_) ?_
  · simp only [norm_sq_gaussianHeightCoeff]
    have he : Tendsto (fun H : ℝ => -(2 * (n : ℝ) ^ 2 / H)) atTop (𝓝 0) := by
      have hi : Tendsto (fun H : ℝ => H⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
      simpa only [mul_zero, div_eq_mul_inv, neg_mul] using
        hi.const_mul (-(2 * (n : ℝ) ^ 2))
    simpa only [Function.comp_def, Real.exp_zero, mul_one] using
      ((Real.continuous_exp.continuousAt.tendsto).comp he).const_mul (‖a n‖ ^ 2)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_sq_gaussianHeightCoeff]
    exact mul_le_of_le_one_right (sq_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (by positivity) hH.le)))

/-- At any observation horizon, the full Gaussian rough current has an error
controlled by the square root of its damping horizon and the weighted head mass. -/
theorem abs_integral_head_mul_gaussianRough_sub_diag_le {Y : ℕ}
    (S : Finset ℕ) (w a : ℕ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers Y) (ha0 : a 0 = 0)
    (hr : ∀ n : ℕ, a n ≠ 0 → ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n)
    (ha : Summable fun n => ‖a n‖ ^ 2) {H : ℝ} (hH : 0 < H) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2 * ‖gaussianHeightCurrent a H t‖ ^ 2) -
        T * ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖gaussianHeightCoeff a H n‖ ^ 2)| ≤
      104 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) * Real.sqrt H * ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hb0 : gaussianHeightCoeff a H 0 = 0 := by simp [gaussianHeightCoeff, ha0]
  have hbr : ∀ n : ℕ, gaussianHeightCoeff a H n ≠ 0 →
      ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n := by
    intro n hn
    exact hr n (fun hz => hn (by simp [gaussianHeightCoeff, hz]))
  obtain ⟨hweighted, hb⟩ := gaussianHeight_weightedMass_le ha hH
  have h := abs_integral_head_mul_infiniteRough_sub_diag_le S w (gaussianHeightCoeff a H)
    hS hb0 hbr (summable_norm_gaussianHeightCoeff ha hH) hweighted T
  refine h.trans ?_
  calc
    _ ≤ 104 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) *
        (Real.sqrt H * ∑' n : ℕ, ‖a n‖ ^ 2) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The same damping is retained while the observation window escapes from
`[0,T]` to `[T,2T]`. Only the off-diagonal constant doubles. -/
theorem abs_integral_dyadic_head_mul_gaussianRough_sub_diag_le {Y : ℕ}
    (S : Finset ℕ) (w a : ℕ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers Y) (ha0 : a 0 = 0)
    (hr : ∀ n : ℕ, a n ≠ 0 → ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n)
    (ha : Summable fun n => ‖a n‖ ^ 2) {T : ℝ} (hT : 0 < T) :
    |(∫ t in T..(2 * T), ‖integerHeightPoly S w t‖ ^ 2 * ‖gaussianHeightCurrent a T t‖ ^ 2) -
        T * ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖gaussianHeightCoeff a T n‖ ^ 2)| ≤
      208 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) * Real.sqrt T * ∑' n : ℕ, ‖a n‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖integerHeightPoly S w t‖ ^ 2 * ‖gaussianHeightCurrent a T t‖ ^ 2
  have hc : Continuous f := by
    have h0 : gaussianHeightCoeff a T 0 = 0 := by simp [gaussianHeightCoeff, ha0]
    exact ((continuous_integerHeightPoly S w).norm.pow 2).mul
      (((PhaseSeries.continuous_phaseSeries h0 (summable_norm_gaussianHeightCoeff ha hT)).comp
        continuous_neg).norm.pow 2)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 T) (hc.intervalIntegrable T (2 * T))
  have h1 := abs_integral_head_mul_gaussianRough_sub_diag_le S w a hS ha0 hr ha hT T
  have h2 := abs_integral_head_mul_gaussianRough_sub_diag_le S w a hS ha0 hr ha hT (2 * T)
  let D : ℝ := (∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖gaussianHeightCoeff a T n‖ ^ 2
  have he : (∫ t in T..(2 * T), f t) - T * D =
      ((∫ t in (0 : ℝ)..(2 * T), f t) - (2 * T) * D) -
        ((∫ t in (0 : ℝ)..T, f t) - T * D) := by linarith
  change |(∫ t in T..(2 * T), f t) - T * D| ≤ _
  rw [he]
  have hab := abs_sub_le ((∫ t in (0 : ℝ)..(2 * T), f t) - (2 * T) * D) 0
    ((∫ t in (0 : ℝ)..T, f t) - T * D)
  simp only [sub_zero, zero_sub, abs_neg] at hab
  exact hab.trans (by dsimp [f, D] at *; linarith)

private theorem tendsto_mean_of_sqrt_bracket (I D : ℝ → ℝ) (C L : ℝ)
    (hdiag : Tendsto D atTop (𝓝 L))
    (hbound : ∀ T : ℝ, 0 < T → |I T - T * D T| ≤ C * Real.sqrt T) :
    Tendsto (fun T : ℝ => I T / T) atTop (𝓝 L) := by
  have hb : ∀ T : ℝ, 0 < T → |I T / T - D T| ≤ C / Real.sqrt T := by
    intro T hT
    have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
    have h := hbound T hT
    have he : I T / T - D T = (I T - T * D T) / T := by field_simp
    rw [he, abs_div, abs_of_pos hT]
    calc
      _ ≤ (C * Real.sqrt T) / T :=
        div_le_div_of_nonneg_right h hT.le
      _ = C / Real.sqrt T := by
        field_simp
        rw [Real.sq_sqrt hT.le]
  have hlim : Tendsto (fun T : ℝ => C / Real.sqrt T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul C
  have herr : Tendsto (fun T : ℝ => I T / T - D T) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hb T hT
  simpa only [sub_add_cancel, zero_add] using herr.add hdiag

/-- Exact diagonal variance while the observation horizon grows and Gaussian
damping vanishes at its reciprocal scale. -/
theorem tendsto_head_gaussianRough_mean {Y : ℕ}
    (S : Finset ℕ) (w a : ℕ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers Y) (ha0 : a 0 = 0)
    (hr : ∀ n : ℕ, a n ≠ 0 → ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n)
    (ha : Summable fun n => ‖a n‖ ^ 2) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T,
      ‖integerHeightPoly S w t‖ ^ 2 * ‖gaussianHeightCurrent a T t‖ ^ 2) / T)
      atTop (𝓝 ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖a n‖ ^ 2)) := by
  apply tendsto_mean_of_sqrt_bracket _
    (fun T => (∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖gaussianHeightCoeff a T n‖ ^ 2)
    (104 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) * ∑' n : ℕ, ‖a n‖ ^ 2)
  · exact (tendsto_gaussianHeight_squareMass ha).const_mul (∑ s ∈ S, ‖w s‖ ^ 2)
  · intro T hT
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      abs_integral_head_mul_gaussianRough_sub_diag_le S w a hS ha0 hr ha hT T

/-- Exact diagonal variance on an escaping height window, with damping
vanishing at that window's scale. Every rough coefficient is retained. -/
theorem tendsto_dyadic_head_gaussianRough_mean {Y : ℕ}
    (S : Finset ℕ) (w a : ℕ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers Y) (ha0 : a 0 = 0)
    (hr : ∀ n : ℕ, a n ≠ 0 → ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n)
    (ha : Summable fun n => ‖a n‖ ^ 2) :
    Tendsto (fun T : ℝ => (∫ t in T..(2 * T),
      ‖integerHeightPoly S w t‖ ^ 2 * ‖gaussianHeightCurrent a T t‖ ^ 2) / T)
      atTop (𝓝 ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖a n‖ ^ 2)) := by
  apply tendsto_mean_of_sqrt_bracket _
    (fun T => (∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖gaussianHeightCoeff a T n‖ ^ 2)
    (208 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) * ∑' n : ℕ, ‖a n‖ ^ 2)
  · exact (tendsto_gaussianHeight_squareMass ha).const_mul (∑ s ∈ S, ‖w s‖ ^ 2)
  · intro T hT
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      abs_integral_dyadic_head_mul_gaussianRough_sub_diag_le S w a hS ha0 hr ha hT

/-- The complete von Mangoldt coefficients after deleting every prime below
`Y`. Prime powers of every remaining prime are included. -/
def roughVonMangoldtCoeff (Y : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  if n ≠ 0 ∧ ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n then
    ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) else 0

theorem roughVonMangoldtCoeff_zero (Y : ℕ) (σ : ℝ) : roughVonMangoldtCoeff Y σ 0 = 0 := by
  simp [roughVonMangoldtCoeff]

theorem roughVonMangoldtCoeff_rough (Y : ℕ) (σ : ℝ) {n : ℕ}
    (hn : roughVonMangoldtCoeff Y σ n ≠ 0) : ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n := by
  by_contra h
  simp [roughVonMangoldtCoeff, h] at hn

theorem summable_sq_roughVonMangoldtCoeff (Y : ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun n => ‖roughVonMangoldtCoeff Y σ n‖ ^ 2 := by
  refine (summable_sq_woldVonMangoldtWeightedCoefficient hσ).of_nonneg_of_le
    (fun n => sq_nonneg _) fun n => ?_
  unfold roughVonMangoldtCoeff woldVonMangoldtWeightedCoefficient
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

/-- On every fixed prime-head probe, the literal infinite rough von Mangoldt
current keeps its unconditional square mass while height and damping change
together. No zero-free, AAL, or recurrence premise is required. -/
theorem tendsto_dyadic_head_gaussianVonMangoldt_mean {Y : ℕ} (S : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers Y) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun T : ℝ => (∫ t in T..(2 * T), ‖integerHeightPoly S w t‖ ^ 2 *
      ‖gaussianHeightCurrent (roughVonMangoldtCoeff Y σ) T t‖ ^ 2) / T)
      atTop (𝓝 ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖roughVonMangoldtCoeff Y σ n‖ ^ 2)) :=
  tendsto_dyadic_head_gaussianRough_mean S w (roughVonMangoldtCoeff Y σ) hS
    (roughVonMangoldtCoeff_zero Y σ) (fun _ => roughVonMangoldtCoeff_rough Y σ)
    (summable_sq_roughVonMangoldtCoeff Y hσ)

/-- The full rough variance vanishes as the prime cutoff grows. This remains
valid above every abscissa strictly greater than one half. -/
theorem tendsto_roughVonMangoldt_squareMass_zero {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun Y : ℕ => ∑' n : ℕ, ‖roughVonMangoldtCoeff Y σ n‖ ^ 2) atTop (𝓝 0) := by
  have hbase := summable_sq_woldVonMangoldtWeightedCoefficient hσ
  have hpoint : ∀ n : ℕ, Tendsto (fun Y : ℕ => ‖roughVonMangoldtCoeff Y σ n‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp only [roughVonMangoldtCoeff_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact tendsto_const_nhds
    by_cases hn1 : n = 1
    · subst n
      have hz : ∀ Y : ℕ, roughVonMangoldtCoeff Y σ 1 = 0 := by
        intro Y
        simp [roughVonMangoldtCoeff]
      simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact tendsto_const_nhds
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    have hz : ∀ᶠ Y : ℕ in atTop, ‖roughVonMangoldtCoeff Y σ n‖ ^ 2 = 0 := by
      filter_upwards [eventually_gt_atTop p] with Y hY
      have hnot : ¬ (n ≠ 0 ∧ ∀ q ∈ Nat.primesBelow Y, ¬ q ∣ n) := by
        rintro ⟨_, h⟩
        exact h p (Nat.mem_primesBelow.mpr ⟨hY, hp⟩) hpn
      simp [roughVonMangoldtCoeff, hnot]
    exact tendsto_const_nhds.congr' (hz.mono fun Y hY => hY.symm)
  have hdom : ∀ᶠ Y : ℕ in atTop, ∀ n : ℕ, ‖‖roughVonMangoldtCoeff Y σ n‖ ^ 2‖ ≤
      ‖(woldVonMangoldtWeightedCoefficient σ n : ℂ)‖ ^ 2 := by
    filter_upwards with Y n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold roughVonMangoldtCoeff woldVonMangoldtWeightedCoefficient
    split_ifs
    · exact le_rfl
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hbase hpoint hdom

#print axioms abs_integral_head_mul_gaussianRough_sub_diag_le
#print axioms tendsto_head_gaussianRough_mean
#print axioms tendsto_dyadic_head_gaussianRough_mean
#print axioms tendsto_dyadic_head_gaussianVonMangoldt_mean
#print axioms tendsto_roughVonMangoldt_squareMass_zero

end GaloisForLFunctions.EulerFETransportTheory
