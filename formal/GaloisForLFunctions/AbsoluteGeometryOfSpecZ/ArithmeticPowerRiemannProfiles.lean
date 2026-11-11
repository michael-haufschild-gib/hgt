import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerDominatedRiemannProfiles

/-!
# Arithmetic staircases in power-tail coordinates

Above any positive cutoff, a summatory arithmetic function at `1/t`
is a finite sum of interval indicators. Its power-weighted mesh converges
whenever cancellation gives an integrable power envelope.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- A power weight times an arithmetic summatory function in inverse coordinates. -/
def arithmeticPowerProfile (p : ℝ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  t ^ (-p) * ∑ n ∈ Icc 1 ⌊1 / t⌋₊, f n

theorem measurable_arithmeticPowerProfile (p : ℝ) (f : ℕ → ℝ) :
    Measurable (arithmeticPowerProfile p f) :=
  (measurable_id.pow_const (-p)).mul
    (measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_const.div measurable_id)))

/-- Holding a negative power constant below a positive cutoff gives a bounded
nonnegative antitone profile. -/
theorem riemannOn_clipped_rpow {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ) :
    RiemannOn (fun t : ℝ => (max δ t) ^ (-p)) := by
  apply riemannOn_of_continuousOn_of_bounded (B := δ ^ (-p))
  · intro t _
    exact ((continuousAt_const.max continuousAt_id).rpow_const
      (Or.inl (ne_of_gt (hδ.trans_le (le_max_left _ _))))).continuousWithinAt
  · intro t _
    rw [abs_of_nonneg (Real.rpow_nonneg (hδ.le.trans (le_max_left _ _)) _)]
    exact Real.rpow_le_rpow_of_nonpos hδ (le_max_left _ _) (neg_nonpos.mpr hp)

theorem antitoneOn_clipped_rpow {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ) :
    AntitoneOn (fun t : ℝ => (max δ t) ^ (-p)) (Set.Ioc 0 1) := by
  intro s _ t _ hst
  exact Real.rpow_le_rpow_of_nonpos (hδ.trans_le (le_max_left _ _))
    (max_le_max_left δ hst) (neg_nonpos.mpr hp)

/-- A negative power on a compact subinterval has convergent meshes even when
the endpoints of that subinterval are jumps. -/
theorem riemannOn_rpow_interval {p δ c : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ)
    (hδc : δ ≤ c) :
    RiemannOn (fun t : ℝ => if δ < t ∧ t ≤ c then t ^ (-p) else 0) := by
  let h := fun t : ℝ => (max δ t) ^ (-p)
  have hi := (riemannOn_clipped_rpow hp hδ).1
  have hc (b : ℝ) : RiemannOn ((Set.Iic b).indicator h) :=
    riemannOn_indicator_Iic (antitoneOn_clipped_rpow hp hδ)
      (fun t _ => Real.rpow_nonneg (hδ.le.trans (le_max_left _ _)) _) hi b
  refine ((hc c).sub (hc δ)).congr fun t _ => ?_
  by_cases htδ : t ≤ δ
  · rw [Set.indicator_of_mem (htδ.trans hδc), Set.indicator_of_mem htδ,
      sub_self, if_neg (fun h => (not_lt.mpr htδ) h.1)]
  · have hδt := lt_of_not_ge htδ
    rw [Set.indicator_of_notMem htδ, sub_zero]
    by_cases htc : t ≤ c
    · rw [Set.indicator_of_mem htc, if_pos ⟨hδt, htc⟩]
      dsimp only [h]
      rw [max_eq_right hδt.le]
    · rw [Set.indicator_of_notMem htc, if_neg (fun h => htc h.2)]

/-- Above a positive cutoff, the inverse staircase sees finitely many terms. -/
theorem sum_inverse_floor_eq {f : ℕ → ℝ} {δ t : ℝ}
    (hδ : 0 < δ) (ht : δ < t) :
    (∑ n ∈ Icc 1 ⌊1 / t⌋₊, f n) =
      ∑ n ∈ Icc 1 ⌊1 / δ⌋₊, if t ≤ 1 / (n : ℝ) then f n else 0 := by
  have ht0 := hδ.trans ht
  have hfloor : ⌊1 / t⌋₊ ≤ ⌊1 / δ⌋₊ :=
    Nat.floor_mono (one_div_le_one_div_of_le hδ ht.le)
  have hfilter : (Icc 1 ⌊1 / δ⌋₊).filter (fun n : ℕ => t ≤ 1 / (n : ℝ)) =
      Icc 1 ⌊1 / t⌋₊ := by
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hn1, _⟩, hn⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      exact ⟨hn1, (Nat.le_floor_iff (by positivity)).mpr ((le_one_div ht0 hn0).mp hn)⟩
    · rintro ⟨hn1, hn⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      exact ⟨⟨hn1, hn.trans hfloor⟩,
        (le_one_div ht0 hn0).mpr ((Nat.le_floor_iff (by positivity)).mp hn)⟩
  rw [← sum_filter, hfilter]

/-- Every positive cutoff of an arithmetic power profile is Riemann integrable
with convergent meshes, independently of cancellation in the coefficients. -/
theorem riemannOn_cut_arithmeticPowerProfile {p δ : ℝ} (hp : 0 ≤ p)
    (hδ : 0 < δ) (f : ℕ → ℝ) :
    RiemannOn ((Set.Ioi δ).indicator (arithmeticPowerProfile p f)) := by
  have hs := riemannOn_sum (Icc 1 ⌊1 / δ⌋₊)
    (fun n t => f n * (if δ < t ∧ t ≤ 1 / (n : ℝ) then t ^ (-p) else 0))
    (fun n hn => (riemannOn_rpow_interval hp hδ (by
      have hn1 := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      exact (le_one_div hδ hn0).mpr
        ((Nat.le_floor_iff (by positivity)).mp (mem_Icc.mp hn).2))).const_mul (f n))
  refine hs.congr fun t _ => ?_
  by_cases ht : δ < t
  · rw [Set.indicator_of_mem ht, arithmeticPowerProfile, sum_inverse_floor_eq hδ ht, mul_sum]
    apply sum_congr rfl
    intro n _
    by_cases hn : t ≤ 1 / (n : ℝ)
    · rw [if_pos ⟨ht, hn⟩, if_pos hn, mul_comm]
    · rw [if_neg (fun h => hn h.2), if_neg hn, mul_zero, mul_zero]
  · rw [Set.indicator_of_notMem ht]
    exact sum_eq_zero fun n _ => by rw [if_neg (fun h => ht h.1), mul_zero]

/-- Cancellation of order `x^β` makes the inverse staircase integrable against
`t⁻ᵖ` precisely when `p+β<1`. -/
theorem riemannOn_arithmeticPowerProfile {p β C : ℝ} {f : ℕ → ℝ}
    (hp : 0 ≤ p) (hβ : 0 ≤ β) (hpos : 0 < p + β) (hsub : p + β < 1)
    (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, |∑ n ∈ Icc 1 N, f n| ≤ C * (N : ℝ) ^ β) :
    RiemannOn (arithmeticPowerProfile p f) := by
  apply riemannOn_of_powerBound_and_cuts hpos hsub
    (measurable_arithmeticPowerProfile p f)
  · intro t ht
    rw [arithmeticPowerProfile, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    have hfloor : (⌊1 / t⌋₊ : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
    calc
      _ ≤ t ^ (-p) * (C * (⌊1 / t⌋₊ : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left (hbound _) (Real.rpow_nonneg ht.1.le _)
      _ ≤ t ^ (-p) * (C * (1 / t) ^ β) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor hβ) hC)
          (Real.rpow_nonneg ht.1.le _)
      _ = C * t ^ (-(p + β)) := by
        rw [Real.div_rpow zero_le_one ht.1.le, Real.one_rpow, one_div,
          ← Real.rpow_neg ht.1.le]
        calc
          _ = C * (t ^ (-p) * t ^ (-β)) := by ring
          _ = _ := by rw [← Real.rpow_add ht.1, ← neg_add]
  · intro δ hδ _
    exact riemannOn_cut_arithmeticPowerProfile hp hδ f

/-- Inverse coordinates turn a power-weighted mesh into a hyperbola sum. -/
theorem tailRiemannSum_inverse_power_eq (p : ℝ) (f : ℝ → ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    tailRiemannSum (fun t => t ^ (-p) * f (1 / t)) N =
      (N : ℝ) ^ (p - 1) * ∑ m ∈ Icc 1 N,
        powerTailWeight p m * f ((N : ℝ) / m) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tailRiemannSum, sum_div, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have hscale : ((m : ℝ) / N) ^ (-p) = powerTailWeight p m * (N : ℝ) ^ p := by
    rw [Real.div_rpow hm0.le hNp.le, Real.rpow_neg hNp.le,
      div_eq_mul_inv, inv_inv]
    rfl
  dsimp only
  rw [one_div_div, hscale, Real.rpow_sub hNp, Real.rpow_one]
  ring

/-- The arithmetic power profile is exactly the normalized hyperbola sum. -/
theorem tailRiemannSum_arithmeticPowerProfile_eq (p : ℝ) (f : ℕ → ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    tailRiemannSum (arithmeticPowerProfile p f) N =
      (N : ℝ) ^ (p - 1) * ∑ m ∈ Icc 1 N,
        powerTailWeight p m * ∑ n ∈ Icc 1 (N / m), f n := by
  have h := tailRiemannSum_inverse_power_eq p
    (fun x => ∑ n ∈ Icc 1 ⌊x⌋₊, f n) hN
  simpa only [arithmeticPowerProfile, Nat.floor_div_eq_div] using h

/-- A normalized arithmetic convolution converges to its summatory Mellin
integral once the source cancellation exponent is below the pole exponent. -/
theorem tendsto_normalized_power_convolution {p β C : ℝ} {f : ArithmeticFunction ℝ}
    (hp : 0 ≤ p) (hβ : 0 ≤ β) (hpos : 0 < p + β) (hsub : p + β < 1)
    (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, |∑ n ∈ Icc 1 N, f n| ≤ C * (N : ℝ) ^ β) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (p - 1) *
      ∑ n ∈ Icc 1 N, (powerTailZeta p * f) n) atTop
      (𝓝 (∫ t in Set.Ioc (0 : ℝ) 1, arithmeticPowerProfile p f t)) := by
  have h := (riemannOn_arithmeticPowerProfile hp hβ hpos hsub hC hbound).2
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [tailRiemannSum_arithmeticPowerProfile_eq p f hN, RHTower.sum_Icc_mul_apply]
  congr 1
  apply sum_congr rfl
  intro m hm
  rw [powerTailZeta_apply (by have := (mem_Icc.mp hm).1; omega)]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
