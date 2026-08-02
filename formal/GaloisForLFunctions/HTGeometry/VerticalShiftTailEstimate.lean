import GaloisForLFunctions.HTGeometry.TrigammaLeadingAsymptotic

/-!
# Telescoping gain along a vertical line

A function whose unit-shift defect decays like `‖z‖^{-p}` and whose forward translates vanish is
itself the negative sum of its defects along the shift orbit.  On a vertical line the sum of
`‖(σ+n)+it‖^{-p}` over `n` is `O(t^{1-p})`: the terms with `σ+n ≤ t` are each at most `t^{-p}` and
there are `O(t)` of them, while the terms beyond that are dominated by the telescoping majorant.

So a defect of order `p` yields a function of order `p-1`, which is the induction step that turns
the digamma difference equation into an asymptotic expansion of any prescribed order.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ : ℝ}

/-- The shifted inverse squares are summable. -/
theorem summable_inv_sq_shift (hσ : 0 < σ) :
    Summable (fun n : ℕ => 1 / (σ + n) ^ 2) := by
  have hmaj : Summable (fun n : ℕ => 1 / ((σ + n) * (σ + n + 1))) :=
    (hasSum_one_div_shift_mul_succ hσ).summable
  have hshift : Summable (fun n : ℕ => 1 / (σ + ((n + 1 : ℕ) : ℝ)) ^ 2) := by
    refine hmaj.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · have hpos : (0 : ℝ) < σ + ((n + 1 : ℕ) : ℝ) := by positivity
      positivity
    · have hpos : (0 : ℝ) < σ + (n : ℝ) := by positivity
      have hpos' : (0 : ℝ) < σ + ((n + 1 : ℕ) : ℝ) := by positivity
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith
  exact (summable_nat_add_iff 1).mp hshift

/-- The shifted inverse squares on a vertical line are summable. -/
theorem summable_inv_sq_vertical (hσ : 0 < σ) (t : ℝ) :
    Summable (fun n : ℕ => 1 / ((σ + n) ^ 2 + t ^ 2)) := by
  refine (summable_inv_sq_shift hσ).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · have hpos : (0 : ℝ) < σ + n := by positivity
    positivity
  · have hpos : (0 : ℝ) < σ + n := by positivity
    have hden : (0 : ℝ) < (σ + n) ^ 2 + t ^ 2 := by nlinarith
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith [sq_nonneg t]

/-- **The shifted inverse-square sum on a vertical line decays like `1/t`.** -/
theorem tsum_inv_sq_vertical_le (hσ : 0 < σ) {t : ℝ} (ht : 2 ≤ t) :
    ∑' n : ℕ, 1 / ((σ + n) ^ 2 + t ^ 2) ≤ 4 / t := by
  have htpos : (0 : ℝ) < t := by linarith
  set N : ℕ := ⌈t⌉₊ with hN
  have hNt : (t : ℝ) ≤ N := Nat.le_ceil t
  have hNle : (N : ℝ) ≤ t + 1 := by
    have := Nat.ceil_lt_add_one (le_of_lt htpos)
    linarith
  have hsum := summable_inv_sq_vertical hσ t
  rw [← hsum.sum_add_tsum_nat_add N]
  have hhead : ∑ n ∈ Finset.range N, 1 / ((σ + n) ^ 2 + t ^ 2) ≤ 2 / t := by
    have hterm : ∀ n ∈ Finset.range N, 1 / ((σ + (n : ℝ)) ^ 2 + t ^ 2) ≤ 1 / t ^ 2 := by
      intro n _
      have hpos : (0 : ℝ) < σ + n := by positivity
      have hden : (0 : ℝ) < (σ + n) ^ 2 + t ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
    calc ∑ n ∈ Finset.range N, 1 / ((σ + (n : ℝ)) ^ 2 + t ^ 2)
        ≤ ∑ _n ∈ Finset.range N, 1 / t ^ 2 := Finset.sum_le_sum hterm
      _ = (N : ℝ) * (1 / t ^ 2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (t + 1) * (1 / t ^ 2) := by
          have : (0 : ℝ) < 1 / t ^ 2 := by positivity
          nlinarith
      _ ≤ 2 / t := by
          rw [show (t + 1) * (1 / t ^ 2) = (t + 1) / t ^ 2 by ring,
            div_le_div_iff₀ (by positivity : (0 : ℝ) < t ^ 2) htpos]
          nlinarith
  have htail : ∑' n : ℕ, 1 / ((σ + ((n + N : ℕ) : ℝ)) ^ 2 + t ^ 2) ≤ 2 / t := by
    set τ : ℝ := σ + (N : ℝ) - 1 with hτ
    have hτpos : (0 : ℝ) < τ := by
      have : (1 : ℝ) ≤ N := by
        have : (1 : ℝ) ≤ t := by linarith
        linarith
      rw [hτ]
      linarith
    have hmaj := hasSum_one_div_shift_mul_succ hτpos
    have hle : ∀ n : ℕ, 1 / ((σ + ((n + N : ℕ) : ℝ)) ^ 2 + t ^ 2)
        ≤ 1 / ((τ + n) * (τ + n + 1)) := by
      intro n
      have hpos : (0 : ℝ) < τ + n := by positivity
      have hden : (0 : ℝ) < (σ + ((n + N : ℕ) : ℝ)) ^ 2 + t ^ 2 := by
        have : (0 : ℝ) < σ + ((n + N : ℕ) : ℝ) := by positivity
        nlinarith
      rw [div_le_div_iff₀ hden (by positivity)]
      have hcast : (σ + ((n + N : ℕ) : ℝ)) = τ + n + 1 := by
        rw [hτ]
        push_cast
        ring
      rw [hcast]
      nlinarith [sq_nonneg t, hpos]
    have hsummable : Summable (fun n : ℕ => 1 / ((σ + ((n + N : ℕ) : ℝ)) ^ 2 + t ^ 2)) := by
      have := (summable_inv_sq_vertical hσ t).comp_injective
        (add_left_injective N)
      exact hmaj.summable.of_nonneg_of_le (fun n => by
        have : (0 : ℝ) < σ + ((n + N : ℕ) : ℝ) := by positivity
        positivity) hle
    calc ∑' n : ℕ, 1 / ((σ + ((n + N : ℕ) : ℝ)) ^ 2 + t ^ 2)
        ≤ ∑' n : ℕ, 1 / ((τ + n) * (τ + n + 1)) :=
          hsummable.tsum_le_tsum hle hmaj.summable
      _ = 1 / τ := hmaj.tsum_eq
      _ ≤ 2 / t := by
          have hτt : t - 1 ≤ τ := by
            rw [hτ]
            linarith
          have ht2 : t / 2 ≤ t - 1 := by linarith
          have hτhalf : t / 2 ≤ τ := le_trans ht2 hτt
          rw [div_le_div_iff₀ hτpos htpos]
          nlinarith
  have hcast : ∀ n : ℕ, (σ + ((n + N : ℕ) : ℝ)) ^ 2 + t ^ 2
      = (σ + ((n : ℝ) + (N : ℝ))) ^ 2 + t ^ 2 := by
    intro n
    push_cast
    ring
  calc (∑ n ∈ Finset.range N, 1 / ((σ + (n : ℝ)) ^ 2 + t ^ 2))
        + ∑' n : ℕ, 1 / ((σ + ((n + N : ℕ) : ℝ)) ^ 2 + t ^ 2)
      ≤ 2 / t + 2 / t := add_le_add hhead htail
    _ = 4 / t := by ring


/-- The square of the modulus on a shifted vertical point. -/
theorem norm_sq_vertical_add_nat (t : ℝ) (n : ℕ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2 = (σ + n) ^ 2 + t ^ 2 := by
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).im = t := by simp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  ring

/-- A power of the modulus at least two splits off the height. -/
theorem pow_norm_vertical_add_nat_ge (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) {p : ℕ} (hp : 2 ≤ p)
    (n : ℕ) :
    t ^ (p - 2) * ((σ + n) ^ 2 + t ^ 2)
      ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ p := by
  have hge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := norm_vertical_add_nat_ge_im t n
  have hsplit : ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ p
      = ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (p - 2)
        * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, norm_sq_vertical_add_nat]
  have hfac : t ^ (p - 2) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (p - 2) :=
    pow_le_pow_left₀ (le_of_lt ht) hge _
  have hpos : (0 : ℝ) ≤ (σ + n) ^ 2 + t ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hfac hpos

/-- **Telescoping gain on a vertical line.**  A unit-shift defect of order `p` whose forward
translates vanish gives a function of order `p-1`. -/
theorem norm_le_of_shift_defect {R E : ℂ → ℂ} {C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    {p : ℕ} (hp : 2 ≤ p) {t : ℝ} (ht : 2 ≤ t)
    (hdef : ∀ n : ℕ, R ((σ : ℂ) + (t : ℂ) * Complex.I + ((n : ℂ) + 1))
        - R ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))
      = E ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)))
    (hE : ∀ n : ℕ, ‖E ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖
      ≤ C / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ p)
    (hvanish : Tendsto (fun n : ℕ => R ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)))
      atTop (nhds 0)) :
    ‖R ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * C / t ^ (p - 1) := by
  have htpos : (0 : ℝ) < t := by linarith
  set f : ℕ → ℂ := fun n => R ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) with hf
  set g : ℕ → ℂ := fun n => E ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) with hg
  have hstep : ∀ n : ℕ, f (n + 1) - f n = g n := by
    intro n
    have := hdef n
    rw [hf, hg]
    push_cast
    exact this
  -- the majorant
  have hmaj : ∀ n : ℕ, ‖g n‖ ≤ (C / t ^ (p - 2)) * (1 / ((σ + n) ^ 2 + t ^ 2)) := by
    intro n
    refine le_trans (hE n) ?_
    have hden : (0 : ℝ) < t ^ (p - 2) * ((σ + n) ^ 2 + t ^ 2) := by positivity
    have hge := pow_norm_vertical_add_nat_ge hσ htpos hp (σ := σ) n
    have hpow : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ p :=
      lt_of_lt_of_le hden hge
    rw [div_le_iff₀ hpow]
    have : (C / t ^ (p - 2)) * (1 / ((σ + n) ^ 2 + t ^ 2))
        * (t ^ (p - 2) * ((σ + n) ^ 2 + t ^ 2)) = C := by
      field_simp
    calc C = (C / t ^ (p - 2)) * (1 / ((σ + n) ^ 2 + t ^ 2))
          * (t ^ (p - 2) * ((σ + n) ^ 2 + t ^ 2)) := this.symm
      _ ≤ (C / t ^ (p - 2)) * (1 / ((σ + n) ^ 2 + t ^ 2))
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ p := by
          refine mul_le_mul_of_nonneg_left hge ?_
          have : (0 : ℝ) < (σ + n) ^ 2 + t ^ 2 := by positivity
          positivity
  have hsummableNorm : Summable (fun n : ℕ => ‖g n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmaj ?_
    exact ((summable_inv_sq_vertical hσ t).mul_left (C / t ^ (p - 2)))
  have hsummable : Summable g := hsummableNorm.of_norm
  -- the telescoped sum
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, g n = f N - f 0 := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => (hstep n).symm)]
    exact Finset.sum_range_sub f N
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g n) atTop (nhds (0 - f 0)) := by
    refine Tendsto.congr (fun N => (hpartial N).symm) ?_
    exact hvanish.sub tendsto_const_nhds
  have hsum : ∑' n : ℕ, g n = -f 0 := by
    have hgs := hsummable.hasSum_iff_tendsto_nat.mpr (by simpa using htend)
    exact hgs.tsum_eq
  have hf0 : f 0 = R ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [hf]
    norm_num
  -- the estimate
  have hnorm : ‖R ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ∑' n : ℕ, ‖g n‖ := by
    have : ‖(-f 0 : ℂ)‖ ≤ ∑' n : ℕ, ‖g n‖ := by
      rw [← hsum]
      exact norm_tsum_le_tsum_norm hsummableNorm
    rw [norm_neg, hf0] at this
    exact this
  refine le_trans hnorm ?_
  have hbound : ∑' n : ℕ, ‖g n‖
      ≤ (C / t ^ (p - 2)) * ∑' n : ℕ, 1 / ((σ + n) ^ 2 + t ^ 2) := by
    rw [← tsum_mul_left]
    exact hsummableNorm.tsum_le_tsum hmaj
      ((summable_inv_sq_vertical hσ t).mul_left (C / t ^ (p - 2)))
  refine le_trans hbound ?_
  have hfactor : (0 : ℝ) ≤ C / t ^ (p - 2) := by positivity
  have htail := tsum_inv_sq_vertical_le hσ ht (σ := σ)
  have hmul : (C / t ^ (p - 2)) * ∑' n : ℕ, 1 / ((σ + n) ^ 2 + t ^ 2)
      ≤ (C / t ^ (p - 2)) * (4 / t) := mul_le_mul_of_nonneg_left htail hfactor
  refine le_trans hmul ?_
  have hpow : t ^ (p - 2) * t = t ^ (p - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [show (C / t ^ (p - 2)) * (4 / t) = 4 * C / (t ^ (p - 2) * t) by ring, hpow]

end

end GaloisForLFunctions.HTGeometry
