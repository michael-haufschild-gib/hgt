import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyNumerator
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct

/-!
# The hard-edge limit of the Cayley numerators

Clearing the Cayley denominator at degree `d` multiplies the packet by `(1 + u/a²)^d`.  When the
degree grows slower than the square of the aperture this factor tends to one locally uniformly, so
the normalized numerators have the same locally uniform limit as the packets themselves.  Since
each numerator is real-rooted, the limit has only real zeros.
-/

open Filter Topology Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- A geometric remainder estimate: `(1+w)^d` differs from `1` by at most `d (1+‖w‖)^d ‖w‖`. -/
theorem norm_one_add_pow_sub_one_le (w : ℂ) (d : ℕ) :
    ‖(1 + w) ^ d - 1‖ ≤ d * (1 + ‖w‖) ^ d * ‖w‖ := by
  have hgeom : (∑ i ∈ Finset.range d, (1 + w) ^ i) * ((1 + w) - 1) = (1 + w) ^ d - 1 :=
    geom_sum_mul (1 + w) d
  have hw : (1 + w) - 1 = w := by ring
  rw [hw] at hgeom
  rw [← hgeom, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.range d, ‖(1 + w) ^ i‖ ≤ (1 + ‖w‖) ^ d := by
    intro i hi
    have hid : i ≤ d := le_of_lt (Finset.mem_range.1 hi)
    have h1 : ‖(1 + w) ^ i‖ ≤ (1 + ‖w‖) ^ i := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using norm_add_le (1 : ℂ) w) i
    exact h1.trans (pow_le_pow_right₀ (by linarith [norm_nonneg w]) hid)
  calc ∑ i ∈ Finset.range d, ‖(1 + w) ^ i‖
      ≤ ∑ _i ∈ Finset.range d, (1 + ‖w‖) ^ d := Finset.sum_le_sum hterm
    _ = d * (1 + ‖w‖) ^ d := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **(HHWB.12) The cleared Cayley denominator tends to one.**  When the degree is small compared
with the square of the aperture, `(1 + u/a²)^d → 1` locally uniformly. -/
theorem tendstoLocallyUniformly_one_add_div_pow {a : ℕ → ℝ} {d : ℕ → ℕ}
    (ha : ∀ n, a n ≠ 0)
    (hratio : Tendsto (fun n => (d n : ℝ) / (a n) ^ (2 : ℕ)) atTop (nhds 0)) :
    TendstoLocallyUniformly (fun n u => (1 + u / ((a n : ℂ) ^ (2 : ℕ))) ^ (d n))
      (fun _ => (1 : ℂ)) atTop := by
  have hasq : ∀ n, (0 : ℝ) < (a n) ^ (2 : ℕ) := fun n =>
    lt_of_le_of_ne (sq_nonneg (a n)) (Ne.symm (pow_ne_zero 2 (ha n)))
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = max R 0 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact le_max_right _ _
  have hKS : K ⊆ Metric.closedBall 0 S := by
    refine hR.trans (Metric.closedBall_subset_closedBall ?_)
    rw [hS]; exact le_max_left _ _
  refine TendstoUniformlyOn.mono ?_ hKS
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun n => (d n : ℝ) * S / (a n) ^ (2 : ℕ) := ⟨_, rfl⟩
  have ht0 : Tendsto t atTop (nhds 0) := by
    have hmul : Tendsto (fun n => S * ((d n : ℝ) / (a n) ^ (2 : ℕ))) atTop (nhds (S * 0)) :=
      hratio.const_mul S
    rw [mul_zero] at hmul
    refine hmul.congr fun n => ?_
    rw [ht]
    ring
  have hlim : Tendsto (fun n => t n * Real.exp (t n)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => Real.exp (t n)) atTop (nhds (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp ht0
    have h2 := ht0.mul h1
    simpa using h2
  have hev : ∀ᶠ n in atTop, t n * Real.exp (t n) < ε := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with n hn u hu
  have hunorm : ‖u‖ ≤ S := by
    have hd := Metric.mem_closedBall.1 hu
    rwa [dist_zero_right] at hd
  have hnormw : ‖u / ((a n : ℂ) ^ (2 : ℕ))‖ ≤ S / (a n) ^ (2 : ℕ) := by
    rw [norm_div, norm_ofReal_sq]
    gcongr
  have hwnn : (0 : ℝ) ≤ ‖u / ((a n : ℂ) ^ (2 : ℕ))‖ := norm_nonneg _
  have hSa : (0 : ℝ) ≤ S / (a n) ^ (2 : ℕ) := by positivity
  have hbase := norm_one_add_pow_sub_one_le (u / ((a n : ℂ) ^ (2 : ℕ))) (d n)
  have hmono : (d n : ℝ) * (1 + ‖u / ((a n : ℂ) ^ (2 : ℕ))‖) ^ (d n) * ‖u / ((a n : ℂ) ^ (2 : ℕ))‖
      ≤ (d n : ℝ) * (1 + S / (a n) ^ (2 : ℕ)) ^ (d n) * (S / (a n) ^ (2 : ℕ)) := by
    gcongr
  have hexp : (1 + S / (a n) ^ (2 : ℕ)) ^ (d n) ≤ Real.exp (t n) := by
    have h1 : (1 : ℝ) + S / (a n) ^ (2 : ℕ) ≤ Real.exp (S / (a n) ^ (2 : ℕ)) := by
      have h := Real.add_one_le_exp (S / (a n) ^ (2 : ℕ))
      linarith
    calc (1 + S / (a n) ^ (2 : ℕ)) ^ (d n) ≤ (Real.exp (S / (a n) ^ (2 : ℕ))) ^ (d n) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = Real.exp ((d n : ℝ) * (S / (a n) ^ (2 : ℕ))) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (t n) := by rw [ht]; congr 1; ring
  have hfinal : (d n : ℝ) * (1 + S / (a n) ^ (2 : ℕ)) ^ (d n) * (S / (a n) ^ (2 : ℕ))
      ≤ t n * Real.exp (t n) := by
    have hrw : (d n : ℝ) * (1 + S / (a n) ^ (2 : ℕ)) ^ (d n) * (S / (a n) ^ (2 : ℕ))
        = t n * (1 + S / (a n) ^ (2 : ℕ)) ^ (d n) := by
      rw [ht]; ring
    rw [hrw]
    have htn : 0 ≤ t n := by rw [ht]; positivity
    exact mul_le_mul_of_nonneg_left hexp htn
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt (hbase.trans (hmono.trans hfinal)) hn

/-- **(HHWB.13) The normalized numerators have the same limit as the packets.** -/
theorem tendstoLocallyUniformly_scaled_cayleyNumerator {a : ℕ → ℝ} {d : ℕ → ℕ}
    {P : ℕ → Polynomial ℂ} {F : ℂ → ℂ}
    (ha : ∀ n, a n ≠ 0) (hd : ∀ n, (P n).natDegree ≤ d n)
    (hasq : Tendsto (fun n => (a n) ^ (2 : ℕ)) atTop atTop)
    (hratio : Tendsto (fun n => (d n : ℝ) / (a n) ^ (2 : ℕ)) atTop (nhds 0))
    (hG : TendstoLocallyUniformly
      (fun n u => (P n).eval (((a n : ℂ) ^ (2 : ℕ) - u) / ((a n : ℂ) ^ (2 : ℕ) + u))) F atTop)
    (hFc : Continuous F) :
    TendstoLocallyUniformly
      (fun n u => (((a n : ℂ) ^ (2 : ℕ)) ^ (d n))⁻¹ * (cayleyNumerator (a n) (d n) (P n)).eval u)
      F atTop := by
  have hprod := tendstoLocallyUniformly_mul
    (tendstoLocallyUniformly_one_add_div_pow ha hratio) hG continuous_const hFc
  have hone : (fun u : ℂ => (1 : ℂ) * F u) = F := by
    funext u
    rw [one_mul]
  rw [hone] at hprod
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hprod ⊢
  intro K hK
  refine (hprod K hK).congr ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hev : ∀ᶠ n in atTop, R < (a n) ^ (2 : ℕ) := hasq.eventually_gt_atTop R
  filter_upwards [hev] with n hn u hu
  have hunorm : ‖u‖ ≤ R := by
    have hd' := Metric.mem_closedBall.1 (hR hu)
    rwa [dist_zero_right] at hd'
  have hane : ((a n : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    intro hcon
    have := norm_ofReal_sq (a n)
    rw [hcon, norm_zero] at this
    linarith [hunorm, norm_nonneg u]
  have hsum : ((a n : ℂ) ^ (2 : ℕ) + u) ≠ 0 := by
    intro hcon
    have heq : u = -((a n : ℂ) ^ (2 : ℕ)) := by linear_combination hcon
    have hnu : ‖u‖ = (a n) ^ (2 : ℕ) := by rw [heq, norm_neg, norm_ofReal_sq]
    linarith
  have heval := eval_cayleyNumerator (a n) (d n) (P n) (hd n) u hsum
  show (1 + u / ((a n : ℂ) ^ (2 : ℕ))) ^ (d n) *
      (P n).eval (((a n : ℂ) ^ (2 : ℕ) - u) / ((a n : ℂ) ^ (2 : ℕ) + u))
    = (((a n : ℂ) ^ (2 : ℕ)) ^ (d n))⁻¹ * (cayleyNumerator (a n) (d n) (P n)).eval u
  rw [heval]
  have hfac : (1 + u / ((a n : ℂ) ^ (2 : ℕ))) ^ (d n)
      = (((a n : ℂ) ^ (2 : ℕ)) ^ (d n))⁻¹ * ((a n : ℂ) ^ (2 : ℕ) + u) ^ (d n) := by
    have hbase : (1 + u / ((a n : ℂ) ^ (2 : ℕ))) = ((a n : ℂ) ^ (2 : ℕ))⁻¹ * ((a n : ℂ) ^ (2 : ℕ) + u) := by
      rw [mul_add, inv_mul_cancel₀ hane, div_eq_inv_mul]
    rw [hbase, mul_pow, inv_pow]
  rw [hfac]
  ring

/-- **(HHWB.3)/(HHWB.4) The hard-edge limit is real-rooted.**  A locally uniform limit of
normalized hard-edge packets built from real-rooted polynomials has only real zeros. -/
theorem hardEdgeCayleyLimit_zero_im_eq_zero {a : ℕ → ℝ} {d : ℕ → ℕ}
    {P : ℕ → Polynomial ℂ} {F : ℂ → ℂ}
    (ha : ∀ n, a n ≠ 0) (hd : ∀ n, (P n).natDegree ≤ d n)
    (hreal : ∀ n, ∀ ρ : ℂ, (P n).eval ρ = 0 → ρ.im = 0)
    (hasq : Tendsto (fun n => (a n) ^ (2 : ℕ)) atTop atTop)
    (hratio : Tendsto (fun n => (d n : ℝ) / (a n) ^ (2 : ℕ)) atTop (nhds 0))
    (hG : TendstoLocallyUniformly
      (fun n u => (P n).eval (((a n : ℂ) ^ (2 : ℕ) - u) / ((a n : ℂ) ^ (2 : ℕ) + u))) F atTop)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    {b z : ℂ} (hb : F b ≠ 0) (hz : F z = 0) : z.im = 0 := by
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact (hF x (Set.mem_univ x)).continuousAt
  have hconv := tendstoLocallyUniformly_scaled_cayleyNumerator ha hd hasq hratio hG hFc
  refine scaled_cayleyNumerator_limit_zero_im_eq_zero ha ?_ hd hreal hconv hF hb hz
  intro n
  refine inv_ne_zero (pow_ne_zero _ ?_)
  simpa using pow_ne_zero 2 (Complex.ofReal_ne_zero.2 (ha n))

end RHTower

end
