import GaloisForLFunctions.HTGeometry.FirstOrderCentralIndexUpper
import GaloisForLFunctions.HTGeometry.PointwiseLimitClass

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- Every transcendental entire order-one ADE admits an escaping radius sequence on which the
central-index logarithmic slope converges to a strictly positive finite number. -/
theorem exists_positive_centralIndex_logSlope_of_order_one
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1) :
    ∃ radii : ℕ → ℝ, ∃ q : ℝ, 0 < q ∧
      Tendsto radii atTop atTop ∧
      Tendsto (fun n => Real.log ((centralIndex a (radii n) : ℕ) : ℝ) /
        Real.log (radii n)) atTop (nhds q) := by
  classical
  obtain ⟨d, C₀, hC₀, hlower⟩ :=
    exists_radius_le_centralIndex_pow_of_order_one ha hn₀ htrans hDA
  obtain ⟨C₁, K, hC₁, hupper⟩ :=
    exists_centralIndex_le_pow_of_order_one ha hn₀ htrans hDA
  choose r hrlarge hrlower using fun n : ℕ => hlower ((n : ℝ) + 2)
  have hr2 : ∀ n, (2 : ℝ) ≤ r n := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact le_trans (by linarith : (2 : ℝ) ≤ (n : ℝ) + 2) (hrlarge n)
  have hrpos : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by norm_num) (hr2 n)
  have hr : Tendsto r atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    obtain ⟨N, hN⟩ := exists_nat_ge B
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact le_trans hN (le_trans hNn (le_trans (by linarith) (hrlarge n)))
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    obtain ⟨s, hsC, hsbound⟩ := hlower (C₀ + 1)
    rw [hd0, pow_zero, mul_one] at hsbound
    linarith
  have hνpos : ∀ n, 0 < ((centralIndex a (r n) : ℕ) : ℝ) := by
    intro n
    by_contra hν
    have hν0 : ((centralIndex a (r n) : ℕ) : ℝ) = 0 := le_antisymm (le_of_not_gt hν)
      (Nat.cast_nonneg _)
    have hb := hrlower n
    rw [hν0, zero_pow (Nat.ne_of_gt hdpos), mul_zero] at hb
    linarith [hrpos n]
  have hlogr : ∀ n, 0 < Real.log (r n) := fun n => Real.log_pos (lt_of_lt_of_le one_lt_two (hr2 n))
  let slope : ℕ → ℝ := fun n =>
    Real.log ((centralIndex a (r n) : ℕ) : ℝ) / Real.log (r n)
  have hC₀err : Tendsto (fun n => Real.log C₀ / Real.log (r n)) atTop (nhds 0) := by
    have hlog : Tendsto (fun n => Real.log (r n)) atTop atTop := Real.tendsto_log_atTop.comp hr
    simpa using (tendsto_const_nhds (x := Real.log C₀) (f := atTop)).div_atTop hlog
  have hC₁err : Tendsto (fun n => Real.log C₁ / Real.log (r n)) atTop (nhds 0) := by
    have hlog : Tendsto (fun n => Real.log (r n)) atTop atTop := Real.tendsto_log_atTop.comp hr
    simpa using (tendsto_const_nhds (x := Real.log C₁) (f := atTop)).div_atTop hlog
  have hlowerSlope : ∀ n,
      Real.log C₀ / Real.log (r n) < 1 / 2 →
      (1 : ℝ) / (2 * d) ≤ slope n := by
    intro n herr
    have hlog := Real.log_le_log (hrpos n) (hrlower n)
    rw [Real.log_mul (ne_of_gt hC₀) (pow_ne_zero _ (ne_of_gt (hνpos n))),
      Real.log_pow] at hlog
    have herr' := (div_lt_iff₀ (hlogr n)).mp herr
    dsimp [slope]
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
    apply (le_div_iff₀ (hlogr n)).2
    calc
      (1 / (2 * (d : ℝ))) * Real.log (r n) = Real.log (r n) / (2 * (d : ℝ)) := by ring
      _ ≤ Real.log ((centralIndex a (r n) : ℕ) : ℝ) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))).2
        nlinarith
  have hupperAlong : ∀ᶠ n : ℕ in atTop,
      ((centralIndex a (r n) : ℕ) : ℝ) ≤ C₁ * (r n) ^ K := hr.eventually hupper
  have hupperSlope : ∀ᶠ n : ℕ in atTop,
      (slope n ≤ (K : ℝ) + 1) := by
    filter_upwards [hupperAlong, hC₁err.eventually_lt_const one_pos] with n hν herr
    have hlog := Real.log_le_log (hνpos n) hν
    rw [Real.log_mul (ne_of_gt hC₁) (pow_ne_zero _ (ne_of_gt (hrpos n))),
      Real.log_pow] at hlog
    have herr' := (div_lt_iff₀ (hlogr n)).mp herr
    dsimp [slope]
    apply (div_le_iff₀ (hlogr n)).2
    linarith
  have hlowerEventually : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / (2 * d) ≤ slope n := by
    filter_upwards [hC₀err.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    exact hlowerSlope n hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlowerEventually.and hupperSlope)
  let p : ℕ → Fin 1 → ℝ := fun n _ => slope (n + N)
  have hp : ∀ n k, p n k ∈ Set.Icc ((1 : ℝ) / (2 * d)) ((K : ℝ) + 1) := by
    intro n k
    exact hN (n + N) (by omega)
  obtain ⟨ns, hns, plim, hplim, htendsto⟩ :=
    exists_subseq_tendsto_of_mem_Icc (p := p) hp
  let radii : ℕ → ℝ := fun n => r (ns n + N)
  let q : ℝ := plim 0
  have hidx : Tendsto (fun n => ns n + N) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    filter_upwards [(hns.tendsto_atTop.eventually_ge_atTop B)] with n hn
    omega
  have hradii : Tendsto radii atTop atTop := hr.comp hidx
  have hqpos : 0 < q := by
    have hqmem := hplim 0
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 : ℝ) / (2 * d)) hqmem.1
  refine ⟨radii, q, hqpos, hradii, ?_⟩
  have hq := htendsto 0
  simpa [radii, q, p, slope] using hq

end

end GaloisForLFunctions.HTGeometry
