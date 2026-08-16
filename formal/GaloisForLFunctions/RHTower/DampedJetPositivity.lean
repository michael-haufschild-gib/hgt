import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Polynomial

/-!
# Eventual positivity of a damped polynomial jet

A polynomial that is positive on the whole real line dominates every polynomial of strictly smaller
degree by a fixed constant: the ratio is continuous and tends to zero at both ends, so it is
bounded.  Consequently a finite jet correction with coefficients that tend to zero cannot destroy
positivity: for all large damping the corrected sum is still positive at every point.

This is the mechanism behind the late-time positivity of a Gaussian heat-filtered prime packet:
the heat operator applied to a positive polynomial is that polynomial plus a finite sum of its
higher derivatives with coefficients `O(t^{-j})`, and every derivative is dominated by the
polynomial itself.
-/

open Filter Topology Polynomial

namespace RHTower

noncomputable section

/-! ## A positive polynomial dominates every lower-degree polynomial -/

theorem tendsto_abs_ratio_atTop {R S : Polynomial ℝ} (hR : ∀ u : ℝ, 0 < R.eval u)
    (hdeg : S.degree < R.degree) :
    Tendsto (fun u : ℝ => |S.eval u| / R.eval u) atTop (nhds 0) := by
  have hbase : Tendsto (fun u : ℝ => S.eval u / R.eval u) atTop (nhds 0) :=
    Polynomial.div_tendsto_atTop_zero_of_degree_lt S R hdeg
  have habs := hbase.abs
  rw [abs_zero] at habs
  refine habs.congr fun u => ?_
  rw [abs_div, abs_of_pos (hR u)]

theorem tendsto_abs_ratio_atBot {R S : Polynomial ℝ} (hR : ∀ u : ℝ, 0 < R.eval u)
    (hdeg : S.degree < R.degree) :
    Tendsto (fun u : ℝ => |S.eval u| / R.eval u) atBot (nhds 0) := by
  have hXdeg : (0 : WithBot ℕ) < (-Polynomial.X : Polynomial ℝ).degree := by
    rw [Polynomial.degree_neg, Polynomial.degree_X]
    exact WithBot.coe_lt_coe.2 Nat.zero_lt_one
  have hcompS : (S.comp (-Polynomial.X)).degree = S.degree := by
    rw [Polynomial.degree_comp hXdeg, Polynomial.degree_neg, Polynomial.degree_X, mul_one]
  have hcompR : (R.comp (-Polynomial.X)).degree = R.degree := by
    rw [Polynomial.degree_comp hXdeg, Polynomial.degree_neg, Polynomial.degree_X, mul_one]
  have heval : ∀ (P : Polynomial ℝ) (u : ℝ), (P.comp (-Polynomial.X)).eval u = P.eval (-u) := by
    intro P u
    rw [Polynomial.eval_comp]
    simp
  have hR' : ∀ u : ℝ, 0 < (R.comp (-Polynomial.X)).eval u := by
    intro u
    rw [heval]
    exact hR (-u)
  have hdeg' : (S.comp (-Polynomial.X)).degree < (R.comp (-Polynomial.X)).degree := by
    rw [hcompS, hcompR]
    exact hdeg
  have htop := tendsto_abs_ratio_atTop hR' hdeg'
  have hneg : Tendsto (fun u : ℝ => -u) atBot atTop := tendsto_neg_atBot_atTop
  have hcomp := htop.comp hneg
  refine hcomp.congr fun u => ?_
  rw [Function.comp_apply, heval, heval]
  simp

/-- **A positive polynomial dominates every polynomial of strictly smaller degree.** -/
theorem exists_ratio_bound {R S : Polynomial ℝ} (hR : ∀ u : ℝ, 0 < R.eval u)
    (hdeg : S.degree < R.degree) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, |S.eval u| ≤ M * R.eval u := by
  classical
  have hcont : Continuous fun u : ℝ => |S.eval u| / R.eval u :=
    (S.continuous.abs).div R.continuous fun u => (hR u).ne'
  have htop := tendsto_abs_ratio_atTop hR hdeg
  have hbot := tendsto_abs_ratio_atBot hR hdeg
  have hIio : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (htop.eventually_mem hIio)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atBot.1 (hbot.eventually_mem hIio)
  set a : ℝ := min N₂ (-|N₁| - |N₂|) with ha
  set b : ℝ := max N₁ (|N₁| + |N₂|) with hb
  have hab : a ≤ b := by
    have h1 : a ≤ -|N₁| - |N₂| := min_le_right _ _
    have h2 : |N₁| + |N₂| ≤ b := le_max_right _ _
    have h3 : (0 : ℝ) ≤ |N₁| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |N₂| := abs_nonneg _
    linarith
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨u₀, hu₀, hmax⟩ := hcompact.exists_isMaxOn ⟨a, Set.left_mem_Icc.2 hab⟩
    (hcont.continuousOn)
  set M : ℝ := max 1 (|S.eval u₀| / R.eval u₀) with hM
  refine ⟨M, le_trans zero_le_one (le_max_left _ _), fun u => ?_⟩
  have hkey : |S.eval u| / R.eval u ≤ M := by
    by_cases hin : u ∈ Set.Icc a b
    · exact le_trans (hmax hin) (le_max_right _ _)
    · rw [Set.mem_Icc] at hin
      by_cases hlt : u < a
      · have hle : u ≤ N₂ := le_trans hlt.le (min_le_left _ _)
        have hmem := hN₂ u hle
        exact le_trans (le_of_lt (Set.mem_Iio.1 hmem)) (le_max_left _ _)
      · have hau : a ≤ u := not_lt.1 hlt
        have hgt : b < u := by
          by_contra hcon
          exact hin ⟨hau, not_lt.1 hcon⟩
        have hle : N₁ ≤ u := le_trans (le_max_left _ _) hgt.le
        have hmem := hN₁ u hle
        exact le_trans (le_of_lt (Set.mem_Iio.1 hmem)) (le_max_left _ _)
  rw [div_le_iff₀ (hR u)] at hkey
  exact hkey

/-! ## The damped jet stays positive -/

variable {ι : Type*}

/-- **(24.190)** A finite jet correction whose total relative weight is below one cannot destroy
positivity. -/
theorem jetSum_pos_of_small_tail (s : Finset ι) (R : ℝ → ℝ) (Rj : ι → ℝ → ℝ) (c M : ι → ℝ)
    (hR : ∀ u, 0 < R u) (hM : ∀ j ∈ s, ∀ u, |Rj j u| ≤ M j * R u)
    (hsmall : ∑ j ∈ s, |c j| * M j < 1) (u : ℝ) :
    0 < R u + ∑ j ∈ s, c j * Rj j u := by
  have hbound : |∑ j ∈ s, c j * Rj j u| ≤ (∑ j ∈ s, |c j| * M j) * R u := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hM j hj u) (abs_nonneg _)
  have hlt : (∑ j ∈ s, |c j| * M j) * R u < R u := by
    have := hR u
    nlinarith [hsmall, this]
  have habs := abs_le.1 hbound
  linarith [habs.1]

/-- The relative weight of a jet correction with coefficients `O(t^{-1})` tends to zero. -/
theorem tendsto_jetWeight_zero (s : Finset ι) (M w : ι → ℝ) (k : ι → ℕ)
    (hk : ∀ j ∈ s, 1 ≤ k j) :
    Tendsto (fun t : ℝ => ∑ j ∈ s, |w j / t ^ (k j)| * M j) atTop (nhds 0) := by
  have hterm : ∀ j ∈ s, Tendsto (fun t : ℝ => |w j / t ^ (k j)| * M j) atTop (nhds 0) := by
    intro j hj
    have hkj : k j ≠ 0 := by
      have := hk j hj
      omega
    have hpow : Tendsto (fun t : ℝ => t ^ (k j)) atTop atTop := tendsto_pow_atTop hkj
    have hdiv : Tendsto (fun t : ℝ => w j / t ^ (k j)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hpow
    have habs := hdiv.abs
    rw [abs_zero] at habs
    have := habs.mul_const (M j)
    simpa using this
  have hsum := tendsto_finsetSum s hterm
  simpa using hsum

/-- **(24.190)** For all large damping the corrected jet is positive at every point. -/
theorem eventually_jetSum_pos (s : Finset ι) (R : ℝ → ℝ) (Rj : ι → ℝ → ℝ) (M w : ι → ℝ)
    (k : ι → ℕ) (hR : ∀ u, 0 < R u) (hM : ∀ j ∈ s, ∀ u, |Rj j u| ≤ M j * R u)
    (hk : ∀ j ∈ s, 1 ≤ k j) :
    ∀ᶠ t : ℝ in atTop, ∀ u : ℝ, 0 < R u + ∑ j ∈ s, (w j / t ^ (k j)) * Rj j u := by
  have hlim := tendsto_jetWeight_zero s M w k hk
  have hev : ∀ᶠ t : ℝ in atTop, ∑ j ∈ s, |w j / t ^ (k j)| * M j < 1 := by
    have hIio : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
    exact hlim.eventually_mem hIio
  filter_upwards [hev] with t ht u
  exact jetSum_pos_of_small_tail s R Rj (fun j => w j / t ^ (k j)) M hR hM ht u

end

end RHTower
