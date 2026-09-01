import GaloisForLFunctions.RHTower.RouteEComponentHistoryGibbsParity
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation

/-!
# Route E bounded-density singleton-history no-go

The Ramaré incidence complement is a negative centered load energy plus one scalar conditional
mean square.  Existing component-history theory identifies the uniform scalar bias on a binary
singleton cell as `(1 - 2 / M)^C` and bounds its physical Gibbs perturbation by an explicit
curvature defect.

This file proves that the bias is at least `exp (-2C / (M - 2))`.  Consequently exact scalar
cancellation and vanishing curvature force unbounded component density `C / (M - 2)`.  It kills
every bounded-density cofinal singleton-history implementation of Route E and extracts the sharp
surviving finite complexity law `C ≥ -(M - 2) log D / 2`.
-/

open Filter Topology

namespace RHTower

open scoped BigOperators

noncomputable section

/-- The singleton-history parity bias has an exponential lower floor in component density. -/
theorem routeE_exp_neg_density_le_binary_singleton_bias
    (M C : ℕ) (hM : 2 < M) :
    Real.exp (-(2 * (C : ℝ) / ((M : ℝ) - 2))) ≤
      ((1 : ℝ) - 2 / (M : ℝ)) ^ C := by
  have hMreal : (2 : ℝ) < M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hdenne : (M : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hb : (0 : ℝ) < (1 : ℝ) - 2 / M := by
    rw [sub_pos, div_lt_one hMpos]
    exact hMreal
  have hlog := HTGeometry.one_sub_inv_le_log hb
  have hinv :
      1 - ((1 : ℝ) - 2 / M)⁻¹ = -(2 / ((M : ℝ) - 2)) := by
    field_simp [hMne, hdenne]
    ring
  rw [hinv] at hlog
  have hmul :
      -(2 * (C : ℝ) / ((M : ℝ) - 2)) ≤
        (C : ℝ) * Real.log ((1 : ℝ) - 2 / M) := by
    have hC : (0 : ℝ) ≤ C := by positivity
    have := mul_le_mul_of_nonneg_left hlog hC
    rw [mul_neg] at this
    have hid :
        -((C : ℝ) * (2 / ((M : ℝ) - 2))) =
          -(2 * (C : ℝ) / ((M : ℝ) - 2)) := by ring
    rw [hid] at this
    exact this
  calc
    Real.exp (-(2 * (C : ℝ) / ((M : ℝ) - 2))) ≤
        Real.exp ((C : ℝ) * Real.log ((1 : ℝ) - 2 / M)) :=
      Real.exp_le_exp.mpr hmul
    _ = Real.exp (Real.log ((1 : ℝ) - 2 / M)) ^ C := by
      rw [Real.exp_nat_mul]
    _ = ((1 : ℝ) - 2 / M) ^ C := by rw [Real.exp_log hb]

/-- Any upper defect on the singleton bias forces a sharp component-complexity lower bound. -/
theorem routeE_component_count_lower_of_exp_neg_density_le
    (M C : ℕ) (D : ℝ) (hM : 2 < M)
    (hfloor : Real.exp (-(2 * (C : ℝ) / ((M : ℝ) - 2))) ≤ D) :
    -(((M : ℝ) - 2) / 2) * Real.log D ≤ C := by
  have hMreal : (2 : ℝ) < M := by exact_mod_cast hM
  have hdenpos : (0 : ℝ) < (M : ℝ) - 2 := by linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hfloor
  rw [Real.log_exp] at hlog
  have hmul : -(2 * (C : ℝ)) ≤ Real.log D * ((M : ℝ) - 2) := by
    exact (div_le_iff₀ hdenpos).mp (by simpa only [neg_div] using hlog)
  have hrev :
      -(((M : ℝ) - 2) * Real.log D) ≤ 2 * (C : ℝ) := by
    nlinarith
  calc
    -(((M : ℝ) - 2) / 2) * Real.log D =
        -(((M : ℝ) - 2) * Real.log D) / 2 := by ring
    _ ≤ (2 * (C : ℝ)) / 2 := div_le_div_of_nonneg_right hrev (by norm_num)
    _ = C := by ring

section BinarySingletonPhysical

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Exact physical cancellation on a binary singleton-history cell forces the exponential
component-density floor below the Gibbs curvature defect. -/
theorem routeE_binary_componentHistory_zero_forces_density_floor
    (m : ℕ) (k : C → Bool → ℕ) (value : C → Bool → ℝ) (X H : ℝ)
    (hM : 2 < m + 1)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hone : ∀ c, k c true = 1)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
      ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool) value x r ∈
        Set.Icc (X - H) (X + H))
    (hzero :
      let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
      (∑ x : {x // x ∈ cell},
            routeEProductHistoryGibbsWeight X
                (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
              ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
          (∑ x : {x // x ∈ cell},
            routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1)) = 0) :
    Real.exp
        (-(2 * (Fintype.card C : ℝ) / (((m + 1 : ℕ) : ℝ) - 2))) ≤
      2 * Real.tanh
        (((((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) / 4)) := by
  classical
  have hcompare := routeE_binary_componentHistory_gibbsParity_sub_bias_le_tanh
    m k value X H hk hone hX hH hHX haperture
  dsimp only at hcompare hzero
  rw [hzero, zero_sub, abs_neg] at hcompare
  have hMreal : (2 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hM
  have hbase : (0 : ℝ) < 1 - 2 / ((m + 1 : ℕ) : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hMreal
  rw [abs_of_nonneg (pow_nonneg (le_of_lt hbase) _)] at hcompare
  exact (routeE_exp_neg_density_le_binary_singleton_bias
    (m + 1) (Fintype.card C) hM).trans hcompare

/-- Exact physical cancellation also forces the sharp finite component-complexity law. -/
theorem routeE_binary_componentHistory_zero_forces_component_count
    (m : ℕ) (k : C → Bool → ℕ) (value : C → Bool → ℝ) (X H : ℝ)
    (hM : 2 < m + 1)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hone : ∀ c, k c true = 1)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
      ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool) value x r ∈
        Set.Icc (X - H) (X + H))
    (hzero :
      let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
      (∑ x : {x // x ∈ cell},
            routeEProductHistoryGibbsWeight X
                (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
              ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
          (∑ x : {x // x ∈ cell},
            routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1)) = 0) :
    -(((((m + 1 : ℕ) : ℝ) - 2) / 2)) *
        Real.log
          (2 * Real.tanh
            (((((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) / 4))) ≤
      Fintype.card C := by
  apply routeE_component_count_lower_of_exp_neg_density_le
    (m + 1) (Fintype.card C)
    (2 * Real.tanh
      (((((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) / 4))) hM
  exact routeE_binary_componentHistory_zero_forces_density_floor
    m k value X H hM hk hone hX hH hHX haperture hzero

end BinarySingletonPhysical

/-- Vanishing defects above the exponential floor force component density to tend to infinity. -/
theorem routeE_density_tendsto_atTop_of_exp_floor_tendsto_zero
    (M C : ℕ → ℕ) (D : ℕ → ℝ)
    (hD : Tendsto D atTop (𝓝 0))
    (hfloor : ∀ᶠ n in atTop,
      Real.exp (-(2 * (C n : ℝ) / ((M n : ℝ) - 2))) ≤ D n) :
    Tendsto (fun n => (C n : ℝ) / ((M n : ℝ) - 2)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  have hpositive : 0 < Real.exp (-2 * K) := Real.exp_pos _
  have hsmall : ∀ᶠ n in atTop, D n < Real.exp (-2 * K) :=
    hD.eventually_lt_const hpositive
  filter_upwards [hfloor, hsmall] with n hfloorn hsmalln
  have hexp :
      Real.exp (-(2 * (C n : ℝ) / ((M n : ℝ) - 2))) <
        Real.exp (-2 * K) :=
    lt_of_le_of_lt hfloorn hsmalln
  have hexponent := Real.exp_lt_exp.mp hexp
  have hnormalized :
      -2 * ((C n : ℝ) / ((M n : ℝ) - 2)) < -2 * K := by
    calc
      -2 * ((C n : ℝ) / ((M n : ℝ) - 2)) =
          -(2 * (C n : ℝ) / ((M n : ℝ) - 2)) := by ring
      _ < -2 * K := hexponent
  linarith

/-- Cofinal singleton-history cancellation with bounded component density and vanishing Gibbs
curvature.  The finite physical theorem above forces its exponential-floor clause. -/
def RouteEBoundedDensitySingletonCancellation : Prop :=
  ∃ (M C : ℕ → ℕ) (D : ℕ → ℝ) (K : ℝ),
    (∀ᶠ n in atTop, 2 < M n) ∧
    (∀ᶠ n in atTop,
      (C n : ℝ) / ((M n : ℝ) - 2) ≤ K) ∧
    Tendsto D atTop (𝓝 0) ∧
    (∀ᶠ n in atTop,
      Real.exp (-(2 * (C n : ℝ) / ((M n : ℝ) - 2))) ≤ D n)

/-- **Route E bounded-density singleton-history no-go.**  Exact scalar cancellation with
vanishing Gibbs curvature cannot persist along any cofinal family whose component count is only
`O(M)`.  Thus a surviving singleton-history Route E must have unbounded component density or a
nonvanishing curvature defect. -/
theorem not_routeEBoundedDensitySingletonCancellation :
    ¬ RouteEBoundedDensitySingletonCancellation := by
  rintro ⟨M, C, D, K, _hM, hdensity, hD, hfloor⟩
  have hdensityTop :=
    routeE_density_tendsto_atTop_of_exp_floor_tendsto_zero M C D hD hfloor
  have hlarge : ∀ᶠ n in atTop,
      K + 1 ≤ (C n : ℝ) / ((M n : ℝ) - 2) :=
    (Filter.tendsto_atTop.mp hdensityTop) (K + 1)
  obtain ⟨n, hupper, hlower⟩ := (hdensity.and hlarge).exists
  linarith

end

end RHTower
