import GaloisForLFunctions.RHTower.RobinCriterionRiemann

/-!
# Reduction of Robin's inequality to colossally abundant integers

A positive integer is colossally abundant if it maximizes `σ(n)/n^(1+ε)` for some
positive `ε`. Ties are included. The primewise extremizers `robinExtremalAt x`
are such integers. Robin's inequality holds eventually on all integers if and
only if it holds eventually on the colossally abundant integers.

For the nontrivial implication, set `ℓ = log n` and select the extremal parameter
`ε = 1/(ℓ log ℓ)`. The supporting-line inequality for `log log` transfers the
extremal bound to `n`. The selected extremal integers tend to infinity, so an
arbitrary finite exceptional set is harmless.
-/

open Filter Topology Set
open ArithmeticFunction (sigma)

namespace RHTower

noncomputable section

/-- Global maximizers of the penalized divisor sum, including tied maximizers. -/
def IsColossallyAbundant (N : ℕ) : Prop :=
  0 < N ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 0 < n →
    (sigma 1 n : ℝ) / (n : ℝ) ^ (1 + ε) ≤
      (sigma 1 N : ℝ) / (N : ℝ) ^ (1 + ε)

private theorem log_penalized_sigma {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    Real.log ((sigma 1 n : ℝ) / (n : ℝ) ^ (1 + ε)) =
      Real.log ((sigma 1 n : ℝ) / (n : ℝ)) - ε * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ : (0 : ℝ) < sigma 1 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne'
  rw [Real.log_div hσ.ne' (Real.rpow_pos_of_pos hnR _).ne',
    Real.log_div hσ.ne' hnR.ne', Real.log_rpow hnR]
  ring

/-- The actual primewise Robin extremizer is colossally abundant. -/
theorem isColossallyAbundant_robinExtremalAt {x : ℝ} (hx : 1 < x) :
    IsColossallyAbundant (robinExtremalAt x) := by
  have hN : 0 < robinExtremalAt x := robinExtremal_pos _ _
  refine ⟨hN, robinParameter x, robinParameter_pos hx, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < robinExtremalAt x := by exact_mod_cast hN
  have hσn : (0 : ℝ) < sigma 1 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne'
  have hσN : (0 : ℝ) < sigma 1 (robinExtremalAt x) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 _ hN.ne'
  apply (Real.log_le_log_iff
    (div_pos hσn (Real.rpow_pos_of_pos hnR _))
    (div_pos hσN (Real.rpow_pos_of_pos hNR _))).mp
  rw [log_penalized_sigma hn, log_penalized_sigma hN]
  exact log_sigma_div_sub_le_robinExtremal (robinParameter_pos hx)
    (fun p hp hpx => robinExponent_eq_zero_of_floor_lt hx hp hpx) (Nat.ne_of_gt hn)

/-- Eventual Robin inequalities on colossally abundant integers suffice for all integers. -/
theorem eventually_robin_iff_eventually_colossallyAbundant :
    (∀ᶠ n : ℕ in atTop, (sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)) ↔
    (∀ᶠ n : ℕ in atTop, IsColossallyAbundant n → (sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)) := by
  constructor
  · intro h
    exact h.mono fun _ hn _ => hn
  intro h
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp eventually_two_fifths_le_theta
  let X : ℝ := max (max X₀ 100) (3 * (N₀ : ℝ))
  have hXX₀ : X₀ ≤ X := (le_max_left _ _).trans (le_max_left _ _)
  have hX100 : 100 ≤ X := (le_max_right _ _).trans (le_max_left _ _)
  have hXN₀ : 3 * (N₀ : ℝ) ≤ X := le_max_right _ _
  have hX1 : 1 < X := by linarith
  have hεX := robinParameter_pos hX1
  have hℓ : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => 1 / (Real.log n * Real.log (Real.log n)))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hℓ.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp hℓ))
  filter_upwards [hsmall.eventually (ge_mem_nhds hεX),
    hℓ.eventually (eventually_ge_atTop X), eventually_ge_atTop 1] with n hn1 hn2 hn3
  let ℓ : ℝ := Real.log n
  have hℓ1 : 1 < ℓ := by dsimp [ℓ]; linarith
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let ε : ℝ := 1 / (ℓ * Real.log ℓ)
  have hmem : ε ∈ Icc (robinParameter ℓ) (robinParameter X) :=
    ⟨robinParameter_le hℓ1, hn1⟩
  obtain ⟨x, ⟨hXx, _hxℓ⟩, hxε⟩ :=
    intermediate_value_Icc' hn2 (continuousOn_robinParameter hX1) hmem
  have hx1 : 1 < x := hX1.trans_le hXx
  let N : ℕ := robinExtremalAt x
  have hNpos : 0 < N := robinExtremal_pos _ _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hθ := hX₀ x (hXX₀.trans hXx)
  have hθN : Chebyshev.theta x ≤ Real.log (N : ℝ) :=
    theta_le_log_robinExtremalAt hx1
  have hu1 : 1 < Real.log (N : ℝ) := by linarith
  have hlarge : N₀ ≤ N := by
    have hlog := Real.log_le_sub_one_of_pos hNR
    have : (N₀ : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hR := hN₀ N hlarge (isColossallyAbundant_robinExtremalAt hx1)
  have hσN : (0 : ℝ) < sigma 1 N := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 N hNpos.ne'
  have hRdiv : (sigma 1 N : ℝ) / (N : ℝ) <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) := by
    apply (div_lt_iff₀ hNR).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hR
  have hRlog := (Real.log_lt_log_iff (div_pos hσN hNR)
    (mul_pos (Real.exp_pos _) (Real.log_pos hu1))).mpr hRdiv
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.log_pos hu1).ne', Real.log_exp] at hRlog
  have hlag := log_sigma_div_sub_le_robinExtremal (robinParameter_pos hx1)
    (fun p hp hpx => robinExponent_eq_zero_of_floor_lt hx1 hp hpx) (Nat.ne_of_gt hnpos)
  change Real.log ((sigma 1 n : ℝ) / (n : ℝ)) - robinParameter x * ℓ ≤
    Real.log ((sigma 1 N : ℝ) / (N : ℝ)) - robinParameter x * Real.log N at hlag
  rw [hxε] at hlag
  have hmis := log_log_sub_log_log_le hℓ1 hu1
  have he : (Real.log (N : ℝ) - ℓ) / (ℓ * Real.log ℓ) =
      ε * (Real.log (N : ℝ) - ℓ) := by dsimp [ε]; ring
  rw [he] at hmis
  have hlog : Real.log ((sigma 1 n : ℝ) / (n : ℝ)) <
      Real.eulerMascheroniConstant + Real.log (Real.log ℓ) := by linarith
  have hσ : (0 : ℝ) < sigma 1 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n hnpos.ne'
  rw [Real.log_lt_iff_lt_exp (div_pos hσ hnR), Real.exp_add,
    Real.exp_log (Real.log_pos hℓ1), div_lt_iff₀ hnR] at hlog
  simpa only [ℓ, mul_assoc, mul_left_comm, mul_comm] using hlog

/-- Robin's eventual criterion restricted to colossally abundant integers. -/
theorem riemannHypothesis_iff_eventually_robin_colossallyAbundant :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, IsColossallyAbundant n →
      (sigma 1 n : ℝ) <
        Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) :=
  riemannHypothesis_iff_eventually_robin.trans
    eventually_robin_iff_eventually_colossallyAbundant

end

end RHTower
