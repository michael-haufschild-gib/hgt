import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonOscillationEnergy
import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonIntegerVariance
import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonPositiveCoercivity
import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonCoercivityWitness

/-!
# Sharp doubling scale and the fixed-horizon obstruction

Every window N >= 1024 admits an exact doubling-resonant cosine with energy at most 384
and squared error about every constant at least N/16. Thus any valid coercivity constant
is at least N/6144; the positive upper bound is 6N. This includes odd window endpoints.
For every fixed finite dilation horizon, the prime-count witness rules out one constant
valid on all windows. These statements concern the existing clipped integer energies.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- Exact doubling resonance supplies a witness on every sufficiently large window. -/
theorem exists_doubling_window_witness (N : ℕ) (hN : 1024 ≤ N) :
    ∃ f : ℕ → ℝ,
      (∀ c : ℝ, (N : ℝ) / 16 ≤ ∑ n ∈ Icc 1 N, (f n - c) ^ 2) ∧
      biScaleJointEnergy 2 N f ≤ 384 := by
  let M := N / 2
  let t := 2 * Real.pi / Real.log 2
  let a := -(t * Real.log (2 * M : ℕ))
  let f := logOscillation t a
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloglo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hloghi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have ht1 : 1 ≤ t := by
    apply (le_div_iff₀ hlogpos).mpr
    nlinarith [Real.pi_gt_three]
  have ht16 : t ≤ 16 := by
    apply (div_le_iff₀ hlogpos).mpr
    nlinarith [Real.pi_lt_four]
  have htpos : 0 < t := by linarith
  have hres : t * Real.log 2 = 2 * Real.pi := by
    dsimp [t]
    field_simp
  have hM : 512 ≤ M := by dsimp [M]; omega
  have hMpos : 0 < M := by omega
  have h2M : 2 * M ≤ N := by dsimp [M]; omega
  have hNupper : N ≤ 2 * M + 1 := by dsimp [M]; omega
  refine ⟨f, ?_, ?_⟩
  · intro c
    have hv := integer_window_variance_lower_bound M hMpos 1 t c htpos (by simpa using hres)
    change (M : ℝ) * Real.log 2 / 2 - 2 * t ≤
      ∑ n ∈ Icc 1 (2 * M), (f n - c) ^ 2 at hv
    have hMr : (512 : ℝ) ≤ M := by exact_mod_cast hM
    have hNr : (N : ℝ) ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast hNupper
    have hlo : (N : ℝ) / 16 ≤ (M : ℝ) * Real.log 2 / 2 - 2 * t := by
      nlinarith [mul_le_mul_of_nonneg_left hloglo (show (0 : ℝ) ≤ M by positivity)]
    refine (hlo.trans hv).trans ?_
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
      exact mem_Icc.mpr ⟨hn1, hnM.trans h2M⟩
    · intro n _ _
      exact sq_nonneg _
  · have hadd := logOscillation_additiveStepEnergy N t a ht1
    have hdil := logOscillation_multiplicativeScaleEnergy 2 N t a 0 (by norm_num) (by
      intro k hk2 hk
      have hk_eq : k = 2 := by omega
      subst k
      refine ⟨1, ?_⟩
      simp [hres])
    change additiveStepEnergy N f ≤ 24 * t at hadd
    change multiplicativeScaleEnergy 2 N f ≤ (2 : ℝ) * N * 0 ^ 2 at hdil
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hdil
    unfold biScaleJointEnergy
    linarith

/-- A constant controls distance to some constant function on the requested window. -/
def WindowCoercivityBound (K N : ℕ) (C : ℝ) : Prop :=
  ∀ f : ℕ → ℝ, ∃ c : ℝ,
    (∑ n ∈ Icc 1 N, (f n - c) ^ 2) ≤ C * biScaleJointEnergy K N f

theorem windowCoercivityBound_six_mul (K N : ℕ) (hK : 2 ≤ K) :
    WindowCoercivityBound K N (6 * N) := by
  intro f
  exact ⟨f 1, window_coercivity K N hK f⟩

/-- The linear upper bound has the sharp order on every sufficiently large window. -/
theorem doubling_coercivity_constant_lower_bound (N : ℕ) (hN : 1024 ≤ N)
    (C : ℝ) (hC : WindowCoercivityBound 2 N C) : (N : ℝ) / 6144 ≤ C := by
  obtain ⟨f, hv, he⟩ := exists_doubling_window_witness N hN
  obtain ⟨c, hc⟩ := hC f
  have hNr : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hCnonneg : 0 ≤ C := by
    by_contra h
    have hbad : C * biScaleJointEnergy 2 N f ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (biScaleJointEnergy_nonneg 2 N f)
    linarith [hv c]
  have hprod := mul_le_mul_of_nonneg_left he hCnonneg
  nlinarith [hv c]

/-- No fixed finite dilation horizon controls all window sizes with one constant. -/
theorem not_uniform_window_coercivity (K : ℕ) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, WindowCoercivityBound K N C := by
  rintro ⟨C, hC⟩
  let B : ℝ := 384 + 65536 * (K : ℝ) ^ 3
  obtain ⟨Q, hQ⟩ := exists_nat_gt (C * B)
  let d := (SieveMoments.oddPrimeModes (2 * K)).card
  let R : ℝ := (Q + 1 : ℕ)
  let N := 1024 * (Q + 1) ^ (d + 2)
  obtain ⟨f, hv, he⟩ := exists_prime_count_window_witness K Q
  change ∀ c : ℝ, (N : ℝ) / 16 ≤ ∑ n ∈ Icc 1 N, (f n - c) ^ 2 at hv
  change biScaleJointEnergy K N f ≤ B * R ^ d at he
  obtain ⟨c, hc⟩ := hC N f
  have hNpos : 0 < (N : ℝ) / 16 := by dsimp [N]; positivity
  have hCnonneg : 0 ≤ C := by
    by_contra h
    have hbad : C * biScaleJointEnergy K N f ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (biScaleJointEnergy_nonneg K N f)
    linarith [hv c]
  have hbound : (N : ℝ) / 16 ≤ C * (B * R ^ d) :=
    (hv c).trans (hc.trans (mul_le_mul_of_nonneg_left he hCnonneg))
  have hNcast : (N : ℝ) / 16 = 64 * R ^ d * R ^ 2 := by
    dsimp [N, R]
    push_cast
    rw [pow_add]
    ring
  rw [hNcast] at hbound
  have hR : 1 ≤ R := by dsimp [R]; exact_mod_cast (show 1 ≤ Q + 1 by omega)
  have hQR : (Q : ℝ) < R := by dsimp [R]; push_cast; linarith
  have hscale : C * B < 64 * R ^ 2 := by nlinarith
  have hpow : 0 < R ^ d := by positivity
  have hstrict := mul_lt_mul_of_pos_right hscale hpow
  nlinarith

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
