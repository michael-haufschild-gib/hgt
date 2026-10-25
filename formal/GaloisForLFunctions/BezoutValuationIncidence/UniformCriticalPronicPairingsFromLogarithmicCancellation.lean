import GaloisForLFunctions.BezoutValuationIncidence.UniformTruncatedMobiusReceiversHaveZeroTrivialDensity
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusEndpoint

/-!
Two logarithms of cancellation at the square-root prefix scale give a common
summable envelope for pronic energies and mixed smooth pairings. A linear
majorant pays the finite head uniformly over the sequence family.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Two logarithms at the critical prefix scale control both the mixed and squared pronic cells. -/
theorem critical_pronic_mixed_add_square_le {n : ℕ} {x B : ℝ}
    (hn : 1 ≤ n) (hB : 0 ≤ B) (hlog : 1 ≤ Real.log (n : ℝ))
    (hx : |x| ≤ B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2) :
    (Real.sqrt (n : ℝ) * |x| + x ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (B + B ^ 2) / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL1 : 1 ≤ Real.log (n : ℝ) ^ 2 := one_le_pow₀ hlog
  have hL0 : 0 < Real.log (n : ℝ) ^ 2 := zero_lt_one.trans_le hL1
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hx' : |x| ≤ B * Real.sqrt (n : ℝ) :=
    hx.trans (div_le_self (by positivity) hL1)
  have hmix : Real.sqrt (n : ℝ) * |x| ≤ B * n / Real.log (n : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg (n : ℝ))
    exact h.trans_eq (by
      rw [show Real.sqrt (n : ℝ) * (B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2) =
        B * Real.sqrt (n : ℝ) ^ 2 / Real.log (n : ℝ) ^ 2 by ring, hs])
  have hsq : x ^ 2 ≤ B ^ 2 * n / Real.log (n : ℝ) ^ 2 := by
    have h := mul_le_mul hx' hx (abs_nonneg x) (by positivity : 0 ≤ B * Real.sqrt (n : ℝ))
    rw [← pow_two, sq_abs] at h
    exact h.trans_eq (by
      rw [show (B * Real.sqrt (n : ℝ)) *
        (B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2) =
          B ^ 2 * Real.sqrt (n : ℝ) ^ 2 / Real.log (n : ℝ) ^ 2 by ring, hs])
  calc
    _ ≤ (B * n / Real.log (n : ℝ) ^ 2 + B ^ 2 * n / Real.log (n : ℝ) ^ 2) /
        ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right (add_le_add hmix hsq) (by positivity)
    _ = (B + B ^ 2) / (((n : ℝ) + 1) * Real.log (n : ℝ) ^ 2) := by
      field_simp [hn0.ne', hL0.ne']
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hn0 hL0)
      (mul_le_mul_of_nonneg_right (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) hL0.le)

/-- A common logarithmic critical-prefix bound has one summable envelope for mixed and square cells. -/
theorem exists_summable_critical_pronic_envelope {ι : Type*} {f : ι → ℕ → ℝ}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlinear : ∀ i : ι, ∀ n : ℕ, 1 ≤ n → |f i n| ≤ A * n)
    (hlog : ∀ᶠ n : ℕ in atTop, ∀ i,
      |f i n| ≤ B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2) :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ n, 0 ≤ g n) ∧ ∀ i : ι, ∀ n : ℕ,
      (Real.sqrt (n : ℝ) * |f i n| + f i n ^ 2) /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤ g n := by
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlog.and ((hloglim.eventually_ge_atTop 1).and (eventually_ge_atTop 1)))
  let p : ℕ → ℝ := fun n => if n < N then A * n else
    B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2
  have hp (n : ℕ) : 0 ≤ p n := by
    dsimp only [p]
    split_ifs <;> positivity
  let g : ℕ → ℝ := fun n => (Real.sqrt (n : ℝ) * p n + p n ^ 2) /
    ((n : ℝ) * ((n : ℝ) + 1))
  have hg0 (n : ℕ) : 0 ≤ g n := by dsimp only [g]; positivity
  have hsum : Summable g := by
    apply (pm_summable_reciprocal_log_sq.mul_left (B + B ^ 2)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' := hN n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 n)]
    change (Real.sqrt (n : ℝ) * p n + p n ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) ≤ _
    have hcell := critical_pronic_mixed_add_square_le hn'.2.2 hB hn'.2.1
      (x := p n) (by simp only [p, if_neg (not_lt.mpr hn), abs_of_nonneg (by positivity :
        0 ≤ B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2), le_refl])
    simpa only [abs_of_nonneg (hp n), mul_one_div] using hcell
  refine ⟨g, hsum, hg0, fun i n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul, div_zero, g, le_refl]
  · have hx : |f i n| ≤ p n := by
      dsimp only [p]
      split_ifs with h
      · exact hlinear i n hn
      · exact (hN n (not_lt.mp h)).1 i
    have hsq : f i n ^ 2 ≤ p n ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
    exact div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)) hsq) (by positivity)

/-- Critical logarithmic prefix bounds give common finite energy and absolutely summable smooth pairings. -/
theorem exists_uniform_critical_pronic_mixed_and_energy_bound {ι : Type*} {f : ι → ℕ → ℝ}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlinear : ∀ i : ι, ∀ n : ℕ, 1 ≤ n → |f i n| ≤ A * n)
    (hlog : ∀ᶠ n : ℕ in atTop, ∀ i,
      |f i n| ≤ B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ι, ∀ T : ℕ,
      (∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * |f i n| /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤ C ∧ pronicNorm (f i) T ^ 2 ≤ C := by
  obtain ⟨g, hg, hg0, hbound⟩ := exists_summable_critical_pronic_envelope hA hB hlinear hlog
  refine ⟨∑' n : ℕ, g n, tsum_nonneg hg0, fun i T => ?_⟩
  have hsum : (∑ n ∈ Icc 1 T,
      (Real.sqrt (n : ℝ) * |f i n| + f i n ^ 2) / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        ∑' n : ℕ, g n :=
    (sum_le_sum fun n _ => hbound i n).trans (hg.sum_le_tsum (Icc 1 T) (fun n _ => hg0 n))
  constructor
  · refine (sum_le_sum fun n _ => ?_).trans hsum
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (by positivity)
  · rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
    refine (sum_le_sum fun n _ => ?_).trans hsum
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

#print axioms critical_pronic_mixed_add_square_le
#print axioms exists_summable_critical_pronic_envelope
#print axioms exists_uniform_critical_pronic_mixed_and_energy_bound
end GaloisForLFunctions.BezoutValuationIncidence
