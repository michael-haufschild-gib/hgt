import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDivisibilityEnergy
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardEnergyLimit
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardMean

/-!
# Uniform divisibility bounds for the actual full-positive source

The energy constant is retained up to arbitrary positive error, simultaneously
for every modulus before taking any radial limit. No masked residue is assumed.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

private theorem sparse_energy_damping (f : ℕ → ℂ) {s : ℝ} (hs : 1 < s) (n : ℕ) :
    (‖f n‖ ^ 2 / n) * (n : ℝ) ^ (-(s - 1)) = ‖f n‖ ^ 2 / (n : ℝ) ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : s ≠ 0)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show -(s - 1) = 1 - s by ring, Real.rpow_sub hn0, Real.rpow_one]
    field_simp

/-- A log-energy limit gives one radial neighborhood for all divisibility masks. -/
theorem uniform_divisibility_bound_of_log_energy {f : ℕ → ℂ} {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : Tendsto (fun N : ℕ =>
      weightPartialSum (fun n => ‖f n‖ ^ 2 / n) N / Real.log N) atTop (𝓝 K))
    (hf : ∀ s : ℝ, 1 < s → LSeriesSummable f (s : ℂ))
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ q : ℕ, q ≠ 0 →
      ‖((s : ℂ) - 1) * LSeries (divisibilityPart q f) (s : ℂ)‖ ^ 2 ≤ (K + e) / q := by
  obtain ⟨A, _, hA⟩ := exists_abel_energy_majorant (w := fun n => ‖f n‖ ^ 2 / n)
    (by simp) (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hK0 hK
    (show 0 < e / 2 by linarith)
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht := (((hid.sub_const 1).mul_const A).add (hid.const_mul (K + e / 2))).mul
    tendsto_sub_mul_tsum_nat_rpow
  simp only [sub_self, zero_mul, mul_one, zero_add] at ht
  have hnear := ht.eventually (gt_mem_nhds (show K + e / 2 < K + e by linarith))
  filter_upwards [hnear, self_mem_nhdsWithin] with s hb hs q hq
  have hs1 : 1 < s := hs
  obtain ⟨hes, heb⟩ := hA (s - 1) (by linarith)
  simp only [sparse_energy_damping f hs1] at hes heb
  rw [show 1 + (s - 1) = s by ring] at heb
  have hc := norm_divisibility_LSeries_sq_le_energy hq hs1 (hf s hs1) hes
  have hZ : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s :=
    tsum_nonneg fun n => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hdZ : 0 ≤ (s - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ s :=
    mul_nonneg (by linarith) hZ
  have hn : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [norm_mul, hn, mul_pow]
  calc
    _ ≤ (s - 1) ^ 2 *
        (((∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
          ∑' n : ℕ, 1 / (n : ℝ) ^ s) / q) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = (((s - 1) * ∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
        ((s - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ s)) / q := by ring
    _ ≤ (((s - 1) * A + (K + e / 2) * s) *
        ((s - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ s)) / q := by
      gcongr
    _ ≤ (K + e) / q := by gcongr

/-- Original full positivity supplies the sharp constant and uniformity in q. -/
theorem exists_forward_uniform_divisibility_energy {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0 ≤ K ∧
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, ‖sourceCoeff lam n‖ ^ 2 / n) / Real.log N)
        atTop (𝓝 K) ∧
      ∀ e : ℝ, 0 < e → ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ q : ℕ, q ≠ 0 →
        ‖((s : ℂ) - 1) * LSeries (divisibilityPart q (sourceCoeff lam)) (s : ℂ)‖ ^ 2 ≤
          (K + e) / q := by
  obtain ⟨K, hK0, hK⟩ := exists_forwardCoeff_energy_limit hW
  rw [forwardCoeff_eq_sourceCoeff] at hK
  refine ⟨K, hK0, hK, fun e he => ?_⟩
  have hweight : Tendsto (fun N : ℕ =>
      weightPartialSum (fun n => ‖sourceCoeff lam n‖ ^ 2 / n) N / Real.log N)
      atTop (𝓝 K) := by
    apply hK.congr
    intro N
    congr 1
    unfold weightPartialSum
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      have hn0 : n = 0 := by
        simp only [Finset.mem_Icc] at hn hn'
        omega
      simp [hn0]
  exact uniform_divisibility_bound_of_log_energy hK0 hweight
    (fun _ hs => (sourceCoeff_LSeries hW hs).1) he

/-- A single constant and interval control all moduli, hence all prime-power tails. -/
theorem exists_forward_divisibility_near_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C eta : ℝ, 0 ≤ C ∧ 0 < eta ∧ ∀ q : ℕ, q ≠ 0 →
      ∀ s : ℝ, 1 < s → s < 1 + eta →
        ‖((s : ℂ) - 1) * LSeries (divisibilityPart q (sourceCoeff lam)) (s : ℂ)‖ ^ 2 ≤
          C / q := by
  obtain ⟨K, hK, _, hbound⟩ := exists_forward_uniform_divisibility_energy hW
  obtain ⟨u, hu, hub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hbound 1 zero_lt_one)
  refine ⟨K + 1, u - 1, by linarith, sub_pos.mpr hu, fun q hq s hs hsu => ?_⟩
  exact hub ⟨hs, by linarith⟩ q hq

end RHTower.WeilSingularArithmetic
