import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRoughHarmonicMeasureTensorizesUniformly
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeFormHasASpectralGapBelowItsPole

/-!
# Rough harmonic variance and prime defect

On a rough interval every prime ladder has logarithmic weight at least the
logarithm of the roughness threshold. Distinct ladder edges remain distinct
in the full defect sum, even when its bottom vertices alone are restricted.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The prime defect with its bottom vertex restricted to a rough interval. -/
def roughPoleDefect (Q N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ u ∈ roughInterval Q N, ∑ t ∈ Icc 1 (N / u),
    Λ t * (x (u * t) - x u / Real.sqrt t) ^ 2

theorem roughPoleDefect_nonneg (Q N : ℕ) (x : ℕ → ℝ) :
    0 ≤ roughPoleDefect Q N x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg vonMangoldt_nonneg (sq_nonneg _)

/-- Every rough ladder is paid by its distinct prime-power edges. -/
theorem log_mul_glauberForm_le_roughPoleDefect {Q : ℕ} (hQ : 2 ≤ Q)
    (N : ℕ) (x : ℕ → ℝ) :
    Real.log Q * glauberForm Q N (poleGauge x) ≤ roughPoleDefect Q N x := by
  set y := poleGauge x
  set T : ℕ → ℕ → ℝ := fun u t => Λ t * (x (u * t) - x u / Real.sqrt t) ^ 2
  have hT : ∀ u t, 0 ≤ T u t := fun _ _ =>
    mul_nonneg vonMangoldt_nonneg (sq_nonneg _)
  have hqL : ∀ q ∈ (Icc Q N).filter Nat.Prime,
      ∀ u ∈ (roughInterval Q N).filter (fun u => ¬ q ∣ u),
      Real.log Q * ladderVar q u N y ≤
        ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := by
    intro q hq u hu
    have hqp := (mem_filter.mp hq).2
    have hu1 : 1 ≤ u := (mem_roughInterval.mp (mem_filter.mp hu).1).1
    have hlQ : Real.log Q ≤ Real.log q :=
      Real.log_le_log (by exact_mod_cast (show 0 < Q by omega))
        (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hq).1).1)
    calc Real.log Q * ladderVar q u N y ≤ Real.log q * ladderVar q u N y :=
          mul_le_mul_of_nonneg_right hlQ (ladderVar_nonneg _ _ _ _)
      _ ≤ Real.log q * ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i),
          1 / ((u * q ^ i : ℕ) : ℝ) * (y (u * q ^ i) - y u) ^ 2 :=
          mul_le_mul_of_nonneg_left (ladderVar_le_base_edges q u N y)
            (Real.log_nonneg (by exact_mod_cast hqp.one_lt.le))
      _ = ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := by
          rw [mul_sum]
          refine sum_congr rfl fun i hi => ?_
          have hi1 := (mem_filter.mp hi).2
          simp only [T]
          rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hqp,
            sq_sub_div_sqrt_eq hu1 (Nat.one_le_pow _ _ hqp.pos) x]
  have hu : ∀ u ∈ roughInterval Q N, ∑ q ∈ (Icc Q N).filter Nat.Prime,
      ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) ≤
        ∑ t ∈ Icc 1 (N / u), T u t := by
    intro u hu
    have hu1 := (mem_roughInterval.mp hu).1
    rw [sum_sigma']
    rw [← sum_image (s := ((Icc Q N).filter Nat.Prime).sigma
        (fun q => (ladder q u N).filter (fun i => 1 ≤ i))) (g := fun z => z.1 ^ z.2)]
    · refine sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => hT u t)
      obtain ⟨⟨q, i⟩, hz, rfl⟩ := mem_image.mp ht
      obtain ⟨hq, hi⟩ := mem_sigma.mp hz
      have hqp := (mem_filter.mp hq).2
      have hiN := (mem_filter.mp (mem_filter.mp hi).1).2
      refine mem_Icc.mpr ⟨Nat.one_le_pow _ _ hqp.pos, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
      exact hiN
    · rintro ⟨q₁, i₁⟩ h₁ ⟨q₂, i₂⟩ h₂ heq
      obtain ⟨hq₁, hi₁⟩ := mem_sigma.mp h₁
      obtain ⟨hq₂, -⟩ := mem_sigma.mp h₂
      obtain ⟨rfl, rfl⟩ := prime_pow_inj (mem_filter.mp hq₁).2 (mem_filter.mp hq₂).2
        (mem_filter.mp hi₁).2 heq
      rfl
  rw [glauberForm, mul_sum]
  calc ∑ q ∈ (Icc Q N).filter Nat.Prime, Real.log Q *
        ∑ u ∈ (roughInterval Q N).filter (fun u => ¬ q ∣ u), ladderVar q u N y
      ≤ ∑ q ∈ (Icc Q N).filter Nat.Prime, ∑ u ∈ roughInterval Q N,
          ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := by
        refine sum_le_sum fun q hq => ?_
        rw [mul_sum]
        refine (sum_le_sum fun u hu => hqL q hq u hu).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun u _ _ => sum_nonneg fun i _ => hT u _
    _ = ∑ u ∈ roughInterval Q N, ∑ q ∈ (Icc Q N).filter Nat.Prime,
          ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := sum_comm
    _ ≤ ∑ u ∈ roughInterval Q N, ∑ t ∈ Icc 1 (N / u), T u t := sum_le_sum hu
    _ = roughPoleDefect Q N x := rfl

/-- Increasing roughness makes bounded-defect vectors close to constants in
the pole gauge, uniformly in the horizon. -/
theorem exists_rough_harmonicVar_le_primeDefect :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ N : ℕ, ∀ x : ℕ → ℝ,
      harmonicVar Q N (poleGauge x) ≤ C / Real.log Q * roughPoleDefect Q N x := by
  obtain ⟨C, hC, hvar⟩ := exists_rough_harmonicVar_le_glauberForm
  refine ⟨C, hC, fun Q hQ N x => ?_⟩
  have hlog : 0 < Real.log Q :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have henergy := log_mul_glauberForm_le_roughPoleDefect hQ N x
  have hbound : glauberForm Q N (poleGauge x) ≤ roughPoleDefect Q N x / Real.log Q := by
    rw [le_div_iff₀ hlog]
    simpa only [mul_comm] using henergy
  calc harmonicVar Q N (poleGauge x) ≤ C * glauberForm Q N (poleGauge x) := hvar Q N _
    _ ≤ C * (roughPoleDefect Q N x / Real.log Q) := mul_le_mul_of_nonneg_left hbound hC.le
    _ = C / Real.log Q * roughPoleDefect Q N x := by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

