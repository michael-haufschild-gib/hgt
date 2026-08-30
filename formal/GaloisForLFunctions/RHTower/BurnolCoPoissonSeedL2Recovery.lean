import GaloisForLFunctions.RHTower.BurnolCoPoissonHeadConstant
import GaloisForLFunctions.RHTower.BurnolCoPoissonCorrectionConstant
import GaloisForLFunctions.RHTower.ConstrainedProlateTrueApertureMetric
import GaloisForLFunctions.HTGeometry.LineScalingL2

/-!
# Finite Möbius recovery of the `L²` regularity of a co-Poisson seed

Burnol's source characterization needs the forward implication from a literal co-Poisson source
whose co-Poisson sum is in `L²` to an `L²` seed.  Compact multiplicative support makes every
rescaled co-Poisson ray finite.  Finite divisor Möbius inversion then recovers the seed pointwise
from finitely many rescaled co-Poisson values and the correction constant.  The correction is only
placed on the compact source window, where it is square-integrable.

No convergence interchange, spectral assertion, or RH assumption occurs in this module.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace BigOperators

noncomputable section

namespace RHTower

theorem burnolSeed_div_nat_eq_zero_of_lt {b : ℝ} {g : ℝ → ℂ}
    (hb : 0 < b) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {t : ℝ} (ht : t ∈ Icc b b⁻¹) {N k : ℕ}
    (hN : b⁻¹ / b ≤ (N : ℝ)) (hk : (N : ℝ) < (k : ℝ)) :
    g (t / (k : ℝ)) = 0 := by
  by_contra hzero
  have hmem : t / (k : ℝ) ∈ Icc b b⁻¹ :=
    hsupp (Function.mem_support.mpr hzero)
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have hNpos : (0 : ℝ) < (N : ℝ) :=
      lt_of_lt_of_le (div_pos (inv_pos.mpr hb) hb) hN
    exact hNpos.trans hk
  have hkb : (k : ℝ) * b ≤ t := by
    rw [mul_comm]
    exact (le_div_iff₀ hkpos).mp hmem.1
  have hk_le : (k : ℝ) ≤ b⁻¹ / b := by
    rw [le_div_iff₀ hb]
    exact hkb.trans ht.2
  linarith

/-- On the source window, every scaled co-Poisson ray has a uniform finite cutoff. -/
theorem burnolSeed_scaled_tsum_eq_finset {b : ℝ} {g : ℝ → ℂ}
    (hb : 0 < b) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {t : ℝ} (ht : t ∈ Icc b b⁻¹) {N n : ℕ}
    (hN : b⁻¹ / b ≤ (N : ℝ)) (hn : 1 ≤ n) :
    (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      g ((t / (n : ℝ)) / ((m + 1 : ℕ) : ℝ))) =
      ∑ m ∈ Finset.range N, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        g ((t / (n : ℝ)) / ((m + 1 : ℕ) : ℝ)) := by
  refine tsum_eq_sum ?_
  intro m hm
  have hmN : N ≤ m := Nat.not_lt.mp (by simpa using hm)
  have hkm : N < n * (m + 1) := by
    calc
      N < m + 1 := Nat.lt_succ_of_le hmN
      _ ≤ n * (m + 1) := by
        exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt hn)
  have hzero : g ((t / (n : ℝ)) / ((m + 1 : ℕ) : ℝ)) = 0 := by
    have hrewrite : (t / (n : ℝ)) / ((m + 1 : ℕ) : ℝ) =
        t / ((n * (m + 1) : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [hrewrite]
    apply burnolSeed_div_nat_eq_zero_of_lt hb hsupp ht hN
    exact_mod_cast hkm
  rw [hzero, mul_zero]

/-- Divisor-filtered finite aperture tails are exactly multiplication-indexed finite rays. -/
theorem finiteApertureRaySum_eq_mul_index {N n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    finiteApertureRaySum N a n =
      ∑ m ∈ Finset.Icc 1 (N / n), a (n * m) := by
  rw [finiteApertureRaySum]
  refine Finset.sum_bij (fun k _ => k / n) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hk.1.2⟩
    rw [Nat.le_div_iff_mul_le hn]
    have hle : n ≤ k := Nat.le_of_dvd (by omega) hk.2
    simpa using hle
  · intro k₁ hk₁ k₂ hk₂ hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk₁ hk₂
    rw [← Nat.mul_div_cancel' hk₁.2, ← Nat.mul_div_cancel' hk₂.2, hq]
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    refine ⟨n * m, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right _ _⟩
      · exact Nat.mul_pos hn hm.1
      · have hmul : m * n ≤ N := (Nat.le_div_iff_mul_le hn).mp hm.2
        simpa [Nat.mul_comm] using hmul
    · simpa [Nat.mul_comm] using Nat.mul_div_left m hn
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    rw [Nat.mul_div_cancel' hk.2]

theorem finset_Icc_one_eq_range_succ (N : ℕ) :
    Finset.Icc 1 N = (Finset.range N).map ⟨Nat.succ, Nat.succ_injective⟩ := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range]
  change 1 ≤ k ∧ k ≤ N ↔ ∃ m, m < N ∧ m + 1 = k
  constructor
  · intro hk
    refine ⟨k - 1, by omega, ?_⟩
    omega
  · rintro ⟨m, hm, rfl⟩
    omega

theorem burnolSeed_scaled_tsum_eq_finset_Icc {b : ℝ} {g : ℝ → ℂ}
    (hb : 0 < b) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {t : ℝ} (ht : t ∈ Icc b b⁻¹) {N n : ℕ}
    (hN : b⁻¹ / b ≤ (N : ℝ)) (hn : 1 ≤ n) :
    (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      g ((t / (n : ℝ)) / ((m + 1 : ℕ) : ℝ))) =
      ∑ m ∈ Finset.Icc 1 N, ((m : ℝ) : ℂ)⁻¹ *
        g ((t / (n : ℝ)) / (m : ℝ)) := by
  rw [burnolSeed_scaled_tsum_eq_finset hb hsupp ht hN hn,
    finset_Icc_one_eq_range_succ]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro m hm
  simp [Nat.succ_eq_add_one]

theorem burnolSeed_sum_Icc_div_eq {b : ℝ} {g : ℝ → ℂ}
    (hb : 0 < b) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {t : ℝ} (ht : t ∈ Icc b b⁻¹) {N n : ℕ}
    (hN : b⁻¹ / b ≤ (N : ℝ)) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 (N / n), ((m : ℝ) : ℂ)⁻¹ *
      g ((t / (n : ℝ)) / (m : ℝ))) =
      ∑ m ∈ Finset.Icc 1 N, ((m : ℝ) : ℂ)⁻¹ *
        g ((t / (n : ℝ)) / (m : ℝ)) := by
  apply Finset.sum_subset
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨hm'.1, hm'.2.trans (Nat.div_le_self _ _)⟩
  · intro m hmN hmdiv
    have hmN' := Finset.mem_Icc.mp hmN
    have hlt : N / n < m := by
      by_contra hnot
      exact hmdiv (Finset.mem_Icc.mpr ⟨hmN'.1, Nat.le_of_not_gt hnot⟩)
    have hnm : N < n * m := by
      have hmul : N < m * n := (Nat.div_lt_iff_lt_mul hn).mp hlt
      simpa [Nat.mul_comm] using hmul
    have hzero : g ((t / (n : ℝ)) / (m : ℝ)) = 0 := by
      have hre : (t / (n : ℝ)) / (m : ℝ) = t / ((n * m : ℕ) : ℝ) := by
        push_cast
        field_simp
      rw [hre]
      apply burnolSeed_div_nat_eq_zero_of_lt hb hsupp ht hN
      exact_mod_cast hnm
    rw [hzero, mul_zero]

theorem finiteApertureRaySum_eq_burnolSeed_scaled_sum
    {b : ℝ} {g : ℝ → ℂ}
    (hb : 0 < b) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {t : ℝ} (ht : t ∈ Icc b b⁻¹) {N n : ℕ}
    (hN : b⁻¹ / b ≤ (N : ℝ)) (hn : 1 ≤ n) :
    finiteApertureRaySum N
      (fun k => ((k : ℝ) : ℂ)⁻¹ * g (t / (k : ℝ))) n =
      ((n : ℝ) : ℂ)⁻¹ *
        ∑ m ∈ Finset.Icc 1 N, ((m : ℝ) : ℂ)⁻¹ *
          g ((t / (n : ℝ)) / (m : ℝ)) := by
  rw [finiteApertureRaySum_eq_mul_index (Nat.zero_lt_of_lt hn)]
  calc
    (∑ m ∈ Finset.Icc 1 (N / n), ((n * m : ℕ) : ℂ)⁻¹ *
        g (t / ((n * m : ℕ) : ℝ))) =
        ((n : ℝ) : ℂ)⁻¹ *
          ∑ m ∈ Finset.Icc 1 (N / n), ((m : ℝ) : ℂ)⁻¹ *
            g ((t / (n : ℝ)) / (m : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hn0 : (((n : ℝ) : ℂ)) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr
          (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn) : (0 : ℝ) < (n : ℝ)))
      have hm0 : (((m : ℝ) : ℂ)) ≠ 0 := by
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        exact Complex.ofReal_ne_zero.mpr
          (ne_of_gt (Nat.cast_pos.mpr hmpos : (0 : ℝ) < (m : ℝ)))
      have harg : t / ((n * m : ℕ) : ℝ) =
          (t / (n : ℝ)) / (m : ℝ) := by
        push_cast
        field_simp
      rw [harg]
      push_cast
      field_simp
    _ = ((n : ℝ) : ℂ)⁻¹ *
          ∑ m ∈ Finset.Icc 1 N, ((m : ℝ) : ℂ)⁻¹ *
            g ((t / (n : ℝ)) / (m : ℝ)) := by
      rw [burnolSeed_sum_Icc_div_eq hb hsupp ht hN (Nat.zero_lt_of_lt hn)]

theorem finiteApertureRaySum_eq_scaled_coPoissonRightSum_add_correction
    {b : ℝ} {g : ℝ → ℂ}
    (hb : 0 < b) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {t : ℝ} (ht : t ∈ Icc b b⁻¹) {N n : ℕ}
    (hN : b⁻¹ / b ≤ (N : ℝ)) (hn : 1 ≤ n) :
    finiteApertureRaySum N
      (fun k => ((k : ℝ) : ℂ)⁻¹ * g (t / (k : ℝ))) n =
      ((n : ℝ) : ℂ)⁻¹ *
        (burnolCoPoissonRightSum g (t / (n : ℝ)) + coPoissonCorrectionConstant g) := by
  rw [finiteApertureRaySum_eq_burnolSeed_scaled_sum hb hsupp ht hN hn,
    ← burnolSeed_scaled_tsum_eq_finset_Icc hb hsupp ht hN hn]
  congr 1
  have htpos : 0 < t := lt_of_lt_of_le hb ht.1
  have htnpos : 0 < t / (n : ℝ) :=
    div_pos htpos (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
  rw [burnolCoPoissonRightSum_eq_sub_correction, abs_of_pos htnpos]
  ring

theorem burnolSeed_eq_finiteMobius_scaled_coPoisson
    {b : ℝ} {g : ℝ → ℂ}
    (hb : 0 < b) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {t : ℝ} (ht : t ∈ Icc b b⁻¹) {N : ℕ}
    (hN : b⁻¹ / b ≤ (N : ℝ)) :
    g t = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) *
      (((n : ℝ) : ℂ)⁻¹ *
        (burnolCoPoissonRightSum g (t / (n : ℝ)) + coPoissonCorrectionConstant g)) := by
  have hNnat : 1 ≤ N := by
    have hNpos : (0 : ℝ) < (N : ℝ) :=
      lt_of_lt_of_le (div_pos (inv_pos.mpr hb) hb) hN
    exact_mod_cast hNpos
  calc
    g t = finiteApertureMobiusReconstruction N
        (fun k => ((k : ℝ) : ℂ)⁻¹ * g (t / (k : ℝ))) := by
      symm
      simpa using finiteApertureMobiusReconstruction_eq hNnat
        (fun k => ((k : ℝ) : ℂ)⁻¹ * g (t / (k : ℝ)))
    _ = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) *
        (((n : ℝ) : ℂ)⁻¹ *
          (burnolCoPoissonRightSum g (t / (n : ℝ)) + coPoissonCorrectionConstant g)) := by
      rw [finiteApertureMobiusReconstruction]
      apply Finset.sum_congr rfl
      intro n hn
      rw [finiteApertureRaySum_eq_scaled_coPoissonRightSum_add_correction hb hsupp ht hN
        (Finset.mem_Icc.mp hn).1]

/-- Every literal compact co-Poisson source seed is square-integrable. -/
theorem BurnolCoPoissonSource.seed_memLp_two
    {b : ℝ} (hb : 0 < b) (src : BurnolCoPoissonSource b) :
    MemLp src.seed 2 volume := by
  let N : ℕ := ⌈b⁻¹ / b⌉₊
  let F : ℝ → ℂ := burnolCoPoissonRightSum src.seed
  let C : ℂ := coPoissonCorrectionConstant src.seed
  let s : Finset ℕ := Finset.Icc 1 N
  let R : ℝ → ℂ := fun t => ∑ n ∈ s, (ArithmeticFunction.moebius n : ℂ) *
    (((n : ℝ) : ℂ)⁻¹ * (F (t / (n : ℝ)) + C))
  have hN : b⁻¹ / b ≤ (N : ℝ) := by
    exact Nat.le_ceil _
  have hF : MemLp F 2 volume := by
    exact (memLp_congr_ae src.vector_eq_sum).mp
      (Lp.memLp (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2))
  have hterm : ∀ n ∈ s, MemLp (fun t : ℝ =>
      (ArithmeticFunction.moebius n : ℂ) * (((n : ℝ) : ℂ)⁻¹ * F (t / (n : ℝ)))) 2 volume := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR0 : ((n : ℝ)⁻¹) ≠ 0 := by
      exact inv_ne_zero (ne_of_gt (Nat.cast_pos.mpr hnpos))
    have hscale : MemLp (fun t : ℝ => F ((n : ℝ)⁻¹ * t)) 2 volume :=
      GaloisForLFunctions.HTGeometry.memLp_two_comp_const_mul hF hnR0
    have hscale' : MemLp (fun t : ℝ => F (t / (n : ℝ))) 2 volume := by
      exact (memLp_congr_ae (Filter.Eventually.of_forall fun t => by
        congr 1
        field_simp)).mpr hscale
    simpa only [mul_assoc] using hscale'.const_mul
      ((ArithmeticFunction.moebius n : ℂ) * ((n : ℝ) : ℂ)⁻¹)
  have hsum : MemLp (fun t : ℝ => ∑ n ∈ s,
      (ArithmeticFunction.moebius n : ℂ) * (((n : ℝ) : ℂ)⁻¹ * F (t / (n : ℝ)))) 2 volume :=
    memLp_finsetSum s hterm
  have hleft : MemLp ((Icc b b⁻¹).indicator fun t : ℝ => ∑ n ∈ s,
      (ArithmeticFunction.moebius n : ℂ) * (((n : ℝ) : ℂ)⁻¹ * F (t / (n : ℝ))) ) 2 volume :=
    hsum.indicator measurableSet_Icc
  have hright : MemLp ((Icc b b⁻¹).indicator fun _ : ℝ => ∑ n ∈ s,
      (ArithmeticFunction.moebius n : ℂ) * (((n : ℝ) : ℂ)⁻¹ * C)) 2 volume := by
    exact memLp_indicator_const 2 measurableSet_Icc _ (Or.inr measure_Icc_lt_top.ne)
  have hsplit : (Icc b b⁻¹).indicator R =
      (Icc b b⁻¹).indicator (fun t : ℝ => ∑ n ∈ s,
        (ArithmeticFunction.moebius n : ℂ) * (((n : ℝ) : ℂ)⁻¹ * F (t / (n : ℝ)))) +
      (Icc b b⁻¹).indicator (fun _ : ℝ => ∑ n ∈ s,
        (ArithmeticFunction.moebius n : ℂ) * (((n : ℝ) : ℂ)⁻¹ * C)) := by
    funext t
    by_cases ht : t ∈ Icc b b⁻¹
    · simp only [Set.indicator_of_mem ht, Pi.add_apply]
      change (∑ n ∈ s, (ArithmeticFunction.moebius n : ℂ) *
        (((n : ℝ) : ℂ)⁻¹ * (F (t / (n : ℝ)) + C))) =
        (∑ n ∈ s, (ArithmeticFunction.moebius n : ℂ) *
          (((n : ℝ) : ℂ)⁻¹ * F (t / (n : ℝ)))) +
        ∑ n ∈ s, (ArithmeticFunction.moebius n : ℂ) * (((n : ℝ) : ℂ)⁻¹ * C)
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    · simp only [Set.indicator_of_notMem ht, Pi.add_apply, zero_add]
  have hseed : src.seed = (Icc b b⁻¹).indicator R := by
    funext t
    by_cases ht : t ∈ Icc b b⁻¹
    · rw [Set.indicator_of_mem ht]
      simpa [R, F, C, s] using
        burnolSeed_eq_finiteMobius_scaled_coPoisson hb src.seed_support ht hN
    · rw [Set.indicator_of_notMem ht]
      by_contra hzero
      exact ht (src.seed_support (Function.mem_support.mpr hzero))
  rw [hseed, hsplit]
  exact hleft.add hright

end RHTower
