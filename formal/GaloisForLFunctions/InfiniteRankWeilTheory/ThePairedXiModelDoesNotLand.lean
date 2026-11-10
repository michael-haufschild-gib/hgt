import GaloisForLFunctions.InfiniteRankWeilTheory.ThePairedXiZerosHaveTheRiemannCount
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheLandingLaw

/-!
# Riemann zero counting does not force approaching zeros to land

All zeros of the paired Xi model are simple, lie strictly inside the
critical strip, and lie off the critical line. Their depths tend to zero.
The analytic zero configuration therefore approaches the line but fails
the landing law, while its count differs from the actual Xi count by at
most one.
-/

noncomputable section
open Complex Set Filter Topology
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

namespace GaloisForLFunctions.InfiniteRankWeilTheory

theorem pairedXiModel_zero_depth {s : ℂ} (hs : pairedXiModel s = 0) :
    ∃ n : ℕ, |s.re - 1 / 2| = pairedXiDepth n := by
  obtain ⟨q, rfl⟩ := (pairedXiModel_eq_zero_iff s).mp hs
  refine ⟨q.1, ?_⟩
  have hr : ((1 / 2 : ℂ) + pairedXiPoint q).re - 1 / 2 = (pairedXiPoint q).re := by
    norm_num [Complex.add_re]
  rw [hr, abs_pairedXiPoint_re]

theorem pairedXiModel_zero_strip {s : ℂ} (hs : pairedXiModel s = 0) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨n, hn⟩ := pairedXiModel_zero_depth hs
  have h := abs_lt.mp (hn.trans_lt (pairedXiDepth_lt_half n))
  constructor <;> linarith only [h.1, h.2]

/-- The model has no critical-line zero at any height. -/
theorem pairedXiModel_ne_zero_on_line {s : ℂ} (hs : s.re = 1 / 2) :
    pairedXiModel s ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := pairedXiModel_zero_depth hzero
  rw [hs, sub_self, abs_zero] at hn
  exact (pairedXiDepth_pos n).ne' hn.symm

theorem finite_pairedXiModel_zeros_abs_im_le (T : ℝ) :
    {s : ℂ | pairedXiModel s = 0 ∧ |s.im| ≤ T}.Finite := by
  have hf := (finite_pairedXiHeight_le T).prod (Set.toFinite (Set.univ : Set (Bool × Bool)))
  refine (hf.image (fun q : ℕ × Bool × Bool => (1 / 2 : ℂ) + pairedXiPoint q)).subset ?_
  rintro s ⟨hs, hT⟩
  obtain ⟨q, rfl⟩ := (pairedXiModel_eq_zero_iff s).mp hs
  refine ⟨q, ⟨?_, Set.mem_univ _⟩, rfl⟩
  simpa only [Set.mem_setOf_eq, Complex.add_im, (show (1 / 2 : ℂ).im = 0 by norm_num),
    zero_add, abs_pairedXiPoint_im] using hT

/-- The actual simple-zero divisor, with its analytic multiplicities. -/
def pairedXiConfig : ZeroConfig where
  carrier := {s | pairedXiModel s = 0}
  mult _ := 1
  one_le_mult _ _ := le_rfl
  strip s hs := ⟨(pairedXiModel_zero_strip hs).1.le, (pairedXiModel_zero_strip hs).2.le⟩
  reflect_mem s hs := by
    show pairedXiModel (1 - conj s) = 0
    rw [pairedXiModel_one_sub, pairedXiModel_conj, hs.out, map_zero]
  mult_reflect _ _ := rfl
  finite_window T₁ T₂ := by
    apply (finite_pairedXiModel_zeros_abs_im_le (|T₁| + |T₂|)).subset
    rintro s ⟨hs, h₁, h₂⟩
    refine ⟨hs, ?_⟩
    rw [abs_le]
    constructor <;> linarith only [h₁, h₂, neg_abs_le T₁, le_abs_self T₂,
      abs_nonneg T₁, abs_nonneg T₂]

/-- The configuration multiplicity is exactly the analytic vanishing order. -/
theorem pairedXiConfig_mult_eq_analyticOrder (s : ℂ) (hs : s ∈ pairedXiConfig.carrier) :
    analyticOrderAt pairedXiModel s = (pairedXiConfig.mult s : ℕ∞) := by
  obtain ⟨q, rfl⟩ := (pairedXiModel_eq_zero_iff s).mp hs
  exact analyticOrderAt_pairedXiModel q

theorem pairedXiConfig_approachesLine : ApproachesLine pairedXiConfig := by
  intro h hh
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_pairedXiDepth_zero.eventually (gt_mem_nhds hh))
  have hf := (Finset.range N).finite_toSet.prod (Set.toFinite (Set.univ : Set (Bool × Bool)))
  refine (hf.image (fun q : ℕ × Bool × Bool => (1 / 2 : ℂ) + pairedXiPoint q)).subset ?_
  rintro s ⟨hs, hre⟩
  obtain ⟨q, hq⟩ := (pairedXiModel_eq_zero_iff s).mp hs
  have hd : |s.re - 1 / 2| = pairedXiDepth q.1 := by
    rw [← hq]
    have hr : ((1 / 2 : ℂ) + pairedXiPoint q).re - 1 / 2 = (pairedXiPoint q).re := by
      norm_num [Complex.add_re]
    rw [hr, abs_pairedXiPoint_re]
  have hn : q.1 < N := by
    by_contra hn
    have hsmall := hN q.1 (Nat.le_of_not_gt hn)
    have hlarge := le_abs_self (s.re - 1 / 2)
    rw [hd] at hlarge
    linarith only [hsmall, hlarge, hre]
  exact ⟨q, ⟨Finset.mem_coe.mpr (Finset.mem_range.mpr hn), Set.mem_univ _⟩, hq⟩

theorem pairedXiConfig_infinite_right : (rightOf pairedXiConfig 0).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => (1 / 2 : ℂ) + pairedXiPoint (n, true, true)) := by
    intro n m h
    exact congrArg Prod.fst (pairedXiPoint_injective (add_left_cancel h))
  apply (infinite_range_of_injective hinj).mono
  rintro s ⟨n, rfl⟩
  refine ⟨(pairedXiModel_eq_zero_iff _).mpr ⟨(n, true, true), rfl⟩, ?_⟩
  change (1 / 2 : ℝ) + 0 < ((1 / 2 : ℂ) + pairedXiPoint (n, true, true)).re
  simpa [quartetSign] using pairedXiDepth_pos n

theorem not_pairedXiConfig_landingLaw : ¬ LandingLaw pairedXiConfig :=
  fun h => pairedXiConfig_infinite_right (h pairedXiConfig_approachesLine)

#print axioms pairedXiConfig_mult_eq_analyticOrder
#print axioms pairedXiConfig_approachesLine
#print axioms pairedXiConfig_infinite_right
#print axioms not_pairedXiConfig_landingLaw

end GaloisForLFunctions.InfiniteRankWeilTheory
