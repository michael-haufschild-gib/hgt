import GaloisForLFunctions.RHTower.ChronologicalHeatL2

/-!
# Damped chronological repair has exactly the raw L² convergence condition

The finite damped-minus-raw residual uses only strict earlier cutoffs N/d, d≥2.
Its L² norm is bounded by 2ε(1+C) when every earlier raw error norm is at most C.
A strong-induction boundedness argument proves that for every schedule ε_N→0
inside [0,1/2], the damped residuals tend to zero in the actual L²(0,∞) norm
if and only if the raw Möbius residuals do. This excludes damping as a way
to improve the convergence question; it does not assert raw nonconvergence.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RHTower

private theorem chronological_bounded_of_tendsto {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, r n ≤ C := by
  have he : ∀ᶠ n in atTop, r n < 1 := hr.eventually (gt_mem_nhds (by linarith : (0:ℝ)<1))
  obtain ⟨K, hK⟩ := eventually_atTop.mp he
  let C := 1 + ∑ i ∈ Finset.range K, |r i|
  have hs : 0 ≤ ∑ i ∈ Finset.range K, |r i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro n
  by_cases hn : n < K
  · have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range K) => abs_nonneg (r i))
      (Finset.mem_range.mpr hn)
    have ha := le_abs_self (r n)
    dsimp [C]
    linarith
  · have hh := hK n (by omega)
    dsimp [C]
    linarith

theorem chronologicalVolterra_zero_convergence_iff {r s e : ℕ → ℝ}
    (hr0 : ∀ n, 0 ≤ r n) (hs0 : ∀ n, 0 ≤ s n)
    (he : Tendsto e atTop (𝓝 0))
    (hcmp : ∀ N C, 0 ≤ C → (∀ k < N, r k ≤ C) →
      s N ≤ r N + e N*(1+C) ∧ r N ≤ s N + e N*(1+C)) :
    Tendsto s atTop (𝓝 0) ↔ Tendsto r atTop (𝓝 0) := by
  constructor
  · intro hs
    have hes : ∀ᶠ n in atTop, e n < 1/4 ∧ s n < 1 :=
      (he.eventually (gt_mem_nhds (by linarith : (0:ℝ)<1/4))).and
        (hs.eventually (gt_mem_nhds (by linarith : (0:ℝ)<1)))
    obtain ⟨K, hK⟩ := eventually_atTop.mp hes
    let C := 2 + ∑ i ∈ Finset.range K, r i
    have hsum : 0 ≤ ∑ i ∈ Finset.range K, r i := Finset.sum_nonneg (fun i _ => hr0 i)
    have hC : 2 ≤ C := by dsimp [C]; linarith
    have hb : ∀ N, r N ≤ C := by
      intro N
      induction N using Nat.strong_induction_on with
      | h N ih =>
        by_cases hN : N < K
        · have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range K) => hr0 i)
            (Finset.mem_range.mpr hN)
          dsimp [C]
          linarith
        · have hh := (hcmp N C (by linarith) ih).2
          have htail := hK N (by omega)
          have hp : e N*(1+C) ≤ (1/4)*(1+C) :=
            mul_le_mul_of_nonneg_right htail.1.le (by linarith)
          linarith
    have hupper := hs.add (he.mul_const (1+C))
    simp only [zero_mul, zero_add] at hupper
    exact squeeze_zero hr0 (fun N => (hcmp N C (by linarith) (fun k _ => hb k)).2) hupper
  · intro hr
    obtain ⟨C, hC, hb⟩ := chronological_bounded_of_tendsto hr
    have hupper := hr.add (he.mul_const (1+C))
    simp only [zero_mul, zero_add] at hupper
    exact squeeze_zero hs0 (fun N => (hcmp N C hC (fun k _ => hb k)).1) hupper

theorem chronologicalGeometric_tail_budget (ε : ℝ) (hε0 : 0 ≤ ε) (hεh : ε ≤ 1/2)
    (S : Finset ℕ) (hS : ∀ d ∈ S, 2 ≤ d) :
    ∑ d ∈ S, ε^(d-1) ≤ 2*ε := by
  have hg := hasSum_geometric_of_lt_one hε0 (by linarith : ε < 1)
  have he : (∑ d ∈ S, ε^(d-1)) = ε * ∑ d ∈ S, ε^(d-2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [show d-1=(d-2)+1 by have hh := hS d hd; omega, pow_succ, mul_comm]
  have hs : (∑ d ∈ S, ε^(d-2)) ≤ 1/(1-ε) := by
    calc
      _ = ∑ j ∈ S.image (fun d => d-2), ε^j := by
        rw [Finset.sum_image]
        intro a ha b hb he
        change a-2=b-2 at he
        have ha2 := hS a ha
        have hb2 := hS b hb
        omega
      _ ≤ ∑' j : ℕ, ε^j := hg.summable.sum_le_tsum _ (fun j _ => pow_nonneg hε0 j)
      _ = _ := by simpa only [one_div] using hg.tsum_eq
  have hi : 1/(1-ε) ≤ (2:ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1-ε)).mpr
    linarith
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left (hs.trans hi) hε0]

theorem chronologicalDampedHeatError_difference (ε : ℝ) (N : ℕ) (t : ℝ) :
    chronologicalDampedHeatError ε N t - chronologicalRawHeatError N t =
      ∑ d ∈ (Finset.Ioc 0 N).erase 1, (-ε)^(d-1) *
        (chronologicalRawHeatError (N/d) ((d:ℝ)*t) - Real.exp (-((d:ℝ)*t))) := by
  by_cases hN : N=0
  · subst N
    simp [chronologicalDampedHeatError, chronologicalRawHeatError]
  · have hmem : 1 ∈ Finset.Ioc 0 N := by simp; omega
    have he := chronologicalDampedHeatError_exact_remainder ε N t
    rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem] at he
    simp only [Nat.cast_one, one_mul, Nat.sub_self, pow_zero, Nat.div_one] at he
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith

theorem chronologicalDampedHeatError_perturbation (ε : ℝ) (N : ℕ) (C : ℝ)
    (hε0 : 0 ≤ ε) (hεh : ε ≤ 1/2) (hC : 0 ≤ C)
    (hprev : ∀ k < N, chronologicalL2Norm (chronologicalRawHeatError k) ≤ C) :
    chronologicalL2Norm (fun t => chronologicalDampedHeatError ε N t - chronologicalRawHeatError N t)
      ≤ 2*ε*(1+C) := by
  let S := (Finset.Ioc 0 N).erase 1
  have hS : ∀ d ∈ S, 2 ≤ d := by
    intro d hd
    have hh := Finset.mem_erase.mp hd
    have hp := (Finset.mem_Ioc.mp hh.2).1
    omega
  have hdf : ∀ d ∈ S, N/d < N := by
    intro d hd
    have hh := Finset.mem_erase.mp hd
    have hp := Finset.mem_Ioc.mp hh.2
    exact Nat.div_lt_self (by omega) (by have hh := hS d hd; omega)
  let F : ℕ → ℝ → ℝ := fun d t => (-ε)^(d-1) *
    (chronologicalRawHeatError (N/d) ((d:ℝ)*t) - Real.exp (-((d:ℝ)*t)))
  have hm (d : ℕ) (hd : d ∈ S) : MemLp (F d) 2 chronologicalPositiveVolume := by
    have hd0 : (0:ℝ) < d := by have hh := hS d hd; exact_mod_cast (by omega : 0 < d)
    exact ((chronological_memLp_dilate (chronologicalRawHeatError_memLp (N/d))
      (chronologicalRawHeatError_continuousOn (N/d)) hd0).sub
      (chronological_memLp_dilate chronologicalExponential_memLp
        (Real.continuous_exp.comp continuous_neg).continuousOn hd0)).const_mul _
  have hb (d : ℕ) (hd : d ∈ S) : chronologicalL2Norm (F d) ≤ ε^(d-1)*(1+C) := by
    have hd1 : (1:ℝ) ≤ d := by have hh := hS d hd; exact_mod_cast (by omega : 1 ≤ d)
    have hd0 : (0:ℝ) < d := by linarith
    have hf := chronological_memLp_dilate (chronologicalRawHeatError_memLp (N/d))
      (chronologicalRawHeatError_continuousOn (N/d)) hd0
    have hsub := lpNorm_sub_le hf (by simp : (1:ENNReal) ≤ 2)
      (g := fun t : ℝ => Real.exp (-((d:ℝ)*t)))
    have hr := chronologicalL2Norm_dilate_le (chronologicalRawHeatError_continuousOn (N/d)) hd1
    have hx := chronologicalL2Norm_dilate_le (Real.continuous_exp.comp continuous_neg).continuousOn hd1
    have hp := hprev (N/d) (hdf d hd)
    have hbase : chronologicalL2Norm (fun t => chronologicalRawHeatError (N/d) ((d:ℝ)*t) -
        Real.exp (-((d:ℝ)*t))) ≤ 1+C := by
      have hx1 := chronologicalExponential_L2Norm_le_one
      change chronologicalL2Norm (fun t => chronologicalRawHeatError (N/d) ((d:ℝ)*t) -
        Real.exp (-((d:ℝ)*t))) ≤ chronologicalL2Norm (fun t => chronologicalRawHeatError (N/d) ((d:ℝ)*t)) +
          chronologicalL2Norm (fun t => Real.exp (-((d:ℝ)*t))) at hsub
      change chronologicalL2Norm (fun t => Real.exp (-((d:ℝ)*t))) ≤
        chronologicalL2Norm (fun t => Real.exp (-t)) at hx
      linarith
    have he : chronologicalL2Norm (F d) = ε^(d-1) *
        chronologicalL2Norm (fun t => chronologicalRawHeatError (N/d) ((d:ℝ)*t) -
          Real.exp (-((d:ℝ)*t))) := by
      unfold chronologicalL2Norm
      change lpNorm (((-ε)^(d-1)) • (fun t => chronologicalRawHeatError (N/d) ((d:ℝ)*t) -
        Real.exp (-((d:ℝ)*t)))) 2 chronologicalPositiveVolume = _
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_pow, abs_neg, abs_of_nonneg hε0]
    rw [he]
    exact mul_le_mul_of_nonneg_left hbase (pow_nonneg hε0 _)
  have he : (fun t => chronologicalDampedHeatError ε N t - chronologicalRawHeatError N t) =
      ∑ d ∈ S, F d := by
    funext t
    simp only [Finset.sum_apply]
    exact chronologicalDampedHeatError_difference ε N t
  rw [he]
  calc
    _ ≤ ∑ d ∈ S, chronologicalL2Norm (F d) := lpNorm_sum_le hm (by simp)
    _ ≤ ∑ d ∈ S, ε^(d-1)*(1+C) := Finset.sum_le_sum hb
    _ = (∑ d ∈ S, ε^(d-1))*(1+C) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (chronologicalGeometric_tail_budget ε hε0 hεh S hS)
      (by linarith)

theorem chronologicalDampedHeat_converges_iff_raw {ε : ℕ → ℝ}
    (hε0 : ∀ N, 0 ≤ ε N) (hεh : ∀ N, ε N ≤ 1/2) (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun N => chronologicalL2Norm (chronologicalDampedHeatError (ε N) N)) atTop (𝓝 0) ↔
      Tendsto (fun N => chronologicalL2Norm (chronologicalRawHeatError N)) atTop (𝓝 0) := by
  have he : Tendsto (fun N => 2*ε N) atTop (𝓝 0) := by simpa using ht.const_mul 2
  apply chronologicalVolterra_zero_convergence_iff
    (fun N => chronologicalL2Norm_nonneg _) (fun N => chronologicalL2Norm_nonneg _) he
  intro N C hC hprev
  have hdiff := chronologicalDampedHeatError_perturbation (ε N) N C (hε0 N) (hεh N) hC hprev
  have hs := lpNorm_le_lpNorm_add_lpNorm_sub' (chronologicalRawHeatError_memLp N) (by simp : (1:ENNReal) ≤ 2)
    (f := chronologicalDampedHeatError (ε N) N)
  have hr := lpNorm_le_lpNorm_add_lpNorm_sub' (chronologicalDampedHeatError_memLp (ε N) N) (by simp : (1:ENNReal) ≤ 2)
    (f := chronologicalRawHeatError N)
  rw [lpNorm_sub_comm] at hr
  change chronologicalL2Norm (chronologicalDampedHeatError (ε N) N) ≤
    chronologicalL2Norm (chronologicalRawHeatError N) + chronologicalL2Norm
      (fun t => chronologicalDampedHeatError (ε N) N t - chronologicalRawHeatError N t) at hs
  change chronologicalL2Norm (chronologicalRawHeatError N) ≤
    chronologicalL2Norm (chronologicalDampedHeatError (ε N) N) + chronologicalL2Norm
      (fun t => chronologicalDampedHeatError (ε N) N t - chronologicalRawHeatError N t) at hr
  constructor <;> linarith

end RHTower
