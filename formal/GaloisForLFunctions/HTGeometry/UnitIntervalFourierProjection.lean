import GaloisForLFunctions.HTGeometry.TruncatedConvolutionSelfAdjoint
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier partial sums converge in mean square on the unit interval

Parseval's identity for the exponential system on an interval gives that the squared `L²` error of
the symmetric Fourier partial sum of a continuous function is the tail of a convergent series, and
hence tends to zero.  This is the density statement behind the compressed approximation of a
ground state.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The squared `L²` norm on the unit interval. -/
def l2NormSq (f : ℝ → ℂ) : ℝ := ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2

theorem l2Pair_self (f : ℝ → ℂ) : l2Pair f f = ((l2NormSq f : ℝ) : ℂ) := by
  rw [l2Pair, l2NormSq, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

theorem l2NormSq_nonneg (f : ℝ → ℂ) : 0 ≤ l2NormSq f := by
  rw [l2NormSq]
  refine intervalIntegral.integral_nonneg (by norm_num) fun x _ => ?_
  positivity

theorem l2Pair_sub_right {f g h : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    l2Pair f (fun x => g x - h x) = l2Pair f g - l2Pair f h := by
  rw [l2Pair, l2Pair, l2Pair, ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  · exact (hf.star.mul hg).intervalIntegrable _ _
  · exact (hf.star.mul hh).intervalIntegrable _ _

theorem l2Pair_sub_left {f g h : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    l2Pair (fun x => f x - g x) h = l2Pair f h - l2Pair g h := by
  rw [l2Pair, l2Pair, l2Pair, ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun x _ => ?_
    rw [map_sub]
    ring
  · exact (hf.star.mul hh).intervalIntegrable _ _
  · exact (hg.star.mul hh).intervalIntegrable _ _

theorem l2Pair_sum_right {ι : Type*} {f : ℝ → ℂ} (hf : Continuous f) (s : Finset ι)
    (g : ι → ℝ → ℂ) (hg : ∀ i, Continuous (g i)) :
    l2Pair f (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, l2Pair f (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [l2Pair]
  | insert a s ha ih =>
    have hcont : Continuous fun x => ∑ i ∈ s, g i x := continuous_finsetSum _ fun i _ => hg i
    have hstep : l2Pair f (fun x => g a x + ∑ i ∈ s, g i x)
        = l2Pair f (g a) + l2Pair f (fun x => ∑ i ∈ s, g i x) :=
      l2Pair_add_right f (g a) _ (hg a) hcont hf
    simp only [Finset.sum_insert ha]
    rw [hstep, ih]

theorem l2Pair_add_left {f g h : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    l2Pair (fun x => f x + g x) h = l2Pair f h + l2Pair g h := by
  rw [l2Pair, l2Pair, l2Pair, ← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr fun x _ => ?_
    rw [map_add]
    ring
  · exact (hf.star.mul hh).intervalIntegrable _ _
  · exact (hg.star.mul hh).intervalIntegrable _ _

theorem l2Pair_congr_left {f f' g : ℝ → ℂ} (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = f' x) :
    l2Pair f g = l2Pair f' g := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  rw [h x hx]

theorem l2Pair_congr_right {f g g' : ℝ → ℂ} (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x = g' x) :
    l2Pair f g = l2Pair f g' := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  rw [h x hx]

theorem l2NormSq_const_mul (c : ℂ) (f : ℝ → ℂ) :
    l2NormSq (fun x => c * f x) = ‖c‖ ^ 2 * l2NormSq f := by
  rw [l2NormSq, l2NormSq, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [norm_mul, mul_pow]

theorem l2NormSq_add_le {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    l2NormSq (fun x => f x + g x) ≤ 2 * l2NormSq f + 2 * l2NormSq g := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖f x + g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
    intro x _
    have htri : ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    nlinarith [norm_nonneg (f x), norm_nonneg (g x), sq_nonneg (‖f x‖ - ‖g x‖),
      norm_nonneg (f x + g x)]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) h01
    (((hf.add hg).norm.pow 2).intervalIntegrable _ _)
    (((continuous_const.mul (hf.norm.pow 2)).add
      (continuous_const.mul (hg.norm.pow 2))).intervalIntegrable _ _) hpt
  rw [l2NormSq]
  refine hmono.trans ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  have hadd : (∫ u in (0 : ℝ)..1, (2 * ‖f u‖ ^ 2 + 2 * ‖g u‖ ^ 2))
      = (∫ u in (0 : ℝ)..1, 2 * ‖f u‖ ^ 2) + ∫ u in (0 : ℝ)..1, 2 * ‖g u‖ ^ 2 :=
    intervalIntegral.integral_add
      ((continuous_const.mul (hf.norm.pow 2)).intervalIntegrable _ _)
      ((continuous_const.mul (hg.norm.pow 2)).intervalIntegrable _ _)
  rw [hadd, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [l2NormSq]
  exact le_refl _

/-! ## The Fourier coefficients on the unit interval -/

theorem fourierCoeffOn_eq_l2Pair (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n = l2Pair (fourierChar n) f := by
  rw [fourierCoeffOn_eq_integral, l2Pair]
  simp only [sub_zero, one_div, inv_one, one_smul, smul_eq_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [fourierChar_conj, fourier_coe_apply, fourierChar]
  congr 2
  push_cast
  ring

/-- The symmetric Fourier partial sum of order `N`. -/
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), l2Pair (fourierChar n) f * fourierChar n x

theorem fourierPartialSum_eq (f : ℝ → ℂ) (N : ℕ) :
    fourierPartialSum f N
      = fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          l2Pair (fourierChar n) f * fourierChar n x := rfl

theorem continuous_fourierPartialSum (f : ℝ → ℂ) (N : ℕ) :
    Continuous (fourierPartialSum f N) := by
  refine continuous_finsetSum _ fun n _ => ?_
  exact continuous_const.mul (continuous_fourierChar n)

/-- **The mean-square error of the Fourier partial sum is the Parseval tail.** -/
theorem l2NormSq_sub_fourierPartialSum {f : ℝ → ℂ} (hf : Continuous f) (N : ℕ) :
    l2NormSq (fun x => f x - fourierPartialSum f N x)
      = l2NormSq f - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖l2Pair (fourierChar n) f‖ ^ 2 := by
  set s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hs
  set c : ℤ → ℂ := fun n => l2Pair (fourierChar n) f with hc
  have hPcont : Continuous (fourierPartialSum f N) := continuous_fourierPartialSum f N
  have hfP : l2Pair f (fourierPartialSum f N) = ∑ n ∈ s, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [fourierPartialSum_eq,
      l2Pair_sum_right hf s (fun n x => c n * fourierChar n x)
        (fun n => continuous_const.mul (continuous_fourierChar n))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [l2Pair_smul_right, ← l2Pair_conj (fourierChar n) f]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    ring
  have hPP : l2Pair (fourierPartialSum f N) (fourierPartialSum f N)
      = ∑ n ∈ s, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    have hexp : ∀ x : ℝ, (starRingEnd ℂ) (fourierPartialSum f N x) * fourierPartialSum f N x
        = ∑ i ∈ s, ∑ j ∈ s, ((starRingEnd ℂ) (c i) * c j) *
            (fourierChar (-i) x * fourierChar j x) := by
      intro x
      simp only [fourierPartialSum_eq, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, fourierChar_conj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [l2Pair, intervalIntegral.integral_congr (fun x _ => hexp x),
      intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [intervalIntegral.integral_finsetSum]
      · rw [Finset.sum_eq_single i]
        · rw [intervalIntegral.integral_const_mul, integral_fourierChar_orthonormal, if_pos rfl,
            mul_one, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        · intro j _ hji
          rw [intervalIntegral.integral_const_mul, integral_fourierChar_orthonormal,
            if_neg (fun h => hji h.symm), mul_zero]
        · intro h
          exact absurd hi h
      · intro j _
        refine Continuous.intervalIntegrable ?_ _ _
        exact continuous_const.mul ((continuous_fourierChar _).mul (continuous_fourierChar _))
    · intro i _
      refine Continuous.intervalIntegrable ?_ _ _
      refine continuous_finsetSum _ fun j _ => ?_
      exact continuous_const.mul ((continuous_fourierChar _).mul (continuous_fourierChar _))
  have hPf : l2Pair (fourierPartialSum f N) f = ∑ n ∈ s, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← l2Pair_conj f (fourierPartialSum f N), hfP, map_sum]
    exact Finset.sum_congr rfl fun n _ => Complex.conj_ofReal _
  have hmain : l2Pair (fun x => f x - fourierPartialSum f N x)
      (fun x => f x - fourierPartialSum f N x)
      = l2Pair f f - ∑ n ∈ s, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [l2Pair_sub_left hf hPcont (by fun_prop), l2Pair_sub_right hf hf hPcont,
      l2Pair_sub_right hPcont hf hPcont, hfP, hPP, hPf]
    ring
  have hcast := hmain
  rw [l2Pair_self, l2Pair_self] at hcast
  have hre := congrArg Complex.re hcast
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.re_sum, Complex.ofReal_re] at hre
  rw [hre]

/-- **Mean-square convergence of the Fourier partial sums.** -/
theorem tendsto_l2NormSq_sub_fourierPartialSum {f : ℝ → ℂ} (hf : Continuous f) :
    Tendsto (fun N : ℕ => l2NormSq (fun x => f x - fourierPartialSum f N x)) atTop (𝓝 0) := by
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hmem : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hf.continuousOn
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
    refine MemLp.of_bound hf.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Set.Ioc_subset_Icc_self hx)
  have hsum := hasSum_sq_fourierCoeffOn h01 hmem
  simp only [sub_zero, inv_one, one_smul] at hsum
  have hsum' : HasSum (fun n : ℤ => ‖l2Pair (fourierChar n) f‖ ^ 2) (l2NormSq f) := by
    simpa only [fourierCoeffOn_eq_l2Pair, l2NormSq] using hsum
  have hmono : Monotone fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro a b hab
    refine Finset.Icc_subset_Icc ?_ ?_ <;> exact_mod_cast by omega
  have hex : ∀ x : ℤ, ∃ n : ℕ, x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro x
    refine ⟨x.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    omega
  have hpart : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖l2Pair (fourierChar n) f‖ ^ 2)
      atTop (𝓝 (l2NormSq f)) :=
    hsum'.comp (Filter.tendsto_atTop_finset_of_monotone hmono hex)
  have hlim : Tendsto
      (fun N : ℕ => l2NormSq f
        - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖l2Pair (fourierChar n) f‖ ^ 2)
      atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := l2NormSq f) (f := (atTop : Filter ℕ)) |>.sub hpart
    simpa using this
  refine hlim.congr fun N => ?_
  exact (l2NormSq_sub_fourierPartialSum hf N).symm

end

end GaloisForLFunctions.HTGeometry
