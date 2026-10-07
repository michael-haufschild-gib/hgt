import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Exact arithmetic rigidity of coherent radical translates on a geometric grid

A finite positive mixture of coherent translates at `j * log b` cannot cancel every
positive power of `b`, unless every coefficient vanishes. The proof detects the outer
nonzero coefficient of the sampled autocorrelation convolution. No spectral hypothesis
or quantitative bound on the coefficients is used.
-/

open Complex MeasureTheory
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower.WeilSpectral

noncomputable section

private theorem outer_convolution_data (K : ℤ → ℝ) (hK : K 1 ≠ 0)
    (hbound : ∃ B : ℤ, ∀ k : ℤ, B < k → K k = 0)
    (C : ℤ →₀ ℝ) (hC : C 0 ≠ 0) :
    ∃ R D : ℤ, 1 ≤ R ∧ 0 ≤ D ∧ K R ≠ 0 ∧ C D ≠ 0 ∧
      (∀ k : ℤ, R < k → K k = 0) ∧ (∀ d : ℤ, D < d → C d = 0) ∧
      Finsupp.linearCombination ℝ (fun d => K (R + D - d)) C = C D * K R ∧
      ∀ m : ℤ, R + D < m → Finsupp.linearCombination ℝ (fun d => K (m - d)) C = 0 := by
  classical
  obtain ⟨B, hB⟩ := hbound
  have hB1 : 1 ≤ B := by
    by_contra h
    exact hK (hB 1 (by omega))
  let S := (Finset.Icc (1 : ℤ) B).filter fun k => K k ≠ 0
  have h1 : 1 ∈ S := by simp [S, hB1, hK]
  let R := S.max' ⟨1, h1⟩
  have hRmem : R ∈ S := Finset.max'_mem _ _
  have hR : K R ≠ 0 := (Finset.mem_filter.mp hRmem).2
  have hR1 : 1 ≤ R := Finset.le_max' _ _ h1
  have hRtop : ∀ k : ℤ, R < k → K k = 0 := by
    intro k hk
    by_cases hkB : k ≤ B
    · by_contra hne
      have hkS : k ∈ S := by simp [S, hne, hkB, show 1 ≤ k by omega]
      have := Finset.le_max' S k hkS
      change k ≤ R at this
      omega
    · exact hB k (by omega)
  have h0 : 0 ∈ C.support := Finsupp.mem_support_iff.mpr hC
  let D := C.support.max' ⟨0, h0⟩
  have hDmem : D ∈ C.support := Finset.max'_mem _ _
  have hD0 : 0 ≤ D := Finset.le_max' _ _ h0
  have hD : C D ≠ 0 := Finsupp.mem_support_iff.mp hDmem
  have heq : Finsupp.linearCombination ℝ (fun d => K (R + D - d)) C = C D * K R := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [smul_eq_mul]
    rw [Finset.sum_eq_single D]
    · congr 2
      ring
    · intro d hd hne
      have hdD : d ≤ D := Finset.le_max' _ _ hd
      rw [hRtop _ (by omega), mul_zero]
    · exact fun h => (h hDmem).elim
  refine ⟨R, D, hR1, hD0, hR, hD, hRtop, ?_, heq, ?_⟩
  · intro d hd
    by_contra hne
    have hmem : d ∈ C.support := Finsupp.mem_support_iff.mpr hne
    have := Finset.le_max' C.support d hmem
    change d ≤ D at this
    omega
  · intro m hm
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro d hd
    have hdD : d ≤ D := Finset.le_max' _ _ hd
    simp only [smul_eq_mul, hRtop (m - d) (by omega), mul_zero]

private theorem outer_convolution_ne_zero (K : ℤ → ℝ) (hK : K 1 ≠ 0)
    (hbound : ∃ B : ℤ, ∀ k : ℤ, B < k → K k = 0)
    (C : ℤ →₀ ℝ) (hC : C 0 ≠ 0) :
    ∃ m : ℤ, 0 < m ∧ Finsupp.linearCombination ℝ (fun d => K (m - d)) C ≠ 0 := by
  obtain ⟨R, D, hR, hD, hKR, hCD, _, _, heq, _⟩ := outer_convolution_data K hK hbound C hC
  refine ⟨R + D, by omega, ?_⟩
  rw [heq]
  exact mul_ne_zero hCD hKR

private def geometricCovariance {I M : ℕ} (a : Fin I → Fin M → ℂ) : ℤ →₀ ℝ :=
  ∑ i : Fin I, ∑ j : Fin M, ∑ k : Fin M,
    Finsupp.single ((j : ℤ) - (k : ℤ)) (conj (a i k) * a i j).re

private theorem geometricCovariance_zero {I M : ℕ} (a : Fin I → Fin M → ℂ) :
    geometricCovariance a 0 = ∑ i, ∑ j, Complex.normSq (a i j) := by
  classical
  simp only [geometricCovariance, Finset.sum_apply', Finsupp.single_apply, sub_eq_zero,
    Int.natCast_inj, Fin.val_inj]
  simp [Complex.normSq_apply]

private theorem geometricCovariance_zero_ne {I M : ℕ} (a : Fin I → Fin M → ℂ)
    (ha : a ≠ 0) : geometricCovariance a 0 ≠ 0 := by
  intro hz
  rw [geometricCovariance_zero] at hz
  apply ha
  funext i j
  apply Complex.normSq_eq_zero.mp
  have hle : Complex.normSq (a i j) ≤ ∑ i, ∑ j, Complex.normSq (a i j) :=
    (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (a i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
        Complex.normSq_nonneg (a k l)) (Finset.mem_univ i))
  exact le_antisymm (hz ▸ hle) (Complex.normSq_nonneg _)

private theorem real_weilTest_neg_self (f : ℝ → ℂ) (x : ℝ) :
    (EF.weilTest f f (-x)).re = (EF.weilTest f f x).re := by
  have h := congrArg Complex.re (congrFun (tilde_weilTest_self f) x)
  simpa only [EF.tilde, Complex.conj_re] using h

private theorem sum_geometric_autocorr {I M : ℕ} (a : Fin I → Fin M → ℂ)
    (L c : ℝ) (m : ℤ) :
    (∑ i, (EF.weilTest
      (∑ j, a i j • transl ((j : ℝ) * c) (truncatedRiemannKernel L))
      (∑ j, a i j • transl ((j : ℝ) * c) (truncatedRiemannKernel L)) ((m : ℝ) * c)).re) =
    Finsupp.linearCombination ℝ
      (fun d : ℤ => truncatedRiemannAutocorr L (((m - d : ℤ) : ℝ) * c))
      (geometricCovariance a) := by
  classical
  have hc : Continuous (truncatedRiemannKernel L) := by
    have heq : truncatedRiemannKernel L = fun u =>
        (truncatedRiemannKernelReal L u : ℂ) := funext (truncatedRiemannKernel_eq L)
    rw [heq]
    exact Complex.continuous_ofReal.comp (continuous_truncatedRiemannKernelReal L)
  simp only [geometricCovariance, map_sum, Finsupp.linearCombination_single, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weilTest_sum_transl hc (hasCompactSupport_truncatedRiemannKernel L)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, transl,
    weilTest_truncatedRiemannKernel_eq, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [truncatedRiemannAutocorr, Int.cast_sub, Int.cast_natCast, star_def]
  congr 2
  funext t
  congr 2
  ring

private theorem sum_geometric_logValue {I M : ℕ} (a : Fin I → Fin M → ℂ)
    (L c : ℝ) (n : ℕ) (m : ℤ) (hn : Real.log n = (m : ℝ) * c) :
    (∑ i, WeilOneSided.logValue
      (∑ j, a i j • transl ((j : ℝ) * c) (truncatedRiemannKernel L)) n) =
    (2 / Real.sqrt n) * Finsupp.linearCombination ℝ
      (fun d : ℤ => truncatedRiemannAutocorr L (((m - d : ℤ) : ℝ) * c))
      (geometricCovariance a) := by
  simp only [WeilOneSided.logValue, Complex.add_re, real_weilTest_neg_self,
    ← two_mul, ← Finset.sum_div, ← Finset.mul_sum, div_mul_eq_mul_div, hn,
    sum_geometric_autocorr]

/-- The exact outer-support invariant of the actual sampled autocorrelation: its last
index is the sum of the kernel's last index and the coefficient covariance's last index;
its value there is their product. All larger sampled correlations vanish. -/
theorem geometric_radical_outer_autocorrelation (c : {c : ℝ // 0 < c})
    (L : {L : ℝ // (c : ℝ) + 1 ≤ L}) (I M : ℕ)
    (a : {a : Fin I → Fin M → ℂ // a ≠ 0}) :
    let C : ℤ →₀ ℝ := ∑ i : Fin I, ∑ j : Fin M, ∑ k : Fin M,
      Finsupp.single ((j : ℤ) - (k : ℤ)) (conj (a.1 i k) * a.1 i j).re
    let K : ℤ → ℝ := fun k => truncatedRiemannAutocorr L ((k : ℝ) * c)
    let V : ℤ → ℝ := fun m => ∑ i, (EF.weilTest
      (∑ j, a.1 i j • transl ((j : ℝ) * c) (truncatedRiemannKernel L))
      (∑ j, a.1 i j • transl ((j : ℝ) * c) (truncatedRiemannKernel L)) ((m : ℝ) * c)).re
    ∃ R D : ℤ, 1 ≤ R ∧ 0 ≤ D ∧ K R ≠ 0 ∧ C D ≠ 0 ∧
      (∀ k : ℤ, R < k → K k = 0) ∧ (∀ d : ℤ, D < d → C d = 0) ∧
      V (R + D) = C D * K R ∧ ∀ m : ℤ, R + D < m → V m = 0 := by
  classical
  dsimp only
  have hK1 : truncatedRiemannAutocorr L (((1 : ℤ) : ℝ) * (c : ℝ)) ≠ 0 := by
    obtain ⟨κ, hκ, hκL⟩ := exists_weilTest_truncatedRiemannKernel_ge c.property
    have h := hκL L L.property
    rw [weilTest_truncatedRiemannKernel_eq, Complex.ofReal_re] at h
    change κ ≤ truncatedRiemannAutocorr L c at h
    simpa using ne_of_gt (lt_of_lt_of_le hκ h)
  have hbound : ∃ B : ℤ, ∀ k : ℤ, B < k →
      truncatedRiemannAutocorr L ((k : ℝ) * c) = 0 := by
    obtain ⟨B, hB⟩ := exists_int_gt (2 * (L : ℝ) / c)
    refine ⟨B, fun k hk => ?_⟩
    have hkR : (B : ℝ) < k := by exact_mod_cast hk
    have hLc : 2 * (L : ℝ) < (k : ℝ) * c :=
      (div_lt_iff₀ c.property).mp (hB.trans hkR)
    exact truncatedRiemannAutocorr_eq_zero (hLc.le.trans (le_abs_self _))
  simpa only [sum_geometric_autocorr, geometricCovariance] using
    outer_convolution_data (fun k : ℤ => truncatedRiemannAutocorr L ((k : ℝ) * c))
      hK1 hbound (geometricCovariance a.1) (geometricCovariance_zero_ne a.1 a.property)

/-- Exact cancellation at every positive power of an integer base forces every coefficient
of a finite coherent mixture of truncated radical translates on that grid to vanish.
The base and cutoff carry only their intrinsic domain constraints. -/
theorem logValue_geometric_radical_eq_zero_iff (b : {b : ℕ // 2 ≤ b})
    (L : {L : ℝ // Real.log (b : ℕ) + 1 ≤ L}) (I M : ℕ)
    (a : Fin I → Fin M → ℂ) :
    (∀ m : ℕ, (∑ i, WeilOneSided.logValue
      (∑ j, a i j • transl ((j : ℝ) * Real.log (b : ℕ))
        (truncatedRiemannKernel L)) ((b : ℕ) ^ (m + 1))) = 0) ↔ a = 0 := by
  classical
  constructor
  · intro hzero
    by_contra ha
    let c := Real.log (b : ℕ)
    let K : ℤ → ℝ := fun k => truncatedRiemannAutocorr L ((k : ℝ) * c)
    have hc : 0 < c := Real.log_pos (by exact_mod_cast (show 1 < (b : ℕ) by omega))
    have hK1 : K 1 ≠ 0 := by
      obtain ⟨κ, hκ, hκL⟩ := exists_weilTest_truncatedRiemannKernel_ge hc
      have h := hκL L L.property
      rw [weilTest_truncatedRiemannKernel_eq, Complex.ofReal_re] at h
      change κ ≤ truncatedRiemannAutocorr L c at h
      simpa only [K, Int.cast_one, one_mul] using ne_of_gt (lt_of_lt_of_le hκ h)
    have hbound : ∃ B : ℤ, ∀ k : ℤ, B < k → K k = 0 := by
      obtain ⟨B, hB⟩ := exists_int_gt (2 * (L : ℝ) / c)
      refine ⟨B, fun k hk => ?_⟩
      have hkR : (B : ℝ) < k := by exact_mod_cast hk
      have hLc : 2 * (L : ℝ) < (k : ℝ) * c := (div_lt_iff₀ hc).mp (hB.trans hkR)
      exact truncatedRiemannAutocorr_eq_zero (hLc.le.trans (le_abs_self _))
    obtain ⟨m, hm, hne⟩ := outer_convolution_ne_zero K hK1 hbound
      (geometricCovariance a) (geometricCovariance_zero_ne a ha)
    have hnat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
    have hnatpos : 1 ≤ m.toNat := by omega
    have hz := hzero (m.toNat - 1)
    rw [Nat.sub_add_cancel hnatpos] at hz
    have hlog : Real.log (((b : ℕ) ^ m.toNat : ℕ) : ℝ) = (m : ℝ) * c := by
      rw [Nat.cast_pow, Real.log_pow]
      have hmR : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hnat
      rw [hmR]
    rw [sum_geometric_logValue a L c _ m hlog] at hz
    have hbp : 0 < (((b : ℕ) ^ m.toNat : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (show 0 < (b : ℕ) by omega) _
    exact hne ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (div_pos (by norm_num)
      (Real.sqrt_pos.mpr hbp))))
  · rintro rfl m
    simp [WeilOneSided.logValue, weilTest_apply]

end

end RHTower.WeilSpectral
