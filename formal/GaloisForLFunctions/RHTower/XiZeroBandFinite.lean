import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling

/-!
# Finiteness and summability in a horizontal band of Xi zeros

The divisor of the completed zeta is locally finite and its support lies in the critical strip, so
only finitely many multiplicity copies have ordinate within a bounded distance of a given height.
Together with the weighted density `Σ_ρ 1/(1+(t−γ)²) = O(log t)` this gives the summability facts
that the segment estimate of Proposition 5.1 needs, at *every* real height rather than only at large
ones.

## Main results

* `finite_xiZeroCopy_band`
* `summable_xiZeroWeight`
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- Every divisor support point is a centred zero. -/
theorem XiC_spectralSupport_eq_zero (ρ : XiDivisorSupport) :
    XiC (xiSpectralPointSupport ρ) = 0 := by
  have hpos := xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
  have h := XiC_xiSpectralPoint_eq_zero (⟨ρ, ⟨0, hn⟩⟩ : XiZeroCopy)
  rwa [xiSpectralPoint_eq_support] at h

/-- Only finitely many divisor support points have ordinate within `r` of `t`. -/
theorem finite_xiDivisorSupport_band (t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {ρ : XiDivisorSupport | |(ρ : ℂ).im - t| ≤ r}.Finite := by
  classical
  have hrect : {z : ℂ | z ∈ (uIcc (t - r) (t + r) ×ℂ uIcc (-1 : ℝ) 1) ∧ XiC z = 0}.Finite :=
    xiC_zeros_closedRectangle_finite (⟨t - r, -1⟩ : ℂ) (⟨t + r, 1⟩ : ℂ)
  have hsub : {ρ : XiDivisorSupport | |(ρ : ℂ).im - t| ≤ r}
      ⊆ xiSpectralPointSupport ⁻¹'
        {z : ℂ | z ∈ (uIcc (t - r) (t + r) ×ℂ uIcc (-1 : ℝ) 1) ∧ XiC z = 0} := by
    intro ρ hρ
    have hmem : |(ρ : ℂ).im - t| ≤ r := hρ
    obtain ⟨hlo, hhi⟩ := abs_le.1 hmem
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit ρ
    have hre : (xiSpectralPointSupport ρ).re = (ρ : ℂ).im := by
      rw [xiSpectralPointSupport]
      simp [Complex.mul_re]
    have him : (xiSpectralPointSupport ρ).im = 1 / 2 - (ρ : ℂ).re := by
      rw [xiSpectralPointSupport]
      simp [Complex.mul_im]
    refine Set.mem_preimage.2 ⟨?_, XiC_spectralSupport_eq_zero ρ⟩
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [hre, uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · rw [him, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨by linarith, by linarith⟩
  have hinj : Set.InjOn xiSpectralPointSupport
      (xiSpectralPointSupport ⁻¹'
        {z : ℂ | z ∈ (uIcc (t - r) (t + r) ×ℂ uIcc (-1 : ℝ) 1) ∧ XiC z = 0}) := by
    intro a _ b _ hab
    have hI : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    have heq : ((a : ℂ) - 1 / 2) * -Complex.I = ((b : ℂ) - 1 / 2) * -Complex.I := hab
    have hcoe : (a : ℂ) = (b : ℂ) := by
      have := mul_right_cancel₀ hI heq
      linear_combination this
    exact Subtype.ext hcoe
  exact (hrect.preimage hinj).subset hsub

/-- Only finitely many divisor copies have ordinate within `r` of `t`. -/
theorem finite_xiZeroCopy_band (t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {q : XiZeroCopy | |(q.1 : ℂ).im - t| ≤ r}.Finite := by
  classical
  have hS := finite_xiDivisorSupport_band t hr
  refine (hS.biUnion (fun ρ _ =>
    (Set.finite_range (fun i : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
      (⟨ρ, i⟩ : XiZeroCopy))))).subset ?_
  intro q hq
  refine Set.mem_biUnion (show q.1 ∈ {ρ : XiDivisorSupport | |(ρ : ℂ).im - t| ≤ r} from hq) ?_
  exact ⟨q.2, rfl⟩

/-- The Cauchy weight is summable over the divisor at every real height. -/
theorem summable_xiZeroWeight (x : ℝ) :
    Summable (fun q : XiZeroCopy => (1 : ℝ) / (1 + (x - (q.1 : ℂ).im) ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_tsum_weighted_density_le
  obtain ⟨t₀, ht₀⟩ := (hC.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
  have hbase : Summable (fun q : XiZeroCopy => (1 : ℝ) / (1 + (t₀ - (q.1 : ℂ).im) ^ 2)) :=
    ht₀.1.1
  set K : ℝ := 1 + 2 * (t₀ - x) ^ 2 + 2 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) (hbase.mul_left K)
  set γ : ℝ := (q.1 : ℂ).im with hγ
  have hden1 : (0 : ℝ) < 1 + (x - γ) ^ 2 := by positivity
  have hden2 : (0 : ℝ) < 1 + (t₀ - γ) ^ 2 := by positivity
  have key : 1 + (t₀ - γ) ^ 2 ≤ K * (1 + (x - γ) ^ 2) := by
    rw [hK]
    nlinarith [sq_nonneg ((t₀ - x) - (x - γ)), sq_nonneg (x - γ), sq_nonneg (t₀ - x)]
  calc (1 : ℝ) / (1 + (x - γ) ^ 2) = K * (1 / (K * (1 + (x - γ) ^ 2))) := by
        field_simp
    _ ≤ K * (1 / (1 + (t₀ - γ) ^ 2)) := by
        gcongr

end

end RHTower
