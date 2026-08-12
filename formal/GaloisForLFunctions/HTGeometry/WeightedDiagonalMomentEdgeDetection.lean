import GaloisForLFunctions.HTGeometry.DiagonalMomentEdgeDetection
import GaloisForLFunctions.HTGeometry.WeightedUnitPowerSumOscillation

/-!
# Positive weighted diagonal moments detect a positive real spectral edge

This coefficient-faithful form retains arbitrary strictly positive atom weights.  It is the edge
theorem needed for continuous source work, rather than flattening a source coefficient to a
support indicator.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Nonnegative real parts of all positively weighted diagonal moments force a positive-real atom
at maximal spectral modulus. -/
theorem exists_positiveReal_maximal_of_forall_weightedPowerMoment_re_nonneg
    {ι : Type*} [Nonempty ι] (z : ι → ℂ) (w : ι → ℝ)
    (hne : ∀ i, z i ≠ 0) (hw : ∀ i, 0 < w i)
    (hfinite : ∀ {r : ℝ}, 0 < r → {i | r ≤ ‖z i‖}.Finite)
    (hsum : Summable (fun i => w i * ‖z i‖))
    (hsumPow : ∀ n : ℕ, Summable (fun i => w i * ‖z i ^ (n + 1)‖))
    (hmom : ∀ n : ℕ,
      0 ≤ (∑' i, (w i : ℂ) * z i ^ (n + 1)).re) :
    ∃ i : ι, z i = (‖z i‖ : ℂ) ∧ ∀ j, ‖z j‖ ≤ ‖z i‖ := by
  classical
  by_contra hcon
  obtain ⟨ia⟩ := ‹Nonempty ι›
  have hiapos : 0 < ‖z ia‖ := norm_pos_iff.mpr (hne ia)
  have hfin := hfinite hiapos
  have hia : ia ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    exact le_rfl
  obtain ⟨i₀, hi₀mem, hi₀max⟩ := hfin.toFinset.exists_max_image
    (fun i => ‖z i‖) ⟨ia, hia⟩
  have hi₀global : ∀ i, ‖z i‖ ≤ ‖z i₀‖ := by
    intro i
    by_cases hi : i ∈ hfin.toFinset
    · exact hi₀max i hi
    · rw [Set.Finite.mem_toFinset] at hi
      exact le_trans (not_le.mp hi).le (hi₀max ia hia)
  set r : ℝ := ‖z i₀‖ with hr
  have hrpos : 0 < r := norm_pos_iff.mpr (hne i₀)
  have hTfin : {i : ι | r ≤ ‖z i‖}.Finite := hfinite hrpos
  set T : Finset ι := hTfin.toFinset with hT
  have hmemT : ∀ i, i ∈ T ↔ r ≤ ‖z i‖ := by
    intro i
    rw [hT, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hi₀T : i₀ ∈ T := (hmemT i₀).mpr le_rfl
  have hTne : T.Nonempty := ⟨i₀, hi₀T⟩
  have hTval : ∀ i ∈ T, ‖z i‖ = r := fun i hi =>
    le_antisymm (hi₀global i) ((hmemT i).mp hi)
  set v : ι → ℂ := fun i => z i / (r : ℂ) with hv
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hvnorm : ∀ i ∈ T, ‖v i‖ = 1 := by
    intro i hi
    rw [hv]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [hTval i hi]
    exact div_self hrpos.ne'
  have hvne1 : ∀ i ∈ T, v i ≠ 1 := by
    intro i hi h1
    have hz : z i = (r : ℂ) := by
      rw [hv] at h1
      rw [div_eq_iff hrC, one_mul] at h1
      exact h1
    apply hcon
    refine ⟨i, ?_, ?_⟩
    · rw [hTval i hi]
      exact hz
    · intro j
      rw [hTval i hi]
      exact hi₀global j
  obtain ⟨ρ, hρ0, hρlt, hρbound⟩ :
      ∃ ρ, 0 ≤ ρ ∧ ρ < r ∧ ∀ i, i ∉ T → ‖z i‖ ≤ ρ := by
    have hhalf : (0 : ℝ) < r / 2 := by linarith
    have hS2fin : {i : ι | r / 2 ≤ ‖z i‖}.Finite := hfinite hhalf
    set D : Finset ι := hS2fin.toFinset \ T with hD
    rcases D.eq_empty_or_nonempty with hDe | hDne
    · refine ⟨r / 2, by linarith, by linarith, fun i hi => ?_⟩
      by_contra hgt
      rw [not_le] at hgt
      have hiD : i ∈ D := by
        rw [hD, Finset.mem_sdiff, Set.Finite.mem_toFinset]
        exact ⟨le_of_lt hgt, hi⟩
      rw [hDe] at hiD
      exact absurd hiD (Finset.notMem_empty i)
    · obtain ⟨id, hidD, hidmax⟩ := D.exists_max_image (fun i => ‖z i‖) hDne
      have hidT : id ∉ T := by
        rw [hD, Finset.mem_sdiff] at hidD
        exact hidD.2
      refine ⟨max ‖z id‖ (r / 2),
        le_trans (by linarith) (le_max_right _ _), ?_, ?_⟩
      · rw [max_lt_iff]
        refine ⟨?_, by linarith⟩
        exact lt_of_not_ge fun hge => hidT ((hmemT id).mpr hge)
      · intro i hi
        by_cases hi2 : r / 2 ≤ ‖z i‖
        · have hiD : i ∈ D := by
            rw [hD, Finset.mem_sdiff, Set.Finite.mem_toFinset]
            exact ⟨hi2, hi⟩
          exact le_trans (hidmax i hiD) (le_max_left _ _)
        · exact le_trans (not_le.mp hi2).le (le_max_right _ _)
  have hsub : Summable (fun i : ↑(↑T : Set ι)ᶜ => w ↑i * ‖z ↑i‖) := hsum.subtype _
  set S₀c : ℝ := ∑' i : ↑(↑T : Set ι)ᶜ, w ↑i * ‖z ↑i‖ with hS₀c
  have hS₀nn : 0 ≤ S₀c := tsum_nonneg fun i => mul_nonneg (hw _).le (norm_nonneg _)
  have htail : ∀ n : ℕ,
      ‖∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i : ℂ) * z ↑i ^ (n + 1)‖ ≤
        S₀c * ρ ^ n := by
    intro n
    have hsubpow : Summable (fun i : ↑(↑T : Set ι)ᶜ =>
        w ↑i * ‖z ↑i ^ (n + 1)‖) := (hsumPow n).subtype _
    have hsubpowNorm : Summable (fun i : ↑(↑T : Set ι)ᶜ =>
        ‖(w ↑i : ℂ) * z ↑i ^ (n + 1)‖) := by
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hw _)] using hsubpow
    calc
      ‖∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i : ℂ) * z ↑i ^ (n + 1)‖
          ≤ ∑' i : ↑(↑T : Set ι)ᶜ, ‖(w ↑i : ℂ) * z ↑i ^ (n + 1)‖ :=
            norm_tsum_le_tsum_norm hsubpowNorm
      _ = ∑' i : ↑(↑T : Set ι)ᶜ, w ↑i * ‖z ↑i ^ (n + 1)‖ := by
          congr 1
          funext i
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw _)]
      _ ≤ ∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i * ‖z ↑i‖) * ρ ^ n := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsubpow (hsub.mul_right _)
          rw [norm_pow, pow_succ']
          have hiT : (↑i : ι) ∉ T := by
            have hi := i.2
            simp only [Set.mem_compl_iff, Finset.mem_coe] at hi
            exact hi
          have hp := pow_le_pow_left₀ (norm_nonneg _) (hρbound _ hiT) n
          calc
            w ↑i * (‖z ↑i‖ * ‖z ↑i‖ ^ n) =
                (w ↑i * ‖z ↑i‖) * ‖z ↑i‖ ^ n := by ring
            _ ≤ (w ↑i * ‖z ↑i‖) * ρ ^ n :=
              mul_le_mul_of_nonneg_left hp
                (mul_nonneg (hw (↑i : ι)).le (norm_nonneg _))
      _ = S₀c * ρ ^ n := by rw [tsum_mul_right]
  have hlow : ∀ n : ℕ,
      -((S₀c / r) * (ρ / r) ^ n) ≤
        (∑ i ∈ T, (w i : ℂ) * v i ^ (n + 1)).re := by
    intro n
    have hpowsum : Summable (fun i : ι => (w i : ℂ) * z i ^ (n + 1)) := by
      have hn := hsumPow n
      apply Summable.of_norm
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hw _)] using hn
    have hsplit := hpowsum.sum_add_tsum_compl (s := T)
    have hmoment : (∑ i ∈ T, (w i : ℂ) * z i ^ (n + 1)).re =
        (∑' i : ι, (w i : ℂ) * z i ^ (n + 1)).re -
          (∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i : ℂ) * z ↑i ^ (n + 1)).re := by
      have hre := congrArg Complex.re hsplit
      rw [Complex.add_re] at hre
      linarith
    have hvsum : (∑ i ∈ T, (w i : ℂ) * v i ^ (n + 1)) =
        (∑ i ∈ T, (w i : ℂ) * z i ^ (n + 1)) /
          ((r : ℝ) : ℂ) ^ (n + 1) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv, div_pow, div_eq_mul_inv]
      ring
    have hre : (∑ i ∈ T, (w i : ℂ) * v i ^ (n + 1)).re =
        (∑ i ∈ T, (w i : ℂ) * z i ^ (n + 1)).re / r ^ (n + 1) := by
      rw [hvsum, ← Complex.ofReal_pow, div_eq_mul_inv, ← Complex.ofReal_inv,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        div_eq_mul_inv]
    have htailre : -(S₀c * ρ ^ n) ≤
        -(∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i : ℂ) * z ↑i ^ (n + 1)).re := by
      have h1 := htail n
      have h2 := Complex.abs_re_le_norm
        (∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i : ℂ) * z ↑i ^ (n + 1))
      have h3 := le_abs_self
        (∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i : ℂ) * z ↑i ^ (n + 1)).re
      linarith
    have hrpow : (0 : ℝ) < r ^ (n + 1) := pow_pos hrpos _
    have hnum : -(S₀c * ρ ^ n) ≤
        (∑' i : ι, (w i : ℂ) * z i ^ (n + 1)).re -
          (∑' i : ↑(↑T : Set ι)ᶜ, (w ↑i : ℂ) * z ↑i ^ (n + 1)).re := by
      have := hmom n
      linarith
    have halg : -((S₀c / r) * (ρ / r) ^ n) =
        -(S₀c * ρ ^ n) / r ^ (n + 1) := by
      rw [div_pow, pow_succ']
      field_simp
    rw [hre, hmoment, halg, div_le_div_iff₀ hrpow hrpow]
    exact mul_le_mul_of_nonneg_right hnum hrpow.le
  have hC : 0 ≤ S₀c / r := div_nonneg hS₀nn hrpos.le
  have hκ0 : 0 ≤ ρ / r := div_nonneg hρ0 hrpos.le
  have hκ1 : ρ / r < 1 := (div_lt_one hrpos).mpr hρlt
  exact realWeightedUnitPowerSum_no_decaying_lower_bound hvnorm hvne1
    (fun i _ => hw i) hi₀T hC hκ0 hκ1 hlow

end

end GaloisForLFunctions.HTGeometry
