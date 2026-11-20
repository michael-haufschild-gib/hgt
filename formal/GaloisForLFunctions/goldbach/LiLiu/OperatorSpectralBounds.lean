import GaloisForLFunctions.goldbach.SpectralSquareProduct
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenbasis
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue

/-!
# Spectral zero exclusion for the operator itself

The product ranges over the nonzero eigenvalues of the given compact
selfadjoint operator, with eigenspace multiplicity. A norm-attaining
eigenvector supplies a factor. On the real slice, an excessive norm forces
that factor to vanish strictly inside the excluded half-space.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open GaloisForLFunctions.HTGeometry Set
noncomputable section

private theorem real_factor (μ x : ℝ) :
    spectralSquareFactor μ x = ((1 - 4 * μ ^ 2 * x * (1 - x) : ℝ) : ℂ) := by
  rw [spectralSquareFactor_eq]
  push_cast
  rfl

/-- The open half-space allows a zero on its boundary. -/
theorem factor_zeroFree_iff (μ : ℝ) {η : ℝ} (hη : 0 < η) (hhalf : η < 1 / 2) :
    (∀ z : ℂ, 1 - η < z.re → spectralSquareFactor μ z ≠ 0) ↔
      4 * μ ^ 2 * η * (1 - η) ≤ 1 := by
  let f : ℝ → ℝ := fun x => 4 * μ ^ 2 * x * (1 - x)
  have hedge : f (1 - η) = 4 * μ ^ 2 * η * (1 - η) := by dsimp [f]; ring
  constructor
  · intro h
    by_contra! hbig
    have hc : Continuous f := by dsimp [f]; fun_prop
    have hi : 1 ∈ Icc (f 1) (f (1 - η)) := ⟨by simp [f], hedge ▸ hbig.le⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (show 1 - η ≤ 1 by linarith) hc.continuousOn hi
    have hstrict : 1 - η < x := hx.1.lt_of_ne fun e => by
      rw [← e, hedge] at hfx
      exact hbig.ne' hfx
    apply h x hstrict
    rw [real_factor, ← Complex.ofReal_zero, Complex.ofReal_inj]
    exact sub_eq_zero.mpr hfx.symm
  · intro hb z hx hz
    have hzreal : z = (z.re : ℂ) := by
      rcases spectralSquareFactor_zero_location μ z hz with h | h
      · linarith only [hhalf, hx, h]
      · exact Complex.ext rfl (by simpa using h)
    conv at hz => arg 1; rw [hzreal]
    rw [real_factor, ← Complex.ofReal_zero, Complex.ofReal_inj, sub_eq_zero] at hz
    have hμ : μ ≠ 0 := by intro e; simp [e] at hz
    have hp := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_ne_zero hμ))
      (mul_pos (sub_pos.mpr hx) (show 0 < z.re - η by linarith only [hhalf, hx]))
    nlinarith only [hp, hb, hz]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complex slice of (1.6), with each nonzero eigenvalue repeated according to its multiplicity. -/
def spectralProduct (T : H →L[ℂ] H) [Fact (IsCompactOperator T)] (δ : ℝ) (z : ℂ) : ℂ :=
  ∏' i : EigenIndex T, spectralSquareFactor (i.1.1.re / δ) z

private theorem exists_norm_index {T : H →L[ℂ] H} [hc : Fact (IsCompactOperator T)]
    (hs : T.IsSymmetric) (hT : T ≠ 0) :
    ∃ i : EigenIndex T, |i.1.1.re| = ‖T‖ := by
  obtain ⟨μ, x, hμ, hx, he⟩ := ContinuousLinearMap.exists_unit_eigenvector_norm hc.out hs hT
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hμ
    exact hT (norm_eq_zero.mp hμ.symm)
  let k : {z : ℂ // z ≠ 0} := ⟨μ, Complex.ofReal_ne_zero.mpr hμ0⟩
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hxk : x ∈ nonzeroEigenspace T k := Module.End.mem_eigenspace_iff.mpr he
  letI : Nontrivial (nonzeroEigenspace T k) :=
    ⟨⟨⟨x, hxk⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  exact ⟨⟨k, ⟨0, Module.finrank_pos⟩⟩, hμ⟩

/-- Hypothesis S bounds the norm at the prescribed width, in squared form. -/
theorem norm_bound_of_zeroFree {T : H →L[ℂ] H} [Fact (IsCompactOperator T)]
    (hs : T.IsSymmetric) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hhalf : η < 1 / 2)
    (h : ∀ z : ℂ, 1 - η < z.re → spectralProduct T δ z ≠ 0) :
    4 * ‖T‖ ^ 2 * η * (1 - η) ≤ δ ^ 2 := by
  by_cases hT : T = 0
  · rw [hT, norm_zero]
    simpa using sq_nonneg δ
  obtain ⟨i, hi⟩ := exists_norm_index hs hT
  have hb := (factor_zeroFree_iff (i.1.1.re / δ) hη hhalf).mp
    fun z hz hf => h z hz (tprod_of_exists_eq_zero ⟨i, hf⟩)
  have hv : 4 * i.1.1.re ^ 2 * η * (1 - η) / δ ^ 2 ≤ 1 := by
    convert hb using 1 <;> ring
  rw [div_le_one (sq_pos_of_pos hδ)] at hv
  simpa only [← hi, sq_abs] using hv

/-- Critical-line zeros bound the norm at the sharper scale δ of Hypothesis R. -/
theorem norm_bound_of_critical {T : H →L[ℂ] H} [Fact (IsCompactOperator T)]
    (hs : T.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ z : ℂ, spectralProduct T δ z = 0 → z.re = 1 / 2) : ‖T‖ ≤ δ := by
  by_cases hT : T = 0
  · simpa [hT] using hδ.le
  obtain ⟨i, hi⟩ := exists_norm_index hs hT
  have hb := (spectralSquareFactor_critical_iff (i.1.1.re / δ)).mp fun z hf =>
    h z (tprod_of_exists_eq_zero ⟨i, hf⟩)
  rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos hδ, div_le_one hδ, hi] at hb
  exact hb

#print axioms factor_zeroFree_iff
#print axioms norm_bound_of_zeroFree
#print axioms norm_bound_of_critical

end
end GaloisForLFunctions.Goldbach.LiLiu
