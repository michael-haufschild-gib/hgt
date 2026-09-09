import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.Integral

/-!
# A two-cell bound for the complete modular strip

The cap above height squared three quarters and inside the unit circle maps
into the literal modular cell under one inversion. This gives a two-cell
cover of the complete strip. Measure-preserving inversion transfers cell
integrability and bounds every nonnegative invariant source's strip integral
by twice its cell integral. The geometry includes all closed boundaries.
-/

open Set MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups
namespace GaloisForLFunctions.RHTower.SelbergModularStripComparison
noncomputable section

/-- The complete unit strip above the modular cell's lowest height. -/
def strip : Set ℍ := {z | |z.re| ≤ (1 : ℝ) / 2 ∧ 3 ≤ 4 * z.im ^ 2}

theorem strip_measurable : MeasurableSet strip := by
  exact (isClosed_le (continuous_re.abs) continuous_const).measurableSet.inter
    (isClosed_le continuous_const (continuous_const.mul (continuous_im.pow 2))).measurableSet

/-- The literal closed modular cell lies in the comparison strip. -/
theorem fd_subset_strip : fd ⊆ strip :=
  fun _ hz => ⟨hz.2, three_le_four_mul_im_sq_of_mem_fd hz⟩

/-- Inversion maps the portion below the unit circle directly into the modular cell. -/
theorem inversion_cap_mem_fd {z : ℍ} (hz : z ∈ strip)
    (hn : Complex.normSq (z : ℂ) ≤ 1) : S • z ∈ fd := by
  have hp := z.normSq_pos
  have hr : 2 * |z.re| ≤ Complex.normSq (z : ℂ) := by
    have hx := abs_nonneg z.re
    have hs := sq_abs z.re
    have hprod := mul_nonneg (sub_nonneg.mpr hz.1) (show 0 ≤ 3 / 2 - |z.re| by linarith [hz.1])
    rw [Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith [hz.2]
  constructor
  · rw [modular_S_smul]
    simp only [Complex.normSq_inv, Complex.normSq_neg]
    exact (one_le_inv₀ hp).mpr hn
  · rw [modular_S_smul]
    change |((-(z : ℂ))⁻¹).re| ≤ (1 : ℝ) / 2
    rw [Complex.inv_re, Complex.neg_re, Complex.normSq_neg, abs_div, abs_neg,
      abs_of_pos hp, UpperHalfPlane.coe_re]
    exact (div_le_iff₀ hp).mpr (by linarith)

/-- Every strip point is covered by the cell or its single inversion preimage. -/
theorem strip_subset_double_cell :
    strip ⊆ fd ∪ (fun z : ℍ => S • z) ⁻¹' fd := by
  intro z hz
  by_cases hn : 1 ≤ Complex.normSq (z : ℂ)
  · exact Or.inl ⟨hn, hz.1⟩
  · exact Or.inr (inversion_cap_mem_fd hz (le_of_not_ge hn))

private theorem integral_inversion {u : ℍ → ℝ}
    (hu : ∀ z, u (S • z) = u z) :
    (∫ z in (fun z : ℍ => S • z) ⁻¹' fd, u z) = ∫ z in fd, u z := by
  have h := (measurePreserving_smul (S : GL (Fin 2) ℝ) (volume : Measure ℍ)).setIntegral_preimage_emb
    (Homeomorph.smul (S : GL (Fin 2) ℝ)).measurableEmbedding u fd
  change (∫ z in (fun z : ℍ => S • z) ⁻¹' fd, u (S • z)) = ∫ z in fd, u z at h
  simpa only [hu] using h

/-- Integrability on the cell transfers to the complete strip for an inversion-invariant source. -/
theorem integrable_strip {u : ℍ → ℝ} (hi : IntegrableOn u fd)
    (hu : ∀ z, u (S • z) = u z) : IntegrableOn u strip := by
  have hj := (measurePreserving_smul (S : GL (Fin 2) ℝ) (volume : Measure ℍ)).integrableOn_comp_preimage
    (Homeomorph.smul (S : GL (Fin 2) ℝ)).measurableEmbedding (f := u) (s := fd)
  have hp : IntegrableOn u ((fun z : ℍ => S • z) ⁻¹' fd) := by
    have hh := hj.mpr hi
    change IntegrableOn (fun z : ℍ => u (S • z)) ((fun z : ℍ => S • z) ⁻¹' fd) at hh
    simpa only [hu] using hh
  exact (hi.union hp).mono_set strip_subset_double_cell

/-- A nonnegative invariant physical density has strip integral at most twice its cell integral. -/
theorem integral_strip_le_twice {u : ℍ → ℝ} (hi : IntegrableOn u fd)
    (hn : ∀ z, 0 ≤ u z) (hu : ∀ z, u (S • z) = u z) :
    (∫ z in strip, u z) ≤ 2 * ∫ z in fd, u z := by
  let t := (fun z : ℍ => S • z) ⁻¹' fd
  have ht : MeasurableSet t := isClosed_fd.measurableSet.preimage
    (Homeomorph.smul (S : GL (Fin 2) ℝ)).continuous.measurable
  have hj := (measurePreserving_smul (S : GL (Fin 2) ℝ) (volume : Measure ℍ)).integrableOn_comp_preimage
    (Homeomorph.smul (S : GL (Fin 2) ℝ)).measurableEmbedding (f := u) (s := fd)
  have hp : IntegrableOn u t := by
    have hh := hj.mpr hi
    change IntegrableOn (fun z : ℍ => u (S • z)) ((fun z : ℍ => S • z) ⁻¹' fd) at hh
    simpa only [hu] using hh
  have hle := setIntegral_mono_set (hi.union hp) (Filter.Eventually.of_forall hn)
    (Filter.Eventually.of_forall strip_subset_double_cell)
  have he := setIntegral_union (μ := (volume : Measure ℍ))
    (show Disjoint fd (t \ fd) from disjoint_left.mpr (fun z hz ht => ht.2 hz))
    (ht.diff isClosed_fd.measurableSet) hi (hp.mono_set sdiff_subset)
  have hs : fd ∪ (t \ fd) = fd ∪ t := by ext z; simp only [mem_union, mem_sdiff]; tauto
  rw [hs] at he
  have hb := setIntegral_mono_set hp (Filter.Eventually.of_forall hn)
    (Filter.Eventually.of_forall (show t \ fd ⊆ t from sdiff_subset))
  change (∫ z in strip, u z) ≤ ∫ z in fd ∪ t, u z at hle
  change (∫ z in t \ fd, u z) ≤ ∫ z in t, u z at hb
  have hinv : (∫ z in t, u z) = ∫ z in fd, u z := integral_inversion hu
  linarith

end
end GaloisForLFunctions.RHTower.SelbergModularStripComparison
