import GaloisForLFunctions.RHTower.SoninExtendedMellinExtension
import GaloisForLFunctions.RHTower.BurnolSoninDilationMellin

/-!
# Dilations of the extended Sonine space

Burnol's `L_a` is the set of vectors that are constant on the central band `[-a,a]` and whose
Fourier transform is constant there too.  Both conditions transport through a dilation: `dilation r`
compresses the physical band to `[-a/r, a/r]` and, because `𝓕 ∘ dilation r = dilation r⁻¹ ∘ 𝓕`,
expands the frequency band to `[-ar, ar]`.  So `L_a` is carried into `L_{min(a/r, ar)}` — for
`1/b ≤ r ≤ b` a vector of `L_b` stays in `L_1`, which is exactly the constraint behind Burnol's
smoothing in Theorem 4.9.

## Main results

* `mem_centralSoninExtendedCarrier_iff` — the two-constant description of `L_a`
* `dilation_mem_centralSoninExtendedCarrier`
* `l2Reflection_mem_centralSoninExtendedCarrier`, `evenProjection_mem_centralSoninExtendedCarrier`
* `centralSoninExtendedCarrier_antitone`
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

/-! ## The two-constant description -/

theorem mem_orthogonal_centralMeanZeroFourier_iff {a : ℝ} (f : SoninL2) :
    f ∈ (centralMeanZeroFourier a)ᗮ ↔
      ∃ c : ℂ, ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
        ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c := by
  rw [← mem_orthogonal_meanZeroBand_iff a (fourierUnitary f)]
  constructor
  · intro hmem p hp
    have hpre : fourierUnitary.symm p ∈ centralMeanZeroFourier a := by
      rw [mem_centralMeanZeroFourier_iff, LinearIsometryEquiv.apply_symm_apply]
      exact hp
    have h0 := hmem _ hpre
    have hiso := fourierUnitary.inner_map_map (fourierUnitary.symm p) f
    rw [LinearIsometryEquiv.apply_symm_apply] at hiso
    rw [hiso]
    exact h0
  · intro hfour p hp
    have hmem : fourierUnitary p ∈ meanZeroBand a := mem_centralMeanZeroFourier_iff.1 hp
    have hiso := fourierUnitary.inner_map_map p f
    rw [← hiso]
    exact hfour _ hmem

/-- **Burnol's description of `L_a`.**  A vector lies in the extended Sonine space exactly when it
is constant on the central band and so is its Fourier transform. -/
theorem mem_centralSoninExtendedCarrier_iff {a : ℝ} (f : SoninL2) :
    f ∈ centralSoninExtendedCarrier a ↔
      (∃ d : ℂ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) ∧
      (∃ c : ℂ, ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
        ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c) := by
  rw [centralSoninExtendedCarrier, ← Submodule.inf_orthogonal, Submodule.mem_inf,
    mem_orthogonal_meanZeroBand_iff, mem_orthogonal_centralMeanZeroFourier_iff]

theorem centralSoninExtendedCarrier_antitone {a b : ℝ} (hab : a ≤ b) :
    centralSoninExtendedCarrier b ≤ centralSoninExtendedCarrier a := by
  rw [centralSoninExtendedCarrier, centralSoninExtendedCarrier]
  exact Submodule.orthogonal_le (sup_le_sup (meanZeroBand_mono hab) (centralMeanZeroFourier_mono hab))

/-! ## Transport of a constant head -/

theorem centralInterval_subset {a b : ℝ} (hab : a ≤ b) : centralInterval a ⊆ centralInterval b := by
  intro x hx
  rw [centralInterval, Set.mem_Icc] at hx ⊢
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem ae_const_mono {a b : ℝ} (hab : a ≤ b) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (f : ℝ → ℂ) t = c) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c := by
  filter_upwards [hc] with t ht hmem
  exact ht (centralInterval_subset hab hmem)

/-- A constant head is carried by a dilation to a constant head of the compressed aperture. -/
theorem ae_const_dilation {a r : ℝ} (hr : 0 < r) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval (a / r) →
      ((dilation r hr f : SoninL2) : ℝ → ℂ) t = (Real.sqrt r : ℂ) * c := by
  have hcomp := (realMul_quasiMeasurePreserving r hr.ne').ae hc
  filter_upwards [dilation_ae r hr f, hcomp] with x hd hx hmem
  rw [hd, hx ?_]
  rw [centralInterval, Set.mem_Icc] at hmem ⊢
  have hlow : r * (-(a / r)) ≤ r * x := mul_le_mul_of_nonneg_left hmem.1 hr.le
  have hhigh : r * x ≤ r * (a / r) := mul_le_mul_of_nonneg_left hmem.2 hr.le
  have he1 : r * (-(a / r)) = -a := by field_simp
  have he2 : r * (a / r) = a := by field_simp
  constructor
  · linarith
  · linarith

/-- **Dilations move the aperture of `L_a`.** -/
theorem dilation_mem_centralSoninExtendedCarrier {a b r : ℝ} (hr : 0 < r) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) (hb1 : b ≤ a / r) (hb2 : b ≤ a * r) :
    dilation r hr f ∈ centralSoninExtendedCarrier b := by
  obtain ⟨⟨d, hd⟩, ⟨c, hc⟩⟩ := (mem_centralSoninExtendedCarrier_iff f).1 hf
  refine (mem_centralSoninExtendedCarrier_iff _).2 ⟨⟨(Real.sqrt r : ℂ) * d, ?_⟩,
    ⟨(Real.sqrt r⁻¹ : ℂ) * c, ?_⟩⟩
  · exact ae_const_mono hb1 (ae_const_dilation hr hd)
  · rw [fourierUnitary_dilation r hr f]
    have hinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr
    have hmul : a / r⁻¹ = a * r := by field_simp
    have h := ae_const_dilation hinv hc
    rw [hmul] at h
    exact ae_const_mono hb2 h

/-! ## Reflection and evenness -/

theorem ae_const_reflection {a : ℝ} {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a →
      ((l2Reflection f : SoninL2) : ℝ → ℂ) t = c := by
  have hneg := ((Measure.measurePreserving_neg
    (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae).eventually hc
  filter_upwards [l2Reflection_ae f, hneg] with x hr hx hmem
  rw [hr]
  refine hx ?_
  rw [centralInterval, Set.mem_Icc] at hmem ⊢
  exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩

theorem l2Reflection_mem_centralSoninExtendedCarrier {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) :
    l2Reflection f ∈ centralSoninExtendedCarrier a := by
  obtain ⟨⟨d, hd⟩, ⟨c, hc⟩⟩ := (mem_centralSoninExtendedCarrier_iff f).1 hf
  refine (mem_centralSoninExtendedCarrier_iff _).2 ⟨⟨d, ae_const_reflection hd⟩, ⟨c, ?_⟩⟩
  rw [fourierUnitary_l2Reflection]
  exact ae_const_reflection hc

theorem evenProjection_mem_centralSoninExtendedCarrier {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) :
    evenProjection f ∈ centralSoninExtendedCarrier a := by
  rw [evenProjection_apply]
  exact Submodule.smul_mem _ _
    (Submodule.add_mem _ hf (l2Reflection_mem_centralSoninExtendedCarrier hf))

theorem evenProjection_mem_evenSubspace (f : SoninL2) : evenProjection f ∈ evenSubspace :=
  ⟨f, rfl⟩

theorem dilation_mem_evenSubspace {r : ℝ} (hr : 0 < r) {f : SoninL2} (hf : f ∈ evenSubspace) :
    dilation r hr f ∈ evenSubspace := by
  rw [mem_evenSubspace_iff] at hf ⊢
  rw [l2Reflection_dilation, hf]

end RHTower

end
