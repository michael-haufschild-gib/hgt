import GaloisForLFunctions.HTGeometry.ContinuousMapCauchyTransform
import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles

/-!
# A vanishing Cauchy transform annihilates every holomorphic function on the carrier

Let `K` be a compact set strictly inside a rectangle on which `G` is holomorphic.  The
`C(K, ℂ)`-valued function `v ↦ G v • (v − ·)⁻¹` is continuous on the boundary of the rectangle, so a
continuous functional and the evaluation maps both commute with its boundary integral.  Evaluating
gives `2πi·G` by the rectangle Cauchy formula, while applying the functional gives the integral of
`G v · Ĉ(v)`.  A functional with vanishing Cauchy transform therefore kills the restriction of `G`.

* `GaloisForLFunctions.HTGeometry.clm_rectangleIntegral`;
* `GaloisForLFunctions.HTGeometry.apply_eq_zero_of_cauchyTransform_eq_zero`.
-/

noncomputable section

open Complex Set MeasureTheory intervalIntegral
open scoped Interval

namespace GaloisForLFunctions.HTGeometry

/-- **A continuous linear map commutes with the rectangle boundary integral.** -/
theorem clm_rectangleIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : ℂ → E)
    (z w : ℂ) (hf : RectangleBorderIntegrable f z w) :
    L (RectangleIntegral f z w) = RectangleIntegral (fun v => L (f v)) z w := by
  simp only [RectangleIntegral, HIntegral, VIntegral, map_sub, map_add, map_smul]
  rw [← L.intervalIntegral_comp_comm hf.1, ← L.intervalIntegral_comp_comm hf.2.1,
    ← L.intervalIntegral_comp_comm hf.2.2.1, ← L.intervalIntegral_comp_comm hf.2.2.2]

variable {K : Set ℂ} [CompactSpace K]

/-- The Cauchy family of a holomorphic function, as a continuous-function-valued map. -/
def cauchyFamily (K : Set ℂ) [CompactSpace K] (G : ℂ → ℂ) (v : ℂ) : C(K, ℂ) :=
  G v • resolventInv K v

theorem cauchyFamily_apply {G : ℂ → ℂ} {v : ℂ} (hv : v ∉ K) (z : K) :
    cauchyFamily K G v z = G v * (v - (z : ℂ))⁻¹ := by
  rw [cauchyFamily, resolventInv_eq hv]
  simp

theorem continuousOn_cauchyFamily {G : ℂ → ℂ} {S : Set ℂ} (hS : S ⊆ Kᶜ)
    (hG : ContinuousOn G S) : ContinuousOn (cauchyFamily K G) S := by
  refine ContinuousOn.smul hG ?_
  exact (continuousOn_resolventInv (K := K)).mono hS

section Contour

variable {G : ℂ → ℂ} {z₁ z₂ : ℂ}

omit [CompactSpace K] in
/-- Points of a horizontal side of the rectangle are off a carrier strictly inside it. -/
theorem notMem_of_horizontal_side {y : ℝ} (hy : y = z₁.im ∨ y = z₂.im)
    (hKin : ∀ z ∈ K, z₁.re < z.re ∧ z.re < z₂.re ∧ z₁.im < z.im ∧ z.im < z₂.im) (x : ℝ) :
    ((x : ℂ) + (y : ℂ) * I) ∉ K := by
  intro hmem
  have h := hKin _ hmem
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  rw [him] at h
  rcases hy with hy | hy
  · exact absurd (hy ▸ h.2.2.1) (lt_irrefl _)
  · exact absurd (hy ▸ h.2.2.2) (lt_irrefl _)

omit [CompactSpace K] in
/-- Points of a vertical side of the rectangle are off a carrier strictly inside it. -/
theorem notMem_of_vertical_side {x : ℝ} (hx : x = z₁.re ∨ x = z₂.re)
    (hKin : ∀ z ∈ K, z₁.re < z.re ∧ z.re < z₂.re ∧ z₁.im < z.im ∧ z.im < z₂.im) (y : ℝ) :
    ((x : ℂ) + (y : ℂ) * I) ∉ K := by
  intro hmem
  have h := hKin _ hmem
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  rw [hre] at h
  rcases hx with hx | hx
  · exact absurd (hx ▸ h.1) (lt_irrefl _)
  · exact absurd (hx ▸ h.2.1) (lt_irrefl _)

theorem mem_rectangle_of_side {x y : ℝ} (hx : x ∈ Set.uIcc z₁.re z₂.re)
    (hy : y ∈ Set.uIcc z₁.im z₂.im) : ((x : ℂ) + (y : ℂ) * I) ∈ Complex.Rectangle z₁ z₂ := by
  constructor <;> simpa using ‹_›

/-- The Cauchy family is integrable along the boundary of a rectangle whose interior contains the
carrier. -/
theorem rectangleBorderIntegrable_cauchyFamily {U : Set ℂ} (hG : ContinuousOn G U)
    (hrect : Complex.Rectangle z₁ z₂ ⊆ U)
    (hKin : ∀ z ∈ K, z₁.re < z.re ∧ z.re < z₂.re ∧ z₁.im < z.im ∧ z.im < z₂.im) :
    RectangleBorderIntegrable (cauchyFamily K G) z₁ z₂ := by
  set S : Set ℂ := Complex.Rectangle z₁ z₂ \ K with hSdef
  have hSK : S ⊆ Kᶜ := fun v hv => hv.2
  have hGS : ContinuousOn G S := hG.mono fun v hv => hrect hv.1
  have hcf : ContinuousOn (cauchyFamily K G) S := continuousOn_cauchyFamily hSK hGS
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (hcf.comp (by fun_prop) ?_).intervalIntegrable
    intro x hx
    exact ⟨mem_rectangle_of_side hx Set.left_mem_uIcc,
      notMem_of_horizontal_side (Or.inl rfl) hKin x⟩
  · refine (hcf.comp (by fun_prop) ?_).intervalIntegrable
    intro x hx
    exact ⟨mem_rectangle_of_side hx Set.right_mem_uIcc,
      notMem_of_horizontal_side (Or.inr rfl) hKin x⟩
  · refine (hcf.comp (by fun_prop) ?_).intervalIntegrable
    intro y hy
    exact ⟨mem_rectangle_of_side Set.right_mem_uIcc hy,
      notMem_of_vertical_side (Or.inr rfl) hKin y⟩
  · refine (hcf.comp (by fun_prop) ?_).intervalIntegrable
    intro y hy
    exact ⟨mem_rectangle_of_side Set.left_mem_uIcc hy,
      notMem_of_vertical_side (Or.inl rfl) hKin y⟩

/-- **The rectangle Cauchy integral formula**, in the boundary-integral normalisation. -/
theorem rectangleIntegral_cauchyKernel {U : Set ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hrect : Complex.Rectangle z₁ z₂ ⊆ U) {p : ℂ}
    (hp : z₁.re < p.re ∧ p.re < z₂.re ∧ z₁.im < p.im ∧ p.im < z₂.im) :
    RectangleIntegral (fun v => G v * (v - p)⁻¹) z₁ z₂ = 2 * ↑Real.pi * I * G p := by
  have hzw : z₁.re ≤ z₂.re := le_of_lt (lt_trans hp.1 hp.2.1)
  have hzw' : z₁.im ≤ z₂.im := le_of_lt (lt_trans hp.2.2.1 hp.2.2.2)
  have hnhds : Complex.Rectangle z₁ z₂ ∈ nhds p := by
    rw [rectangle_mem_nhds_iff]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, Set.uIoo_of_le hzw]
      exact ⟨hp.1, hp.2.1⟩
    · rw [Set.mem_preimage, Set.uIoo_of_le hzw']
      exact ⟨hp.2.2.1, hp.2.2.2⟩
  have hpU : p ∈ U := hrect (mem_of_mem_nhds hnhds)
  have hds : DifferentiableOn ℂ (dslope G p) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hpU)).mpr hG
  have hpp : Set.EqOn ((fun v => G v * (v - p)⁻¹) - fun s => G p / (s - p)) (dslope G p)
      (Complex.Rectangle z₁ z₂ \ {p}) := by
    intro s hs
    have hsp : s ≠ p := hs.2
    have hne : s - p ≠ 0 := sub_ne_zero.mpr hsp
    rw [Pi.sub_apply, dslope_of_ne _ hsp, slope_def_field]
    field_simp
  have hres := ResidueTheoremOnRectangleWithSimplePole (f := fun v => G v * (v - p)⁻¹)
    (g := dslope G p) (A := G p) hzw hzw' hnhds (hds.mono hrect) hpp
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [RectangleIntegral', smul_eq_mul] at hres
  field_simp at hres
  have hfun : (fun v => G v * (v - p)⁻¹) = fun v => G v / (v - p) := by
    funext v
    rw [div_eq_mul_inv]
  rw [hfun]
  exact hres

omit [CompactSpace K] in
/-- Two functions agreeing off the carrier have the same rectangle boundary integral, provided the
carrier is strictly inside the rectangle. -/
theorem rectangleIntegral_congr_off {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E}
    (hKin : ∀ z ∈ K, z₁.re < z.re ∧ z.re < z₂.re ∧ z₁.im < z.im ∧ z.im < z₂.im)
    (h : ∀ v, v ∉ K → f v = g v) :
    RectangleIntegral f z₁ z₂ = RectangleIntegral g z₁ z₂ := by
  simp only [RectangleIntegral, HIntegral, VIntegral]
  rw [intervalIntegral.integral_congr
      (fun x _ => h _ (notMem_of_horizontal_side (Or.inl rfl) hKin x)),
    intervalIntegral.integral_congr
      (fun x _ => h _ (notMem_of_horizontal_side (Or.inr rfl) hKin x)),
    intervalIntegral.integral_congr
      (fun y _ => h _ (notMem_of_vertical_side (Or.inr rfl) hKin y)),
    intervalIntegral.integral_congr
      (fun y _ => h _ (notMem_of_vertical_side (Or.inl rfl) hKin y))]

/-- **A functional whose Cauchy transform vanishes off the carrier annihilates the restriction of
every function holomorphic on a rectangle containing the carrier in its interior.** -/
theorem apply_eq_zero_of_cauchyTransform_eq_zero {U : Set ℂ} (hU : IsOpen U)
    (hG : DifferentiableOn ℂ G U) (hrect : Complex.Rectangle z₁ z₂ ⊆ U)
    (hKin : ∀ z ∈ K, z₁.re < z.re ∧ z.re < z₂.re ∧ z₁.im < z.im ∧ z.im < z₂.im)
    (L : C(K, ℂ) →L[ℂ] ℂ) (hzero : ∀ v, v ∉ K → cauchyTransform L v = 0)
    (gK : C(K, ℂ)) (hgK : ∀ z : K, gK z = G (z : ℂ)) :
    L gK = 0 := by
  have hbi := rectangleBorderIntegrable_cauchyFamily (K := K) hG.continuousOn hrect hKin
  have hLv : ∀ v, v ∉ K → L (cauchyFamily K G v) = 0 := by
    intro v hv
    rw [cauchyFamily, map_smul, smul_eq_mul, ← cauchyTransform_eq_apply_resolventInv,
      hzero v hv, mul_zero]
  have hLzero : L (RectangleIntegral (cauchyFamily K G) z₁ z₂) = 0 := by
    rw [clm_rectangleIntegral L _ z₁ z₂ hbi,
      rectangleIntegral_congr_off (g := fun _ : ℂ => (0 : ℂ)) hKin hLv]
    simp [RectangleIntegral, HIntegral, VIntegral]
  have hEval : RectangleIntegral (cauchyFamily K G) z₁ z₂ = (2 * (Real.pi : ℂ) * I) • gK := by
    ext z
    have hcomm := clm_rectangleIntegral (ContinuousMap.evalCLM ℂ z) (cauchyFamily K G) z₁ z₂ hbi
    have hpt : ∀ v, v ∉ K → (ContinuousMap.evalCLM ℂ z) (cauchyFamily K G v)
        = G v * (v - (z : ℂ))⁻¹ := fun v hv => cauchyFamily_apply hv z
    have hcif := rectangleIntegral_cauchyKernel (G := G) hU hG hrect (hKin (z : ℂ) z.2)
    calc (RectangleIntegral (cauchyFamily K G) z₁ z₂) z
        = (ContinuousMap.evalCLM ℂ z) (RectangleIntegral (cauchyFamily K G) z₁ z₂) := rfl
      _ = RectangleIntegral (fun v => (ContinuousMap.evalCLM ℂ z) (cauchyFamily K G v)) z₁ z₂ :=
          hcomm
      _ = RectangleIntegral (fun v => G v * (v - (z : ℂ))⁻¹) z₁ z₂ :=
          rectangleIntegral_congr_off hKin hpt
      _ = 2 * (Real.pi : ℂ) * I * G (z : ℂ) := hcif
      _ = ((2 * (Real.pi : ℂ) * I) • gK) z := by
          rw [ContinuousMap.smul_apply, smul_eq_mul, hgK z]
  rw [hEval, map_smul, smul_eq_mul] at hLzero
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact (mul_eq_zero.mp hLzero).resolve_left h2pi

end Contour

end GaloisForLFunctions.HTGeometry
