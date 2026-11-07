import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsExist
import GaloisForLFunctions.RHTower.DeckIncompleteEisensteinDensity
import GaloisForLFunctions.BlackHoleRingdown.TheGeneralHorizonData

/-!
# The odd sector of the horizon is a cavity

The mirror `ι z = -z̄` is the action of `diag(-1, 1) ∈ GL₂(ℝ)` (`mirrorGL_smul`), so it preserves the
hyperbolic measure; it maps the modular cell to itself, so it acts on horizon data as a unitary
involution `M` (`mirrorL2`, `mirrorL2_mirrorL2`).

Every incomplete Eisenstein series is mirror-even (`mirrorL2_incEisL2`): the mirror permutes the
coprime rows `(c, d) ↦ (-c, d)` and preserves heights. Hence a mirror-odd datum `f` is orthogonal
to the whole Eisenstein space, `⟨g, f⟩ = ⟨Mg, Mf⟩ = -⟨g, f⟩`, and so it is cuspidal
(`mem_cuspidalL2Closure_of_odd`).

**The odd half of the horizon is a cavity.** Every mirror-odd square-integrable horizon datum is a
superposition of cusp forms (`hasSum_odd`), so it never rings down in the modes of the zeros of `ξ`:
the zeros couple only to the mirror-even half. For every datum `f`, the odd part `f - Mf` is
cuspidal (`sub_mirrorL2_mem_cuspidal`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace OddCusp

namespace OddSector

/-! ### The mirror as an isometry of the horizon -/

/-- The mirror as an element of `GL₂(ℝ)`. -/
def mirrorGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

theorem mirrorGL_smul (z : ℍ) : mirrorGL • z = mirror z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul, coe_mirror]
  simp [UpperHalfPlane.σ, UpperHalfPlane.num, UpperHalfPlane.denom, mirrorGL]
  split_ifs with h
  · norm_num at h
  · rfl

theorem mirror_mirror (z : ℍ) : mirror (mirror z) = z :=
  UpperHalfPlane.ext (by simp)

theorem continuous_mirror : Continuous mirror := by
  have e : mirror = fun z : ℍ => mirrorGL • z := funext fun z => (mirrorGL_smul z).symm
  rw [e]
  exact continuous_const_smul mirrorGL

theorem measurePreserving_mirror : MeasurePreserving mirror (volume : Measure ℍ) volume := by
  have e : (fun z : ℍ => mirrorGL • z) = mirror := funext mirrorGL_smul
  refine ⟨continuous_mirror.measurable, ?_⟩
  rw [← e]
  exact (measurePreserving_smul mirrorGL (volume : Measure ℍ)).map_eq

theorem mirror_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) : mirror z ∈ ModularGroup.fd := by
  obtain ⟨h1, h2⟩ := hz
  constructor
  · have e : Complex.normSq ((mirror z : ℍ) : ℂ) = Complex.normSq (z : ℂ) := by
      rw [coe_mirror, Complex.normSq_neg, Complex.normSq_conj]
    rw [e]
    exact h1
  · have e : (mirror z).re = -z.re := by
      show (-(starRingEnd ℂ) (z : ℂ)).re = -(z : ℂ).re
      simp
    rw [e, abs_neg]
    exact h2

theorem preimage_mirror_fd : mirror ⁻¹' ModularGroup.fd = ModularGroup.fd := by
  ext z
  constructor
  · intro hz
    have := mirror_mem_fd hz
    rwa [mirror_mirror] at this
  · exact mirror_mem_fd

theorem measurePreserving_mirror_fd :
    MeasurePreserving mirror MaassCongruenceL2.cellMeasure MaassCongruenceL2.cellMeasure := by
  have h := measurePreserving_mirror.restrict_preimage GaloisForLFunctions.HTGeometry.measurableSet_fd
  rwa [preimage_mirror_fd] at h

/-- **The mirror of horizon data**, a linear isometry of `L²` of the cell. -/
def mirrorL2 : DeckL2 0 →ₗᵢ[ℂ] DeckL2 0 :=
  Lp.compMeasurePreservingₗᵢ ℂ mirror measurePreserving_mirror_fd

theorem coeFn_mirrorL2 (f : DeckL2 0) :
    ⇑(mirrorL2 f) =ᵐ[MaassCongruenceL2.cellMeasure] ⇑f ∘ mirror :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_mirror_fd

theorem mirrorL2_mirrorL2 (f : DeckL2 0) : mirrorL2 (mirrorL2 f) = f := by
  apply Lp.ext
  have h1 := coeFn_mirrorL2 (mirrorL2 f)
  have h2 := measurePreserving_mirror_fd.quasiMeasurePreserving.ae_eq_comp (coeFn_mirrorL2 f)
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]
  simp [mirror_mirror]

/-! ### Incomplete Eisenstein series are mirror-even -/

/-- The mirror is an involution of the modular group by conjugation. -/
theorem mirrorSL_mirrorSL (g : SL(2, ℤ)) : mirrorSL (mirrorSL g) = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The row `(c, d) ↦ (-c, d)`. -/
def negRow (p : EisensteinSeries.gammaSet 1 1 0) : EisensteinSeries.gammaSet 1 1 0 :=
  ⟨![-p.1 0, p.1 1], by
    rw [EisensteinSeries.gammaSet_one_mem_iff]
    have h := (EisensteinSeries.gammaSet_one_mem_iff 1 p.1).mp p.2
    simpa using h⟩

theorem negRow_negRow (p : EisensteinSeries.gammaSet 1 1 0) : negRow (negRow p) = p := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [negRow]

/-- The row involution as an equivalence. -/
def negRowEquiv : EisensteinSeries.gammaSet 1 1 0 ≃ EisensteinSeries.gammaSet 1 1 0 :=
  ⟨negRow, negRow, negRow_negRow, negRow_negRow⟩

/-- Mirroring the point mirrors the row: `Im(M_p ι z) = Im(M_{p'} z)`. -/
theorem im_gammaSetMatrix_smul_mirror (p : EisensteinSeries.gammaSet 1 1 0) (z : ℍ) :
    (GaloisForLFunctions.HTGeometry.gammaSetMatrix p • mirror z).im =
      (GaloisForLFunctions.HTGeometry.gammaSetMatrix (negRow p) • z).im := by
  set g := GaloisForLFunctions.HTGeometry.gammaSetMatrix p
  have e : g • mirror z = mirror (mirrorSL g • z) := by
    rw [mirror_smul, mirrorSL_mirrorSL]
  rw [e, mirror_im]
  obtain ⟨n, hn⟩ := GaloisForLFunctions.HTGeometry.coe_smul_eq_coe_smul_add_int_of_bottomRow_eq
    (mirrorSL g) (GaloisForLFunctions.HTGeometry.gammaSetMatrix (negRow p))
    (by simp [g, negRow]) (by simp [g, negRow]) z
  show ((mirrorSL g • z : ℍ) : ℂ).im = ((GaloisForLFunctions.HTGeometry.gammaSetMatrix (negRow p) • z : ℍ) : ℂ).im
  rw [hn]
  simp

theorem deckRho_zero_symm (g : SL(2, ℤ)) (v : DeckSpace 0) : (deckRho 0 g).symm v = v := by
  have h : deckRho 0 g v = v := by
    ext q
    rw [deckRho_apply, Subsingleton.elim (q * _) q]
  calc (deckRho 0 g).symm v = (deckRho 0 g).symm (deckRho 0 g v) := by rw [h]
    _ = v := (deckRho 0 g).symm_apply_apply v

theorem incEis_mirror (ψ : ℝ → ℂ) (v : DeckSpace 0) (z : ℍ) :
    incEis ψ v (mirror z) = incEis ψ v z := by
  unfold incEis
  rw [← negRowEquiv.tsum_eq (fun p => eisTerm ψ v p z)]
  refine tsum_congr fun p => ?_
  simp only [eisTerm, deckRho_zero_symm]
  rw [im_gammaSetMatrix_smul_mirror]
  rfl

/-- **Every incomplete Eisenstein series is mirror-even.** -/
theorem mirrorL2_incEisL2 (ψ : HeightProfile) (v : DeckSpace 0) :
    mirrorL2 (incEisL2 ψ v) = incEisL2 ψ v := by
  apply Lp.ext
  have h1 := coeFn_mirrorL2 (incEisL2 ψ v)
  have h2 := measurePreserving_mirror_fd.quasiMeasurePreserving.ae_eq_comp (incEisL2_coeFn ψ v)
  filter_upwards [h1, h2, incEisL2_coeFn ψ v] with z hz1 hz2 hz3
  rw [hz1, hz2]
  simp only [Function.comp_apply]
  rw [incEis_mirror, hz3]

/-! ### The odd sector is cuspidal -/

/-- A mirror-odd datum is orthogonal to the Eisenstein space. -/
theorem inner_eisSpace_eq_zero_of_odd {f : DeckL2 0} (hf : mirrorL2 f = -f) {g : DeckL2 0}
    (hg : g ∈ eisSpace 0) : ⟪g, f⟫_ℂ = 0 := by
  set Z : Submodule ℂ (DeckL2 0) :=
    { carrier := {g | ⟪g, f⟫_ℂ = 0}
      add_mem' := fun {a b} ha hb => by
        change ⟪a + b, f⟫_ℂ = 0
        rw [inner_add_left, show ⟪a, f⟫_ℂ = 0 from ha, show ⟪b, f⟫_ℂ = 0 from hb, add_zero]
      zero_mem' := by
        change ⟪(0 : DeckL2 0), f⟫_ℂ = 0
        exact inner_zero_left _
      smul_mem' := fun c a ha => by
        change ⟪c • a, f⟫_ℂ = 0
        rw [inner_smul_left, show ⟪a, f⟫_ℂ = 0 from ha, mul_zero] }
  have hclosed : IsClosed (Z : Set (DeckL2 0)) :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hgen : eisGen 0 ⊆ Z := by
    rintro _ ⟨ψ, -, v, -, rfl⟩
    change ⟪incEisL2 ψ v, f⟫_ℂ = 0
    have h := mirrorL2.inner_map_map (incEisL2 ψ v) f
    rw [mirrorL2_incEisL2, hf, inner_neg_right] at h
    linear_combination -h / 2
  exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 hgen) hclosed hg

/-- **The odd sector of the horizon is cuspidal.** -/
theorem mem_cuspidalL2Closure_of_odd {f : DeckL2 0} (hf : mirrorL2 f = -f) :
    f ∈ cuspidalL2Closure 0 :=
  (mem_cuspidalL2Closure_iff_eisSpace f).2
    ⟨mem_deckCentralFixedL2_zero f, fun _ hg => inner_eisSpace_eq_zero_of_odd hf hg⟩

/-- For every datum, the odd part is cuspidal: the zeros couple only to the even part. -/
theorem sub_mirrorL2_mem_cuspidal (f : DeckL2 0) : f - mirrorL2 f ∈ cuspidalL2Closure 0 :=
  mem_cuspidalL2Closure_of_odd (by rw [map_sub, mirrorL2_mirrorL2, neg_sub])

/-- **The odd sector is a cavity**: a mirror-odd datum is the sum of its components on the cusp
forms. -/
theorem hasSum_odd {f : DeckL2 0} (hf : mirrorL2 f = -f) :
    HasSum (fun i => (cuspEigenBasis 0).repr ⟨f, mem_cuspidalL2Closure_of_odd hf⟩ i •
      ((cuspEigenBasis 0 i : CuspidalL2 0) : DeckL2 0)) f := by
  have h := (cuspEigenBasis 0).hasSum_repr ⟨f, mem_cuspidalL2Closure_of_odd hf⟩
  have h2 := h.map (cuspidalL2Closure 0).subtypeL (cuspidalL2Closure 0).subtypeL.continuous
  convert h2 using 1
  funext i
  simp

end OddSector

end GaloisForLFunctions.BlackHoleRingdown
