import GaloisForLFunctions.ScaleSignedIncidenceCriticality.DepthResolutionNeedsAScaleBound

/-!
# The depth is the complete dilation invariant

Dilating the ordinates of a lattice configuration rescales its spacing and leaves its depth
untouched. On the two-coordinate family that is the whole structure: dilation acts transitively on
the scale and trivially on the depth, so

`DilationEquiv p q ↔ sdDepth p = sdDepth q`  (`dilationEquiv_iff_sdDepth_eq`),

the depth is a **complete** invariant of the dilation action. Two consequences, and they are the
point of the module.

* `faithful_sdDepth_iff_dilationEquiv` — a reading is faithful for the depth exactly when its
  fibres lie inside dilation orbits. Resolving the depth — on this family, resolving RH — is
  therefore not an analytic estimate but a *separation of orbits* of the dilation group.
* `not_faithful_scaleDepthReading` — and the fibres of a level certificate are as far from orbits
  as possible: a single fibre meets every depth in `(0, ½]`
  (`exists_mem_shadow_scaleDepthReading_sdDepth_eq`). The failure is not marginal; the certificate
  does not even partially separate the orbits.

Read with the rest of the programme this says what sort of object a closing mechanism has to be. The
scale readings of the field — apertures, radii, heights, Nyquist data — are coordinates *along* the
orbits and so are invisible to the invariant; a mechanism must instead be built from a quantity
that is constant on orbits and separates them. The depth is the only such quantity up to
reparametrisation (`sdDepth_isCompleteInvariant`), which is why no change of unit and no
strengthening of a scale certificate can help.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 1. The dilation action -/

/-- Two lattice data are *dilation equivalent* when a rescaling of the ordinates carries one to the
other: the scale is divided by `t` and the depth is unchanged. -/
def DilationEquiv (p q : ScaleDepthDatum) : Prop :=
  ∃ t : ℝ, 0 < t ∧ sdScale q = sdScale p / t ∧ sdDepth q = sdDepth p

theorem dilationEquiv_refl (p : ScaleDepthDatum) : DilationEquiv p p :=
  ⟨1, one_pos, by rw [div_one], rfl⟩

theorem dilationEquiv_symm {p q : ScaleDepthDatum} (h : DilationEquiv p q) :
    DilationEquiv q p := by
  obtain ⟨t, ht, hs, hd⟩ := h
  have htne : t ≠ 0 := ne_of_gt ht
  refine ⟨t⁻¹, by positivity, ?_, hd.symm⟩
  rw [hs]
  field_simp

/-- **The depth is a complete invariant of the dilation action.** -/
theorem dilationEquiv_iff_sdDepth_eq (p q : ScaleDepthDatum) :
    DilationEquiv p q ↔ sdDepth p = sdDepth q := by
  refine ⟨fun h => ?_, fun hd => ?_⟩
  · obtain ⟨-, -, -, hdd⟩ := h
    exact hdd.symm
  · have hp : sdScale p ≠ 0 := ne_of_gt p.2.1
    have hq : sdScale q ≠ 0 := ne_of_gt q.2.1
    refine ⟨sdScale p / sdScale q, div_pos p.2.1 q.2.1, ?_, hd.symm⟩
    field_simp

/-! ### 2. Faithfulness is orbit separation -/

theorem bddAbove_sdDepth_image (s : Set ScaleDepthDatum) : BddAbove (sdDepth '' s) :=
  ⟨1 / 2, by rintro x ⟨p, -, rfl⟩; exact p.2.2.2⟩

/-- **Faithfulness for the depth is separation of dilation orbits.** A reading determines the depth
exactly when data it identifies are dilation equivalent. -/
theorem faithful_sdDepth_iff_dilationEquiv {O : Type*} (r : ScaleDepthDatum → O) :
    Faithful sdDepth r ↔ ∀ p q : ScaleDepthDatum, r q = r p → DilationEquiv p q := by
  rw [faithful_iff fun p => bddAbove_sdDepth_image (shadow r p)]
  constructor
  · intro h p q hr
    rw [dilationEquiv_iff_sdDepth_eq]
    exact le_antisymm (h q p (mem_shadow_comm (r := r) hr)) (h p q hr)
  · intro h p q hq
    exact ((dilationEquiv_iff_sdDepth_eq p q).mp (h p q hq)).ge

/-- The depth itself is such a reading: it is a complete invariant, and the finest coarsening of
the data that still determines RH on this family. -/
theorem sdDepth_isCompleteInvariant :
    Faithful sdDepth sdDepth ∧ ∀ p q : ScaleDepthDatum, sdDepth q = sdDepth p →
      DilationEquiv p q :=
  ⟨(faithful_sdDepth_iff_dilationEquiv sdDepth).mpr
      fun p q hr => (dilationEquiv_iff_sdDepth_eq p q).mpr hr.symm,
    fun p q hr => (dilationEquiv_iff_sdDepth_eq p q).mpr hr.symm⟩

/-! ### 3. A level certificate does not separate orbits at all -/

/-- Inside one fibre of a level certificate every depth occurs. -/
theorem exists_mem_shadow_scaleDepthReading_sdDepth_eq {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    {p₀ : ScaleDepthDatum} (hp₀ : scaleDepthReading a η p₀) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    ∃ q ∈ shadow (scaleDepthReading a η) p₀, sdDepth q = δ := by
  refine ⟨⟨(2 * a, δ), by linarith, hδ, hδ'⟩, ?_, rfl⟩
  exact propext (iff_of_true
    (scaleDepthReading_of_dense hη ⟨(2 * a, δ), by linarith, hδ, hδ'⟩ le_rfl) hp₀)

/-- **A level certificate separates no orbit.** Its fibres meet every depth, so they are not
contained in any dilation orbit and the certificate is not faithful for the depth. -/
theorem not_faithful_scaleDepthReading {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    {p₀ : ScaleDepthDatum} (hp₀ : scaleDepthReading a η p₀) :
    ¬ Faithful sdDepth (scaleDepthReading a η) := by
  intro hf
  obtain ⟨q, hq, hqd⟩ :=
    exists_mem_shadow_scaleDepthReading_sdDepth_eq ha hη hp₀
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
  obtain ⟨q', hq', hqd'⟩ :=
    exists_mem_shadow_scaleDepthReading_sdDepth_eq ha hη hp₀
      (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  have hr : scaleDepthReading a η q' = scaleDepthReading a η q :=
    (mem_shadow_iff.mp hq').trans (mem_shadow_iff.mp hq).symm
  have := (dilationEquiv_iff_sdDepth_eq q q').mp
    ((faithful_sdDepth_iff_dilationEquiv (scaleDepthReading a η)).mp hf q q' hr)
  rw [hqd, hqd'] at this
  norm_num at this

/-- **Resolving RH on the lattice family is orbit separation.** The depth is the complete dilation
invariant, faithfulness for it is exactly the containment of fibres in orbits, and the scale
certificates of the field fail that containment maximally. -/
theorem resolvingTheDepthIsSeparatingOrbits {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    {p₀ : ScaleDepthDatum} (hp₀ : scaleDepthReading a η p₀) :
    (∀ p q : ScaleDepthDatum, DilationEquiv p q ↔ sdDepth p = sdDepth q) ∧
      (∀ (O : Type) (r : ScaleDepthDatum → O),
        Faithful sdDepth r ↔ ∀ p q : ScaleDepthDatum, r q = r p → DilationEquiv p q) ∧
      ¬ Faithful sdDepth (scaleDepthReading a η) :=
  ⟨dilationEquiv_iff_sdDepth_eq, fun _ r => faithful_sdDepth_iff_dilationEquiv r,
    not_faithful_scaleDepthReading ha hη hp₀⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
