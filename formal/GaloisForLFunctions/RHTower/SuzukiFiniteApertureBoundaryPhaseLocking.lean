import GaloisForLFunctions.HTGeometry.StrongResolventSpectralInclusion

/-!
# Suzuki's finite-aperture boundary-phase locking

Suzuki's finite-aperture construction produces, at every aperture, a closed symmetric operator with
deficiency indices `(1,1)` and a circle of self-adjoint extensions.  The apertures are nested: the
finite Hilbert spaces increase to the global one and the finite graphs exhaust the global graph.

Read through the Cayley transform the whole limit problem becomes subspace geometry.  The finite
ranges increase to the global range, so the range projections converge strongly; the finite
deficiency projections are the differences of the ambient and range projections, so they converge
strongly too; at deficiency index one the boundary transport is just the normalized image of one
global deficiency vector.  Locking the finite boundary phase to the global one therefore produces
finite self-adjoint extensions whose embedded Cayley transforms — hence, by the Cayley resolvent
formula, whose embedded resolvents — converge strongly to the global ones.

The statement is a generalized strong resolvent limit across varying Hilbert spaces: the finite
resolvent is embedded by the inclusion and precomposed with the ambient projection.  Nothing here
uses RH; the Suzuki instantiation of the hypotheses is a separate, RH-dependent matter.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology Submodule GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Preorder ι]

/-- The finite deficiency projection at one aperture: the part of the finite ambient space
orthogonal to the finite range. -/
def apertureDeficiencyProjection (HS M : ι → Submodule ℂ E)
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection] (i : ι) : E →L[ℂ] E :=
  (HS i ⊓ (M i)ᗮ).starProjection

/-- The boundary block of a finite self-adjoint extension at deficiency index one: one unit phase
times the rank-one transport between the two transported deficiency vectors. -/
def apertureBoundaryBlock (Ep Em : ι → E →L[ℂ] E) (ep em : E) (zeta : ι → ℂ) (i : ι) :
    E →L[ℂ] E :=
  zeta i • rankOneTransport (lineTransport (Ep i) ep) (lineTransport (Em i) em)

/-- The global boundary block. -/
def globalBoundaryBlock (ep em : E) (z : ℂ) : E →L[ℂ] E := z • rankOneTransport ep em

/-- **Automatic deficiency transport at one aperture chain.**  The transported deficiency vectors
converge to the global one. -/
theorem tendsto_apertureTransport (HS M : ι → Submodule ℂ E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdense : (⨆ i, HS i).topologicalClosure = ⊤)
    {e : E} (he : ‖e‖ = 1)
    (hline : ((⨆ i, M i).topologicalClosure)ᗮ = ℂ ∙ e) :
    Tendsto (fun i => lineTransport (apertureDeficiencyProjection HS M i) e) atTop (𝓝 e) := by
  have hpt : Tendsto (fun i => (HS i ⊓ (M i)ᗮ).starProjection e) atTop
      (𝓝 (((⨆ i, M i).topologicalClosure)ᗮ.starProjection e)) :=
    tendsto_deficiency_starProjection HS M hHS hM hle hdense e
  have hlim : ((⨆ i, M i).topologicalClosure)ᗮ.starProjection e = e := by
    rw [starProjection_eq_self_iff, hline]
    exact Submodule.mem_span_singleton_self e
  rw [hlim] at hpt
  exact tendsto_lineTransport (𝕜 := ℂ) (fun i => (HS i ⊓ (M i)ᗮ).starProjection) he hpt

/-- **Boundary blocks converge exactly when the phases do.**  This is the classification of
admissible phase schedules at deficiency index one. -/
theorem tendsto_opNorm_apertureBoundaryBlock_iff
    {Ep Em : ι → E →L[ℂ] E} {ep em : E} {zeta : ι → ℂ} {z : ℂ}
    (hep : ‖ep‖ = 1) (hem : ‖em‖ = 1)
    (hup : Tendsto (fun i => lineTransport (Ep i) ep) atTop (𝓝 ep))
    (hum : Tendsto (fun i => lineTransport (Em i) em) atTop (𝓝 em))
    (hbound : ∀ i, ‖zeta i‖ ≤ 1) :
    Tendsto (fun i => ‖apertureBoundaryBlock Ep Em ep em zeta i
        - globalBoundaryBlock ep em z‖) atTop (𝓝 0) ↔
      Tendsto zeta atTop (𝓝 z) := by
  constructor
  · intro h
    exact tendsto_phase_of_tendsto_opNorm (𝕜 := ℂ) hup hum hep hem hbound h
  · intro h
    exact tendsto_opNorm_phaseBlock (𝕜 := ℂ) h hup hum hbound

/-- **Boundary-phase locking.**  Along a nested aperture exhaustion with deficiency index one, the
phase-locked finite Cayley transforms converge strongly to the global Cayley transform. -/
theorem tendsto_apertureCayley_of_phaseLock
    (HS Mp Mm : ι → Submodule ℂ E)
    [∀ i, (HS i).HasOrthogonalProjection]
    [∀ i, (Mp i).HasOrthogonalProjection] [∀ i, (Mm i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (Mp i)ᗮ).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (Mm i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, Mp i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, Mm i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, Mp i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    [((⨆ i, Mm i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hMp : Monotone Mp) (hMm : Monotone Mm)
    (hlep : ∀ i, Mp i ≤ HS i) (hlem : ∀ i, Mm i ≤ HS i)
    (hdense : (⨆ i, HS i).topologicalClosure = ⊤)
    {ep em : E} [(ℂ ∙ ep).HasOrthogonalProjection] (hep : ‖ep‖ = 1) (hem : ‖em‖ = 1)
    (hlinep : ((⨆ i, Mp i).topologicalClosure)ᗮ = ℂ ∙ ep)
    (hlinem : ((⨆ i, Mm i).topologicalClosure)ᗮ = ℂ ∙ em)
    (V : E →L[ℂ] E) {zeta : ι → ℂ} {z : ℂ} (hbound : ∀ i, ‖zeta i‖ ≤ 1)
    (hlock : Tendsto zeta atTop (𝓝 z)) (x : E) :
    Tendsto (fun i => cayleyAssembly V
        (apertureBoundaryBlock (fun j => apertureDeficiencyProjection HS Mp j)
          (fun j => apertureDeficiencyProjection HS Mm j) ep em zeta i)
        ((Mp i).starProjection) (apertureDeficiencyProjection HS Mp i) x) atTop
      (𝓝 (cayleyAssembly V (globalBoundaryBlock ep em z)
        ((⨆ i, Mp i).topologicalClosure.starProjection)
        ((ℂ ∙ ep).starProjection) x)) := by
  have hQ : ∀ y : E, Tendsto (fun i => (Mp i).starProjection y) atTop
      (𝓝 ((⨆ i, Mp i).topologicalClosure.starProjection y)) := fun y =>
    starProjection_tendsto_closure_iSup Mp hMp y
  have hproj : ∀ y : E, (ℂ ∙ ep).starProjection y
      = ((⨆ i, Mp i).topologicalClosure)ᗮ.starProjection y := by
    intro y
    refine eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [← hlinep]
      exact Submodule.starProjection_apply_mem _ y
    · intro w hw
      rw [← hlinep] at hw
      exact (((⨆ i, Mp i).topologicalClosure)ᗮ).starProjection_inner_eq_zero y w hw
  have hEfun : ∀ y : E, Tendsto (fun i => apertureDeficiencyProjection HS Mp i y) atTop
      (𝓝 ((ℂ ∙ ep).starProjection y)) := by
    intro y
    rw [hproj y]
    exact tendsto_deficiency_starProjection HS Mp hHS hMp hlep hdense y
  have hEb : ∀ i, ‖apertureDeficiencyProjection HS Mp i‖ ≤ 1 := fun i =>
    starProjection_norm_le _
  have hup := tendsto_apertureTransport HS Mp hHS hMp hlep hdense hep hlinep
  have hum := tendsto_apertureTransport HS Mm hHS hMm hlem hdense hem hlinem
  have hW : Tendsto (fun i => ‖apertureBoundaryBlock
      (fun j => apertureDeficiencyProjection HS Mp j)
      (fun j => apertureDeficiencyProjection HS Mm j) ep em zeta i
      - globalBoundaryBlock ep em z‖) atTop (𝓝 0) :=
    tendsto_opNorm_phaseBlock (𝕜 := ℂ) hlock hup hum hbound
  exact tendsto_cayleyAssembly V (globalBoundaryBlock ep em z) hQ hEfun hEb hW x

/-- **Generalized strong resolvent limit.**  The phase-locked embedded finite resolvents converge
strongly to the global resolvent. -/
theorem tendsto_apertureResolvent_of_phaseLock
    (c : ℂ) {P Ca : ι → E →L[ℂ] E} {C : E →L[ℂ] E}
    (hP : ∀ x, Tendsto (fun i => P i x) atTop (𝓝 x))
    (hC : ∀ x, Tendsto (fun i => Ca i x) atTop (𝓝 (C x))) (x : E) :
    Tendsto (fun i => (c • (P i - Ca i)) x) atTop (𝓝 (cayleyResolvent c C x)) :=
  tendsto_cayleyResolvent c hP hC x

end

end GaloisForLFunctions.RHTower
