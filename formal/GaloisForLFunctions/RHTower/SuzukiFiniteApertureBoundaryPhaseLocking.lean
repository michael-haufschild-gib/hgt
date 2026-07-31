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

/-! ## Theorem 4.2: necessity of the phase lock -/

/-- The finite boundary block in transported coordinates. -/
theorem apertureBoundaryBlock_apply (Ep Em : ι → E →L[ℂ] E) (ep em : E) (zeta : ι → ℂ) (i : ι)
    (y : E) :
    apertureBoundaryBlock Ep Em ep em zeta i y
      = (zeta i * inner ℂ (lineTransport (Ep i) ep) y) • lineTransport (Em i) em := by
  rw [apertureBoundaryBlock, smul_apply, rankOneTransport_apply, smul_smul]

theorem inner_self_eq_one {v : E} (hv : ‖v‖ = 1) : (inner ℂ v v : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hv]
  norm_num

/-- **Theorem 4.2, necessity.**  If the boundary parts of arbitrary finite self-adjoint extensions
converge to the global boundary part, their phases converge to the global phase.  The identity is
read off at the deficiency image of the global transported vector, so only finite boundary data is
tested. -/
theorem tendsto_phase_of_tendsto_apertureBoundary
    {Ep Em : ι → E →L[ℂ] E} {ep em : E} {zeta : ι → ℂ} {z : ℂ}
    (hep : ‖ep‖ = 1) (hem : ‖em‖ = 1) (hbound : ∀ i, ‖zeta i‖ ≤ 1)
    (hEp : Tendsto (fun i => Ep i ep) atTop (𝓝 ep))
    (hum : Tendsto (fun i => lineTransport (Em i) em) atTop (𝓝 em))
    (hlim : Tendsto (fun i => apertureBoundaryBlock Ep Em ep em zeta i (Ep i ep)) atTop
      (𝓝 (globalBoundaryBlock ep em z ep))) :
    Tendsto zeta atTop (𝓝 z) := by
  have hup : Tendsto (fun i => lineTransport (Ep i) ep) atTop (𝓝 ep) :=
    tendsto_lineTransport (𝕜 := ℂ) Ep hep hEp
  have hglobal : globalBoundaryBlock ep em z ep = z • em := by
    rw [globalBoundaryBlock, smul_apply, rankOneTransport_apply, inner_self_eq_one hep, one_smul]
  rw [hglobal] at hlim
  have hfin : Tendsto (fun i => (zeta i * inner ℂ (lineTransport (Ep i) ep) (Ep i ep))
      • lineTransport (Em i) em) atTop (𝓝 (z • em)) := by
    refine hlim.congr fun i => ?_
    rw [apertureBoundaryBlock_apply]
  -- pair against the global minus vector
  have hpair := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := em)) hfin
  have hrhs : (inner ℂ em (z • em) : ℂ) = z := by
    rw [inner_smul_right, inner_self_eq_one hem, mul_one]
  rw [hrhs] at hpair
  have hprod : Tendsto (fun i => zeta i * (inner ℂ (lineTransport (Ep i) ep) (Ep i ep)
      * inner ℂ em (lineTransport (Em i) em))) atTop (𝓝 z) := by
    refine hpair.congr fun i => ?_
    rw [inner_smul_right]
    ring
  -- the correction factor tends to one
  have hc : Tendsto (fun i => (inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)) atTop (𝓝 1) := by
    have := Filter.Tendsto.inner (𝕜 := ℂ) hup hEp
    rwa [inner_self_eq_one hep] at this
  have hw : Tendsto (fun i => (inner ℂ em (lineTransport (Em i) em) : ℂ)) atTop (𝓝 1) := by
    have := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := em)) hum
    rwa [inner_self_eq_one hem] at this
  have hcorr : Tendsto (fun i => (inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)
      * inner ℂ em (lineTransport (Em i) em)) atTop (𝓝 1) := by
    simpa using hc.mul hw
  -- split off the correction
  have hsplit : ∀ i, zeta i - z
      = (zeta i * ((inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)
          * inner ℂ em (lineTransport (Em i) em)) - z)
        + zeta i * (1 - (inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)
          * inner ℂ em (lineTransport (Em i) em)) := by
    intro i
    ring
  have h1 : Tendsto (fun i => zeta i * ((inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)
      * inner ℂ em (lineTransport (Em i) em)) - z) atTop (𝓝 0) := by
    simpa using hprod.sub (tendsto_const_nhds (x := z))
  have h2 : Tendsto (fun i => zeta i * (1 - (inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)
      * inner ℂ em (lineTransport (Em i) em))) atTop (𝓝 0) := by
    have hgap : Tendsto (fun i => ‖1 - (inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)
        * inner ℂ em (lineTransport (Em i) em)‖) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (1 : ℂ))).sub hcorr
      simpa using this.norm
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hgap
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_right (hbound i)
      (norm_nonneg (1 - (inner ℂ (lineTransport (Ep i) ep) (Ep i ep) : ℂ)
        * inner ℂ em (lineTransport (Em i) em)))
    simpa using this
  have hzero : Tendsto (fun i => zeta i - z) atTop (𝓝 0) := by
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr fun i => (hsplit i).symm
  simpa using hzero.add_const z

end

end GaloisForLFunctions.RHTower
