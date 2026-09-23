import Mathlib

/-!
# Rigidity of marked cyclic unitary presentations

Two unitary group actions on Hilbert spaces with distinguished cyclic vectors and the *same*
matrix coefficient are uniquely equivalent as marked presentations: there is exactly one unitary
carrying one cyclic vector to the other and intertwining the two actions.

The proof is the Gelfand--Naimark--Segal uniqueness argument.  All inner products between orbit
vectors are computed by the matrix coefficient, `⟪U_g Ω, U_h Ω⟫ = ⟪Ω, U_{g⁻¹h} Ω⟫`, so the two
orbit maps `(G →₀ ℂ) → H` have the same kernel and the induced map between their ranges is
isometric; density extends it to a unitary, and the same density forces uniqueness.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

variable {G : Type*} [Group G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

/-! ## The orbit map -/

/-- The cyclic orbit map `c ↦ ∑_g c_g · U_g Ω`. -/
def cyclicMap (U : G →* (H ≃ₗᵢ[ℂ] H)) (Ω : H) : (G →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ fun g : G => U g Ω

theorem cyclicMap_apply (U : G →* (H ≃ₗᵢ[ℂ] H)) (Ω : H) (c : G →₀ ℂ) :
    cyclicMap U Ω c = c.sum fun g a => a • U g Ω :=
  Finsupp.linearCombination_apply ℂ c

theorem range_cyclicMap (U : G →* (H ≃ₗᵢ[ℂ] H)) (Ω : H) :
    LinearMap.range (cyclicMap U Ω) = Submodule.span ℂ (Set.range fun g : G => U g Ω) :=
  Finsupp.range_linearCombination ℂ

theorem cyclicMap_single (U : G →* (H ≃ₗᵢ[ℂ] H)) (Ω : H) (g : G) :
    cyclicMap U Ω (Finsupp.single g 1) = U g Ω := by
  rw [cyclicMap, Finsupp.linearCombination_single, one_smul]

theorem monoidHom_apply_mul (U : G →* (H ≃ₗᵢ[ℂ] H)) (g h : G) (x : H) :
    U (g * h) x = U g (U h x) := by
  rw [map_mul]
  rfl

/-- The Gram kernel of the orbit is computed by the matrix coefficient. -/
theorem inner_orbit (U : G →* (H ≃ₗᵢ[ℂ] H)) (Ω : H) (g h : G) :
    (inner ℂ (U g Ω) (U h Ω) : ℂ) = inner ℂ Ω (U (g⁻¹ * h) Ω) := by
  have hUg : U g (U (g⁻¹ * h) Ω) = U h Ω := by
    rw [← monoidHom_apply_mul U g (g⁻¹ * h) Ω]
    congr 2
    group
  rw [← hUg, LinearIsometryEquiv.inner_map_map]

theorem inner_cyclicMap (U : G →* (H ≃ₗᵢ[ℂ] H)) (Ω : H) (c d : G →₀ ℂ) :
    (inner ℂ (cyclicMap U Ω c) (cyclicMap U Ω d) : ℂ)
      = ∑ g ∈ c.support, ∑ h ∈ d.support,
          (starRingEnd ℂ) (c g) * d h * inner ℂ Ω (U (g⁻¹ * h) Ω) := by
  rw [cyclicMap_apply, cyclicMap_apply, Finsupp.sum, Finsupp.sum, sum_inner]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_orbit]
  ring

/-! ## Equal coefficients give equal norms -/

variable {U : G →* (H ≃ₗᵢ[ℂ] H)} {U' : G →* (H' ≃ₗᵢ[ℂ] H')} {Ω : H} {Ω' : H'}

theorem norm_cyclicMap_eq
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω')) (c : G →₀ ℂ) :
    ‖cyclicMap U Ω c‖ = ‖cyclicMap U' Ω' c‖ := by
  have heq : (inner ℂ (cyclicMap U Ω c) (cyclicMap U Ω c) : ℂ)
      = inner ℂ (cyclicMap U' Ω' c) (cyclicMap U' Ω' c) := by
    rw [inner_cyclicMap, inner_cyclicMap]
    exact Finset.sum_congr rfl fun g _ =>
      Finset.sum_congr rfl fun h _ => by rw [hcoef]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at heq
  have hsq : ‖cyclicMap U Ω c‖ ^ (2 : ℕ) = ‖cyclicMap U' Ω' c‖ ^ (2 : ℕ) := by
    exact_mod_cast heq
  rw [← Real.sqrt_sq (norm_nonneg (cyclicMap U Ω c)),
    ← Real.sqrt_sq (norm_nonneg (cyclicMap U' Ω' c)), hsq]

theorem ker_cyclicMap_eq
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω')) :
    LinearMap.ker (cyclicMap U Ω) = LinearMap.ker (cyclicMap U' Ω') := by
  ext c
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    have hn := norm_cyclicMap_eq hcoef c
    rw [h, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm
  · intro h
    have hn := norm_cyclicMap_eq hcoef c
    rw [h, norm_zero] at hn
    exact norm_eq_zero.mp hn

/-! ## The induced isometry between the cyclic spans -/

/-- The transfer map between the two cyclic spans. -/
def cyclicTransfer (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω')) :
    (LinearMap.range (cyclicMap U Ω)) →ₗ[ℂ] H' :=
  (Submodule.liftQ (LinearMap.ker (cyclicMap U Ω)) (cyclicMap U' Ω')
      (le_of_eq (ker_cyclicMap_eq hcoef))).comp
    ((cyclicMap U Ω).quotKerEquivRange.symm : _ →ₗ[ℂ] _)

theorem cyclicTransfer_apply
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω')) (c : G →₀ ℂ) :
    cyclicTransfer hcoef ⟨cyclicMap U Ω c, LinearMap.mem_range_self _ c⟩ = cyclicMap U' Ω' c := by
  have hmk : (cyclicMap U Ω).quotKerEquivRange.symm ⟨cyclicMap U Ω c, LinearMap.mem_range_self _ c⟩
      = Submodule.Quotient.mk c := by
    apply (cyclicMap U Ω).quotKerEquivRange.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  rw [cyclicTransfer, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [hmk, Submodule.liftQ_apply]

theorem norm_cyclicTransfer
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω'))
    (y : LinearMap.range (cyclicMap U Ω)) : ‖cyclicTransfer hcoef y‖ = ‖y‖ := by
  obtain ⟨c, hc⟩ := y.2
  have hy : y = ⟨cyclicMap U Ω c, LinearMap.mem_range_self _ c⟩ := Subtype.ext hc.symm
  rw [hy, cyclicTransfer_apply]
  exact (norm_cyclicMap_eq hcoef c).symm

/-- The transfer map as a linear isometry of the cyclic span into the target. -/
def cyclicIsometry (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω')) :
    (LinearMap.range (cyclicMap U Ω)) →ₗᵢ[ℂ] H' where
  toLinearMap := cyclicTransfer hcoef
  norm_map' := norm_cyclicTransfer hcoef

/-! ## Extension by density -/

theorem isUniformInducing_subtypeL (p : Submodule ℂ H) :
    IsUniformInducing (p.subtypeL) :=
  isometry_subtype_coe.isUniformInducing

theorem denseRange_subtypeL {p : Submodule ℂ H} (hp : Dense (p : Set H)) :
    DenseRange (p.subtypeL) := by
  have hrange : Set.range (p.subtypeL) = (p : Set H) := Subtype.range_coe
  rw [DenseRange, hrange]
  exact hp

variable [CompleteSpace H] [CompleteSpace H']

/-- The marked transfer, extended to the whole space. -/
def markedMap (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω')) : H →L[ℂ] H' :=
  ContinuousLinearMap.extend (cyclicIsometry hcoef).toContinuousLinearMap
    (LinearMap.range (cyclicMap U Ω)).subtypeL

omit [CompleteSpace H] in
theorem markedMap_apply
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω'))
    (hcyc : Dense ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H))
    (y : LinearMap.range (cyclicMap U Ω)) :
    markedMap hcoef (y : H) = cyclicTransfer hcoef y :=
  ContinuousLinearMap.extend_eq _ (denseRange_subtypeL hcyc)
    (isUniformInducing_subtypeL _) y

omit [CompleteSpace H] in
theorem markedMap_cyclicMap
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω'))
    (hcyc : Dense ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H)) (c : G →₀ ℂ) :
    markedMap hcoef (cyclicMap U Ω c) = cyclicMap U' Ω' c := by
  have h := markedMap_apply hcoef hcyc ⟨cyclicMap U Ω c, LinearMap.mem_range_self _ c⟩
  rw [cyclicTransfer_apply] at h
  exact h

omit [CompleteSpace H] in
theorem norm_markedMap
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω'))
    (hcyc : Dense ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H)) (x : H) :
    ‖markedMap hcoef x‖ = ‖x‖ := by
  have hfun : (fun x : H => ‖markedMap hcoef x‖) = fun x : H => ‖x‖ := by
    refine Continuous.ext_on hcyc ((markedMap hcoef).continuous.norm) continuous_norm ?_
    rintro y hy
    show ‖markedMap hcoef y‖ = ‖y‖
    have hval := markedMap_apply hcoef hcyc ⟨y, hy⟩
    rw [show ((⟨y, hy⟩ : LinearMap.range (cyclicMap U Ω)) : H) = y from rfl] at hval
    rw [hval, norm_cyclicTransfer]
    rfl
  exact congrFun hfun x

/-! ## The marked unitary -/

omit [CompleteSpace H] in
theorem markedMap_omega
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω'))
    (hcyc : Dense ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H)) :
    markedMap hcoef Ω = Ω' := by
  have h1 : cyclicMap U Ω (Finsupp.single (1 : G) 1) = Ω := by
    rw [cyclicMap_single, map_one]
    rfl
  have h2 : cyclicMap U' Ω' (Finsupp.single (1 : G) 1) = Ω' := by
    rw [cyclicMap_single, map_one]
    rfl
  have h3 := markedMap_cyclicMap hcoef hcyc (Finsupp.single (1 : G) 1)
  rw [h1, h2] at h3
  exact h3

omit [CompleteSpace H] in
theorem markedMap_intertwine
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω'))
    (hcyc : Dense ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H))
    (g : G) (x : H) :
    markedMap hcoef (U g x) = U' g (markedMap hcoef x) := by
  set L : H →L[ℂ] H' := (markedMap hcoef).comp ((U g).toLinearIsometry.toContinuousLinearMap)
    with hL
  set R : H →L[ℂ] H' := ((U' g).toLinearIsometry.toContinuousLinearMap).comp (markedMap hcoef)
    with hR
  have hgen : Set.EqOn (L : H → H') (R : H → H') (Set.range fun h : G => U h Ω) := by
    rintro _ ⟨h, rfl⟩
    show markedMap hcoef (U g (U h Ω)) = U' g (markedMap hcoef (U h Ω))
    have e1 : U g (U h Ω) = cyclicMap U Ω (Finsupp.single (g * h) 1) := by
      rw [cyclicMap_single, monoidHom_apply_mul]
    have e2 : U h Ω = cyclicMap U Ω (Finsupp.single h 1) := (cyclicMap_single U Ω h).symm
    rw [e1, e2, markedMap_cyclicMap hcoef hcyc, markedMap_cyclicMap hcoef hcyc,
      cyclicMap_single, cyclicMap_single]
    exact monoidHom_apply_mul U' g h Ω'
  have hspan : Set.EqOn (L : H → H') (R : H → H')
      ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H) := by
    intro y hy
    rw [range_cyclicMap] at hy
    exact LinearMap.eqOn_span (f := (L : H →ₗ[ℂ] H')) (g := (R : H →ₗ[ℂ] H')) hgen hy
  have hall : (L : H → H') = (R : H → H') :=
    Continuous.ext_on hcyc L.continuous R.continuous hspan
  exact congrFun hall x

/-- **Theorem 3.1.**  Two marked cyclic unitary presentations with the same matrix coefficient are
uniquely equivalent: there is exactly one unitary carrying the first cyclic vector to the second
and intertwining the two actions. -/
theorem exists_unique_marked_intertwiner
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (U' : G →* (H' ≃ₗᵢ[ℂ] H')) (Ω : H) (Ω' : H')
    (hcyc : Dense ((Submodule.span ℂ (Set.range fun g : G => U g Ω) : Submodule ℂ H) : Set H))
    (hcyc' : Dense
      ((Submodule.span ℂ (Set.range fun g : G => U' g Ω') : Submodule ℂ H') : Set H'))
    (hcoef : ∀ g : G, (inner ℂ Ω (U g Ω) : ℂ) = inner ℂ Ω' (U' g Ω')) :
    ∃! V : H ≃ₗᵢ[ℂ] H', V Ω = Ω' ∧ ∀ (g : G) (x : H), V (U g x) = U' g (V x) := by
  have hcycR : Dense ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H) := by
    rw [range_cyclicMap]
    exact hcyc
  have hcycR' : Dense ((LinearMap.range (cyclicMap U' Ω') : Submodule ℂ H') : Set H') := by
    rw [range_cyclicMap]
    exact hcyc'
  have hcoef' : ∀ g : G, (inner ℂ Ω' (U' g Ω') : ℂ) = inner ℂ Ω (U g Ω) := fun g => (hcoef g).symm
  set V : H →L[ℂ] H' := markedMap hcoef with hV
  set W : H' →L[ℂ] H := markedMap hcoef' with hW
  -- the two extensions are mutually inverse
  have hWV : (W.comp V : H → H) = (id : H → H) := by
    refine Continuous.ext_on hcycR (W.comp V).continuous continuous_id ?_
    rintro y hy
    obtain ⟨c, rfl⟩ := hy
    show W (V (cyclicMap U Ω c)) = cyclicMap U Ω c
    rw [hV, hW, markedMap_cyclicMap hcoef hcycR, markedMap_cyclicMap hcoef' hcycR']
  have hVW : (V.comp W : H' → H') = (id : H' → H') := by
    refine Continuous.ext_on hcycR' (V.comp W).continuous continuous_id ?_
    rintro y hy
    obtain ⟨c, rfl⟩ := hy
    show V (W (cyclicMap U' Ω' c)) = cyclicMap U' Ω' c
    rw [hV, hW, markedMap_cyclicMap hcoef' hcycR', markedMap_cyclicMap hcoef hcycR]
  have hVWl : (V : H →ₗ[ℂ] H') ∘ₗ (W : H' →ₗ[ℂ] H) = LinearMap.id :=
    LinearMap.ext fun y => congrFun hVW y
  have hWVl : (W : H' →ₗ[ℂ] H) ∘ₗ (V : H →ₗ[ℂ] H') = LinearMap.id :=
    LinearMap.ext fun x => congrFun hWV x
  refine ⟨⟨LinearEquiv.ofLinear (V : H →ₗ[ℂ] H') (W : H' →ₗ[ℂ] H) hVWl hWVl,
    norm_markedMap hcoef hcycR⟩, ⟨markedMap_omega hcoef hcycR,
    markedMap_intertwine hcoef hcycR⟩, ?_⟩
  · rintro V₂ ⟨hV₂Ω, hV₂int⟩
    have hgen : Set.EqOn (V₂ : H → H')
        (fun x : H => markedMap hcoef x) (Set.range fun h : G => U h Ω) := by
      rintro _ ⟨h, rfl⟩
      show V₂ (U h Ω) = markedMap hcoef (U h Ω)
      have hL : V₂ (U h Ω) = U' h Ω' := by
        rw [hV₂int h Ω, hV₂Ω]
      have hR : markedMap hcoef (U h Ω) = U' h Ω' := by
        rw [show U h Ω = cyclicMap U Ω (Finsupp.single h 1) from (cyclicMap_single U Ω h).symm,
          markedMap_cyclicMap hcoef hcycR, cyclicMap_single]
      rw [hL, hR]
    have hspan : Set.EqOn (V₂ : H → H') (fun x : H => markedMap hcoef x)
        ((LinearMap.range (cyclicMap U Ω) : Submodule ℂ H) : Set H) := by
      intro y hy
      rw [range_cyclicMap] at hy
      exact LinearMap.eqOn_span
        (f := (V₂.toLinearEquiv.toLinearMap : H →ₗ[ℂ] H'))
        (g := ((markedMap hcoef) : H →ₗ[ℂ] H')) hgen hy
    have hall : (V₂ : H → H') = fun x : H => markedMap hcoef x :=
      Continuous.ext_on hcycR V₂.continuous (markedMap hcoef).continuous hspan
    exact LinearIsometryEquiv.ext fun x => congrFun hall x

end

end GaloisForLFunctions.HTGeometry
