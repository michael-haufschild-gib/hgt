import GaloisForLFunctions.HTGeometry.ExplicitDigammaHerglotzPalette
import GaloisForLFunctions.HTGeometry.ShiftedDigammaFamilyIndependence

/-!
# Joint differential independence of the explicit digamma palette

Differential independence is a finitary condition, so it passes from all finite subfamilies to an
arbitrary index (`DifferentialIndependent.of_finite`).  Combining this with the shifted-digamma
independence theorem gives the joint statement for an arbitrary family of pairwise incongruent
shifts, and in particular for the explicit palette `α_n = 1/(n+2)`, whose points are pairwise
distinct modulo `ℤ`.

* `differentialIndependent_digammaShiftMero_general` — arbitrary index;
* `differentialIndependent_explicitDigammaPalette` — the whole countable explicit palette
  `n ↦ ψ(z + 1/(n+2))` is differentially independent over `ℂ(z)`.
-/

open Filter Set Topology Function

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

open Bottcher

local instance explicitPaletteDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance explicitPaletteDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-! ## Differential independence is finitary -/

theorem DifferentialIndependent.of_finite {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    [Differential K] {ι : Type*} (x : ι → K)
    (h : ∀ t : Set ι, t.Finite → DifferentialIndependent F fun i : t => x (i : ι)) :
    DifferentialIndependent F x := by
  rw [DifferentialIndependent]
  refine algebraicIndependent_of_finite_type ?_
  intro T hT
  have hsfin : (Prod.fst '' T).Finite := hT.image _
  have hind := h (Prod.fst '' T) hsfin
  rw [DifferentialIndependent] at hind
  have hcomp := hind.comp
    (fun p : T => ((⟨(p : ι × ℕ).1, ⟨(p : ι × ℕ), p.2, rfl⟩⟩ : (Prod.fst '' T : Set ι)),
      (p : ι × ℕ).2)) ?_
  · exact hcomp
  · intro p p' hpp
    apply Subtype.ext
    have h1 : (p : ι × ℕ).1 = (p' : ι × ℕ).1 :=
      congrArg (fun q : (Prod.fst '' T : Set ι) × ℕ => (q.1 : ι)) hpp
    have h2 : (p : ι × ℕ).2 = (p' : ι × ℕ).2 :=
      congrArg (fun q : (Prod.fst '' T : Set ι) × ℕ => q.2) hpp
    exact Prod.ext h1 h2

/-! ## Arbitrary families of pairwise incongruent shifted digammas -/

/-- **Joint shifted-digamma independence at an arbitrary index.**  Any family of digammas whose
shifts are pairwise distinct modulo `ℤ` is differentially independent over `ℂ(X)`. -/
theorem differentialIndependent_digammaShiftMero_general {ι : Type*} (lam : ι → ℂ)
    (hincong : ∀ i i' : ι, i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ)) :
    letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).toAlgebra
    DifferentialIndependent (RatFunc ℂ) fun i => digammaShiftMero (lam i) := by
  classical
  letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).toAlgebra
  letI := ratFuncCoordinateDifferential
  refine DifferentialIndependent.of_finite _ ?_
  intro t ht
  haveI : Fintype t := ht.fintype
  set e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t with he
  have hincong' : ∀ m m' : Fin (Fintype.card t), m ≠ m' → ∀ n : ℤ,
      lam (e.symm m : ι) - lam (e.symm m' : ι) ≠ (n : ℂ) := by
    intro m m' hmm n
    refine hincong _ _ (fun hc => hmm ?_) n
    have hsub : e.symm m = e.symm m' := Subtype.ext hc
    rw [← e.apply_symm_apply m, ← e.apply_symm_apply m', hsub]
  have hbase := differentialIndependent_digammaShiftMero (fun m => lam (e.symm m : ι)) hincong'
  have hcomp := hbase.comp e e.injective
  have hfun : ((fun m => digammaShiftMero (lam (e.symm m : ι))) ∘ e)
      = fun i : t => digammaShiftMero (lam (i : ι)) := by
    funext i
    simp only [Function.comp_apply, he, Equiv.symm_apply_apply]
  rwa [hfun] at hcomp

/-! ## The explicit palette -/

/-- **The explicit digamma palette is jointly differentially independent.**  The palette points
`α_n = 1/(n+2)` lie in `(0, 1/2]`, so distinct codes give shifts that differ by no integer, and the
whole countable family `n ↦ ψ(z + α_n)` is differentially independent over `ℂ(z)`. -/
theorem differentialIndependent_explicitDigammaPalette :
    letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).toAlgebra
    DifferentialIndependent (RatFunc ℂ)
      fun n : ℕ => digammaShiftMero ((explicitDigammaPalettePoint n : ℝ) : ℂ) := by
  letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).toAlgebra
  letI := ratFuncCoordinateDifferential
  refine differentialIndependent_digammaShiftMero_general
    (fun n : ℕ => ((explicitDigammaPalettePoint n : ℝ) : ℂ)) ?_
  intro m n hmn k hcon
  have hreal : explicitDigammaPalettePoint m - explicitDigammaPalettePoint n = (k : ℝ) := by
    have hcast : (((explicitDigammaPalettePoint m - explicitDigammaPalettePoint n : ℝ)) : ℂ)
        = ((k : ℝ) : ℂ) := by push_cast at hcon ⊢; linear_combination hcon
    exact_mod_cast hcast
  exact explicitDigammaPalettePoint_sub_ne_int hmn k hreal

/-- **Every finite subfamily of the explicit palette is differentially independent.**  This is the
finite form used by the orientation-chamber argument. -/
theorem differentialIndependent_explicitDigammaPalette_fin {r : ℕ} (idx : Fin r → ℕ)
    (hidx : Function.Injective idx) :
    letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).toAlgebra
    DifferentialIndependent (RatFunc ℂ)
      fun i : Fin r => digammaShiftMero ((explicitDigammaPalettePoint (idx i) : ℝ) : ℂ) := by
  letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).toAlgebra
  letI := ratFuncCoordinateDifferential
  exact differentialIndependent_explicitDigammaPalette.comp idx hidx

end

end GaloisForLFunctions.HTGeometry
