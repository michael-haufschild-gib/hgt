import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.SmoothWeilAction
import Mathlib.Topology.Separation.Hausdorff

/-! Characters pulled back along a local Artin map are smooth on the Weil
group exactly when their kernels are open on the local multiplicative group.
The compact inertia group maps onto the open subgroup of valuation zero. -/

noncomputable section

open NumberField IsDedekindDomain Topology
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/-- A surjective homomorphism identifying inertia with the open valuation
kernel detects smoothness of every character of the target. -/
theorem isSmooth_comp_iff_of_degree {U : Type*} [Group U] [TopologicalSpace U] [T2Space U]
    [SeparatelyContinuousMul U] (a : Weil h →* U) (ha : Function.Surjective a)
    (hc : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ))
    (ord : U →* Multiplicative ℤ) (hord : IsOpen (ord.ker : Set U))
    (hdeg : ∀ σ, Multiplicative.toAdd (ord (a σ)) = -deg σ)
    (χ : U →* ℂˣ) : IsSmooth (χ.comp a) ↔ IsOpen (χ.ker : Set U) := by
  letI : CompactSpace (Ine (F := E) A) := compactSpace_Ine A
  have hker (σ : Weil h) : a σ ∈ ord.ker ↔ (σ : G E Ω) ∈ Ine (F := E) A := by
    rw [MonoidHom.mem_ker, ← deg_eq_zero_iff]
    constructor
    · intro hσ
      have h := hdeg σ
      rw [hσ] at h
      change 0 = -deg σ at h
      omega
    · intro hσ
      have h := hdeg σ
      rw [hσ, neg_zero] at h
      exact h
  let b : Ine (F := E) A → ord.ker := fun σ => ⟨a (ineIncl h σ), (hker _).mpr σ.2⟩
  have hb : Continuous b := hc.subtype_mk _
  have hbs : Function.Surjective b := by
    intro x
    obtain ⟨σ, hσ⟩ := ha x.1
    have hσI := (hker σ).mp (by rw [hσ]; exact x.2)
    refine ⟨⟨σ, hσI⟩, Subtype.ext ?_⟩
    exact hσ
  let Q : Set ord.ker := Subtype.val ⁻¹' (χ.ker : Set U)
  constructor
  · intro hs
    have hopen : IsOpen Q := (Topology.IsQuotientMap.of_surjective_continuous hbs hb).isCoinducing.isOpen_preimage.mp hs
    have hopen' : IsOpen (Subtype.val '' Q : Set U) := hord.isOpenMap_subtype_val _ hopen
    refine χ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hopen'.mem_nhds ?_) ?_)
    · exact ⟨1, by simp [Q], rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
  · intro hs
    exact hs.preimage hc

end GlobalTheory.WeilDeligne
