import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilGroupAtFinitePlace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameInertiaLabelOfRepresentation

/-! A Weil representation is smooth when its kernel on inertia is open.
Compactness gives finite inertia image and the tame action gives a prime-field label. -/

noncomputable section

open IsLocalRing NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

/-- The kernel of the restriction to inertia is open. -/
def IsSmooth {h : IsPlaceOver A w} {M : Type*} [Monoid M] (f : Weil h →* M) : Prop :=
  IsOpen {σ : Ine (F := E) A | f (ineIncl h σ) = 1}

theorem IsSmooth.of_open {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    {U : Set (Ine (F := E) A)} (hU : IsOpen U) (h1 : 1 ∈ U)
    (hf : ∀ σ ∈ U, f (ineIncl h σ) = 1) : IsSmooth f :=
  Subgroup.isOpen_of_mem_nhds (f.comp (ineIncl h)).ker (g := 1)
    (Filter.mem_of_superset (hU.mem_nhds h1) hf)

theorem IsSmooth.of_le {h : IsPlaceOver A w} {M M' : Type*} [Monoid M] [Monoid M']
    {f : Weil h →* M} {g : Weil h →* M'} (hf : IsSmooth f) (hg : ∀ σ, f σ = 1 → g σ = 1) :
    IsSmooth g :=
  .of_open hf (by simp) fun σ hσ => hg (ineIncl h σ) hσ

theorem IsSmooth.of_le₂ {h : IsPlaceOver A w} {M M' M'' : Type*}
    [Monoid M] [Monoid M'] [Monoid M''] {f : Weil h →* M} {f' : Weil h →* M'}
    {g : Weil h →* M''} (hf : IsSmooth f) (hf' : IsSmooth f')
    (hg : ∀ σ, f σ = 1 → f' σ = 1 → g σ = 1) : IsSmooth g :=
  .of_open (hf.inter hf') (by simp) fun σ hσ => hg (ineIncl h σ) hσ.1 hσ.2

theorem IsSmooth.of_trivial {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    (hf : ∀ σ, f (ineIncl h σ) = 1) : IsSmooth f :=
  .of_open isOpen_univ trivial fun σ _ => hf σ

variable [IsAlgClosure E Ω]

/-- Smoothness makes the image of inertia finite. -/
theorem IsSmooth.finite_range {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    (hf : IsSmooth f) : (Set.range fun σ : Ine (F := E) A => f (ineIncl h σ)).Finite := by
  letI := compactSpace_Ine (E := E) A
  let g := f.comp (ineIncl h)
  letI : Finite (Ine (F := E) A ⧸ g.ker) := Subgroup.quotient_finite_of_isOpen _ hf
  let ĝ := QuotientGroup.lift g.ker g le_rfl
  refine (Set.finite_range ĝ).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨QuotientGroup.mk σ, rfl⟩

/-- The characteristic polynomial of an inertia element in a smooth tame
Weil action has a unique monic prime-field label. -/
theorem existsUnique_inertia_label {h : IsPlaceOver A w} {p N : ℕ} [Fact p.Prime]
    (hp : A.valuation (p : Ω) < 1) (hNorm : normV w = p)
    {B : ValuationSubring ℂ} {κ : ResidueField B ≃+* Fbar p} {t : Fbar p →* ℂ}
    (ht : IsTeich B κ t)
    (ρ : Weil h →* GL (Fin N) ℂ) (hρ : IsSmooth ρ)
    (hW : ∀ s : Weil h, (s : G E Ω) ∈ Ine (F := E) A →
      (∀ y : Ω, y ≠ 0 → A.valuation ((s : G E Ω) y / y - 1) < 1) → ρ s = 1)
    (τ : Ine (F := E) A) :
    ∃! f : (ZMod p)[X], f.Monic ∧
      (ρ (ineIncl h τ) : Matrix (Fin N) (Fin N) ℂ).charpoly =
        ((rootsBar f).map fun x => X - C (t x)).prod := by
  obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp hρ
  have hK (s : Weil h) (hs : (s : G E Ω) ∈ Ine (F := E) A) :
      (s : G E Ω) ∈ U ↔ ρ s = 1 := by
    have he := Set.ext_iff.mp hpre (⟨s, hs⟩ : Ine (F := E) A)
    change (s : G E Ω) ∈ U ↔ ρ (ineIncl h ⟨s, hs⟩) = 1 at he
    rw [show ineIncl h ⟨s, hs⟩ = s from Subtype.ext rfl] at he
    exact he
  have hF : IsFrob A p (frob h : G E Ω) := by
    rw [← hNorm]
    exact isFrob_frob
  exact GlobalTheory.TameKummer.existsUnique_label_of_smooth_tame_inertia A hp ht
    (Weil h) (Ine_le_Weil h) ρ hU hK hW (ineIncl h τ) (frob h) τ.2 hF

end GlobalTheory.WeilDeligne
