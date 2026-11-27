import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.SmoothWeilAction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaSubgroup
import Mathlib.LinearAlgebra.Semisimple

/-! The wild inertia invariants of a Weil–Deligne representation form its
tame part. Both the Weil operators and monodromy restrict to this subspace. -/

noncomputable section

open IsLocalRing NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes
open GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

/-- A Frobenius-semisimple Weil action with nilpotent monodromy and the
Weil–Deligne commutation relation. -/
structure WDRep (h : IsPlaceOver A w) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] where
  ρ : Representation ℂ (Weil h) V
  N : End ℂ V
  smooth : IsSmooth ρ
  semisimple : ∀ σ, End.IsSemisimple (ρ σ)
  nilpotent : IsNilpotent N
  comm : ∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)

namespace WDRep

variable {h : IsPlaceOver A w} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [IsAlgClosure E Ω] in
theorem comm_apply (a : WDRep h V) (σ : Weil h) (v : V) :
    a.ρ σ (a.N v) = ((normV w : ℕ) : ℂ) ^ deg σ • a.N (a.ρ σ v) :=
  LinearMap.congr_fun (a.comm σ) v

def tameSpace (a : WDRep h V) : Submodule ℂ V := wildInvariants A a.ρ

omit [IsAlgClosure E Ω] in
theorem mem_tameSpace (a : WDRep h V) {v : V} :
    v ∈ a.tameSpace ↔ ∀ σ : Weil h, (σ : G E Ω) ∈ wildInertia A → a.ρ σ v = v :=
  mem_wildInvariants A a.ρ v

omit [IsAlgClosure E Ω] in
theorem ρ_mem_tameSpace (a : WDRep h V) (σ : Weil h) :
    ∀ v ∈ a.tameSpace, a.ρ σ v ∈ a.tameSpace :=
  fun _ hv => map_mem_wildInvariants A (Weil_le_Dec h) a.ρ σ hv

theorem N_mem_tameSpace (a : WDRep h V) : ∀ v ∈ a.tameSpace, a.N v ∈ a.tameSpace := by
  intro v hv
  rw [mem_tameSpace] at hv ⊢
  intro u hu
  rw [a.comm_apply, deg_eq_zero_iff.mpr (wildInertia_le_inertia A hu), hv u hu, zpow_zero, one_smul]

/-- Restrict the Weil action and monodromy to the wild inertia invariants. -/
def tamePart (a : WDRep h V) : WDRep h a.tameSpace where
  ρ := { toFun := fun σ => (a.ρ σ).restrict (a.ρ_mem_tameSpace σ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => by ext; simp }
  N := a.N.restrict a.N_mem_tameSpace
  smooth := a.smooth.of_le fun σ hσ => by ext; simp [hσ]
  semisimple σ := End.IsSemisimple.restrict (a.ρ_mem_tameSpace σ) (a.semisimple σ)
  nilpotent := End.isNilpotent.restrict a.N_mem_tameSpace a.nilpotent
  comm σ := LinearMap.ext fun v => Subtype.ext (a.comm_apply σ v)

def Tame (a : WDRep h V) : Prop := ∀ σ : Weil h, (σ : G E Ω) ∈ wildInertia A → a.ρ σ = 1

theorem tame_tamePart (a : WDRep h V) : a.tamePart.Tame := fun σ hσ =>
  LinearMap.ext fun v => Subtype.ext (a.mem_tameSpace.mp v.2 σ hσ)

omit [IsAlgClosure E Ω] in
theorem tame_of_finrank_tameSpace (a : WDRep h V) (hd : finrank ℂ a.tameSpace = finrank ℂ V) :
    a.Tame := fun σ hs => LinearMap.ext fun v =>
  wild_apply_eq_of_finrank_invariants A a.ρ hd σ hs v

private theorem existsUnique_label_of_tame (a : WDRep h V) (ha : a.Tame)
    {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1) (hNorm : normV w = p)
    {B : ValuationSubring ℂ} {κ : ResidueField B ≃+* Fbar p} {t : Fbar p →* ℂ}
    (ht : IsTeich B κ t) (τ : Ine (F := E) A) :
    ∃! f : (ZMod p)[X], f.Monic ∧ (a.ρ (ineIncl h τ)).charpoly =
      ((rootsBar f).map fun x => X - C (t x)).prod := by
  let b := finBasis ℂ V
  let T := (LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom
  let ρ : Weil h →* GL (Fin (finrank ℂ V)) ℂ := (Units.map T).comp a.ρ.toHomUnits
  have hρ (σ : Weil h) : (ρ σ : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ) =
      LinearMap.toMatrix b b (a.ρ σ) := rfl
  have hone (σ : Weil h) (hσ : a.ρ σ = 1) : ρ σ = 1 := by
    apply Units.ext
    change T (a.ρ σ) = 1
    rw [hσ, map_one]
  have h := existsUnique_inertia_label hp hNorm ht ρ (a.smooth.of_le hone)
    (fun σ _ hσ => hone σ (ha σ hσ)) τ
  simpa only [hρ, LinearMap.charpoly_toMatrix] using h

/-- The inertia polynomial of the tame part has a unique prime-field label
at a place whose residue cardinality is prime. -/
theorem existsUnique_tame_label (a : WDRep h V) {p : ℕ} [Fact p.Prime]
    (hp : A.valuation (p : Ω) < 1) (hNorm : normV w = p)
    {B : ValuationSubring ℂ} {κ : ResidueField B ≃+* Fbar p} {t : Fbar p →* ℂ}
    (ht : IsTeich B κ t) (τ : Ine (F := E) A) :
    ∃! f : (ZMod p)[X], f.Monic ∧ (a.tamePart.ρ (ineIncl h τ)).charpoly =
      ((rootsBar f).map fun x => X - C (t x)).prod :=
  a.tamePart.existsUnique_label_of_tame a.tame_tamePart hp hNorm ht τ

end WDRep
end GlobalTheory.WeilDeligne
