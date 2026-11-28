import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothRepresentationScalarTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothIrreducibleClass

/-! Scalar character twisting descends to smooth irreducible
classes and gives an action of the smooth character group. -/

noncomputable section

namespace Representation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem scalarTwist_mul (ρ : Representation ℂ G V) (χ ψ : G →* ℂˣ) :
    (ρ.scalarTwist χ).scalarTwist ψ = ρ.scalarTwist (χ * ψ) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  simp only [scalarTwist_apply, smul_smul, MonoidHom.mul_apply, Units.val_mul, mul_comm (ψ g : ℂ) (χ g : ℂ)]

@[simp] theorem scalarTwist_one (ρ : Representation ℂ G V) : ρ.scalarTwist 1 = ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  simp

def Equiv.scalarTwist {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (χ : G →* ℂˣ) : (ρ.scalarTwist χ).Equiv (σ.scalarTwist χ) :=
  Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => by
    change e.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • σ g (e.toLinearEquiv v)
    rw [map_smul, show e.toLinearEquiv (ρ g v) = σ g (e.toLinearEquiv v) from
      Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v]

theorem isOpen_ker_mul [TopologicalSpace G] [IsTopologicalGroup G] (χ ψ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) (hψ : IsOpen (ψ.ker : Set G)) :
    IsOpen ((χ * ψ).ker : Set G) := by
  refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ ψ.ker) ?_ (hχ.inter hψ)
  intro g hg
  change χ g * ψ g = 1
  rw [MonoidHom.mem_ker.mp hg.1, MonoidHom.mem_ker.mp hg.2, mul_one]

theorem isOpen_ker_inv [TopologicalSpace G] (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsOpen (χ⁻¹.ker : Set G) := by
  have he : (χ⁻¹.ker : Set G) = χ.ker := by
    ext g
    change (χ g)⁻¹ = 1 ↔ χ g = 1
    exact inv_eq_one
  rwa [he]

end Representation

namespace GlobalTheory.PRep

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def IrrRep.twist (σ : IrrRep G) (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) : IrrRep G where
  V := σ.V
  ρ := σ.ρ.scalarTwist χ
  smooth := Representation.scalarTwist_smooth σ.ρ σ.smooth χ hχ
  irr := by
    letI := σ.irr
    exact Representation.scalarTwist_irreducible σ.ρ χ

def IrrCl.twist (x : IrrCl G) (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) : IrrCl G :=
  Quotient.lift (s := IrrRep.setoid G) (fun σ => (σ.twist χ hχ).cl)
    (fun a b hab => by
      obtain ⟨e⟩ : Nonempty (a.ρ.Equiv b.ρ) := hab
      exact IrrRep.cl_eq_iff.mpr ⟨e.scalarTwist χ⟩) x

@[simp] theorem IrrRep.cl_twist (σ : IrrRep G) (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) :
    (σ.twist χ hχ).cl = σ.cl.twist χ hχ := rfl

theorem IrrCl.twist_mul (x : IrrCl G) (χ ψ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) (hψ : IsOpen (ψ.ker : Set G))
    (hχψ : IsOpen ((χ * ψ).ker : Set G)) :
    (x.twist χ hχ).twist ψ hψ = x.twist (χ * ψ) hχψ := by
  rw [← IrrCl.cl_rep x, ← IrrRep.cl_twist, ← IrrRep.cl_twist, ← IrrRep.cl_twist]
  apply IrrRep.cl_eq_iff.mpr
  change Nonempty (((x.rep.ρ.scalarTwist χ).scalarTwist ψ).Equiv (x.rep.ρ.scalarTwist (χ * ψ)))
  rw [Representation.scalarTwist_mul]
  exact ⟨Representation.Equiv.refl _⟩

@[simp] theorem IrrCl.twist_one (x : IrrCl G) (h : IsOpen ((1 : G →* ℂˣ).ker : Set G)) :
    x.twist 1 h = x := by
  rw [← IrrCl.cl_rep x, ← IrrRep.cl_twist]
  apply IrrRep.cl_eq_iff.mpr
  change Nonempty ((x.rep.ρ.scalarTwist 1).Equiv x.rep.ρ)
  rw [Representation.scalarTwist_one]
  exact ⟨Representation.Equiv.refl _⟩

end GlobalTheory.PRep

#print axioms GlobalTheory.PRep.IrrCl.twist_mul
#print axioms GlobalTheory.PRep.IrrCl.twist_one
