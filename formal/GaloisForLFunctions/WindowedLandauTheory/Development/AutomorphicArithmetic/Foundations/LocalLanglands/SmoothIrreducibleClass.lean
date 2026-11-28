import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Defs.Basic

/-! Smooth irreducible representations and their isomorphism classes.
Smoothness is openness of each vector stabilizer. -/

noncomputable section

namespace GlobalTheory.PRep

variable (G : Type) [Group G] [TopologicalSpace G]

structure IrrRep : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : ∀ v : V, IsOpen {g : G | ρ g v = v}
  irr : ρ.IsIrreducible

attribute [instance] IrrRep.acg IrrRep.mod

instance IrrRep.setoid : Setoid (IrrRep G) where
  r σ τ := Nonempty (σ.ρ.Equiv τ.ρ)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨φ⟩ => ⟨φ.symm⟩, fun ⟨φ⟩ ⟨ψ⟩ => ⟨φ.trans ψ⟩⟩

def IrrCl : Type 1 := Quotient (IrrRep.setoid G)

variable {G}

def IrrRep.cl (σ : IrrRep G) : IrrCl G := Quotient.mk _ σ

theorem IrrRep.cl_eq_iff {σ τ : IrrRep G} : σ.cl = τ.cl ↔ Nonempty (σ.ρ.Equiv τ.ρ) := Quotient.eq

def IrrCl.rep (c : IrrCl G) : IrrRep G := Quotient.out c

@[simp] theorem IrrCl.cl_rep (c : IrrCl G) : c.rep.cl = c := Quotient.out_eq c

end GlobalTheory.PRep

#print axioms GlobalTheory.PRep.IrrCl.cl_rep
