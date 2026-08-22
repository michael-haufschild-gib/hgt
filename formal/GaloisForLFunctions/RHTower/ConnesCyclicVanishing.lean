import Mathlib

/-!
# §VIII (15): a relation killed by a cyclic vector is the zero operator

§VIII (15) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  "Now (15) implies that in `L²_δ(X)₀` one has `∑ λ_g U(g)(ξ_Χ) = 0`.  By the cyclicity of `ξ_Χ`
  one then gets `∑ λ_g U(g) = 0` on any `L²_{δ,Χ₀}(X)₀`, which gives a contradiction."

The mechanism is elementary and needs no analysis: an operator that commutes with the
representation and kills a cyclic vector kills a spanning set, hence vanishes.  For a *commutative*
group the finite combinations `∑_g λ_g U(g)` automatically commute with the representation, so the
step above is exactly `connes_cyclic_relation_vanishes`.
-/

open Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **§VIII (15), the mechanism.**  An operator commuting with the representation and killing a
cyclic vector is zero. -/
theorem connes_vanishing_of_cyclic {G : Type*} {U : G → (V →ₗ[ℂ] V)} {T : V →ₗ[ℂ] V} {ξ : V}
    (hcyc : Submodule.span ℂ (Set.range fun a : G => U a ξ) = ⊤)
    (hcomm : ∀ a : G, T.comp (U a) = (U a).comp T)
    (hTξ : T ξ = 0) : T = 0 := by
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ Submodule.span ℂ (Set.range fun a : G => U a ξ) := by
    rw [hcyc]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have h := congrArg (fun L : V →ₗ[ℂ] V => L ξ) (hcomm a)
      simp only [LinearMap.comp_apply] at h
      show T (U a ξ) = (0 : V →ₗ[ℂ] V) (U a ξ)
      rw [h, hTξ, map_zero, LinearMap.zero_apply]
  | zero => simp
  | add x y _ _ ihx ihy =>
      show T (x + y) = (0 : V →ₗ[ℂ] V) (x + y)
      rw [map_add, LinearMap.zero_apply]
      rw [LinearMap.zero_apply] at ihx ihy
      rw [ihx, ihy, add_zero]
  | smul c x _ ih =>
      show T (c • x) = (0 : V →ₗ[ℂ] V) (c • x)
      rw [map_smul, LinearMap.zero_apply]
      rw [LinearMap.zero_apply] at ih
      rw [ih, smul_zero]

/-- A finite combination of a commutative representation commutes with the representation. -/
theorem connes_combination_comm {G : Type*} [CommGroup G] {U : G → (V →ₗ[ℂ] V)}
    (hU : ∀ a b : G, U (a * b) = (U a).comp (U b)) (s : Finset G) (lam : G → ℂ) (a : G) :
    (∑ g ∈ s, lam g • U g).comp (U a) = (U a).comp (∑ g ∈ s, lam g • U g) := by
  refine LinearMap.ext fun v => ?_
  show (∑ g ∈ s, lam g • U g) (U a v) = U a ((∑ g ∈ s, lam g • U g) v)
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  show (lam g • U g) (U a v) = U a ((lam g • U g) v)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  congr 1
  have h3 : (U g) (U a v) = U (g * a) v := by rw [hU g a]; rfl
  have h4 : U a ((U g) v) = U (a * g) v := by rw [hU a g]; rfl
  rw [h3, h4, mul_comm]

/-- **§VIII (15).**  A finite relation of a commutative representation that annihilates a cyclic
vector is the zero operator. -/
theorem connes_cyclic_relation_vanishes {G : Type*} [CommGroup G] {U : G → (V →ₗ[ℂ] V)}
    (hU : ∀ a b : G, U (a * b) = (U a).comp (U b)) {ξ : V}
    (hcyc : Submodule.span ℂ (Set.range fun a : G => U a ξ) = ⊤)
    (s : Finset G) (lam : G → ℂ)
    (hzero : (∑ g ∈ s, lam g • U g) ξ = 0) :
    (∑ g ∈ s, lam g • U g) = 0 :=
  connes_vanishing_of_cyclic hcyc (connes_combination_comm hU s lam) hzero

end

end GaloisForLFunctions.RHTower
