import GaloisForLFunctions.HTGeometry.RittKoenigsCocycle
import GaloisForLFunctions.HTGeometry.RittFirstOrderForm
import GaloisForLFunctions.HTGeometry.RittDifferentialAlgebraicBridge

/-!
# The Ritt frame of a linearizer, and the order-one implication

Substitution by the map on germs at a fixed point, together with the derivation and the chain-rule
factor `R′`, is a Ritt frame over the rational function field.  The Koenigs equation
`S κ = λ κ` is the linearizing equation of that frame with the derivation-constant multiplier `λ`.

So if the linearizer satisfies an algebraic differential equation of order one — that is, if `κ` and
`d κ` are algebraically dependent over `ℂ(t)` — the frame produces Ritt's first-order relation
`(d κ)^r = A · κ^j`, which is a rational cocycle for the map.  An interior tree channel has none, so
its linearizer satisfies no algebraic differential equation of order one.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

noncomputable section

variable {L : Type*} [Field L] [Algebra ℂ L] [Algebra (RatFunc ℂ) L]
  [IsScalarTower ℂ (RatFunc ℂ) L]

/-- **The Ritt frame of substitution by a rational map.** -/
def koenigsRittFrame (d : Derivation ℂ L L) (S : L →ₐ[ℂ] L)
    {R : RatFunc ℂ} (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) (hRd : ratFuncDeriv R ≠ 0)
    (hcomp : ∀ Q : RatFunc ℂ, S (algebraMap (RatFunc ℂ) L Q)
      = algebraMap (RatFunc ℂ) L (ratFuncSubstitutionAlgHom R hR Q))
    (hfixed : ∀ y : L, S y = y → ∃ a : RatFunc ℂ, algebraMap (RatFunc ℂ) L a = y)
    (hdbase : ∀ a : RatFunc ℂ, d (algebraMap (RatFunc ℂ) L a)
      = algebraMap (RatFunc ℂ) L (ratFuncDeriv a))
    (hchain : ∀ x : L, d (S x)
      = algebraMap (RatFunc ℂ) L (ratFuncDeriv R) * S (d x)) :
    RittFrame (RatFunc ℂ) L where
  σ := S.toRingHom
  ψ := (ratFuncSubstitutionAlgHom R hR).toRingHom
  d := fun x => d x
  dK := ratFuncDeriv
  ρ := ratFuncDeriv R
  comp := hcomp
  fixed := hfixed
  d_add := fun x y => map_add d x y
  d_mul := fun x y => by
    have h := d.leibniz x y
    simp only [smul_eq_mul] at h
    rw [h]
    ring
  d_base := hdbase
  ρ_ne := hRd
  chain := hchain

/-- **The linearizer of an interior tree channel satisfies no order-one algebraic differential
equation.** -/
theorem no_order_one_dependence_koenigs_treeRG_interior {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    (d : Derivation ℂ L L) (S : L →ₐ[ℂ] L)
    {hR : ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c}
    (hRd : ratFuncDeriv (treeRG p (u : ℂ) (v : ℂ)) ≠ 0)
    (hcomp : ∀ Q : RatFunc ℂ, S (algebraMap (RatFunc ℂ) L Q)
      = algebraMap (RatFunc ℂ) L
        (ratFuncSubstitutionAlgHom (treeRG p (u : ℂ) (v : ℂ)) hR Q))
    (hfixed : ∀ y : L, S y = y → ∃ a : RatFunc ℂ, algebraMap (RatFunc ℂ) L a = y)
    (hdbase : ∀ a : RatFunc ℂ, d (algebraMap (RatFunc ℂ) L a)
      = algebraMap (RatFunc ℂ) L (ratFuncDeriv a))
    (hchain : ∀ x : L, d (S x)
      = algebraMap (RatFunc ℂ) L (ratFuncDeriv (treeRG p (u : ℂ) (v : ℂ))) * S (d x))
    {kap : L} {lam : ℂ} (hlam : lam ≠ 0) (hkap : kap ≠ 0) (hdkap : d kap ≠ 0)
    (hSkap : S kap = algebraMap ℂ L lam * kap)
    (hdep : ¬ AlgebraicIndependent (RatFunc ℂ) ![kap, d kap]) : False := by
  set Fr := koenigsRittFrame d S hR hRd hcomp hfixed hdbase hchain with hFr
  have hlamR : (RatFunc.C lam : RatFunc ℂ) ≠ 0 := by simpa using hlam
  have hlamalg : algebraMap (RatFunc ℂ) L (RatFunc.C lam) = algebraMap ℂ L lam := by
    rw [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]
  have hqconst : Fr.dK (RatFunc.C lam) = 0 := ratFuncDeriv_C lam
  have hshift : Fr.σ kap = algebraMap (RatFunc ℂ) L (RatFunc.C lam) * kap := by
    rw [hlamalg]
    exact hSkap
  obtain ⟨r, j, A, hr, hA, hrel⟩ :=
    exists_rittForm_of_not_algebraicIndependent Fr hkap hlamR hdkap hqconst hshift hdep
  have hιinj : Function.Injective (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) L) :=
    (algebraMap (RatFunc ℂ) L).injective
  exact no_koenigs_relation_treeRG_interior hp hv huv hu d S
    (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) L) hιinj hcomp hchain hlam hkap hSkap hA hr hrel

/-- **A differentially algebraic linearizer of an interior tree channel collapses its jet tower.**
Ritt's first-order branch is refuted by the fibre count, so only the tower branch survives. -/
theorem jet_collapse_of_DA_koenigs_treeRG_interior {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    [Differential (RatFunc ℂ)] [Differential L] [DifferentialAlgebra (RatFunc ℂ) L] [CharZero L]
    (d : Derivation ℂ L L) (S : L →ₐ[ℂ] L)
    {hR : ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c}
    (hRd : ratFuncDeriv (treeRG p (u : ℂ) (v : ℂ)) ≠ 0)
    (hcomp : ∀ Q : RatFunc ℂ, S (algebraMap (RatFunc ℂ) L Q)
      = algebraMap (RatFunc ℂ) L
        (ratFuncSubstitutionAlgHom (treeRG p (u : ℂ) (v : ℂ)) hR Q))
    (hfixed : ∀ y : L, S y = y → ∃ a : RatFunc ℂ, algebraMap (RatFunc ℂ) L a = y)
    (hdbase : ∀ a : RatFunc ℂ, d (algebraMap (RatFunc ℂ) L a)
      = algebraMap (RatFunc ℂ) L (ratFuncDeriv a))
    (hchain : ∀ x : L, d (S x)
      = algebraMap (RatFunc ℂ) L (ratFuncDeriv (treeRG p (u : ℂ) (v : ℂ))) * S (d x))
    (hd : (koenigsRittFrame d S hR hRd hcomp hfixed hdbase hchain).d
      = ⇑(Differential.deriv : Derivation ℤ L L))
    {kap : L} {lam : ℂ} (hlam : lam ≠ 0) (hkap : kap ≠ 0) (hdkap : d kap ≠ 0)
    (hSkap : S kap = algebraMap ℂ L lam * kap)
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ) kap) :
    ∃ n : ℕ, 2 ≤ n ∧ (koenigsRittFrame d S hR hRd hcomp hfixed hdbase hchain).d^[n] kap
      ∈ (koenigsRittFrame d S hR hRd hcomp hfixed hdbase hchain).jetPrefixField kap n := by
  set Fr := koenigsRittFrame d S hR hRd hcomp hfixed hdbase hchain with hFr
  have hlamR : (RatFunc.C lam : RatFunc ℂ) ≠ 0 := by simpa using hlam
  have hlamalg : algebraMap (RatFunc ℂ) L (RatFunc.C lam) = algebraMap ℂ L lam := by
    rw [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]
  have hqconst : Fr.dK (RatFunc.C lam) = 0 := ratFuncDeriv_C lam
  have hshift : Fr.σ kap = algebraMap (RatFunc ℂ) L (RatFunc.C lam) * kap := by
    rw [hlamalg]
    exact hSkap
  have hdkap' : Fr.d kap ≠ 0 := hdkap
  rcases rittForm_or_jet_mem_jetPrefixField Fr hd hkap hdkap' hlamR hqconst hshift hDA with
    ⟨r, j, A, hr, hA, hrel⟩ | hcol
  · exact absurd hrel (by
      intro hrel'
      have hιinj : Function.Injective (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) L) :=
        (algebraMap (RatFunc ℂ) L).injective
      exact no_koenigs_relation_treeRG_interior hp hv huv hu d S
        (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) L) hιinj hcomp hchain hlam hkap hSkap hA hr hrel')
  · exact hcol

end

end GaloisForLFunctions.HTGeometry
