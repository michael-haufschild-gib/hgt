import GaloisForLFunctions.HTGeometry.PowerSeriesSimpleRootLift
import Mathlib.FieldTheory.Separable

/-!
# Deforming a split separable polynomial in one variable

A monic polynomial over `M⟦u⟧` whose residue at `u = 0` splits with distinct roots has its own roots
in `M⟦u⟧`, canonically labelled by the residue roots, and every coefficientwise automorphism
permutes the lifts exactly as it permutes the residue roots.  This is the step that transports a
Galois permutation across one deformation variable without disturbing the labelling.

## Main results

* `eval_derivative_ne_zero_of_separable` — a separable polynomial has nonvanishing derivative at
  each of its roots.
* `exists_powerSeriesRootFamily` — the labelled family of lifts and its equivariance.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem eval_derivative_ne_zero_of_separable {M : Type*} [Field M] {p : Polynomial M}
    (hsep : p.Separable) {a : M} (hroot : p.IsRoot a) :
    Polynomial.eval a (Polynomial.derivative p) ≠ 0 := by
  intro h0
  obtain ⟨u, v, huv⟩ := hsep
  have heval := congrArg (Polynomial.eval a) huv
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_one,
    hroot, h0] at heval
  simp at heval

/-- **One-variable deformation with a labelled root family.**  If the residue of `G` at `u = 0`
splits with distinct roots `ρ`, then `G` has roots `y k ≡ ρ k` in `M⟦u⟧`, and every coefficientwise
automorphism fixing `G` permutes the `y k` exactly as it permutes the `ρ k`. -/
theorem exists_powerSeriesRootFamily
    {M : Type*} [Field M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Polynomial (PowerSeries M)) (ρ : ι → M)
    (hinj : Function.Injective ρ)
    (hres : G.map (PowerSeries.constantCoeff (R := M))
      = ∏ k, (Polynomial.X - Polynomial.C (ρ k))) :
    ∃ y : ι → PowerSeries M,
      (∀ k, G.IsRoot (y k)) ∧
      (∀ k, (PowerSeries.X : PowerSeries M) ∣ (y k - PowerSeries.C (ρ k))) ∧
      ∀ (φ : M ≃+* M) (π : Equiv.Perm ι),
        G.map (PowerSeries.map (φ : M →+* M)) = G → (∀ k, φ (ρ k) = ρ (π k)) →
        ∀ k, PowerSeries.map (φ : M →+* M) (y k) = y (π k) := by
  classical
  have hsep : (G.map (PowerSeries.constantCoeff (R := M))).Separable := by
    rw [hres]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr hinj
  have hconstC : ∀ k, PowerSeries.constantCoeff (R := M) (PowerSeries.C (ρ k)) = ρ k := by
    intro k
    simp
  have hroot : ∀ k, (G.map (PowerSeries.constantCoeff (R := M))).IsRoot (ρ k) := by
    intro k
    rw [hres]
    show Polynomial.eval (ρ k) (∏ j, (Polynomial.X - Polynomial.C (ρ j))) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hv : ∀ k, (PowerSeries.X : PowerSeries M) ∣
      Polynomial.eval (PowerSeries.C (ρ k)) G := by
    intro k
    rw [PowerSeries.X_dvd_iff]
    have hmap := Polynomial.eval_map_apply (PowerSeries.constantCoeff (R := M))
      (PowerSeries.C (ρ k)) (p := G)
    rw [hconstC k] at hmap
    rw [← hmap]
    exact hroot k
  have hdu : ∀ k, IsUnit
      (Polynomial.eval (PowerSeries.C (ρ k)) (Polynomial.derivative G)) := by
    intro k
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hmap := Polynomial.eval_map_apply (PowerSeries.constantCoeff (R := M))
      (PowerSeries.C (ρ k)) (p := Polynomial.derivative G)
    rw [hconstC k] at hmap
    rw [← hmap, ← Polynomial.derivative_map]
    exact (eval_derivative_ne_zero_of_separable hsep (hroot k)).isUnit
  choose y hy using fun k =>
    (existsUnique_isRoot_powerSeries_of_isUnit_deriv (hdu k) (hv k)).exists
  refine ⟨y, fun k => (hy k).1, fun k => (hy k).2, ?_⟩
  intro φ π hG hπ k
  have hmapC : PowerSeries.map (φ : M →+* M) (PowerSeries.C (ρ k))
      = PowerSeries.C (ρ (π k)) := by
    rw [PowerSeries.map_C]
    congr 1
    exact hπ k
  refine map_lift_eq φ hG (y₀ := PowerSeries.C (ρ k)) ?_ ?_ (hy k).1 (hy k).2 (hy (π k)).1 ?_
  · rw [hmapC]
    exact hdu (π k)
  · rw [hmapC]
    exact hv (π k)
  · rw [hmapC]
    exact (hy (π k)).2

end

end GaloisForLFunctions.HTGeometry
