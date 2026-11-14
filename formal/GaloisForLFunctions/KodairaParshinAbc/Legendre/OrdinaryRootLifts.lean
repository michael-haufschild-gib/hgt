import GaloisForLFunctions.KodairaParshinAbc.Legendre.DeuringZeros
import GaloisForLFunctions.HTGeometry.PowerSeriesSimpleRootLift
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Hensel lifts and formal inverse branches of Deuring polynomials

The proved derivative tests supply the simple-root hypotheses in local lifting.
Deuring roots lift in the valuation rings of nonarchimedean local fields; ordinary
weight-two numerator roots have unique p-adic lifts and unique formal inverse branches.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial
open scoped ValuativeRel

attribute [local instance] Ideal.Quotient.field

/-- The weight-two operator commutes with every coefficient-ring map. -/
theorem map_legendreOperator {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X]) :
    (legendreOperator f).map φ = legendreOperator (f.map φ) := by
  simp [legendreOperator, derivative_map]

/-- Every Deuring residue root lifts to the valuation ring of a nonarchimedean local field. -/
theorem binomialSquare_localField_root_lift
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [CharP (𝒪[K] ⧸ 𝓂[K]) (2 * n + 1)]
    (a₀ : 𝒪[K] ⧸ 𝓂[K]) (hroot : (binomialSquare n : (𝒪[K] ⧸ 𝓂[K])[X]).IsRoot a₀) :
    ∃ a : 𝒪[K], (binomialSquare n : (𝒪[K])[X]).IsRoot a ∧
      Ideal.Quotient.mk 𝓂[K] a = a₀ := by
  apply HTGeometry.ABHN.nonarchimedeanLocalField_hensel_lift_residue_root K
    (binomialSquare n) (binomialSquare_monic n) a₀
  · rw [← eval_map_algebraMap, map_binomialSquare]
    exact hroot
  · rw [← eval_map_algebraMap, ← derivative_map, map_binomialSquare]
    exact binomialSquare_root_simple n a₀ hroot

private theorem ordinary_derivative_ne_zero {K : Type*} [Field K]
    (n : ℕ) [CharP K (2 * n + 1)] (hn : 2 ≤ n) (z : K)
    (hroot : (legendreOperator (binomialSquare n : K[X])).eval z = 0)
    (hL : z ^ 2 - z + 1 ≠ 0) :
    (legendreOperator (binomialSquare n : K[X])).derivative.eval z ≠ 0 :=
  ((binomialSquare_operator_multiple_zero n hn z).resolve_left
    (not_not.mpr hroot)).resolve_right hL

private theorem padic_residue_zero_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private theorem padic_residue_eq_iff {p : ℕ} [Fact p.Prime] (x y : ℤ_[p]) :
    PadicInt.toZMod x = PadicInt.toZMod y ↔ ‖x - y‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, padic_residue_zero_iff]

private theorem padic_norm_eq_one_of_residue_ne_zero {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) (hx : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x)
    (not_lt.mp fun h => hx ((padic_residue_zero_iff x).mpr h))

/-- Every ordinary numerator residue root has exactly one p-adic lift in its residue class.
The root and elliptic exceptions are retained as an unconditional pointwise alternative. -/
theorem ordinary_numerator_padic_lift (n : ℕ) [Fact (2 * n + 1).Prime]
    (hn : 2 ≤ n) (a : ZMod (2 * n + 1)) :
    (legendreOperator (binomialSquare n : (ZMod (2 * n + 1))[X])).eval a ≠ 0 ∨
      a ^ 2 - a + 1 = 0 ∨
        ∃! x : ℤ_[2 * n + 1],
          (legendreOperator (binomialSquare n : (ℤ_[2 * n + 1])[X])).IsRoot x ∧
            PadicInt.toZMod x = a := by
  by_cases hroot :
      (legendreOperator (binomialSquare n : (ZMod (2 * n + 1))[X])).eval a = 0
  · by_cases hL : a ^ 2 - a + 1 = 0
    · exact Or.inr (Or.inl hL)
    refine Or.inr (Or.inr ?_)
    have hd := ordinary_derivative_ne_zero n hn a hroot hL
    obtain ⟨a₀, ha₀⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := 2 * n + 1)) a
    let f : (ℤ_[2 * n + 1])[X] := legendreOperator (binomialSquare n)
    have hmap : f.map PadicInt.toZMod =
        legendreOperator (binomialSquare n : (ZMod (2 * n + 1))[X]) := by
      dsimp only [f]
      rw [map_legendreOperator, map_binomialSquare]
    have hv : PadicInt.toZMod (f.eval a₀) = 0 := by
      have he : PadicInt.toZMod (f.eval a₀) =
          (f.map PadicInt.toZMod).eval (PadicInt.toZMod a₀) := by
        simp only [eval_map, eval₂_at_apply]
      rw [he, hmap, ha₀]
      exact hroot
    have hder : PadicInt.toZMod (f.derivative.eval a₀) ≠ 0 := by
      have he : PadicInt.toZMod (f.derivative.eval a₀) =
          (f.derivative.map PadicInt.toZMod).eval (PadicInt.toZMod a₀) := by
        simp only [eval_map, eval₂_at_apply]
      rw [he, ← derivative_map, hmap, ha₀]
      exact hd
    have hvnorm := (padic_residue_zero_iff _).mp hv
    have hdnorm := padic_norm_eq_one_of_residue_ne_zero _ hder
    have hnorm : ‖f.eval a₀‖ < ‖f.derivative.eval a₀‖ ^ 2 := by
      rw [hdnorm, one_pow]
      exact hvnorm
    obtain ⟨x, hx, hclose, _, huniq⟩ := hensels_lemma (F := f) (a := a₀) (by simpa using hnorm)
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at hx hclose huniq
    rw [hdnorm] at hclose huniq
    refine ⟨x, ⟨hx, ((padic_residue_eq_iff x a₀).mpr hclose).trans ha₀⟩, ?_⟩
    intro y hy
    exact huniq y hy.1 ((padic_residue_eq_iff y a₀).mp (hy.2.trans ha₀.symm))
  · exact Or.inl hroot

/-- An ordinary numerator root has a unique formal inverse branch `B(y(T)) = T`. -/
theorem ordinary_numerator_formal_inverse {K : Type*} [Field K]
    (n : ℕ) [CharP K (2 * n + 1)] (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).eval z ≠ 0 ∨
      z ^ 2 - z + 1 = 0 ∨
        ∃! y : PowerSeries K,
          (legendreOperator (binomialSquare n : K[X])).eval₂ PowerSeries.C y = PowerSeries.X ∧
            PowerSeries.constantCoeff y = z := by
  by_cases hroot : (legendreOperator (binomialSquare n : K[X])).eval z = 0
  · by_cases hL : z ^ 2 - z + 1 = 0
    · exact Or.inr (Or.inl hL)
    refine Or.inr (Or.inr ?_)
    let f : K[X] := legendreOperator (binomialSquare n)
    let G : (PowerSeries K)[X] := f.map PowerSeries.C - C PowerSeries.X
    have hfroot : f.eval z = 0 := hroot
    have hd : f.derivative.eval z ≠ 0 := ordinary_derivative_ne_zero n hn z hroot hL
    have hv : G.eval (PowerSeries.C z) = -PowerSeries.X := by
      simp only [G, eval_sub, eval_map, eval₂_at_apply, eval_C, hfroot, map_zero, zero_sub]
    have hder : G.derivative.eval (PowerSeries.C z) = PowerSeries.C (f.derivative.eval z) := by
      simp only [G, derivative_sub, derivative_C, sub_zero, derivative_map,
        eval_map, eval₂_at_apply]
    have hdu : IsUnit (G.derivative.eval (PowerSeries.C z)) := by
      rw [hder, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C]
      exact isUnit_iff_ne_zero.mpr hd
    have hdiv : PowerSeries.X ∣ G.eval (PowerSeries.C z) := by
      rw [hv]
      exact dvd_neg.mpr (dvd_refl _)
    obtain ⟨y, hy, huniq⟩ :=
      HTGeometry.existsUnique_isRoot_powerSeries_of_isUnit_deriv hdu hdiv
    have hpred (v : PowerSeries K) :
        (G.IsRoot v ∧ PowerSeries.X ∣ v - PowerSeries.C z) ↔
          (f.eval₂ PowerSeries.C v = PowerSeries.X ∧ PowerSeries.constantCoeff v = z) := by
      simp only [IsRoot, G, eval_sub, eval_map, eval_C, PowerSeries.X_dvd_iff,
        map_sub, PowerSeries.constantCoeff_C, sub_eq_zero]
    exact ⟨y, (hpred y).mp hy, fun v hv => huniq v ((hpred v).mpr hv)⟩
  · exact Or.inl hroot

end GaloisForLFunctions.KodairaParshinAbc.Legendre
