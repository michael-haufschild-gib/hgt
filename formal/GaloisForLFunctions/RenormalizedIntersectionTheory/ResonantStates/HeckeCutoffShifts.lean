import GaloisForLFunctions.RHTower.EisensteinHeckeSecondMoment
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CutoffGramKernel

/-!
# Hecke operators are two shifts on the resonant cutoff family

At a resonance the constant term has one Weyl power. The two branches of `T_p`
therefore change its cutoff to `pY` and `Y/p`. Multiplication by `Y^u` absorbs
the coefficients, giving the sum of two translations in logarithmic height.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The exact Hecke action on the entire cutoff family of a resonant state. -/
theorem hecke_cutoff_shifts {p : ℕ} (hp : p.Prime) {u : ℂ} (hAu : msA u = 0)
    (Y : ℝ) (z : ℍ) :
    heckeTruncated p u Y z =
      (p : ℂ) ^ u * truncatedLineModel u (Y * p) z +
        (p : ℂ) ^ (-u) * truncatedLineModel u (Y / p) z := by
  have hupper := weyl_scalar_identity hp.pos u false
  rw [weylExponent_false, sqrt_inv_mul_cpow_half_sub hp.pos] at hupper
  have hupper' : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) *
      ((p : ℂ) ^ ((1 : ℂ) / 2 - u))⁻¹ = (p : ℂ) ^ u := by
    linear_combination hupper
  rw [heckeTruncated_eq hp]
  unfold heckeRemainder weylRemainderTerm truncatedLineModel
  simp only [constantCoefficient_false, constantCoefficient_true, hAu, weylExponent_false,
    sqrt_inv_mul_cpow_half_sub hp.pos, hupper', cuspConstantPart_eq_msAB,
    zero_mul, add_zero]
  split_ifs <;> ring

/-- Complex normalization makes each Hecke action a coefficient-free pair of height shifts. -/
theorem normalized_hecke_cutoff_shifts {p : ℕ} (hp : p.Prime) {u : ℂ}
    (hAu : msA u = 0) {Y : ℝ} (hY : 0 < Y) (z : ℍ) :
    (Y : ℂ) ^ u * heckeTruncated p u Y z =
      ((Y * p : ℝ) : ℂ) ^ u * truncatedLineModel u (Y * p) z +
        ((Y / p : ℝ) : ℂ) ^ u * truncatedLineModel u (Y / p) z := by
  rw [hecke_cutoff_shifts hp hAu]
  have hm := natCast_mul_ofReal_cpow p hY.le u
  have hd := ofReal_div_natCast_cpow_eisensteinHeckeMaassSelberg p hY.le u
  push_cast
  rw [mul_comm (Y : ℂ) (p : ℂ), hm, hd, Complex.cpow_neg]
  ring

/-- The elementary model of one Hecke transform. All primes use the same height axis. -/
def heckeCuspCutoff (p : ℕ) (u : ℂ) (Y y : ℝ) : ℂ :=
  (p : ℂ) ^ u * cuspCutoff u (Y * p) y +
    (p : ℂ) ^ (-u) * cuspCutoff u (Y / p) y

/-- Simultaneous Hecke transforms at arbitrary primes preserve the same cusp-model
norm, including every cross term between primes, states and cutoff heights. -/
theorem hecke_finite_combination_isometry {ι : Type*} (S : Finset ι)
    (p : ι → ℕ) (u : ι → ℂ) (Y : ι → ℝ) (c : ι → ℂ)
    (hp : ∀ i ∈ S, (p i).Prime)
    (hu : ∀ i ∈ S, u i ∈ eisensteinLineDomain)
    (hur : ∀ i ∈ S, (u i).re < 0) (hAu : ∀ i ∈ S, msA (u i) = 0)
    (hY : ∀ i ∈ S, (p i : ℝ) ≤ Y i) :
    (∫ z in fd, ‖∑ i ∈ S, c i * heckeTruncated (p i) (u i) (Y i) z‖ ^ 2) =
      ∫ y, ‖∑ i ∈ S, c i * heckeCuspCutoff (p i) (u i) (Y i) y‖ ^ 2 := by
  let I := S ×ˢ (Finset.univ : Finset Bool)
  let U : ι × Bool → ℂ := fun j => u j.1
  let H : ι × Bool → ℝ := fun j =>
    if j.2 then Y j.1 * p j.1 else Y j.1 / p j.1
  let C : ι × Bool → ℂ := fun j =>
    c j.1 * if j.2 then (p j.1 : ℂ) ^ u j.1 else (p j.1 : ℂ) ^ (-u j.1)
  have hmem {j : ι × Bool} (hj : j ∈ I) : j.1 ∈ S :=
    (Finset.mem_product.mp hj).1
  have hH : ∀ j ∈ I, 1 ≤ H j := by
    intro j hj
    have hp0 : (0 : ℝ) < p j.1 := by exact_mod_cast (hp j.1 (hmem hj)).pos
    have hp1 : (1 : ℝ) ≤ p j.1 := by exact_mod_cast (hp j.1 (hmem hj)).pos
    have hYi := hY j.1 (hmem hj)
    dsimp [H]
    split
    · nlinarith
    · exact (le_div_iff₀ hp0).mpr (by simpa using hYi)
  have h := resonant_finite_combination_isometry I U H C
    (fun j hj => hu j.1 (hmem hj)) (fun j hj => hur j.1 (hmem hj))
    (fun j hj => hAu j.1 (hmem hj)) hH
  have ha (z : ℍ) :
      (∑ i ∈ S, c i * heckeTruncated (p i) (u i) (Y i) z) =
        ∑ j ∈ I, C j * truncatedLineModel (U j) (H j) z := by
    simp only [I, Finset.sum_product, Fintype.sum_bool, C, U, H,
      Bool.false_eq_true, if_true, if_false]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hecke_cutoff_shifts (hp i hi) (hAu i hi)]
    ring
  have hb (y : ℝ) :
      (∑ i ∈ S, c i * heckeCuspCutoff (p i) (u i) (Y i) y) =
        ∑ j ∈ I, C j * cuspCutoff (U j) (H j) y := by
    simp only [I, Finset.sum_product, Fintype.sum_bool, C, U, H,
      Bool.false_eq_true, if_true, if_false]
    apply Finset.sum_congr rfl
    intro i hi
    unfold heckeCuspCutoff
    ring
  simp_rw [ha, hb]
  exact h

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
