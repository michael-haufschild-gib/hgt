import GaloisForLFunctions.AdelicKreinGeometry.TheStableGluingFormula
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The glue absorbs exactly its own pair

In the variable of the zeros, the pair `u^{s'/2} + u^{−s'/2}` (`stablePair s'`) is a real zero pair at
`ρ = (1 ± s')/2`. Glued at exponent `s` through the boost `u^{−s/2}`, it is absorbed iff `s' = s`.

* **One square for every exponent** (`negIndex_stablePair_of_pos`): `κ(u^{s'/2} + u^{−s'/2}) = 1` for
  `s' > 0`, a single hyperbolic feature pair.
* **The form** (`hermQuad_gram_stablePair`): at slopes `u_i`, `2 Re(ĀB)` with `A = Σ w_i u_i^{−s'/2}`,
  `B = Σ w_i u_i^{s'/2}`.
* **No absorption off the boost exponent** (`boostPolarIndexAt_stablePair_of_ne`): for `s ≠ s'` the
  functionals `ℓ_s`, `A`, `B` at the slopes `1, 4, 16` are the rows of a Vandermonde matrix in the
  distinct nodes `4^{−s/2}, 4^{−s'/2}, 4^{s'/2}`, so some weight vector has `ℓ_s = 0`, `A = 1`, `B = −1`
  and form `−2`: `κ^{(s/2)} = 1`.
* **Exact absorption** (`negIndex_archGlueAt_stablePair_eq`, `negIndex_archGlue_stablePair_of_ne`):
  `κ(stablePair s' glued at s) = 1` if `s' = s` and `2` otherwise; at the Hecke exponent `s = 1` only
  the pole pair `{0, 1}` is absorbed.

So a drop of the stable index is not forced by a zero beyond the strip: a real zero pair farther from
the line than `(1 ± s)/2` costs its square like any other datum. The glue at exponent `s` detects one
exponent, its own.
-/

open Complex Finset
open scoped ComplexConjugate Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {s s' : ℝ}

theorem val_inv_mul_posUnits' (u v : posUnits) :
    ((((u⁻¹ * v : posUnits) : ℚˣ) : ℚ) : ℝ) = ((((u : ℚˣ) : ℚ) : ℝ))⁻¹ * (((v : ℚˣ) : ℚ) : ℝ) := by
  simp [Units.val_mul, Units.val_inv_eq_inv_val]

/-- The pair `u^{s'/2} + u^{−s'/2}` is a single hyperbolic feature pair, so it has at most one
square. -/
theorem negIndex_stablePair_le_one (s' : ℝ) : negIndex (stablePair s') ≤ 1 := by
  have h := negIndex_le_of_hyperbolic_features (k := stablePair s') (m := 1)
    (fun _ u => (((((u : ℚˣ) : ℚ) : ℝ) ^ (-(s' / 2)) : ℝ) : ℂ))
    (fun _ u => (((((u : ℚˣ) : ℚ) : ℝ) ^ (s' / 2) : ℝ) : ℂ)) fun a b => by
      have ha := posUnits_val_pos a
      have hb := posUnits_val_pos b
      simp only [Fin.sum_univ_one, Complex.conj_ofReal, stablePair, val_inv_mul_posUnits',
        Real.mul_rpow (inv_nonneg.mpr ha.le) hb.le, Real.inv_rpow ha.le, Real.rpow_neg ha.le,
        Real.rpow_neg hb.le]
      push_cast
      field_simp
      ring
  exact_mod_cast h

/-- **The pair has one square at every exponent.** -/
theorem negIndex_stablePair_of_pos (hs' : 0 < s') : negIndex (stablePair s') = 1 := by
  refine le_antisymm (negIndex_stablePair_le_one s') ?_
  set t : ℝ := (((posFour : ℚˣ) : ℚ) : ℝ) ^ (s' / 2)
  have ht : 1 < t := Real.one_lt_rpow (by norm_num [posFour]) (by linarith)
  have h1 : stablePair s' 1 = ((2 : ℝ) : ℂ) := by rw [stablePair]; norm_num
  have h4 : stablePair s' posFour = ((t + t⁻¹ : ℝ) : ℂ) := rfl
  have hneg : hermQuad (gram (stablePair s') ![1, posFour]) ![1, -1] < 0 := by
    rw [hermQuad_gram]
    simp [Fin.sum_univ_two, stablePair_inv, h1, h4]
    have ht0 : 0 < t := by linarith
    have : 2 < t + t⁻¹ := by
      rw [← sub_pos]
      have : t + t⁻¹ - 2 = (t - 1) ^ 2 / t := by field_simp; ring
      rw [this]; exact div_pos (by nlinarith) ht0
    linarith
  have h1' := one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg
  exact le_trans (by exact_mod_cast h1'.trans (negIndexOn_le_hermNegIndex _ ⊤))
    (hermNegIndex_gram_le_negIndex (stablePair s') _)

/-- **The form of the pair**: `2 Re(ĀB)`, `A = Σ w_i u_i^{−s'/2}`, `B = Σ w_i u_i^{s'/2}`. -/
theorem hermQuad_gram_stablePair {n : ℕ} (u : Fin n → posUnits) (w : Fin n → ℂ) :
    hermQuad (gram (stablePair s') u) w =
      (conj (boostMassAt s' u w) * ∑ a, w a * (((((u a : ℚˣ) : ℚ) : ℝ) ^ (s' / 2) : ℝ) : ℂ) +
        conj (∑ a, w a * (((((u a : ℚˣ) : ℚ) : ℝ) ^ (s' / 2) : ℝ) : ℂ)) *
          boostMassAt s' u w).re := by
  set D : Fin n → AffineGroupQ := fun a => dilation (u a : ℚˣ)
  have hD : (fun a => slopeAbs (D a)) = u := funext fun a => slopeAbs_dilation (u a)
  have e : gram (stablePair s') u = gram (fun x => ((slopePow Rat.AbsoluteValue.real s' x +
      (slopePow Rat.AbsoluteValue.real s' x)⁻¹ : ℝ) : ℂ)) D := by
    rw [← hD, ← gram_comp_slopeAbs]
    simp only [stablePair, slopePow_real_eq_at]
  have hmass : ∑ a, boostWeights Rat.AbsoluteValue.real s' D w a = boostMassAt s' u w := by
    rw [sum_boostWeights_eq_at, hD]
  have hpow : ∀ a, slopePow Rat.AbsoluteValue.real s' (D a) =
      ((((u a : ℚˣ) : ℚ) : ℝ)) ^ (s' / 2) := fun a => by
    rw [slopePow_real_eq_at, slopeAbs_dilation]
  rw [e, hermQuad_gram_boostPair, hmass]
  simp only [hpow]

/-- `(4^k)^p = (4^p)^k`. -/
theorem posFour_pow_rpow (k : ℕ) (p : ℝ) :
    ((((posFour ^ k : posUnits) : ℚˣ) : ℚ) : ℝ) ^ p = ((4 : ℝ) ^ p) ^ k := by
  have h : ((((posFour ^ k : posUnits) : ℚˣ) : ℚ) : ℝ) = (4 : ℝ) ^ k := by
    simp [posFour]
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

/-- **No absorption off the boost exponent**: for `s ≠ s'` the pair keeps its square on `ℓ_s = 0`. -/
theorem one_le_boostPolarIndexAt_stablePair (hs : 0 < s) (hs' : 0 < s') (hne : s ≠ s') :
    1 ≤ boostPolarIndexAt s (stablePair s') := by
  set α : ℝ := (4 : ℝ) ^ (-(s / 2))
  set β : ℝ := (4 : ℝ) ^ (-(s' / 2))
  set γ : ℝ := (4 : ℝ) ^ (s' / 2)
  have hα1 : α < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hβ1 : β < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hγ1 : 1 < γ := Real.one_lt_rpow (by norm_num) (by linarith)
  have hαβ : α ≠ β := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 4) (by linarith)).ne'
    · exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 4) (by linarith)).ne
  set v : Fin 3 → ℂ := ![(α : ℂ), (β : ℂ), (γ : ℂ)]
  have hinj : Function.Injective v := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [v, Complex.ofReal_inj] at h ⊢
    all_goals first
      | exact hαβ h | exact hαβ h.symm | linarith
  set M : Matrix (Fin 3) (Fin 3) ℂ := Matrix.vandermonde v
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  set w : Fin 3 → ℂ := M⁻¹ *ᵥ ![0, 1, -1]
  have hMw : M *ᵥ w = ![0, 1, -1] := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hrow : ∀ i, ∑ k, w k * (v i) ^ (k : ℕ) = (M *ᵥ w) i := fun i => by
    simp only [Matrix.mulVec, dotProduct, M, Matrix.vandermonde_apply]
    exact sum_congr rfl fun k _ => mul_comm _ _
  set u : Fin 3 → posUnits := fun k => posFour ^ (k : ℕ)
  have hℓ : boostMassAt s u w = 0 := by
    have := hrow 0
    rw [hMw] at this
    simp only [boostMassAt, LinearMap.coe_mk, AddHom.coe_mk, u, posFour_pow_rpow,
      Complex.ofReal_pow]
    simpa [v] using this
  have hA : boostMassAt s' u w = 1 := by
    have := hrow 1
    rw [hMw] at this
    simp only [boostMassAt, LinearMap.coe_mk, AddHom.coe_mk, u, posFour_pow_rpow,
      Complex.ofReal_pow]
    simpa [v] using this
  have hB : ∑ a, w a * (((((u a : ℚˣ) : ℚ) : ℝ) ^ (s' / 2) : ℝ) : ℂ) = -1 := by
    have := hrow 2
    rw [hMw] at this
    simp only [u, posFour_pow_rpow, Complex.ofReal_pow]
    simpa [v] using this
  have hneg : hermQuad (gram (stablePair s') u) w < 0 := by
    rw [hermQuad_gram_stablePair, hA, hB]
    norm_num
  exact le_trans (by exact_mod_cast one_le_negIndexOn hℓ hneg)
    (negIndexOn_le_boostPolarIndexAt (stablePair s') u)

theorem boostPolarIndexAt_stablePair_of_ne (hs : 0 < s) (hs' : 0 < s') (hne : s ≠ s') :
    boostPolarIndexAt s (stablePair s') = 1 :=
  le_antisymm ((boostPolarIndexAt_le_negIndex _).trans (negIndex_stablePair_le_one s'))
    (one_le_boostPolarIndexAt_stablePair hs hs' hne)

/-- **The stable glue absorbs exactly its own pair**: glued at exponent `s`, the pair at
`(1 ± s')/2` has one square if `s' = s` and two otherwise. -/
theorem negIndex_archGlueAt_stablePair_eq (hs0 : 0 < s) (hs1 : s < 1) (hs' : 0 < s') {c : ℝ}
    (hc : 0 < c) : negIndex (archGlueAt s (stablePair s') c) = if s' = s then 1 else 2 := by
  split_ifs with h
  · subst h
    rw [archGlueAt_stablePair, negIndex_poleSuccessor_negPowRat hs0 hs1 hc.le]
  · rw [negIndex_archGlueAt_eq hs0 hs1 isHermKernel_stablePair hc,
      boostPolarIndexAt_stablePair_of_ne hs0 hs' (Ne.symm h)]
    rfl

theorem boostPolarIndex_eq_boostPolarIndexAt_one (K : posUnits → ℂ) :
    boostPolarIndex K = boostPolarIndexAt 1 K := rfl

/-- **At the Hecke exponent only the pole pair is absorbed**: every other pair `u^{±s'/2}` glued at
`∞` has two squares. -/
theorem negIndex_archGlue_stablePair_of_ne (hs' : 0 < s') (hne : s' ≠ 1) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (stablePair s') c) = 2 := by
  rw [negIndex_archGlue_eq isHermKernel_stablePair hc, boostPolarIndex_eq_boostPolarIndexAt_one,
    boostPolarIndexAt_stablePair_of_ne one_pos hs' (Ne.symm hne)]
  rfl

end GaloisForLFunctions.AdelicKreinGeometry
