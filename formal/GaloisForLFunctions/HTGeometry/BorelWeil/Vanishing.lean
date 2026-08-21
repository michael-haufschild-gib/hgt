/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.Sections
import GaloisForLFunctions.HTGeometry.BorelWeil.RootSL2
import GaloisForLFunctions.HTGeometry.BorelWeil.PolynomialCurve
import GaloisForLFunctions.HTGeometry.BorelWeil.PolynomialInversion

/-!
# Borel–Weil vanishing for non-dominant weights

If a weight `lam` fails to be dominant, i.e. `lam i < lam j` for some `i < j`, then the space of
sections `bwSections lam` is zero.

The proof is the rank-one (root `SL₂`) argument.  Restricting a section `f` to the two polynomial
curves `s ↦ g · rootL s` and `t ↦ g · rootU (-t) · rootWinv` produces polynomials `q` and `r`, and
the Bruhat identity `rootU (-t) · rootWinv · rootBeta t = rootL (-t⁻¹)` together with the
`B`-equivariance of `f` forces `q(-t⁻¹) = t^{lam j - lam i} r(t)` for `t ≠ 0`.  Since
`lam j - lam i > 0`, the degree bookkeeping of `eq_zero_of_pow_mul_eval` gives `q = 0`, and
`f g = q(0) = 0`.

## Main results

* `GaloisForLFunctions.HTGeometry.BorelWeil.bwSections_eq_bot_of_lt`
* `GaloisForLFunctions.HTGeometry.BorelWeil.bwSections_eq_bot_of_not_antitone`
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {k : Type*} [Field k]

omit [Fintype n] [LinearOrder n] in
theorem single_eq_smul_single (i j : n) (c : k) :
    (Matrix.single i j c : Matrix n n k) = c • Matrix.single i j 1 := by
  ext r s
  simp [Matrix.single, Matrix.smul_apply]

omit [LinearOrder n] in
/-- The Borel character of a block element is read off from its two block diagonal entries. -/
theorem borelChar_of_coe_blk {i j : n} (hij : i ≠ j) (lam : n → ℕ)
    {x : SpecialLinearGroup n k} {a b c d : k} (hx : (x : Matrix n n k) = blk i j a b c d) :
    borelChar lam x = (1 + a) ^ (lam i) * (1 + d) ^ (lam j) := by
  classical
  have hsub : ∏ r ∈ ({i, j} : Finset n), ((x : Matrix n n k) r r) ^ (lam r)
      = ∏ r : n, ((x : Matrix n n k) r r) ^ (lam r) := by
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro r _ hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    rw [hx, blk_diag_other a b c d hr.1 hr.2, one_pow]
  rw [borelChar, ← hsub, Finset.prod_pair hij, hx, blk_diag_left hij, blk_diag_right hij]

theorem rootU_mem_borel {i j : n} (hij : i ≠ j) (hlt : i < j) (c : k) :
    rootU i j hij c ∈ borel n k := by
  rw [mem_borel_iff, coe_rootU]
  exact blk_blockTriangular hlt _ _ _

theorem rootBeta_mem_borel {i j : n} (hij : i ≠ j) (hlt : i < j) {t : k} (ht : t ≠ 0) :
    rootBeta i j hij t ∈ borel n k := by
  rw [mem_borel_iff, coe_rootBeta i j hij ht]
  exact blk_blockTriangular hlt _ _ _

omit [LinearOrder n] in
theorem borelChar_rootBeta {i j : n} (hij : i ≠ j) (lam : n → ℕ) {t : k} (ht : t ≠ 0) :
    borelChar lam (rootBeta i j hij t) = (t⁻¹) ^ (lam i) * t ^ (lam j) := by
  have h1 : (1 : k) + (t⁻¹ - 1) = t⁻¹ := by ring
  have h2 : (1 : k) + (t - 1) = t := by ring
  rw [borelChar_of_coe_blk hij lam (coe_rootBeta i j hij ht), h1, h2]

/-- **Borel–Weil vanishing.**  A weight that increases across an increasing pair of indices
carries no nonzero section. -/
theorem bwSections_eq_bot_of_lt [Infinite k] {lam : n → ℕ} {i j : n} (hlt : i < j)
    (hlam : lam i < lam j) : bwSections (k := k) lam = ⊥ := by
  classical
  have hne : i ≠ j := ne_of_lt hlt
  set d : ℕ := lam j - lam i with hd_def
  have hd : 0 < d := by omega
  refine (Submodule.eq_bot_iff _).mpr ?_
  intro f hf
  funext g
  show f g = 0
  -- The lower unipotent curve through `g`.
  have hcurve1 : ∀ s : k, ((g * rootL i j hne s : SpecialLinearGroup n k) : Matrix n n k)
      = (g : Matrix n n k) + s • ((g : Matrix n n k) * Matrix.single j i 1) := by
    intro s
    rw [SpecialLinearGroup.coe_mul, rootL, coe_slTrans, Matrix.transvection, mul_add, mul_one,
      single_eq_smul_single, Matrix.mul_smul]
  obtain ⟨q, hq⟩ := exists_poly_of_affine hf.1 _ _ _ hcurve1
  -- The "opposite cell" curve through `g`.
  have hcurve2 : ∀ t : k,
      ((g * rootU i j hne (-t) * rootWinv i j hne : SpecialLinearGroup n k) : Matrix n n k)
        = ((g : Matrix n n k) * ((rootWinv i j hne : SpecialLinearGroup n k) : Matrix n n k))
          + t • (-((g : Matrix n n k) * Matrix.single i j 1
              * ((rootWinv i j hne : SpecialLinearGroup n k) : Matrix n n k))) := by
    intro t
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, rootU, coe_slTrans,
      Matrix.transvection, mul_add, mul_one, single_eq_smul_single, Matrix.mul_smul,
      Matrix.add_mul, Matrix.smul_mul]
    congr 1
    rw [neg_smul, smul_neg]
  obtain ⟨r, hr⟩ := exists_poly_of_affine hf.1 _ _ _ hcurve2
  -- The Bruhat relation between the two curves.
  have hrel : ∀ t : k, t ≠ 0 → q.eval (-t⁻¹) = t ^ d * r.eval t := by
    intro t ht
    have hbr : (g * rootU i j hne (-t) * rootWinv i j hne) * rootBeta i j hne t
        = g * rootL i j hne (-t⁻¹) := by
      rw [← rootBruhat i j hne ht]
      simp [mul_assoc]
    have heq := hf.2 (g * rootU i j hne (-t) * rootWinv i j hne) (rootBeta i j hne t)
      (rootBeta_mem_borel hne hlt ht)
    rw [hbr] at heq
    have hpow : (t⁻¹ : k) ^ (lam i) * t ^ (lam j) = t ^ d := by
      rw [hd_def, inv_pow, inv_mul_eq_div, div_eq_iff (pow_ne_zero _ ht), ← pow_add,
        Nat.sub_add_cancel hlam.le]
    rw [← hq (-t⁻¹), heq, hr t, borelChar_rootBeta hne lam ht, hpow]
  -- Degree bookkeeping kills `q`.
  have hrel2 : ∀ x : k, x ≠ 0 →
      x ^ d * q.eval x = (Polynomial.C ((-1 : k) ^ d) * r).eval (-x⁻¹) := by
    intro x hx
    have hx' : (-x⁻¹ : k) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hx)
    have := hrel (-x⁻¹) hx'
    rw [show (-(-x⁻¹ : k)⁻¹) = x by field_simp] at this
    rw [this]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [neg_pow, inv_pow]
    field_simp
  have hq0 : q = 0 := eq_zero_of_pow_mul_eval hd hrel2
  have hfinal := hq 0
  rw [hq0] at hfinal
  simpa using hfinal

/-- **Borel–Weil vanishing, dominance form.** -/
theorem bwSections_eq_bot_of_not_antitone [Infinite k] {lam : n → ℕ} (hlam : ¬ Antitone lam) :
    bwSections (k := k) lam = ⊥ := by
  rw [Antitone] at hlam
  push Not at hlam
  obtain ⟨i, j, hij, hlt⟩ := hlam
  have hne : i ≠ j := by
    rintro rfl
    exact absurd hlt (lt_irrefl _)
  exact bwSections_eq_bot_of_lt (lt_of_le_of_ne hij hne) hlt

end GaloisForLFunctions.HTGeometry.BorelWeil
