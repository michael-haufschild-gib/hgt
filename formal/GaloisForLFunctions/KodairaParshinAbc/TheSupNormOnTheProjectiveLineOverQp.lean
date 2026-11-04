import Mathlib.Analysis.Polynomial.Norm
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-!
# The sup norm on the projective line over `ℚ_p`

For a flat projective model with reduced fibres, the sup norm of a global section over the
`K̄_v`-points equals the norm induced by the integral model: a section of norm `1` reduces to a
nonzero section of the special fibre, which is nonzero at some closed point, and that point lifts.
Over `K_v` itself the lifting only reaches the `k(v)`-rational points of the special fibre.

This module settles the case `(P¹_{ℤ_p}, O(n))` over `ℚ_p`.  A section of `O(n)` is a polynomial
`f` of degree `≤ n`; its model norm is the Gauss norm `‖f‖ = max ‖aᵢ‖` (`Polynomial.supNorm`), and
its pointwise norm is `‖f(x)‖` on the chart `‖x‖ ≤ 1` and `‖(reflect n f)(y)‖` on the chart at
infinity.

* Both charts are bounded by the Gauss norm (`norm_eval_le_supNorm`, `norm_eval_reflect_le`).
* **For `n ≤ p` the Gauss norm is attained at a `ℚ_p`-point** (`exists_attains_supNorm`): the
  reduction of `f/‖f‖` is a nonzero section of `O(n)` over `F_p`; if it vanished at all `p + 1`
  points of `P¹(F_p)` it would have `p` affine roots and a root at infinity, impossible in degree
  `≤ p`.
* **For `n = p + 1` this fails** (`sup_lt_supNorm_X_sub_X_pow`): `x - x^p` has Gauss norm `1`,
  but its reduction `x(1 - x^{p-1})` vanishes on all of `P¹(F_p)`, so every `ℚ_p`-point gives norm
  `< 1`.

So over `ℚ_p` the sup norm on `H⁰(P¹, O(n))` is the model norm exactly for `n ≤ p`; passing to
`K̄_v`, whose residue field is infinite, removes the restriction.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.KodairaParshinAbc

variable {p : ℕ} [hp : Fact p.Prime]

/-- The ultrametric inequality for finite sums in `ℚ_p`. -/
theorem padic_norm_sum_le {ι : Type*} (s : Finset ι) (g : ι → ℚ_[p]) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ s, ‖g i‖ ≤ M) : ‖∑ i ∈ s, g i‖ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Padic.nonarchimedean _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- On the closed unit disc a polynomial is bounded by its Gauss norm. -/
theorem norm_eval_le_supNorm (f : ℚ_[p][X]) {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    ‖f.eval x‖ ≤ f.supNorm := by
  rw [eval_eq_sum_range]
  refine padic_norm_sum_le _ _ (supNorm_nonneg f) fun i _ => ?_
  rw [norm_mul, norm_pow]
  calc ‖f.coeff i‖ * ‖x‖ ^ i ≤ ‖f.coeff i‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hx) (norm_nonneg _)
    _ = ‖f.coeff i‖ := mul_one _
    _ ≤ f.supNorm := le_supNorm f i

theorem supNorm_reflect_le (f : ℚ_[p][X]) (n : ℕ) : (reflect n f).supNorm ≤ f.supNorm := by
  obtain ⟨i, hi⟩ := exists_eq_supNorm (reflect n f)
  rw [hi, coeff_reflect]
  exact le_supNorm f _

/-- The chart at infinity is bounded by the Gauss norm as well. -/
theorem norm_eval_reflect_le (f : ℚ_[p][X]) (n : ℕ) {y : ℚ_[p]} (hy : ‖y‖ ≤ 1) :
    ‖(reflect n f).eval y‖ ≤ f.supNorm :=
  (norm_eval_le_supNorm _ hy).trans (supNorm_reflect_le f n)

/-! ## Reduction modulo `p` -/

theorem norm_coe_eq_one_of_toZMod_ne_zero {y : ℤ_[p]} (hy : PadicInt.toZMod y ≠ 0) :
    ‖(y : ℚ_[p])‖ = 1 := by
  rw [← PadicInt.norm_def, ← PadicInt.isUnit_iff, ← IsLocalRing.notMem_maximalIdeal,
    ← PadicInt.ker_toZMod, RingHom.mem_ker]
  exact hy

theorem norm_coe_lt_one_of_toZMod_eq_zero {y : ℤ_[p]} (hy : PadicInt.toZMod y = 0) :
    ‖(y : ℚ_[p])‖ < 1 := by
  rw [← PadicInt.norm_def]
  have hmem : y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]
    exact hy
  exact PadicInt.mem_nonunits.mp hmem

/-- Evaluation commutes with a ring homomorphism. -/
theorem map_eval_eq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (G : R[X]) (y : R) :
    φ (G.eval y) = (G.map φ).eval (φ y) := by
  rw [eval_map, eval₂_hom]

/-- A polynomial with coefficients in the unit ball comes from `ℤ_p[X]`. -/
theorem exists_integral_model (g : ℚ_[p][X]) (hg : ∀ i, ‖g.coeff i‖ ≤ 1) :
    ∃ G : ℤ_[p][X], G.map PadicInt.Coe.ringHom = g ∧ G.natDegree = g.natDegree := by
  apply exists_natDegree_eq_of_mem_lifts
  rw [lifts_iff_coeff_lifts]
  intro n
  exact ⟨⟨g.coeff n, hg n⟩, rfl⟩

/-- **The Gauss norm is attained on `P¹(ℚ_p)` for sections of `O(n)`, `n ≤ p`.** -/
theorem exists_attains_supNorm {f : ℚ_[p][X]} {n : ℕ} (hn : f.natDegree ≤ n) (hnp : n ≤ p) :
    ∃ x : ℚ_[p], ‖x‖ ≤ 1 ∧ (‖f.eval x‖ = f.supNorm ∨ ‖(reflect n f).eval x‖ = f.supNorm) := by
  by_cases hf : f = 0
  · exact ⟨0, by simp, Or.inl (by simp [hf])⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_supNorm f
  have hM : 0 < f.supNorm :=
    lt_of_le_of_ne (supNorm_nonneg f) (Ne.symm ((supNorm_eq_zero_iff f).not.mpr hf))
  set a := f.coeff i₀ with ha_def
  have ha : a ≠ 0 := by
    intro h
    rw [hi₀, h, norm_zero] at hM
    exact lt_irrefl _ hM
  set g := C a⁻¹ * f with hg_def
  have hgcoeff : ∀ i, g.coeff i = a⁻¹ * f.coeff i := fun i => coeff_C_mul _
  have hg1 : ∀ i, ‖g.coeff i‖ ≤ 1 := by
    intro i
    rw [hgcoeff, norm_mul, norm_inv, ← hi₀, inv_mul_le_iff₀ hM, mul_one]
    exact le_supNorm f i
  have hfg : f = C a * g := by
    rw [hg_def, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  obtain ⟨G, hGmap, hGdeg⟩ := exists_integral_model g hg1
  have hGcoeff : ∀ i, ((G.coeff i : ℤ_[p]) : ℚ_[p]) = g.coeff i := by
    intro i
    rw [← hGmap, coeff_map]
    rfl
  have hGeval : ∀ y : ℤ_[p], ((G.eval y : ℤ_[p]) : ℚ_[p]) = g.eval (y : ℚ_[p]) := by
    intro y
    rw [← hGmap]
    exact map_eval_eq PadicInt.Coe.ringHom G y
  set Gbar := G.map (PadicInt.toZMod (p := p)) with hGbar
  have hG1 : G.coeff i₀ = 1 := by
    apply Subtype.ext
    rw [show ((G.coeff i₀ : ℤ_[p]) : ℚ_[p]) = g.coeff i₀ from hGcoeff i₀, hgcoeff,
      inv_mul_cancel₀ ha]
    rfl
  have hGbar0 : Gbar ≠ 0 := by
    intro h
    have := congrArg (coeff · i₀) h
    simp only [hGbar, coeff_map, hG1, map_one, coeff_zero] at this
    exact one_ne_zero this
  have hgdeg : g.natDegree ≤ f.natDegree := natDegree_C_mul_le _ _
  have hdeg : Gbar.natDegree ≤ n := (natDegree_map_le).trans (hGdeg ▸ hgdeg.trans hn)
  by_cases hroot : ∃ z : ZMod p, Gbar.eval z ≠ 0
  · obtain ⟨z, hz⟩ := hroot
    refine ⟨((z.val : ℤ_[p]) : ℚ_[p]), ?_, Or.inl ?_⟩
    · rw [← PadicInt.norm_def]
      exact PadicInt.norm_le_one _
    · have hred : PadicInt.toZMod (G.eval (z.val : ℤ_[p])) ≠ 0 := by
        rw [map_eval_eq, map_natCast, ZMod.natCast_zmod_val]
        exact hz
      have hfx : ‖f.eval ((z.val : ℤ_[p]) : ℚ_[p])‖ =
          ‖a‖ * ‖g.eval ((z.val : ℤ_[p]) : ℚ_[p])‖ := by
        conv_lhs => rw [hfg]
        rw [eval_mul, eval_C, norm_mul]
      rw [hfx, ← hGeval, norm_coe_eq_one_of_toZMod_ne_zero hred, mul_one, hi₀]
  · push Not at hroot
    have hp_le : p ≤ Gbar.natDegree := by
      by_contra hlt
      push Not at hlt
      exact hGbar0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero Gbar (f := id)
        Function.injective_id (fun z => hroot z) (by rwa [ZMod.card]))
    have hdn : Gbar.natDegree = n := by omega
    have hlead : PadicInt.toZMod (G.coeff n) ≠ 0 := by
      have : Gbar.coeff n ≠ 0 := by
        rw [← hdn]
        exact leadingCoeff_ne_zero.mpr hGbar0
      rwa [hGbar, coeff_map] at this
    refine ⟨0, by simp, Or.inr ?_⟩
    have hfn : f.coeff n = a * g.coeff n := by
      conv_lhs => rw [hfg]
      exact coeff_C_mul _
    rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_le (Nat.zero_le n), Nat.sub_zero, hfn,
      norm_mul, ← hGcoeff, norm_coe_eq_one_of_toZMod_ne_zero hlead, mul_one, hi₀]

/-! ## Sharpness at `n = p + 1` -/

theorem coeff_X_sub_X_pow (i : ℕ) :
    ((X - X ^ p : ℚ_[p][X])).coeff i = (if i = 1 then 1 else 0) - (if i = p then 1 else 0) := by
  rw [coeff_sub, coeff_X, coeff_X_pow]
  congr 1
  split_ifs <;> simp_all [eq_comm]

theorem supNorm_X_sub_X_pow : ((X - X ^ p : ℚ_[p][X])).supNorm = 1 := by
  have hp1 : p ≠ 1 := hp.out.one_lt.ne'
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_eq_supNorm (X - X ^ p : ℚ_[p][X])
    rw [hi, coeff_X_sub_X_pow]
    split_ifs <;> simp_all
  · have := le_supNorm (X - X ^ p : ℚ_[p][X]) 1
    rwa [coeff_X_sub_X_pow, if_pos rfl, if_neg (Ne.symm hp1), sub_zero, norm_one] at this

theorem reflect_X_sub_X_pow : reflect (p + 1) (X - X ^ p : ℚ_[p][X]) = X ^ p - X := by
  have hp1 : 1 < p := hp.out.one_lt
  ext i
  rw [coeff_reflect, coeff_X_sub_X_pow, coeff_sub, coeff_X_pow, coeff_X]
  by_cases hi : i ≤ p + 1
  · rw [revAt_le hi]
    have e1 : (p + 1 - i = 1) ↔ i = p := by omega
    have e2 : (p + 1 - i = p) ↔ 1 = i := by omega
    simp only [e1, e2]
  · rw [revAt_eq_self_of_lt (by omega)]
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ p := by omega
    have h3 : (1 : ℕ) ≠ i := by omega
    simp only [h1, h2, h3, if_false]

/-- Fermat's little theorem on the unit disc: `‖x - x^p‖ < 1` for `‖x‖ ≤ 1`. -/
theorem norm_sub_pow_lt_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) : ‖x - x ^ p‖ < 1 := by
  set y : ℤ_[p] := ⟨x, hx⟩
  have hxy : x - x ^ p = ((y - y ^ p : ℤ_[p]) : ℚ_[p]) := by
    push_cast
    rfl
  rw [hxy]
  apply norm_coe_lt_one_of_toZMod_eq_zero
  rw [map_sub, map_pow, ZMod.pow_card, sub_self]

/-- **Failure at `n = p + 1`.**  The section `x - x^p` of `O(p + 1)` has Gauss norm `1` while its
norm is `< 1` at every `ℚ_p`-point of both charts. -/
theorem sup_lt_supNorm_X_sub_X_pow :
    ((X - X ^ p : ℚ_[p][X])).natDegree ≤ p + 1 ∧ ((X - X ^ p : ℚ_[p][X])).supNorm = 1 ∧
      ∀ x : ℚ_[p], ‖x‖ ≤ 1 →
        ‖((X - X ^ p : ℚ_[p][X])).eval x‖ < 1 ∧
          ‖(reflect (p + 1) (X - X ^ p : ℚ_[p][X])).eval x‖ < 1 := by
  refine ⟨?_, supNorm_X_sub_X_pow, fun x hx => ⟨?_, ?_⟩⟩
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_X_le.trans (by omega)
    · exact (natDegree_X_pow_le p).trans (by omega)
  · simpa using norm_sub_pow_lt_one hx
  · rw [reflect_X_sub_X_pow]
    have := norm_sub_pow_lt_one hx
    rw [← norm_neg] at this
    simpa using this

end GaloisForLFunctions.KodairaParshinAbc
