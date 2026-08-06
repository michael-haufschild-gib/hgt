import GaloisForLFunctions.HTGeometry.DifferenceTwoOrbitBrick
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Digamma and its half-translate are independent over the rational functions

The digamma recurrence `ψ(z+1) = ψ(z) + 1/z` turns a relation

  `E·ψ(z) + O·ψ(z+1/2) = P(z)/Q(z)`

into the shift-difference equation `R(z+1) - R(z) = E/z + O/(z+1/2)` for the rational function
`R = P/Q`.  Its pole part is supported on the two `ℤ`-orbits of `0` and `-1/2`, which differ by a
half-integer, so the two-orbit difference brick forces both residues to vanish.

Consequently `ψ(z)` and `ψ(z+1/2)` are linearly independent over `ℂ(z)`: no `ℂ`-combination of the
two is a rational function unless it is trivial.  This is the independence of the two digamma modes
that the archimedean factor of the completed zeta function carries, one for each parity class of
integer shifts.

The hypothesis is allowed to fail on a finite exceptional set, and the quotient need not be in lowest
terms: passing to the reduced fraction only enlarges that exceptional set.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- The set where a polynomial's translate is a root is finite. -/
theorem finite_setOf_translate_isRoot {Q : Polynomial ℂ} (hQ : Q ≠ 0) (a : ℂ) :
    {z : ℂ | Q.eval (z + a) = 0}.Finite := by
  have hroots : {x : ℂ | Q.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hQ
  have hinj : Function.Injective (fun z : ℂ => z + a) := fun x y hxy => by
    simpa using hxy
  exact Set.Finite.preimage hinj.injOn hroots

/-- **Half-translate digamma independence, cofinite form.** If a `ℂ`-combination of `ψ(z)` and
`ψ(z+1/2)` agrees with a rational function in lowest terms on a right half-plane off a finite
exceptional set and off the denominator's zeros, both coefficients vanish. -/
theorem digamma_half_translate_independent_of_cofinite {E O : ℂ} {P Q : Polynomial ℂ}
    (hQ : Q ≠ 0) (hco : IsCoprime P Q) {T : Set ℂ} (hT : T.Finite)
    (h : ∀ z : ℂ, 0 < z.re → z ∉ T → Q.eval z ≠ 0 →
      E * Complex.digamma z + O * Complex.digamma (z + 1 / 2) = P.eval z / Q.eval z) :
    E = 0 ∧ O = 0 := by
  classical
  set A : Polynomial ℂ := C E * (X + C (1 / 2 : ℂ)) + C O * X with hA_def
  have hAeval : ∀ z : ℂ, A.eval z = E * (z + 1 / 2) + O * z := by
    intro z
    simp [hA_def]
  have hTshift : ((fun z : ℂ => z + 1) ⁻¹' T).Finite := by
    have hinj : Function.Injective (fun z : ℂ => z + 1) := fun x y hxy => by simpa using hxy
    exact Set.Finite.preimage hinj.injOn hT
  set S : Set ℂ :=
    {z : ℂ | 0 < z.re} \
      ({z : ℂ | Q.eval (z + 0) = 0} ∪ {z : ℂ | Q.eval (z + 1) = 0} ∪
        (T ∪ (fun z : ℂ => z + 1) ⁻¹' T)) with hS_def
  have hSinf : S.Infinite := by
    refine Set.Infinite.sdiff ?_
      (((finite_setOf_translate_isRoot hQ 0).union
        (finite_setOf_translate_isRoot hQ 1)).union (hT.union hTshift))
    apply Set.Infinite.mono (s := (fun t : ℝ => (t : ℂ)) '' (Set.Ioi 0))
    · rintro z ⟨t, ht, rfl⟩
      simpa using ht
    · exact (Set.Ioi_infinite 0).image Complex.ofReal_injective.injOn
  have hnegNat : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m hzm
    have := congrArg Complex.re hzm
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [this] at hz
    linarith
  have hcross : ∀ z ∈ S,
      (z - 0) ^ (0 + 1) * (z - (-(1 / 2) : ℂ)) ^ (0 + 1) *
          (P.eval (z + 1) * Q.eval z - P.eval z * Q.eval (z + 1))
        = A.eval z * (Q.eval z * Q.eval (z + 1)) := by
    intro z hz
    obtain ⟨hzre, hzbad⟩ := hz
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, not_or] at hzbad
    obtain ⟨⟨hQ0, hQ1⟩, hT0, hT1⟩ := hzbad
    have hQz : Q.eval z ≠ 0 := by simpa using hQ0
    have hQz1 : Q.eval (z + 1) ≠ 0 := hQ1
    have hzre' : (0 : ℝ) < z.re := hzre
    have hz1re : 0 < (z + 1).re := by
      rw [Complex.add_re, Complex.one_re]; linarith
    have hzne : z ≠ 0 := by
      intro h0
      rw [h0] at hzre'
      simp at hzre'
    have hhalfne : z + 1 / 2 ≠ 0 := by
      intro h0
      have hre0 := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.zero_re] at hre0
      have : z.re = -(1 / 2 : ℂ).re := by linarith
      rw [this] at hzre'
      norm_num at hzre'
    have hstep1 : Complex.digamma (z + 1) = Complex.digamma z + z⁻¹ :=
      Complex.digamma_apply_add_one z (hnegNat z hzre)
    have hstep2 : Complex.digamma (z + 1 / 2 + 1) =
        Complex.digamma (z + 1 / 2) + (z + 1 / 2)⁻¹ := by
      refine Complex.digamma_apply_add_one (z + 1 / 2) (hnegNat (z + 1 / 2) ?_)
      rw [Complex.add_re]
      have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
      rw [h2]
      linarith
    have hz := h z hzre hT0 hQz
    have hz1 := h (z + 1) hz1re hT1 hQz1
    rw [show z + 1 + 1 / 2 = z + 1 / 2 + 1 by ring, hstep1, hstep2] at hz1
    rw [eq_div_iff hQz] at hz
    rw [eq_div_iff hQz1] at hz1
    have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hzne
    have hhinv : (z + 1 / 2) * (z + 1 / 2)⁻¹ = 1 := mul_inv_cancel₀ hhalfne
    rw [hAeval]
    linear_combination (-(z * (z + 1 / 2) * Q.eval z)) * hz1 +
      (z * (z + 1 / 2) * Q.eval (z + 1)) * hz +
      (E * (z + 1 / 2) * Q.eval z * Q.eval (z + 1)) * hzinv +
      (O * z * Q.eval z * Q.eval (z + 1)) * hhinv
  have hAzero : A = 0 := by
    refine difference_two_orbit_pole_free_of_eval (c₀ := 0) (c₁ := -(1 / 2))
      (n := 0) (k := 0) hQ hco ?_ ?_ hSinf hcross
    · intro m hm
      have hre := congrArg Complex.re hm
      simp only [Complex.sub_re, Complex.zero_re, Complex.neg_re, Complex.intCast_re] at hre
      have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
      rw [h2] at hre
      have hint : (2 * m : ℤ) = 1 := by
        have : (2 : ℝ) * (m : ℝ) = 1 := by linarith
        exact_mod_cast this
      omega
    · refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      refine max_le ?_ ?_
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        refine le_trans (Polynomial.natDegree_add_le _ _) ?_
        simp
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        simp
  have hE : E = 0 := by
    have h0 := congrArg (Polynomial.eval (0 : ℂ)) hAzero
    rw [hAeval] at h0
    simp only [Polynomial.eval_zero] at h0
    have : E * (1 / 2 : ℂ) = 0 := by linear_combination h0
    simpa using this
  refine ⟨hE, ?_⟩
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) hAzero
  rw [hAeval] at h1
  simp only [Polynomial.eval_zero] at h1
  rw [hE] at h1
  linear_combination h1

/-- **Half-translate digamma independence.** -/
theorem digamma_half_translate_independent {E O : ℂ} {P Q : Polynomial ℂ}
    (hQ : Q ≠ 0) (hco : IsCoprime P Q)
    (h : ∀ z : ℂ, 0 < z.re → Q.eval z ≠ 0 →
      E * Complex.digamma z + O * Complex.digamma (z + 1 / 2) = P.eval z / Q.eval z) :
    E = 0 ∧ O = 0 :=
  digamma_half_translate_independent_of_cofinite hQ hco Set.finite_empty
    fun z hz _ hQz => h z hz hQz

/-- **Half-translate digamma independence for an arbitrary quotient.** The fraction need not be in
lowest terms and the identity may fail on a finite exceptional set. -/
theorem digamma_half_translate_independent_of_quotient {E O : ℂ} {P Q : Polynomial ℂ}
    (hQ : Q ≠ 0) {T : Set ℂ} (hT : T.Finite)
    (h : ∀ z : ℂ, 0 < z.re → z ∉ T → Q.eval z ≠ 0 →
      E * Complex.digamma z + O * Complex.digamma (z + 1 / 2) = P.eval z / Q.eval z) :
    E = 0 ∧ O = 0 := by
  classical
  set R : RatFunc ℂ :=
    algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q with hR_def
  have hQK : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := fun h0 =>
    hQ (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hdenK : algebraMap (Polynomial ℂ) (RatFunc ℂ) R.denom ≠ 0 := fun h0 =>
    R.denom_ne_zero (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hcrossK : algebraMap (Polynomial ℂ) (RatFunc ℂ) (R.num * Q)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (P * R.denom) := by
    rw [map_mul, map_mul]
    have hnd := RatFunc.num_div_denom R
    rw [hR_def] at hnd
    rw [div_eq_div_iff hdenK hQK] at hnd
    linear_combination hnd
  have hcross : R.num * Q = P * R.denom := RatFunc.algebraMap_injective ℂ hcrossK
  refine digamma_half_translate_independent_of_cofinite R.denom_ne_zero R.isCoprime_num_denom
    (T := T ∪ {z : ℂ | Q.eval z = 0}) (hT.union (Polynomial.finite_setOf_isRoot hQ)) ?_
  intro z hz hzT hden
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hzT
  have hQz : Q.eval z ≠ 0 := hzT.2
  have hval := h z hz hzT.1 hQz
  rw [hval]
  have := congrArg (Polynomial.eval z) hcross
  simp only [Polynomial.eval_mul] at this
  field_simp
  linear_combination -this

end GaloisForLFunctions.HTGeometry
