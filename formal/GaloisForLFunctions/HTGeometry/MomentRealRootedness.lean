import GaloisForLFunctions.HTGeometry.OrthogonalMomentPolynomials

/-!
# Orthogonal moment polynomials have no non-real roots

If `z` is a non-real root of a real polynomial `Q`, the monic real quadratic
`(X - Re z)² + (Im z)²` divides `Q`, because the remainder of `Q` by that quadratic is real, linear,
and vanishes at `z`.

Applied to `Q = monicOrtho s (n+1)` this forces a contradiction with orthogonality.  Writing
`Q = ((X - Re z)² + (Im z)²) g`, the quotient `g` has degree `n - 1`, so `⟪Q, g⟫ = 0`.  But the
integrand rearranges as a sum of two squares,

`Q g = ((X - Re z) g)² + (Im z)² g²`,

whose moment value is at least `(Im z)² ⟪g, g⟫ > 0`.  A quantity that is both zero and positive
cannot exist, so `Q` has no non-real root.

The argument uses only positivity of the moment form: no representing measure, no factorisation of
real polynomials into irreducibles, and no sum-of-squares theorem are required.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The monic real quadratic vanishing exactly at `z` and its conjugate. -/
noncomputable def conjQuadratic (z : ℂ) : Polynomial ℝ := (X - C z.re) ^ (2 : ℕ) + C (z.im ^ (2 : ℕ))

theorem degree_sq_X_sub_C (a : ℝ) : ((X - C a) ^ (2 : ℕ) : Polynomial ℝ).degree = 2 := by
  simp [degree_pow, degree_X_sub_C]

theorem conjQuadratic_aux_lt (z : ℂ) :
    (C (z.im ^ (2 : ℕ)) : Polynomial ℝ).degree < ((X - C z.re) ^ (2 : ℕ) : Polynomial ℝ).degree := by
  rw [degree_sq_X_sub_C]
  exact lt_of_le_of_lt degree_C_le (by decide)

theorem conjQuadratic_monic (z : ℂ) : (conjQuadratic z).Monic :=
  ((monic_X_sub_C z.re).pow 2).add_of_left (conjQuadratic_aux_lt z)

theorem conjQuadratic_ne_zero (z : ℂ) : conjQuadratic z ≠ 0 :=
  (conjQuadratic_monic z).ne_zero

theorem conjQuadratic_degree (z : ℂ) : (conjQuadratic z).degree = 2 := by
  rw [conjQuadratic, degree_add_eq_left_of_degree_lt (conjQuadratic_aux_lt z),
    degree_sq_X_sub_C]

theorem conjQuadratic_natDegree (z : ℂ) : (conjQuadratic z).natDegree = 2 :=
  natDegree_eq_of_degree_eq_some (conjQuadratic_degree z)

/-- The quadratic vanishes at `z`. -/
theorem aeval_conjQuadratic (z : ℂ) : Polynomial.aeval z (conjQuadratic z) = 0 := by
  have key : (z - (z.re : ℂ)) ^ (2 : ℕ) + ((z.im : ℝ) : ℂ) ^ (2 : ℕ) = 0 := by
    have hz : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hz, mul_pow, Complex.I_sq]
    ring
  simpa [conjQuadratic] using key

/-- **A non-real root forces a real quadratic factor.**  The remainder of `Q` by `conjQuadratic z`
is linear with real coefficients and vanishes at `z`; a non-real number cannot satisfy a nontrivial
real linear equation, so the remainder is zero. -/
theorem conjQuadratic_dvd_of_aeval_eq_zero (Q : Polynomial ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (hQ : Polynomial.aeval z Q = 0) : conjQuadratic z ∣ Q := by
  rw [← modByMonic_eq_zero_iff_dvd (conjQuadratic_monic z)]
  set r := Q %ₘ conjQuadratic z with hrdef
  have hdeg : r.degree ≤ 1 := by
    refine Order.le_of_lt_succ ?_
    have hlt := degree_modByMonic_lt Q (conjQuadratic_monic z)
    rwa [conjQuadratic_degree z] at hlt
  have hrz : Polynomial.aeval z r = 0 := by
    have hsplit : r + conjQuadratic z * (Q /ₘ conjQuadratic z) = Q :=
      modByMonic_add_div Q (conjQuadratic z)
    have hmap := congrArg (Polynomial.aeval z) hsplit
    rw [map_add, map_mul, aeval_conjQuadratic, zero_mul, add_zero, hQ] at hmap
    exact hmap
  have hform : r = C (r.coeff 1) * X + C (r.coeff 0) := eq_X_add_C_of_degree_le_one hdeg
  have hlin : (r.coeff 1 : ℂ) * z + (r.coeff 0 : ℂ) = 0 := by
    rw [hform] at hrz
    simpa using hrz
  have him : r.coeff 1 * z.im = 0 := by
    have := congrArg Complex.im hlin
    simpa using this
  have hc1 : r.coeff 1 = 0 := by
    rcases mul_eq_zero.mp him with hc | hi
    · exact hc
    · exact absurd hi hz
  have hc0 : r.coeff 0 = 0 := by
    rw [hc1] at hlin
    simpa using hlin
  rw [hform, hc1, hc0]
  simp

/-- **The orthogonal moment polynomials have no non-real roots.**  A non-real root would produce a
quotient `g` of degree low enough to be orthogonal to `monicOrtho s (n+1)`, while the same pairing
is a sum of two moment squares bounded below by `(Im z)² ⟪g, g⟫ > 0`. -/
theorem monicOrtho_aeval_ne_zero (h : PositiveMomentForm s) (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    Polynomial.aeval z (monicOrtho s (n + 1)) ≠ 0 := by
  intro hQ
  obtain ⟨g, hQg⟩ := conjQuadratic_dvd_of_aeval_eq_zero (monicOrtho s (n + 1)) hz hQ
  have hgne : g ≠ 0 := by
    intro hg0
    rw [hg0, mul_zero] at hQg
    exact monicOrtho_ne_zero s (n + 1) hQg
  have hnd : (monicOrtho s (n + 1)).natDegree = 2 + g.natDegree := by
    rw [hQg, natDegree_mul (conjQuadratic_ne_zero z) hgne, conjQuadratic_natDegree]
  have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
  have hglt : g.natDegree < n + 1 := by omega
  have hgdeg : g.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hgne]
    exact_mod_cast hglt
  have hzero : momentInner s (monicOrtho s (n + 1)) g = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) (n + 1) le_rfl g hgdeg
  have hpoly : conjQuadratic z * g * g
      = ((X - C z.re) * g) * ((X - C z.re) * g) + (z.im ^ (2 : ℕ)) • (g * g) := by
    simp only [conjQuadratic, Polynomial.smul_eq_C_mul]
    ring
  have hexp : momentInner s (monicOrtho s (n + 1)) g
      = momentInner s ((X - C z.re) * g) ((X - C z.re) * g)
        + z.im ^ (2 : ℕ) * momentInner s g g := by
    rw [hQg, momentInner_def, hpoly, momentFunctional_add, momentFunctional_smul,
      momentInner_def, momentInner_def]
  have hpos : 0 < momentInner s ((X - C z.re) * g) ((X - C z.re) * g)
      + z.im ^ (2 : ℕ) * momentInner s g g := by
    have h1 : 0 ≤ momentInner s ((X - C z.re) * g) ((X - C z.re) * g) := h.nonneg _
    have h2 : 0 < momentInner s g g := h.pos_of_ne_zero g hgne
    have h3 : 0 < z.im ^ (2 : ℕ) :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hz))
    have h4 : 0 < z.im ^ (2 : ℕ) * momentInner s g g := mul_pos h3 h2
    linarith
  rw [hexp] at hzero
  exact absurd hzero (ne_of_gt hpos)

/-- Every complex root of an orthogonal moment polynomial is real. -/
theorem monicOrtho_root_im_eq_zero (h : PositiveMomentForm s) (n : ℕ) {z : ℂ}
    (hz : Polynomial.aeval z (monicOrtho s (n + 1)) = 0) : z.im = 0 := by
  by_contra hne
  exact monicOrtho_aeval_ne_zero h n hne hz

/-! ## Splitting over the reals -/

/-- **A real polynomial all of whose complex roots are real splits over `ℝ`.**  Induction on a
degree bound: a nonconstant polynomial has a complex root by the fundamental theorem of algebra,
that root is real by hypothesis, so a real linear factor splits off and the quotient inherits the
hypothesis. -/
theorem splits_of_forall_aeval_im_eq_zero :
    ∀ (N : ℕ) (Q : Polynomial ℝ), Q.natDegree ≤ N →
      (∀ z : ℂ, Polynomial.aeval z Q = 0 → z.im = 0) → Q.Splits := by
  intro N
  induction N with
  | zero =>
      intro Q hQ _
      exact Splits.of_natDegree_eq_zero (Nat.le_zero.mp hQ)
  | succ N ih =>
      intro Q hQ hroot
      rcases Nat.eq_zero_or_pos Q.natDegree with h0 | hpos
      · exact Splits.of_natDegree_eq_zero h0
      have hQ0 : Q ≠ 0 := by
        intro hzq
        rw [hzq] at hpos
        simp at hpos
      have hmapdeg : 0 < (Q.map (algebraMap ℝ ℂ)).degree := by
        rw [degree_map, degree_eq_natDegree hQ0]
        exact_mod_cast hpos
      obtain ⟨z, hz⟩ := Complex.exists_root hmapdeg
      have hzQ : Polynomial.aeval z Q = 0 := by
        have hmap : Polynomial.aeval z Q = (Q.map (algebraMap ℝ ℂ)).eval z := by
          simp [aeval_def, eval_map]
        rw [hmap]
        exact hz
      have him : z.im = 0 := hroot z hzQ
      have hzre : z = ((z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hreal : Q.eval z.re = 0 := by
        have hbridge : Polynomial.aeval ((z.re : ℝ) : ℂ) Q = ((Q.eval z.re : ℝ) : ℂ) := by
          simpa using aeval_algebraMap_apply ℂ z.re Q
        have hzero : Polynomial.aeval ((z.re : ℝ) : ℂ) Q = 0 := by
          rw [← hzre]; exact hzQ
        rw [hbridge] at hzero
        exact_mod_cast hzero
      obtain ⟨Q1, hQ1⟩ := (dvd_iff_isRoot.mpr hreal : (X - C z.re) ∣ Q)
      have hQ1ne : Q1 ≠ 0 := by
        intro hzz
        rw [hzz, mul_zero] at hQ1
        exact hQ0 hQ1
      have hdeg1 : Q1.natDegree ≤ N := by
        have hsum : Q.natDegree = 1 + Q1.natDegree := by
          rw [hQ1, natDegree_mul (X_sub_C_ne_zero z.re) hQ1ne, natDegree_X_sub_C]
        omega
      have hroot1 : ∀ w : ℂ, Polynomial.aeval w Q1 = 0 → w.im = 0 := by
        intro w hw
        refine hroot w ?_
        rw [hQ1, map_mul, hw, mul_zero]
      have hsplit1 := ih Q1 hdeg1 hroot1
      rw [hQ1]
      exact splits_X_sub_C_mul_iff.mpr hsplit1

/-- **The orthogonal moment polynomials split over `ℝ`.**  Every root is real, so the polynomial is
a product of real linear factors. -/
theorem monicOrtho_splits (h : PositiveMomentForm s) (n : ℕ) :
    (monicOrtho s (n + 1)).Splits :=
  splits_of_forall_aeval_im_eq_zero (monicOrtho s (n + 1)).natDegree (monicOrtho s (n + 1))
    le_rfl fun _ hz => monicOrtho_root_im_eq_zero h n hz

end HTGeometry
