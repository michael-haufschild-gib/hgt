import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy

/-!
# Extremality of the monic orthogonal polynomial and comparison of Jacobi data

Two facts about the monic orthogonal family of a positive definite moment form, both purely
algebraic consequences of the Pythagorean splitting `A = Pₙ + R` with `deg R < n`:

* `monicOrthoNormSq_le_momentInner_of_monic` — `Pₙ` minimizes the moment square among all monic
  polynomials of degree `n`.  This is the classical variational description
  `Hₙ = inf {L(Q²) : Q monic of degree n}`.
* `monicOrthoNormSq_le_of_momentInner_le` and `monicOrthoBeta_le_of_momentInner_le` — if two
  moment forms are comparable with constant `K` on every polynomial, then their monic norms are
  comparable with the same constant `K`, and their lower Jacobi coefficients `βₙ = Hₙ/Hₙ₋₁` are
  comparable with constant `K²`.

The variational description is what makes the comparison work: it removes all reference to the two
different orthogonal families, so a single test polynomial (the monic orthogonal polynomial of the
*other* form) transfers the bound.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-! ## The variational description of the monic norm -/

/-- **The monic orthogonal polynomial minimizes the moment square.**  For every monic `A` of degree
`n`, the moment square of `A` is the moment square of `monicOrtho s n` plus the moment square of the
lower-degree remainder. -/
theorem momentInner_self_eq_monicOrthoNormSq_add {s : ℕ → ℝ} (h : PositiveMomentForm s)
    {A : Polynomial ℝ} (hA : A.Monic) {n : ℕ} (hdeg : A.natDegree = n) :
    momentInner s A A =
      monicOrthoNormSq s n + momentInner s (A - monicOrtho s n) (A - monicOrtho s n) := by
  set R : Polynomial ℝ := A - monicOrtho s n with hR
  have hdegR : R.degree < (n : WithBot ℕ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hA1 : A = 1 := by
        have := hA.leadingCoeff
        have hnat : A.natDegree = 0 := by rw [hdeg, hn]
        exact Polynomial.eq_one_of_monic_natDegree_zero hA hnat
      simp [hR, hA1, hn]
    · have hAdeg : A.degree = (n : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hA.ne_zero, hdeg]
      have hPdeg : (monicOrtho s n).degree = (n : WithBot ℕ) := monicOrtho_degree s n
      have hdegeq : A.degree = (monicOrtho s n).degree := by rw [hAdeg, hPdeg]
      have hlc : A.leadingCoeff = (monicOrtho s n).leadingCoeff := by
        rw [hA.leadingCoeff, (monicOrtho_monic s n).leadingCoeff]
      have := Polynomial.degree_sub_lt hdegeq hA.ne_zero hlc
      rwa [hAdeg] at this
  have horth : momentInner s (monicOrtho s n) R = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h n n le_rfl R hdegR
  have hsplit : A = monicOrtho s n + R := by rw [hR]; ring
  rw [hsplit, momentInner_add_left, momentInner_add_right, momentInner_add_right, horth,
    momentInner_comm s R (monicOrtho s n), horth]
  simp [monicOrthoNormSq]

/-- **Variational bound.**  `monicOrthoNormSq s n ≤ momentInner s A A` for every monic `A` of degree
`n`. -/
theorem monicOrthoNormSq_le_momentInner_of_monic {s : ℕ → ℝ} (h : PositiveMomentForm s)
    {A : Polynomial ℝ} (hA : A.Monic) {n : ℕ} (hdeg : A.natDegree = n) :
    monicOrthoNormSq s n ≤ momentInner s A A := by
  rw [momentInner_self_eq_monicOrthoNormSq_add h hA hdeg]
  exact le_add_of_nonneg_right (h.nonneg _)

/-! ## Comparison of two moment forms -/

/-- **Monic norms inherit a uniform comparison of the moment forms.**  If the `t`-form is bounded by
`K` times the `s`-form on every polynomial, the same holds for the monic orthogonal norms. -/
theorem monicOrthoNormSq_le_of_momentInner_le {s t : ℕ → ℝ} (ht : PositiveMomentForm t) {K : ℝ}
    (hK : ∀ p : Polynomial ℝ, momentInner t p p ≤ K * momentInner s p p) (n : ℕ) :
    monicOrthoNormSq t n ≤ K * monicOrthoNormSq s n := by
  have hmin := monicOrthoNormSq_le_momentInner_of_monic ht (monicOrtho_monic s n)
    (natDegree_monicOrtho s n)
  exact hmin.trans (by simpa [monicOrthoNormSq] using hK (monicOrtho s n))

/-- **Lower Jacobi coefficients inherit the squared comparison constant.**  `βₙ = Hₙ / Hₙ₋₁`, so a
two-sided comparison with constant `K` of the norms gives a two-sided comparison with constant `K²`
of the `β`'s. -/
theorem monicOrthoBeta_le_of_momentInner_le {s t : ℕ → ℝ} (hs : PositiveMomentForm s)
    (ht : PositiveMomentForm t) {K : ℝ} (hKpos : 0 < K)
    (hKts : ∀ p : Polynomial ℝ, momentInner t p p ≤ K * momentInner s p p)
    (hKst : ∀ p : Polynomial ℝ, momentInner s p p ≤ K * momentInner t p p) (n : ℕ) :
    monicOrthoBeta t (n + 1) ≤ K ^ 2 * monicOrthoBeta s (n + 1) := by
  have hup : monicOrthoNormSq t (n + 1) ≤ K * monicOrthoNormSq s (n + 1) :=
    monicOrthoNormSq_le_of_momentInner_le ht hKts (n + 1)
  have hdown : monicOrthoNormSq s n ≤ K * monicOrthoNormSq t n :=
    monicOrthoNormSq_le_of_momentInner_le hs hKst n
  have hsn : 0 < monicOrthoNormSq s n := monicOrthoNormSq_pos hs n
  have htn : 0 < monicOrthoNormSq t n := monicOrthoNormSq_pos ht n
  have hsn1 : 0 < monicOrthoNormSq s (n + 1) := monicOrthoNormSq_pos hs (n + 1)
  have htn1 : 0 < monicOrthoNormSq t (n + 1) := monicOrthoNormSq_pos ht (n + 1)
  have key : monicOrthoNormSq t (n + 1) * monicOrthoNormSq s n
      ≤ K ^ 2 * monicOrthoNormSq s (n + 1) * monicOrthoNormSq t n := by
    have h1 : monicOrthoNormSq t (n + 1) * monicOrthoNormSq s n
        ≤ (K * monicOrthoNormSq s (n + 1)) * monicOrthoNormSq s n :=
      mul_le_mul_of_nonneg_right hup hsn.le
    have h2 : (K * monicOrthoNormSq s (n + 1)) * monicOrthoNormSq s n
        ≤ (K * monicOrthoNormSq s (n + 1)) * (K * monicOrthoNormSq t n) :=
      mul_le_mul_of_nonneg_left hdown (by positivity)
    have h3 : (K * monicOrthoNormSq s (n + 1)) * (K * monicOrthoNormSq t n)
        = K ^ 2 * monicOrthoNormSq s (n + 1) * monicOrthoNormSq t n := by ring
    linarith
  have hgoal : monicOrthoNormSq t (n + 1) / monicOrthoNormSq t n
      ≤ K ^ 2 * (monicOrthoNormSq s (n + 1) / monicOrthoNormSq s n) := by
    rw [div_le_iff₀ htn]
    have hrw : K ^ 2 * (monicOrthoNormSq s (n + 1) / monicOrthoNormSq s n) * monicOrthoNormSq t n
        = K ^ 2 * monicOrthoNormSq s (n + 1) * monicOrthoNormSq t n / monicOrthoNormSq s n := by
      field_simp
    rw [hrw, le_div_iff₀ hsn]
    exact key
  simpa [monicOrthoBeta] using hgoal

end HTGeometry
