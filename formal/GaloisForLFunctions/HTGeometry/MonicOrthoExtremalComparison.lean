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

A third group identifies `monicOrtho` with any concretely given orthogonal family of exact degrees:
`monicOrtho_eq_of_orthogonal_family`.  This is what lets a source-defined family (built from its own
recurrence, as the archimedean Gamma--Jacobi family is) be used to evaluate `monicOrthoNormSq` and
hence the lower Jacobi coefficients.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-! ## The variational description of the monic norm -/

/-- A monic polynomial of degree `n` differs from `monicOrtho s n` by a polynomial of degree `< n`. -/
theorem degree_sub_monicOrtho_lt (s : ℕ → ℝ) {A : Polynomial ℝ} (hA : A.Monic) {n : ℕ}
    (hdeg : A.natDegree = n) : (A - monicOrtho s n).degree < (n : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hA1 : A = 1 := Polynomial.eq_one_of_monic_natDegree_zero hA (by rw [hdeg, hn])
    simp [hA1, hn]
  · have hAdeg : A.degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero, hdeg]
    have hdegeq : A.degree = (monicOrtho s n).degree := by
      rw [hAdeg, monicOrtho_degree s n]
    have hlc : A.leadingCoeff = (monicOrtho s n).leadingCoeff := by
      rw [hA.leadingCoeff, (monicOrtho_monic s n).leadingCoeff]
    have := Polynomial.degree_sub_lt hdegeq hA.ne_zero hlc
    rwa [hAdeg] at this

/-- **Uniqueness of the monic orthogonal polynomial.**  A monic polynomial of degree `n` orthogonal
to every strictly lower degree is `monicOrtho s n`. -/
theorem eq_monicOrtho_of_monic_of_orthogonal {s : ℕ → ℝ} (h : PositiveMomentForm s)
    {A : Polynomial ℝ} (hA : A.Monic) {n : ℕ} (hdeg : A.natDegree = n)
    (horth : ∀ q : Polynomial ℝ, q.degree < (n : WithBot ℕ) → momentInner s A q = 0) :
    A = monicOrtho s n := by
  have hR := degree_sub_monicOrtho_lt s hA hdeg
  have h1 : momentInner s A (A - monicOrtho s n) = 0 := horth _ hR
  have h2 : momentInner s (monicOrtho s n) (A - monicOrtho s n) = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h n n le_rfl _ hR
  have hzero : momentInner s (A - monicOrtho s n) (A - monicOrtho s n) = 0 := by
    rw [momentInner_sub_left, h1, h2, sub_zero]
  by_contra hne
  have hRne : A - monicOrtho s n ≠ 0 := sub_ne_zero_of_ne hne
  exact absurd hzero (ne_of_gt (h.pos_of_ne_zero _ hRne))

/-- **The monic orthogonal polynomial minimizes the moment square.**  For every monic `A` of degree
`n`, the moment square of `A` is the moment square of `monicOrtho s n` plus the moment square of the
lower-degree remainder. -/
theorem momentInner_self_eq_monicOrthoNormSq_add {s : ℕ → ℝ} (h : PositiveMomentForm s)
    {A : Polynomial ℝ} (hA : A.Monic) {n : ℕ} (hdeg : A.natDegree = n) :
    momentInner s A A =
      monicOrthoNormSq s n + momentInner s (A - monicOrtho s n) (A - monicOrtho s n) := by
  set R : Polynomial ℝ := A - monicOrtho s n with hR
  have hdegR : R.degree < (n : WithBot ℕ) := degree_sub_monicOrtho_lt s hA hdeg
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

/-! ## Identification with a concretely given orthogonal family -/

/-- **Triangular families span by degree.**  If `f k` has exact degree `k`, every polynomial of
degree `< m` lies in the span of `f 0, …, f (m-1)`. -/
theorem mem_span_of_degree_lt {f : ℕ → Polynomial ℝ} (hdeg : ∀ k, (f k).natDegree = k)
    (hne : ∀ k, f k ≠ 0) (m : ℕ) :
    ∀ p : Polynomial ℝ, p.degree < (m : WithBot ℕ) →
      p ∈ Submodule.span ℝ (f '' {k : ℕ | k < m}) := by
  induction m with
  | zero =>
      intro p hp
      have hbot : p.degree = ⊥ := Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
      rw [Polynomial.degree_eq_bot.mp hbot]
      exact Submodule.zero_mem _
  | succ m ih =>
      intro p hp
      have hmono : (f '' {k : ℕ | k < m}) ⊆ (f '' {k : ℕ | k < m + 1}) :=
        Set.image_mono fun k hk => Nat.lt_succ_of_lt hk
      rcases eq_or_ne p 0 with rfl | hp0
      · exact Submodule.zero_mem _
      · have hdlt : p.natDegree < m + 1 := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
        have hdm : p.natDegree ≤ m := Nat.lt_succ_iff.mp hdlt
        set d := p.natDegree with hd
        have hlcf : (f d).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hne d)
        set c : ℝ := p.leadingCoeff / (f d).leadingCoeff with hc
        set g : Polynomial ℝ := Polynomial.C c * f d with hg
        have hgdeg : g.degree = (d : WithBot ℕ) := by
          have hcne : c ≠ 0 :=
            div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0) hlcf
          rw [hg, Polynomial.degree_C_mul hcne,
            Polynomial.degree_eq_natDegree (hne d), hdeg d]
        have hglc : g.leadingCoeff = p.leadingCoeff := by
          rw [hg, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]
          field_simp
        have hsub : (p - g).degree < (d : WithBot ℕ) := by
          have hdegeq : p.degree = g.degree := by
            rw [hgdeg, Polynomial.degree_eq_natDegree hp0]
          have := Polynomial.degree_sub_lt hdegeq hp0 hglc.symm
          rwa [Polynomial.degree_eq_natDegree hp0] at this
        have hcast : ((d : ℕ) : WithBot ℕ) ≤ ((m : ℕ) : WithBot ℕ) := by exact_mod_cast hdm
        have hmem1 : (p - g) ∈ Submodule.span ℝ (f '' {k : ℕ | k < m + 1}) :=
          Submodule.span_mono hmono (ih _ (lt_of_lt_of_le hsub hcast))
        have hmem2 : f d ∈ Submodule.span ℝ (f '' {k : ℕ | k < m + 1}) :=
          Submodule.subset_span ⟨d, hdlt, rfl⟩
        have hpeq : p = (p - g) + c • f d := by
          rw [hg, Polynomial.smul_eq_C_mul]; ring
        rw [hpeq]
        exact Submodule.add_mem _ hmem1 (Submodule.smul_mem _ _ hmem2)

/-- **The monic orthogonal family is any orthogonal family of exact degrees, renormalized.** -/
theorem monicOrtho_eq_of_orthogonal_family {s : ℕ → ℝ} (h : PositiveMomentForm s)
    {f : ℕ → Polynomial ℝ} (hdeg : ∀ k, (f k).natDegree = k) (hne : ∀ k, f k ≠ 0)
    (horth : ∀ m n : ℕ, m ≠ n → momentInner s (f m) (f n) = 0) (n : ℕ) :
    monicOrtho s n = ((f n).leadingCoeff)⁻¹ • f n := by
  have hlcf : (f n).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hne n)
  set A : Polynomial ℝ := ((f n).leadingCoeff)⁻¹ • f n with hA
  have hAmonic : A.Monic := by
    have : A = Polynomial.C ((f n).leadingCoeff)⁻¹ * f n := by
      rw [hA, Polynomial.smul_eq_C_mul]
    rw [Polynomial.Monic, this, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    field_simp
  have hAdeg : A.natDegree = n := by
    have hCne : ((f n).leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero hlcf
    rw [hA, Polynomial.smul_eq_C_mul, Polynomial.natDegree_C_mul hCne, hdeg n]
  refine (eq_monicOrtho_of_monic_of_orthogonal h hAmonic hAdeg ?_).symm
  intro q hq
  have hqmem := mem_span_of_degree_lt hdeg hne n q hq
  have hstep : ∀ p : Polynomial ℝ, p ∈ Submodule.span ℝ (f '' {k : ℕ | k < n}) →
      momentInner s A p = 0 := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, hk, rfl⟩ := hx
        rw [hA, momentInner_smul_left, horth n k (Nat.ne_of_gt hk), mul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [momentInner_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [momentInner_smul_right, hx, mul_zero]
  exact hstep q hqmem

/-- The monic norm evaluated through a concrete orthogonal family. -/
theorem monicOrthoNormSq_of_orthogonal_family {s : ℕ → ℝ} (h : PositiveMomentForm s)
    {f : ℕ → Polynomial ℝ} (hdeg : ∀ k, (f k).natDegree = k) (hne : ∀ k, f k ≠ 0)
    (horth : ∀ m n : ℕ, m ≠ n → momentInner s (f m) (f n) = 0) (n : ℕ) :
    monicOrthoNormSq s n =
      (((f n).leadingCoeff)⁻¹) ^ 2 * momentInner s (f n) (f n) := by
  rw [monicOrthoNormSq, monicOrtho_eq_of_orthogonal_family h hdeg hne horth n,
    momentInner_smul_left, momentInner_smul_right]
  ring

end HTGeometry
