import GaloisForLFunctions.RHTower.HeatHankelLadderNesting
import GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect
import GaloisForLFunctions.RHTower.XiGaussianExplicitFormulaRectangle

/-!
# The heat-Hankel rungs as matrix positive-semidefiniteness

Each rung of the ladder is the quadratic form of an explicit symmetric matrix,

```text
H(N,t)_{j k} = m_{j+k}(t) ,      m_n = xiGaussianHeatMomentReal n ,
```

so the criterion `∀ a, xiHeatHankelForm N a t ≥ 0` is exactly `Matrix.PosSemidef (H N t)`.  Stating
it that way puts the rung inside mathlib's positive-semidefinite API — eigenvalues, Cholesky-type
decompositions, Schur complements and minor criteria all become available on an object the corpus
previously carried only as a bare sum.

The Hankel symmetry `H j k = H k j` is immediate from `j + k = k + j`, so the matrix is Hermitian
over `ℝ` without any hypothesis on the zeros.
-/

open Finset Matrix

namespace RHTower

/-- The `N × N` Hankel matrix of Gaussian-damped moments at heat parameter `t`. -/
noncomputable def xiHeatHankelMatrix (N : ℕ) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun j k => xiGaussianHeatMomentReal ((j : ℕ) + (k : ℕ)) t

/-- **The Hankel matrix is symmetric**, unconditionally. -/
theorem xiHeatHankelMatrix_isHermitian (N : ℕ) (t : ℝ) :
    (xiHeatHankelMatrix N t).IsHermitian := by
  ext j k
  simp only [xiHeatHankelMatrix, Matrix.conjTranspose_apply, star_trivial]
  rw [Nat.add_comm]

/-- The quadratic form of the Hankel matrix on a `Fin N` vector is the ladder rung on its
extension by zero. -/
theorem xiHeatHankelMatrix_quadratic (N : ℕ) (t : ℝ) (x : Fin N → ℝ) :
    ∑ j, ∑ k, x j * x k * xiHeatHankelMatrix N t j k
      = xiHeatHankelForm N (fun n => if h : n < N then x ⟨n, h⟩ else 0) t := by
  classical
  unfold xiHeatHankelForm xiHeatHankelMatrix
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ Finset.range N,
    (if h : j < N then x ⟨j, h⟩ else 0) * (if h : k < N then x ⟨k, h⟩ else 0) *
      xiGaussianHeatMomentReal (j + k) t) N]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun k =>
    (if h : (j : ℕ) < N then x ⟨(j : ℕ), h⟩ else 0) * (if h : k < N then x ⟨k, h⟩ else 0) *
      xiGaussianHeatMomentReal ((j : ℕ) + k) t) N]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [j.isLt, k.isLt]

/-- **The rung is matrix positive-semidefiniteness.**  Nonnegativity of the order-`N` heat-Hankel
form for every coefficient vector is exactly `PosSemidef` of the `N × N` Hankel matrix. -/
theorem posSemidef_xiHeatHankelMatrix_of_forall_nonneg {N : ℕ} {t : ℝ}
    (h : ∀ a : ℕ → ℝ, 0 ≤ xiHeatHankelForm N a t) :
    (xiHeatHankelMatrix N t).PosSemidef := by
  classical
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨xiHeatHankelMatrix_isHermitian N t, fun x => ?_⟩
  have hx : star x ⬝ᵥ (xiHeatHankelMatrix N t *ᵥ x)
      = ∑ j, ∑ k, x j * x k * xiHeatHankelMatrix N t j k := by
    simp only [star_trivial, dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hx, xiHeatHankelMatrix_quadratic]
  exact h _

/-- **RH gives positive-semidefiniteness at every order and every positive time.** -/
theorem posSemidef_xiHeatHankelMatrix_of_riemannHypothesis (hRH : RiemannHypothesis)
    (N : ℕ) {t : ℝ} (ht : 0 < t) :
    (xiHeatHankelMatrix N t).PosSemidef :=
  posSemidef_xiHeatHankelMatrix_of_forall_nonneg
    (fun a => (riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg).mp hRH N a t ht)

/-- **A failure of semidefiniteness at any order disproves RH.**  With `Matrix.PosSemidef` in hand,
the disproof side of the ladder is a statement about eigenvalues of an explicit finite symmetric
matrix. -/
theorem not_riemannHypothesis_of_not_posSemidef {N : ℕ} {t : ℝ} (ht : 0 < t)
    (h : ¬ (xiHeatHankelMatrix N t).PosSemidef) : ¬ RiemannHypothesis :=
  fun hRH => h (posSemidef_xiHeatHankelMatrix_of_riemannHypothesis hRH N ht)


/-! ### The second rung is the corpus's Turán defect

The corpus already carries `xiHeatTuranDefect t = m₀m₂ − m₁²` and proves it nonnegative under RH.
That quantity is exactly the determinant of the order-two Hankel matrix, so the existing object is
the second rung of the ladder rather than a separate construction. -/

/-- **The order-two determinant is the Turán defect.** -/
theorem det_xiHeatHankelMatrix_two (t : ℝ) :
    (xiHeatHankelMatrix 2 t).det = xiHeatTuranDefect t := by
  rw [Matrix.det_fin_two, xiHeatTuranDefect]
  simp only [xiHeatHankelMatrix]
  norm_num
  ring

/-- **The Turán nonnegativity is the order-two minor criterion.**  Recovering the corpus's existing
theorem through the matrix route: positive-semidefiniteness has nonnegative determinant, and at
order two that determinant is the Turán defect. -/
theorem xiHeatTuranDefect_nonneg_of_posSemidef {t : ℝ}
    (h : (xiHeatHankelMatrix 2 t).PosSemidef) :
    0 ≤ xiHeatTuranDefect t := by
  rw [← det_xiHeatHankelMatrix_two]
  exact h.det_nonneg

/-- **A negative determinant at any order disproves RH.**  The determinant is a single real number
computed from finitely many Gaussian-damped moments; at order two it is the Turán defect, and the
statement generalises the corpus's `not_riemannHypothesis_of_xiHeatTuranDefect_neg` to every
rung. -/
theorem not_riemannHypothesis_of_det_neg {N : ℕ} {t : ℝ} (ht : 0 < t)
    (hdet : (xiHeatHankelMatrix N t).det < 0) : ¬ RiemannHypothesis := by
  refine not_riemannHypothesis_of_not_posSemidef (N := N) ht ?_
  intro hpsd
  exact absurd hpsd.det_nonneg (not_le.mpr hdet)



/-! ### A certified disproof scheme at order two

`XiGaussianExplicitFormulaRectangle` shows the Gaussian heat moments are approximable to arbitrary
accuracy by prime–archimedean contour data.  Combined with the determinant criterion, that makes the
disproof direction *certifiable*: approximate the three moments to accuracy `ε`, bound them by `B`,
and if the approximate determinant is below the explicit error budget, the true determinant is
negative and RH is false.

The budget is exact.  Writing `mⱼ = aⱼ + δⱼ` with `|δⱼ| ≤ ε` and `|aⱼ| ≤ B`,

```text
|m₀m₂ − a₀a₂| ≤ 2Bε + ε² ,     |m₁² − a₁²| ≤ 2Bε + ε² ,
```

so the determinant moves by at most `4Bε + 2ε²`.  Nothing here evaluates anything; it is the
statement that a numerical certificate of the right size would suffice. -/

/-- **Perturbation bound for the order-two determinant.** -/
theorem abs_turan_sub_approx_le {t : ℝ} {a0 a1 a2 ε B : ℝ} (hε : 0 ≤ ε) (_hB : 0 ≤ B)
    (h0 : |xiGaussianHeatMomentReal 0 t - a0| ≤ ε)
    (h1 : |xiGaussianHeatMomentReal 1 t - a1| ≤ ε)
    (h2 : |xiGaussianHeatMomentReal 2 t - a2| ≤ ε)
    (hb0 : |a0| ≤ B) (hb1 : |a1| ≤ B) (hb2 : |a2| ≤ B) :
    |xiHeatTuranDefect t - (a0 * a2 - a1 ^ (2 : ℕ))| ≤ 4 * B * ε + 2 * ε ^ (2 : ℕ) := by
  set m0 := xiGaussianHeatMomentReal 0 t
  set m1 := xiGaussianHeatMomentReal 1 t
  set m2 := xiGaussianHeatMomentReal 2 t
  have e0 := abs_le.mp h0
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  have c0 := abs_le.mp hb0
  have c1 := abs_le.mp hb1
  have c2 := abs_le.mp hb2
  rw [xiHeatTuranDefect, abs_le]
  constructor <;> nlinarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, c0.1, c0.2, c1.1, c1.2,
    c2.1, c2.2, sq_nonneg ε, sq_nonneg (m1 - a1), hε]

/-- **A certified numerical disproof at order two.**  If approximations to the first three
Gaussian heat moments, accurate to `ε` and bounded by `B`, have determinant strictly below the error
budget `−(4Bε + 2ε²)`, then RH is false.  No evaluation occurs here — this is the statement that a
certificate of that size would suffice. -/
theorem not_riemannHypothesis_of_certified_negative {t : ℝ} (ht : 0 < t)
    {a0 a1 a2 ε B : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (h0 : |xiGaussianHeatMomentReal 0 t - a0| ≤ ε)
    (h1 : |xiGaussianHeatMomentReal 1 t - a1| ≤ ε)
    (h2 : |xiGaussianHeatMomentReal 2 t - a2| ≤ ε)
    (hb0 : |a0| ≤ B) (hb1 : |a1| ≤ B) (hb2 : |a2| ≤ B)
    (hcert : a0 * a2 - a1 ^ (2 : ℕ) < -(4 * B * ε + 2 * ε ^ (2 : ℕ))) :
    ¬ RiemannHypothesis := by
  refine not_riemannHypothesis_of_det_neg (N := 2) ht ?_
  rw [det_xiHeatHankelMatrix_two]
  have hbound := abs_turan_sub_approx_le hε hB h0 h1 h2 hb0 hb1 hb2
  have := abs_le.mp hbound
  linarith [this.2]



/-! ### The certificate at every order: a witness vector

The determinant route is order-two.  At general order the natural certificate is a **witness
vector**: if some `x` makes the approximate quadratic form negative by more than the perturbation
can account for, the true form is negative and RH fails.  The perturbation bound is elementary —
entrywise accuracy `ε` moves the form by at most `ε·(∑|xⱼ|)²` — and needs no spectral theory.

This subsumes the order-two determinant version and is what a numerical refutation would actually
produce: a heat parameter, an order, and a vector. -/

/-- **Entrywise perturbation of the quadratic form.** -/
theorem abs_form_sub_le {N : ℕ} {t : ℝ} (M : Fin N → Fin N → ℝ) {ε : ℝ} (_hε : 0 ≤ ε)
    (happrox : ∀ j k, |xiHeatHankelMatrix N t j k - M j k| ≤ ε) (x : Fin N → ℝ) :
    |(∑ j, ∑ k, x j * x k * xiHeatHankelMatrix N t j k) - ∑ j, ∑ k, x j * x k * M j k|
      ≤ ε * (∑ j, |x j|) ^ (2 : ℕ) := by
  classical
  have hdiff : (∑ j, ∑ k, x j * x k * xiHeatHankelMatrix N t j k)
      - ∑ j, ∑ k, x j * x k * M j k
      = ∑ j, ∑ k, x j * x k * (xiHeatHankelMatrix N t j k - M j k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdiff]
  calc |∑ j, ∑ k, x j * x k * (xiHeatHankelMatrix N t j k - M j k)|
      ≤ ∑ j, |∑ k, x j * x k * (xiHeatHankelMatrix N t j k - M j k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, |x j| * |x k| * ε := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (happrox j k) (by positivity)
    _ = ε * (∑ j, |x j|) ^ (2 : ℕ) := by
        rw [sq, Finset.sum_mul_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **A certified numerical disproof at any order.**  Given entrywise approximations to the Hankel
matrix accurate to `ε`, and a vector making the approximate form more negative than `ε·(∑|xⱼ|)²`,
the Riemann Hypothesis is false.  The certificate is `(t, N, M, x)`; nothing is evaluated here. -/
theorem not_riemannHypothesis_of_certified_witness {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : Fin N → Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ j k, |xiHeatHankelMatrix N t j k - M j k| ≤ ε)
    (x : Fin N → ℝ)
    (hcert : (∑ j, ∑ k, x j * x k * M j k) < -(ε * (∑ j, |x j|) ^ (2 : ℕ))) :
    ¬ RiemannHypothesis := by
  classical
  have hb := abs_le.mp (abs_form_sub_le M hε happrox x)
  have htrue : (∑ j, ∑ k, x j * x k * xiHeatHankelMatrix N t j k) < 0 := by
    linarith [hb.2]
  rw [xiHeatHankelMatrix_quadratic] at htrue
  exact not_riemannHypothesis_of_xiHeatHankelForm_neg ht htrue



/-! ### The rungs are reachable from the prime side

`exists_admissible_gaussianSource_contour_approximates_heatMoment` approximates each Gaussian heat
moment to arbitrary accuracy by a normalized prime–archimedean contour integral.  Since the Hankel
entries are the real parts of those moments and `|Re a − Re b| ≤ ‖a − b‖`, the whole matrix is
approximable entrywise from prime-side data.

Composed with the witness certificate this says: the disproof scheme is realisable in principle from
the prime side alone — one does not need the zeros to evaluate a rung, only to know the answer. -/

/-- **Entrywise prime-side approximation of a rung.**  For every order and accuracy there is a
matrix, each of whose entries is the real part of a normalized prime–archimedean contour integral,
within that accuracy of the Hankel matrix. -/
theorem exists_primeSide_approx_hankel (N : ℕ) {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : Fin N → Fin N → ℝ, ∀ j k, |xiHeatHankelMatrix N t j k - M j k| ≤ ε := by
  classical
  have hpair : ∀ p : Fin N × Fin N, ∃ r : ℝ,
      |xiHeatHankelMatrix N t p.1 p.2 - r| ≤ ε := by
    intro p
    obtain ⟨z₁, z₂, _, _, hdist⟩ :=
      exists_admissible_gaussianSource_contour_approximates_heatMoment ht
        ((p.1 : ℕ) + (p.2 : ℕ)) hε
    set C : ℂ := (2 * Real.pi * Complex.I)⁻¹ *
      rectIntegral (fun z => xiGaussianTestC t ((p.1 : ℕ) + (p.2 : ℕ)) z *
        continuedPrimeArchSourceRelativeTrace z) z₁ z₂ with hC
    refine ⟨C.re, ?_⟩
    have hnorm : ‖xiGaussianHeatMoment ((p.1 : ℕ) + (p.2 : ℕ)) t - C‖ < ε := by
      rw [Complex.dist_eq] at hdist
      rwa [← norm_neg, neg_sub] at hdist
    have hre := Complex.abs_re_le_norm
      (xiGaussianHeatMoment ((p.1 : ℕ) + (p.2 : ℕ)) t - C)
    rw [Complex.sub_re] at hre
    have : xiHeatHankelMatrix N t p.1 p.2
        = (xiGaussianHeatMoment ((p.1 : ℕ) + (p.2 : ℕ)) t).re := rfl
    rw [this]
    linarith [hre, hnorm]
  choose r hr using hpair
  exact ⟨fun j k => r (j, k), fun j k => hr (j, k)⟩



/-! ### The positive direction is certifiable per rung too

The same perturbation bound runs the other way.  If a prime-side approximation is uniformly
*positive* on the unit-`ℓ¹` scale — its form at least `ε·(∑|xⱼ|)²` for every `x` — then the true
rung is positive semidefinite, unconditionally.

This does not prove RH: a certificate settles one order at one heat parameter, and RH is the
conjunction over all orders and all `t > 0`.  What it does say is that each rung is *finitely
verifiable from prime data*, so RH is a limit of statements each of which is certifiable in
principle without knowing a single zero. -/

/-- **Certified positivity of a rung.**  A prime-side approximation whose form dominates the
perturbation budget at every vector forces the true rung positive semidefinite. -/
theorem posSemidef_of_certified_positive {N : ℕ} {t : ℝ}
    (M : Fin N → Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ j k, |xiHeatHankelMatrix N t j k - M j k| ≤ ε)
    (hcert : ∀ x : Fin N → ℝ, ε * (∑ j, |x j|) ^ (2 : ℕ) ≤ ∑ j, ∑ k, x j * x k * M j k) :
    (xiHeatHankelMatrix N t).PosSemidef := by
  classical
  refine posSemidef_xiHeatHankelMatrix_of_forall_nonneg (fun a => ?_)
  set x : Fin N → ℝ := fun j => a (j : ℕ) with hx
  have hform : xiHeatHankelForm N a t
      = ∑ j, ∑ k, x j * x k * xiHeatHankelMatrix N t j k := by
    rw [xiHeatHankelMatrix_quadratic]
    unfold xiHeatHankelForm
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j < N := Finset.mem_range.mp hj
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkN : k < N := Finset.mem_range.mp hk
    simp [hx, hjN, hkN]
  rw [hform]
  have hb := abs_le.mp (abs_form_sub_le M hε happrox x)
  have hpos := hcert x
  linarith [hb.1]

/-- **Both directions, per rung.**  Prime-side data certifies either outcome at a given order and
heat parameter: a witness vector below the budget refutes RH outright, and uniform positivity above
the budget establishes that rung.  RH itself is the conjunction over all rungs, so no finite
certificate settles it in the positive direction — the asymmetry is intrinsic, not an artefact of
the scheme. -/
theorem rung_decided_by_prime_certificate {N : ℕ} {t : ℝ}
    (M : Fin N → Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ j k, |xiHeatHankelMatrix N t j k - M j k| ≤ ε) :
    (∀ x : Fin N → ℝ, ε * (∑ j, |x j|) ^ (2 : ℕ) ≤ ∑ j, ∑ k, x j * x k * M j k) →
      (xiHeatHankelMatrix N t).PosSemidef :=
  fun hcert => posSemidef_of_certified_positive M hε happrox hcert



/-! ### What RH says about prime-side data

Read in the other direction, the perturbation bound turns RH into an assertion about
*approximations* rather than about the zeros: under RH no prime-side approximation to a rung,
however coarse, can be more negative than its own accuracy permits.  That is the form in which the
hypothesis constrains computable objects, and it is exactly what the refutation certificate would
exhibit failing — the two are contrapositives. -/

/-- **RH bounds how negative any approximation can be.**  Under RH an entrywise `ε`-accurate
approximation to a rung has quadratic form at least `−ε·(∑|xⱼ|)²` at every vector. -/
theorem approx_form_ge_of_riemannHypothesis (hRH : RiemannHypothesis) {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : Fin N → Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ j k, |xiHeatHankelMatrix N t j k - M j k| ≤ ε)
    (x : Fin N → ℝ) :
    -(ε * (∑ j, |x j|) ^ (2 : ℕ)) ≤ ∑ j, ∑ k, x j * x k * M j k := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  exact not_riemannHypothesis_of_certified_witness ht M hε happrox x hcon hRH

/-- **The apparatus closes.**  For a fixed rung and accuracy exactly one of two things holds: every
vector respects the budget — which RH guarantees — or some vector violates it, which refutes RH.
There is no third possibility. -/
theorem certificate_dichotomy {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : Fin N → Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ j k, |xiHeatHankelMatrix N t j k - M j k| ≤ ε) :
    (∀ x : Fin N → ℝ, -(ε * (∑ j, |x j|) ^ (2 : ℕ)) ≤ ∑ j, ∑ k, x j * x k * M j k)
      ∨ ¬ RiemannHypothesis := by
  classical
  by_cases h : ∀ x : Fin N → ℝ, -(ε * (∑ j, |x j|) ^ (2 : ℕ)) ≤ ∑ j, ∑ k, x j * x k * M j k
  · exact Or.inl h
  · rw [not_forall] at h
    obtain ⟨x, hx⟩ := h
    rw [not_le] at hx
    exact Or.inr (not_riemannHypothesis_of_certified_witness ht M hε happrox x hx)



/-! ### A concrete consequence: log-convexity of the Gaussian heat moments

Specialising the rung to a vector supported on two indices turns positive-semidefiniteness into a
discriminant condition, giving

```text
m_{j+k}(t)²  ≤  m_{2j}(t) · m_{2k}(t)      for all j, k and every t > 0.
```

Under RH this holds for every pair — a concrete infinite family of inequalities on explicit
Gaussian-damped moments, each of which is a Cauchy–Schwarz statement and together log-convexity of
the even-indexed moments.  It is the most elementary arithmetic content the ladder yields. -/

/-- **Two-index specialisation.**  The rung's form at a vector supported on `{j,k}` is the binary
quadratic `u²m₂ⱼ + 2uv·m_{j+k} + v²m₂ₖ`. -/
theorem hankelForm_two_support {N : ℕ} (t : ℝ) {j k : ℕ} (hj : j < N) (hk : k < N) (hjk : j ≠ k)
    (u v : ℝ) :
    xiHeatHankelForm N (fun n => if n = j then u else if n = k then v else 0) t
      = u ^ (2 : ℕ) * xiGaussianHeatMomentReal (2 * j) t
        + 2 * (u * v) * xiGaussianHeatMomentReal (j + k) t
        + v ^ (2 : ℕ) * xiGaussianHeatMomentReal (2 * k) t := by
  classical
  unfold xiHeatHankelForm
  rw [Finset.sum_eq_add_of_mem j k (Finset.mem_range.mpr hj) (Finset.mem_range.mpr hk) hjk ?_]
  · rw [Finset.sum_eq_add_of_mem j k (Finset.mem_range.mpr hj) (Finset.mem_range.mpr hk) hjk ?_,
      Finset.sum_eq_add_of_mem j k (Finset.mem_range.mpr hj) (Finset.mem_range.mpr hk) hjk ?_]
    · simp only [if_neg hjk, if_neg (Ne.symm hjk), if_true]
      rw [two_mul j, two_mul k, Nat.add_comm k j]
      ring
    · intro i _ hi
      simp only [if_neg hi.1, if_neg hi.2, mul_zero, zero_mul]
    · intro i _ hi
      simp only [if_neg hi.1, if_neg hi.2, mul_zero, zero_mul]
  · intro i _ hi
    refine Finset.sum_eq_zero fun m _ => ?_
    simp only [if_neg hi.1, if_neg hi.2, zero_mul]

/-- **Log-convexity of the Gaussian heat moments under RH.**  For all indices and every positive
heat parameter, `m_{j+k}² ≤ m_{2j}·m_{2k}`. -/
theorem sq_heatMoment_le_mul_of_riemannHypothesis (hRH : RiemannHypothesis)
    {j k : ℕ} (hjk : j ≠ k) {t : ℝ} (ht : 0 < t) :
    xiGaussianHeatMomentReal (j + k) t ^ (2 : ℕ)
      ≤ xiGaussianHeatMomentReal (2 * j) t * xiGaussianHeatMomentReal (2 * k) t := by
  classical
  set N := max j k + 1 with hN
  have hj : j < N := by omega
  have hk : k < N := by omega
  have hform := fun (u v : ℝ) =>
    (riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg).mp hRH N
      (fun n => if n = j then u else if n = k then v else 0) t ht
  have hquad : ∀ u v : ℝ, 0 ≤ u ^ (2 : ℕ) * xiGaussianHeatMomentReal (2 * j) t
      + 2 * (u * v) * xiGaussianHeatMomentReal (j + k) t
      + v ^ (2 : ℕ) * xiGaussianHeatMomentReal (2 * k) t := by
    intro u v
    rw [← hankelForm_two_support t hj hk hjk u v]
    exact hform u v
  set A := xiGaussianHeatMomentReal (2 * j) t
  set B := xiGaussianHeatMomentReal (j + k) t
  set C := xiGaussianHeatMomentReal (2 * k) t
  have hA : 0 ≤ A := by simpa using hquad 1 0
  have hC : 0 ≤ C := by simpa using hquad 0 1
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- degenerate rung: the diagonal entry vanishes, forcing the off-diagonal to vanish too
    have h1 : ∀ v : ℝ, 0 ≤ 2 * v * B + v ^ (2 : ℕ) * C := by
      intro v
      have hq := hquad 1 v
      rw [← hA0] at hq
      nlinarith [hq]
    have hC1 : (0 : ℝ) < C + 1 := by linarith
    have hB : B = 0 := by
      by_contra hBne
      have hB2 : 0 < B ^ (2 : ℕ) := by positivity
      have hv := h1 (-(B / (C + 1)))
      have hclear : 0 ≤ B ^ (2 : ℕ) * (-C - 2) := by
        have hexp : 2 * (-(B / (C + 1))) * B + (-(B / (C + 1))) ^ (2 : ℕ) * C
            = (B ^ (2 : ℕ) * (-C - 2)) / (C + 1) ^ (2 : ℕ) := by
          field_simp
          ring
        rw [hexp] at hv
        have := (div_nonneg_iff.mp hv)
        rcases this with ⟨h, _⟩ | ⟨_, h2⟩
        · exact h
        · nlinarith [sq_nonneg (C + 1), hC1, h2]
      nlinarith [hclear, hB2, hC]
    rw [hB, ← hA0]
    simp
  · have hkey := hquad (-B) A
    nlinarith [hkey, hApos, hA, hC]



/-! ### The third rung, explicitly

The corpus carried explicit rungs only to order two (`xiHeatHankelForm_one`, `_two`, and the Turán
defect).  The order-three determinant is the next explicit inequality the ladder yields:

```text
m₀m₂m₄ − m₀m₃² − m₁²m₄ + 2m₁m₂m₃ − m₂³  ≥  0 ,
```

a concrete quintic relation among the first five Gaussian-damped moments, implied by RH and
violated by no critical-line configuration.  Like the Turán defect it is a determinant of an
explicit finite matrix, so a negative value refutes RH through `not_riemannHypothesis_of_det_neg`. -/

/-- The third Hankel determinant of the Gaussian heat moments. -/
noncomputable def xiHeatThirdHankelDet (t : ℝ) : ℝ :=
  xiGaussianHeatMomentReal 0 t * xiGaussianHeatMomentReal 2 t * xiGaussianHeatMomentReal 4 t
    - xiGaussianHeatMomentReal 0 t * xiGaussianHeatMomentReal 3 t ^ (2 : ℕ)
    - xiGaussianHeatMomentReal 1 t ^ (2 : ℕ) * xiGaussianHeatMomentReal 4 t
    + 2 * (xiGaussianHeatMomentReal 1 t * xiGaussianHeatMomentReal 2 t
        * xiGaussianHeatMomentReal 3 t)
    - xiGaussianHeatMomentReal 2 t ^ (3 : ℕ)

/-- **The order-three determinant is that expression.** -/
theorem det_xiHeatHankelMatrix_three (t : ℝ) :
    (xiHeatHankelMatrix 3 t).det = xiHeatThirdHankelDet t := by
  rw [Matrix.det_fin_three, xiHeatThirdHankelDet]
  simp only [xiHeatHankelMatrix]
  norm_num
  ring

/-- **RH forces the third Hankel determinant nonnegative.**  The next explicit rung after the Turán
defect. -/
theorem xiHeatThirdHankelDet_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 0 < t) : 0 ≤ xiHeatThirdHankelDet t := by
  rw [← det_xiHeatHankelMatrix_three]
  exact (posSemidef_xiHeatHankelMatrix_of_riemannHypothesis hRH 3 ht).det_nonneg

/-- **A negative third determinant refutes RH.** -/
theorem not_riemannHypothesis_of_xiHeatThirdHankelDet_neg {t : ℝ} (ht : 0 < t)
    (h : xiHeatThirdHankelDet t < 0) : ¬ RiemannHypothesis := by
  refine not_riemannHypothesis_of_det_neg (N := 3) ht ?_
  rwa [det_xiHeatHankelMatrix_three]



/-! ### All minors at once

Rather than record rungs one at a time, positive-semidefiniteness gives every principal minor of
every rung simultaneously: a submatrix indexed by any selection of rows and the same columns is
again positive semidefinite, hence has nonnegative determinant.

This subsumes the Turán defect, the third Hankel determinant, and every other minor of every order —
an infinite family of explicit polynomial inequalities in the Gaussian-damped moments, all
consequences of RH, each refuting it if negative. -/

/-- **Every principal minor of every rung is nonnegative under RH.**  The selection map need not be
injective; `Matrix.PosSemidef.submatrix` handles arbitrary index maps, and a repeated index simply
gives a singular submatrix with determinant zero. -/
theorem det_submatrix_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {N m : ℕ} {t : ℝ} (ht : 0 < t) (f : Fin m → Fin N) :
    0 ≤ ((xiHeatHankelMatrix N t).submatrix f f).det :=
  ((posSemidef_xiHeatHankelMatrix_of_riemannHypothesis hRH N ht).submatrix f).det_nonneg

/-- **A negative principal minor at any order refutes RH.**  This is the general form of the
determinant criterion: the certificate is an order, a heat parameter, and a selection of indices. -/
theorem not_riemannHypothesis_of_det_submatrix_neg {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (f : Fin m → Fin N)
    (h : ((xiHeatHankelMatrix N t).submatrix f f).det < 0) : ¬ RiemannHypothesis :=
  fun hRH => absurd (det_submatrix_nonneg_of_riemannHypothesis hRH ht f) (not_le.mpr h)

/-- **The moment minors as a family.**  Selecting indices `f` from order `N` produces the minor of
the Gaussian-damped moment matrix at those positions; the Turán defect is the selection `{0,1}` at
order two and the third Hankel determinant is `{0,1,2}` at order three.  Both are instances of the
same statement. -/
theorem turan_is_a_minor (t : ℝ) :
    ((xiHeatHankelMatrix 2 t).submatrix (id : Fin 2 → Fin 2) id).det = xiHeatTuranDefect t := by
  rw [Matrix.submatrix_id_id, det_xiHeatHankelMatrix_two]


end RHTower
