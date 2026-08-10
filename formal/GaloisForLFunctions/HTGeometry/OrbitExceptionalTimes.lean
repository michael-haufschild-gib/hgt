import GaloisForLFunctions.HTGeometry.AnalyticImageFiniteness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Exceptional times of a trigonometric orbit are finite

A trigonometric orbit — one whose real coordinates are finite combinations of `cos (λ t)` and
`sin (λ t)` — meets the union of finitely many low-dimensional polynomial images only finitely
often on any compact time interval, as soon as it passes once through a point with algebraically
independent coordinates.

This is the exceptional-time statement of an exact-complexity theorem: the states reachable by a
bounded number of gates form finitely many polynomial images (one per gate-support pattern), each
with fewer parameters than the state has coordinates, so the times at which the orbit is reachable
are finitely many.

No o-minimality and no semialgebraic geometry: `AnalyticImageFiniteness.finite_meets_image` supplies
each piece, and a finite union of finite sets is finite.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-! ## Analyticity of trigonometric orbits -/

theorem analyticOnNhd_cos_mul (lam : ℝ) :
    AnalyticOnNhd ℝ (fun t : ℝ => Real.cos (lam * t)) Set.univ := by
  have hlin : AnalyticOnNhd ℝ (fun t : ℝ => lam * t) Set.univ :=
    analyticOnNhd_const.mul analyticOnNhd_id
  exact Real.analyticOnNhd_cos.comp hlin (fun t _ => Set.mem_univ _)

theorem analyticOnNhd_sin_mul (lam : ℝ) :
    AnalyticOnNhd ℝ (fun t : ℝ => Real.sin (lam * t)) Set.univ := by
  have hlin : AnalyticOnNhd ℝ (fun t : ℝ => lam * t) Set.univ :=
    analyticOnNhd_const.mul analyticOnNhd_id
  exact Real.analyticOnNhd_sin.comp hlin (fun t _ => Set.mem_univ _)

/-- **A trigonometric sum is real-analytic.** -/
theorem analyticOnNhd_trigSum {n : ℕ} (a b lam : Fin n → ℝ) :
    AnalyticOnNhd ℝ
      (fun t : ℝ => ∑ j, (a j * Real.cos (lam j * t) + b j * Real.sin (lam j * t))) Set.univ := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact analyticOnNhd_const
  | insert j s hjs ih =>
      simp only [Finset.sum_insert hjs]
      refine AnalyticOnNhd.add ?_ ih
      exact (analyticOnNhd_const.mul (analyticOnNhd_cos_mul (lam j))).add
        (analyticOnNhd_const.mul (analyticOnNhd_sin_mul (lam j)))

/-! ## Finitely many parametrisations -/

/-- **A real-analytic curve through an algebraically independent point meets a finite union of
lower-dimensional polynomial images only finitely often.** -/
theorem finite_meets_iUnion_images {ι : Type*} {r : ℕ} (Ps : Finset ι) (m : ι → ℕ)
    (hm : ∀ p ∈ Ps, m p < r) (Φ : ∀ p : ι, Fin r → MvPolynomial (Fin (m p)) ℚ)
    (γ : Fin r → ℝ → ℝ) (hγ : ∀ i, AnalyticOnNhd ℝ (γ i) Set.univ)
    {t₀ : ℝ} (hP : AlgebraicIndependent ℚ (fun i => γ i t₀))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ p ∈ Ps, ∃ u : Fin (m p) → ℝ,
      ∀ i, γ i t = MvPolynomial.aeval u (Φ p i)}.Finite := by
  classical
  have hsub : {t ∈ S | ∃ p ∈ Ps, ∃ u : Fin (m p) → ℝ,
        ∀ i, γ i t = MvPolynomial.aeval u (Φ p i)}
      ⊆ ⋃ p ∈ Ps, {t ∈ S | ∃ u : Fin (m p) → ℝ,
        ∀ i, γ i t = MvPolynomial.aeval u (Φ p i)} := by
    rintro t ⟨htS, p, hp, u, hu⟩
    exact Set.mem_biUnion hp ⟨htS, u, hu⟩
  refine Set.Finite.subset (Set.Finite.biUnion Ps.finite_toSet fun p hp => ?_) hsub
  exact finite_meets_image (hm p hp) (Φ p) γ hγ hP hS

/-- **The exceptional times of a trigonometric orbit are finite.**  If each coordinate of the orbit
is a finite trigonometric sum, and at one time the coordinates are algebraically independent over
`ℚ`, then on any compact time set the orbit lands in the union of finitely many polynomial images
with fewer parameters than coordinates only finitely often. -/
theorem finite_exceptional_times {ι : Type*} {r n : ℕ} (Ps : Finset ι) (m : ι → ℕ)
    (hm : ∀ p ∈ Ps, m p < r) (Φ : ∀ p : ι, Fin r → MvPolynomial (Fin (m p)) ℚ)
    (a b : Fin r → Fin n → ℝ) (lam : Fin n → ℝ)
    {t₀ : ℝ}
    (hP : AlgebraicIndependent ℚ
      (fun i : Fin r => ∑ j, (a i j * Real.cos (lam j * t₀) + b i j * Real.sin (lam j * t₀))))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ p ∈ Ps, ∃ u : Fin (m p) → ℝ, ∀ i : Fin r,
      (∑ j, (a i j * Real.cos (lam j * t) + b i j * Real.sin (lam j * t)))
        = MvPolynomial.aeval u (Φ p i)}.Finite :=
  finite_meets_iUnion_images Ps m hm Φ
    (fun i t => ∑ j, (a i j * Real.cos (lam j * t) + b i j * Real.sin (lam j * t)))
    (fun i => analyticOnNhd_trigSum (a i) (b i) lam) hP hS

/-- **Subfamily version of the finite-union statement.** -/
theorem finite_meets_iUnion_images_subfamily {ι : Type*} {r k : ℕ} (Ps : Finset ι) (m : ι → ℕ)
    (hm : ∀ p ∈ Ps, m p < k) (σ : Fin k → Fin r)
    (Φ : ∀ p : ι, Fin r → MvPolynomial (Fin (m p)) ℚ)
    (γ : Fin r → ℝ → ℝ) (hγ : ∀ i, AnalyticOnNhd ℝ (γ i) Set.univ)
    {t₀ : ℝ} (hP : AlgebraicIndependent ℚ (fun i => γ (σ i) t₀))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ p ∈ Ps, ∃ u : Fin (m p) → ℝ,
      ∀ i, γ i t = MvPolynomial.aeval u (Φ p i)}.Finite := by
  classical
  have hsub : {t ∈ S | ∃ p ∈ Ps, ∃ u : Fin (m p) → ℝ,
        ∀ i, γ i t = MvPolynomial.aeval u (Φ p i)}
      ⊆ ⋃ p ∈ Ps, {t ∈ S | ∃ u : Fin (m p) → ℝ,
        ∀ i, γ i t = MvPolynomial.aeval u (Φ p i)} := by
    rintro t ⟨htS, p, hp, u, hu⟩
    exact Set.mem_biUnion hp ⟨htS, u, hu⟩
  refine Set.Finite.subset (Set.Finite.biUnion Ps.finite_toSet fun p hp => ?_) hsub
  exact finite_meets_image_subfamily (hm p hp) σ (Φ p) γ hγ hP hS

/-- **The exceptional times of a trigonometric orbit are finite, subfamily version.**  Only `k`
of the coordinates need be algebraically independent at `t₀`, and each parametrisation needs fewer
than `k` parameters. -/
theorem finite_exceptional_times_subfamily {ι : Type*} {r k n : ℕ} (Ps : Finset ι) (m : ι → ℕ)
    (hm : ∀ p ∈ Ps, m p < k) (σ : Fin k → Fin r)
    (Φ : ∀ p : ι, Fin r → MvPolynomial (Fin (m p)) ℚ)
    (a b : Fin r → Fin n → ℝ) (lam : Fin n → ℝ) {t₀ : ℝ}
    (hP : AlgebraicIndependent ℚ (fun i : Fin k =>
      ∑ j, (a (σ i) j * Real.cos (lam j * t₀) + b (σ i) j * Real.sin (lam j * t₀))))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ p ∈ Ps, ∃ u : Fin (m p) → ℝ, ∀ i : Fin r,
      (∑ j, (a i j * Real.cos (lam j * t) + b i j * Real.sin (lam j * t)))
        = MvPolynomial.aeval u (Φ p i)}.Finite :=
  finite_meets_iUnion_images_subfamily Ps m hm σ Φ
    (fun i t => ∑ j, (a i j * Real.cos (lam j * t) + b i j * Real.sin (lam j * t)))
    (fun i => analyticOnNhd_trigSum (a i) (b i) lam) hP hS

end GaloisForLFunctions.HTGeometry
