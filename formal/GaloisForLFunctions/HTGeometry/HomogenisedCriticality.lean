/-
# The homogeneous form of the criticality expression

The criticality expression uses the unit-sphere form of the tangential condition, so its two terms
have total degrees differing by two.  Multiplying the gradient term by the norm-square polynomial
-- which is identically one on the shell -- makes the degrees agree without changing anything on
the shell.

Main results:
* `normSqPoly`, `eval_normSqPoly` — the norm-square polynomial.
* `criticalityPolyHom`, `criticalitySquareSumHom` — the homogeneous forms.
* `eval_map_criticalitySquareSumHom_eq_zero_of_forall` — **they still vanish at a critical point of
  the shell**.
* `exists_criticalLocusShellPolyHom` — **the critical-locus shell polynomial, homogeneous form**.
-/
import GaloisForLFunctions.HTGeometry.CriticalLocusShellPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The norm-square polynomial of the coordinates. -/
def normSqPoly (N : ℕ) : MvPolynomial (Fin N) ℝ := ∑ a, MvPolynomial.X a ^ 2

theorem eval_normSqPoly (θ : Fin N → ℝ) :
    MvPolynomial.eval θ (normSqPoly N) = ∑ a, (θ a) ^ 2 := by
  rw [normSqPoly, map_sum]
  exact Finset.sum_congr rfl fun a _ => by simp

/-- The homogeneous form of the criticality expression in one coordinate direction. -/
def criticalityPolyHom (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (i : Fin N) :
    Polynomial (MvPolynomial (Fin N) ℝ) :=
  (∑ n ∈ Finset.range m,
      Polynomial.C (MvPolynomial.pderiv i (c n) * normSqPoly N) * Polynomial.X ^ n)
    + (∑ n ∈ Finset.range m,
        Polynomial.C ((n : MvPolynomial (Fin N) ℝ) * c n) * Polynomial.X ^ (n - 1))
      * (Polynomial.X * Polynomial.C (MvPolynomial.X i))

/-- The sum over all coordinate directions of the squared homogeneous criticality expressions. -/
def criticalitySquareSumHom (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) :
    Polynomial (MvPolynomial (Fin N) ℝ) :=
  ∑ i : Fin N, (criticalityPolyHom m c i) ^ 2

theorem eval_map_criticalityPolyHom (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (i : Fin N)
    (θ : Fin N → ℝ) (y : ℝ) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalityPolyHom m c i))
      = (∑ n ∈ Finset.range m,
          MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * (∑ a, (θ a) ^ 2) * y ^ n)
        + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ (c n) * y ^ (n - 1))
          * (y * θ i) := by
  rw [criticalityPolyHom, ← Polynomial.coe_mapRingHom]
  simp only [map_add, map_mul, map_sum, map_pow, Polynomial.coe_mapRingHom, Polynomial.map_C,
    Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, MvPolynomial.eval_X, map_natCast,
    Polynomial.eval_natCast, eval_normSqPoly]

theorem eval_map_criticalitySquareSumHom (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (θ : Fin N → ℝ) (y : ℝ) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalitySquareSumHom m c))
      = ∑ i : Fin N,
        (Polynomial.eval y
          (Polynomial.map (MvPolynomial.eval θ) (criticalityPolyHom m c i))) ^ 2 := by
  rw [criticalitySquareSumHom, ← Polynomial.coe_mapRingHom]
  simp only [map_sum, map_pow, Polynomial.coe_mapRingHom, Polynomial.eval_finsetSum,
    Polynomial.eval_pow]

/-- **The homogeneous square sum still vanishes at a critical point of the shell.** -/
theorem eval_map_criticalitySquareSumHom_eq_zero_of_forall (m : ℕ)
    (c : ℕ → MvPolynomial (Fin N) ℝ) {θ : Fin N → ℝ} (hθ : ∑ a, (θ a) ^ 2 = 1) (y : ℝ)
    (h : ∀ i : Fin N,
      (∑ n ∈ Finset.range m, MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * y ^ n)
        + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ (c n) * y ^ (n - 1))
          * (y * θ i) = 0) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalitySquareSumHom m c))
      = 0 := by
  rw [eval_map_criticalitySquareSumHom]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_map_criticalityPolyHom]
  have hone : ∀ n : ℕ,
      MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * (∑ a, (θ a) ^ 2) * y ^ n
        = MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * y ^ n := by
    intro n
    rw [hθ, mul_one]
  rw [Finset.sum_congr rfl (fun n _ => hone n), h i]
  ring

/-- **The critical-locus shell polynomial, homogeneous form.**  It comes with the polynomial
relation of every labelled spectral action, the product formula for its values, and the vanishing
at every critical point of the shell. -/
theorem exists_criticalLocusShellPolyHom {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    ∃ (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (G : MvPolynomial (Fin N) ℝ),
      (∀ (π₀ : Equiv.Perm (Fin D)) (θ : Fin N → ℝ),
        ∑ n ∈ Finset.range m, MvPolynomial.eval θ (c n)
          * (shellSpectralAction hP k π₀ θ) ^ n = 0) ∧
      (∀ θ : Fin N → ℝ, MvPolynomial.eval θ G
        = ∏ π : Equiv.Perm (Fin D),
            Polynomial.eval (shellSpectralAction hP k π θ)
              (Polynomial.map (MvPolynomial.eval θ) (criticalitySquareSumHom m c))) ∧
      (∀ (π₀ : Equiv.Perm (Fin D)) (θ₀ : Fin N → ℝ), (∑ a, (θ₀ a) ^ 2 = 1) →
        (∀ i : Fin N, HasDerivAt (fun t : ℝ =>
            shellSpectralAction hP k π₀ (fun j => θ₀ j + (if j = i then t else 0)))
          (shellSpectralAction hP k π₀ θ₀ * θ₀ i) 0) →
        MvPolynomial.eval θ₀ G = 0) := by
  classical
  obtain ⟨m, c, hrel⟩ := exists_shellRelation_labeledAction hP k
  set Q : Polynomial (MvPolynomial (Fin N) ℝ) := criticalitySquareSumHom m c with hQ
  set kC : Fin D → MvPolynomial (Fin N) ℝ := fun j => MvPolynomial.C (k j) with hkC
  obtain ⟨G, hG⟩ := exists_shellPoly_of_isSymmetric_over hP (actionValueProduct Q kC)
    (isSymmetric_actionValueProduct Q kC)
  have hfac : ∀ (θ : Fin N → ℝ) (π : Equiv.Perm (Fin D)),
      Polynomial.eval₂ (MvPolynomial.eval θ)
          (∑ j, MvPolynomial.eval θ (kC j) *
            (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues (π j)) Q
        = Polynomial.eval (shellSpectralAction hP k π θ)
            (Polynomial.map (MvPolynomial.eval θ) Q) := by
    intro θ π
    rw [Polynomial.eval_map]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hkC, MvPolynomial.eval_C]
  have hvalue : ∀ θ : Fin N → ℝ, MvPolynomial.eval θ G
      = ∏ π : Equiv.Perm (Fin D),
          Polynomial.eval (shellSpectralAction hP k π θ)
            (Polynomial.map (MvPolynomial.eval θ) Q) := by
    intro θ
    rw [← hG θ, eval₂_actionValueProduct]
    exact Finset.prod_congr rfl fun π _ => hfac θ π
  refine ⟨m, c, G, hrel, hvalue, fun π₀ θ₀ hθ₀ hcrit => ?_⟩
  have hcritEq : ∀ i : Fin N,
      (∑ n ∈ Finset.range m, MvPolynomial.eval θ₀ (MvPolynomial.pderiv i (c n))
          * (shellSpectralAction hP k π₀ θ₀) ^ n)
        + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ₀ (c n)
            * (shellSpectralAction hP k π₀ θ₀) ^ (n - 1))
          * (shellSpectralAction hP k π₀ θ₀ * θ₀ i) = 0 :=
    fun i => shell_criticality_relation c (shellSpectralAction hP k π₀) θ₀ i (hrel π₀) (hcrit i)
  have hzero := eval_map_criticalitySquareSumHom_eq_zero_of_forall m c hθ₀
    (shellSpectralAction hP k π₀ θ₀) hcritEq
  rw [hvalue θ₀]
  exact Finset.prod_eq_zero (Finset.mem_univ π₀) hzero

end

end GaloisForLFunctions.HTGeometry
