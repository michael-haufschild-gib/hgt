import GaloisForLFunctions.HTGeometry.KhovanskiiSystem
import GaloisForLFunctions.HTGeometry.TranscendentalBaseExistence
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicDeriv

/-!
# Countable complex exponential algebraic closure

Starting from the prime subfield, repeatedly adjoin every coordinate of every nonsingular
Khovanskii system whose coefficients lie in the preceding field.  The union is a subfield because
the stages are increasing.  Each fixed nonsingular locus is countable and the system space over a
countable coefficient field is countable, so every stage and the final closure are countable.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Multivariate polynomials over countable coefficients and countably many variables form a
countable type. -/
theorem countable_mvPolynomial {R σ : Type} [CommSemiring R]
    [Countable R] [Countable σ] : Countable (MvPolynomial σ R) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  refine MvPolynomial.cardinalMk_le_max.trans ?_
  exact max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl

/-- Evaluating a univariate polynomial embedded in one multivariate coordinate. -/
theorem eval₂_toMvPolynomial {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : σ → S) (i : σ) (p : Polynomial R) :
    MvPolynomial.eval₂ f g (Polynomial.toMvPolynomial i p) =
      Polynomial.eval₂ f (g i) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.toMvPolynomial]

/-- Partial differentiation in the selected coordinate agrees with univariate differentiation. -/
theorem pderiv_toMvPolynomial {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) (p : Polynomial R) :
    MvPolynomial.pderiv i (Polynomial.toMvPolynomial i p) =
      Polynomial.toMvPolynomial i p.derivative := by
  simp [Polynomial.toMvPolynomial]

/-- A univariate embedding has zero partial derivative in every other coordinate. -/
theorem pderiv_toMvPolynomial_of_ne {R σ : Type*}
    [CommSemiring R] [DecidableEq σ] {i j : σ} (h : j ≠ i) (p : Polynomial R) :
    MvPolynomial.pderiv j (Polynomial.toMvPolynomial i p) = 0 := by
  simp [Polynomial.toMvPolynomial, h]

/-- Scalar extension of a Khovanskii system from a complex subfield to `ℂ`. -/
def mapKhovanskiiSystem {n : ℕ} (F : Subfield ℂ)
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) F) :
    Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ :=
  fun i => MvPolynomial.map F.subtype (P i)

/-- All coordinates of nonsingular Khovanskii systems over one coefficient field. -/
def khovanskiiCoordinatesOver (F : Subfield ℂ) : Set ℂ :=
  ⋃ n : ℕ, ⋃ P : Fin n → MvPolynomial (Fin n ⊕ Fin n) F,
    khovanskiiCoordinateSet (mapKhovanskiiSystem F P)

theorem countable_khovanskiiCoordinatesOver (F : Subfield ℂ) [Countable F] :
    (khovanskiiCoordinatesOver F).Countable := by
  have hsystems (n : ℕ) :
      Countable (Fin n → MvPolynomial (Fin n ⊕ Fin n) F) := by
    letI : Countable (MvPolynomial (Fin n ⊕ Fin n) F) := countable_mvPolynomial
    infer_instance
  exact Set.countable_iUnion fun n => by
    letI := hsystems n
    exact Set.countable_iUnion fun P =>
      countable_khovanskiiCoordinateSet (mapKhovanskiiSystem F P)

/-- Finite-stage exponential algebraic closure. -/
def complexEclStage : ℕ → Subfield ℂ
  | 0 => Subfield.closure (∅ : Set ℂ)
  | n + 1 => Subfield.closure
      ((complexEclStage n : Set ℂ) ∪ khovanskiiCoordinatesOver (complexEclStage n))

theorem complexEclStage_le_succ (n : ℕ) :
    complexEclStage n ≤ complexEclStage (n + 1) := by
  intro z hz
  exact Subfield.subset_closure (Or.inl hz)

theorem complexEclStage_mono : Monotone complexEclStage := by
  intro m n hmn
  induction hmn with
  | refl => exact le_rfl
  | @step n _ ih => exact ih.trans (complexEclStage_le_succ n)

theorem countable_complexEclStage : ∀ n : ℕ, Countable (complexEclStage n)
  | 0 => by
      exact GaloisForLFunctions.countable_subfield_closure Set.countable_empty
  | n + 1 => by
      letI : Countable (complexEclStage n) := countable_complexEclStage n
      apply GaloisForLFunctions.countable_subfield_closure
      have hcarrier : ((complexEclStage n : Set ℂ)).Countable :=
        Set.countable_coe_iff.mp (countable_complexEclStage n)
      exact hcarrier.union (countable_khovanskiiCoordinatesOver (complexEclStage n))

/-- The complex exponential algebraic closure of the empty set, realized as the increasing union
of its finite Khovanskii stages. -/
def complexExponentialAlgebraicClosure : Subfield ℂ where
  carrier := ⋃ n : ℕ, (complexEclStage n : Set ℂ)
  zero_mem' := Set.mem_iUnion.mpr ⟨0, (complexEclStage 0).zero_mem⟩
  one_mem' := Set.mem_iUnion.mpr ⟨0, (complexEclStage 0).one_mem⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hyn⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨max m n, ?_⟩
    exact (complexEclStage (max m n)).add_mem
      (complexEclStage_mono (Nat.le_max_left m n) hxm)
      (complexEclStage_mono (Nat.le_max_right m n) hyn)
  neg_mem' := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n, (complexEclStage n).neg_mem hxn⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hyn⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨max m n, ?_⟩
    exact (complexEclStage (max m n)).mul_mem
      (complexEclStage_mono (Nat.le_max_left m n) hxm)
      (complexEclStage_mono (Nat.le_max_right m n) hyn)
  inv_mem' := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n, (complexEclStage n).inv_mem hxn⟩

theorem mem_complexExponentialAlgebraicClosure_iff (z : ℂ) :
    z ∈ complexExponentialAlgebraicClosure ↔ ∃ n, z ∈ complexEclStage n := by
  change z ∈ ⋃ n : ℕ, (complexEclStage n : Set ℂ) ↔ _
  simp only [Set.mem_iUnion]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn⟩

theorem complexEclStage_le_complexExponentialAlgebraicClosure (n : ℕ) :
    complexEclStage n ≤ complexExponentialAlgebraicClosure := by
  intro z hz
  exact Set.mem_iUnion.mpr ⟨n, hz⟩

/-- A nonsingular system over stage `n` contributes all of its coordinates at stage `n+1`. -/
theorem khovanskiiCoordinate_mem_complexEclStage_succ {n r : ℕ}
    (P : Fin r → MvPolynomial (Fin r ⊕ Fin r) (complexEclStage n))
    {z : Fin r → ℂ} (hz : z ∈ khovanskiiLocus
      (mapKhovanskiiSystem (complexEclStage n) P)) (i : Fin r) :
    z i ∈ complexEclStage (n + 1) := by
  apply Subfield.subset_closure
  right
  apply Set.mem_iUnion.mpr
  refine ⟨r, Set.mem_iUnion.mpr ⟨P, ?_⟩⟩
  apply Set.mem_iUnion.mpr
  exact ⟨i, ⟨z, hz, rfl⟩⟩

/-- Every complex number algebraic over `ℚ` enters the first Khovanskii stage. -/
theorem isAlgebraic_mem_complexEclStage_one {z : ℂ} (hz : IsAlgebraic ℚ z) :
    z ∈ complexEclStage 1 := by
  let F := complexEclStage 0
  let q : Polynomial ℚ := minpoly ℚ z
  let qF : Polynomial F := q.map (algebraMap ℚ F)
  let P : Fin 1 → MvPolynomial (Fin 1 ⊕ Fin 1) F := fun _ =>
    Polynomial.toMvPolynomial (Sum.inl (0 : Fin 1)) qF
  let w : Fin 1 → ℂ := fun _ => z
  have hcomp : F.subtype.comp (algebraMap ℚ F) = algebraMap ℚ ℂ := by
    ext r
    simp
  have hzero : exponentialSystemEval (mapKhovanskiiSystem F P) w = 0 := by
    funext i
    fin_cases i
    change MvPolynomial.eval (complexExponentialGraph w)
      (MvPolynomial.map F.subtype (P 0)) = 0
    rw [MvPolynomial.eval_map, show P 0 =
      Polynomial.toMvPolynomial (Sum.inl (0 : Fin 1)) qF by rfl,
      eval₂_toMvPolynomial]
    change Polynomial.eval₂ F.subtype z qF = 0
    rw [show qF = q.map (algebraMap ℚ F) by rfl, Polynomial.eval₂_map, hcomp]
    exact minpoly.aeval ℚ z
  have hderiv : Polynomial.eval₂ (algebraMap ℚ ℂ) z q.derivative ≠ 0 := by
    simpa [Polynomial.aeval_def] using
      (GaloisForLFunctions.aeval_derivative_minpoly_ne_zero hz)
  have hdet : (exponentialJacobian (mapKhovanskiiSystem F P) w).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    change MvPolynomial.eval (complexExponentialGraph w)
          (MvPolynomial.pderiv (Sum.inl (0 : Fin 1))
            (MvPolynomial.map F.subtype (P 0))) +
        Complex.exp (w 0) * MvPolynomial.eval (complexExponentialGraph w)
          (MvPolynomial.pderiv (Sum.inr (0 : Fin 1))
            (MvPolynomial.map F.subtype (P 0))) ≠ 0
    rw [MvPolynomial.pderiv_map, MvPolynomial.pderiv_map,
      show P 0 = Polynomial.toMvPolynomial (Sum.inl (0 : Fin 1)) qF by rfl,
      pderiv_toMvPolynomial]
    have hother : MvPolynomial.pderiv (Sum.inr (0 : Fin 1))
        (Polynomial.toMvPolynomial (Sum.inl (0 : Fin 1)) qF) = 0 :=
      pderiv_toMvPolynomial_of_ne (by simp) qF
    rw [hother,
      map_zero, map_zero, mul_zero, add_zero,
      MvPolynomial.eval_map, eval₂_toMvPolynomial]
    change Polynomial.eval₂ F.subtype z qF.derivative ≠ 0
    rw [show qF = q.map (algebraMap ℚ F) by rfl,
      Polynomial.derivative_map, Polynomial.eval₂_map, hcomp]
    exact hderiv
  have hw : w ∈ khovanskiiLocus (mapKhovanskiiSystem F P) :=
    mem_khovanskiiLocus_of_eval_eq_zero_of_det_ne_zero _ _ hzero hdet
  have hcoord := khovanskiiCoordinate_mem_complexEclStage_succ P hw 0
  simpa [w] using hcoord

/-- Every complex algebraic number belongs to the exponential algebraic closure. -/
theorem isAlgebraic_mem_complexExponentialAlgebraicClosure {z : ℂ}
    (hz : IsAlgebraic ℚ z) : z ∈ complexExponentialAlgebraicClosure :=
  complexEclStage_le_complexExponentialAlgebraicClosure 1
    (isAlgebraic_mem_complexEclStage_one hz)

/-- Exponentiating an element of stage `n` produces an element of stage `n+1`. -/
theorem exp_mem_complexEclStage_succ {n : ℕ} {z : ℂ} (hz : z ∈ complexEclStage n) :
    Complex.exp z ∈ complexEclStage (n + 1) := by
  let F := complexEclStage n
  let c : F := ⟨z, hz⟩
  let P : Fin 2 → MvPolynomial (Fin 2 ⊕ Fin 2) F := fun i =>
    if i = 0 then MvPolynomial.X (Sum.inl (0 : Fin 2)) - MvPolynomial.C c
    else MvPolynomial.X (Sum.inl (1 : Fin 2)) - MvPolynomial.X (Sum.inr (0 : Fin 2))
  let w : Fin 2 → ℂ := fun i => if i = 0 then z else Complex.exp z
  have hzero : exponentialSystemEval (mapKhovanskiiSystem F P) w = 0 := by
    funext i
    fin_cases i <;>
      simp [exponentialSystemEval, exponentialPolynomialEval, mapKhovanskiiSystem,
        P, w, complexExponentialGraph, c]
  have hdet : (exponentialJacobian (mapKhovanskiiSystem F P) w).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [exponentialJacobian, mapKhovanskiiSystem, P, w, c]
  have hw : w ∈ khovanskiiLocus (mapKhovanskiiSystem F P) :=
    mem_khovanskiiLocus_of_eval_eq_zero_of_det_ne_zero _ _ hzero hdet
  have hcoord := khovanskiiCoordinate_mem_complexEclStage_succ P hw 1
  simpa [w] using hcoord

/-- The complex exponential algebraic closure is closed under the complex exponential. -/
theorem exp_mem_complexExponentialAlgebraicClosure {z : ℂ}
    (hz : z ∈ complexExponentialAlgebraicClosure) :
    Complex.exp z ∈ complexExponentialAlgebraicClosure := by
  obtain ⟨n, hn⟩ := (mem_complexExponentialAlgebraicClosure_iff z).mp hz
  exact complexEclStage_le_complexExponentialAlgebraicClosure (n + 1)
    (exp_mem_complexEclStage_succ hn)

/-- The complex exponential algebraic closure of the empty set is countable. -/
theorem countable_complexExponentialAlgebraicClosure :
    Countable complexExponentialAlgebraicClosure := by
  apply Set.countable_coe_iff.mpr
  change (⋃ n : ℕ, (complexEclStage n : Set ℂ)).Countable
  exact Set.countable_iUnion fun n =>
    Set.countable_coe_iff.mp (countable_complexEclStage n)

end

end GaloisForLFunctions.HTGeometry
