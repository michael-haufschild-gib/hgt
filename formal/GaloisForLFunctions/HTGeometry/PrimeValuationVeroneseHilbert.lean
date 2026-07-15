import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseKernel

/-!
# The full valuation--Veronese Hilbert layer

For a finite recurrent point geometry, every homogeneous degree has an exact tail quotient.
This module packages their dimensions as one Hilbert function, proves monotonicity in the presence
of a homogenizing coordinate, and gives a sharp finite-point interpolation bound: from degree
`card R - 1` onward the Hilbert function is exactly the number of recurrent points.

The proof is constructive.  Products of normalized homogeneous linear separators give delta
polynomials on the finite recurrent set, and powers of the homogenizing coordinate raise them to
any later degree without changing their values.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

universe u v

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000

/-- The dimension of the complete degree-`m` homogeneous coordinate space on the recurrent set. -/
def recurrentHomogeneousHilbertFunction
    {P σ : Type*} (x : P → σ → ℂ) (m : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (homogeneousRecurringEvaluation x m))

/-- The dimension of the complete degree-`m` valuation-tail quotient. -/
def valuationTailHilbertFunction
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (m : ℕ) : ℕ :=
  Module.finrank ℂ
    (homogeneousSubmodule σ ℂ m ⧸ homogeneousTailRelationSubmodule x m)

/-- Every degree of the valuation-tail Hilbert function is the corresponding recurrent
homogeneous coordinate rank. -/
theorem valuationTailHilbertFunction_eq_recurrent
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ)
    (hrange : (Set.range x).Finite) (m : ℕ) :
    valuationTailHilbertFunction x m = recurrentHomogeneousHilbertFunction x m :=
  finrank_homogeneousTailQuotient_eq_recurringRange x hrange m

/-- A coordinate separating two distinct points of a finite embedded point family. -/
noncomputable def finitePointSeparatingCoordinate
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a b : V) : σ :=
  if hab : a = b then h₀ else Classical.choose (by
    have hv : v a ≠ v b := hinj.ne hab
    by_contra h
    push_neg at h
    exact hv (funext h))

theorem finitePointSeparatingCoordinate_ne
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    {a b : V} (hab : a ≠ b) :
    v a (finitePointSeparatingCoordinate h₀ v hinj a b) ≠
      v b (finitePointSeparatingCoordinate h₀ v hinj a b) := by
  rw [finitePointSeparatingCoordinate, dif_neg hab]
  exact Classical.choose_spec (by
    have hv : v a ≠ v b := hinj.ne hab
    by_contra h
    push_neg at h
    exact hv (funext h))

/-- The normalized homogeneous linear separator that is one at `a` and zero at `b`. -/
noncomputable def finitePointHomogeneousSeparator
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a b : V) :
    MvPolynomial σ ℂ :=
  let i := finitePointSeparatingCoordinate h₀ v hinj a b
  C ((v a i - v b i)⁻¹) * (X i - C (v b i) * X h₀)

theorem finitePointHomogeneousSeparator_isHomogeneous
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a b : V) :
    IsHomogeneous (finitePointHomogeneousSeparator h₀ v hinj a b) 1 := by
  unfold finitePointHomogeneousSeparator
  exact ((isHomogeneous_X (R := ℂ)
    (finitePointSeparatingCoordinate h₀ v hinj a b)).sub
      (isHomogeneous_C_mul_X
        (v b (finitePointSeparatingCoordinate h₀ v hinj a b)) h₀)).C_mul _

theorem eval_finitePointHomogeneousSeparator_right
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    (hone : ∀ a, v a h₀ = 1) (a b : V) :
    eval (v b) (finitePointHomogeneousSeparator h₀ v hinj a b) = 0 := by
  simp [finitePointHomogeneousSeparator, hone]

theorem eval_finitePointHomogeneousSeparator_left
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    (hone : ∀ a, v a h₀ = 1) {a b : V} (hab : a ≠ b) :
    eval (v a) (finitePointHomogeneousSeparator h₀ v hinj a b) = 1 := by
  have hne := finitePointSeparatingCoordinate_ne h₀ v hinj hab
  have hsub :
      v a (finitePointSeparatingCoordinate h₀ v hinj a b) -
        v b (finitePointSeparatingCoordinate h₀ v hinj a b) ≠ 0 :=
    sub_ne_zero.mpr hne
  simp [finitePointHomogeneousSeparator, hone, hsub]

/-- A homogeneous delta polynomial for one point of a finite embedded family. -/
noncomputable def finitePointHomogeneousDelta
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a : V) :
    MvPolynomial σ ℂ :=
  ∏ b ∈ Finset.univ.erase a, finitePointHomogeneousSeparator h₀ v hinj a b

theorem finitePointHomogeneousDelta_isHomogeneous
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a : V) :
    IsHomogeneous (finitePointHomogeneousDelta h₀ v hinj a)
      (Fintype.card V - 1) := by
  have hhom := IsHomogeneous.prod (Finset.univ.erase a)
    (fun b => finitePointHomogeneousSeparator h₀ v hinj a b) (fun _ => 1)
    (fun b _ => finitePointHomogeneousSeparator_isHomogeneous h₀ v hinj a b)
  simpa [finitePointHomogeneousDelta] using hhom

theorem eval_finitePointHomogeneousDelta_self
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    (hone : ∀ a, v a h₀ = 1) (a : V) :
    eval (v a) (finitePointHomogeneousDelta h₀ v hinj a) = 1 := by
  simp only [finitePointHomogeneousDelta, eval_prod]
  apply Finset.prod_eq_one
  intro b hb
  exact eval_finitePointHomogeneousSeparator_left h₀ v hinj hone
    (Finset.mem_erase.mp hb).1.symm

theorem eval_finitePointHomogeneousDelta_of_ne
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    (hone : ∀ a, v a h₀ = 1) {a b : V} (hba : b ≠ a) :
    eval (v b) (finitePointHomogeneousDelta h₀ v hinj a) = 0 := by
  simp only [finitePointHomogeneousDelta, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩)
  exact eval_finitePointHomogeneousSeparator_right h₀ v hinj hone a b

/-- Homogeneous finite-point interpolation in the sharp uniform degree `card V - 1`. -/
noncomputable def finitePointHomogeneousInterpolate
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (f : V → ℂ) :
    MvPolynomial σ ℂ :=
  ∑ a, C (f a) * finitePointHomogeneousDelta h₀ v hinj a

theorem finitePointHomogeneousInterpolate_isHomogeneous
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (f : V → ℂ) :
    IsHomogeneous (finitePointHomogeneousInterpolate h₀ v hinj f)
      (Fintype.card V - 1) := by
  apply IsHomogeneous.sum Finset.univ
  intro a ha
  exact (finitePointHomogeneousDelta_isHomogeneous h₀ v hinj a).C_mul (f a)

theorem eval_finitePointHomogeneousInterpolate
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    (hone : ∀ a, v a h₀ = 1) (f : V → ℂ) (b : V) :
    eval (v b) (finitePointHomogeneousInterpolate h₀ v hinj f) = f b := by
  simp only [finitePointHomogeneousInterpolate, eval_sum, eval_mul, eval_C]
  rw [Finset.sum_eq_single b]
  · rw [eval_finitePointHomogeneousDelta_self h₀ v hinj hone b, mul_one]
  · intro a ha hab
    rw [eval_finitePointHomogeneousDelta_of_ne h₀ v hinj hone hab.symm, mul_zero]
  · simp

/-- Every function on a finite normalized embedded point family is represented by a homogeneous
polynomial in every degree at least `card V - 1`. -/
theorem exists_homogeneous_eval_eq_of_card_sub_one_le
    {σ V : Type*} [Fintype V] [DecidableEq V]
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    (hone : ∀ a, v a h₀ = 1) (m : ℕ) (hm : Fintype.card V - 1 ≤ m)
    (f : V → ℂ) :
    ∃ Q : homogeneousSubmodule σ ℂ m, ∀ a, eval (v a) Q.1 = f a := by
  let P := finitePointHomogeneousInterpolate h₀ v hinj f
  let Q : MvPolynomial σ ℂ := P * X h₀ ^ (m - (Fintype.card V - 1))
  have hP : IsHomogeneous P (Fintype.card V - 1) :=
    finitePointHomogeneousInterpolate_isHomogeneous h₀ v hinj f
  have hQ : IsHomogeneous Q m := by
    unfold Q
    convert hP.mul (isHomogeneous_X_pow (R := ℂ) h₀ (m - (Fintype.card V - 1))) using 1
    omega
  refine ⟨⟨Q, hQ⟩, fun a => ?_⟩
  simp [Q, P, hone, eval_finitePointHomogeneousInterpolate]

/-- With a recurrent homogenizing coordinate, recurrent evaluation is surjective from degree
`card R - 1` onward. -/
theorem homogeneousRecurringEvaluation_surjective_of_card_sub_one_le
    {P σ : Type*} (x : P → σ → ℂ) (hrange : (Set.range x).Finite)
    (h₀ : σ) (hone : ∀ v : recurringValueSet x, v.1 h₀ = 1)
    (m : ℕ) (hm : (recurringValueSet x).ncard - 1 ≤ m) :
    Function.Surjective (homogeneousRecurringEvaluation x m) := by
  letI : Fintype (recurringValueSet x) :=
    (recurringValueSet_finite_of_range_finite x hrange).fintype
  intro f
  have hcard : Fintype.card (recurringValueSet x) = (recurringValueSet x).ncard :=
    Set.fintypeCard_eq_ncard
  obtain ⟨Q, hQ⟩ := exists_homogeneous_eval_eq_of_card_sub_one_le
    h₀ (fun v : recurringValueSet x => v.1) Subtype.val_injective hone m
    (by simpa [hcard] using hm) f
  refine ⟨Q, ?_⟩
  funext v
  exact hQ v

/-- The complete recurrent Hilbert function is bounded by the number of recurrent points. -/
theorem recurrentHomogeneousHilbertFunction_le_ncard
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ)
    (hrange : (Set.range x).Finite) (m : ℕ) :
    recurrentHomogeneousHilbertFunction x m ≤ (recurringValueSet x).ncard := by
  letI : Fintype (recurringValueSet x) :=
    (recurringValueSet_finite_of_range_finite x hrange).fintype
  rw [recurrentHomogeneousHilbertFunction]
  calc
    Module.finrank ℂ (LinearMap.range (homogeneousRecurringEvaluation x m)) ≤
        Module.finrank ℂ (recurringValueSet x → ℂ) := Submodule.finrank_le _
    _ = Fintype.card (recurringValueSet x) := Module.finrank_pi ℂ
    _ = (recurringValueSet x).ncard := Set.fintypeCard_eq_ncard

/-- Multiplication by a homogenizing coordinate embeds every recurrent evaluation layer into the
next one without changing its values. -/
theorem homogeneousRecurringEvaluation_range_mono
    {P σ : Type*} (x : P → σ → ℂ) (h₀ : σ)
    (hone : ∀ v : recurringValueSet x, v.1 h₀ = 1) (m : ℕ) :
    LinearMap.range (homogeneousRecurringEvaluation x m) ≤
      LinearMap.range (homogeneousRecurringEvaluation x (m + 1)) := by
  intro y hy
  obtain ⟨Q, rfl⟩ := hy
  let R : homogeneousSubmodule σ ℂ (m + 1) :=
    ⟨Q.1 * X h₀, by
      convert Q.2.mul (isHomogeneous_X (R := ℂ) h₀) using 1⟩
  refine ⟨R, ?_⟩
  funext v
  simp [R, hone]

/-- The full recurrent Hilbert function is nondecreasing degree by degree. -/
theorem recurrentHomogeneousHilbertFunction_mono
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (h₀ : σ)
    (hone : ∀ v : recurringValueSet x, v.1 h₀ = 1) (m : ℕ) :
    recurrentHomogeneousHilbertFunction x m ≤
      recurrentHomogeneousHilbertFunction x (m + 1) := by
  exact Submodule.finrank_mono
    (homogeneousRecurringEvaluation_range_mono x h₀ hone m)

/-- **Full finite-point Hilbert stabilization.**  From degree `card R - 1` onward, every function
on the recurrent point set is represented and the Hilbert function equals `card R`. -/
theorem recurrentHomogeneousHilbertFunction_eq_ncard_of_card_sub_one_le
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ)
    (hrange : (Set.range x).Finite) (h₀ : σ)
    (hone : ∀ v : recurringValueSet x, v.1 h₀ = 1)
    (m : ℕ) (hm : (recurringValueSet x).ncard - 1 ≤ m) :
    recurrentHomogeneousHilbertFunction x m = (recurringValueSet x).ncard := by
  letI : Fintype (recurringValueSet x) :=
    (recurringValueSet_finite_of_range_finite x hrange).fintype
  rw [recurrentHomogeneousHilbertFunction,
    LinearMap.range_eq_top.mpr
      (homogeneousRecurringEvaluation_surjective_of_card_sub_one_le
        x hrange h₀ hone m hm), Module.finrank_top, Module.finrank_pi ℂ,
    Set.fintypeCard_eq_ncard]

/-- The valuation-tail Hilbert function has the same sharp stabilization law. -/
theorem valuationTailHilbertFunction_eq_ncard_of_card_sub_one_le
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ)
    (hrange : (Set.range x).Finite) (h₀ : σ)
    (hone : ∀ v : recurringValueSet x, v.1 h₀ = 1)
    (m : ℕ) (hm : (recurringValueSet x).ncard - 1 ≤ m) :
    valuationTailHilbertFunction x m = (recurringValueSet x).ncard := by
  rw [valuationTailHilbertFunction_eq_recurrent x hrange m]
  exact recurrentHomogeneousHilbertFunction_eq_ncard_of_card_sub_one_le
    x hrange h₀ hone m hm

end

end GaloisForLFunctions.HTGeometry
