import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseKernel
import Mathlib.RingTheory.MvPolynomial.Basic

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

/-- A coordinate separating two distinct points of an embedded point family. -/
theorem exists_finitePointSeparatingCoordinate
    {σ V : Type*} (v : V → σ → ℂ) (hinj : Function.Injective v)
    {a b : V} (hab : a ≠ b) : ∃ i, v a i ≠ v b i := by
  by_contra h
  apply hab
  apply hinj
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

noncomputable def finitePointSeparatingCoordinate
    {σ V : Type*}
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a b : V) : σ := by
  classical
  exact if hab : a = b then h₀ else
    Classical.choose (exists_finitePointSeparatingCoordinate v hinj hab)

theorem finitePointSeparatingCoordinate_ne
    {σ V : Type*}
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    {a b : V} (hab : a ≠ b) :
    v a (finitePointSeparatingCoordinate h₀ v hinj a b) ≠
      v b (finitePointSeparatingCoordinate h₀ v hinj a b) := by
  rw [finitePointSeparatingCoordinate, dif_neg hab]
  exact Classical.choose_spec (exists_finitePointSeparatingCoordinate v hinj hab)

/-- The normalized homogeneous linear separator that is one at `a` and zero at `b`. -/
noncomputable def finitePointHomogeneousSeparator
    {σ V : Type*}
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a b : V) :
    MvPolynomial σ ℂ :=
  let i := finitePointSeparatingCoordinate h₀ v hinj a b
  C ((v a i - v b i)⁻¹) * (X i - C (v b i) * X h₀)

theorem finitePointHomogeneousSeparator_isHomogeneous
    {σ V : Type*}
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v) (a b : V) :
    IsHomogeneous (finitePointHomogeneousSeparator h₀ v hinj a b) 1 := by
  unfold finitePointHomogeneousSeparator
  exact ((isHomogeneous_X (R := ℂ)
    (finitePointSeparatingCoordinate h₀ v hinj a b)).sub
      (isHomogeneous_C_mul_X
        (v b (finitePointSeparatingCoordinate h₀ v hinj a b)) h₀)).C_mul _

theorem eval_finitePointHomogeneousSeparator_right
    {σ V : Type*}
    (h₀ : σ) (v : V → σ → ℂ) (hinj : Function.Injective v)
    (hone : ∀ a, v a h₀ = 1) (a b : V) :
    eval (v b) (finitePointHomogeneousSeparator h₀ v hinj a b) = 0 := by
  simp [finitePointHomogeneousSeparator, hone]

theorem eval_finitePointHomogeneousSeparator_left
    {σ V : Type*}
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

/-- Inclusion of all homogeneous vanishing layers forces inclusion of the normalized recurrent
point sets.  A point outside the target set is separated by a homogeneous delta polynomial on its
union with that finite target. -/
theorem recurringValueSet_subset_of_homogeneousVanishingSubmodules_le
    {P Q σ : Type*} (x : P → σ → ℂ) (y : Q → σ → ℂ)
    (hyrange : (Set.range y).Finite) (h₀ : σ)
    (hxone : ∀ v : recurringValueSet x, v.1 h₀ = 1)
    (hyone : ∀ v : recurringValueSet y, v.1 h₀ = 1)
    (hlayers : ∀ m,
      homogeneousRecurringVanishingSubmodule y m ≤
        homogeneousRecurringVanishingSubmodule x m) :
    recurringValueSet x ⊆ recurringValueSet y := by
  classical
  intro v hvx
  by_contra hvy
  let S : Set (σ → ℂ) := Set.insert v (recurringValueSet y)
  have hSfinite : S.Finite :=
    (recurringValueSet_finite_of_range_finite y hyrange).insert v
  letI : Fintype S := hSfinite.fintype
  letI : DecidableEq S := Classical.decEq _
  let f : S → ℂ := fun w => if w.1 = v then 1 else 0
  have hSone : ∀ w : S, w.1 h₀ = 1 := by
    intro w
    rcases w.2 with hw | hw
    · simpa [hw] using hxone ⟨v, hvx⟩
    · exact hyone ⟨w.1, hw⟩
  let m := Fintype.card S - 1
  obtain ⟨R, hR⟩ := exists_homogeneous_eval_eq_of_card_sub_one_le
    h₀ (fun w : S => w.1) Subtype.val_injective hSone m le_rfl f
  let vS : S := ⟨v, Set.mem_insert v (recurringValueSet y)⟩
  have hRv : eval v R.1 = 1 := by
    simpa [vS, f] using hR vS
  have hRy : R ∈ homogeneousRecurringVanishingSubmodule y m := by
    intro w hw
    let wS : S := ⟨w, Set.mem_insert_of_mem v hw⟩
    have hwv : w ≠ v := by
      intro hwv
      apply hvy
      simpa [hwv] using hw
    simpa [wS, f, hwv] using hR wS
  have hRx := hlayers m hRy
  rw [hRx v hvx] at hRv
  exact zero_ne_one hRv

/-- **Homogeneous tomography is injective.**  For finite-range normalized sources, equality of
every homogeneous recurrent vanishing layer is equivalent to equality of the recurrent point
geometry. -/
theorem recurringValueSet_eq_iff_homogeneousVanishingSubmodules_eq
    {P Q σ : Type*} (x : P → σ → ℂ) (y : Q → σ → ℂ)
    (hxrange : (Set.range x).Finite) (hyrange : (Set.range y).Finite) (h₀ : σ)
    (hxone : ∀ v : recurringValueSet x, v.1 h₀ = 1)
    (hyone : ∀ v : recurringValueSet y, v.1 h₀ = 1) :
    recurringValueSet x = recurringValueSet y ↔
      ∀ m, homogeneousRecurringVanishingSubmodule x m =
        homogeneousRecurringVanishingSubmodule y m := by
  constructor
  · intro hxy m
    ext R
    change (∀ v ∈ recurringValueSet x, eval v R.1 = 0) ↔
      ∀ v ∈ recurringValueSet y, eval v R.1 = 0
    rw [hxy]
  · intro hlayers
    apply Set.Subset.antisymm
    · apply recurringValueSet_subset_of_homogeneousVanishingSubmodules_le
        x y hyrange h₀ hxone hyone
      intro m
      rw [hlayers m]
    · apply recurringValueSet_subset_of_homogeneousVanishingSubmodules_le
        y x hxrange h₀ hyone hxone
      intro m
      rw [hlayers m]

/-- With a recurrent homogenizing coordinate, recurrent evaluation is surjective from degree
`card R - 1` onward. -/
theorem homogeneousRecurringEvaluation_surjective_of_card_sub_one_le
    {P σ : Type*} (x : P → σ → ℂ) (hrange : (Set.range x).Finite)
    (h₀ : σ) (hone : ∀ v : recurringValueSet x, v.1 h₀ = 1)
    (m : ℕ) (hm : (recurringValueSet x).ncard - 1 ≤ m) :
    Function.Surjective (homogeneousRecurringEvaluation x m) := by
  letI : Fintype (recurringValueSet x) :=
    (recurringValueSet_finite_of_range_finite x hrange).fintype
  letI : DecidableEq (recurringValueSet x) := Classical.decEq _
  intro f
  have hcard : Fintype.card (recurringValueSet x) = (recurringValueSet x).ncard :=
    Set.fintypeCard_eq_ncard (recurringValueSet x)
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
    _ = (recurringValueSet x).ncard :=
      Set.fintypeCard_eq_ncard (recurringValueSet x)

/-- A fixed homogeneous layer in finitely many variables is finite-dimensional. -/
noncomputable instance finiteDimensional_homogeneousSubmodule
    {σ : Type*} [Fintype σ] (m : ℕ) :
    FiniteDimensional ℂ (homogeneousSubmodule σ ℂ m) := by
  let inclusion :
      homogeneousSubmodule σ ℂ m →ₗ[ℂ] restrictTotalDegree σ ℂ m :=
    { toFun := fun Q =>
        ⟨Q.1, (mem_restrictTotalDegree σ m Q.1).2 Q.2.totalDegree_le⟩
      map_add' := by intro Q R; rfl
      map_smul' := by intro a Q; rfl }
  exact Module.Finite.of_injective inclusion (by
    intro Q R hQR
    apply Subtype.ext
    exact congrArg
      (fun z : restrictTotalDegree σ ℂ m => z.1) hQR)

/-- The complete degree-`m` Hilbert index. -/
abbrev recurrentHilbertIndex
    {P σ : Type*} (x : P → σ → ℂ) (m : ℕ) :=
  Fin (recurrentHomogeneousHilbertFunction x m)

/-- A basis of the complete recurrent evaluation range, indexed by its Hilbert number. -/
noncomputable def recurrentEvaluationBasis
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (m : ℕ) :
    Module.Basis (recurrentHilbertIndex x m) ℂ
      (LinearMap.range (homogeneousRecurringEvaluation x m)) :=
  Module.finBasis ℂ _

/-- A homogeneous polynomial preimage of one recurrent evaluation basis vector. -/
noncomputable def recurrentHilbertPivot
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (m : ℕ)
    (j : recurrentHilbertIndex x m) : homogeneousSubmodule σ ℂ m :=
  Classical.choose (recurrentEvaluationBasis x m j).2

theorem homogeneousRecurringEvaluation_recurrentHilbertPivot
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (m : ℕ)
    (j : recurrentHilbertIndex x m) :
    homogeneousRecurringEvaluation x m (recurrentHilbertPivot x m j) =
      (recurrentEvaluationBasis x m j).1 :=
  Classical.choose_spec (recurrentEvaluationBasis x m j).2

/-- The chosen polynomial lifts of the full Hilbert basis remain independent on the recurrent
point set. -/
theorem recurrentHilbertPivot_linearIndependent
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (m : ℕ) :
    LinearIndependent ℂ (fun j : recurrentHilbertIndex x m =>
      fun v : recurringValueSet x => eval v.1 (recurrentHilbertPivot x m j).1) := by
  have hLI := (recurrentEvaluationBasis x m).linearIndependent.map'
    (LinearMap.range (homogeneousRecurringEvaluation x m)).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  change LinearIndependent ℂ (fun j : recurrentHilbertIndex x m =>
    homogeneousRecurringEvaluation x m (recurrentHilbertPivot x m j))
  simpa only [homogeneousRecurringEvaluation_recurrentHilbertPivot] using! hLI

/-- Coordinates of an arbitrary homogeneous observable in the complete recurrent Hilbert basis. -/
noncomputable def recurrentHilbertCoefficient
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (m : ℕ)
    (Q : homogeneousSubmodule σ ℂ m) (j : recurrentHilbertIndex x m) : ℂ :=
  (recurrentEvaluationBasis x m).repr
    ⟨homogeneousRecurringEvaluation x m Q, ⟨Q, rfl⟩⟩ j

/-- Every homogeneous observable has its exact full-Hilbert coordinate expansion on every
recurrent point. -/
theorem recurrentHilbertPivot_spans
    {P σ : Type*} [Fintype σ] (x : P → σ → ℂ) (m : ℕ)
    (Q : homogeneousSubmodule σ ℂ m) :
    ∀ v : recurringValueSet x,
      eval v.1 Q.1 = ∑ j, recurrentHilbertCoefficient x m Q j *
        eval v.1 (recurrentHilbertPivot x m j).1 := by
  let y : LinearMap.range (homogeneousRecurringEvaluation x m) :=
    ⟨homogeneousRecurringEvaluation x m Q, ⟨Q, rfl⟩⟩
  have hsum := (recurrentEvaluationBasis x m).sum_repr y
  have hsum' := congrArg
    (LinearMap.range (homogeneousRecurringEvaluation x m)).subtype hsum
  simp only [map_sum, map_smul] at hsum'
  intro v
  have hv := congrFun hsum' v
  change (homogeneousRecurringEvaluation x m Q) v =
    ∑ j, recurrentHilbertCoefficient x m Q j *
      (homogeneousRecurringEvaluation x m (recurrentHilbertPivot x m j)) v
  simp_rw [homogeneousRecurringEvaluation_recurrentHilbertPivot]
  simpa only [y, recurrentHilbertCoefficient, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using! hv.symm

/-- Exponent vectors of all monomials in one complete homogeneous degree. -/
def homogeneousMonomialIndex (σ : Type*) (m : ℕ) :=
  {d : σ →₀ ℕ // d.degree = m}

noncomputable instance homogeneousMonomialIndexFintype
    {σ : Type*} [Fintype σ] (m : ℕ) : Fintype (homogeneousMonomialIndex σ m) :=
  ((Finsupp.finite_of_degree_le m).subset (by
    intro d hd
    exact le_of_eq hd)).fintype

noncomputable instance homogeneousMonomialIndexDecidableEq
    {σ : Type*} [Fintype σ] (m : ℕ) : DecidableEq (homogeneousMonomialIndex σ m) :=
  Classical.decEq _

/-- The monomial represented by one complete homogeneous exponent index. -/
def homogeneousMonomial
    {σ : Type*} (m : ℕ) (d : homogeneousMonomialIndex σ m) :
    homogeneousSubmodule σ ℂ m :=
  ⟨monomial d.1 1, isHomogeneous_monomial 1 d.2⟩

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
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact Q.2.mul (isHomogeneous_X (R := ℂ) h₀)⟩
  refine ⟨R, ?_⟩
  funext v
  change eval v.1 (Q.1 * X h₀) = eval v.1 Q.1
  simp [hone v]

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
        x hrange h₀ hone m hm), finrank_top, Module.finrank_pi ℂ,
    Set.fintypeCard_eq_ncard (recurringValueSet x)]

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
