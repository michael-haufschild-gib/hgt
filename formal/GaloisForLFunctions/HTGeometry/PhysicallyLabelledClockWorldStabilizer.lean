import GaloisForLFunctions.HTGeometry.RelationalHistoryExternalTimeAmbiguityClassification

/-!
# Two physical labels remove finite clock--world mixing

A nondegenerate diagonal observable and one fully connected coupling have
scalar common commutant on every nonempty finite-dimensional world.  Equality
of their Heisenberg derivatives therefore determines an arbitrary generator
up to one scalar energy origin.

After adjoining an arbitrary finite clock factor, the exact common commutant
of the two lifted world observables consists of clock-only operators.  Thus
retaining only these two physical world labels already excludes every
clock--world mixing transformation; the remaining freedom acts on the clock
factor alone.
-/

namespace HTGeometry

noncomputable section

universe u v w

variable {𝕜 : Type u} {world : Type v}
  [Field 𝕜] [Fintype world] [DecidableEq world]

/-- A physically labelled coordinate observable with prescribed distinct
labels. -/
def labelledCoordinateObservable (label : world → 𝕜) :
    Matrix world world 𝕜 :=
  Matrix.diagonal label

/-- One fully connected coupling observable. -/
def completeCouplingObservable : Matrix world world 𝕜 :=
  fun _ _ => 1

/--
Rank-one coupling with a marked nonzero weight on every physical
label.  Positive shell-fusion weights are the intended arithmetic
specialization.
-/
def weightedCompleteCouplingObservable (weight : world → 𝕜) :
    Matrix world world 𝕜 :=
  fun i j => weight i * weight j

/-- Commutation with a nondegenerate coordinate observable kills every
off-diagonal matrix entry. -/
theorem offDiagonal_eq_zero_of_commutes_labelledCoordinate
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Matrix world world 𝕜)
    (hcomm :
      X * labelledCoordinateObservable label =
        labelledCoordinateObservable label * X)
    {i j : world} (hij : i ≠ j) :
    X i j = 0 := by
  have hijEntry := congr_fun (congr_fun hcomm i) j
  simp only [labelledCoordinateObservable, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at hijEntry
  have hne : label j - label i ≠ 0 :=
    sub_ne_zero.mpr (hlabel.ne hij.symm)
  apply (mul_eq_zero.mp ?_).resolve_right hne
  calc
    X i j * (label j - label i) =
        X i j * label j - label i * X i j := by ring
    _ = 0 := sub_eq_zero.mpr hijEntry

/-- Entrywise form used when diagonal labels may repeat between different
clock blocks. -/
theorem matrixEntry_eq_zero_of_commutes_diagonal_of_label_ne
    (label : world → 𝕜) (X : Matrix world world 𝕜)
    (hcomm :
      X * Matrix.diagonal label =
        Matrix.diagonal label * X)
    {i j : world} (hlabel : label i ≠ label j) :
    X i j = 0 := by
  have hijEntry := congr_fun (congr_fun hcomm i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hijEntry
  have hne : label j - label i ≠ 0 :=
    sub_ne_zero.mpr hlabel.symm
  apply (mul_eq_zero.mp ?_).resolve_right hne
  calc
    X i j * (label j - label i) =
        X i j * label j - label i * X i j := by ring
    _ = 0 := sub_eq_zero.mpr hijEntry

/-- **Two-label scalar-commutant law.**  On every nonempty finite world, the
common commutant of one nondegenerate coordinate observable and one fully
connected coupling is exactly the scalar matrices. -/
theorem eq_scalar_of_commutes_two_completeObservables
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Matrix world world 𝕜)
    (hcoordinate :
      X * labelledCoordinateObservable label =
        labelledCoordinateObservable label * X)
    (hcoupling :
      X * completeCouplingObservable =
        completeCouplingObservable * X)
    [Nonempty world] :
    ∃ c : 𝕜, X = Matrix.scalar world c := by
  let anchor : world := Classical.choice inferInstance
  refine ⟨X anchor anchor, Matrix.ext fun i j => ?_⟩
  by_cases hij : i = j
  · subst j
    have hentry := congr_fun (congr_fun hcoupling i) anchor
    simp only [Matrix.mul_apply, completeCouplingObservable,
      mul_one, one_mul] at hentry
    have hdiagSum :
        ∑ x, X i x = X i i := by
      apply Finset.sum_eq_single i
      · intro b _ hbi
        exact offDiagonal_eq_zero_of_commutes_labelledCoordinate
          label hlabel X hcoordinate hbi.symm
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hanchorSum :
        ∑ x, X x anchor = X anchor anchor := by
      apply Finset.sum_eq_single anchor
      · intro b _ hba
        exact offDiagonal_eq_zero_of_commutes_labelledCoordinate
          label hlabel X hcoordinate hba
      · intro ha
        exact (ha (Finset.mem_univ anchor)).elim
    rw [hdiagSum, hanchorSum] at hentry
    simp [Matrix.scalar, hentry]
  · have hzero :=
      offDiagonal_eq_zero_of_commutes_labelledCoordinate
        label hlabel X hcoordinate hij
    simp [Matrix.scalar, hij, hzero]

/--
**Full-support fusion commutant rigidity.**  A simple diagonal label
and one rank-one coupling whose weights are all nonzero have scalar
common commutant.

This weighted form applies to finite positive shell packets: shell
depth gives the simple diagonal label and square-root source mass
gives the full-support coupling vector.
-/
theorem
    eq_scalar_of_commutes_labelledCoordinate_weightedCompleteCoupling
    (label weight : world → 𝕜)
    (hlabel : Function.Injective label)
    (hweight : ∀ i, weight i ≠ 0)
    (X : Matrix world world 𝕜)
    (hcoordinate :
      X * labelledCoordinateObservable label =
        labelledCoordinateObservable label * X)
    (hcoupling :
      X * weightedCompleteCouplingObservable weight =
        weightedCompleteCouplingObservable weight * X)
    [Nonempty world] :
    ∃ c : 𝕜, X = Matrix.scalar world c := by
  let anchor : world := Classical.choice inferInstance
  refine ⟨X anchor anchor, Matrix.ext fun i j => ?_⟩
  by_cases hij : i = j
  · subst j
    have hentry := congr_fun (congr_fun hcoupling i) anchor
    simp only [Matrix.mul_apply, weightedCompleteCouplingObservable] at hentry
    have hleft :
        ∑ x, X i x * (weight x * weight anchor) =
          X i i * (weight i * weight anchor) := by
      apply Finset.sum_eq_single i
      · intro b _ hbi
        rw [offDiagonal_eq_zero_of_commutes_labelledCoordinate
          label hlabel X hcoordinate hbi.symm]
        simp
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hright :
        ∑ x, weight i * weight x * X x anchor =
          weight i * weight anchor * X anchor anchor := by
      apply Finset.sum_eq_single anchor
      · intro b _ hba
        rw [offDiagonal_eq_zero_of_commutes_labelledCoordinate
          label hlabel X hcoordinate hba]
        simp
      · intro ha
        exact (ha (Finset.mem_univ anchor)).elim
    rw [hleft, hright] at hentry
    have hnonzero : weight i * weight anchor ≠ 0 :=
      mul_ne_zero (hweight i) (hweight anchor)
    have hdiag : X i i = X anchor anchor := by
      apply mul_right_cancel₀ hnonzero
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hentry
    simp [Matrix.scalar, hdiag]
  · have hzero :=
      offDiagonal_eq_zero_of_commutes_labelledCoordinate
        label hlabel X hcoordinate hij
    simp [Matrix.scalar, hij, hzero]

/-- **Two physical meanings fix every finite law.**  Agreement of arbitrary
matrix Heisenberg laws on the two explicit labelled observables is equivalent
to a scalar difference of generators. -/
theorem sameLaw_on_two_completeObservables_iff_exists_scalar
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (H K : Matrix world world 𝕜) [Nonempty world] :
    (heisenbergObservableDerivative H
        (labelledCoordinateObservable label) =
      heisenbergObservableDerivative K
        (labelledCoordinateObservable label) ∧
      heisenbergObservableDerivative H
        completeCouplingObservable =
      heisenbergObservableDerivative K
        completeCouplingObservable) ↔
      ∃ c : 𝕜, H - K = Matrix.scalar world c := by
  constructor
  · rintro ⟨hcoordinate, hcoupling⟩
    apply eq_scalar_of_commutes_two_completeObservables
      label hlabel (H - K)
    · simpa [heisenbergObservableDerivative, sub_mul, mul_sub,
        sub_eq_sub_iff_sub_eq_sub] using hcoordinate
    · simpa [heisenbergObservableDerivative, sub_mul, mul_sub,
        sub_eq_sub_iff_sub_eq_sub] using hcoupling
  · rintro ⟨c, hc⟩
    have law_of (X : Matrix world world 𝕜) :
        heisenbergObservableDerivative H X =
          heisenbergObservableDerivative K X := by
      have hcomm :
          (H - K) * X = X * (H - K) := by
        rw [hc]
        exact Matrix.scalar_commute c
          (fun r => Commute.all c r) X
      unfold heisenbergObservableDerivative
      simp only [sub_mul, mul_sub] at hcomm
      exact sub_eq_sub_iff_sub_eq_sub.mpr hcomm
    exact
      ⟨law_of (labelledCoordinateObservable label),
        law_of completeCouplingObservable⟩

section ClockWorld

variable {clock : Type w}
  [Fintype clock] [DecidableEq clock]

/-- World coordinate label lifted identically across all clock sectors. -/
def liftedWorldCoordinateObservable (label : world → 𝕜) :
    Matrix (clock × world) (clock × world) 𝕜 :=
  Matrix.diagonal (fun ci => label ci.2)

/-- World complete coupling lifted identically across all clock sectors. -/
def liftedWorldCompleteCouplingObservable :
    Matrix (clock × world) (clock × world) 𝕜 :=
  fun ci dj => if ci.1 = dj.1 then 1 else 0

/-- An arbitrary clock operator acting identically on every world label. -/
def liftedClockOperator (T : Matrix clock clock 𝕜) :
    Matrix (clock × world) (clock × world) 𝕜 :=
  fun ci dj => if ci.2 = dj.2 then T ci.1 dj.1 else 0

omit [DecidableEq clock] in
/-- Lifting clock operators respects multiplication. -/
theorem liftedClockOperator_mul
    (T U : Matrix clock clock 𝕜) :
    liftedClockOperator (world := world) T *
        liftedClockOperator (world := world) U =
      liftedClockOperator (world := world) (T * U) := by
  ext ai bj
  simp [liftedClockOperator, Matrix.mul_apply,
    Fintype.sum_prod_type]

omit [Fintype world] [Fintype clock] [DecidableEq clock] in
/-- A nonempty world factor makes the clock-operator lift injective. -/
theorem liftedClockOperator_injective [Nonempty world] :
    Function.Injective
      (liftedClockOperator (𝕜 := 𝕜) (clock := clock)
        (world := world)) := by
  intro T U h
  let anchor : world := Classical.choice inferInstance
  ext a b
  have hentry := congr_fun (congr_fun h (a, anchor)) (b, anchor)
  simpa [liftedClockOperator] using hentry

/-- Every clock-only operator commutes with the lifted world coordinate. -/
theorem liftedClockOperator_commutes_worldCoordinate
    (label : world → 𝕜) (T : Matrix clock clock 𝕜) :
    liftedClockOperator (world := world) T *
        liftedWorldCoordinateObservable (clock := clock) label =
      liftedWorldCoordinateObservable (clock := clock) label *
        liftedClockOperator (world := world) T := by
  ext ci dj
  simp only [liftedWorldCoordinateObservable,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    liftedClockOperator]
  by_cases hij : ci.2 = dj.2
  · simp [hij, mul_comm]
  · simp [hij]

/-- Every clock-only operator commutes with the lifted world coupling. -/
theorem liftedClockOperator_commutes_worldCoupling
    (T : Matrix clock clock 𝕜) :
    liftedClockOperator (world := world) T *
        liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world) =
      liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world) *
        liftedClockOperator (world := world) T := by
  ext ci dj
  simp only [Matrix.mul_apply, Fintype.sum_prod_type,
    liftedClockOperator, liftedWorldCompleteCouplingObservable]
  simp

/-- Preserving the two world labels forces an arbitrary total operator to be
clock-only. -/
theorem eq_liftedClockOperator_of_commutes_world_pair
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Matrix (clock × world) (clock × world) 𝕜)
    (hcoordinate :
      X * liftedWorldCoordinateObservable (clock := clock) label =
        liftedWorldCoordinateObservable (clock := clock) label * X)
    (hcoupling :
      X * liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world) =
        liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world) * X)
    [Nonempty world] :
    ∃ T : Matrix clock clock 𝕜,
      X = liftedClockOperator (world := world) T := by
  let anchor : world := Classical.choice inferInstance
  let T : Matrix clock clock 𝕜 :=
    fun a b => X (a, anchor) (b, anchor)
  refine ⟨T, Matrix.ext fun ai bj => ?_⟩
  by_cases hij : ai.2 = bj.2
  · have hentry :=
      congr_fun (congr_fun hcoupling ai)
        (bj.1, anchor)
    simp only [Matrix.mul_apply,
      liftedWorldCompleteCouplingObservable] at hentry
    have hleft :
        ∑ x : clock × world,
          X ai x * (if x.1 = bj.1 then 1 else 0) =
        X ai (bj.1, ai.2) := by
      rw [Fintype.sum_prod_type]
      change
        (∑ c : clock, ∑ k : world,
          X ai (c, k) * (if c = bj.1 then 1 else 0)) =
          X ai (bj.1, ai.2)
      calc
        _ = ∑ k : world, X ai (bj.1, k) := by
          simp only [mul_ite, mul_one, mul_zero,
            Finset.sum_ite_irrel, Finset.sum_const_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
        _ = X ai (bj.1, ai.2) := by
          apply Finset.sum_eq_single ai.2
          · intro k _ hki
            apply matrixEntry_eq_zero_of_commutes_diagonal_of_label_ne
              (fun ci : clock × world => label ci.2) X hcoordinate
            exact hlabel.ne hki.symm
          · intro hi
            exact (hi (Finset.mem_univ ai.2)).elim
    have hright :
        ∑ x : clock × world,
          (if ai.1 = x.1 then 1 else 0) *
            X x (bj.1, anchor) =
        X (ai.1, anchor) (bj.1, anchor) := by
      rw [Fintype.sum_prod_type]
      change
        (∑ c : clock, ∑ k : world,
          (if ai.1 = c then 1 else 0) *
            X (c, k) (bj.1, anchor)) =
          X (ai.1, anchor) (bj.1, anchor)
      calc
        _ = ∑ k : world,
            X (ai.1, k) (bj.1, anchor) := by
          simp only [ite_mul, one_mul, zero_mul,
            Finset.sum_ite_irrel, Finset.sum_const_zero,
            Finset.sum_ite_eq, Finset.mem_univ, if_true]
        _ = X (ai.1, anchor) (bj.1, anchor) := by
          apply Finset.sum_eq_single anchor
          · intro k _ hka
            apply matrixEntry_eq_zero_of_commutes_diagonal_of_label_ne
              (fun ci : clock × world => label ci.2) X hcoordinate
            exact hlabel.ne hka
          · intro ha
            exact (ha (Finset.mem_univ anchor)).elim
    rw [hleft, hright] at hentry
    simpa [liftedClockOperator, T, hij] using hentry
  · have hzero :
        X ai bj = 0 := by
      apply matrixEntry_eq_zero_of_commutes_diagonal_of_label_ne
        (fun ci : clock × world => label ci.2) X hcoordinate
      exact hlabel.ne hij
    simp [liftedClockOperator, hij, hzero]

/-- **Exact finite clock--world stabilizer.**  The common commutant of the
two lifted physical world labels consists exactly of arbitrary clock-only
operators.  Hence no operator mixing clock and world can preserve both
labels. -/
theorem commutes_world_pair_iff_exists_liftedClockOperator
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Matrix (clock × world) (clock × world) 𝕜)
    [Nonempty world] :
    (X * liftedWorldCoordinateObservable (clock := clock) label =
        liftedWorldCoordinateObservable (clock := clock) label * X ∧
      X * liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world) =
        liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world) * X) ↔
      ∃ T : Matrix clock clock 𝕜,
        X = liftedClockOperator (world := world) T := by
  constructor
  · rintro ⟨hcoordinate, hcoupling⟩
    exact eq_liftedClockOperator_of_commutes_world_pair
      label hlabel X hcoordinate hcoupling
  · rintro ⟨T, rfl⟩
    exact
      ⟨liftedClockOperator_commutes_worldCoordinate label T,
        liftedClockOperator_commutes_worldCoupling T⟩

/-- Conjugation by an invertible refactorization preserves a label exactly
when the refactorization commutes with that label. -/
theorem conjugates_eq_self_iff_commutes_of_twoSidedInverse
    (S Sinv O : Matrix (clock × world) (clock × world) 𝕜)
    (hleft : S * Sinv = 1) (hright : Sinv * S = 1) :
    S * O * Sinv = O ↔ S * O = O * S := by
  constructor
  · intro hconjugates
    calc
      S * O = (S * O) * (Sinv * S) := by rw [hright, mul_one]
      _ = (S * O * Sinv) * S := by simp only [mul_assoc]
      _ = O * S := by rw [hconjugates]
  · intro hcommutes
    calc
      S * O * Sinv = O * S * Sinv := by rw [hcommutes]
      _ = O * (S * Sinv) := by simp only [mul_assoc]
      _ = O := by rw [hleft, mul_one]

/-- **Physical finite refactorization classification.**  Every invertible
clock--world refactorization that preserves the two labelled world
observables by conjugation is clock-only, and every clock-only
refactorization preserves them. -/
theorem preserves_world_pair_iff_exists_liftedClockOperator
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (S Sinv : Matrix (clock × world) (clock × world) 𝕜)
    (hleft : S * Sinv = 1) (hright : Sinv * S = 1)
    [Nonempty world] :
    (S * liftedWorldCoordinateObservable (clock := clock) label * Sinv =
        liftedWorldCoordinateObservable (clock := clock) label ∧
      S * liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world) * Sinv =
        liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world)) ↔
      ∃ T : Matrix clock clock 𝕜,
        S = liftedClockOperator (world := world) T := by
  rw [
    conjugates_eq_self_iff_commutes_of_twoSidedInverse
      S Sinv
        (liftedWorldCoordinateObservable (clock := clock) label)
      hleft hright,
    conjugates_eq_self_iff_commutes_of_twoSidedInverse
      S Sinv
        (liftedWorldCompleteCouplingObservable
          (clock := clock) (world := world))
      hleft hright]
  exact commutes_world_pair_iff_exists_liftedClockOperator
    label hlabel S

end ClockWorld

section ClockOrigin

variable {clock : Type w}
  [Group clock] [Fintype clock] [DecidableEq clock]

/-- Projector onto one labelled clock reading. -/
def clockBasisProjector (t : clock) : Matrix clock clock 𝕜 :=
  Matrix.diagonal (fun i => if i = t then 1 else 0)

/-- Left translation of the regular clock basis by one group element. -/
def clockLeftTranslation (g : clock) : Matrix clock clock 𝕜 :=
  fun row column => if row = g * column then 1 else 0

/-- Changing clock origin carries the projector at `t` to the projector at
`g * t`. -/
theorem clockLeftTranslation_projector_intertwines
    (g t : clock) :
    clockLeftTranslation (𝕜 := 𝕜) g * clockBasisProjector t =
      clockBasisProjector (g * t) * clockLeftTranslation g := by
  ext row column
  simp only [clockBasisProjector, Matrix.mul_diagonal,
    Matrix.diagonal_mul, clockLeftTranslation]
  by_cases hcol : column = t
  · subst column
    by_cases hrow : row = g * t <;> simp [hrow]
  · by_cases hrow : row = g * t <;>
      simp [hcol, hrow, Ne.symm hcol]

/-- A clock-origin change conjugates each regular translation by the same
group element. -/
theorem clockLeftTranslation_shift_covariant
    (g h : clock) :
    clockLeftTranslation (𝕜 := 𝕜) g * clockLeftTranslation h =
      clockLeftTranslation (g * h * g⁻¹) * clockLeftTranslation g := by
  ext row column
  simp [clockLeftTranslation, Matrix.mul_apply]
  rw [mul_assoc]

theorem mul_clockLeftTranslation_apply
    (T : Matrix clock clock 𝕜) (h row column : clock) :
    ((T * clockLeftTranslation (𝕜 := 𝕜) h) row column) =
      T row (h * column) := by
  simp only [Matrix.mul_apply, clockLeftTranslation, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem clockLeftTranslation_mul_apply
    (h : clock) (T : Matrix clock clock 𝕜) (row column : clock) :
    ((clockLeftTranslation (𝕜 := 𝕜) h * T) row column) =
      T (h⁻¹ * row) column := by
  simp only [Matrix.mul_apply, clockLeftTranslation, ite_mul,
    one_mul, zero_mul]
  have hiff (x : clock) :
      row = h * x ↔ x = h⁻¹ * row := by
    constructor <;> intro hx
    · calc
        x = h⁻¹ * (h * x) := by group
        _ = h⁻¹ * row := by rw [← hx]
    · calc
        row = h * (h⁻¹ * row) := by group
        _ = h * x := by rw [hx]
  simp_rw [hiff]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Clock-origin rigidity.**  An operator that transports every labelled
clock reading and every regular shift according to one origin change is that
origin change, up to one global scalar. -/
theorem eq_smul_clockLeftTranslation_of_intertwines
    (g : clock) (T : Matrix clock clock 𝕜)
    (hprojector :
      ∀ t : clock,
        T * clockBasisProjector t =
          clockBasisProjector (g * t) * T)
    (hshift :
      ∀ h : clock,
        T * clockLeftTranslation h =
          clockLeftTranslation (g * h * g⁻¹) * T) :
    ∃ c : 𝕜, T = c • clockLeftTranslation g := by
  refine ⟨T g 1, Matrix.ext fun row column => ?_⟩
  by_cases hrow : row = g * column
  · have hentry :=
      congr_fun (congr_fun (hshift column) (g * column)) 1
    rw [mul_clockLeftTranslation_apply (𝕜 := 𝕜),
      clockLeftTranslation_mul_apply (𝕜 := 𝕜)] at hentry
    have hindex :
        (g * column * g⁻¹)⁻¹ * (g * column) = g := by
      group
    rw [mul_one, hindex] at hentry
    subst row
    simpa [clockLeftTranslation] using hentry
  · have hentry :=
      congr_fun (congr_fun (hprojector column) row) column
    simp only [clockBasisProjector, Matrix.mul_diagonal,
      Matrix.diagonal_mul] at hentry
    simp [clockLeftTranslation, hrow] at hentry ⊢
    exact hentry

/-- Exact classification of all finite labelled-clock origin changes. -/
theorem clockOriginStabilizer_iff
    (T : Matrix clock clock 𝕜) :
    (∃ g : clock,
      (∀ t : clock,
        T * clockBasisProjector t =
          clockBasisProjector (g * t) * T) ∧
      (∀ h : clock,
        T * clockLeftTranslation h =
          clockLeftTranslation (g * h * g⁻¹) * T)) ↔
    ∃ g : clock, ∃ c : 𝕜,
      T = c • clockLeftTranslation g := by
  constructor
  · rintro ⟨g, hprojector, hshift⟩
    obtain ⟨c, hc⟩ :=
      eq_smul_clockLeftTranslation_of_intertwines
        g T hprojector hshift
    exact ⟨g, c, hc⟩
  · rintro ⟨g, c, rfl⟩
    refine ⟨g, ?_, ?_⟩
    · intro t
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [clockLeftTranslation_projector_intertwines]
    · intro h
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [clockLeftTranslation_shift_covariant]

/-- An invertible classified clock transformation has nonzero global
scalar. -/
theorem smul_clockLeftTranslation_scalar_ne_zero_of_leftInverse
    (g : clock) (c : 𝕜) (Tinv : Matrix clock clock 𝕜)
    (hleft :
      (c • clockLeftTranslation (𝕜 := 𝕜) g) * Tinv = 1) :
    c ≠ 0 := by
  intro hc
  subst c
  have hentry := congr_fun (congr_fun hleft 1) 1
  simp at hentry

/-- Exact classification of invertible finite labelled-clock origin
changes: one group translation times one nonzero global scalar. -/
theorem invertibleClockOriginStabilizer_iff
    (T Tinv : Matrix clock clock 𝕜)
    (hleft : T * Tinv = 1) :
    (∃ g : clock,
      (∀ t : clock,
        T * clockBasisProjector t =
          clockBasisProjector (g * t) * T) ∧
      (∀ h : clock,
        T * clockLeftTranslation h =
          clockLeftTranslation (g * h * g⁻¹) * T)) ↔
    ∃ g : clock, ∃ c : 𝕜,
      c ≠ 0 ∧ T = c • clockLeftTranslation g := by
  constructor
  · intro h
    obtain ⟨g, c, hc⟩ := (clockOriginStabilizer_iff T).mp h
    refine ⟨g, c, ?_, hc⟩
    apply smul_clockLeftTranslation_scalar_ne_zero_of_leftInverse
      g c Tinv
    rw [← hc]
    exact hleft
  · rintro ⟨g, c, _, hc⟩
    exact (clockOriginStabilizer_iff T).mpr ⟨g, c, hc⟩

end ClockOrigin

section FinitePhysicalClockWorldOrigin

variable {clock : Type w}
  [Group clock] [Fintype clock] [DecidableEq clock]

/-- **Exact finite physical clock--world stabilizer.**  If an invertible
refactorization preserves two complete physical world labels, transports every
labelled clock reading by one common origin change, and covariantly transports
every regular clock shift, then it is exactly that clock-origin translation
times one nonzero global scalar.  Conversely every such transformation has
all of those properties. -/
theorem physicalFiniteClockWorldStabilizer_iff
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (S Sinv : Matrix (clock × world) (clock × world) 𝕜)
    (hleft : S * Sinv = 1) (hright : Sinv * S = 1)
    [Nonempty world] :
    (S * liftedWorldCoordinateObservable (clock := clock) label * Sinv =
          liftedWorldCoordinateObservable (clock := clock) label ∧
      S * liftedWorldCompleteCouplingObservable
            (clock := clock) (world := world) * Sinv =
          liftedWorldCompleteCouplingObservable
            (clock := clock) (world := world) ∧
      ∃ g : clock,
        (∀ t : clock,
          S * liftedClockOperator (world := world)
                (clockBasisProjector t) =
            liftedClockOperator (world := world)
                (clockBasisProjector (g * t)) * S) ∧
        (∀ h : clock,
          S * liftedClockOperator (world := world)
                (clockLeftTranslation h) =
            liftedClockOperator (world := world)
                (clockLeftTranslation (g * h * g⁻¹)) * S)) ↔
    ∃ g : clock, ∃ c : 𝕜,
      c ≠ 0 ∧
        S = liftedClockOperator (world := world)
          (c • clockLeftTranslation g) := by
  constructor
  · rintro ⟨hcoordinate, hcoupling, g, hprojector, hshift⟩
    obtain ⟨T, hS⟩ :=
      (preserves_world_pair_iff_exists_liftedClockOperator
        label hlabel S Sinv hleft hright).mp
        ⟨hcoordinate, hcoupling⟩
    have hprojectorT :
        ∀ t : clock,
          T * clockBasisProjector t =
            clockBasisProjector (g * t) * T := by
      intro t
      have hp := hprojector t
      rw [hS, liftedClockOperator_mul,
        liftedClockOperator_mul] at hp
      exact liftedClockOperator_injective (world := world) hp
    have hshiftT :
        ∀ h : clock,
          T * clockLeftTranslation h =
            clockLeftTranslation (g * h * g⁻¹) * T := by
      intro h
      have hs := hshift h
      rw [hS, liftedClockOperator_mul,
        liftedClockOperator_mul] at hs
      exact liftedClockOperator_injective (world := world) hs
    obtain ⟨c, hT⟩ :=
      eq_smul_clockLeftTranslation_of_intertwines
        g T hprojectorT hshiftT
    have hc : c ≠ 0 := by
      intro hc
      have hTzero : T = 0 := by
        rw [hT, hc]
        simp
      have hSzero : S = 0 := by
        rw [hS, hTzero]
        ext ai bj
        simp [liftedClockOperator]
      let anchor : world := Classical.choice inferInstance
      have hentry :=
        congr_fun (congr_fun hleft (1, anchor)) (1, anchor)
      rw [hSzero] at hentry
      simp at hentry
    refine ⟨g, c, hc, ?_⟩
    rw [hS, hT]
  · rintro ⟨g, c, _, hS⟩
    have hworld :=
      (preserves_world_pair_iff_exists_liftedClockOperator
        label hlabel S Sinv hleft hright).mpr
        ⟨c • clockLeftTranslation g, hS⟩
    refine ⟨hworld.1, hworld.2, g, ?_, ?_⟩
    · intro t
      rw [hS, liftedClockOperator_mul, liftedClockOperator_mul]
      congr 1
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [clockLeftTranslation_projector_intertwines]
    · intro h
      rw [hS, liftedClockOperator_mul, liftedClockOperator_mul]
      congr 1
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [clockLeftTranslation_shift_covariant]

end FinitePhysicalClockWorldOrigin

end

end HTGeometry
