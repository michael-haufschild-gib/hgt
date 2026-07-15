import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Full-row-rank linear forms preserve algebraic independence

If a coefficient matrix has a right inverse, substitution by its row linear forms has a left
inverse on multivariate polynomial rings.  Hence those linear forms in an algebraically independent
family remain algebraically independent.  This is the nonlinear-rank core used to pass from
polynomial differential-operator row rank to differential transcendence rank.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Matrix MvPolynomial

noncomputable section

/-- Row linear forms of a matrix, evaluated in an algebra over the coefficient ring. -/
def matrixLinearForms
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype n] (M : Matrix m n R) (x : n → A) (i : m) : A :=
  ∑ j, algebraMap R A (M i j) * x j

theorem aeval_toMvPolynomial_eq_matrixLinearForms
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype n] (M : Matrix m n R) (x : n → A) (i : m) :
    MvPolynomial.aeval x (M.toMvPolynomial i) = matrixLinearForms M x i := by
  simp [Matrix.toMvPolynomial, matrixLinearForms, MvPolynomial.aeval_def]

/-- A right-invertible row transformation preserves algebraic independence. -/
theorem algebraicIndependent_matrixLinearForms_of_mul_eq_one
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (N : Matrix n m R) (hMN : M * N = 1)
    (x : n → A) (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R (matrixLinearForms M x) := by
  rw [algebraicIndependent_iff]
  intro p hp
  let q : MvPolynomial n R := MvPolynomial.bind₁ M.toMvPolynomial p
  have hqeval : MvPolynomial.aeval x q = 0 := by
    dsimp [q]
    rw [MvPolynomial.aeval_bind₁]
    simpa only [aeval_toMvPolynomial_eq_matrixLinearForms] using hp
  have hq : q = 0 := hx.eq_zero_of_aeval_eq_zero q hqeval
  have hundone : MvPolynomial.bind₁ N.toMvPolynomial q = p := by
    dsimp [q]
    rw [MvPolynomial.bind₁_bind₁]
    have hvar : (fun i => MvPolynomial.bind₁ N.toMvPolynomial (M.toMvPolynomial i)) =
        (MvPolynomial.X : m → MvPolynomial m R) := by
      funext i
      rw [← Matrix.toMvPolynomial_mul, hMN, Matrix.toMvPolynomial_one]
    rw [hvar]
    exact AlgHom.congr_fun MvPolynomial.bind₁_X_left p
  rw [hq, map_zero] at hundone
  exact hundone.symm

/-- A matrix over a field with linearly independent rows has a right inverse. -/
theorem exists_matrix_rightInverse_of_linearIndependent_rows
    {R m n : Type*} [Field R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (hM : LinearIndependent R M.row) :
    ∃ N : Matrix n m R, M * N = 1 := by
  have hrank : M.rank = Fintype.card m := hM.rank_matrix
  have hrange : Module.finrank R (LinearMap.range M.mulVecLin) =
      Module.finrank R (m → R) := by
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq hrange
  have hsurj : Function.Surjective M.mulVec := by
    exact LinearMap.range_eq_top.mp htop
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj

/-- **Affine splitting law.**  Once a matrix right inverse exists, every other right inverse is
uniquely obtained by adding a matrix killed by left multiplication.  Thus the finite-dimensional
splitting space is a nonempty affine torsor over the kernel of `H ↦ M * H`; any obstruction to a
compatible family of splittings must be global rather than pointwise linear algebra. -/
theorem matrix_rightInverse_iff_kernelPerturbation
    {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (N N' : Matrix n m R) (hMN : M * N = 1) :
    M * N' = 1 ↔ ∃ H : Matrix n m R, M * H = 0 ∧ N' = N + H := by
  constructor
  · intro hMN'
    refine ⟨N' - N, ?_, ?_⟩
    · rw [Matrix.mul_sub, hMN', hMN, sub_self]
    · abel
  · rintro ⟨H, hMH, rfl⟩
    rw [Matrix.mul_add, hMN, hMH, add_zero]

/-- **Surjective splitting-tower law.**  A tower of nonempty finite-stage splitting spaces with
surjective restriction maps has a compatible global splitting.  Hence any genuine completion
obstruction must fail the Mittag--Leffler lifting property at some scale. -/
theorem exists_compatible_of_surjective_tower
    {S : ℕ → Type*} [Nonempty (S 0)]
    (restrict : ∀ n, S (n + 1) → S n)
    (hsurj : ∀ n, Function.Surjective (restrict n)) :
    ∃ q : ∀ n, S n, ∀ n, restrict n (q (n + 1)) = q n := by
  classical
  let lift : ∀ n, S n → S (n + 1) := fun n s ↦ Classical.choose (hsurj n s)
  have hlift : ∀ n s, restrict n (lift n s) = s :=
    fun n s ↦ Classical.choose_spec (hsurj n s)
  let q : ∀ n, S n := fun n ↦
    @Nat.rec (fun n ↦ S n) (Classical.choice inferInstance)
      (fun n s ↦ lift n s) n
  refine ⟨q, ?_⟩
  intro n
  change restrict n (lift n (q n)) = q n
  exact hlift n (q n)

/-!
## A genuine completion-boundary model

Finite-dimensional affine splitting towers are Mittag--Leffler, so a completion obstruction needs
an infinite-dimensional or topological boundary.  The algebraic direct sum gives the sharp model.
At scale `n`, require the first `n` coordinates of a finitely supported reconstruction to be one.
Every finite stage is nonempty, but compatibility would force one finitely supported function to be
one at every coordinate.  The product completion contains exactly that missing boundary point.
-/

/-- Finitely supported reconstructions satisfying the first `n` unit clock constraints. -/
def finitePrefixOneSplitting (R : Type*) [Semiring R] (n : ℕ) :=
  {v : ℕ →₀ R // ∀ i, i < n → v i = 1}

/-- Every finite packet of unit clock constraints has an algebraic finite-support solution. -/
instance finitePrefixOneSplitting_nonempty
    (R : Type*) [Semiring R] (n : ℕ) :
    Nonempty (finitePrefixOneSplitting R n) := by
  let v : ℕ →₀ R := Finsupp.onFinset (Finset.range n)
    (fun i ↦ if i < n then 1 else 0) (by
      intro i hi
      simp only [Finset.mem_range]
      by_contra hnot
      simp [hnot] at hi)
  refine ⟨⟨v, ?_⟩⟩
  intro i hi
  simp [v, hi, Finsupp.onFinset_apply]

/-- Forgetting the last unit constraint preserves the underlying finite-support reconstruction. -/
def finitePrefixOneSplitting_restrict
    (R : Type*) [Semiring R] (n : ℕ) :
    finitePrefixOneSplitting R (n + 1) → finitePrefixOneSplitting R n :=
  fun v ↦ ⟨v.1, fun i hi ↦ v.2 i (lt_trans hi (Nat.lt_succ_self n))⟩

/-- **Algebraic completion obstruction.**  Every finite splitting space is nonempty, but the tower
has no compatible point in the algebraic direct sum: compatibility would produce a finitely
supported function equal to one at every natural-number coordinate. -/
theorem finitePrefixOneSplitting_no_compatible
    (R : Type*) [Semiring R] [Nontrivial R] :
    ¬ ∃ q : ∀ n, finitePrefixOneSplitting R n,
      ∀ n, finitePrefixOneSplitting_restrict R n (q (n + 1)) = q n := by
  rintro ⟨q, hq⟩
  have hval : ∀ n, (q n).1 = (q 0).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hstep := congrArg Subtype.val (hq n)
        exact hstep.trans ih
  have hall : ∀ i, (q 0).1 i = 1 := by
    intro i
    have hi := (q (i + 1)).2 i (Nat.lt_succ_self i)
    rw [hval (i + 1)] at hi
    exact hi
  by_cases hs : (q 0).1.support.Nonempty
  · let i := (q 0).1.support.max' hs + 1
    have hi : i ∉ (q 0).1.support := by
      intro himem
      have hle := (q 0).1.support.le_max' i himem
      omega
    have hzero : (q 0).1 i = 0 := by
      by_contra hne
      exact hi ((Finsupp.mem_support_iff).2 hne)
    exact one_ne_zero ((hall i).symm.trans hzero)
  · have hempty : (q 0).1.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hzero : (q 0).1 0 = 0 := by
      by_contra hne
      have hmem := (Finsupp.mem_support_iff).2 hne
      rw [hempty] at hmem
      simp at hmem
    exact one_ne_zero ((hall 0).symm.trans hzero)

/-- **Positive thin-boundary statement.**  The product completion contains exactly one
reconstruction satisfying every finite unit clock constraint: the constant-one boundary point. -/
theorem existsUnique_productCompletion_unitBoundary
    (R : Type*) [Semiring R] :
    ∃! v : ℕ → R, ∀ n i, i < n → v i = 1 := by
  refine ⟨fun _ ↦ 1, by simp, ?_⟩
  intro v hv
  funext i
  exact hv (i + 1) i (Nat.lt_succ_self i)

/-!
## The clock normalization--symmetry anomaly

Making the constant product-boundary normal in a positive diagonal completion means choosing a
strictly positive summable clock weight.  Such a weight cannot become shift-stationary after any
finite cutoff: otherwise its positive tail would be constant although summability forces it to
tend to zero.  More strongly, no bounded positive change of metric removes this persistent defect.

For a two-sided clock, reflection symmetry turns the multiplicative one-step defect into its
inverse.  Thus positivity, completion, and self-duality do not erase the clock defect; they force
it to be a persistent anti-self-dual modular observable.
-/

/-- **Persistent clock-defect theorem.**  A strictly positive summable clock weight cannot become
shift-stationary after any finite cutoff.  Its normalization defect recurs arbitrarily far along
the clock. -/
theorem summable_positive_has_persistentClockDefect
    (w : ℕ → ℝ) (hpos : ∀ n, 0 < w n) (hsum : Summable w) :
    ∀ N, ∃ n, N ≤ n ∧ w (n + 1) ≠ w n := by
  intro N
  by_contra hdefect
  simp only [not_exists, not_and, not_not] at hdefect
  have hconst : ∀ n, N ≤ n → w n = w N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hdefect n hn).trans ih
  have heq : (fun _ : ℕ => w N) =ᶠ[atTop] w := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hconst n hn).symm
  have hlimN : Tendsto w atTop (nhds (w N)) :=
    tendsto_const_nhds.congr' heq
  have hwNzero : w N = 0 :=
    tendsto_nhds_unique hlimN hsum.tendsto_atTop_zero
  exact (hpos N).ne' hwNzero

/-- **Bounded-gauge nontriviality.**  A positive bounded gauge cannot remove the persistent defect
of a summable positive clock.  Equivalently, the normalization anomaly is nontrivial modulo
bounded positive changes of metric. -/
theorem no_boundedPositiveGauge_stationarizes_summableClock
    (w g : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hg : ∀ n, 0 < g n)
    (hsum : Summable w) (C : ℝ) (hgC : ∀ n, g n ≤ C) :
    ¬ ∀ n, g (n + 1) * w (n + 1) = g n * w n := by
  let v : ℕ → ℝ := fun n => g n * w n
  have hvpos : ∀ n, 0 < v n := fun n => mul_pos (hg n) (hw n)
  have hvsum : Summable v := by
    apply Summable.of_nonneg_of_le
    · exact fun n => (hvpos n).le
    · intro n
      exact mul_le_mul_of_nonneg_right (hgC n) (hw n).le
    · exact hsum.mul_left C
  intro hstationary
  obtain ⟨n, _hn, hdefect⟩ :=
    summable_positive_has_persistentClockDefect v hvpos hvsum 0
  exact hdefect (hstationary n)

/-- Multiplicative modular ratio of a two-sided clock weight. -/
def clockModularRatio (w : ℤ → ℝ) (n : ℤ) : ℝ :=
  w (n + 1) / w n

/-- **Self-dual modular law.**  Reflection symmetry of a two-sided weight makes its modular clock
defect anti-self-dual: reflection reverses and inverts the one-step ratio. -/
theorem clockModularRatio_reflection
    (w : ℤ → ℝ) (hsym : ∀ n, w (-n) = w n) (n : ℤ) :
    clockModularRatio w (-n - 1) = (clockModularRatio w n)⁻¹ := by
  have hidx : -n - 1 + 1 = -n := by ring
  have hden : w (-n - 1) = w (n + 1) := by
    have hneg : -n - 1 = -(n + 1) := by ring
    rw [hneg, hsym (n + 1)]
  rw [clockModularRatio, clockModularRatio, hidx, hsym n, hden]
  field_simp

/-- **Modular reconstruction.**  The modular ratio of a nowhere-zero two-sided clock weight is a
complete invariant up to one overall scalar. -/
theorem clockModularRatio_eq_implies_proportional
    (w v : ℤ → ℝ) (hw : ∀ n, w n ≠ 0) (hv : ∀ n, v n ≠ 0)
    (hratio : ∀ n, clockModularRatio w n = clockModularRatio v n) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ n, v n = c * w n := by
  let q : ℤ → ℝ := fun n => v n / w n
  have hqstep : ∀ n, q (n + 1) = q n := by
    intro n
    apply (div_eq_div_iff (hw (n + 1)) (hw n)).2
    have hcross : w (n + 1) * v n = v (n + 1) * w n :=
      (div_eq_div_iff (hw n) (hv n)).1 (hratio n)
    calc
      v (n + 1) * w n = w (n + 1) * v n := hcross.symm
      _ = v n * w (n + 1) := mul_comm _ _
  have hqconst : ∀ n, q n = q 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih => exact (hqstep n).trans ih
    | pred n ih =>
        have hs := hqstep (-n - 1)
        have hidx : -n - 1 + 1 = -(n : ℤ) := by ring
        rw [hidx] at hs
        exact hs.symm.trans ih
  refine ⟨q 0, div_ne_zero (hv 0) (hw 0), ?_⟩
  intro n
  exact (div_eq_iff (hw n)).1 (hqconst n)

/-- **Normalized modular completeness.**  On positive two-sided clock weights normalized to total
mass one, the modular ratio is injective.  Hence the self-dual modular cocycle determines the
entire positive diagonal boundary completion, not just its local distortion. -/
theorem clockModularRatio_injective_on_normalizedPositiveWeights
    (w v : ℤ → ℝ) (hw : ∀ n, 0 < w n) (hv : ∀ n, 0 < v n)
    (hratio : ∀ n, clockModularRatio w n = clockModularRatio v n)
    (hnormw : ∑' n, w n = 1) (hnormv : ∑' n, v n = 1) :
    w = v := by
  obtain ⟨c, _hc, hcv⟩ :=
    clockModularRatio_eq_implies_proportional w v
      (fun n => (hw n).ne') (fun n => (hv n).ne') hratio
  have hmass : (∑' n, v n) = c * ∑' n, w n := by
    calc
      (∑' n, v n) = ∑' n, c * w n := tsum_congr hcv
      _ = c * ∑' n, w n := tsum_mul_left
  have hcone : c = 1 := by
    rw [hnormv, hnormw, mul_one] at hmass
    exact hmass.symm
  funext n
  rw [hcv n, hcone, one_mul]

/-- Linearly independent matrix rows evaluated on an algebraically independent family remain
algebraically independent. -/
theorem algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
    {R A m n : Type*} [Field R] [CommRing A] [Algebra R A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (hM : LinearIndependent R M.row)
    (x : n → A) (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R (matrixLinearForms M x) := by
  obtain ⟨N, hMN⟩ := exists_matrix_rightInverse_of_linearIndependent_rows M hM
  exact algebraicIndependent_matrixLinearForms_of_mul_eq_one M N hMN x hx

end

end GaloisForLFunctions.HTGeometry
