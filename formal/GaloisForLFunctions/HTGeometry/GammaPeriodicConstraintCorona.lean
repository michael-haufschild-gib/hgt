import GaloisForLFunctions.RHTower.PinnedAffinePrimeJetRigidity
import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.HTGeometry.FormalUnitInverseFreeness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The Gamma shift source has a finite-invisible periodic conormal

The homogeneous tangent of the affine digamma shift equation is the space of period-one
functions.  Finite Fourier packets in that tangent realize every prescribed finite jet by a
Vandermonde isomorphism.  Nevertheless, the infinite factorial-tail Taylor functional annihilates
every such packet because translation by one is the identity.

This is the first concrete source model of the finite-observable conormal corona: every finite
clock window is free, while one nonzero infinite-support source constraint survives.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The frequency of the `m`-th period-one Fourier mode. -/
def gammaPeriodicFrequency (m : ℕ) : ℂ :=
  (m : ℂ) * (2 * (Real.pi : ℂ) * I)

/-- The `m`-th entire period-one Fourier mode. -/
def gammaPeriodicMode (m : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (gammaPeriodicFrequency m * z)

@[simp] theorem gammaPeriodicFrequency_exp (m : ℕ) :
    Complex.exp (gammaPeriodicFrequency m) = 1 := by
  simp [gammaPeriodicFrequency]

@[simp] theorem gammaPeriodicMode_add_one (m : ℕ) (z : ℂ) :
    gammaPeriodicMode m (z + 1) = gammaPeriodicMode m z := by
  rw [gammaPeriodicMode, mul_add, mul_one, Complex.exp_add,
    gammaPeriodicFrequency_exp, mul_one]
  rfl

theorem gammaPeriodicMode_periodic (m : ℕ) :
    Function.Periodic (gammaPeriodicMode m) 1 :=
  gammaPeriodicMode_add_one m

theorem iteratedDeriv_gammaPeriodicMode (m n : ℕ) :
    iteratedDeriv n (gammaPeriodicMode m) =
      fun z ↦ gammaPeriodicFrequency m ^ n * gammaPeriodicMode m z := by
  exact HurwitzExp.iteratedDeriv_expLin (gammaPeriodicFrequency m) n

@[simp] theorem iteratedDeriv_gammaPeriodicMode_zero (m n : ℕ) :
    iteratedDeriv n (gammaPeriodicMode m) 0 = gammaPeriodicFrequency m ^ n := by
  rw [iteratedDeriv_gammaPeriodicMode]
  simp [gammaPeriodicMode]

theorem gammaPeriodicFrequency_fin_injective {k : ℕ} :
    Function.Injective (fun i : Fin k ↦ gammaPeriodicFrequency i) := by
  intro i j hij
  apply Fin.ext
  have hcast : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := by
    apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
    simpa [gammaPeriodicFrequency] using hij
  exact_mod_cast hcast

/-- The first `k` derivatives at zero of a finite period-one Fourier packet. -/
def gammaPeriodicFourierJet {k : ℕ} (a : Fin k → ℂ) (n : Fin k) : ℂ :=
  ∑ m : Fin k, a m * gammaPeriodicFrequency m ^ (n : ℕ)

/-- **Finite-window freedom.**  Every finite clock packet is realized uniquely by a square packet
of periodic Fourier modes. -/
theorem existsUnique_gammaPeriodicFourierJet {k : ℕ} (c : Fin k → ℂ) :
    ∃! a : Fin k → ℂ, ∀ n : Fin k, gammaPeriodicFourierJet a n = c n := by
  simpa [gammaPeriodicFourierJet] using
    RHTower.existsUnique_weightedFiniteMoments
      (fun i : Fin k ↦ gammaPeriodicFrequency i) (fun _ ↦ 1)
      gammaPeriodicFrequency_fin_injective (fun _ ↦ one_ne_zero) c

/-- A finite period-one Fourier polynomial. -/
def gammaPeriodicFourierPolynomial {k : ℕ} (a : Fin k → ℂ) (z : ℂ) : ℂ :=
  ∑ m : Fin k, a m * gammaPeriodicMode m z

theorem gammaPeriodicFourierPolynomial_periodic {k : ℕ} (a : Fin k → ℂ) :
    Function.Periodic (gammaPeriodicFourierPolynomial a) 1 := by
  intro z
  simp [gammaPeriodicFourierPolynomial]

theorem iteratedDeriv_gammaPeriodicFourierPolynomial_zero
    {k : ℕ} (a : Fin k → ℂ) (n : Fin k) :
    iteratedDeriv (n : ℕ) (gammaPeriodicFourierPolynomial a) 0 =
      gammaPeriodicFourierJet a n := by
  change iteratedDeriv (n : ℕ)
    (fun z : ℂ ↦ ∑ m : Fin k, a m * gammaPeriodicMode m z) 0 = _
  rw [HurwitzExp.iteratedDeriv_finset_sum Finset.univ (n : ℕ)]
  · simp [gammaPeriodicFourierJet, iteratedDeriv_const_mul_field,
      iteratedDeriv_gammaPeriodicMode_zero]
  · intro m hm
    exact contDiff_const.mul (HurwitzExp.contDiff_expLin (gammaPeriodicFrequency m))

/-- Every prescribed finite jet is carried by an actual entire period-one Fourier polynomial. -/
theorem existsUnique_gammaPeriodicFourierPolynomial_jet
    {k : ℕ} (c : Fin k → ℂ) :
    ∃! a : Fin k → ℂ,
      Function.Periodic (gammaPeriodicFourierPolynomial a) 1 ∧
        ∀ n : Fin k,
          iteratedDeriv (n : ℕ) (gammaPeriodicFourierPolynomial a) 0 = c n := by
  obtain ⟨a, ha, hua⟩ := existsUnique_gammaPeriodicFourierJet c
  refine ⟨a, ⟨gammaPeriodicFourierPolynomial_periodic a, fun n ↦ ?_⟩, ?_⟩
  · rw [iteratedDeriv_gammaPeriodicFourierPolynomial_zero, ha n]
  · intro b hb
    apply hua
    intro n
    rw [← iteratedDeriv_gammaPeriodicFourierPolynomial_zero]
    exact hb.2 n

/-- The factorial-tail conormal of one period-one Fourier mode has sum zero.  It is the Taylor
form of `e_m(1) - e_m(0) = 0`. -/
theorem gammaPeriodicMode_taylorConormal_hasSum (m : ℕ) :
    HasSum (fun n : ℕ ↦
      gammaPeriodicFrequency m ^ (n + 1) / (n + 1).factorial) 0 := by
  have hexp : NormedSpace.exp (gammaPeriodicFrequency m) = 1 := by
    simpa only [← Complex.exp_eq_exp_ℂ] using gammaPeriodicFrequency_exp m
  simpa [hexp] using (hasSum_nat_add_iff' 1).mpr
    (NormedSpace.expSeries_div_hasSum_exp (gammaPeriodicFrequency m))

/-- **Concrete infinite conormal.**  The same nonzero infinite-support Taylor functional
annihilates every finite periodic Fourier packet, even though those packets realize arbitrary
finite jet data. -/
theorem gammaPeriodicFourier_taylorConormal_hasSum
    {k : ℕ} (a : Fin k → ℂ) :
    HasSum (fun n : ℕ ↦
      ∑ m : Fin k,
        a m * (gammaPeriodicFrequency m ^ (n + 1) / (n + 1).factorial)) 0 := by
  classical
  have hsum : ∀ s : Finset (Fin k),
      HasSum (fun n : ℕ ↦
        ∑ m ∈ s,
          a m * (gammaPeriodicFrequency m ^ (n + 1) / (n + 1).factorial)) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert m s hm ih =>
        have hmSum := (gammaPeriodicMode_taylorConormal_hasSum m).mul_left (a m)
        simpa [Finset.sum_insert hm] using hmSum.add ih
  simpa using hsum Finset.univ

/-- Every differentiated consequence `D^k (exp D - 1)` of the period-one source constraint also
annihilates one Fourier mode.  Thus the Gamma corona conormal is not one-dimensional over the
constants; its thinness is cyclicity over the source operator algebra. -/
theorem gammaPeriodicMode_shiftedTaylorConormal_hasSum (m k : ℕ) :
    HasSum (fun n : ℕ ↦
      gammaPeriodicFrequency m ^ (n + k + 1) / (n + 1).factorial) 0 := by
  have h := (gammaPeriodicMode_taylorConormal_hasSum m).mul_left
    (gammaPeriodicFrequency m ^ k)
  convert h using 1
  · funext n
    rw [show n + k + 1 = k + (n + 1) by omega, pow_add]
    ring
  · simp

/-- **Cyclic source-conormal law.**  Every finite period-one Fourier packet is annihilated by
every shifted factorial-tail conormal `D^k (exp D - 1)`.  These infinitely many constant-field
relations are all source-operator translates of the single unit-shift relation. -/
theorem gammaPeriodicFourier_shiftedTaylorConormal_hasSum
    {r : ℕ} (a : Fin r → ℂ) (k : ℕ) :
    HasSum (fun n : ℕ ↦
      ∑ m : Fin r,
        a m * (gammaPeriodicFrequency m ^ (n + k + 1) / (n + 1).factorial)) 0 := by
  classical
  have hsum : ∀ s : Finset (Fin r),
      HasSum (fun n : ℕ ↦
        ∑ m ∈ s,
          a m *
            (gammaPeriodicFrequency m ^ (n + k + 1) / (n + 1).factorial)) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert m s hm ih =>
        have hmSum :=
          (gammaPeriodicMode_shiftedTaylorConormal_hasSum m k).mul_left (a m)
        simpa [Finset.sum_insert hm] using hmSum.add ih
  simpa using hsum Finset.univ

/-! ### Rank-one curvature of finite unit-translation shadows -/

/-- Taylor coefficient carrying the `j`-th raw derivative into the `i`-th derivative after unit
translation. -/
def gammaClockTranslationCoefficient (i j : ℕ) : ℂ :=
  if i ≤ j then 1 / (j - i).factorial else 0

/-- The canonical finite Taylor shadow of unit translation on the first `n` raw derivatives. -/
def gammaClockTranslation (n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun a i := ∑ j : Fin n, gammaClockTranslationCoefficient i j * a j
  map_add' a b := by
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Forget the highest raw derivative. -/
def gammaClockTruncate (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun a i := a i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Failure of the two adjacent finite unit-translation shadows to commute with truncation. -/
def gammaClockCurvature (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (gammaClockTruncate n).comp (gammaClockTranslation (n + 1)) -
    (gammaClockTranslation n).comp (gammaClockTruncate n)

/-- **Exact Gamma clock curvature.**  The whole discrepancy between adjacent translation shadows
comes from the omitted highest derivative, with the factorial-tail coefficient expected from
Taylor translation. -/
theorem gammaClockCurvature_apply (n : ℕ)
    (a : Fin (n + 1) → ℂ) (i : Fin n) :
    gammaClockCurvature n a i =
      a (Fin.last n) / ((n - i).factorial : ℂ) := by
  change (∑ j : Fin (n + 1),
      gammaClockTranslationCoefficient (i : ℕ) (j : ℕ) * a j) -
      (∑ j : Fin n,
        gammaClockTranslationCoefficient (i : ℕ) (j : ℕ) * a j.castSucc) = _
  rw [Fin.sum_univ_castSucc]
  simp only [gammaClockTranslationCoefficient, Fin.val_castSucc]
  rw [add_sub_cancel_left]
  simp [Nat.le_of_lt i.isLt, div_eq_mul_inv, mul_comm]

/-- The factorial-tail boundary vector exposed at resolution `n`. -/
def gammaClockBoundaryVector (n : ℕ) : Fin n → ℂ :=
  fun i => 1 / ((n - i).factorial : ℂ)

/-- The Gamma curvature is the outer product of highest-jet evaluation with the factorial-tail
boundary vector. -/
theorem gammaClockCurvature_eq_outerProduct (n : ℕ)
    (a : Fin (n + 1) → ℂ) :
    gammaClockCurvature n a =
      a (Fin.last n) • gammaClockBoundaryVector n := by
  funext i
  rw [gammaClockCurvature_apply]
  simp [gammaClockBoundaryVector, div_eq_mul_inv]

/-- The curvature range is exactly the boundary line generated by the factorial tail. -/
theorem range_gammaClockCurvature (n : ℕ) :
    LinearMap.range (gammaClockCurvature n) =
      ℂ ∙ gammaClockBoundaryVector n := by
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    rw [gammaClockCurvature_eq_outerProduct]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    refine ⟨Pi.single (Fin.last n) 1, ?_⟩
    rw [gammaClockCurvature_eq_outerProduct]
    simp

theorem gammaClockBoundaryVector_ne_zero (n : ℕ) :
    gammaClockBoundaryVector (n + 1) ≠ 0 := by
  intro hzero
  have hlast := congrFun hzero (Fin.last n)
  simp [gammaClockBoundaryVector] at hlast

/-- Every positive Gamma clock resolution has exactly rank-one translation curvature. -/
theorem finrank_range_gammaClockCurvature (n : ℕ) :
    Module.finrank ℂ (LinearMap.range (gammaClockCurvature (n + 1))) = 1 := by
  rw [range_gammaClockCurvature]
  exact finrank_span_singleton (gammaClockBoundaryVector_ne_zero n)

/-- Forward zero-extension of finite jet directions.  This is the Ind variance of the clock, in
contrast with backward observable truncation. -/
def gammaClockExtendZero (n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun a := Fin.snoc a 0
  map_add' a b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c a := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- **Gamma Ind-flatness.**  The same finite unit-translation shadows which have rank-one
curvature under backward observation commute exactly with forward zero-extension.  Thus Gamma's
field is globally integrable on the algebraic direct-limit clock even though its dual truncation
tower is curved. -/
theorem gammaClockTranslation_extendZero (n : ℕ) :
    (gammaClockTranslation (n + 1)).comp (gammaClockExtendZero n) =
      (gammaClockExtendZero n).comp (gammaClockTranslation n) := by
  apply LinearMap.ext
  intro a
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · dsimp [gammaClockTranslation, gammaClockExtendZero]
    rw [Fin.sum_univ_castSucc]
    simp [gammaClockTranslationCoefficient, Nat.not_le_of_lt]
  · dsimp [gammaClockTranslation, gammaClockExtendZero]
    rw [Fin.sum_univ_castSucc]
    simp

/-- The finite raw-jet action of multiplication by the coordinate `z`. Differentiating
`z f(z)` gives the lower-triangular rule `(z f)^(j) = z f^(j) + j f^(j-1)`. -/
def gammaClockCoordinateMultiplication (n : ℕ) (z : ℂ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun a i := Fin.cases (z * a 0)
    (fun j => z * a j.succ + (j.succ : ℕ) * a j.castSucc) i
  map_add' a b := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · simp [mul_add]
      ring
  map_smul' c a := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [smul_eq_mul, mul_add] <;> ring

/-- **Algebraic Pro-flatness.** Coordinate multiplication on differentiated jets commutes exactly
with forgetting the highest derivative. This is the variance-dual statement to the Ind-flatness
of finite Taylor translation. -/
theorem gammaClockCoordinateMultiplication_truncate (n : ℕ) (z : ℂ) :
    (gammaClockTruncate (n + 1)).comp
        (gammaClockCoordinateMultiplication (n + 1) z) =
      (gammaClockCoordinateMultiplication n z).comp
        (gammaClockTruncate (n + 1)) := by
  apply LinearMap.ext
  intro a
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [gammaClockCoordinateMultiplication, gammaClockTruncate, LinearMap.comp_apply]

/-- Failure of coordinate multiplication to commute with forward zero-extension. This is the
incoming boundary transfer dual to the outgoing Taylor-translation curvature. -/
def gammaClockCoordinateIncoming (n : ℕ) (z : ℂ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 2) → ℂ) :=
  (gammaClockCoordinateMultiplication (n + 1) z).comp
      (gammaClockExtendZero (n + 1)) -
    (gammaClockExtendZero (n + 1)).comp
      (gammaClockCoordinateMultiplication n z)

/-- **Exact incoming Gamma boundary channel.** The algebraic prolongation defect is zero on all
retained jet slots and sends only the old highest derivative into the new boundary slot, with
Leibniz weight `n+1`. -/
theorem gammaClockCoordinateIncoming_apply_castSucc (n : ℕ) (z : ℂ)
    (a : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    gammaClockCoordinateIncoming n z a i.castSucc = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [gammaClockCoordinateIncoming, gammaClockCoordinateMultiplication,
      gammaClockExtendZero, LinearMap.comp_apply]
  · change (z * (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ) j.succ.castSucc +
        (j.succ : ℕ) * (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ)
          j.castSucc.castSucc) -
        (Fin.snoc (gammaClockCoordinateMultiplication n z a) (0 : ℂ) :
          Fin (n + 2) → ℂ) j.succ.castSucc = 0
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    simp [gammaClockCoordinateMultiplication]

theorem gammaClockCoordinateIncoming_apply_last (n : ℕ) (z : ℂ)
    (a : Fin (n + 1) → ℂ) :
    gammaClockCoordinateIncoming n z a (Fin.last (n + 1)) =
      (n + 1 : ℂ) * a (Fin.last n) := by
  change gammaClockCoordinateMultiplication (n + 1) z
      (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ)
      (Fin.last (n + 1)) -
      (Fin.snoc (gammaClockCoordinateMultiplication n z a) (0 : ℂ) :
        Fin (n + 2) → ℂ) (Fin.last (n + 1)) = _
  rw [Fin.snoc_last, show Fin.last (n + 1) = (Fin.last n).succ by rfl]
  simp only [gammaClockCoordinateMultiplication, sub_zero]
  change (@Fin.cases (n + 1) (fun _ : Fin (n + 2) => ℂ)
      (z * (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ) 0)
      (fun j => z * (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ) j.succ +
        (j.succ : ℕ) *
          (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ) j.castSucc)
      (Fin.last (n + 1))) = _
  rw [show Fin.last (n + 1) = (Fin.last n).succ by rfl, Fin.cases_succ,
    show (Fin.last n).succ = Fin.last (n + 1) by rfl,
    Fin.snoc_last, Fin.snoc_castSucc]
  simp

/-- Pair the incoming algebraic prolongation defect with the outgoing analytic Taylor curvature.
This is the finite transgression current from the Gamma source conormal into the newest independent
clock direction. -/
def gammaClockPairedBoundaryCurrent (n : ℕ) (z : ℂ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  (gammaClockCurvature (n + 1)).comp (gammaClockCoordinateIncoming n z)

/-- **Exact Gamma capacity--current pairing.**  The paired opposite-variance current reads the old
highest jet and returns the factorial-tail boundary symbol with Leibniz weight `n+1`.  In
particular it is independent of the base coordinate `z`; the affine source coefficient changes
the two realizations but not their transverse boundary pairing. -/
theorem gammaClockPairedBoundaryCurrent_apply (n : ℕ) (z : ℂ)
    (a : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    gammaClockPairedBoundaryCurrent n z a i =
      (n + 1 : ℂ) * a (Fin.last n) / ((n + 1 - i).factorial : ℂ) := by
  rw [gammaClockPairedBoundaryCurrent, LinearMap.comp_apply,
    gammaClockCurvature_apply, gammaClockCoordinateIncoming_apply_last]

/-- The paired current is the outer product of highest-jet evaluation and the differentiated
shift-conormal boundary vector. -/
theorem gammaClockPairedBoundaryCurrent_eq_outerProduct (n : ℕ) (z : ℂ)
    (a : Fin (n + 1) → ℂ) :
    gammaClockPairedBoundaryCurrent n z a =
      ((n + 1 : ℂ) * a (Fin.last n)) • gammaClockBoundaryVector (n + 1) := by
  funext i
  rw [gammaClockPairedBoundaryCurrent_apply]
  simp [gammaClockBoundaryVector, div_eq_mul_inv]

/-- The source-paired Gamma transgression has exactly the same rank-one range as the outgoing
factorial-tail conormal boundary symbol. -/
theorem range_gammaClockPairedBoundaryCurrent (n : ℕ) (z : ℂ) :
    LinearMap.range (gammaClockPairedBoundaryCurrent n z) =
      ℂ ∙ gammaClockBoundaryVector (n + 1) := by
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    rw [gammaClockPairedBoundaryCurrent_eq_outerProduct]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    refine ⟨Pi.single (Fin.last n) ((n + 1 : ℂ)⁻¹), ?_⟩
    rw [gammaClockPairedBoundaryCurrent_eq_outerProduct]
    simp only [Pi.single_eq_same]
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [mul_inv_cancel₀ hn, one_smul]

/-- Every positive Gamma clock layer carries one nonzero paired boundary-current direction. -/
theorem finrank_range_gammaClockPairedBoundaryCurrent (n : ℕ) (z : ℂ) :
    Module.finrank ℂ (LinearMap.range (gammaClockPairedBoundaryCurrent n z)) = 1 := by
  rw [range_gammaClockPairedBoundaryCurrent]
  exact finrank_span_singleton (gammaClockBoundaryVector_ne_zero n)

/-- The new-boundary projector in the split Gamma jet clock. -/
def gammaClockBoundaryProjector (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.id - (gammaClockExtendZero n).comp (gammaClockTruncate n)

@[simp] theorem gammaClockBoundaryProjector_apply_last (n : ℕ)
    (a : Fin (n + 1) → ℂ) :
    gammaClockBoundaryProjector n a (Fin.last n) = a (Fin.last n) := by
  simp [gammaClockBoundaryProjector, gammaClockExtendZero, gammaClockTruncate,
    LinearMap.comp_apply]

@[simp] theorem gammaClockBoundaryProjector_apply_castSucc (n : ℕ)
    (a : Fin (n + 1) → ℂ) (i : Fin n) :
    gammaClockBoundaryProjector n a i.castSucc = 0 := by
  simp [gammaClockBoundaryProjector, gammaClockExtendZero, gammaClockTruncate,
    LinearMap.comp_apply]

/-- **Canonical Gamma boundary symbol.**  Translation compressed to the newly exposed highest-jet
line is exactly the identity on that line.  Gamma therefore supplies the missing colligation datum
canonically: factorial-tail curvature is its outgoing transfer, while its boundary self-symbol is
the unit. -/
theorem gammaClockBoundaryCompression_eq_projector (n : ℕ) :
    (gammaClockBoundaryProjector n).comp
        ((gammaClockTranslation (n + 1)).comp (gammaClockBoundaryProjector n)) =
      gammaClockBoundaryProjector n := by
  apply LinearMap.ext
  intro a
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [LinearMap.comp_apply, gammaClockBoundaryProjector_apply_last]
    dsimp [gammaClockTranslation]
    rw [Fin.sum_univ_castSucc]
    simp [gammaClockTranslationCoefficient, Nat.not_le_of_lt]
  · simp only [LinearMap.comp_apply, gammaClockBoundaryProjector_apply_castSucc]

/-! ### Formal-unit/global-nonunit specialization -/

/-- Positive-degree coefficients of the formal shift cofactor
`(exp D - 1) / D = 1 + D/2! + D^2/3! + ...`. -/
def gammaShiftCofactorCoefficients (n : ℕ) : ℂ :=
  1 / ((n + 2).factorial : ℂ)

/-- The shift cofactor as a formal unit. -/
def gammaShiftCofactorFormal : PowerSeries ℂ :=
  GaloisForLFunctions.unitPowerSeriesOfCoefficients gammaShiftCofactorCoefficients

/-- Its canonical formal inverse. -/
def gammaShiftCofactorFormalInverse : PowerSeries ℂ :=
  GaloisForLFunctions.unitInversePowerSeriesOfCoefficients gammaShiftCofactorCoefficients

@[simp] theorem gammaShiftCofactorFormal_constantCoeff :
    gammaShiftCofactorFormal.constantCoeff = 1 := by
  simp [gammaShiftCofactorFormal]

theorem gammaShiftCofactorFormal_mul_inverse :
    gammaShiftCofactorFormal * gammaShiftCofactorFormalInverse = 1 := by
  exact GaloisForLFunctions.unitPowerSeries_mul_unitInverse gammaShiftCofactorCoefficients

theorem gammaShiftCofactorFormal_inverse_mul :
    gammaShiftCofactorFormalInverse * gammaShiftCofactorFormal = 1 := by
  exact GaloisForLFunctions.unitInverse_mul_unitPowerSeries gammaShiftCofactorCoefficients

/-- The global analytic symbol of the shift cofactor away from its removable origin. -/
def gammaShiftCofactorSymbol (z : ℂ) : ℂ :=
  (Complex.exp z - 1) / z

@[simp] theorem gammaShiftCofactorSymbol_periodicFrequency (m : ℕ) :
    gammaShiftCofactorSymbol (gammaPeriodicFrequency m) = 0 := by
  simp [gammaShiftCofactorSymbol]

theorem gammaPeriodicFrequency_ne_zero {m : ℕ} (hm : m ≠ 0) :
    gammaPeriodicFrequency m ≠ 0 := by
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hm) Complex.two_pi_I_ne_zero

/-- Reflection preserves the global nonunit divisor up to the nowhere-zero exponential unit. -/
theorem gammaShiftCofactorSymbol_neg {z : ℂ} (hz : z ≠ 0) :
    gammaShiftCofactorSymbol (-z) =
      Complex.exp (-z) * gammaShiftCofactorSymbol z := by
  rw [gammaShiftCofactorSymbol, gammaShiftCofactorSymbol]
  rw [Complex.exp_neg]
  field_simp [hz, Complex.exp_ne_zero]
  ring

end


end GaloisForLFunctions.HTGeometry
