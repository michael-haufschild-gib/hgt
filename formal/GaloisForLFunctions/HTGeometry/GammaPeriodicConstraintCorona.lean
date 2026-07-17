import GaloisForLFunctions.RHTower.PinnedAffinePrimeJetRigidity
import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.HTGeometry.FormalUnitInverseFreeness
import GaloisForLFunctions.HTGeometry.GammaClockCoronaConormal
import GaloisForLFunctions.HTGeometry.ClockDescentAnomaly
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

/-- Coefficient of the basic Gamma/digamma unit-shift conormal on the `(n+1)`-st derivative. -/
def gammaPeriodicConormalCoefficient (n : ℕ) : ℂ :=
  1 / ((n + 1).factorial : ℂ)

/-- A raw clock growing exactly fast enough to cancel the factorial conormal decay. -/
def gammaFactorialRawClock (n : ℕ) : ℂ :=
  ((n + 1).factorial : ℂ)

@[simp] theorem gammaPeriodicConormalCoefficient_mul_factorialRawClock (n : ℕ) :
    gammaPeriodicConormalCoefficient n * gammaFactorialRawClock n = 1 := by
  simp only [gammaPeriodicConormalCoefficient, gammaFactorialRawClock, one_div]
  apply inv_mul_cancel₀
  exact_mod_cast Nat.factorial_ne_zero (n + 1)

/-! ### Exact comparison with the universal finite-blind stream corona -/

/-- The factorial Taylor coefficients satisfy the unique weighted-prepend recurrence. -/
theorem gammaPeriodicConormalCoefficient_succ (n : ℕ) :
    gammaPeriodicConormalCoefficient (n + 1) =
      ((n + 2 : ℕ) : ℂ)⁻¹ * gammaPeriodicConormalCoefficient n := by
  simp only [gammaPeriodicConormalCoefficient, one_div]
  conv_lhs => rw [Nat.factorial_succ]
  push_cast
  rw [mul_inv_rev]
  ring

/-- Diagonal factorial normalization from raw coefficient streams to analytic Taylor-conormal
streams.  Its inverse multiplies by the corresponding factorial scale. -/
def gammaFactorialStreamEquiv : (ℕ → ℂ) ≃ₗ[ℂ] (ℕ → ℂ) where
  toFun c n := gammaPeriodicConormalCoefficient n * c n
  invFun a n := gammaFactorialRawClock n * a n
  left_inv c := by
    funext n
    change gammaFactorialRawClock n *
      (gammaPeriodicConormalCoefficient n * c n) = c n
    rw [← mul_assoc, mul_comm (gammaFactorialRawClock n),
      gammaPeriodicConormalCoefficient_mul_factorialRawClock]
    simp
  right_inv a := by
    funext n
    change gammaPeriodicConormalCoefficient n *
      (gammaFactorialRawClock n * a n) = a n
    rw [← mul_assoc, gammaPeriodicConormalCoefficient_mul_factorialRawClock]
    simp
  map_add' c d := by
    funext n
    simp only [Pi.add_apply, mul_add]
  map_smul' a c := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The Taylor-normalized dual shift.  Its kernel recurrence is the factorial-tail recurrence,
not the constant-stream recurrence. -/
def gammaTaylorStreamSource : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun a n := Nat.casesOn n (-a 0)
    (fun m => ((m + 2 : ℕ) : ℂ)⁻¹ * a m - a (m + 1))
  map_add' a b := by
    funext n
    cases n <;> simp [mul_add] <;> ring
  map_smul' c a := by
    funext n
    cases n with
    | zero => simp
    | succ n =>
        simp
        ring

@[simp] theorem gammaTaylorStreamSource_apply_zero (a : ℕ → ℂ) :
    gammaTaylorStreamSource a 0 = -a 0 := rfl

@[simp] theorem gammaTaylorStreamSource_apply_succ (a : ℕ → ℂ) (n : ℕ) :
    gammaTaylorStreamSource a (n + 1) =
      ((n + 2 : ℕ) : ℂ)⁻¹ * a n - a (n + 1) := rfl

/-- **Raw Gamma corona comparison.**  Factorial normalization conjugates the source-defined
constant-stream constraint to the analytic Taylor-weighted constraint. -/
theorem gammaFactorialStreamEquiv_intertwines (c : ℕ → ℂ) :
    gammaFactorialStreamEquiv (streamCoronaSource ℂ c) =
      gammaTaylorStreamSource (gammaFactorialStreamEquiv c) := by
  funext n
  cases n with
  | zero =>
      simp [gammaFactorialStreamEquiv, gammaPeriodicConormalCoefficient]
  | succ n =>
      change gammaPeriodicConormalCoefficient (n + 1) *
          (c n - c (n + 1)) =
        ((n + 2 : ℕ) : ℂ)⁻¹ *
            (gammaPeriodicConormalCoefficient n * c n) -
          gammaPeriodicConormalCoefficient (n + 1) * c (n + 1)
      rw [gammaPeriodicConormalCoefficient_succ]
      ring

/-- Factorial normalization preserves finite observability. -/
theorem gammaFactorialStreamEquiv_eventuallyZero
    {c : ℕ → ℂ} (hc : c ∈ eventuallyZeroStream ℂ) :
    gammaFactorialStreamEquiv c ∈ eventuallyZeroStream ℂ := by
  obtain ⟨N, hN⟩ := hc
  exact ⟨N, fun n hn => by simp [gammaFactorialStreamEquiv, hN n hn]⟩

/-- Inverse factorial normalization also preserves finite observability. -/
theorem gammaFactorialStreamEquiv_symm_eventuallyZero
    {c : ℕ → ℂ} (hc : c ∈ eventuallyZeroStream ℂ) :
    gammaFactorialStreamEquiv.symm c ∈ eventuallyZeroStream ℂ := by
  obtain ⟨N, hN⟩ := hc
  exact ⟨N, fun n hn => by simp [gammaFactorialStreamEquiv, hN n hn]⟩

/-- Factorial normalization descended to the finite-blind corona quotient. -/
def gammaFactorialCoronaScale : StreamCorona ℂ →ₗ[ℂ] StreamCorona ℂ :=
  Submodule.mapQ _ _ gammaFactorialStreamEquiv.toLinearMap
    (fun _ hc => gammaFactorialStreamEquiv_eventuallyZero hc)

/-- Inverse factorial normalization on the finite-blind corona quotient. -/
def gammaFactorialCoronaUnscale : StreamCorona ℂ →ₗ[ℂ] StreamCorona ℂ :=
  Submodule.mapQ _ _ gammaFactorialStreamEquiv.symm.toLinearMap
    (fun _ hc => gammaFactorialStreamEquiv_symm_eventuallyZero hc)

/-- The raw finite-blind corona and the Taylor-normalized corona are canonically linearly
equivalent. -/
def gammaFactorialCoronaEquiv : StreamCorona ℂ ≃ₗ[ℂ] StreamCorona ℂ where
  toFun := gammaFactorialCoronaScale
  invFun := gammaFactorialCoronaUnscale
  left_inv x := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [gammaFactorialCoronaScale, gammaFactorialCoronaUnscale,
      Submodule.mapQ_apply]
  right_inv x := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [gammaFactorialCoronaScale, gammaFactorialCoronaUnscale,
      Submodule.mapQ_apply]
  map_add' := gammaFactorialCoronaScale.map_add
  map_smul' := gammaFactorialCoronaScale.map_smul

/-- The analytic factorial-tail conormal stream. -/
def gammaFactorialConormalStream : ℕ → ℂ :=
  gammaPeriodicConormalCoefficient

/-- Factorial normalization carries the raw constant conormal to the analytic factorial-tail
conormal, coefficient for coefficient. -/
theorem gammaFactorialStreamEquiv_const :
    gammaFactorialStreamEquiv (fun _ => (1 : ℂ)) =
      gammaFactorialConormalStream := by
  funext n
  simp [gammaFactorialStreamEquiv, gammaFactorialConormalStream]

/-- The comparison equivalence carries the nonzero raw corona class to the analytic conormal
class. -/
@[simp] theorem gammaFactorialCoronaEquiv_const :
    gammaFactorialCoronaEquiv
        (Submodule.Quotient.mk (fun _ => (1 : ℂ)) : StreamCorona ℂ) =
      (Submodule.Quotient.mk gammaFactorialConormalStream : StreamCorona ℂ) := by
  change Submodule.Quotient.mk
      (gammaFactorialStreamEquiv (fun _ => (1 : ℂ))) =
    Submodule.Quotient.mk gammaFactorialConormalStream
  rw [gammaFactorialStreamEquiv_const]

/-- The Taylor-weighted source preserves finite observability. -/
theorem eventuallyZeroStream_le_comap_gammaTaylorStreamSource :
    eventuallyZeroStream ℂ ≤
      (eventuallyZeroStream ℂ).comap gammaTaylorStreamSource := by
  rintro a ⟨N, hN⟩
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [gammaTaylorStreamSource_apply_succ, hN m (by omega),
    hN (m + 1) (by omega)]
  simp

/-- The analytic Taylor-weighted constraint descended to the finite-blind corona. -/
def gammaTaylorCoronaConstraint : StreamCorona ℂ →ₗ[ℂ] StreamCorona ℂ :=
  Submodule.mapQ _ _ gammaTaylorStreamSource
    eventuallyZeroStream_le_comap_gammaTaylorStreamSource

/-- **Corona-level Gamma comparison.**  The factorial comparison intertwines the raw and analytic
corona constraints. -/
theorem gammaFactorialCoronaEquiv_intertwines :
    gammaFactorialCoronaEquiv.toLinearMap.comp (streamCoronaConstraint ℂ) =
      gammaTaylorCoronaConstraint.comp gammaFactorialCoronaEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk
      (gammaFactorialStreamEquiv (streamCoronaSource ℂ c)) =
    Submodule.Quotient.mk
      (gammaTaylorStreamSource (gammaFactorialStreamEquiv c))
  rw [gammaFactorialStreamEquiv_intertwines]

/-- The analytic factorial-tail class survives finite observability. -/
theorem gammaFactorialConormalCoronaClass_ne_zero :
    (Submodule.Quotient.mk gammaFactorialConormalStream : StreamCorona ℂ) ≠ 0 := by
  intro hzero
  apply coronaClass_const_ne_zero ℂ
  apply gammaFactorialCoronaEquiv.injective
  simpa using hzero

/-- The analytic factorial-tail stream is killed by the Taylor-weighted source modulo a single
finite boundary coordinate. -/
theorem gammaTaylorStreamSource_factorial_mem_eventuallyZero :
    gammaTaylorStreamSource gammaFactorialConormalStream ∈ eventuallyZeroStream ℂ := by
  refine ⟨1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [gammaTaylorStreamSource_apply_succ]
  exact sub_eq_zero.mpr (gammaPeriodicConormalCoefficient_succ m).symm

/-- The analytic factorial-tail class is a nonzero conormal in the Taylor-normalized corona. -/
theorem gammaFactorialConormalCoronaClass_mem_ker :
    (Submodule.Quotient.mk gammaFactorialConormalStream : StreamCorona ℂ) ∈
      LinearMap.ker gammaTaylorCoronaConstraint := by
  rw [LinearMap.mem_ker, gammaTaylorCoronaConstraint, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact gammaTaylorStreamSource_factorial_mem_eventuallyZero

/-- **Analytic Gamma corona line theorem.**  The Taylor-normalized finite-blind constraint has
exactly one conormal line, spanned by the factorial-tail class.  The comparison equivalence
therefore identifies the complete raw and analytic corona kernels, not only one chosen vector. -/
theorem ker_gammaTaylorCoronaConstraint :
    LinearMap.ker gammaTaylorCoronaConstraint =
      Submodule.span ℂ
        {(Submodule.Quotient.mk gammaFactorialConormalStream : StreamCorona ℂ)} := by
  apply le_antisymm
  · intro x hx
    let y : StreamCorona ℂ := gammaFactorialCoronaEquiv.symm x
    have hyker : y ∈ LinearMap.ker (streamCoronaConstraint ℂ) := by
      rw [LinearMap.mem_ker]
      apply gammaFactorialCoronaEquiv.injective
      have hcomm := LinearMap.congr_fun gammaFactorialCoronaEquiv_intertwines y
      simp only [LinearMap.comp_apply] at hcomm
      calc
        gammaFactorialCoronaEquiv ((streamCoronaConstraint ℂ) y) =
            gammaTaylorCoronaConstraint (gammaFactorialCoronaEquiv y) := hcomm
        _ = 0 := by
          rw [gammaFactorialCoronaEquiv.apply_symm_apply,
            LinearMap.mem_ker.mp hx]
        _ = gammaFactorialCoronaEquiv 0 := by rw [map_zero]
    have hyspan : y ∈ Submodule.span ℂ
        {(Submodule.Quotient.mk (fun _ => (1 : ℂ)) : StreamCorona ℂ)} := by
      rw [← ker_streamCoronaConstraint ℂ]
      exact hyker
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hyspan
    dsimp [y] at ha
    rw [← gammaFactorialCoronaEquiv.apply_symm_apply x, ← ha, map_smul,
      gammaFactorialCoronaEquiv_const]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact gammaFactorialConormalCoronaClass_mem_ker

/-- **Uniqueness of the Gamma comparison scale.**  Zeroth-order normalization and intertwining
with the Taylor-weighted prepend recurrence force the complete factorial-tail sequence. -/
theorem gammaFactorialConormalStream_unique
    (w : ℕ → ℂ) (hzero : w 0 = 1)
    (hsucc : ∀ n, w (n + 1) = ((n + 2 : ℕ) : ℂ)⁻¹ * w n) :
    w = gammaFactorialConormalStream := by
  funext n
  induction n with
  | zero => simpa [gammaFactorialConormalStream,
      gammaPeriodicConormalCoefficient] using hzero
  | succ n ih =>
      rw [hsucc n, ih, gammaFactorialConormalStream,
        gammaPeriodicConormalCoefficient_succ]

/-- **Raw-clock domain no-go.**  The genuine factorial-tail source conormal does not define a
summable pairing on every raw sequence: on the factorial-growth clock every term is one.  Hence an
analytic HT conormal necessarily comes with a proper source-selected summability domain, not only a
finer topology on all of `ℂ^ℕ`. -/
theorem gammaPeriodicConormal_not_summable_on_all_rawClocks :
    ¬ Summable (fun n : ℕ ↦
      gammaPeriodicConormalCoefficient n * gammaFactorialRawClock n) := by
  intro h
  have hone : Summable (fun _ : ℕ ↦ (1 : ℂ)) := by simpa using h
  exact one_ne_zero ((summable_const_iff (β := ℕ) (1 : ℂ)).mp hone)

/-- The maximal raw positive-derivative-tail subspace on which every differentiated Gamma shift
conormal is summable.  The parameter `k` indexes the source-operator translates
`D^k (exp D - 1)` of the basic conormal. -/
def gammaCoronaClockDomain : Submodule ℂ (ℕ → ℂ) where
  carrier := {b | ∀ k : ℕ, Summable (fun n : ℕ ↦
    gammaPeriodicConormalCoefficient n * b (n + k))}
  zero_mem' := by
    intro k
    simp
  add_mem' := by
    intro a b ha hb k
    have h := (ha k).add (hb k)
    simpa [mul_add] using h
  smul_mem' := by
    intro s a ha k
    have h := (ha k).mul_left s
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Tail shift on positive raw derivative clocks. -/
def gammaCoronaClockTail (b : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ b (n + 1)

/-- The maximal Gamma conormal domain is stable under the derivative-tail shift.  This is the
domain form of closure under all differentiated source constraints. -/
theorem gammaCoronaClockDomain_tail
    {b : ℕ → ℂ} (hb : b ∈ gammaCoronaClockDomain) :
    gammaCoronaClockTail b ∈ gammaCoronaClockDomain := by
  intro k
  have h := hb (k + 1)
  apply h.congr
  intro n
  simp only [gammaCoronaClockTail]
  congr 2

/-- Positive derivative-tail clock of one period-one Fourier mode. -/
def gammaPeriodicModeTail (m : ℕ) : ℕ → ℂ :=
  fun n ↦ gammaPeriodicFrequency m ^ (n + 1)

/-- Every periodic Fourier mode lies in the maximal Gamma conormal domain. -/
theorem gammaPeriodicModeTail_mem_coronaClockDomain (m : ℕ) :
    gammaPeriodicModeTail m ∈ gammaCoronaClockDomain := by
  intro k
  have h := (gammaPeriodicMode_shiftedTaylorConormal_hasSum m k).summable
  apply h.congr
  intro n
  simp [gammaPeriodicConormalCoefficient, gammaPeriodicModeTail, div_eq_mul_inv]
  ring

/-- Positive derivative-tail clock of a finite period-one Fourier packet. -/
def gammaPeriodicFourierTail {r : ℕ} (a : Fin r → ℂ) : ℕ → ℂ :=
  fun n ↦ ∑ m : Fin r, a m * gammaPeriodicFrequency m ^ (n + 1)

/-- **Concrete Gamma rigging.**  Every finite periodic Fourier packet lies in the maximal domain on
which the entire cyclic family of differentiated shift conormals is summable. -/
theorem gammaPeriodicFourierTail_mem_coronaClockDomain
    {r : ℕ} (a : Fin r → ℂ) :
    gammaPeriodicFourierTail a ∈ gammaCoronaClockDomain := by
  intro k
  have h := (gammaPeriodicFourier_shiftedTaylorConormal_hasSum a k).summable
  apply h.congr
  intro n
  simp only [gammaPeriodicConormalCoefficient, gammaPeriodicFourierTail, one_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The `k`-th differentiated Gamma conormal as an actual linear functional on its maximal cyclic
summability domain. -/
def gammaCoronaConormal (k : ℕ) : gammaCoronaClockDomain →ₗ[ℂ] ℂ where
  toFun b := ∑' n : ℕ, gammaPeriodicConormalCoefficient n * b.1 (n + k)
  map_add' a b := by
    have h := (a.2 k).tsum_add (b.2 k)
    simpa [mul_add] using h
  map_smul' s a := by
    have h := (a.2 k).tsum_mul_left s
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- **Cyclic conormal covariance.**  Tail shift advances the differentiated source conormal by one:
`λ_k(Tb)=λ_(k+1)(b)`. -/
theorem gammaCoronaConormal_tail (k : ℕ) (b : gammaCoronaClockDomain) :
    gammaCoronaConormal k
        ⟨gammaCoronaClockTail b.1, gammaCoronaClockDomain_tail b.2⟩ =
      gammaCoronaConormal (k + 1) b := by
  apply tsum_congr
  intro n
  simp only [gammaCoronaClockTail]
  congr 2

/-- Every finite periodic Fourier packet is annihilated by every functional in the cyclic Gamma
corona-conormal family. -/
theorem gammaCoronaConormal_fourierTail {r : ℕ}
    (a : Fin r → ℂ) (k : ℕ) :
    gammaCoronaConormal k
        ⟨gammaPeriodicFourierTail a,
          gammaPeriodicFourierTail_mem_coronaClockDomain a⟩ = 0 := by
  change (∑' n : ℕ, gammaPeriodicConormalCoefficient n *
    gammaPeriodicFourierTail a (n + k)) = 0
  have hzero := (gammaPeriodicFourier_shiftedTaylorConormal_hasSum a k).tsum_eq
  rw [← hzero]
  apply tsum_congr
  intro n
  simp only [gammaPeriodicConormalCoefficient, gammaPeriodicFourierTail, one_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

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

/-- **Finite transgression of the cyclic Gamma conormal.**  At resolution `N`, the coefficient
of the infinite source conormal that reaches the `i`-th retained clock coordinate is exactly the
factorial boundary symbol exposed by finite translation curvature.  Thus the finite boundary
current is not an independently chosen rank-one line: it is the visible truncation of the cyclic
source conormal. -/
theorem gammaCoronaConormal_boundaryCoefficient (N : ℕ) (i : Fin N) :
    gammaPeriodicConormalCoefficient (N - (i : ℕ) - 1) =
      gammaClockBoundaryVector N i := by
  simp only [gammaPeriodicConormalCoefficient, gammaClockBoundaryVector]
  congr 3
  omega

/-- **Boundary tomography is jointly faithful.**  Although every individual finite clock forgets
the infinite Gamma constraint, the oriented family of all finite boundary symbols uniquely
reconstructs its full factorial-tail conormal.  This is the positive inverse-limit residue of the
finite-observation no-go. -/
theorem gammaCoronaConormal_ext_of_boundaryCoefficients
    (c : ℕ → ℂ)
    (h : ∀ (N : ℕ) (i : Fin N),
      c (N - (i : ℕ) - 1) = gammaClockBoundaryVector N i) :
    c = gammaPeriodicConormalCoefficient := by
  funext k
  have hk := h (k + 1) (⟨0, Nat.succ_pos k⟩ : Fin (k + 1))
  simpa [gammaPeriodicConormalCoefficient, gammaClockBoundaryVector] using hk

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

/-! ### Exact opposite-variance Weyl seam -/

/-- The finite comparison seam between unit Taylor translation and coordinate multiplication.
The source shift changes multiplication by `z` to multiplication by `z+1`. -/
def gammaClockWeylSeam (n : ℕ) (z : ℂ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  clockComparisonSeam
    (gammaClockTranslation (n + 1))
    (gammaClockCoordinateMultiplication n z)
    (gammaClockCoordinateMultiplication n (z + 1))

@[simp] private theorem gammaClockTranslation_single
    (N : ℕ) (j i : Fin N) (c : ℂ) :
    gammaClockTranslation N (Pi.single j c : Fin N → ℂ) i =
      gammaClockTranslationCoefficient i j * c := by
  classical
  simp [gammaClockTranslation, Pi.single_apply]

private theorem gammaClockCoordinateMultiplication_single_castSucc
    (n : ℕ) (z c : ℂ) (j : Fin n) :
    gammaClockCoordinateMultiplication n z
        (Pi.single j.castSucc c : Fin (n + 1) → ℂ) =
      Pi.single j.castSucc (z * c) +
        Pi.single j.succ (((j : ℕ) + 1 : ℂ) * c) := by
  classical
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [gammaClockCoordinateMultiplication, Pi.single_apply]
  · simp [gammaClockCoordinateMultiplication, Pi.single_apply]
    split_ifs <;> simp_all

private theorem gammaClockCoordinateMultiplication_single_last
    (n : ℕ) (z c : ℂ) :
    gammaClockCoordinateMultiplication n z
        (Pi.single (Fin.last n) c : Fin (n + 1) → ℂ) =
      Pi.single (Fin.last n) (z * c) := by
  classical
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [gammaClockCoordinateMultiplication, Pi.single_apply]
  · simp [gammaClockCoordinateMultiplication, Pi.single_apply]

private theorem gammaClockWeylSeam_single (n : ℕ) (z : ℂ)
    (j i : Fin (n + 1)) :
    gammaClockWeylSeam n z
        (Pi.single j (1 : ℂ) : Fin (n + 1) → ℂ) i =
      -(n + 1 : ℂ) *
          (Pi.single j (1 : ℂ) : Fin (n + 1) → ℂ) (Fin.last n) /
        ((n + 1 - i).factorial : ℂ) := by
  classical
  simp only [gammaClockWeylSeam, clockComparisonSeam,
    LinearMap.sub_apply, LinearMap.comp_apply]
  refine Fin.lastCases ?_ (fun j0 => ?_) j
  · rw [gammaClockCoordinateMultiplication_single_last]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [gammaClockCoordinateMultiplication,
        gammaClockTranslationCoefficient]
      have hn : (((n.factorial : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hsn : ((((n + 1).factorial : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n + 1)
      field_simp [hn, hsn]
      rw [Nat.factorial_succ]
      push_cast
      ring
    · simp [gammaClockCoordinateMultiplication,
        gammaClockTranslationCoefficient]
      have hsub : n - (k : ℕ) = (n - ((k : ℕ) + 1)) + 1 := by omega
      rw [hsub]
      have hbase : (((n - ((k : ℕ) + 1)).factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n - ((k : ℕ) + 1))
      have hsucc : ((((n - ((k : ℕ) + 1) + 1).factorial : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n - ((k : ℕ) + 1) + 1)
      field_simp [hbase, hsucc]
      rw [Nat.factorial_succ]
      push_cast
      have hn : n = n - ((k : ℕ) + 1) + ((k : ℕ) + 1) := by omega
      have hnc : (n : ℂ) =
          (n - ((k : ℕ) + 1) : ℕ) + (((k : ℕ) + 1 : ℕ) : ℂ) := by
        exact_mod_cast hn
      rw [hnc]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  · rw [gammaClockCoordinateMultiplication_single_castSucc]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [gammaClockCoordinateMultiplication,
        gammaClockTranslationCoefficient]
      have hj : ((((j0 : ℕ).factorial : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (j0 : ℕ)
      have hsj : (((((j0 : ℕ) + 1).factorial : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero ((j0 : ℕ) + 1)
      field_simp [hj, hsj]
      rw [Nat.factorial_succ]
      push_cast
      ring
    · by_cases hkj : k < j0
      · have hkle : k ≤ j0 := le_of_lt hkj
        simp [gammaClockCoordinateMultiplication,
          gammaClockTranslationCoefficient, hkj, hkle]
        have hsub : (j0 : ℕ) - (k : ℕ) =
            ((j0 : ℕ) - ((k : ℕ) + 1)) + 1 := by omega
        rw [hsub]
        have hbase : ((((j0 : ℕ) - ((k : ℕ) + 1)).factorial : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero ((j0 : ℕ) - ((k : ℕ) + 1))
        have hsucc : (((((j0 : ℕ) - ((k : ℕ) + 1) + 1).factorial : ℕ) : ℂ)) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero ((j0 : ℕ) - ((k : ℕ) + 1) + 1)
        field_simp [hbase, hsucc]
        rw [Nat.factorial_succ]
        push_cast
        have hj : (j0 : ℕ) =
            (j0 : ℕ) - ((k : ℕ) + 1) + ((k : ℕ) + 1) := by omega
        have hjc : ((j0 : ℕ) : ℂ) =
            (((j0 : ℕ) - ((k : ℕ) + 1) : ℕ) : ℂ) +
              (((k : ℕ) + 1 : ℕ) : ℂ) := by
          exact_mod_cast hj
        rw [hjc]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      · by_cases hEq : k = j0
        · subst k
          simp [gammaClockCoordinateMultiplication,
            gammaClockTranslationCoefficient]
        · have hjk : j0 < k :=
            lt_of_le_of_ne (Nat.le_of_not_gt hkj) (Ne.symm hEq)
          have hnle : ¬ (k : ℕ) ≤ (j0 : ℕ) := Nat.not_le_of_gt hjk
          simp [gammaClockCoordinateMultiplication,
            gammaClockTranslationCoefficient, hkj, hjk, hnle]

/-- **Exact finite Gamma Weyl seam.**  The comparison defect between analytic unit translation and
algebraic coordinate multiplication is supported only on the omitted highest jet.  Its emitted
factorial tail has total coefficient `-(n+1)`, independently of the base coordinate. -/
theorem gammaClockWeylSeam_apply (n : ℕ) (z : ℂ)
    (a : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    gammaClockWeylSeam n z a i =
      -(n + 1 : ℂ) * a (Fin.last n) /
        ((n + 1 - i).factorial : ℂ) := by
  classical
  have ha : a = ∑ j : Fin (n + 1),
      a j • (Pi.single j (1 : ℂ) : Fin (n + 1) → ℂ) := by
    funext k
    simp [Pi.single_apply]
  calc
    gammaClockWeylSeam n z a i =
        gammaClockWeylSeam n z
          (∑ j : Fin (n + 1),
            a j • (Pi.single j (1 : ℂ) : Fin (n + 1) → ℂ)) i := by rw [← ha]
    _ = ∑ j : Fin (n + 1), a j *
          gammaClockWeylSeam n z
            (Pi.single j (1 : ℂ) : Fin (n + 1) → ℂ) i := by
      simp
    _ = -(n + 1 : ℂ) * a (Fin.last n) /
          ((n + 1 - i).factorial : ℂ) := by
      rw [Finset.sum_eq_single (Fin.last n)]
      · rw [gammaClockWeylSeam_single]
        simp
        ring
      · intro j hj hne
        rw [gammaClockWeylSeam_single]
        simp [hne]
      · simp

/-- **Cross-realization boundary-charge identity.**  The finite Weyl seam is not merely another
rank-one defect with the same dimension as the paired opposite-variance current: it is exactly
that current with reversed orientation.  The algebraic commutator and the analytic/algebraic
boundary transgression are therefore two presentations of one finite boundary charge. -/
theorem gammaClockWeylSeam_eq_neg_pairedBoundaryCurrent
    (n : ℕ) (z : ℂ) :
    gammaClockWeylSeam n z = -gammaClockPairedBoundaryCurrent n z := by
  apply LinearMap.ext
  intro a
  funext i
  rw [gammaClockWeylSeam_apply]
  simp only [LinearMap.neg_apply, Pi.neg_apply]
  rw [gammaClockPairedBoundaryCurrent_apply]
  ring

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

/-- The analytic shift cofactor with its removable value at the origin restored.  Unlike
`gammaShiftCofactorSymbol`, this completed symbol separates the constant periodic gauge from the
nonconstant periodic defect. -/
def gammaShiftCofactorEntireSymbol (z : ℂ) : ℂ :=
  if z = 0 then 1 else gammaShiftCofactorSymbol z

@[simp] theorem gammaShiftCofactorEntireSymbol_zero :
    gammaShiftCofactorEntireSymbol 0 = 1 := by
  simp [gammaShiftCofactorEntireSymbol]

/-- The completed cofactor is one on the constant gauge mode and zero on every nonconstant
nonnegative periodic Fourier mode. -/
@[simp] theorem gammaShiftCofactorEntireSymbol_periodicFrequency (m : ℕ) :
    gammaShiftCofactorEntireSymbol (gammaPeriodicFrequency m) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [gammaShiftCofactorEntireSymbol, gammaPeriodicFrequency]
  · simp [gammaShiftCofactorEntireSymbol,
      gammaPeriodicFrequency_ne_zero hm, hm]

/-- The completed shift cofactor acting on a finite periodic Fourier gauge packet. -/
def gammaShiftCofactorGaugeReduction {k : ℕ} (a : Fin k → ℂ) : ℂ :=
  ∑ m : Fin k,
    a m * gammaShiftCofactorEntireSymbol (gammaPeriodicFrequency m)

/-- **Canonical Gamma gauge reduction.**  On every nonempty finite periodic Fourier packet, the
completed global cofactor is exactly projection to the constant mode. -/
theorem gammaShiftCofactorGaugeReduction_eq_constantMode
    {k : ℕ} (a : Fin (k + 1) → ℂ) :
    gammaShiftCofactorGaugeReduction a = a 0 := by
  rw [gammaShiftCofactorGaugeReduction, Fin.sum_univ_succ]
  simp

/-- The kernel of source-canonical Gamma gauge reduction consists exactly of the nonconstant
periodic gauge packets. -/
theorem gammaShiftCofactorGaugeReduction_eq_zero_iff
    {k : ℕ} (a : Fin (k + 1) → ℂ) :
    gammaShiftCofactorGaugeReduction a = 0 ↔ a 0 = 0 := by
  rw [gammaShiftCofactorGaugeReduction_eq_constantMode]

/-- Gamma gauge reduction reaches every constant calibration target. -/
theorem gammaShiftCofactorGaugeReduction_surjective (k : ℕ) :
    Function.Surjective
      (gammaShiftCofactorGaugeReduction : (Fin (k + 1) → ℂ) → ℂ) := by
  intro c
  refine ⟨fun _ ↦ c, ?_⟩
  rw [gammaShiftCofactorGaugeReduction_eq_constantMode]

end


end GaloisForLFunctions.HTGeometry
