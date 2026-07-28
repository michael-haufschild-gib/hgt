import Mathlib
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Noncommutative tomography from a left-invertible clock compass

Let `curvature : Curv → A` be a finite family in an arbitrary associative algebra and let each
clock reporter be a scalar linear combination

`clockReporter C curvature i = ∑ a, C i a • curvature a`.

If `D` is a scalar left inverse of `C`, every curvature generator is reconstructed from the clock
reporters.  More strongly, the two induced free-algebra evaluation maps have exactly the same
range.  Hence the reporters reconstruct every ordered noncommutative word and any two state
functionals agreeing on all clock polynomials agree on all curvature polynomials.  The
degree-two antisymmetric specialization reconstructs every multiplicative commutator.

The final section proves the principal-symbol bridge needed by the physical application.  For
every split nonzero covector, the kernel of the linearized Riemann principal symbol on symmetric
metric perturbations consists exactly of pure-gauge symbols.  Together with the reporter left
inverse, complete clock data therefore lose no physical graviton polarization at principal-symbol
level.

All results are algebraic and unconditional.  A physical application must separately derive the
reporter relation and left inverse from gauge-invariant clock observables; no arbitrary family in
this file is postulated to be spacetime curvature.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A Curv Clock : Type*}

/-- Scalar linear reporter built from a finite family in an associative algebra. -/
def clockReporter
    [CommSemiring R] [Semiring A] [Algebra R A] [Fintype Curv]
    (C : Clock → Curv → R) (curvature : Curv → A) (i : Clock) : A :=
  ∑ a, C i a • curvature a

/-- A scalar left inverse reconstructs each algebra-valued generator. -/
theorem curvature_reconstruction
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0)
    (a : Curv) :
    ∑ i, D a i • clockReporter C curvature i = curvature a := by
  classical
  simp only [clockReporter, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hDC]
  simp

/-- A complete scalar reporter family has the same joint zero set as the reported family. -/
theorem clockReporter_jointKernel
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0) :
    (∀ i, clockReporter C curvature i = 0) ↔ ∀ a, curvature a = 0 := by
  constructor
  · intro hclock a
    rw [← curvature_reconstruction C D curvature hDC a]
    simp [hclock]
  · intro hcurvature i
    simp [clockReporter, hcurvature]

/-- Evaluation of noncommutative curvature polynomials. -/
def curvatureWordEval
    [CommSemiring R] [Semiring A] [Algebra R A]
    (curvature : Curv → A) :
    FreeAlgebra R Curv →ₐ[R] A :=
  FreeAlgebra.lift R curvature

/-- Evaluation of noncommutative clock-reporter polynomials. -/
def clockWordEval
    [CommSemiring R] [Semiring A] [Algebra R A] [Fintype Curv]
    (C : Clock → Curv → R) (curvature : Curv → A) :
    FreeAlgebra R Clock →ₐ[R] A :=
  FreeAlgebra.lift R (clockReporter C curvature)

/-- Recode each curvature generator as its left-inverse clock combination. -/
def curvatureToClockCode
    [CommSemiring R] [Fintype Clock]
    (D : Curv → Clock → R) :
    FreeAlgebra R Curv →ₐ[R] FreeAlgebra R Clock :=
  FreeAlgebra.lift R (fun a => ∑ i, D a i • FreeAlgebra.ι R i)

/-- Recode each clock reporter as its defining curvature combination. -/
def clockToCurvatureCode
    [CommSemiring R] [Fintype Curv]
    (C : Clock → Curv → R) :
    FreeAlgebra R Clock →ₐ[R] FreeAlgebra R Curv :=
  FreeAlgebra.lift R (fun i => ∑ a, C i a • FreeAlgebra.ι R a)

/-- Every ordered curvature polynomial evaluates as a recoded clock polynomial. -/
theorem clockWordEval_comp_curvatureToClockCode
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0) :
    (clockWordEval C curvature).comp (curvatureToClockCode D) =
      curvatureWordEval curvature := by
  apply FreeAlgebra.hom_ext
  funext a
  simp only [Function.comp_apply, AlgHom.coe_comp, curvatureToClockCode,
    FreeAlgebra.lift_ι_apply, map_sum, map_smul, clockWordEval,
    curvatureWordEval]
  exact curvature_reconstruction C D curvature hDC a

/-- Every ordered clock polynomial evaluates as its defining curvature polynomial. -/
theorem curvatureWordEval_comp_clockToCurvatureCode
    [CommSemiring R] [Semiring A] [Algebra R A] [Fintype Curv]
    (C : Clock → Curv → R) (curvature : Curv → A) :
    (curvatureWordEval curvature).comp (clockToCurvatureCode C) =
      clockWordEval C curvature := by
  apply FreeAlgebra.hom_ext
  funext i
  simp [Function.comp_apply, clockToCurvatureCode, curvatureWordEval,
    clockWordEval, clockReporter]

/-- **Complete noncommutative clock-compass tomography.**  The reporter and curvature
free-algebra evaluations generate exactly the same associative subalgebra. -/
theorem curvatureWordEval_range_eq_clockWordEval_range
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0) :
    (curvatureWordEval curvature).range =
      (clockWordEval C curvature).range := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    refine ⟨curvatureToClockCode D p, ?_⟩
    exact DFunLike.congr_fun
      (clockWordEval_comp_curvatureToClockCode C D curvature hDC) p
  · rintro x ⟨q, rfl⟩
    refine ⟨clockToCurvatureCode C q, ?_⟩
    exact DFunLike.congr_fun
      (curvatureWordEval_comp_clockToCurvatureCode C curvature) q

/-- Agreement of arbitrary state/readout functionals on all clock polynomials forces agreement
on all ordered curvature polynomials.  No positivity or commutativity is assumed. -/
theorem states_agree_on_curvature_words_of_agree_on_clock_words
    [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    {S : Type*}
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0)
    (state₁ state₂ : A → S)
    (hstate : ∀ q : FreeAlgebra R Clock,
      state₁ (clockWordEval C curvature q) =
        state₂ (clockWordEval C curvature q)) :
    ∀ p : FreeAlgebra R Curv,
      state₁ (curvatureWordEval curvature p) =
        state₂ (curvatureWordEval curvature p) := by
  intro p
  rw [← DFunLike.congr_fun
    (clockWordEval_comp_curvatureToClockCode C D curvature hDC) p]
  exact hstate (curvatureToClockCode D p)

/-- Multiplicative commutator in an arbitrary ring. -/
def mulCommutator [Ring A] (x y : A) : A :=
  x * y - y * x

/-- Degree-two antisymmetric specialization of complete clock-compass tomography. -/
theorem curvature_commutator_reconstruction
    [CommRing R] [Ring A] [Algebra R A]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → R) (D : Curv → Clock → R)
    (curvature : Curv → A)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0)
    (a b : Curv) :
    mulCommutator (curvature a) (curvature b) =
      ∑ i, ∑ j,
        (D a i * D b j) •
          mulCommutator (clockReporter C curvature i)
            (clockReporter C curvature j) := by
  let k := clockReporter C curvature
  have hprod (u v : Clock → R) :
      (∑ i, u i • k i) * (∑ j, v j • k j) =
        ∑ i, ∑ j, (u i * v j) • (k i * k j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [smul_smul, mul_comm]
  rw [← curvature_reconstruction C D curvature hDC a,
    ← curvature_reconstruction C D curvature hDC b]
  simp only [mulCommutator]
  rw [hprod, hprod]
  simp only [Finset.sum_sub_distrib, smul_sub]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (D b j) (D a i)]

section DifferentialPhase

open GaloisForLFunctions
open scoped Differential

/-- Differential algebraicity is closed under the finite sums used below. -/
theorem differentialAlgebraicOver_finset_sum_clock
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {s : Finset ι} {f : ι → E}
    (hf : ∀ i ∈ s, DifferentialAlgebraicOver F (f i)) :
    DifferentialAlgebraicOver F (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using differentialAlgebraicOver_algebraMap (F := F) (E := E) 0
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact differentialAlgebraicOver_add (hf i (by simp))
        (ih fun j hj => hf j (by simp [hj]))

/-- Differential algebraicity is closed under finite clock-reporter sums. -/
theorem differentialAlgebraicOver_clockReporter
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [Fintype Curv]
    (C : Clock → Curv → F) (curvature : Curv → E)
    (hcurvature : ∀ a, DifferentialAlgebraicOver F (curvature a))
    (i : Clock) :
    DifferentialAlgebraicOver F (clockReporter C curvature i) := by
  unfold clockReporter
  apply differentialAlgebraicOver_finset_sum_clock
  intro a _
  rw [Algebra.smul_def]
  exact differentialAlgebraicOver_mul
    (differentialAlgebraicOver_algebraMap (C i a)) (hcurvature a)

/-- **Clock-compass differential-phase invariance.**  A scalar-left-invertible clock compass is
differentially algebraic in every channel exactly when the reconstructed curvature family is.
Thus calibration cannot create or hide a hypertranscendental sector. -/
theorem clockReporter_differentialAlgebraic_phase_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → F) (D : Curv → Clock → F)
    (curvature : Curv → E)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0) :
    (∀ i, DifferentialAlgebraicOver F (clockReporter C curvature i)) ↔
      ∀ a, DifferentialAlgebraicOver F (curvature a) := by
  constructor
  · intro hclock a
    have hreconstruct :
        curvature a =
          ∑ i, algebraMap F E (D a i) * clockReporter C curvature i := by
      rw [← curvature_reconstruction C D curvature hDC a]
      simp only [Algebra.smul_def]
    rw [hreconstruct]
    apply differentialAlgebraicOver_finset_sum_clock
    intro i _
    exact differentialAlgebraicOver_mul
      (differentialAlgebraicOver_algebraMap (D a i)) (hclock i)
  · intro hcurvature i
    exact differentialAlgebraicOver_clockReporter C curvature hcurvature i

/-- A complete clock compass exposes a hypertranscendental channel exactly when its reconstructed
curvature family does.  The result permits cancellations in individual reporters; only the
complete family has an invariant HT/DA phase. -/
theorem exists_hypertranscendental_clockReporter_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [Fintype Curv] [DecidableEq Curv] [Fintype Clock]
    (C : Clock → Curv → F) (D : Curv → Clock → F)
    (curvature : Curv → E)
    (hDC : ∀ a b, ∑ i, D a i * C i b = if a = b then 1 else 0) :
    (∃ i, HypertranscendentalOver F (clockReporter C curvature i)) ↔
      ∃ a, HypertranscendentalOver F (curvature a) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    by_contra hnone
    have hcurvatureDA : ∀ a, DifferentialAlgebraicOver F (curvature a) := by
      intro a
      by_contra ha
      exact hnone ⟨a, ha⟩
    have hclock :=
      (clockReporter_differentialAlgebraic_phase_iff C D curvature hDC).2 hcurvatureDA
    exact hi (hclock i)
  · rintro ⟨a, ha⟩
    by_contra hnone
    have hclockDA :
        ∀ i, DifferentialAlgebraicOver F (clockReporter C curvature i) := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    have hcurvature :=
      (clockReporter_differentialAlgebraic_phase_iff C D curvature hDC).1 hclockDA
    exact ha (hcurvature a)

end DifferentialPhase

section LinearizedCurvatureSymbol

variable {K V : Type*} [Field K]
variable [AddCommGroup V] [Module K V]

/-- Twice the principal symbol of the linearized Riemann operator.  The factor two is removed so
the kernel theorem is proved without carrying a harmless denominator through its four terms. -/
def doubledLinearizedRiemannSymbol
    (ξ : V →ₗ[K] K) (h : V →ₗ[K] V →ₗ[K] K)
    (a b c d : V) : K :=
  ξ c * ξ b * h a d + ξ d * ξ a * h b c
    - ξ d * ξ b * h a c - ξ c * ξ a * h b d

/-- Every infinitesimal metric gauge symbol lies in the kernel of the linearized Riemann symbol. -/
theorem doubledLinearizedRiemannSymbol_pureGauge
    (ξ v : V →ₗ[K] K)
    (h : V →ₗ[K] V →ₗ[K] K)
    (hgauge : ∀ x y, h x y = ξ x * v y + ξ y * v x) :
    ∀ a b c d, doubledLinearizedRiemannSymbol ξ h a b c d = 0 := by
  intro a b c d
  simp only [doubledLinearizedRiemannSymbol, hgauge]
  ring

/-- For a split nonzero covector, the pure-gauge principal-symbol parametrization is faithful. -/
theorem pureGaugeMetricSymbol_ext
    [CharZero K]
    (ξ : V →ₗ[K] K) (n : V) (hξn : ξ n = 1)
    (v w : V →ₗ[K] K)
    (heq : ∀ x y, ξ x * v y + ξ y * v x =
      ξ x * w y + ξ y * w x) :
    v = w := by
  apply LinearMap.ext
  intro y
  have hnn := heq n n
  have hny := heq n y
  rw [hξn, one_mul, one_mul] at hnn hny
  have hn : v n = w n := by
    linear_combination hnn / 2
  linear_combination hny - ξ y * hn

/-- **Exact principal-symbol kernel of linearized gravity.**  If `n` splits the nonzero covector
`ξ`, then a symmetric metric symbol has zero linearized Riemann symbol exactly when it is a
pure-gauge symbol `ξ ⊗ v + v ⊗ ξ`.  Thus curvature loses gauge and no other polarization. -/
theorem doubledLinearizedRiemannSymbol_vanishes_iff_pureGauge
    [CharZero K]
    (ξ : V →ₗ[K] K) (n : V) (h : V →ₗ[K] V →ₗ[K] K)
    (hξn : ξ n = 1)
    (hsym : ∀ x y, h x y = h y x) :
    (∀ a b c d, doubledLinearizedRiemannSymbol ξ h a b c d = 0) ↔
      ∃ v : V →ₗ[K] K, ∀ x y, h x y = ξ x * v y + ξ y * v x := by
  constructor
  · intro hzero
    let v : V →ₗ[K] K := h n - (h n n / 2) • ξ
    refine ⟨v, ?_⟩
    intro x y
    let x₀ : V := x - ξ x • n
    let y₀ : V := y - ξ y • n
    have hξx₀ : ξ x₀ = 0 := by
      simp [x₀, hξn]
    have hξy₀ : ξ y₀ = 0 := by
      simp [y₀, hξn]
    have htrans : h x₀ y₀ = 0 := by
      have hs := hzero x₀ n y₀ n
      simp [doubledLinearizedRiemannSymbol, hξn, hξx₀, hξy₀] at hs
      exact hs
    simp only [v, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    have hexpand :
        h x₀ y₀ =
          h x y - ξ y * h x n - ξ x * h n y + ξ x * ξ y * h n n := by
      simp only [x₀, y₀, map_sub, LinearMap.map_smul_of_tower,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsym x n]
      ring
    rw [hexpand] at htrans
    rw [hsym x n] at htrans
    linear_combination htrans
  · rintro ⟨v, hgauge⟩
    exact doubledLinearizedRiemannSymbol_pureGauge ξ v h hgauge

end LinearizedCurvatureSymbol

end

end GaloisForLFunctions.HTGeometry
