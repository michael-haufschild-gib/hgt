import GaloisForLFunctions.HTGeometry.TwoLocalPauliAnticommutingFan
import GaloisForLFunctions.HTGeometry.PauliCommutatorCoefficient
import GaloisForLFunctions.HTGeometry.PauliLabelGraphGeneration
import GaloisForLFunctions.HTGeometry.GaussianAffineStableRankLowerTail

open scoped BigOperators
open Finset Matrix
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem optPhase_eq_conjugationSign_mul_swap
    (q p : Option (Fin 3)) :
    optPhase q p = boolPauliConjugationSign q p * optPhase p q := by
  fin_cases q <;> fin_cases p <;>
    norm_num +decide [optPhase, boolPauliConjugationSign]

theorem optPhaseProd_eq_conjugationSign_mul_swap
    {σ : Type*} [Fintype σ]
    (Q P : σ → Option (Fin 3)) :
    optPhaseProd Q P = finitePauliConjugationSign Q P * optPhaseProd P Q := by
  rw [optPhaseProd, optPhaseProd, finitePauliConjugationSign,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ =>
    optPhase_eq_conjugationSign_mul_swap (Q s) (P s)

theorem norm_optPhase (q p : Option (Fin 3)) :
    ‖optPhase q p‖ = 1 := by
  fin_cases q <;> fin_cases p <;>
    norm_num +decide [optPhase]

theorem norm_optPhaseProd
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) :
    ‖optPhaseProd Q P‖ = 1 := by
  rw [optPhaseProd, norm_prod]
  simp [norm_optPhase]

theorem norm_optPhaseProd_sub_swap_of_conjugationSign_eq_neg_one
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {Q P : σ → Option (Fin 3)}
    (hanti : finitePauliConjugationSign Q P = -1) :
    ‖optPhaseProd Q P - optPhaseProd P Q‖ = 2 := by
  rw [optPhaseProd_eq_conjugationSign_mul_swap, hanti]
  have hrewrite :
      (-1 : ℂ) * optPhaseProd P Q - optPhaseProd P Q =
        (-2 : ℂ) * optPhaseProd P Q := by ring
  rw [hrewrite, norm_mul, norm_optPhaseProd]
  norm_num

theorem complex_affine_real_projection_sq_le
    (c b : ℂ) (hc : c ≠ 0) (x : ℝ) :
    ‖c‖ ^ 2 * (x - (-(b / c).re)) ^ 2 ≤
      ‖(x : ℂ) * c + b‖ ^ 2 := by
  have hfactor : (x : ℂ) * c + b = c * ((x : ℂ) + b / c) := by
    field_simp
  rw [hfactor, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖c‖)
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_add, sub_neg_eq_add]
  nlinarith [sq_nonneg (b / c).im]

def complexAffineGaussianWeight (c : ℂ) : ℝ≥0 :=
  ⟨‖c‖ ^ 2, sq_nonneg ‖c‖⟩

/-- Product-Gaussian affine lower tail for independent real coefficients
observed in arbitrary complex channels. -/
theorem measure_pi_gaussian_complex_affine_sq_sum_le
    {I : Type*} [Fintype I] (c b : I → ℂ)
    (hc : ∀ i, c i ≠ 0) {θ : ℝ}
    (hθ : θ ≤ gaussianIntervalActivationMass) :
    (Measure.pi fun _ : I => gaussianReal 0 1).real
        {x | ∑ i, ‖(x i : ℂ) * c i + b i‖ ^ 2 ≤
          θ * ∑ i, (complexAffineGaussianWeight (c i) : ℝ)} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i, (complexAffineGaussianWeight (c i) : ℝ)) ^ 2 /
          ∑ i, (complexAffineGaussianWeight (c i) : ℝ) ^ 2) := by
  let center : I → ℝ := fun i => -((b i / c i).re)
  have hbase := measure_pi_gaussian_weighted_shifted_sq_sum_le
    (fun i => complexAffineGaussianWeight (c i)) center hθ
  apply (measureReal_mono ?_).trans hbase
  intro x hx
  have hsum :
      ∑ i, (complexAffineGaussianWeight (c i) : ℝ) *
          (x i - center i) ^ 2 ≤
        ∑ i, ‖(x i : ℂ) * c i + b i‖ ^ 2 := by
    exact Finset.sum_le_sum fun i _ =>
      complex_affine_real_projection_sq_le (c i) (b i) (hc i) (x i)
  exact hsum.trans hx

theorem optMulLabel_right_injective
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    Function.Injective fun Q : σ → Option (Fin 3) => optMulLabel Q P := by
  intro Q R hQR
  have hQR' : optMulLabel P Q = optMulLabel P R := by
    calc
      optMulLabel P Q = optMulLabel Q P := optMulLabel_comm Q P
      _ = optMulLabel R P := hQR
      _ = optMulLabel P R := (optMulLabel_comm R P).symm
  calc
    Q = optMulLabel P (optMulLabel P Q) :=
      (optMulLabel_optMulLabel_self P Q).symm
    _ = optMulLabel P (optMulLabel P R) := congrArg (optMulLabel P) hQR'
    _ = R := optMulLabel_optMulLabel_self P R

def localPauliAnticommutingFanHamiltonian
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (x : {j : Fin n // j ≠ firstActivePauliSite P} → ℝ) :
    Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ :=
  ∑ j, (x j : ℂ) •
    finitePauliMatrix (localPauliAnticommutingFanLabel P j)

theorem trace_localPauliAnticommutingFan_commutator
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (x : {j : Fin n // j ≠ firstActivePauliSite P} → ℝ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    Matrix.trace
        (finitePauliMatrix
            (optMulLabel (localPauliAnticommutingFanLabel P k) P.1) *
          (localPauliAnticommutingFanHamiltonian P x * finitePauliMatrix P.1 -
            finitePauliMatrix P.1 * localPauliAnticommutingFanHamiltonian P x)) =
      (x k : ℂ) *
        (optPhaseProd (localPauliAnticommutingFanLabel P k) P.1 -
          optPhaseProd P.1 (localPauliAnticommutingFanLabel P k)) *
        (2 : ℂ) ^ n := by
  have htrace := trace_pauli_commutator_sum
    (R := optMulLabel (localPauliAnticommutingFanLabel P k) P.1)
    (S := localPauliAnticommutingFanLabel P)
    (T := fun _ : Unit => P.1)
    (h := fun j => (x j : ℂ)) (k := fun _ => 1)
  simp only [Fintype.sum_unique, one_smul] at htrace
  change Matrix.trace
      (finitePauliMatrix
          (optMulLabel (localPauliAnticommutingFanLabel P k) P.1) *
        ((∑ j, (x j : ℂ) •
            finitePauliMatrix (localPauliAnticommutingFanLabel P j)) *
            finitePauliMatrix P.1 -
          finitePauliMatrix P.1 *
            (∑ j, (x j : ℂ) •
              finitePauliMatrix (localPauliAnticommutingFanLabel P j)))) = _
  rw [htrace]
  rw [Finset.sum_eq_single k]
  · simp
    ring
  · intro j _ hjk
    have hlabels :
        optMulLabel (localPauliAnticommutingFanLabel P k) P.1 ≠
          optMulLabel (localPauliAnticommutingFanLabel P j) P.1 := by
      intro h
      have hfan := optMulLabel_right_injective P.1 h
      exact hjk (localPauliAnticommutingFanLabel_injective P hfan).symm
    simp [hlabels]
  · simp

theorem norm_localPauliAnticommutingFan_phaseDifference
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    ‖optPhaseProd (localPauliAnticommutingFanLabel P k) P.1 -
        optPhaseProd P.1 (localPauliAnticommutingFanLabel P k)‖ = 2 := by
  exact norm_optPhaseProd_sub_swap_of_conjugationSign_eq_neg_one
    (finitePauliConjugationSign_localPauliAnticommutingFanLabel P k)

def localPauliAnticommutingFanCommutatorScale
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) : ℂ :=
  (optPhaseProd (localPauliAnticommutingFanLabel P k) P.1 -
      optPhaseProd P.1 (localPauliAnticommutingFanLabel P k)) *
    (2 : ℂ) ^ n

theorem norm_localPauliAnticommutingFanCommutatorScale
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    ‖localPauliAnticommutingFanCommutatorScale P k‖ =
      2 * (2 : ℝ) ^ n := by
  rw [localPauliAnticommutingFanCommutatorScale, norm_mul,
    norm_localPauliAnticommutingFan_phaseDifference, norm_pow]
  norm_num

theorem trace_localPauliAnticommutingFan_commutator_affine
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (B : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : {j : Fin n // j ≠ firstActivePauliSite P} → ℝ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    Matrix.trace
        (finitePauliMatrix
            (optMulLabel (localPauliAnticommutingFanLabel P k) P.1) *
          ((localPauliAnticommutingFanHamiltonian P x + B) * finitePauliMatrix P.1 -
            finitePauliMatrix P.1 * (localPauliAnticommutingFanHamiltonian P x + B))) =
      (x k : ℂ) *
          (optPhaseProd (localPauliAnticommutingFanLabel P k) P.1 -
            optPhaseProd P.1 (localPauliAnticommutingFanLabel P k)) *
          (2 : ℂ) ^ n +
        Matrix.trace
          (finitePauliMatrix
              (optMulLabel (localPauliAnticommutingFanLabel P k) P.1) *
            (B * finitePauliMatrix P.1 - finitePauliMatrix P.1 * B)) := by
  have hsplit :
      (localPauliAnticommutingFanHamiltonian P x + B) * finitePauliMatrix P.1 -
          finitePauliMatrix P.1 * (localPauliAnticommutingFanHamiltonian P x + B) =
        (localPauliAnticommutingFanHamiltonian P x * finitePauliMatrix P.1 -
            finitePauliMatrix P.1 * localPauliAnticommutingFanHamiltonian P x) +
          (B * finitePauliMatrix P.1 - finitePauliMatrix P.1 * B) := by
    noncomm_ring
  rw [hsplit, Matrix.mul_add, Matrix.trace_add,
    trace_localPauliAnticommutingFan_commutator]

def localPauliAnticommutingFanCommutatorDrift
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (B : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) : ℂ :=
  Matrix.trace
    (finitePauliMatrix
        (optMulLabel (localPauliAnticommutingFanLabel P k) P.1) *
      (B * finitePauliMatrix P.1 - finitePauliMatrix P.1 * B))

def localPauliAnticommutingFanCommutatorCoordinate
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (B : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : {j : Fin n // j ≠ firstActivePauliSite P} → ℝ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) : ℂ :=
  Matrix.trace
    (finitePauliMatrix
        (optMulLabel (localPauliAnticommutingFanLabel P k) P.1) *
      ((localPauliAnticommutingFanHamiltonian P x + B) * finitePauliMatrix P.1 -
        finitePauliMatrix P.1 * (localPauliAnticommutingFanHamiltonian P x + B)))

theorem localPauliAnticommutingFanCommutatorCoordinate_eq_affine
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (B : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : {j : Fin n // j ≠ firstActivePauliSite P} → ℝ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    localPauliAnticommutingFanCommutatorCoordinate P B x k =
      (x k : ℂ) * localPauliAnticommutingFanCommutatorScale P k +
        localPauliAnticommutingFanCommutatorDrift P B k := by
  rw [localPauliAnticommutingFanCommutatorCoordinate,
    localPauliAnticommutingFanCommutatorScale,
    localPauliAnticommutingFanCommutatorDrift,
    trace_localPauliAnticommutingFan_commutator_affine]
  ring

/-- Quenched active-fan tube law.  After every omitted Hamiltonian coefficient
is frozen into `B`, a fixed nonidentity Pauli target still has an
`exp(-c (n-1))` lower-tail bound. -/
theorem measure_localPauliAnticommutingFanCommutator_sq_sum_le
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (B : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (Measure.pi fun _ : {j : Fin n // j ≠ firstActivePauliSite P} =>
        gaussianReal 0 1).real
      {x | ∑ k, ‖localPauliAnticommutingFanCommutatorCoordinate P B x k‖ ^ 2 ≤
        θ * ((n - 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ n) ^ 2} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 * (n - 1 : ℕ)) := by
  let c := localPauliAnticommutingFanCommutatorScale P
  let b := localPauliAnticommutingFanCommutatorDrift P B
  have hc : ∀ k, c k ≠ 0 := by
    intro k hk
    have hnorm := norm_localPauliAnticommutingFanCommutatorScale P k
    change ‖c k‖ = 2 * (2 : ℝ) ^ n at hnorm
    rw [hk, norm_zero] at hnorm
    have hpos : 0 < 2 * (2 : ℝ) ^ n := by positivity
    linarith
  have hbase := measure_pi_gaussian_complex_affine_sq_sum_le c b hc hθ
  have hweight : ∀ k,
      (complexAffineGaussianWeight (c k) : ℝ) =
        (2 * (2 : ℝ) ^ n) ^ 2 := by
    intro k
    change ‖c k‖ ^ 2 = _
    rw [show ‖c k‖ = 2 * (2 : ℝ) ^ n by
      exact norm_localPauliAnticommutingFanCommutatorScale P k]
  have hcard : Fintype.card
      {j : Fin n // j ≠ firstActivePauliSite P} = n - 1 :=
    card_sites_ne_firstActivePauliSite P
  have hratio :
      (∑ k, (complexAffineGaussianWeight (c k) : ℝ)) ^ 2 /
          ∑ k, (complexAffineGaussianWeight (c k) : ℝ) ^ 2 =
        ((n - 1 : ℕ) : ℝ) := by
    simp_rw [hweight]
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, hcard]
    by_cases hm : n - 1 = 0
    · simp [hm]
    · have hmpos : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hapos : 0 < (2 * (2 : ℝ) ^ n) ^ 2 := by positivity
      field_simp
      ring
  have hsum :
      ∑ k, (complexAffineGaussianWeight (c k) : ℝ) =
        ((n - 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ n) ^ 2 := by
    simp_rw [hweight]
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  have hexponent :
      -2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ k, (complexAffineGaussianWeight (c k) : ℝ)) ^ 2 /
          ∑ k, (complexAffineGaussianWeight (c k) : ℝ) ^ 2 =
        -2 * (gaussianIntervalActivationMass - θ) ^ 2 *
          ((n - 1 : ℕ) : ℝ) := by
    calc
      -2 * (gaussianIntervalActivationMass - θ) ^ 2 *
              (∑ k, (complexAffineGaussianWeight (c k) : ℝ)) ^ 2 /
            ∑ k, (complexAffineGaussianWeight (c k) : ℝ) ^ 2 =
          (-2 * (gaussianIntervalActivationMass - θ) ^ 2) *
            ((∑ k, (complexAffineGaussianWeight (c k) : ℝ)) ^ 2 /
              ∑ k, (complexAffineGaussianWeight (c k) : ℝ) ^ 2) := by ring
      _ = -2 * (gaussianIntervalActivationMass - θ) ^ 2 *
          ((n - 1 : ℕ) : ℝ) := by rw [hratio]
  rw [hexponent, hsum] at hbase
  simpa only [c, b,
    localPauliAnticommutingFanCommutatorCoordinate_eq_affine,
    mul_assoc] using hbase

/-- A uniform conditional real-measure bound survives integration over an
arbitrary independent probability space. -/
theorem measureReal_prod_le_of_forall_section_le
    {I A : Type*} [MeasurableSpace I] [MeasurableSpace A]
    {μ : Measure I} {ν : Measure A}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set (I × A)} (hS : MeasurableSet S)
    {p : ℝ} (hp : 0 ≤ p)
    (hsec : ∀ y, ν.real (Prod.mk y ⁻¹' S) ≤ p) :
    (μ.prod ν).real S ≤ p := by
  have hsecENN : ∀ y, ν (Prod.mk y ⁻¹' S) ≤ ENNReal.ofReal p := by
    intro y
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    simpa [Measure.real, ENNReal.toReal_ofReal hp] using hsec y
  have hbound : (μ.prod ν) S ≤ ENNReal.ofReal p := by
    rw [Measure.prod_apply hS]
    calc
      (∫⁻ y, ν (Prod.mk y ⁻¹' S) ∂μ) ≤
          ∫⁻ _y, ENNReal.ofReal p ∂μ := lintegral_mono hsecENN
      _ = ENNReal.ofReal p := by simp
  change ((μ.prod ν) S).toReal ≤ p
  rw [← ENNReal.toReal_ofReal hp]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

/-- Quenched affine Gaussian lower tail integrated over any independent
random drift. -/
theorem measure_prod_pi_gaussian_complex_affine_sq_sum_le
    {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype I]
    (c : I → ℂ) (b : Ω → I → ℂ)
    (hc : ∀ i, c i ≠ 0)
    (hb : ∀ i, Measurable fun ω => b ω i)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (μ.prod (Measure.pi fun _ : I => gaussianReal 0 1)).real
        {p | ∑ i, ‖(p.2 i : ℂ) * c i + b p.1 i‖ ^ 2 ≤
          θ * ∑ i, (complexAffineGaussianWeight (c i) : ℝ)} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i, (complexAffineGaussianWeight (c i) : ℝ)) ^ 2 /
          ∑ i, (complexAffineGaussianWeight (c i) : ℝ) ^ 2) := by
  have hS : MeasurableSet
      {p : Ω × (I → ℝ) |
        ∑ i, ‖(p.2 i : ℂ) * c i + b p.1 i‖ ^ 2 ≤
          θ * ∑ i, (complexAffineGaussianWeight (c i) : ℝ)} := by
    apply measurableSet_le
    · fun_prop
    · exact measurable_const
  apply measureReal_prod_le_of_forall_section_le hS (Real.exp_nonneg _)
  intro ω
  change (Measure.pi fun _ : I => gaussianReal 0 1).real
      {x | ∑ i, ‖(x i : ℂ) * c i + b ω i‖ ^ 2 ≤
        θ * ∑ i, (complexAffineGaussianWeight (c i) : ℝ)} ≤ _
  exact measure_pi_gaussian_complex_affine_sq_sum_le c (b ω) hc hθ

/-- Full quenched law: the active-fan exponent survives integration over any
independent random inactive Hamiltonian, with no bound on its drift. -/
theorem measure_prod_localPauliAnticommutingFanCommutator_sq_sum_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (B : Ω → Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (hB : ∀ k, Measurable fun ω =>
      localPauliAnticommutingFanCommutatorDrift P (B ω) k)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (μ.prod (Measure.pi fun _ : {j : Fin n // j ≠ firstActivePauliSite P} =>
        gaussianReal 0 1)).real
      {p | ∑ k,
          ‖localPauliAnticommutingFanCommutatorCoordinate P (B p.1) p.2 k‖ ^ 2 ≤
        θ * ((n - 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ n) ^ 2} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 * (n - 1 : ℕ)) := by
  have hS : MeasurableSet
      {p : Ω × ({j : Fin n // j ≠ firstActivePauliSite P} → ℝ) |
        ∑ k,
            ‖localPauliAnticommutingFanCommutatorCoordinate P (B p.1) p.2 k‖ ^ 2 ≤
          θ * ((n - 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ n) ^ 2} := by
    simp_rw [localPauliAnticommutingFanCommutatorCoordinate_eq_affine]
    apply measurableSet_le
    · refine Finset.measurable_sum _ fun k _ => ?_
      have hx : Measurable fun p :
          Ω × ({j : Fin n // j ≠ firstActivePauliSite P} → ℝ) =>
          (p.2 k : ℂ) := by fun_prop
      have hdrift : Measurable fun p :
          Ω × ({j : Fin n // j ≠ firstActivePauliSite P} → ℝ) =>
          localPauliAnticommutingFanCommutatorDrift P (B p.1) k :=
        (hB k).comp measurable_fst
      exact ((hx.mul measurable_const).add hdrift).norm.pow_const 2
    · exact measurable_const
  apply measureReal_prod_le_of_forall_section_le hS (Real.exp_nonneg _)
  intro ω
  change (Measure.pi fun _ : {j : Fin n // j ≠ firstActivePauliSite P} =>
      gaussianReal 0 1).real
    {x | ∑ k,
        ‖localPauliAnticommutingFanCommutatorCoordinate P (B ω) x k‖ ^ 2 ≤
      θ * ((n - 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ n) ^ 2} ≤ _
  exact measure_localPauliAnticommutingFanCommutator_sq_sum_le P (B ω) hθ

end

end GaloisForLFunctions.HTGeometry
