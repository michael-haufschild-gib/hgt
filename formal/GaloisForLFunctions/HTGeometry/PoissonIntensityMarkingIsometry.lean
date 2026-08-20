import GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle
import GaloisForLFunctions.HTGeometry.BoundedConservationBlindness

/-!
# Poisson intensity information and the common-marking isometry

Relative entropy is additive over independent products, so the relative entropy of two independent
Poisson packets is the extended (unnormalized) intensity divergence.  Marking each source particle
by a row-stochastic kernel leaves that divergence unchanged, and probability normalization splits
it into a shape term and an extensive mass term.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

/-! ## Additivity of relative entropy over independent products -/

/-- **Relative entropy is additive over independent products.** -/
theorem klDiv_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ₁ ν₁ : Measure X) (μ₂ ν₂ : Measure Y)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  rw [← Measure.compProd_const (μ := μ₁) (ν := μ₂), ← Measure.compProd_const (μ := ν₁) (ν := ν₂),
    klDiv_compProd_eq_add, Measure.compProd_const, Measure.compProd_const]
  congr 1
  have hswap : MeasurableEmbedding (Prod.swap : Y × X → X × Y) :=
    (MeasurableEquiv.prodComm).measurableEmbedding
  rw [show μ₁.prod μ₂ = Measure.map Prod.swap (μ₂.prod μ₁) from Measure.prod_swap.symm,
    show μ₁.prod ν₂ = Measure.map Prod.swap (ν₂.prod μ₁) from Measure.prod_swap.symm,
    klDiv_map_measurableEmbedding hswap, ← Measure.compProd_const, ← Measure.compProd_const,
    klDiv_compProd_left]

/-- **Relative entropy is additive over finite independent packets.** -/
theorem klDiv_pi {n : ℕ} {Z : Type*} [MeasurableSpace Z] (μ ν : Fin n → Measure Z)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  induction n with
  | zero =>
      have : Measure.pi μ = Measure.pi ν := by
        refine Measure.ext fun s _ => ?_
        have h1 : IsProbabilityMeasure (Measure.pi μ) := inferInstance
        have h2 : IsProbabilityMeasure (Measure.pi ν) := inferInstance
        rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
        · simp
        · have hs : s = Set.univ := by
            ext y
            simp [Subsingleton.elim y x, hx]
          rw [hs, measure_univ, measure_univ]
      rw [this, klDiv_self]
      simp
  | succ k ih =>
      have hmp := measurePreserving_piFinSuccAbove μ 0
      have hnp := measurePreserving_piFinSuccAbove ν 0
      have hemb : MeasurableEmbedding
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Z) 0) :=
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Z) 0).measurableEmbedding
      rw [← klDiv_map_measurableEmbedding hemb, hmp.map_eq, hnp.map_eq, klDiv_prod,
        ih (fun j => μ ((0 : Fin (k + 1)).succAbove j)) (fun j => ν ((0 : Fin (k + 1)).succAbove j)),
        Fin.sum_univ_succ]
      simp

/-! ## The intensity divergence -/

/-- Extended (unnormalized) relative entropy of positive intensity vectors. -/
def intensityDiv {I : Type*} [Fintype I] (a b : I → ℝ) : ℝ :=
  ∑ i, (a i * Real.log (a i / b i) - a i + b i)

/-- **Poisson packet information is the intensity divergence.** -/
theorem toReal_klDiv_poissonPacket {n : ℕ} (a b : Fin n → ℝ≥0) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) :
    (klDiv (Measure.pi fun i => Po(a i)) (Measure.pi fun i => Po(b i))).toReal
      = intensityDiv (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) := by
  rw [klDiv_pi, ENNReal.toReal_sum fun i _ => klDiv_poissonMeasure_ne_top (ha i) (hb i),
    intensityDiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toReal_klDiv_poissonMeasure (ha i) (hb i)]
  ring

/-- **Common-marking isometry.**  Marking each source particle by a row-stochastic kernel leaves
the intensity divergence unchanged. -/
theorem intensityDiv_marking {I J : Type*} [Fintype I] [Fintype J] (a b : I → ℝ) (K : I → J → ℝ)
    (hK0 : ∀ i j, 0 ≤ K i j) (hK1 : ∀ i, ∑ j, K i j = 1) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    intensityDiv (fun q : I × J => a q.1 * K q.1 q.2) (fun q : I × J => b q.1 * K q.1 q.2)
      = intensityDiv a b := by
  rw [intensityDiv, intensityDiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ∀ j ∈ Finset.univ,
      a i * K i j * Real.log (a i * K i j / (b i * K i j)) - a i * K i j + b i * K i j
        = K i j * (a i * Real.log (a i / b i) - a i + b i) := by
    intro j _
    rcases eq_or_lt_of_le (hK0 i j) with h | h
    · rw [← h]
      simp
    · have hane : a i ≠ 0 := (ha i).ne'
      have hbne : b i ≠ 0 := (hb i).ne'
      have hkne : K i j ≠ 0 := h.ne'
      rw [show a i * K i j / (b i * K i j) = a i / b i from by field_simp]
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hK1 i, one_mul]

/-- **Mass--shape decomposition.**  Probability normalization retains the shape term and isolates
the extensive mass coordinate. -/
theorem intensityDiv_mass_shape {I : Type*} [Fintype I] (a b : I → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hA : 0 < ∑ i, a i) (hB : 0 < ∑ i, b i) :
    intensityDiv a b
      = (∑ i, a i) *
          (∑ i, (a i / ∑ k, a k) * Real.log ((a i / ∑ k, a k) / (b i / ∑ k, b k)))
        + (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) - (∑ i, a i) + (∑ i, b i) := by
  have hsumP : ∑ i, a i / (∑ k, a k) = 1 := by
    rw [← Finset.sum_div, div_self hA.ne']
  have hexpand : ∀ i ∈ Finset.univ, a i * Real.log (a i / b i) - a i + b i
      = (∑ k, a k) * ((a i / ∑ k, a k) * Real.log ((a i / ∑ k, a k) / (b i / ∑ k, b k)))
        + ((∑ k, a k) * Real.log ((∑ k, a k) / (∑ k, b k))) * (a i / ∑ k, a k)
        + (-a i + b i) := by
    intro i _
    have hai := ha i
    have hbi := hb i
    have hlog : Real.log (a i / b i)
        = Real.log ((a i / ∑ k, a k) / (b i / ∑ k, b k))
          + Real.log ((∑ k, a k) / (∑ k, b k)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [hlog]
    field_simp
    ring
  have hneg : ∑ x, (-a x + b x) = -(∑ x, a x) + ∑ x, b x := by
    simp [Finset.sum_add_distrib]
  rw [intensityDiv, Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsumP, mul_one, hneg]
  ring

/-- Symmetrized intensity divergence. -/
def intensityJeffreys {I : Type*} [Fintype I] (a b : I → ℝ) : ℝ :=
  intensityDiv a b + intensityDiv b a

theorem intensityJeffreys_mass_shape {I : Type*} [Fintype I] (a b : I → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hA : 0 < ∑ i, a i) (hB : 0 < ∑ i, b i) :
    intensityJeffreys a b
      = (∑ i, a i) * (∑ i, (a i / ∑ k, a k) * Real.log ((a i / ∑ k, a k) / (b i / ∑ k, b k)))
        + (∑ i, b i) * (∑ i, (b i / ∑ k, b k) * Real.log ((b i / ∑ k, b k) / (a i / ∑ k, a k)))
        + ((∑ i, a i) - (∑ i, b i)) * Real.log ((∑ i, a i) / (∑ i, b i)) := by
  rw [intensityJeffreys, intensityDiv_mass_shape a b ha hb hA hB,
    intensityDiv_mass_shape b a hb ha hB hA,
    show Real.log ((∑ i, b i) / (∑ i, a i)) = -Real.log ((∑ i, a i) / (∑ i, b i)) from by
      rw [← Real.log_inv, inv_div]]
  ring

/-! ## The literal Gamma-six packet -/

/-- Displacement clock of the Gamma-six shell. -/
def gammaSixClock (m : ℕ) (δ : ℝ) : ℝ := (m : ℝ) * Real.log 6 * δ

/-- Labelled coordinate count of the Gamma-six shell. -/
def gammaSixCount (m : ℕ) : ℕ := 5 * 6 ^ m

/-- Forward coordinate intensity of the Gamma-six shell. -/
def gammaSixForward (m : ℕ) (δ : ℝ) : ℝ := Real.exp (-((m : ℝ) * Real.log 6) * (1 - δ))

/-- Reflected coordinate intensity of the Gamma-six shell. -/
def gammaSixReflected (m : ℕ) (δ : ℝ) : ℝ := Real.exp (-((m : ℝ) * Real.log 6) * (1 + δ))

theorem gammaSixForward_pos (m : ℕ) (δ : ℝ) : 0 < gammaSixForward m δ := Real.exp_pos _

theorem gammaSixReflected_pos (m : ℕ) (δ : ℝ) : 0 < gammaSixReflected m δ := Real.exp_pos _

theorem gammaSixCount_cast (m : ℕ) :
    ((gammaSixCount m : ℕ) : ℝ) = 5 * Real.exp ((m : ℝ) * Real.log 6) := by
  rw [gammaSixCount, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
  push_cast
  ring

theorem gammaSixForward_total (m : ℕ) (δ : ℝ) :
    ((gammaSixCount m : ℕ) : ℝ) * gammaSixForward m δ = 5 * Real.exp (gammaSixClock m δ) := by
  rw [gammaSixCount_cast, gammaSixForward, gammaSixClock, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem gammaSixReflected_total (m : ℕ) (δ : ℝ) :
    ((gammaSixCount m : ℕ) : ℝ) * gammaSixReflected m δ = 5 * Real.exp (-gammaSixClock m δ) := by
  rw [gammaSixCount_cast, gammaSixReflected, gammaSixClock, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem gammaSix_logRatio (m : ℕ) (δ : ℝ) :
    Real.log (gammaSixForward m δ / gammaSixReflected m δ) = 2 * gammaSixClock m δ := by
  rw [gammaSixForward, gammaSixReflected, ← Real.exp_sub, Real.log_exp, gammaSixClock]
  ring

theorem intensityDiv_const {n : ℕ} (a b : ℝ) :
    intensityDiv (fun _ : Fin n => a) (fun _ : Fin n => b)
      = (n : ℝ) * (a * Real.log (a / b) - a + b) := by
  rw [intensityDiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Directed Gamma-six polarity, forward direction.** -/
theorem gammaSix_forward_div (m : ℕ) (δ : ℝ) :
    intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ)
      = 2 * gammaSixClock m δ * (5 * Real.exp (gammaSixClock m δ))
        - 5 * Real.exp (gammaSixClock m δ) + 5 * Real.exp (-gammaSixClock m δ) := by
  have hF := gammaSixForward_total m δ
  have hR := gammaSixReflected_total m δ
  rw [intensityDiv_const, gammaSix_logRatio]
  linear_combination (2 * gammaSixClock m δ - 1) * hF + hR

/-- **Directed Gamma-six polarity, reflected direction.** -/
theorem gammaSix_reflected_div (m : ℕ) (δ : ℝ) :
    intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)
      = -(2 * gammaSixClock m δ) * (5 * Real.exp (-gammaSixClock m δ))
        - 5 * Real.exp (-gammaSixClock m δ) + 5 * Real.exp (gammaSixClock m δ) := by
  have hlog : Real.log (gammaSixReflected m δ / gammaSixForward m δ)
      = -(2 * gammaSixClock m δ) := by
    rw [gammaSixReflected, gammaSixForward, ← Real.exp_sub, Real.log_exp, gammaSixClock]
    ring
  have hF := gammaSixForward_total m δ
  have hR := gammaSixReflected_total m δ
  rw [intensityDiv_const, hlog]
  linear_combination (-(2 * gammaSixClock m δ) - 1) * hR + hF

/-- **Symmetrized Gamma-six polarity.** -/
theorem gammaSix_jeffreys (m : ℕ) (δ : ℝ) :
    intensityJeffreys (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ)
      = 20 * gammaSixClock m δ * Real.sinh (gammaSixClock m δ) := by
  rw [intensityJeffreys, gammaSix_forward_div, gammaSix_reflected_div, Real.sinh_eq]
  ring

/-- **Directed Gamma-six chirality is the hyperbolic virial.** -/
theorem gammaSix_chirality (m : ℕ) (δ : ℝ) :
    intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ)
      - intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)
      = 20 * (gammaSixClock m δ * Real.cosh (gammaSixClock m δ)
        - Real.sinh (gammaSixClock m δ)) := by
  rw [gammaSix_forward_div, gammaSix_reflected_div, Real.sinh_eq, Real.cosh_eq]
  ring

/-- The Gamma-six functional equation exchanges the two intensities. -/
@[simp] theorem gammaSixForward_neg (m : ℕ) (δ : ℝ) :
    gammaSixForward m (-δ) = gammaSixReflected m δ := by
  rw [gammaSixForward, gammaSixReflected]
  congr 1
  ring

@[simp] theorem gammaSixReflected_neg (m : ℕ) (δ : ℝ) :
    gammaSixReflected m (-δ) = gammaSixForward m δ := by
  rw [gammaSixForward, gammaSixReflected]
  congr 1

@[simp] theorem gammaSixClock_neg (m : ℕ) (δ : ℝ) :
    gammaSixClock m (-δ) = -gammaSixClock m δ := by
  rw [gammaSixClock, gammaSixClock]
  ring

/-- **Reflection preserves the symmetrized polarity.** -/
theorem gammaSix_jeffreys_reflection (m : ℕ) (δ : ℝ) :
    intensityJeffreys (fun _ : Fin (gammaSixCount m) => gammaSixForward m (-δ))
        (fun _ : Fin (gammaSixCount m) => gammaSixReflected m (-δ))
      = intensityJeffreys (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ) := by
  rw [gammaSix_jeffreys, gammaSix_jeffreys, gammaSixClock_neg, Real.sinh_neg]
  ring

/-- **Reflection reverses the chirality.** -/
theorem gammaSix_chirality_reflection (m : ℕ) (δ : ℝ) :
    (intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixForward m (-δ))
        (fun _ : Fin (gammaSixCount m) => gammaSixReflected m (-δ))
      - intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixReflected m (-δ))
        (fun _ : Fin (gammaSixCount m) => gammaSixForward m (-δ)))
      = -(intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ)
      - intensityDiv (fun _ : Fin (gammaSixCount m) => gammaSixReflected m δ)
        (fun _ : Fin (gammaSixCount m) => gammaSixForward m δ)) := by
  rw [gammaSix_chirality, gammaSix_chirality, gammaSixClock_neg, Real.sinh_neg, Real.cosh_neg]
  ring

/-- **Intensity Hellinger square of the Gamma-six shell.** -/
theorem gammaSix_intensityHellingerSq (m : ℕ) (δ : ℝ) :
    ∑ _i : Fin (gammaSixCount m),
        (Real.sqrt (gammaSixForward m δ) - Real.sqrt (gammaSixReflected m δ)) ^ 2
      = 10 * (Real.cosh (gammaSixClock m δ) - 1) := by
  have hA := gammaSixForward_pos m δ
  have hB := gammaSixReflected_pos m δ
  have hsq : (Real.sqrt (gammaSixForward m δ) - Real.sqrt (gammaSixReflected m δ)) ^ 2
      = gammaSixForward m δ + gammaSixReflected m δ
        - 2 * Real.exp (-((m : ℝ) * Real.log 6)) := by
    have hmul : Real.sqrt (gammaSixForward m δ) * Real.sqrt (gammaSixReflected m δ)
        = Real.exp (-((m : ℝ) * Real.log 6)) := by
      rw [← Real.sqrt_mul hA.le, gammaSixForward, gammaSixReflected, ← Real.exp_add,
        show -((m : ℝ) * Real.log 6) * (1 - δ) + -((m : ℝ) * Real.log 6) * (1 + δ)
          = -((m : ℝ) * Real.log 6) + -((m : ℝ) * Real.log 6) from by ring, Real.exp_add]
      exact Real.sqrt_mul_self (Real.exp_pos _).le
    nlinarith [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, hmul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq, mul_sub, mul_add,
    gammaSixForward_total, gammaSixReflected_total, gammaSixCount_cast, Real.cosh_eq]
  rw [show (5 : ℝ) * Real.exp ((m : ℝ) * Real.log 6) * (2 * Real.exp (-((m : ℝ) * Real.log 6)))
      = 10 * (Real.exp ((m : ℝ) * Real.log 6) * Real.exp (-((m : ℝ) * Real.log 6))) from by ring,
    ← Real.exp_add]
  simp
  ring

/-- **Poisson Hellinger affinity of the Gamma-six shell**, per coordinate raised to the coordinate
count. -/
theorem gammaSix_affinity (m : ℕ) (δ : ℝ) (a b : ℝ≥0)
    (ha : (a : ℝ) = gammaSixForward m δ) (hb : (b : ℝ) = gammaSixReflected m δ) :
    hellingerAffinity Po(a) Po(b) ^ (gammaSixCount m)
      = Real.exp (-5 * (Real.cosh (gammaSixClock m δ) - 1)) := by
  rw [hellingerAffinity_poissonMeasure, ← Real.exp_nat_mul]
  congr 1
  have hsum := gammaSix_intensityHellingerSq m δ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, gammaSixCount_cast]
    at hsum
  rw [ha, hb, gammaSixCount_cast]
  nlinarith [hsum]

end

end GaloisForLFunctions.HTGeometry
