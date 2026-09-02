import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum
import GaloisForLFunctions.HTGeometry.PositiveDefinitePacketCauchy
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite positive spectral kernel in the form used by the non-Markovian Langevin paper. -/
def finitePositiveMemoryKernel {ι : Type*} [Fintype ι]
    (weight : ι → ℝ≥0) (frequency : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i, (weight i : ℝ) * realFourierCharacter (frequency i) t

@[simp]
theorem finitePositiveMemoryKernel_zero {ι : Type*} [Fintype ι]
    (weight : ι → ℝ≥0) (frequency : ι → ℝ) :
    finitePositiveMemoryKernel weight frequency 0 = ∑ i, (weight i : ℝ) := by
  simp [finitePositiveMemoryKernel, realFourierCharacter]

theorem finitePositiveMemoryKernel_neg {ι : Type*} [Fintype ι]
    (weight : ι → ℝ≥0) (frequency : ι → ℝ) (t : ℝ) :
    finitePositiveMemoryKernel weight frequency (-t) =
      star (finitePositiveMemoryKernel weight frequency t) := by
  classical
  unfold finitePositiveMemoryKernel
  change (∑ i, ((weight i : ℝ) : ℂ) * realFourierCharacter (frequency i) (-t)) =
    (starRingEnd ℂ) (∑ i, ((weight i : ℝ) : ℂ) * realFourierCharacter (frequency i) t)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  have hw : (starRingEnd ℂ) (((weight i : ℝ) : ℂ)) = (((weight i : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  rw [hw]
  congr 1
  change Complex.exp (Complex.I * (((frequency i * -t : ℝ) : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (Complex.I * (((frequency i * t : ℝ) : ℂ))))
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp

theorem norm_finitePositiveMemoryKernel_le_zero {ι : Type*} [Fintype ι]
    (weight : ι → ℝ≥0) (frequency : ι → ℝ) (t : ℝ) :
    ‖finitePositiveMemoryKernel weight frequency t‖ ≤ ∑ i, (weight i : ℝ) := by
  classical
  rw [finitePositiveMemoryKernel]
  calc
    ‖∑ i, ((weight i : ℝ) : ℂ) * realFourierCharacter (frequency i) t‖
        ≤ ∑ i, ‖((weight i : ℝ) : ℂ) * realFourierCharacter (frequency i) t‖ :=
      norm_sum_le _ _
    _ = ∑ i, (weight i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp

/-- Finite positive spectral kernels are positive definite, strengthening the paper's pointwise
bound to all finite coherent packets. -/
theorem positiveDefiniteOnReal_finitePositiveMemoryKernel
    {ι : Type*} [Fintype ι] (weight : ι → ℝ≥0) (frequency : ι → ℝ) :
    PositiveDefiniteOnReal (finitePositiveMemoryKernel weight frequency) := by
  classical
  intro N t c
  let v : ι → ℂ := fun k => ∑ j, c j * realFourierCharacter (frequency k) (t j)
  let r : ℝ := ∑ k, (weight k : ℝ) * Complex.normSq (v k)
  refine ⟨r, Finset.sum_nonneg fun k _ => mul_nonneg (weight k).property (Complex.normSq_nonneg _), ?_⟩
  have hchar (k : ι) (i j : Fin N) :
      realFourierCharacter (frequency k) (t j - t i) =
        star (realFourierCharacter (frequency k) (t i)) *
          realFourierCharacter (frequency k) (t j) :=
    realFourierCharacter_sub _ _ _
  simp only [finitePositiveMemoryKernel]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have hreorder (f : Fin N → Fin N → ι → ℂ) :
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
    calc
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ k, ∑ j, f i j k := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ k, ∑ i, ∑ j, f i j k := by rw [Finset.sum_comm]
  rw [hreorder]
  dsimp only [r]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [show (∑ i, ∑ j,
      star (c i) * (((weight k : ℝ) : ℂ) *
        realFourierCharacter (frequency k) (t j - t i)) * c j) =
      ((weight k : ℝ) : ℂ) * star (v k) * v k by
    simp only [v, hchar]
    have hstar :
        star (∑ i, c i * realFourierCharacter (frequency k) (t i)) =
          ∑ i, star (c i * realFourierCharacter (frequency k) (t i)) := by
      rw [star_sum]
    rw [hstar]
    simp only [star_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [mul_assoc]
  change ((weight k : ℝ) : ℂ) *
      ((starRingEnd ℂ) (v k) * v k) =
    ((weight k : ℝ) : ℂ) * ((Complex.normSq (v k) : ℝ) : ℂ)
  rw [← Complex.normSq_eq_conj_mul_self]

/-- Coupling-square weights of a finite bosonic environment. -/
def finiteBathMemoryWeight {ι : Type*} (coupling : ι → ℂ) (i : ι) : ℝ≥0 :=
  ⟨Complex.normSq (coupling i), Complex.normSq_nonneg _⟩

/-- Paper equation (4): memory kernel of a finite mode environment. -/
def finiteBathMemoryKernel {ι : Type*} [Fintype ι]
    (systemFrequency : ℝ) (environmentFrequency : ι → ℝ)
    (coupling : ι → ℂ) (t : ℝ) : ℂ :=
  finitePositiveMemoryKernel (finiteBathMemoryWeight coupling)
    (fun i => systemFrequency - environmentFrequency i) t

theorem finiteBathMemoryKernel_neg {ι : Type*} [Fintype ι]
    (systemFrequency : ℝ) (environmentFrequency : ι → ℝ)
    (coupling : ι → ℂ) (t : ℝ) :
    finiteBathMemoryKernel systemFrequency environmentFrequency coupling (-t) =
      star (finiteBathMemoryKernel systemFrequency environmentFrequency coupling t) :=
  finitePositiveMemoryKernel_neg _ _ _

theorem norm_finiteBathMemoryKernel_le_zero {ι : Type*} [Fintype ι]
    (systemFrequency : ℝ) (environmentFrequency : ι → ℝ)
    (coupling : ι → ℂ) (t : ℝ) :
    ‖finiteBathMemoryKernel systemFrequency environmentFrequency coupling t‖ ≤
      ∑ i, Complex.normSq (coupling i) := by
  change ‖finitePositiveMemoryKernel (finiteBathMemoryWeight coupling)
      (fun i => systemFrequency - environmentFrequency i) t‖ ≤
    ∑ i, (finiteBathMemoryWeight coupling i : ℝ)
  exact norm_finitePositiveMemoryKernel_le_zero
    (finiteBathMemoryWeight coupling)
    (fun i => systemFrequency - environmentFrequency i) t

theorem positiveDefiniteOnReal_finiteBathMemoryKernel {ι : Type*} [Fintype ι]
    (systemFrequency : ℝ) (environmentFrequency : ι → ℝ)
    (coupling : ι → ℂ) :
    PositiveDefiniteOnReal
      (finiteBathMemoryKernel systemFrequency environmentFrequency coupling) :=
  positiveDefiniteOnReal_finitePositiveMemoryKernel _ _

/-- Initial-environment stochastic driving in the interaction picture. -/
def finiteBathInitialDrive {ι : Type*} [Fintype ι]
    (systemFrequency : ℝ) (environmentFrequency : ι → ℝ)
    (coupling initialAmplitude : ι → ℂ) (t : ℝ) : ℂ :=
  -Complex.I * ∑ i, coupling i * initialAmplitude i *
    realFourierCharacter (systemFrequency - environmentFrequency i) t

/-- Vacuum initial amplitudes produce exactly zero added environmental noise. -/
@[simp]
theorem finiteBathInitialDrive_vacuum {ι : Type*} [Fintype ι]
    (systemFrequency : ℝ) (environmentFrequency : ι → ℝ)
    (coupling : ι → ℂ) (t : ℝ) :
    finiteBathInitialDrive systemFrequency environmentFrequency coupling (fun _ => 0) t = 0 := by
  simp [finiteBathInitialDrive]

/-- Complex-time extension of a finite bath memory kernel. -/
def finiteBathMemoryAnalytic {n : ℕ}
    (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ)
    (coupling : Fin n → ℂ) (z : ℂ) : ℂ :=
  GaloisForLFunctions.expSum (fun i => (Complex.normSq (coupling i) : ℂ))
    (fun i => systemFrequency - environmentFrequency i) z

theorem finiteBathMemoryKernel_eq_analytic_on_imaginary_axis
    {n : ℕ}
    (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ)
    (coupling : Fin n → ℂ) (t : ℝ) :
    finiteBathMemoryKernel systemFrequency environmentFrequency coupling t =
      finiteBathMemoryAnalytic systemFrequency environmentFrequency coupling
        ((t : ℂ) * Complex.I) := by
  classical
  unfold finiteBathMemoryKernel finitePositiveMemoryKernel finiteBathMemoryWeight
    finiteBathMemoryAnalytic GaloisForLFunctions.expSum realFourierCharacter
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg Complex.exp
  push_cast
  ring

theorem differentiable_finiteBathMemoryAnalytic
    {n : ℕ}
    (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ)
    (coupling : Fin n → ℂ) :
    Differentiable ℂ
      (finiteBathMemoryAnalytic systemFrequency environmentFrequency coupling) :=
  GaloisForLFunctions.differentiable_expSum _ _

theorem isStripAlmostPeriodic_finiteBathMemoryAnalytic
    {n : ℕ}
    (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ)
    (coupling : Fin n → ℂ) (σ R : ℝ) :
    IsStripAlmostPeriodic
      (finiteBathMemoryAnalytic systemFrequency environmentFrequency coupling) σ R :=
  GaloisForLFunctions.isStripAlmostPeriodic_expSum _ _ _ _

/-- Unit-coupling bath response is the finite Gibbs partition function at complex inverse time. -/
theorem finiteBathMemoryAnalytic_unit_eq_finiteComplexGibbsPartition
    {n : ℕ}
    (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ) :
    finiteBathMemoryAnalytic systemFrequency environmentFrequency (fun _ => 1) =
      _root_.HTGeometry.finiteComplexGibbsPartition
        (fun i => environmentFrequency i - systemFrequency) := by
  funext z
  simp only [finiteBathMemoryAnalytic, GaloisForLFunctions.expSum, Complex.normSq_one,
    Complex.ofReal_one, one_mul, _root_.HTGeometry.finiteComplexGibbsPartition]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  push_cast
  ring

/-- Normalized positive-feedback drift of a constant history. -/
def normalizedPositiveFeedbackConstantDrift (epsilon : ℝ) (z : ℂ) : ℂ :=
  ((1 - epsilon : ℝ) : ℂ) * z

/-- Arbitrary coherent constants are preserved exactly at balanced feedback. -/
theorem normalizedPositiveFeedback_preserves_all_constants_iff (epsilon : ℝ) :
    (∀ z : ℂ, normalizedPositiveFeedbackConstantDrift epsilon z = 0) ↔ epsilon = 1 := by
  constructor
  · intro h
    have h1 := h 1
    simp [normalizedPositiveFeedbackConstantDrift] at h1
    have h1R : 1 - epsilon = 0 := by exact_mod_cast h1
    linarith
  · rintro rfl
    simp [normalizedPositiveFeedbackConstantDrift]

/-- Normalized deterministic laser drift. -/
def normalizedLaserDrift (pump : ℝ) (z : ℂ) : ℂ :=
  ((-1 + pump / (1 + Complex.normSq z) : ℝ) : ℂ) * z

/-- Exact equilibrium classification: vacuum or the pump-selected phase circle. -/
theorem normalizedLaserDrift_eq_zero_iff (pump : ℝ) (z : ℂ) :
    normalizedLaserDrift pump z = 0 ↔ z = 0 ∨ Complex.normSq z = pump - 1 := by
  rw [normalizedLaserDrift, mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · right
      have hreal : -1 + pump / (1 + Complex.normSq z) = 0 := by
        exact_mod_cast h
      have hden : (1 + Complex.normSq z : ℝ) ≠ 0 := by
        nlinarith [Complex.normSq_nonneg z]
      field_simp [hden] at hreal
      linarith
    · left
      exact h
  · intro h
    rcases h with rfl | h
    · exact Or.inr rfl
    · left
      apply Complex.ofReal_eq_zero.mpr
      have hden : (1 + Complex.normSq z : ℝ) ≠ 0 := by
        nlinarith [Complex.normSq_nonneg z]
      field_simp [hden]
      linarith

/-- Above-threshold feedback law, with physical nonnegativity encoded in the parameter types. -/
def quadraticNarrowedLinewidth (baseline feedback : ℝ≥0) : ℝ :=
  (baseline : ℝ) / (1 + (feedback : ℝ)) ^ 2

theorem quadraticNarrowedLinewidth_le_baseline (baseline feedback : ℝ≥0) :
    quadraticNarrowedLinewidth baseline feedback ≤ baseline := by
  rw [quadraticNarrowedLinewidth]
  have hk : 0 ≤ (feedback : ℝ) := feedback.property
  have hden : 1 ≤ (1 + (feedback : ℝ)) ^ 2 := by nlinarith [sq_nonneg (feedback : ℝ)]
  exact (div_le_iff₀ (by positivity : 0 < (1 + (feedback : ℝ)) ^ 2)).2
    (by nlinarith [baseline.property, mul_nonneg baseline.property (sub_nonneg.mpr hden)])

theorem quadraticNarrowedLinewidth_zero_feedback (baseline : ℝ≥0) :
    quadraticNarrowedLinewidth baseline 0 = baseline := by
  simp [quadraticNarrowedLinewidth]

/-! ## Applications to existing finite Gibbs and KMS/Wightman spectra -/

/-- Imaginary-time finite Gibbs partition as a paper memory kernel. -/
def finiteGibbsMemoryKernel {α : Type*} [Fintype α]
    (energy : α → ℝ) (t : ℝ) : ℂ :=
  finitePositiveMemoryKernel (fun _ => (1 : ℝ≥0)) (fun a => -energy a) t

theorem finiteGibbsMemoryKernel_eq_partition_imaginaryTime
    {α : Type*} [Fintype α] (energy : α → ℝ) (t : ℝ) :
    finiteGibbsMemoryKernel energy t =
      _root_.HTGeometry.finiteComplexGibbsPartition energy ((t : ℂ) * Complex.I) := by
  classical
  unfold finiteGibbsMemoryKernel finitePositiveMemoryKernel
    _root_.HTGeometry.finiteComplexGibbsPartition realFourierCharacter
  apply Finset.sum_congr rfl
  intro a _
  simp only [NNReal.coe_one, Complex.ofReal_one, one_mul]
  apply congrArg Complex.exp
  push_cast
  ring

theorem finiteGibbsMemoryKernel_neg {α : Type*} [Fintype α]
    (energy : α → ℝ) (t : ℝ) :
    finiteGibbsMemoryKernel energy (-t) = star (finiteGibbsMemoryKernel energy t) :=
  finitePositiveMemoryKernel_neg _ _ _

theorem norm_finiteGibbsMemoryKernel_le_card {α : Type*} [Fintype α]
    (energy : α → ℝ) (t : ℝ) :
    ‖finiteGibbsMemoryKernel energy t‖ ≤ Fintype.card α := by
  simpa [finiteGibbsMemoryKernel] using
    norm_finitePositiveMemoryKernel_le_zero
      (fun _ : α => (1 : ℝ≥0)) (fun a => -energy a) t

theorem positiveDefiniteOnReal_finiteGibbsMemoryKernel
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    PositiveDefiniteOnReal (finiteGibbsMemoryKernel energy) :=
  positiveDefiniteOnReal_finitePositiveMemoryKernel _ _

/-- Nonnegative KMS/Wightman transition weight, bundled so later kernel theorems need no
positivity premise. -/
def finiteKMSMemoryWeight {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (p : α × α) : ℝ≥0 :=
  ⟨_root_.HTGeometry.finiteKMSWightmanTransitionIntensity
      β energy amplitude p.1 p.2,
    _root_.HTGeometry.finiteKMSWightmanTransitionIntensity_nonneg
      β energy amplitude p.1 p.2⟩

def finiteKMSMemoryFrequency {α : Type*}
    (energy : α → ℝ) (p : α × α) : ℝ :=
  energy p.2 - energy p.1

/-- Canonical finite-temperature two-time response as a positive spectral memory kernel. -/
def finiteKMSMemoryKernel {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (t : ℝ) : ℂ :=
  finitePositiveMemoryKernel (finiteKMSMemoryWeight β energy amplitude)
    (finiteKMSMemoryFrequency energy) t

theorem finiteKMSMemoryKernel_neg {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (t : ℝ) :
    finiteKMSMemoryKernel β energy amplitude (-t) =
      star (finiteKMSMemoryKernel β energy amplitude t) :=
  finitePositiveMemoryKernel_neg _ _ _

theorem norm_finiteKMSMemoryKernel_le_zero {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (t : ℝ) :
    ‖finiteKMSMemoryKernel β energy amplitude t‖ ≤
      ∑ p : α × α,
        _root_.HTGeometry.finiteKMSWightmanTransitionIntensity
          β energy amplitude p.1 p.2 := by
  change ‖finitePositiveMemoryKernel (finiteKMSMemoryWeight β energy amplitude)
      (finiteKMSMemoryFrequency energy) t‖ ≤
    ∑ p : α × α, (finiteKMSMemoryWeight β energy amplitude p : ℝ)
  exact norm_finitePositiveMemoryKernel_le_zero
    (finiteKMSMemoryWeight β energy amplitude)
    (finiteKMSMemoryFrequency energy) t

theorem positiveDefiniteOnReal_finiteKMSMemoryKernel
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) :
    PositiveDefiniteOnReal (finiteKMSMemoryKernel β energy amplitude) :=
  positiveDefiniteOnReal_finitePositiveMemoryKernel _ _

/-- Canonical Hermitian completion of an arbitrary transition amplitude. -/
def hermitianizedAmplitude {α : Type*} (seed : α → α → ℂ) (a b : α) : ℂ :=
  seed a b + star (seed b a)

theorem hermitianizedAmplitude_symm {α : Type*}
    (seed : α → α → ℂ) (a b : α) :
    hermitianizedAmplitude seed b a = star (hermitianizedAmplitude seed a b) := by
  simp [hermitianizedAmplitude, add_comm]

/-- KMS memory of an automatically Hermitian observable. -/
def finiteHermitianKMSMemoryKernel {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ) : ℝ → ℂ :=
  finiteKMSMemoryKernel β energy (hermitianizedAmplitude seed)

theorem finiteHermitianKMSMemoryKernel_even
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ) (t : ℝ) :
    finiteHermitianKMSMemoryKernel β energy seed (-t) =
      finiteHermitianKMSMemoryKernel β energy seed t := by
  classical
  unfold finiteHermitianKMSMemoryKernel finiteKMSMemoryKernel
    finitePositiveMemoryKernel finiteKMSMemoryWeight finiteKMSMemoryFrequency
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (((_root_.HTGeometry.finiteKMSWightmanTransitionIntensity
      β energy (hermitianizedAmplitude seed) b a : ℝ) : ℂ) *
        realFourierCharacter (energy a - energy b) (-t)) =
    (((_root_.HTGeometry.finiteKMSWightmanTransitionIntensity
      β energy (hermitianizedAmplitude seed) a b : ℝ) : ℂ) *
        realFourierCharacter (energy b - energy a) t)
  have hsym := _root_.HTGeometry.finiteKMSWightmanTransitionIntensity_symm
    β energy (hermitianizedAmplitude seed) (hermitianizedAmplitude_symm seed) b a
  rw [hsym]
  congr 1
  unfold realFourierCharacter
  apply congrArg Complex.exp
  push_cast
  ring

theorem finiteHermitianKMSMemoryKernel_im_eq_zero
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ) (t : ℝ) :
    (finiteHermitianKMSMemoryKernel β energy seed t).im = 0 := by
  have hneg := finiteKMSMemoryKernel_neg β energy (hermitianizedAmplitude seed) t
  have heven := finiteHermitianKMSMemoryKernel_even β energy seed t
  have hstar : star (finiteHermitianKMSMemoryKernel β energy seed t) =
      finiteHermitianKMSMemoryKernel β energy seed t := hneg.symm.trans heven
  have him := congrArg Complex.im hstar
  have : -(finiteHermitianKMSMemoryKernel β energy seed t).im =
      (finiteHermitianKMSMemoryKernel β energy seed t).im := by
    simpa [Complex.star_def] using him
  linarith

/-- Real form of the Hermitian KMS memory kernel. -/
def finiteHermitianKMSMemoryReal {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ) (t : ℝ) : ℝ :=
  (finiteHermitianKMSMemoryKernel β energy seed t).re

theorem finiteHermitianKMSMemoryReal_ofReal
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ) (t : ℝ) :
    ((finiteHermitianKMSMemoryReal β energy seed t : ℝ) : ℂ) =
      finiteHermitianKMSMemoryKernel β energy seed t := by
  apply Complex.ext
  · rfl
  · simp [finiteHermitianKMSMemoryKernel_im_eq_zero]

theorem positiveDefiniteOnReal_finiteHermitianKMSMemoryReal
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ) :
    PositiveDefiniteOnReal
      (fun t => ((finiteHermitianKMSMemoryReal β energy seed t : ℝ) : ℂ)) := by
  rw [show (fun t => ((finiteHermitianKMSMemoryReal β energy seed t : ℝ) : ℂ)) =
      finiteHermitianKMSMemoryKernel β energy seed from by
    funext t
    exact finiteHermitianKMSMemoryReal_ofReal β energy seed t]
  exact positiveDefiniteOnReal_finiteKMSMemoryKernel
    β energy (hermitianizedAmplitude seed)

theorem finiteHermitianKMSMemoryReal_even
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ) (t : ℝ) :
    finiteHermitianKMSMemoryReal β energy seed (-t) =
      finiteHermitianKMSMemoryReal β energy seed t := by
  exact congrArg Complex.re (finiteHermitianKMSMemoryKernel_even β energy seed t)

theorem finiteHermitianKMSMemoryPacketEnergy_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ)
    {N : ℕ} (time coefficient : Fin N → ℝ) :
    0 ≤ realKernelPacketEnergy
      (finiteHermitianKMSMemoryReal β energy seed) time coefficient :=
  realKernelPacketEnergy_nonneg_of_positiveDefinite _
    (positiveDefiniteOnReal_finiteHermitianKMSMemoryReal β energy seed)
    time coefficient

theorem finiteHermitianKMSMemoryPacketCross_sq_le
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ)
    {N M : ℕ} (s a : Fin N → ℝ) (t b : Fin M → ℝ) :
    realKernelPacketCross (finiteHermitianKMSMemoryReal β energy seed) s a t b ^ 2 ≤
      realKernelPacketEnergy (finiteHermitianKMSMemoryReal β energy seed) s a *
        realKernelPacketEnergy (finiteHermitianKMSMemoryReal β energy seed) t b :=
  realKernelPacketCross_sq_le_energy_mul_energy_of_positiveDefinite _
    (positiveDefiniteOnReal_finiteHermitianKMSMemoryReal β energy seed)
    (finiteHermitianKMSMemoryReal_even β energy seed) s a t b

theorem finiteHermitianKMSMemoryPacketChannelGram_posSemidef
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ)
    {M N : ℕ} (time coefficient : Fin M → Fin N → ℝ) :
    (realKernelPacketChannelGram
      (finiteHermitianKMSMemoryReal β energy seed) time coefficient).PosSemidef :=
  realKernelPacketChannelGram_posSemidef_of_positiveDefinite _
    (positiveDefiniteOnReal_finiteHermitianKMSMemoryReal β energy seed)
    (finiteHermitianKMSMemoryReal_even β energy seed) time coefficient

theorem finiteHermitianKMSMemoryPacketChannelGram_det_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (seed : α → α → ℂ)
    {M N : ℕ} (time coefficient : Fin M → Fin N → ℝ) :
    0 ≤ (realKernelPacketChannelGram
      (finiteHermitianKMSMemoryReal β energy seed) time coefficient).det :=
  realKernelPacketChannelGram_det_nonneg_of_positiveDefinite _
    (positiveDefiniteOnReal_finiteHermitianKMSMemoryReal β energy seed)
    (finiteHermitianKMSMemoryReal_even β energy seed) time coefficient

end

end GaloisForLFunctions.HTGeometry

