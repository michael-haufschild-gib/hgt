import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma

/-!
# Occupation vacuum--anomaly reciprocity

For a finite family of bosonic nomes, normalized vacuum amplitude and unnormalized
occupation mass are reciprocal records of one occupation line.
-/

namespace HTGeometry

noncomputable section

open scoped BigOperators


private theorem complex_tsum_pi_geometric_fin :
    ∀ (n : ℕ) (q : Fin n → ℂ), (∀ i, ‖q i‖ < 1) →
      Summable (fun ν : Fin n → ℕ => ‖∏ i, q i ^ ν i‖) ∧
      ∑' ν : Fin n → ℕ, ∏ i, q i ^ ν i =
        ∏ i, (1 - q i)⁻¹ := by
  intro n
  induction n with
  | zero =>
      intro q hq
      constructor
      · exact Summable.of_finite
      · simp
  | succ n ih =>
      intro q hq
      let r : Fin n → ℂ := fun i => q i.succ
      obtain ⟨hbNorm, hbValue⟩ := ih r (fun i => hq i.succ)
      let a : ℕ → ℂ := fun k => q 0 ^ k
      let b : (Fin n → ℕ) → ℂ := fun ν => ∏ i, r i ^ ν i
      have haNorm : Summable (fun k => ‖a k‖) := by
        simpa only [a, norm_pow] using
          summable_geometric_of_lt_one (norm_nonneg (q 0)) (hq 0)
      have hbNorm' : Summable (fun ν => ‖b ν‖) := by
        simpa only [b, r] using hbNorm
      have hbSum : HasSum b (∏ i, (1 - r i)⁻¹) := by
        have h := hbNorm'.of_norm.hasSum
        rw [show (∑' ν, b ν) = ∏ i, (1 - r i)⁻¹ by
          simpa only [b] using hbValue] at h
        exact h
      have habNorm :
          Summable (fun x : ℕ × (Fin n → ℕ) => a x.1 * b x.2) :=
        summable_mul_of_summable_norm (f := a) (g := b) haNorm hbNorm'
      have habNormReal :
          Summable (fun x : ℕ × (Fin n → ℕ) => ‖a x.1‖ * ‖b x.2‖) := by
        exact Summable.mul_of_nonneg
          (f := fun k : ℕ => ‖a k‖) (g := fun ν : Fin n → ℕ => ‖b ν‖)
          haNorm hbNorm'
          (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have habSum :
          HasSum (fun x : ℕ × (Fin n → ℕ) => a x.1 * b x.2)
            ((1 - q 0)⁻¹ * ∏ i, (1 - r i)⁻¹) :=
        HasSum.mul (f := a) (g := b)
          (hasSum_geometric_of_norm_lt_one (hq 0)) hbSum habNorm
      constructor
      · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).summable_iff
          (f := fun ν : Fin (n + 1) → ℕ => ‖∏ i, q i ^ ν i‖)]
        simpa only [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero,
          Fin.cons_succ, norm_mul, a, b, r] using habNormReal
      · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).tsum_eq
          (fun ν : Fin (n + 1) → ℕ => ∏ i, q i ^ ν i)]
        simpa only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ,
          a, b, r] using habSum.tsum_eq

theorem complex_tsum_pi_geometric {ι : Type*} [Fintype ι]
    (q : ι → ℂ) (hq : ∀ i, ‖q i‖ < 1) :
    ∑' ν : ι → ℕ, ∏ i, q i ^ ν i =
      ∏ i, (1 - q i)⁻¹ := by
  let e := Fintype.equivFin ι
  let pe : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℕ) e
  calc
    (∑' ν : ι → ℕ, ∏ i, q i ^ ν i) =
        ∑' ν : Fin (Fintype.card ι) → ℕ,
          ∏ j, q (e.symm j) ^ ν j := by
            rw [← pe.tsum_eq
              (fun ν : Fin (Fintype.card ι) → ℕ => ∏ j, q (e.symm j) ^ ν j)]
            congr 1
            funext ν
            exact Fintype.prod_equiv e
              (fun i => q i ^ ν i)
              (fun j => q (e.symm j) ^ pe ν j) (by simp [pe])
    _ = ∏ j, (1 - q (e.symm j))⁻¹ :=
      (complex_tsum_pi_geometric_fin _ _ (fun j => hq (e.symm j))).2
    _ = ∏ i, (1 - q i)⁻¹ := by
      exact Fintype.prod_equiv e.symm
        (fun j => (1 - q (e.symm j))⁻¹)
        (fun i => (1 - q i)⁻¹) (by simp)

/-- Total unnormalized mass of a finite independent occupation family. -/
def finiteOccupationMass {ι : Type*} [Fintype ι] (q : ι → ℂ) : ℂ :=
  ∑' ν : ι → ℕ, ∏ i, q i ^ ν i

/-- Vacuum amplitude of the normalized occupation family. -/
def finiteOccupationVacuumAmplitude {ι : Type*} [Fintype ι]
    (q : ι → ℂ) : ℂ :=
  ∏ i, (1 - q i)

theorem finiteOccupationMass_eq_inv_vacuumAmplitude
    {ι : Type*} [Fintype ι] (q : ι → ℂ)
    (hq : ∀ i, ‖q i‖ < 1) :
    finiteOccupationMass q =
      (finiteOccupationVacuumAmplitude q)⁻¹ := by
  rw [finiteOccupationMass, finiteOccupationVacuumAmplitude,
    complex_tsum_pi_geometric q hq]
  exact Finset.prod_inv_distrib fun i => 1 - q i

theorem finiteOccupationVacuumAmplitude_ne_zero
    {ι : Type*} [Fintype ι] (q : ι → ℂ)
    (hq : ∀ i, ‖q i‖ < 1) :
    finiteOccupationVacuumAmplitude q ≠ 0 := by
  rw [finiteOccupationVacuumAmplitude]
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  exact sub_ne_zero.mpr fun h => by
    have hqi := hq i
    rw [← h] at hqi
    norm_num at hqi

/-- Vacuum amplitude times raw occupation mass is exactly one. -/
theorem finiteOccupation_vacuum_mul_mass
    {ι : Type*} [Fintype ι] (q : ι → ℂ)
    (hq : ∀ i, ‖q i‖ < 1) :
    finiteOccupationVacuumAmplitude q * finiteOccupationMass q = 1 := by
  rw [finiteOccupationMass_eq_inv_vacuumAmplitude q hq]
  exact mul_inv_cancel₀ (finiteOccupationVacuumAmplitude_ne_zero q hq)

/-! ## Hilbert half-density realization -/

/-- Half-density coefficient of a finite real occupation family. -/
def finiteOccupationHalfDensityWeight
    {ι : Type*} [Fintype ι] (q : ι → ℝ) (ν : ι →₀ ℕ) : ℂ :=
  nomeMonomial (fun i => (Real.sqrt (q i) : ℂ)) ν

theorem norm_nomeMonomial_of_nonneg
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (ν : ι →₀ ℕ) :
    ‖nomeMonomial (fun i => (q i : ℂ)) ν‖ =
      ν.prod fun i n => q i ^ n := by
  simp only [nomeMonomial, Finsupp.prod]
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq i)]

theorem norm_finiteOccupationHalfDensityWeight_sq
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (ν : ι →₀ ℕ) :
    ‖finiteOccupationHalfDensityWeight q ν‖ ^ (2 : ℕ) =
      ν.prod fun i n => q i ^ n := by
  rw [finiteOccupationHalfDensityWeight,
    norm_nomeMonomial_of_nonneg
      (fun i => Real.sqrt (q i)) (fun _ => Real.sqrt_nonneg _)]
  simp only [Finsupp.prod]
  rw [pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← mul_pow, Real.mul_self_sqrt (hq i)]

theorem summable_norm_sq_finiteOccupationHalfDensityWeight
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (_hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Summable (fun ν : ι →₀ ℕ =>
      ‖finiteOccupationHalfDensityWeight q ν‖ ^ (2 : ℕ)) := by
  apply (summable_nomeMonomial_pow_iff 1
    (fun i => (Real.sqrt (q i) : ℂ)) ?_).2
  · exact Summable.of_finite
  · intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sqrt_lt' zero_lt_one]
    simpa using hq1 i

/-- Unnormalized finite occupation half-density as an actual `ell²` vector. -/
def finiteOccupationRawHalfDensity
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    lp (fun _ : ι →₀ ℕ => ℂ) 2 :=
  ⟨finiteOccupationHalfDensityWeight q,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_finiteOccupationHalfDensityWeight q hq0 hq1)⟩

theorem norm_finiteOccupationRawHalfDensity_sq
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ‖finiteOccupationRawHalfDensity q hq0 hq1‖ ^ (2 : ℕ) =
      ∏ i, (1 - q i)⁻¹ := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  simp only [finiteOccupationRawHalfDensity]
  rw [show (fun ν : ι →₀ ℕ =>
      ‖finiteOccupationHalfDensityWeight q ν‖ ^ (2 : ℕ)) =
      fun ν => ν.prod fun i n => q i ^ n by
        funext ν
        exact norm_finiteOccupationHalfDensityWeight_sq q hq0 ν]
  have hsumReal : Summable (fun ν : ι →₀ ℕ =>
      ν.prod fun i n => q i ^ n) := by
    have hsum := (summable_nomeMonomial_pow_iff 0
      (fun i => (q i : ℂ)) (fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq0 i)]
      exact hq1 i)).2 (Summable.of_finite :
        Summable (fun i => ‖(q i : ℂ)‖ ^ (0 + 1)))
    apply hsum.congr
    intro ν
    rw [pow_one, norm_nomeMonomial_of_nonneg q hq0 ν]
  have hEuler :
      ∑' ν : ι →₀ ℕ, nomeMonomial (fun i => (q i : ℂ)) ν =
        ∏ i, (1 - (q i : ℂ))⁻¹ := by
    let e := (Finsupp.equivFunOnFinite : (ι →₀ ℕ) ≃ (ι → ℕ))
    calc
      (∑' ν : ι →₀ ℕ, nomeMonomial (fun i => (q i : ℂ)) ν) =
          ∑' ν : ι →₀ ℕ, ∏ i, (q i : ℂ) ^ (e ν) i := by
            apply tsum_congr
            intro ν
            rw [nomeMonomial,
              Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
            rfl
      _ = ∑' f : ι → ℕ, ∏ i, (q i : ℂ) ^ f i :=
        e.tsum_eq (fun f : ι → ℕ => ∏ i, (q i : ℂ) ^ f i)
      _ = ∏ i, (1 - (q i : ℂ))⁻¹ :=
        complex_tsum_pi_geometric (fun i => (q i : ℂ)) (fun i => by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq0 i)]
          exact hq1 i)
  have hcastTerms : (fun ν : ι →₀ ℕ =>
      ((ν.prod fun i n => q i ^ n : ℝ) : ℂ)) =
      fun ν => nomeMonomial (fun i => (q i : ℂ)) ν := by
    funext ν
    simp only [nomeMonomial, Finsupp.prod]
    push_cast
    rfl
  rw [← hcastTerms] at hEuler
  rw [← Complex.ofReal_tsum] at hEuler
  exact_mod_cast congrArg Complex.re hEuler

/-- Finite-product vacuum mass. -/
def finiteOccupationBoundaryVolume
    {ι : Type*} [Fintype ι] (q : ι → ℝ) : ℝ :=
  ∏ i, (1 - q i)

theorem finiteOccupationBoundaryVolume_pos
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq1 : ∀ i, q i < 1) :
    0 < finiteOccupationBoundaryVolume q := by
  rw [finiteOccupationBoundaryVolume]
  exact Finset.prod_pos fun i _ => sub_pos.mpr (hq1 i)

/-- Projectively normalized occupation direction; the raw norm record remains
available separately. -/
def finiteOccupationNormalizedHalfDensity
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    lp (fun _ : ι →₀ ℕ => ℂ) 2 :=
  ((Real.sqrt (finiteOccupationBoundaryVolume q) : ℝ) : ℂ) •
    finiteOccupationRawHalfDensity q hq0 hq1

/-- Vacuum basis vector of the occupation carrier. -/
def finiteOccupationVacuum
    (ι : Type*) [Fintype ι] :
    lp (fun _ : ι →₀ ℕ => ℂ) 2 :=
  lp.single 2 0 1

theorem norm_finiteOccupationNormalizedHalfDensity_sq
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ‖finiteOccupationNormalizedHalfDensity q hq0 hq1‖ ^ (2 : ℕ) = 1 := by
  have hvol := finiteOccupationBoundaryVolume_pos q hq1
  rw [finiteOccupationNormalizedHalfDensity, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hvol.le,
    norm_finiteOccupationRawHalfDensity_sq q hq0 hq1]
  rw [finiteOccupationBoundaryVolume]
  calc
    (∏ i, (1 - q i)) * ∏ i, (1 - q i)⁻¹ =
        (∏ i, (1 - q i)) * (∏ i, (1 - q i))⁻¹ := by
      congr 1
      exact Finset.prod_inv_distrib
        (s := (Finset.univ : Finset ι)) fun i : ι => 1 - q i
    _ = 1 := mul_inv_cancel₀ hvol.ne'

theorem inner_vacuum_finiteOccupationNormalizedHalfDensity
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    inner ℂ (finiteOccupationVacuum ι)
        (finiteOccupationNormalizedHalfDensity q hq0 hq1) =
      (Real.sqrt (finiteOccupationBoundaryVolume q) : ℂ) := by
  rw [finiteOccupationVacuum, lp.inner_single_left]
  rw [RCLike.inner_apply, map_one, mul_one]
  change ((Real.sqrt (finiteOccupationBoundaryVolume q) : ℂ) *
    finiteOccupationHalfDensityWeight q 0) =
      (Real.sqrt (finiteOccupationBoundaryVolume q) : ℂ)
  simp [finiteOccupationHalfDensityWeight, nomeMonomial]

theorem norm_inner_vacuum_normalized_sq
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ‖inner ℂ (finiteOccupationVacuum ι)
        (finiteOccupationNormalizedHalfDensity q hq0 hq1)‖ ^ (2 : ℕ) =
      finiteOccupationBoundaryVolume q := by
  rw [inner_vacuum_finiteOccupationNormalizedHalfDensity q hq0 hq1,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (finiteOccupationBoundaryVolume_pos q hq1).le]

end

end HTGeometry
