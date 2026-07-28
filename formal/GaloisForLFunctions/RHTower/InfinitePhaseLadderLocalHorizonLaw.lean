/-
# Infinite phase-ladder local-horizon law

This file removes finite-dimensionality from the local-horizon quantum return law.

Every finite spectral level is lifted to the infinite phase lattice

`E(j,k) = E(j) + 2πk/T`,  `k ∈ ℕ`,

with a common geometric probability distribution.  At target time `T` every added phase is exactly
one.  At every other time the infinite-ladder amplitude has modulus at most one.  Consequently the
lift preserves every exact target return probability while it can only reduce distinguishability
of earlier return records.

The lift is realized on `ℓ²(Fin (m+1) × ℕ)` by a normalized state and a maximal self-adjoint
diagonal Hamiltonian.  That Hamiltonian is norm-unbounded on its domain and has infinitely many
distinct energy levels over every finite spectral coordinate.  The capstone theorem combines this
genuine infinite system with the exact finite nearest-neighbour local record.
-/
import GaloisForLFunctions.RHTower.MaximalRealDiagonalSelfAdjoint
import GaloisForLFunctions.RHTower.LocalHorizonQuantumReturnLaw

open scoped BigOperators InnerProductSpace LinearPMap
open Complex

noncomputable section

namespace RHTower.ParityForecast

/-- Strictly positive geometric probability on the infinite ladder. -/
def phaseLadderWeight (k : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (k + 1)

theorem phaseLadderWeight_pos (k : ℕ) :
    0 < phaseLadderWeight k := by
  unfold phaseLadderWeight
  positivity

theorem phaseLadderWeight_nonneg (k : ℕ) :
    0 ≤ phaseLadderWeight k :=
  (phaseLadderWeight_pos k).le

theorem phaseLadderWeight_summable :
    Summable phaseLadderWeight := by
  unfold phaseLadderWeight
  simpa [pow_succ] using
    summable_geometric_two.mul_right ((1 : ℝ) / 2)

theorem phaseLadderWeight_tsum :
    ∑' k : ℕ, phaseLadderWeight k = 1 := by
  unfold phaseLadderWeight
  rw [show (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1)) =
      fun k => ((1 : ℝ) / 2) ^ k * ((1 : ℝ) / 2) by
    funext k
    rw [pow_succ]]
  rw [tsum_mul_right, tsum_geometric_two]
  norm_num

/-- The `k`-th common phase of a ladder whose spacing is one target-time period. -/
def phaseLadderPhase (T t : ℝ) (k : ℕ) : ℂ :=
  Complex.exp
    (((t / T) * (k : ℝ) * (2 * Real.pi) : ℝ) * I)

theorem phaseLadderPhase_norm (T t : ℝ) (k : ℕ) :
    ‖phaseLadderPhase T t k‖ = 1 := by
  unfold phaseLadderPhase
  exact Complex.norm_exp_ofReal_mul_I _

theorem phaseLadderPhase_target {T : ℝ} (hT : 0 < T) (k : ℕ) :
    phaseLadderPhase T T k = 1 := by
  unfold phaseLadderPhase
  rw [div_self hT.ne']
  norm_num
  simpa [mul_assoc] using Complex.exp_nat_mul_two_pi_mul_I k

/-- Common infinite-ladder survival amplitude. -/
def phaseLadderAmplitude (T t : ℝ) : ℂ :=
  ∑' k : ℕ, (phaseLadderWeight k : ℂ) *
    phaseLadderPhase T t k

theorem phaseLadderAmplitude_summable (T t : ℝ) :
    Summable (fun k : ℕ => (phaseLadderWeight k : ℂ) *
      phaseLadderPhase T t k) := by
  apply Summable.of_norm
  simpa [norm_mul, phaseLadderPhase_norm,
    Real.norm_eq_abs, abs_of_nonneg,
    phaseLadderWeight_nonneg] using
      phaseLadderWeight_summable

theorem phaseLadderAmplitude_norm_le_one (T t : ℝ) :
    ‖phaseLadderAmplitude T t‖ ≤ 1 := by
  unfold phaseLadderAmplitude
  calc
    ‖∑' k : ℕ, (phaseLadderWeight k : ℂ) *
        phaseLadderPhase T t k‖
        ≤ ∑' k : ℕ, ‖(phaseLadderWeight k : ℂ) *
          phaseLadderPhase T t k‖ :=
      norm_tsum_le_tsum_norm (by
        simpa using (phaseLadderAmplitude_summable T t).norm)
    _ = ∑' k : ℕ, phaseLadderWeight k := by
      apply tsum_congr
      intro k
      rw [norm_mul, phaseLadderPhase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (phaseLadderWeight_nonneg k)]
    _ = 1 := phaseLadderWeight_tsum

theorem phaseLadderAmplitude_target {T : ℝ} (hT : 0 < T) :
    phaseLadderAmplitude T T = 1 := by
  unfold phaseLadderAmplitude
  simp_rw [phaseLadderPhase_target hT, mul_one]
  rw [← Complex.ofReal_tsum, phaseLadderWeight_tsum]
  norm_num

/-- One-period phase-lattice lift of an arbitrary finite real spectrum. -/
def phaseLadderEnergy {m : ℕ}
    (T : ℝ) (energy : Fin (m + 1) → ℝ)
    (x : Fin (m + 1) × ℕ) : ℝ :=
  energy x.1 + 2 * Real.pi * (x.2 : ℝ) / T

theorem phaseLadderEnergy_injective_nat
    {m : ℕ} {T : ℝ} (hT : 0 < T)
    (energy : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    Function.Injective
      (fun k : ℕ => phaseLadderEnergy T energy (j, k)) := by
  intro k l hkl
  unfold phaseLadderEnergy at hkl
  have hc : 0 < 2 * Real.pi / T := div_pos (mul_pos (by norm_num) Real.pi_pos) hT
  have hmul :
      (2 * Real.pi / T) * (k : ℝ) =
        (2 * Real.pi / T) * (l : ℝ) := by
    calc
      _ = 2 * Real.pi * (k : ℝ) / T := by ring
      _ = 2 * Real.pi * (l : ℝ) / T := by linarith
      _ = _ := by ring
  have hcast : (k : ℝ) = (l : ℝ) := by
    exact mul_left_cancel₀ hc.ne' hmul
  exact_mod_cast hcast

theorem phaseLadderHamiltonian_selfAdjoint
    {m : ℕ} (T : ℝ) (energy : Fin (m + 1) → ℝ) :
    IsSelfAdjoint
      (RHTower.maximalRealDiagonal
        (phaseLadderEnergy T energy)) :=
  RHTower.maximalRealDiagonal_isSelfAdjoint _

/-- The genuine infinite Hilbert space of a finite spectrum with an infinite phase ladder. -/
abbrev PhaseLadderSpace (m : ℕ) :=
  RHTower.DiagonalL2 (Fin (m + 1) × ℕ)

theorem phaseLadderProductWeight_summable
    {m : ℕ} (weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) :
    Summable (fun x : Fin (m + 1) × ℕ =>
      weight x.1 * phaseLadderWeight x.2) := by
  rw [summable_prod_of_nonneg (fun x =>
    mul_nonneg (hweight x.1) (phaseLadderWeight_nonneg x.2))]
  constructor
  · intro j
    exact phaseLadderWeight_summable.mul_left (weight j)
  · exact (hasSum_fintype _).summable

/-- Unit-state candidate whose Born weights are the product spectral weights. -/
def phaseLadderKet
    {m : ℕ} (weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) :
    PhaseLadderSpace m :=
  ⟨fun x => (Real.sqrt
      (weight x.1 * phaseLadderWeight x.2) : ℂ),
    HilbertSchmidt.memℓp_of_sq (by
      apply (phaseLadderProductWeight_summable weight hweight).congr
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt
          (mul_nonneg (hweight x.1)
            (phaseLadderWeight_nonneg x.2))])⟩

@[simp] theorem phaseLadderKet_apply
    {m : ℕ} (weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    (x : Fin (m + 1) × ℕ) :
    phaseLadderKet weight hweight x =
      (Real.sqrt
        (weight x.1 * phaseLadderWeight x.2) : ℂ) :=
  rfl

/-- Exact diagonal time evolution of the infinite phase-ladder state. -/
def phaseLadderKetAt
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) (t : ℝ) :
    PhaseLadderSpace m :=
  ⟨fun x =>
      (Real.sqrt
        (weight x.1 * phaseLadderWeight x.2) : ℂ) *
        Complex.exp
          (((phaseLadderEnergy T energy x * t : ℝ) : ℂ) * I),
    HilbertSchmidt.memℓp_of_sq (by
      apply (phaseLadderProductWeight_summable weight hweight).congr
      intro x
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt
          (mul_nonneg (hweight x.1)
            (phaseLadderWeight_nonneg x.2))])⟩

@[simp] theorem phaseLadderKetAt_apply
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) (t : ℝ)
    (x : Fin (m + 1) × ℕ) :
    phaseLadderKetAt T energy weight hweight t x =
      (Real.sqrt
        (weight x.1 * phaseLadderWeight x.2) : ℂ) *
        Complex.exp
          (((phaseLadderEnergy T energy x * t : ℝ) : ℂ) * I) :=
  rfl

theorem phaseLadderKetAt_zero
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) :
    phaseLadderKetAt T energy weight hweight 0 =
      phaseLadderKet weight hweight := by
  apply lp.ext
  funext x
  simp

theorem phaseLadderKet_norm
    {m : ℕ} {weight : Fin (m + 1) → ℝ}
    (hweight : ∀ j, 0 ≤ weight j)
    (hsum : ∑ j, weight j = 1) :
    ‖phaseLadderKet weight hweight‖ = 1 := by
  have hnormsq : ‖phaseLadderKet weight hweight‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    have hprod := phaseLadderProductWeight_summable weight hweight
    rw [show (∑' x : Fin (m + 1) × ℕ,
        ‖phaseLadderKet weight hweight x‖ ^ 2) =
        ∑' x : Fin (m + 1) × ℕ,
          weight x.1 * phaseLadderWeight x.2 by
      apply tsum_congr
      intro x
      rw [phaseLadderKet_apply, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt
          (mul_nonneg (hweight x.1)
            (phaseLadderWeight_nonneg x.2))]]
    rw [hprod.tsum_prod]
    simp_rw [tsum_mul_left, phaseLadderWeight_tsum, mul_one]
    rw [tsum_fintype, hsum]
  nlinarith [norm_nonneg (phaseLadderKet weight hweight)]

theorem phaseLadderKetAt_norm
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    (hsum : ∑ j, weight j = 1) (t : ℝ) :
    ‖phaseLadderKetAt T energy weight hweight t‖ = 1 := by
  have hnormsq :
      ‖phaseLadderKetAt T energy weight hweight t‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    have hprod := phaseLadderProductWeight_summable weight hweight
    rw [show (∑' x : Fin (m + 1) × ℕ,
        ‖phaseLadderKetAt T energy weight hweight t x‖ ^ 2) =
        ∑' x : Fin (m + 1) × ℕ,
          weight x.1 * phaseLadderWeight x.2 by
      apply tsum_congr
      intro x
      rw [phaseLadderKetAt_apply, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt
          (mul_nonneg (hweight x.1)
            (phaseLadderWeight_nonneg x.2))]]
    rw [hprod.tsum_prod]
    simp_rw [tsum_mul_left, phaseLadderWeight_tsum, mul_one]
    rw [tsum_fintype, hsum]
  nlinarith [norm_nonneg
    (phaseLadderKetAt T energy weight hweight t)]

/-- Finite spectral survival amplitude before the ladder lift. -/
def finiteSpectralAmplitude
    {m : ℕ} (energy weight : Fin (m + 1) → ℝ)
    (t : ℝ) : ℂ :=
  ∑ j : Fin (m + 1), (weight j : ℂ) *
    Complex.exp (((energy j * t : ℝ) : ℂ) * I)

theorem phaseLadderPhase_factor
    {m : ℕ} (T : ℝ) (energy : Fin (m + 1) → ℝ)
    (t : ℝ) (x : Fin (m + 1) × ℕ) :
    Complex.exp
        (((phaseLadderEnergy T energy x * t : ℝ) : ℂ) * I) =
      Complex.exp (((energy x.1 * t : ℝ) : ℂ) * I) *
        phaseLadderPhase T t x.2 := by
  unfold phaseLadderEnergy phaseLadderPhase
  rw [show
      (((energy x.1 + 2 * Real.pi * (x.2 : ℝ) / T) * t : ℝ) : ℂ) * I =
        (((energy x.1 * t : ℝ) : ℂ) * I) +
          ((((t / T) * (x.2 : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) by
    push_cast
    ring, Complex.exp_add]

theorem phaseLadderReturnAmplitude_factor
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) (t : ℝ) :
    inner ℂ (phaseLadderKet weight hweight)
        (phaseLadderKetAt T energy weight hweight t) =
      finiteSpectralAmplitude energy weight t *
        phaseLadderAmplitude T t := by
  rw [lp.inner_eq_tsum]
  have hprod : Summable (fun x : Fin (m + 1) × ℕ =>
      ((weight x.1 * phaseLadderWeight x.2 : ℝ) : ℂ) *
        Complex.exp
          (((phaseLadderEnergy T energy x * t : ℝ) : ℂ) * I)) := by
    apply Summable.of_norm
    apply (phaseLadderProductWeight_summable weight hweight).congr
    intro x
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg (hweight x.1)
          (phaseLadderWeight_nonneg x.2))]
  rw [show (fun x : Fin (m + 1) × ℕ =>
      inner ℂ (phaseLadderKet weight hweight x)
        (phaseLadderKetAt T energy weight hweight t x)) =
      fun x =>
        ((weight x.1 * phaseLadderWeight x.2 : ℝ) : ℂ) *
          Complex.exp
            (((phaseLadderEnergy T energy x * t : ℝ) : ℂ) * I) by
    funext x
    rw [phaseLadderKet_apply, phaseLadderKetAt_apply,
      RCLike.inner_apply, Complex.conj_ofReal]
    calc
      (Real.sqrt
          (weight x.1 * phaseLadderWeight x.2) : ℂ) *
            Complex.exp
              (((phaseLadderEnergy T energy x * t : ℝ) : ℂ) * I) *
          (Real.sqrt
            (weight x.1 * phaseLadderWeight x.2) : ℂ) =
        ((Real.sqrt
          (weight x.1 * phaseLadderWeight x.2) ^ 2 : ℝ) : ℂ) *
            Complex.exp
              (((phaseLadderEnergy T energy x * t : ℝ) : ℂ) * I) := by
          push_cast
          ring
      _ = _ := by
        rw [Real.sq_sqrt
          (mul_nonneg (hweight x.1)
            (phaseLadderWeight_nonneg x.2))]]
  rw [hprod.tsum_prod]
  simp_rw [phaseLadderPhase_factor]
  rw [tsum_fintype]
  rw [finiteSpectralAmplitude, phaseLadderAmplitude,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← (phaseLadderAmplitude_summable T t).tsum_mul_left]
  apply tsum_congr
  intro k
  push_cast
  ring

theorem finiteSpectralAmplitude_angular
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (t : ℝ) :
    finiteSpectralAmplitude
        (angularEnergy T n) (interpolatedWeight n θ) t =
      scaledInterpolatedAmplitude T n θ t := by
  rw [← scaledInterpolatedClock_survivalAmplitude
    hT n hθ0 hθ1 t]
  rw [interpolatedClock, scaledInterpolatedClockAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (interpolatedWeight_nonneg n hθ0 hθ1)]
  unfold finiteSpectralAmplitude
  apply Finset.sum_congr rfl
  intro j _hj
  rw [scaledPhase_eq_angular]

/-- Observable return probability of the genuine infinite phase-ladder system. -/
def phaseLadderReturnProbability
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) (t : ℝ) : ℝ :=
  ‖inner ℂ (phaseLadderKet weight hweight)
      (phaseLadderKetAt T energy weight hweight t)‖ ^ 2

theorem phaseLadderReturnProbability_factor
    {m : ℕ} (T : ℝ) (energy weight : Fin (m + 1) → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) (t : ℝ) :
    phaseLadderReturnProbability T energy weight hweight t =
      ‖finiteSpectralAmplitude energy weight t‖ ^ 2 *
        ‖phaseLadderAmplitude T t‖ ^ 2 := by
  rw [phaseLadderReturnProbability,
    phaseLadderReturnAmplitude_factor, norm_mul]
  ring

/-- The concrete infinite lift of the interpolated clock family. -/
def infiniteInterpolatedReturnProbability
    (T : ℝ) (n : ℕ) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) : ℝ :=
  phaseLadderReturnProbability T
    (angularEnergy T n) (interpolatedWeight n θ)
    (interpolatedWeight_nonneg n hθ0 hθ1) t

theorem infiniteInterpolatedReturnProbability_factor
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (t : ℝ) :
    infiniteInterpolatedReturnProbability T n θ hθ0 hθ1 t =
      scaledInterpolatedProbability T n θ t *
        ‖phaseLadderAmplitude T t‖ ^ 2 := by
  rw [infiniteInterpolatedReturnProbability,
    phaseLadderReturnProbability_factor,
    finiteSpectralAmplitude_angular hT n hθ0 hθ1]
  rfl

theorem infiniteInterpolatedReturnProbability_target
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    infiniteInterpolatedReturnProbability T n θ hθ0 hθ1 T =
      θ ^ 2 := by
  rw [infiniteInterpolatedReturnProbability_factor
      hT n hθ0 hθ1,
    scaledInterpolatedProbability_target hT hn hθ0,
    phaseLadderAmplitude_target hT, norm_one, one_pow,
    mul_one]

theorem infiniteInterpolated_difference_le_finite
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    {θ φ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (t : ℝ) :
    |infiniteInterpolatedReturnProbability T n θ hθ0 hθ1 t -
        infiniteInterpolatedReturnProbability T n φ hφ0 hφ1 t| ≤
      |scaledInterpolatedProbability T n θ t -
        scaledInterpolatedProbability T n φ t| := by
  rw [infiniteInterpolatedReturnProbability_factor
      hT n hθ0 hθ1,
    infiniteInterpolatedReturnProbability_factor
      hT n hφ0 hφ1,
    ← sub_mul, abs_mul]
  have hL0 : 0 ≤ ‖phaseLadderAmplitude T t‖ ^ 2 := sq_nonneg _
  have hL1 : ‖phaseLadderAmplitude T t‖ ^ 2 ≤ 1 := by
    nlinarith [phaseLadderAmplitude_norm_le_one T t,
      norm_nonneg (phaseLadderAmplitude T t)]
  rw [abs_of_nonneg hL0]
  exact mul_le_of_le_one_right (abs_nonneg _) hL1

/-- Norm-unboundedness on a partial operator's unit vectors. -/
def LinearPMap.IsNormUnbounded
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  ∀ C : ℝ, ∃ x : A.domain, ‖(x : H)‖ = 1 ∧ C < ‖A x‖

theorem phaseLadderEnergy_unbounded
    {m : ℕ} {T : ℝ} (hT : 0 < T)
    (energy : Fin (m + 1) → ℝ) (C : ℝ) :
    ∃ k : ℕ, C <
      phaseLadderEnergy T energy (0, k) := by
  let c : ℝ := 2 * Real.pi / T
  have hc : 0 < c := div_pos
    (mul_pos (by norm_num) Real.pi_pos) hT
  obtain ⟨k, hk⟩ := exists_nat_gt ((C - energy 0) / c)
  refine ⟨k, ?_⟩
  unfold phaseLadderEnergy
  have hscaled : C - energy 0 < c * (k : ℝ) := by
    have hmul :
        c * ((C - energy 0) / c) < c * (k : ℝ) :=
      mul_lt_mul_of_pos_left hk hc
    have hleft :
        c * ((C - energy 0) / c) = C - energy 0 := by
      field_simp [hc.ne']
    rwa [hleft] at hmul
  have heq :
      c * (k : ℝ) =
        2 * Real.pi * (k : ℝ) / T := by
    unfold c
    ring
  rw [heq] at hscaled
  linarith

theorem phaseLadderHamiltonian_isNormUnbounded
    {m : ℕ} {T : ℝ} (hT : 0 < T)
    (energy : Fin (m + 1) → ℝ) :
    LinearPMap.IsNormUnbounded
      (RHTower.maximalRealDiagonal
        (phaseLadderEnergy T energy)) := by
  intro C
  obtain ⟨k, hk⟩ :=
    phaseLadderEnergy_unbounded hT energy (max C 0)
  let i : Fin (m + 1) × ℕ := (0, k)
  let e :
      (RHTower.maximalRealDiagonal
        (phaseLadderEnergy T energy)).domain :=
    ⟨HilbertSchmidt.lpBasis _ i,
      RHTower.lpBasis_mem_maximalRealDiagonalDomain _ i⟩
  refine ⟨e, ?_, ?_⟩
  · change ‖HilbertSchmidt.lpBasis (Fin (m + 1) × ℕ) i‖ = 1
    exact (HilbertSchmidt.lpBasis _).orthonormal.norm_eq_one i
  · have henergy :
        0 < phaseLadderEnergy T energy i := by
      exact (le_max_right C 0).trans_lt hk
    rw [show
        RHTower.maximalRealDiagonal
            (phaseLadderEnergy T energy) e =
          (phaseLadderEnergy T energy i : ℂ) •
            HilbertSchmidt.lpBasis (Fin (m + 1) × ℕ) i by
      apply lp.ext
      funext j
      rw [RHTower.maximalRealDiagonal_apply]
      change
        (phaseLadderEnergy T energy j : ℂ) *
            (HilbertSchmidt.lpBasis _ i) j =
          (phaseLadderEnergy T energy i : ℂ) *
            (HilbertSchmidt.lpBasis _ i) j
      by_cases hji : j = i
      · subst j
        rfl
      · rw [HilbertSchmidt.lpBasis_apply,
          lp.single_apply_ne _ _ _ hji]
        simp,
      norm_smul,
      (HilbertSchmidt.lpBasis _).orthonormal.norm_eq_one,
      mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos henergy]
    exact (le_max_left C 0).trans_lt hk

/-- One fully physical infinite-system witness for the local-horizon law. -/
structure InfiniteLocalHorizonWitness
    (R : ℕ) (T H p δ : ℝ) where
  q : ℕ
  horder : 2 * R + 2 < endpointN q
  hsize : R + 2 ≤ endpointN q + 1
  sqrt_le_one : Real.sqrt p ≤ 1
  baseline :
    FixedEndpointPathModel T (endpointN q) 0
  model :
    FixedEndpointPathModel T (endpointN q) (Real.sqrt p)
  baseline_nearestNeighbor :
    NearestNeighborHamiltonian baseline.hamiltonian
  model_nearestNeighbor :
    NearestNeighborHamiltonian model.hamiltonian
  baseline_selfAdjoint :
    ContinuousLinearMap.adjoint baseline.hamiltonian =
      baseline.hamiltonian
  model_selfAdjoint :
    ContinuousLinearMap.adjoint model.hamiltonian =
      model.hamiltonian
  local_eq :
    ∀ i j : Fin (R + 2),
      (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
      inner ℂ
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ
            (Fin.castLE hsize i))
          (model.hamiltonian
            (EuclideanSpace.basisFun
              (Fin (endpointN q + 1)) ℂ
              (Fin.castLE hsize j))) =
        inner ℂ
          (EuclideanSpace.basisFun
            (Fin (endpointN q + 1)) ℂ
            (Fin.castLE hsize i))
          (baseline.hamiltonian
            (EuclideanSpace.basisFun
              (Fin (endpointN q + 1)) ℂ
              (Fin.castLE hsize j)))
  infiniteHamiltonian_selfAdjoint :
    IsSelfAdjoint
      (RHTower.maximalRealDiagonal
        (phaseLadderEnergy T
          (angularEnergy T (endpointN q))))
  infiniteHamiltonian_unbounded :
    LinearPMap.IsNormUnbounded
      (RHTower.maximalRealDiagonal
        (phaseLadderEnergy T
          (angularEnergy T (endpointN q))))
  infinitelyManyDistinctLevels :
    ∀ j : Fin (endpointN q + 1),
      Function.Injective
        (fun k : ℕ =>
          phaseLadderEnergy T
            (angularEnergy T (endpointN q)) (j, k))
  baselineInfiniteState_normalized :
    ‖phaseLadderKet
      (interpolatedWeight (endpointN q) 0)
      (interpolatedWeight_nonneg
        (endpointN q) (by norm_num) (by norm_num))‖ = 1
  modelInfiniteState_normalized :
    ‖phaseLadderKet
      (interpolatedWeight (endpointN q) (Real.sqrt p))
      (interpolatedWeight_nonneg
        (endpointN q) (Real.sqrt_nonneg p) sqrt_le_one)‖ = 1
  earlierInfiniteRecord :
    ∀ t : ℝ, |t| ≤ H →
      |infiniteInterpolatedReturnProbability
          T (endpointN q) (Real.sqrt p)
          (Real.sqrt_nonneg p) sqrt_le_one t -
        infiniteInterpolatedReturnProbability
          T (endpointN q) 0
          (by norm_num) (by norm_num) t| < δ
  exactInfiniteTarget :
    infiniteInterpolatedReturnProbability
        T (endpointN q) (Real.sqrt p)
        (Real.sqrt_nonneg p) sqrt_le_one T = p

/--
**Universal infinite local-horizon law.**

For every finite observation radius, every positive future time, every strict earlier window,
every positive tolerance, and every target probability in `[0,1]`, there is a countably
infinite-dimensional quantum system with:

* a maximal self-adjoint, genuinely unbounded Hamiltonian;
* infinitely many distinct energy levels above every finite spectral coordinate;
* normalized initial and evolved states;
* an exactly common finite nearest-neighbour Hamiltonian record through the requested radius;
* an earlier infinite-system return record within the requested tolerance;
* exactly the prescribed future return probability.
-/
theorem exists_infiniteLocalHorizonWitness
    (R : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Nonempty (InfiniteLocalHorizonWitness R T H p δ) := by
  obtain ⟨q, horder, hsize, baseline, hbaselineNN,
      hbaselineSA, hall⟩ :=
    localHorizon_every_future_probability
      R T H hT hH0 hHT hδ
  obtain ⟨M, hMNN, hMSA, _hintertwines, hlocal,
      hwindow, _htarget⟩ := hall p hp
  have hn : 0 < endpointN q := by
    simp [endpointN]
  have hsqrt_le : Real.sqrt p ≤ 1 :=
    Real.sqrt_le_one.mpr hp.2
  have hbaselineNorm :
      ‖phaseLadderKet
        (interpolatedWeight (endpointN q) 0)
        (interpolatedWeight_nonneg
          (endpointN q) (by norm_num) (by norm_num))‖ = 1 := by
    apply phaseLadderKet_norm
    exact interpolatedWeight_sum hn 0
  have hmodelNorm :
      ‖phaseLadderKet
        (interpolatedWeight (endpointN q) (Real.sqrt p))
        (interpolatedWeight_nonneg
          (endpointN q) (Real.sqrt_nonneg p) hsqrt_le)‖ = 1 := by
    apply phaseLadderKet_norm
    exact interpolatedWeight_sum hn (Real.sqrt p)
  refine ⟨{
    q := q
    horder := horder
    hsize := hsize
    sqrt_le_one := hsqrt_le
    baseline := baseline
    model := M
    baseline_nearestNeighbor := hbaselineNN
    model_nearestNeighbor := hMNN
    baseline_selfAdjoint := hbaselineSA
    model_selfAdjoint := hMSA
    local_eq := hlocal
    infiniteHamiltonian_selfAdjoint :=
      phaseLadderHamiltonian_selfAdjoint T
        (angularEnergy T (endpointN q))
    infiniteHamiltonian_unbounded :=
      phaseLadderHamiltonian_isNormUnbounded hT
        (angularEnergy T (endpointN q))
    infinitelyManyDistinctLevels := fun j =>
      phaseLadderEnergy_injective_nat hT
        (angularEnergy T (endpointN q)) j
    baselineInfiniteState_normalized := hbaselineNorm
    modelInfiniteState_normalized := hmodelNorm
    earlierInfiniteRecord := ?_
    exactInfiniteTarget := ?_ }⟩
  · intro t ht
    have hfinite :
        |scaledInterpolatedProbability
            T (endpointN q) (Real.sqrt p) t -
          scaledInterpolatedProbability
            T (endpointN q) 0 t| < δ := by
      rw [← M.returnProbability_eq hT
          (Real.sqrt_nonneg p) hsqrt_le,
        ← baseline.returnProbability_eq hT
          (by norm_num) (by norm_num)]
      exact hwindow t ht
    exact lt_of_le_of_lt
      (infiniteInterpolated_difference_le_finite
        hT (endpointN q)
        (Real.sqrt_nonneg p) hsqrt_le
        (by norm_num) (by norm_num) t)
      hfinite
  · rw [infiniteInterpolatedReturnProbability_target
      hT hn (Real.sqrt_nonneg p) hsqrt_le,
    Real.sq_sqrt hp.1]

end RHTower.ParityForecast
