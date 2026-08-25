import GaloisForLFunctions.RHTower.CriticalPrimeKernelSampling
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem criticalPrimeCoordinateHead_bound (P : Finset Nat.Primes) (p : Nat.Primes) :
    ‖(if p ∈ P then (1 : ℂ) else 0)‖ ≤ 1 := by
  by_cases hp : p ∈ P <;> simp [hp]

/-- Orthogonal cutoff to a finite set of prime coordinates. -/
def criticalPrimeCoordinateHead (P : Finset Nat.Primes) :
    CriticalPrimeEllTwo →L[ℂ] CriticalPrimeEllTwo :=
  GaloisForLFunctions.HTGeometry.LpDiagonal.lpDiag
    (fun p => if p ∈ P then (1 : ℂ) else 0) 1 zero_le_one
    (criticalPrimeCoordinateHead_bound P)

@[simp] theorem criticalPrimeCoordinateHead_apply
    (P : Finset Nat.Primes) (v : CriticalPrimeEllTwo) (p : Nat.Primes) :
    criticalPrimeCoordinateHead P v p = if p ∈ P then v p else 0 := by
  rw [criticalPrimeCoordinateHead,
    GaloisForLFunctions.HTGeometry.LpDiagonal.lpDiag_coe]
  by_cases hp : p ∈ P <;> simp [hp]

theorem criticalPrimeCoordinateHead_isCompactOperator (P : Finset Nat.Primes) :
    IsCompactOperator (criticalPrimeCoordinateHead P) := by
  classical
  have h := GaloisForLFunctions.HTGeometry.LpDiagonal.isCompactOperator_lpDiagFinset
    (I := Nat.Primes) (fun _ => (1 : ℂ)) P
  have hfun :
      (fun v : CriticalPrimeEllTwo =>
        ∑ p ∈ P, lp.single (E := fun _ : Nat.Primes => ℂ) 2 p (v p)) =
        criticalPrimeCoordinateHead P := by
    funext v
    symm
    simpa [criticalPrimeCoordinateHead] using
      (GaloisForLFunctions.HTGeometry.LpDiagonal.lpDiag_indicator_eq_sum
        (I := Nat.Primes) (fun _ => (1 : ℂ)) 1 zero_le_one P
        (criticalPrimeCoordinateHead_bound P) v)
  rw [← hfun]
  simpa using h

/-- Finite-prime head of the normalized kernel sampler. -/
def criticalPrimeKernelSamplingHead
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (P : Finset Nat.Primes) : H →L[ℂ] CriticalPrimeEllTwo :=
  criticalPrimeCoordinateHead P ∘L
    criticalPrimeKernelSamplingOperator k hsummable hC hBessel

@[simp] theorem criticalPrimeKernelSamplingHead_apply
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (P : Finset Nat.Primes) (x : H) (p : Nat.Primes) :
    criticalPrimeKernelSamplingHead k hsummable hC hBessel P x p =
      if p ∈ P then criticalPrimeKernelRestriction k p x else 0 := by
  simp [criticalPrimeKernelSamplingHead]

theorem criticalPrimeKernelSamplingHead_isCompactOperator
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (P : Finset Nat.Primes) :
    IsCompactOperator (criticalPrimeKernelSamplingHead k hsummable hC hBessel P) := by
  exact (criticalPrimeCoordinateHead_isCompactOperator P).comp_clm _

theorem norm_criticalPrimeKernelSamplingOperator_sub_head_le
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (P : Finset Nat.Primes) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ x,
      ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (ε * ‖x‖) ^ (2 : ℝ)) :
    ‖criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
        criticalPrimeKernelSamplingHead k hsummable hC hBessel P‖ ≤ ε := by
  refine opNorm_le_bound _ hε fun x => ?_
  have hleft : 0 ≤ ‖(criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
      criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x‖ := norm_nonneg _
  have hright : 0 ≤ ε * ‖x‖ := mul_nonneg hε (norm_nonneg _)
  have hdiag :
      ‖(criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
          criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x‖ ^ (2 : ℝ) =
        ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) := by
    have hnorm := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : Nat.Primes => ℂ)
      (by norm_num)
      ((criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
        criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x)
    calc
      ‖(criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
          criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x‖ ^ (2 : ℝ) =
          ∑' p, ‖((criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
            criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x :
              CriticalPrimeEllTwo) p‖ ^ (2 : ℝ) := by simpa using hnorm
      _ = ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) := by
        congr 1
        funext p
        change ‖criticalPrimeKernelSamplingOperator k hsummable hC hBessel x p -
          criticalPrimeKernelSamplingHead k hsummable hC hBessel P x p‖ ^ (2 : ℝ) = _
        rw [criticalPrimeKernelSamplingOperator_apply,
          criticalPrimeKernelSamplingHead_apply]
        by_cases hp : p ∈ P <;> simp [hp]
  have hpow :
      ‖(criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
          criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x‖ ^ (2 : ℝ) ≤
        (ε * ‖x‖) ^ (2 : ℝ) := by
    rw [hdiag]
    exact htail x
  have hleft2 :
      ‖(criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
          criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x‖ ^ (2 : ℝ) =
        ‖(criticalPrimeKernelSamplingOperator k hsummable hC hBessel -
          criticalPrimeKernelSamplingHead k hsummable hC hBessel P) x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : (ε * ‖x‖) ^ (2 : ℝ) = (ε * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

theorem criticalPrimeKernelSamplingOperator_isCompactOperator_of_tailBessel
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (P : ℕ → Finset Nat.Primes) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hε0 : Tendsto ε atTop (nhds 0))
    (htail : ∀ n x,
      ∑' p, ‖if p ∈ P n then 0 else criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (ε n * ‖x‖) ^ (2 : ℝ)) :
    IsCompactOperator (criticalPrimeKernelSamplingOperator k hsummable hC hBessel) := by
  let K : ℕ → (H →L[ℂ] CriticalPrimeEllTwo) := fun n =>
    criticalPrimeKernelSamplingHead k hsummable hC hBessel (P n)
  have hKcompact : ∀ n, IsCompactOperator (K n) := by
    intro n
    exact criticalPrimeKernelSamplingHead_isCompactOperator k hsummable hC hBessel (P n)
  have hdiff : ∀ n,
      ‖criticalPrimeKernelSamplingOperator k hsummable hC hBessel - K n‖ ≤ ε n := by
    intro n
    exact norm_criticalPrimeKernelSamplingOperator_sub_head_le
      k hsummable hC hBessel (P n) (hε n) (htail n)
  have htend : Tendsto K atTop
      (nhds (criticalPrimeKernelSamplingOperator k hsummable hC hBessel)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hε0
    rw [← norm_neg]
    simpa using hdiff n
  exact isCompactOperator_of_tendsto htend (Eventually.of_forall hKcompact)

end

end RHTower
