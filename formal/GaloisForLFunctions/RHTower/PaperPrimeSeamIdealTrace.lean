import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace
import GaloisForLFunctions.RHTower.XiPrimeSeamAdjacentEssentialNormNoGo

/-!
# Exact prime-seam cancellation through the compact ideal trace

The extended trace of the compact ideal assigns zero to a prime-seam Gram precisely when its
two endpoint charges agree. Along the prime ray, every tail has an infinite-cost edge exactly
at the off-critical strip points, even though the essential norms of the edges tend to zero.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry Filter Topology Classical
open scoped ENNReal

/-- The compact-ideal Gram trace of a canonical prime-seam edge. -/
def paperPrimeSeamTraceCost (a : Set.Ioi (0 : ℝ)) (rho : ℂ) (p q : Nat.Primes) : ℝ≥0∞ :=
  compactOperatorTraceCost evenSubspace (primeSeamCoboundary a.1 rho p q)

/-- Exact endpoint cancellation is the only finite-cost chamber. -/
theorem paperPrimeSeamTraceCost_eq (a : Set.Ioi (0 : ℝ)) (rho : ℂ) (p q : Nat.Primes) :
    paperPrimeSeamTraceCost a rho p q =
      if orbitwiseNatPrimeSeamCharge (p : ℕ) rho =
        orbitwiseNatPrimeSeamCharge (q : ℕ) rho then 0 else ∞ := by
  have h : IsCompactOperator (primeSeamCoboundary a.1 rho p q) ↔
      orbitwiseNatPrimeSeamCharge (p : ℕ) rho =
        orbitwiseNatPrimeSeamCharge (q : ℕ) rho := by
    constructor
    · exact seamCharge_eq_of_isCompactOperator_primeSeamCoboundary a.2
    · intro heq
      let T : evenSubspace →L[ℂ] evenSubspace :=
        evenCentralPositiveEulerQuadraticCorner a.1 ((p : ℕ) : ℝ) ((q : ℕ) : ℝ)
          (one_lt_natPrime_cast p) (one_lt_natPrime_cast q)
      have hzero : primeSeamCoboundary a.1 rho p q = 0 := by
        calc
          primeSeamCoboundary a.1 rho p q =
              (orbitwiseNatPrimeSeamCharge (p : ℕ) rho -
                orbitwiseNatPrimeSeamCharge (q : ℕ) rho) • T := rfl
          _ = (0 : ℂ) • T := congrArg (fun c : ℂ => c • T) (sub_eq_zero.mpr heq)
          _ = 0 := zero_smul ℂ T
      rw [hzero]
      exact isCompactOperator_zero
  simp only [paperPrimeSeamTraceCost, compactOperatorTraceCost_eq, h]

@[simp] theorem paperPrimeSeamTraceCost_eq_zero_iff
    (a : Set.Ioi (0 : ℝ)) (rho : ℂ) (p q : Nat.Primes) :
    paperPrimeSeamTraceCost a rho p q = 0 ↔
      orbitwiseNatPrimeSeamCharge (p : ℕ) rho = orbitwiseNatPrimeSeamCharge (q : ℕ) rho := by
  rw [paperPrimeSeamTraceCost_eq]
  split <;> simp_all

@[simp] theorem paperPrimeSeamTraceCost_eq_top_iff
    (a : Set.Ioi (0 : ℝ)) (rho : ℂ) (p q : Nat.Primes) :
    paperPrimeSeamTraceCost a rho p q = ∞ ↔
      orbitwiseNatPrimeSeamCharge (p : ℕ) rho ≠ orbitwiseNatPrimeSeamCharge (q : ℕ) rho := by
  rw [paperPrimeSeamTraceCost_eq]
  split <;> simp_all

/-- Every finite edge cost is already zero; no positive finite threshold is needed. -/
theorem paperPrimeSeamTraceCost_lt_top_iff
    (a : Set.Ioi (0 : ℝ)) (rho : ℂ) (p q : Nat.Primes) :
    paperPrimeSeamTraceCost a rho p q < ∞ ↔
      orbitwiseNatPrimeSeamCharge (p : ℕ) rho = orbitwiseNatPrimeSeamCharge (q : ℕ) rho := by
  rw [paperPrimeSeamTraceCost_eq]
  split <;> simp_all

/-- Eventual finite trace cost on the adjacent prime ray detects the critical line. -/
theorem paperPrimeSeamTraceCost_eventually_finite_iff
    (a : Set.Ioi (0 : ℝ)) (rho : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paperPrimeSeamTraceCost a rho.1 (primeRayPoint n) (primeRayPoint (n + 1)) < ∞) ↔
      rho.1.re = 1 / 2 := by
  simp only [paperPrimeSeamTraceCost_lt_top_iff, primeRayPoint_coe]
  constructor
  · exact re_eq_half_of_eventually_const_primeRay_seam rho.2
  · intro hre
    refine ⟨0, fun n _ => ?_⟩
    have hleft := (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half
      rho.1 _ (primeRay_prime n)).mpr hre
    have hright := (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half
      rho.1 _ (primeRay_prime (n + 1))).mpr hre
    exact hleft.trans hright.symm

/-- Off-critical strip points have an infinite-cost edge in every prime-ray tail. -/
theorem paperPrimeSeamTraceCost_cofinally_infinite_iff
    (a : Set.Ioi (0 : ℝ)) (rho : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      paperPrimeSeamTraceCost a rho.1 (primeRayPoint n) (primeRayPoint (n + 1)) = ∞) ↔
      rho.1.re ≠ 1 / 2 := by
  have h := not_congr (paperPrimeSeamTraceCost_eventually_finite_iff a rho)
  push Not at h
  simpa only [top_le_iff] using h

/-- Essential-norm decay coexists with cofinal infinite ideal-trace cost exactly off the line. -/
theorem paperPrimeSeamTraceCost_smallNorm_dichotomy
    (a : Set.Ioi (0 : ℝ)) (rho : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    Tendsto (fun n : ℕ => essentialNorm
      (primeSeamCoboundary a.1 rho.1 (primeRayPoint n) (primeRayPoint (n + 1))))
      atTop (𝓝 0) ∧
    ((∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      paperPrimeSeamTraceCost a rho.1 (primeRayPoint n) (primeRayPoint (n + 1)) = ∞) ↔
      rho.1.re ≠ 1 / 2) :=
  ⟨tendsto_primeRay_adjacent_essentialNorm_zero a.2 rho.1 rho.2,
    paperPrimeSeamTraceCost_cofinally_infinite_iff a rho⟩

/-- Compact perturbations of a seam presentation retain the exact trace cost. -/
theorem paperPrimeSeamTraceCost_compactPerturbation
    (a : Set.Ioi (0 : ℝ)) (rho : ℂ) (p q : Nat.Primes)
    (K : compactOperatorStarAlgebra evenSubspace) :
    compactOperatorTraceCost evenSubspace (primeSeamCoboundary a.1 rho p q + K.1) =
      paperPrimeSeamTraceCost a rho p q :=
  compactOperatorTraceCost_add_compact _ K

end

end RHTower
