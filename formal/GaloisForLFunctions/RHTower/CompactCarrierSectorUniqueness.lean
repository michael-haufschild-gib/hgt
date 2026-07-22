import GaloisForLFunctions.RHTower.CompactCarrierLambert
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# Sectorial uniqueness for actual compact-carrier Euler tangents

This file assembles the compact Banach carrier, the actual prime Euler-unit
tangent, and the PNT-free prime-log Blaschke theorem.  Its geometric input is
stated directly as uniform positivity of `Re (z s)` on every translated sector
pullback; subsequent domain modules verify that input for the carriers they
use.
-/

noncomputable section

namespace RHTower

open Complex Metric Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Uniform positivity of a compact carrier on every translated sector-root
pullback. -/
def UniformSectorCarrierPositive
    (s : C(K, ℂ)) (n : ℕ) (R₀ : ℝ) : Prop :=
  ∀ R ≥ R₀, ∃ d : ℝ, 0 < d ∧
    ∀ z ∈ ball (0 : ℂ) 1, ∀ k : K,
      d ≤ (sectorRootMap n R z * s k).re

/-- The sector positivity hypothesis makes the compact-carrier Lambert
transform analytic on every translated sector pullback. -/
theorem compactCarrierLambert_sector_analytic
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {n : ℕ} {R₀ : ℝ} (hsector : UniformSectorCarrierPositive s n R₀) :
    ∀ R ≥ R₀,
      AnalyticOnNhd ℂ
        (fun z => compactCarrierLambertTransform L s (sectorRootMap n R z))
        (ball 0 1) := by
  intro R hRR₀
  obtain ⟨d, hd, hpos⟩ := hsector R hRR₀
  intro z hz
  have hq : ‖compactExponentialTest s (sectorRootMap n R z)‖ < 1 :=
    norm_compactExponentialTest_lt_one_of_re_pos s _ d hd (hpos z hz)
  have hH := compactCarrierLambertTransform_analyticAt L s _ hq
  have hroot := sectorRootMap_analyticOnNhd n R z hz
  simpa [Function.comp_def] using hH.comp
    (f := sectorRootMap n R) (x := z) hroot

/-- The same sector positivity gives a uniform bound on each translated
pullback. -/
theorem compactCarrierLambert_sector_bounded
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {n : ℕ} {R₀ : ℝ} (hsector : UniformSectorCarrierPositive s n R₀) :
    ∀ R ≥ R₀, ∃ M : ℝ, 1 ≤ M ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        ‖compactCarrierLambertTransform L s (sectorRootMap n R z)‖ ≤ M := by
  intro R hRR₀
  obtain ⟨d, hd, hpos⟩ := hsector R hRR₀
  let r : ℝ := Real.exp (-d)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    simpa [r] using (Real.exp_lt_one_iff.mpr (show -d < 0 by linarith))
  let A : ℝ := ‖L‖ * ∑' m : ℕ, (m : ℝ) * r ^ m
  refine ⟨max 1 A, le_max_left _ _, fun z hz => ?_⟩
  have hqr : ‖compactExponentialTest s (sectorRootMap n R z)‖ ≤ r := by
    exact norm_compactExponentialTest_le_exp_neg_of_re s _ d (hpos z hz)
  have hk := norm_compactLambertKernel_le_geometricMajorant s _ r hr0 hr1 hqr
  have hL := L.le_opNorm (compactLambertKernel s (sectorRootMap n R z))
  calc
    ‖compactCarrierLambertTransform L s (sectorRootMap n R z)‖
        ≤ ‖L‖ * ‖compactLambertKernel s (sectorRootMap n R z)‖ := by
          simpa [compactCarrierLambertTransform] using hL
    _ ≤ A := by dsimp [A]; gcongr
    _ ≤ max 1 A := le_max_right _ _

/-- Prime-log zeros of the compact-carrier Lambert transform follow directly
from annihilation of the actual compact Euler-unit tangents. -/
theorem compactCarrierLambert_primeLog_zero
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {R₀ : ℝ}
    (hann : ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      L (compactPrimeEulerUnitTangent s (p : ℕ)) = 0) :
    ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      compactCarrierLambertTransform L s (Real.log (p : ℝ)) = 0 := by
  intro p hp
  exact compactCarrierLambertTransform_primeLog_eq_zero_of_annihilates
    L s p.prop.two_le (hann p hp)

/-- Cofinite annihilation of the actual Euler tangents forces the
compact-carrier Lambert transform to vanish on a full positive ray. -/
theorem compactCarrierLambert_zero_on_ray
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {n : ℕ} (hn : n ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hsector : UniformSectorCarrierPositive s n R₀)
    (hann : ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      L (compactPrimeEulerUnitTangent s (p : ℕ)) = 0) :
    ∀ x : ℝ, R₀ + 1 ≤ x →
      compactCarrierLambertTransform L s x = 0 := by
  apply primeLog_zero_uniqueness_on_ray hn R₀ hR₀
  · exact compactCarrierLambert_sector_analytic L s hsector
  · exact compactCarrierLambert_sector_bounded L s hsector
  · exact compactCarrierLambert_primeLog_zero L s hann

/-- The complete Lambert--Mobius recovery: cofinite annihilation of the actual
Euler tangents forces the compact Fourier--Borel transform itself to vanish
identically. -/
theorem compactFourierBorel_eq_zero_of_tangent_annihilation
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {n : ℕ} (hn : n ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hsector : UniformSectorCarrierPositive s n R₀)
    (hann : ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      L (compactPrimeEulerUnitTangent s (p : ℕ)) = 0) :
    ∀ z : ℂ, compactFourierBorel L s z = 0 := by
  have hHray := compactCarrierLambert_zero_on_ray L s hn hR₀ hsector hann
  apply entire_eq_zero_of_lambert_ray_zero
    (compactFourierBorel L s) (R₀ + 1) (compactFourierBorel_analyticOnNhd L s)
  intro x hx
  · let R : ℝ := x - 1
    have hRR₀ : R₀ ≤ R := by dsimp [R]; linarith
    obtain ⟨d, hd, hpos⟩ := hsector R hRR₀
    have hbase : ∀ k : K, d ≤ ((x : ℂ) * s k).re := by
      intro k
      have hk := hpos 0 (by simp) k
      simpa [R] using hk
    let r : ℝ := Real.exp (-d)
    have hr0 : 0 ≤ r := Real.exp_nonneg _
    have hr1 : r < 1 := by
      simpa [r] using (Real.exp_lt_one_iff.mpr (show -d < 0 by linarith))
    have hdecay : ∀ m : ℕ+,
        ‖compactFourierBorel L s ((m : ℂ) * x)‖ ≤
          ‖L‖ * r ^ (m : ℕ) := by
      intro m
      have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.prop
      have hmre : ∀ k : K,
          (m : ℝ) * d ≤ (((m : ℂ) * (x : ℂ)) * s k).re := by
        intro k
        have hk := hbase k
        have hmxcast : (m : ℂ) * (x : ℂ) = (((m : ℝ) * x : ℝ) : ℂ) := by
          norm_cast
        calc
          (m : ℝ) * d ≤ (m : ℝ) * (((x : ℂ) * s k).re) :=
            mul_le_mul_of_nonneg_left hk hmpos.le
          _ = (((m : ℂ) * (x : ℂ)) * s k).re := by
            rw [hmxcast]
            simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
            ring
      have htest := norm_compactExponentialTest_le_exp_neg_of_re s
        ((m : ℂ) * (x : ℂ)) ((m : ℝ) * d) hmre
      have hL := L.le_opNorm (compactExponentialTest s ((m : ℂ) * (x : ℂ)))
      calc
        ‖compactFourierBorel L s ((m : ℂ) * x)‖
            ≤ ‖L‖ * ‖compactExponentialTest s ((m : ℂ) * (x : ℂ))‖ := by
              simpa [compactFourierBorel] using hL
        _ ≤ ‖L‖ * Real.exp (-((m : ℝ) * d)) := by gcongr
        _ = ‖L‖ * r ^ (m : ℕ) := by
          congr 1
          rw [show -((m : ℝ) * d) = (m : ℕ) * (-d) by ring,
            Real.exp_nat_mul]
    have hzero : ∀ m : ℕ+,
        positiveLambertDerivative (compactFourierBorel L s)
          ((m : ℂ) * (x : ℂ)) = 0 := by
      intro m
      have hmone : (1 : ℝ) ≤ (m : ℕ) := by exact_mod_cast m.prop
      have hxpos : 0 < x := by linarith
      have hmx : R₀ + 1 ≤ (m : ℝ) * x := by nlinarith
      have htransform : compactCarrierLambertTransform L s
          ((m : ℂ) * (x : ℂ)) = 0 := by
        simpa using hHray ((m : ℝ) * x) hmx
      have hq : ‖compactExponentialTest s ((m : ℂ) * (x : ℂ))‖ < 1 := by
        have hmre : ∀ k : K,
            (m : ℝ) * d ≤ (((m : ℂ) * (x : ℂ)) * s k).re := by
          intro k
          have hk := hbase k
          have hmxcast : (m : ℂ) * (x : ℂ) = (((m : ℝ) * x : ℝ) : ℂ) := by
            norm_cast
          calc
            (m : ℝ) * d ≤ (m : ℝ) * (((x : ℂ) * s k).re) :=
              mul_le_mul_of_nonneg_left hk (by exact_mod_cast m.prop.le)
            _ = (((m : ℂ) * (x : ℂ)) * s k).re := by
              rw [hmxcast]
              simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
              ring
        exact norm_compactExponentialTest_lt_one_of_re_pos s _ ((m : ℝ) * d)
          (mul_pos (by exact_mod_cast m.prop) hd) hmre
      rw [positiveLambertDerivative_compactFourierBorel L s _ hq]
      exact htransform
    exact ⟨‖L‖, r, norm_nonneg L, hr0, hr1, hdecay, hzero⟩

end RHTower
