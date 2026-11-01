import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormKeepsADefectReserveAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasFiniteRamanujanApproximation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilReserveHasPolynomialOverlapCost

/-!
# Nonpositive directions localize in a finite conductor sector

The localization question asks where the nonpositive directions of the complete Weil form can live.
Two facts answer it at every fixed overlap.

* **The complete form pays a fixed fraction of the jump energy.** For the tilted spline at every
  overlap `c > 0` there are `a > 0`, `C` with `E(x) ≥ a D_N(x) − C |x|²` eventually (CACT
  `exists_tiltedUnitSpline_complete_defect_reserve`). Here `D_N` is the pole defect, the dilation
  jump energy of `F = x√n` (`jumpEnergy_eq_poleDefect`). So nonpositive unit vectors have
  `D_N ≤ C/a` (`eventually_poleDefect_le_of_nonpos`).
* **Low jump energy is conductor structure.** A unit vector with `D_N ≤ K` lies within squared
  distance `η` of the span of finitely many Ramanujan conductor profiles `c_m(n)/√(φ(m)n)`,
  `m ∈ S(K, η)`, uniformly in `N` (RAPT `exists_finite_ramanujan_approximation_of_poleDefect_le`).
  The cutoff is exponential in `K/η`: prime dilations have spectral gap `≍ log p` on divisibility
  by `p`, so only small conductors carry low jump energy.

**Theorem** (`eventually_nonpos_localizes_in_conductor_sector`). At every fixed overlap `c > 0` and
for every `η > 0` there is a finite conductor set `S` such that, for all large `N`, every unit
vector with nonpositive complete Weil energy lies within squared distance `η` of the span of the
conductor profiles `m ∈ S`.

**Growing overlap** (`nonpos_localizes_uniformly_at_growing_overlap`). CACT's polynomial reserve
(fraction `a/c⁷`, mass cost `C c⁹`, valid for `N ≥ H c⁸`) bounds the jump energy of every
nonpositive unit vector by `(C/a) c¹⁶` (`poleDefect_le_of_nonpos_at_growing_overlap`). Hence, for every
`c ≥ 1` and `η > 0`, one finite conductor sector captures every nonpositive unit vector at every
horizon `N ≥ H c⁸`. This covers every schedule `c ≤ (N/H)^{1/8}`, in particular
`c ≤ (log N)^{1/4}`. In RAPT's construction the sector consists of the divisors of a `P`-smooth
modulus with `log P ≍ c¹⁶/η`.
-/

open Finset Filter Topology
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.SpacingScaleHarmonicAnalysis
  GaloisForLFunctions.CriticalArithmeticCorrelationTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- **Nonpositive directions have bounded jump energy at every fixed overlap.** -/
theorem eventually_poleDefect_le_of_nonpos {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, (∑ n ∈ Icc 1 N, x n ^ 2) = 1 →
      weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) ≤ 0 →
        poleDefect N x ≤ K := by
  obtain ⟨a, ha, C, hC, hreserve⟩ := exists_tiltedUnitSpline_complete_defect_reserve hc
  refine ⟨C / a, ?_⟩
  filter_upwards [hreserve, eventually_ge_atTop 1] with N hN hN1 x hx hE
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hden : 0 < (c / N) * ∫ u, tiltedUnitSpline u ^ 2 :=
    mul_pos (div_pos hc hN0) integral_tiltedUnitSpline_sq_pos
  have hq : weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hE hden.le
  have h := (hN x).trans hq
  rw [hx, mul_one] at h
  rw [le_div_iff₀ ha]
  linarith

/-- **Nonpositive directions localize in a finite conductor sector.** At every fixed overlap and
every precision `η > 0`, a finite set of conductors captures every nonpositive unit vector, for all
large horizons. -/
theorem eventually_nonpos_localizes_in_conductor_sector {c : ℝ} (hc : 0 < c) {η : ℝ}
    (hη : 0 < η) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, x n ^ 2) = 1 →
      weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) ≤ 0 →
        ∃ b : ℕ → ℝ, (∑ n ∈ Icc 1 N, (x n - ∑ m ∈ S, b m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  obtain ⟨K, hK⟩ := eventually_poleDefect_le_of_nonpos hc
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le K hη
  refine ⟨S, hS, ?_⟩
  filter_upwards [hK] with N hN x hx hE
  exact happ N x hx.le (hN x hx hE)

/-- In packet coordinates: a nonpositive packet has jump energy at most `K` times its mass. -/
theorem eventually_jumpEnergy_le_of_nonpos_at_overlap {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℝ, (∑ n ∈ Icc 1 N, F n ^ 2 / n) = 1 →
      weilQuad (atomicTest N (atomAmplitude F) (atomDilate tiltedUnitSpline (c / N))) ≤ 0 →
        jumpEnergy N F ≤ K := by
  obtain ⟨K, hK⟩ := eventually_poleDefect_le_of_nonpos hc
  refine ⟨K, ?_⟩
  filter_upwards [hK] with N hN F hF hE
  have hmass : (∑ n ∈ Icc 1 N, atomAmplitude F n ^ 2) = 1 := by
    rw [← hF]; exact sum_congr rfl fun n hn => atomAmplitude_sq (mem_Icc.mp hn).1 F
  rw [jumpEnergy_eq_poleDefect]
  exact hN _ hmass hE

/-- **Jump energy of nonpositive directions at growing overlap.** Uniformly for `c ≥ 1` and
`N ≥ H c⁸`, a nonpositive unit vector has pole defect at most `(C/a) c¹⁶`. -/
theorem poleDefect_le_of_nonpos_at_growing_overlap :
    ∃ a C H : ℝ, 0 < a ∧ 0 < C ∧ 0 < H ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
      ∀ x : ℕ → ℝ, (∑ n ∈ Icc 1 N, x n ^ 2) = 1 →
        weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) ≤ 0 →
          poleDefect N x ≤ C / a * c ^ 16 := by
  obtain ⟨a, C, H, ha, hC, hH, hres⟩ := exists_tiltedUnitSpline_complete_defect_reserve_polynomial
  refine ⟨a, C, H, ha, hC, hH, fun c hc N hN x hx hE => ?_⟩
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hden : 0 < (c / N) * ∫ u, tiltedUnitSpline u ^ 2 :=
    mul_pos (div_pos hc0 hN0) integral_tiltedUnitSpline_sq_pos
  have hq : weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hE hden.le
  have h := (hres c hc N hN x).trans hq
  rw [hx, mul_one] at h
  have hc7 : 0 < c ^ 7 := pow_pos hc0 7
  have hD : poleDefect N x ≤ C * c ^ 9 / (a / c ^ 7) := by
    rw [le_div_iff₀ (div_pos ha hc7)]; linarith
  calc poleDefect N x ≤ C * c ^ 9 / (a / c ^ 7) := hD
    _ = C / a * c ^ 16 := by field_simp

/-- **Localization at growing overlap.** For every `c ≥ 1` and `η > 0` one finite conductor sector
captures every nonpositive unit vector at every horizon `N ≥ H c⁸`. -/
theorem nonpos_localizes_uniformly_at_growing_overlap :
    ∃ H : ℝ, 0 < H ∧ ∀ c : ℝ, 1 ≤ c → ∀ η : ℝ, 0 < η →
      ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧ ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) → ∀ x : ℕ → ℝ,
        (∑ n ∈ Icc 1 N, x n ^ 2) = 1 →
        weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) ≤ 0 →
          ∃ b : ℕ → ℝ,
            (∑ n ∈ Icc 1 N, (x n - ∑ m ∈ S, b m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  obtain ⟨a, C, H, -, -, hH, hD⟩ := poleDefect_le_of_nonpos_at_growing_overlap
  refine ⟨H, hH, fun c hc η hη => ?_⟩
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le (C / a * c ^ 16) hη
  exact ⟨S, hS, fun N hN x hx hE => happ N x hx.le (hD c hc N hN x hx hE)⟩

end GaloisForLFunctions.ArithmeticCouplingTheory
