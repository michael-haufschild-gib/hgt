import GaloisForLFunctions.RHTower.XiMassAdjacentPrimeDifference
import Mathlib.Algebra.BigOperators.Module

/-!
# Full adjacent-prime graph and exact Xi mass boundary flux

The adjacent-prime estimate holds on every edge of the connected ordered prime-log path, not only
one disjoint matching. Its full edge layer is absolutely summable with the same telescoping bound.
Finite Abel summation then gives an exact decomposition of the scalar prime source into a terminal
boundary flux and cumulative-mass-weighted graph gradients. This identifies the surviving scalar
class as a nonlocal flux-at-infinity problem.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Balanced edge across every consecutive pair in the ordered prime-log path. -/
def xiMassBalancedSuccessorPrimeAtom (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  (xiMassNthPrimeCriticalCoefficient (n + 1) /
      xiMassNthPrimeCriticalCoefficient n) *
      xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ) -
    xiMassCenteredPrimeAtom a τ (nthPrimeSubtype (n + 1) : ℕ)

def xiMassSuccessorPrimePotentialGap (n : ℕ) : ℝ :=
  xiMassAdjacentPrimePotential n - xiMassAdjacentPrimePotential (n + 1)

theorem xiMassBalancedSuccessorPrimeAtom_eq (a : ℝ) (τ : ℂ) (n : ℕ) :
    xiMassBalancedSuccessorPrimeAtom a τ n =
      xiMassNthPrimeCriticalCoefficient (n + 1) *
        (stripFourier (xiMassAnalyticTest a τ)
            (Real.log (nthPrimeSubtype n : ℕ) : ℂ) -
          stripFourier (xiMassAnalyticTest a τ)
            (Real.log (nthPrimeSubtype (n + 1) : ℕ) : ℂ)) := by
  unfold xiMassBalancedSuccessorPrimeAtom xiMassNthPrimeCriticalCoefficient
    xiMassCenteredPrimeAtom
  rw [div_mul_mul_eq_mul
    (xiMassPrimeCriticalTerm_ne_zero (nthPrimeSubtype n))]
  ring

theorem xiMassSuccessorPrimeCriticalGap_le_potential (n : ℕ) :
    xiMassPrimePowerCriticalWeight (nthPrimeSubtype (n + 1)) 0 *
        (Real.log (nthPrimeSubtype (n + 1) : ℝ) -
          Real.log (nthPrimeSubtype n : ℝ)) ≤
      16 * xiMassSuccessorPrimePotentialGap n := by
  let x : ℝ := Real.log (nthPrimeSubtype n : ℝ)
  let y : ℝ := Real.log (nthPrimeSubtype (n + 1) : ℝ)
  have hp0 : 0 < (nthPrimeSubtype (n + 1) : ℝ) :=
    nthPrimeSubtype_pos _
  have hx : 0 ≤ x := Real.log_nonneg (by
    exact_mod_cast (nthPrimeSubtype n).prop.one_le)
  have hxy : x ≤ y :=
    nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ n)
  have h := log_weight_gap_le_quarterPotential hx hxy
  rw [xiMassPrimePowerCriticalWeight_eq]
  norm_num
  rw [Real.rpow_def_of_pos hp0]
  unfold xiMassSuccessorPrimePotentialGap xiMassAdjacentPrimePotential
  convert h using 1 <;> simp only [x, y] <;> ring_nf

theorem xiMassSuccessorPrimePotentialGap_nonneg (n : ℕ) :
    0 ≤ xiMassSuccessorPrimePotentialGap n := by
  exact sub_nonneg.mpr (antitone_xiMassAdjacentPrimePotential (Nat.le_succ n))

theorem sum_xiMassSuccessorPrimePotentialGap (N : ℕ) :
    ∑ n ∈ Finset.range N, xiMassSuccessorPrimePotentialGap n =
      xiMassAdjacentPrimePotential 0 - xiMassAdjacentPrimePotential N := by
  simpa [xiMassSuccessorPrimePotentialGap] using
    (Finset.sum_range_sub' xiMassAdjacentPrimePotential N)

theorem summable_xiMassSuccessorPrimePotentialGap :
    Summable xiMassSuccessorPrimePotentialGap := by
  apply summable_of_sum_range_le xiMassSuccessorPrimePotentialGap_nonneg
  intro N
  rw [sum_xiMassSuccessorPrimePotentialGap]
  have hpos : 0 < xiMassAdjacentPrimePotential N := Real.exp_pos _
  linarith

theorem tsum_xiMassSuccessorPrimePotentialGap_le :
    (∑' n : ℕ, xiMassSuccessorPrimePotentialGap n) ≤
      xiMassAdjacentPrimePotential 0 := by
  have hs := summable_xiMassSuccessorPrimePotentialGap
  apply le_of_tendsto ((hs.hasSum_iff_tendsto_nat).mp hs.hasSum)
  exact Filter.Eventually.of_forall fun N => by
    rw [sum_xiMassSuccessorPrimePotentialGap]
    have hpos : 0 < xiMassAdjacentPrimePotential N := Real.exp_pos _
    linarith

theorem norm_xiMassBalancedSuccessorPrimeAtom_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) (n : ℕ) :
    ‖xiMassBalancedSuccessorPrimeAtom a ((σ : ℂ) + u * I) n‖ ≤
      16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassSuccessorPrimePotentialGap n := by
  rw [xiMassBalancedSuccessorPrimeAtom_eq, norm_mul]
  have hlog := nthPrimeSubtype_log_strictMono n.lt_succ_self
  have hLip := norm_stripFourier_xiMassAnalyticTest_sub_le ha hσ u
    (Real.log (nthPrimeSubtype n : ℝ))
    (Real.log (nthPrimeSubtype (n + 1) : ℝ))
  rw [abs_of_nonpos (by linarith)] at hLip
  rw [show -(Real.log (nthPrimeSubtype n : ℝ) -
      Real.log (nthPrimeSubtype (n + 1) : ℝ)) =
      Real.log (nthPrimeSubtype (n + 1) : ℝ) -
        Real.log (nthPrimeSubtype n : ℝ) by ring] at hLip
  have hcoeff :
      ‖xiMassNthPrimeCriticalCoefficient (n + 1)‖ =
        xiMassPrimePowerCriticalWeight (nthPrimeSubtype (n + 1)) 0 := by
    rw [xiMassNthPrimeCriticalCoefficient, xiMassPrimePowerCriticalWeight, pow_one]
  rw [hcoeff]
  have hJ : 0 ≤ ∫ x : ℝ, |x| * Real.exp (-(σ * |x|)) :=
    integral_nonneg fun _ => by positivity
  have hcritical := xiMassSuccessorPrimeCriticalGap_le_potential n
  calc
    xiMassPrimePowerCriticalWeight (nthPrimeSubtype (n + 1)) 0 *
        ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + ↑u * I))
              ↑(Real.log ↑↑(nthPrimeSubtype n)) -
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + ↑u * I))
              ↑(Real.log ↑↑(nthPrimeSubtype (n + 1)))‖ ≤
        xiMassPrimePowerCriticalWeight (nthPrimeSubtype (n + 1)) 0 *
          ((Real.log (nthPrimeSubtype (n + 1) : ℝ) -
              Real.log (nthPrimeSubtype n : ℝ)) *
            (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))) :=
      mul_le_mul_of_nonneg_left hLip (norm_nonneg _)
    _ = (xiMassPrimePowerCriticalWeight (nthPrimeSubtype (n + 1)) 0 *
          (Real.log (nthPrimeSubtype (n + 1) : ℝ) -
            Real.log (nthPrimeSubtype n : ℝ))) *
        (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) := by ring
    _ ≤ (16 * xiMassSuccessorPrimePotentialGap n) *
        (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) :=
      mul_le_mul_of_nonneg_right hcritical hJ
    _ = 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassSuccessorPrimePotentialGap n := by ring

theorem summable_norm_xiMassBalancedSuccessorPrimeAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun n : ℕ =>
      ‖xiMassBalancedSuccessorPrimeAtom a ((σ : ℂ) + u * I) n‖) := by
  let C : ℝ := 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))
  have hmajor : Summable (fun n : ℕ => C * xiMassSuccessorPrimePotentialGap n) :=
    summable_xiMassSuccessorPrimePotentialGap.mul_left C
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa [C] using
      norm_xiMassBalancedSuccessorPrimeAtom_vertical_le ha hσ u n)
    hmajor

def xiMassBalancedSuccessorPrimeLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' n : ℕ, xiMassBalancedSuccessorPrimeAtom a τ n

theorem norm_xiMassBalancedSuccessorPrimeLayer_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassBalancedSuccessorPrimeLayer a ((σ : ℂ) + u * I)‖ ≤
      16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotential 0 := by
  let C : ℝ := 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (integral_nonneg fun _ => by positivity)
  have hnorm := summable_norm_xiMassBalancedSuccessorPrimeAtom ha hσ u
  have hmajor : Summable (fun n : ℕ => C * xiMassSuccessorPrimePotentialGap n) :=
    summable_xiMassSuccessorPrimePotentialGap.mul_left C
  calc
    ‖xiMassBalancedSuccessorPrimeLayer a ((σ : ℂ) + u * I)‖ ≤
        ∑' n : ℕ,
          ‖xiMassBalancedSuccessorPrimeAtom a ((σ : ℂ) + u * I) n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, C * xiMassSuccessorPrimePotentialGap n :=
      Summable.tsum_le_tsum
        (fun n => by simpa [C] using
          norm_xiMassBalancedSuccessorPrimeAtom_vertical_le ha hσ u n)
        hnorm hmajor
    _ = C * (∑' n : ℕ, xiMassSuccessorPrimePotentialGap n) := tsum_mul_left
    _ ≤ C * xiMassAdjacentPrimePotential 0 :=
      mul_le_mul_of_nonneg_left tsum_xiMassSuccessorPrimePotentialGap_le hC
    _ = 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotential 0 := rfl

def xiMassPrimeFourierProfile (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  stripFourier (xiMassAnalyticTest a τ)
    (Real.log (nthPrimeSubtype n : ℕ) : ℂ)

def xiMassPrimeCriticalPartialMass (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, xiMassNthPrimeCriticalCoefficient n

theorem complex_sum_range_by_parts_flux
    (f g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, g n * f n =
      f (N - 1) * (∑ n ∈ Finset.range N, g n) +
        ∑ n ∈ Finset.range (N - 1),
          (∑ k ∈ Finset.range (n + 1), g k) * (f n - f (n + 1)) := by
  have h := Finset.sum_range_by_parts f g N
  simp only [smul_eq_mul] at h
  calc
    (∑ n ∈ Finset.range N, g n * f n) =
        ∑ n ∈ Finset.range N, f n * g n := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = f (N - 1) * (∑ n ∈ Finset.range N, g n) -
        ∑ n ∈ Finset.range (N - 1),
          (f (n + 1) - f n) * (∑ k ∈ Finset.range (n + 1), g k) := h
    _ = f (N - 1) * (∑ n ∈ Finset.range N, g n) +
        ∑ n ∈ Finset.range (N - 1),
          (∑ k ∈ Finset.range (n + 1), g k) * (f n - f (n + 1)) := by
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      apply congrArg (fun z => f (N - 1) * (∑ n ∈ Finset.range N, g n) + z)
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem sum_range_xiMassPrimeAtom_eq_graphFlux
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ) =
      xiMassPrimeFourierProfile a τ (N - 1) *
          xiMassPrimeCriticalPartialMass N +
        ∑ n ∈ Finset.range (N - 1),
          xiMassPrimeCriticalPartialMass (n + 1) *
            (xiMassPrimeFourierProfile a τ n -
              xiMassPrimeFourierProfile a τ (n + 1)) := by
  simpa [xiMassCenteredPrimeAtom, xiMassNthPrimeCriticalCoefficient,
    xiMassPrimeFourierProfile, xiMassPrimeCriticalPartialMass] using
      complex_sum_range_by_parts_flux
        (xiMassPrimeFourierProfile a τ)
        xiMassNthPrimeCriticalCoefficient N

end

end RHTower
