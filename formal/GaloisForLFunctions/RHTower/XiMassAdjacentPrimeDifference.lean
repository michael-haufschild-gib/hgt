import GaloisForLFunctions.RHTower.XiMassStripFourierLipschitz
import GaloisForLFunctions.RHTower.XiMassPrimeSqrtDilation
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Balanced adjacent-prime differences in the Xi mass trace

Exact critical-coefficient balancing converts each adjacent prime pair into a frequency
difference of the actual mass-test Fourier transform. Its uniform frequency Lipschitz law and a
quarter-exponential potential telescope give absolute summability and one vertical-height-independent
bound, without a prime-gap estimate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Critical von-Mangoldt coefficient at the `n`th prime. -/
def xiMassNthPrimeCriticalCoefficient (n : ℕ) : ℂ :=
  LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
    (1 / 2 : ℂ) (nthPrimeSubtype n : ℕ)

/-- Balanced difference of two adjacent prime atoms. -/
def xiMassBalancedAdjacentPrimeAtom (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  (xiMassNthPrimeCriticalCoefficient (2 * n + 1) /
      xiMassNthPrimeCriticalCoefficient (2 * n)) *
      xiMassCenteredPrimeAtom a τ (nthPrimeSubtype (2 * n) : ℕ) -
    xiMassCenteredPrimeAtom a τ (nthPrimeSubtype (2 * n + 1) : ℕ)

/-- Quarter-exponential potential on the ordered prime-log ray. -/
def xiMassAdjacentPrimePotential (n : ℕ) : ℝ :=
  Real.exp (-(Real.log (nthPrimeSubtype n : ℝ) / 4))

/-- Even-block drop of the quarter-exponential potential. -/
def xiMassAdjacentPrimePotentialGap (n : ℕ) : ℝ :=
  xiMassAdjacentPrimePotential (2 * n) -
    xiMassAdjacentPrimePotential (2 * n + 2)

/-- The coefficient balance converts the masked pair into a Fourier-frequency difference. -/
theorem xiMassBalancedAdjacentPrimeAtom_eq (a : ℝ) (τ : ℂ) (n : ℕ) :
    xiMassBalancedAdjacentPrimeAtom a τ n =
      xiMassNthPrimeCriticalCoefficient (2 * n + 1) *
        (stripFourier (xiMassAnalyticTest a τ)
            (Real.log (nthPrimeSubtype (2 * n) : ℕ) : ℂ) -
          stripFourier (xiMassAnalyticTest a τ)
            (Real.log (nthPrimeSubtype (2 * n + 1) : ℕ) : ℂ)) := by
  unfold xiMassBalancedAdjacentPrimeAtom xiMassNthPrimeCriticalCoefficient
    xiMassCenteredPrimeAtom
  rw [div_mul_mul_eq_mul
    (xiMassPrimeCriticalTerm_ne_zero (nthPrimeSubtype (2 * n)))]
  ring

/-- The quarter-exponential potential decreases along the ordered primes. -/
theorem antitone_xiMassAdjacentPrimePotential :
    Antitone xiMassAdjacentPrimePotential := by
  intro m n hmn
  unfold xiMassAdjacentPrimePotential
  apply Real.exp_le_exp.mpr
  have hlog := nthPrimeSubtype_log_strictMono.monotone hmn
  linarith

/-- Elementary exponential-potential inequality behind the adjacent-pair telescope. -/
theorem log_weight_gap_le_quarterPotential
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y * Real.exp (-y / 2) * (y - x) ≤
      16 * (Real.exp (-x / 4) - Real.exp (-y / 4)) := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hy4 : y / 4 ≤ Real.exp (y / 4) := by
    have h := Real.add_one_le_exp (y / 4)
    linarith
  have hy : y ≤ 4 * Real.exp (y / 4) := by linarith
  have hdecay : y * Real.exp (-y / 2) ≤ 4 * Real.exp (-y / 4) := by
    calc
      y * Real.exp (-y / 2) ≤
          (4 * Real.exp (y / 4)) * Real.exp (-y / 2) :=
        mul_le_mul_of_nonneg_right hy (Real.exp_nonneg _)
      _ = 4 * Real.exp (-y / 4) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hd0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hd : y - x ≤ 4 * (Real.exp ((y - x) / 4) - 1) := by
    have h := Real.add_one_le_exp ((y - x) / 4)
    linarith
  calc
    y * Real.exp (-y / 2) * (y - x) ≤
        (4 * Real.exp (-y / 4)) * (y - x) :=
      mul_le_mul_of_nonneg_right hdecay hd0
    _ ≤ (4 * Real.exp (-y / 4)) *
        (4 * (Real.exp ((y - x) / 4) - 1)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = 16 * (Real.exp (-x / 4) - Real.exp (-y / 4)) := by
      rw [show -x / 4 = -y / 4 + (y - x) / 4 by ring, Real.exp_add]
      ring

/-- Critical mass times one adjacent logarithmic gap is controlled by the potential drop. -/
theorem xiMassAdjacentPrimeCriticalGap_le_potential (n : ℕ) :
    xiMassPrimePowerCriticalWeight (nthPrimeSubtype (2 * n + 1)) 0 *
        (Real.log (nthPrimeSubtype (2 * n + 1) : ℝ) -
          Real.log (nthPrimeSubtype (2 * n) : ℝ)) ≤
      16 * (xiMassAdjacentPrimePotential (2 * n) -
        xiMassAdjacentPrimePotential (2 * n + 1)) := by
  let x : ℝ := Real.log (nthPrimeSubtype (2 * n) : ℝ)
  let y : ℝ := Real.log (nthPrimeSubtype (2 * n + 1) : ℝ)
  have hp0 : 0 < (nthPrimeSubtype (2 * n + 1) : ℝ) :=
    nthPrimeSubtype_pos _
  have hx : 0 ≤ x := Real.log_nonneg (by
    exact_mod_cast (nthPrimeSubtype (2 * n)).prop.one_le)
  have hxy : x ≤ y :=
    nthPrimeSubtype_log_strictMono.monotone (by omega)
  have h := log_weight_gap_le_quarterPotential hx hxy
  rw [xiMassPrimePowerCriticalWeight_eq]
  norm_num
  rw [Real.rpow_def_of_pos hp0]
  unfold xiMassAdjacentPrimePotential
  convert h using 1 <;> simp only [x, y] <;> ring_nf

/-- The even-block potential drops are nonnegative. -/
theorem xiMassAdjacentPrimePotentialGap_nonneg (n : ℕ) :
    0 ≤ xiMassAdjacentPrimePotentialGap n := by
  exact sub_nonneg.mpr (antitone_xiMassAdjacentPrimePotential (by omega))

/-- Exact finite telescope of the even-block potential drops. -/
theorem sum_xiMassAdjacentPrimePotentialGap (N : ℕ) :
    ∑ n ∈ Finset.range N, xiMassAdjacentPrimePotentialGap n =
      xiMassAdjacentPrimePotential 0 - xiMassAdjacentPrimePotential (2 * N) := by
  simpa [xiMassAdjacentPrimePotentialGap, Nat.mul_add] using
    (Finset.sum_range_sub' (fun n : ℕ => xiMassAdjacentPrimePotential (2 * n)) N)

/-- The even-block potential telescope is summable without any prime-gap estimate. -/
theorem summable_xiMassAdjacentPrimePotentialGap :
    Summable xiMassAdjacentPrimePotentialGap := by
  apply summable_of_sum_range_le xiMassAdjacentPrimePotentialGap_nonneg
  intro N
  rw [sum_xiMassAdjacentPrimePotentialGap]
  have hpos : 0 < xiMassAdjacentPrimePotential (2 * N) := Real.exp_pos _
  linarith

theorem tsum_xiMassAdjacentPrimePotentialGap_le :
    (∑' n : ℕ, xiMassAdjacentPrimePotentialGap n) ≤
      xiMassAdjacentPrimePotential 0 := by
  have hs := summable_xiMassAdjacentPrimePotentialGap
  apply le_of_tendsto ((hs.hasSum_iff_tendsto_nat).mp hs.hasSum)
  exact Filter.Eventually.of_forall fun N => by
    rw [sum_xiMassAdjacentPrimePotentialGap]
    have hpos : 0 < xiMassAdjacentPrimePotential (2 * N) := Real.exp_pos _
    linarith

/-- Uniform pointwise majorant for each balanced adjacent-prime atom. -/
theorem norm_xiMassBalancedAdjacentPrimeAtom_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) (n : ℕ) :
    ‖xiMassBalancedAdjacentPrimeAtom a ((σ : ℂ) + u * I) n‖ ≤
      16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotentialGap n := by
  rw [xiMassBalancedAdjacentPrimeAtom_eq, norm_mul]
  have hlog := nthPrimeSubtype_log_strictMono (by omega : 2 * n < 2 * n + 1)
  have hLip := norm_stripFourier_xiMassAnalyticTest_sub_le ha hσ u
    (Real.log (nthPrimeSubtype (2 * n) : ℝ))
    (Real.log (nthPrimeSubtype (2 * n + 1) : ℝ))
  rw [abs_of_nonpos (by linarith)] at hLip
  rw [show -(Real.log (nthPrimeSubtype (2 * n) : ℝ) -
      Real.log (nthPrimeSubtype (2 * n + 1) : ℝ)) =
      Real.log (nthPrimeSubtype (2 * n + 1) : ℝ) -
        Real.log (nthPrimeSubtype (2 * n) : ℝ) by ring] at hLip
  have hcoeff :
      ‖xiMassNthPrimeCriticalCoefficient (2 * n + 1)‖ =
        xiMassPrimePowerCriticalWeight (nthPrimeSubtype (2 * n + 1)) 0 := by
    rw [xiMassNthPrimeCriticalCoefficient, xiMassPrimePowerCriticalWeight, pow_one]
  rw [hcoeff]
  have hJ : 0 ≤ ∫ x : ℝ, |x| * Real.exp (-(σ * |x|)) :=
    integral_nonneg fun _ => by positivity
  have hcritical := xiMassAdjacentPrimeCriticalGap_le_potential n
  have hpotential :
      xiMassAdjacentPrimePotential (2 * n) -
          xiMassAdjacentPrimePotential (2 * n + 1) ≤
        xiMassAdjacentPrimePotentialGap n := by
    unfold xiMassAdjacentPrimePotentialGap
    have hmono := antitone_xiMassAdjacentPrimePotential
      (show 2 * n + 1 ≤ 2 * n + 2 by omega)
    linarith
  calc
    xiMassPrimePowerCriticalWeight (nthPrimeSubtype (2 * n + 1)) 0 *
        ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + ↑u * I))
              ↑(Real.log ↑↑(nthPrimeSubtype (2 * n))) -
          stripFourier (xiMassAnalyticTest a ((σ : ℂ) + ↑u * I))
              ↑(Real.log ↑↑(nthPrimeSubtype (2 * n + 1)))‖ ≤
        xiMassPrimePowerCriticalWeight (nthPrimeSubtype (2 * n + 1)) 0 *
          ((Real.log (nthPrimeSubtype (2 * n + 1) : ℝ) -
              Real.log (nthPrimeSubtype (2 * n) : ℝ)) *
            (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))) :=
      mul_le_mul_of_nonneg_left hLip (norm_nonneg _)
    _ = (xiMassPrimePowerCriticalWeight (nthPrimeSubtype (2 * n + 1)) 0 *
          (Real.log (nthPrimeSubtype (2 * n + 1) : ℝ) -
            Real.log (nthPrimeSubtype (2 * n) : ℝ))) *
        (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) := by ring
    _ ≤ (16 * (xiMassAdjacentPrimePotential (2 * n) -
          xiMassAdjacentPrimePotential (2 * n + 1))) *
        (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) :=
      mul_le_mul_of_nonneg_right hcritical hJ
    _ ≤ (16 * xiMassAdjacentPrimePotentialGap n) *
        (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpotential (by norm_num)) hJ
    _ = 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotentialGap n := by ring

/-- Absolute summability of the actual balanced adjacent-prime atoms, uniformly majorized in `u`. -/
theorem summable_norm_xiMassBalancedAdjacentPrimeAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun n : ℕ =>
      ‖xiMassBalancedAdjacentPrimeAtom a ((σ : ℂ) + u * I) n‖) := by
  let C : ℝ := 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))
  have hmajor : Summable (fun n : ℕ => C * xiMassAdjacentPrimePotentialGap n) :=
    summable_xiMassAdjacentPrimePotentialGap.mul_left C
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa [C] using
      norm_xiMassBalancedAdjacentPrimeAtom_vertical_le ha hσ u n)
    hmajor

theorem summable_xiMassBalancedAdjacentPrimeAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun n : ℕ =>
      xiMassBalancedAdjacentPrimeAtom a ((σ : ℂ) + u * I) n) :=
  summable_norm_iff.mp
    (summable_norm_xiMassBalancedAdjacentPrimeAtom ha hσ u)

/-- Sum of all balanced adjacent-prime atoms. -/
def xiMassBalancedAdjacentPrimeLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' n : ℕ, xiMassBalancedAdjacentPrimeAtom a τ n

/-- **Uniform vertical bound for the balanced adjacent-prime layer.** -/
theorem norm_xiMassBalancedAdjacentPrimeLayer_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassBalancedAdjacentPrimeLayer a ((σ : ℂ) + u * I)‖ ≤
      16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotential 0 := by
  let C : ℝ := 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (integral_nonneg fun _ => by positivity)
  have hnorm := summable_norm_xiMassBalancedAdjacentPrimeAtom ha hσ u
  have hmajor : Summable (fun n : ℕ => C * xiMassAdjacentPrimePotentialGap n) :=
    summable_xiMassAdjacentPrimePotentialGap.mul_left C
  calc
    ‖xiMassBalancedAdjacentPrimeLayer a ((σ : ℂ) + u * I)‖ ≤
        ∑' n : ℕ, ‖xiMassBalancedAdjacentPrimeAtom a ((σ : ℂ) + u * I) n‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, C * xiMassAdjacentPrimePotentialGap n :=
      Summable.tsum_le_tsum
        (fun n => by simpa [C] using
          norm_xiMassBalancedAdjacentPrimeAtom_vertical_le ha hσ u n)
        hnorm hmajor
    _ = C * (∑' n : ℕ, xiMassAdjacentPrimePotentialGap n) := tsum_mul_left
    _ ≤ C * xiMassAdjacentPrimePotential 0 :=
      mul_le_mul_of_nonneg_left tsum_xiMassAdjacentPrimePotentialGap_le hC
    _ = 16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotential 0 := rfl

/-- C38-B: the balanced adjacent-prime layer is uniformly bounded on every positive vertical line. -/
theorem exists_norm_xiMassBalancedAdjacentPrimeLayer_vertical_bound
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖xiMassBalancedAdjacentPrimeLayer a ((σ : ℂ) + u * I)‖ ≤ C := by
  exact ⟨16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
      xiMassAdjacentPrimePotential 0,
    norm_xiMassBalancedAdjacentPrimeLayer_vertical_le ha hσ⟩

end

end RHTower
