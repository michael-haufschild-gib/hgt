import GaloisForLFunctions.BiScaleUncertainty.PrimeAnchorMixedRecovery
import GaloisForLFunctions.BiScaleUncertainty.PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer

/-!
# Mixed-observation error in the complete arithmetic graph

Finite Möbius inversion transfers a terminal-prime mixed row to the literal
divisor-clock synthesis. Every inverse weight, product cutoff, clock amplitude,
mass contribution, and prime edge remains in the displayed error budget.
-/

open Finset RHTower RHTower.Sieve RHTower.CHMDDoobGraph
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
noncomputable section
set_option autoImplicit false

def denominator (N p : ℕ) (c b : ℕ → ℝ) : ℝ :=
  |selbergMultiplesCoord N c p| *
    |selbergMultiplesCoord N c p + selbergMultiplesCoord N b p|

def numerator (N p : ℕ) (c b : ℕ → ℝ) (q : ℕ) : ℝ :=
  |selbergMultiplesCoord N c p + selbergMultiplesCoord N b p| * error N p c b q +
    |selbergMultiplesCoord N b q| * error N p c b p

def radius (N p : ℕ) (c b : ℕ → ℝ) (q : ℕ) : ℝ :=
  numerator N p c b q / denominator N p c b

theorem coordinate_le_radius (N p q : ℕ) (c b : ℕ → ℝ)
    (hD : 0 < denominator N p c b) :
    |selbergMultiplesCoord N c q - selbergMultiplesCoord N b q| ≤ radius N p c b q := by
  apply (le_div_iff₀ hD).mpr
  simpa only [denominator, numerator, mul_comm] using coordinate_inverse N p q c b

/-- Finite arithmetic divisor clocks, using the canonical full graph lift. -/
def synthesis (N k : ℕ) (c : ℕ → ℝ) : SourceGraph :=
  ∑ d ∈ Icc 1 N, c d • canonicalPrimeGraphClockAtom k N d

/-- Explicit cost of finite multiples inversion followed by graph synthesis. -/
def inversionCost (N k : ℕ) (r : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 N, (d : ℝ) * ‖canonicalPrimeGraphClockAtom k N d‖ *
    ∑ m ∈ Icc 1 (N / d), |(μ m : ℝ)| * r (d * m)

theorem coefficients_inverse (N : ℕ) (c : ℕ → ℝ) :
    ∀ d ∈ Icc 1 N, c d = pmRamanujanResidueCoeff (selbergMultiplesCoord N c) N d := by
  apply (sieve_active_coefficients_eq_iff N _ _).mpr
  intro q hq
  rw [selbergMultiplesCoord_ramanujan_inverse, if_pos hq]

theorem coefficient_error_le (N : ℕ) (c b r : ℕ → ℝ)
    (hr : ∀ q, |selbergMultiplesCoord N c q - selbergMultiplesCoord N b q| ≤ r q)
    {d : ℕ} (hd : d ∈ Icc 1 N) :
    |c d - b d| ≤ (d : ℝ) * ∑ m ∈ Icc 1 (N / d), |(μ m : ℝ)| * r (d * m) := by
  have he : c d - b d = (d : ℝ) * ∑ m ∈ Icc 1 (N / d),
      (μ m : ℝ) * (selbergMultiplesCoord N c (d*m) - selbergMultiplesCoord N b (d*m)) := by
    rw [coefficients_inverse N c d hd, coefficients_inverse N b d hd]
    simp only [pmRamanujanResidueCoeff, mul_sub, sum_sub_distrib]
  rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hr (d*m)) (abs_nonneg _))

theorem synthesis_error_le (N k : ℕ) (c b r : ℕ → ℝ)
    (hr : ∀ q, |selbergMultiplesCoord N c q - selbergMultiplesCoord N b q| ≤ r q) :
    ‖synthesis N k c - synthesis N k b‖ ≤ inversionCost N k r := by
  unfold synthesis inversionCost
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun d hd => ?_)
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (coefficient_error_le N c b r hr hd)
    (norm_nonneg (canonicalPrimeGraphClockAtom k N d))
  convert h using 1
  ring

/-- The full graph error is controlled by the measured mixed row. -/
theorem mixed_graph_error (N k p : ℕ) (c b : ℕ → ℝ)
    (hD : 0 < denominator N p c b) :
    ‖synthesis N k c - synthesis N k b‖ ≤ inversionCost N k (radius N p c b) :=
  synthesis_error_le N k c b _ (fun q => coordinate_le_radius N p q c b hD)

/-- Complete signed energy, including the subtracted mass and every arithmetic edge. -/
theorem mixed_energy_error (N k p : ℕ) (c b : ℕ → ℝ)
    (hD : 0 < denominator N p c b) :
    |sourceEnergy (synthesis N k c) - sourceEnergy (synthesis N k b)| ≤
      inversionCost N k (radius N p c b) ^ 2 +
        2 * inversionCost N k (radius N p c b) * ‖synthesis N k b‖ := by
  have h := mixed_graph_error N k p c b hD
  have hK := (norm_nonneg (synthesis N k c - synthesis N k b)).trans h
  refine (abs_sourceEnergy_sub_le (synthesis N k c) (synthesis N k b)).trans ?_
  gcongr

/-- Small measured error gives a linear energy modulus with an explicit reference cost. -/
theorem mixed_energy_error_linear (N k p : ℕ) (c b : ℕ → ℝ)
    (hD : 0 < denominator N p c b)
    (hsmall : inversionCost N k (radius N p c b) ≤ 1) :
    |sourceEnergy (synthesis N k c) - sourceEnergy (synthesis N k b)| ≤
      (1 + 2 * ‖synthesis N k b‖) * inversionCost N k (radius N p c b) := by
  have hK := (norm_nonneg (synthesis N k c - synthesis N k b)).trans
    (mixed_graph_error N k p c b hD)
  have he := mixed_energy_error N k p c b hD
  nlinarith

/-- The denominator is computed from the actual terminal-prime tapers. -/
theorem moebius_denominator {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (w v : ℕ → ℝ) :
    denominator N p (fun d => (μ d : ℝ) * w d) (fun d => (μ d : ℝ) * v d) =
      |w p / (p : ℝ)| * |(w p + v p) / (p : ℝ)| := by
  unfold denominator
  rw [selbergMultiplesCoord_moebius_mul_primeTail hp w,
    selbergMultiplesCoord_moebius_mul_primeTail hp v]
  simp only [neg_div, abs_neg]
  congr 1
  rw [← neg_add, abs_neg, add_div]

theorem moebius_denominator_pos {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (w v : ℕ → ℝ) (hw : 0 < w p) (hv : 0 ≤ v p) :
    0 < denominator N p (fun d => (μ d : ℝ) * w d) (fun d => (μ d : ℝ) * v d) := by
  rw [moebius_denominator hp w v]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hs : 0 < w p + v p := by linarith
  rw [abs_of_pos (div_pos hw hp0), abs_of_pos (div_pos hs hp0)]
  exact mul_pos (div_pos hw hp0) (div_pos hs hp0)

/-- Positive arithmetic tapers supply the denominator; it is not an analytic premise. -/
theorem moebius_mixed_energy_error {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (k : ℕ) (w v : ℕ → ℝ) (hw : 0 < w p) (hv : 0 ≤ v p) :
    let c := fun d => (μ d : ℝ) * w d
    let b := fun d => (μ d : ℝ) * v d
    |sourceEnergy (synthesis N k c) - sourceEnergy (synthesis N k b)| ≤
      inversionCost N k (radius N p c b) ^ 2 +
        2 * inversionCost N k (radius N p c b) * ‖synthesis N k b‖ :=
  mixed_energy_error N k p _ _ (moebius_denominator_pos hp w v hw hv)

/-- Every finite power-damped Möbius row has a live terminal-prime anchor. -/
theorem powerDamped_mixed_energy_error {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (k : ℕ) (ε η : ℝ) :
    let c := fun d => (μ d : ℝ) * Real.exp (-ε * Real.log d)
    let b := fun d => (μ d : ℝ) * Real.exp (-η * Real.log d)
    |sourceEnergy (synthesis N k c) - sourceEnergy (synthesis N k b)| ≤
      inversionCost N k (radius N p c b) ^ 2 +
        2 * inversionCost N k (radius N p c b) * ‖synthesis N k b‖ :=
  moebius_mixed_energy_error hp k _ _ (Real.exp_pos _) (Real.exp_pos _).le

theorem barbanVehov_anchor {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (X : ℕ) (hX : p < X) :
    selbergMultiplesCoord N (barbanVehovWeight X) p = -Real.log ((X : ℝ) / p) / p := by
  rw [selbergMultiplesCoord_primeTail hp]
  simp only [barbanVehovWeight, if_pos hX.le,
    ArithmeticFunction.moebius_apply_prime (mem_filter.mp hp).2.1,
    Int.cast_neg, Int.cast_one, neg_one_mul]

theorem barbanVehov_anchor_neg {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (X : ℕ) (hX : p < X) :
    selbergMultiplesCoord N (barbanVehovWeight X) p < 0 := by
  rw [barbanVehov_anchor hp X hX]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hl : 0 < Real.log ((X : ℝ) / p) :=
    Real.log_pos ((lt_div_iff₀ hp0).mpr (by exact_mod_cast hX))
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hl) hp0

/-- BV cutoffs below the terminal prime are excluded by the proved taper-zero boundary. -/
theorem barbanVehov_mixed_energy_error {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (k X Y : ℕ) (hX : p < X) (hY : p < Y) :
    |sourceEnergy (synthesis N k (barbanVehovWeight X)) -
      sourceEnergy (synthesis N k (barbanVehovWeight Y))| ≤
      inversionCost N k (radius N p (barbanVehovWeight X) (barbanVehovWeight Y)) ^ 2 +
        2 * inversionCost N k (radius N p (barbanVehovWeight X) (barbanVehovWeight Y)) *
          ‖synthesis N k (barbanVehovWeight Y)‖ := by
  apply mixed_energy_error
  have hx := barbanVehov_anchor_neg hp X hX
  have hy := barbanVehov_anchor_neg hp Y hY
  exact mul_pos (abs_pos.mpr hx.ne) (abs_pos.mpr (add_neg hx hy).ne)

theorem inversionCost_const (N k : ℕ) (t : ℝ) :
    inversionCost N k (fun _ => t) = t * inversionCost N k (fun _ => 1) := by
  unfold inversionCost
  simp only [mul_one]
  conv_rhs => rw [mul_sum]
  apply sum_congr rfl
  intro d _
  rw [← sum_mul]
  ring

/-- A finite observation horizon suffices for a uniform linear energy modulus
on each fixed nonzero anchor slice. -/
theorem fixed_anchor_uniform_energy_error (N k p : ℕ) (c b : ℕ → ℝ)
    (hb : selbergMultiplesCoord N b p ≠ 0)
    (hfix : selbergMultiplesCoord N c p = selbergMultiplesCoord N b p)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hobs : ∀ q ∈ Icc 1 N, error N p c b q ≤ η) :
    let L := inversionCost N k (fun _ => 1) / |selbergMultiplesCoord N b p|
    |sourceEnergy (synthesis N k c) - sourceEnergy (synthesis N k b)| ≤
      (L ^ 2 + 2 * L * ‖synthesis N k b‖) * η := by
  let a := |selbergMultiplesCoord N b p|
  have ha : 0 < a := abs_pos.mpr hb
  have hcoord (q : ℕ) :
      |selbergMultiplesCoord N c q - selbergMultiplesCoord N b q| ≤ η / a := by
    apply (le_div_iff₀ ha).mpr
    by_cases hq : q ∈ Icc 1 N
    · have he : error N p c b q =
          a * |selbergMultiplesCoord N c q - selbergMultiplesCoord N b q| := by
        simp only [error, mixed, hfix, ← mul_sub, abs_mul, a]
      have hh := hobs q hq
      rw [he] at hh
      nlinarith only [hh]
    · rw [selbergMultiplesCoord_eq_zero_of_notMem c hq,
        selbergMultiplesCoord_eq_zero_of_notMem b hq, sub_self, abs_zero, zero_mul]
      exact hη
  let L := inversionCost N k (fun _ => 1) / a
  have hL : 0 ≤ L := by
    dsimp [L, inversionCost]
    positivity
  have hgraph : ‖synthesis N k c - synthesis N k b‖ ≤ L * η := by
    have hg := synthesis_error_le N k c b _ hcoord
    rw [inversionCost_const] at hg
    convert hg using 1
    dsimp [L]
    ring
  have he : |sourceEnergy (synthesis N k c) - sourceEnergy (synthesis N k b)| ≤
      (L*η)^2 + 2*(L*η)*‖synthesis N k b‖ := by
    refine (abs_sourceEnergy_sub_le _ _).trans ?_
    gcongr
  have hηsq : η^2 ≤ η := by nlinarith
  have hLs := mul_le_mul_of_nonneg_left hηsq (sq_nonneg L)
  change _ ≤ (L^2 + 2*L*‖synthesis N k b‖)*η
  nlinarith only [he, hLs]

end
end GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
