import GaloisForLFunctions.HTGeometry.CoefficientUniformJetEscape
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Complete bounded-gauge space and continuity of prime-log differential jets

The bounded real gauges on the discrete prime index set form a complete uniform function space.
On this space every upper-half-plane Cauchy-jet coordinate is continuous: locally in the uniform
norm, the dyadic prime weights admit one summable geometric majorant.  The factorial identity then
transfers continuity from normalized Cauchy jets to actual iterated derivatives.  Consequently the
rank-defect locus of every fixed finite differential coefficient pattern is closed in gauge space.
-/

namespace GaloisForLFunctions.HTGeometry

open BoundedContinuousFunction
open scoped BoundedContinuousFunction

/-- The prime index set carries its intrinsic discrete topology. -/
instance primeLogPrimeTopology : TopologicalSpace Nat.Primes := ⊥

instance primeLogPrimeDiscreteTopology : DiscreteTopology Nat.Primes where
  eq_bot := rfl

/-- Bounded real prime-log gauges, equipped with the uniform norm.  This is a complete space. -/
abbrev PrimeLogBoundedGauge := Nat.Primes →ᵇ ℝ

/-- A pointwise bounded prime gauge as an element of the complete uniform gauge space. -/
noncomputable def primeLogBoundedGaugeOfBound
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C) :
    PrimeLogBoundedGauge :=
  BoundedContinuousFunction.ofNormedAddCommGroup u continuous_of_discreteTopology C fun p => by
    simpa only [Real.norm_eq_abs] using hu p

@[simp]
theorem primeLogBoundedGaugeOfBound_apply
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C) (p : Nat.Primes) :
    primeLogBoundedGaugeOfBound u C hu p = u p :=
  rfl

/-- Every normalized prime-log Cauchy-jet coordinate is continuous at every bounded gauge. -/
theorem continuousAt_primeLogCauchyJetPacket_boundedGauge_coordinate
    {ι : Type*} (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im)
    (orders : ι → ℕ) (s : Σ i, Fin (orders i))
    (u₀ : PrimeLogBoundedGauge) :
    ContinuousAt
      (fun u : PrimeLogBoundedGauge ↦
        primeLogCauchyJetPacket (fun p ↦ u p) nodes orders s) u₀ := by
  let z := nodes s.1
  let k := s.2.1 + 1
  let kernel : Nat.Primes → ℂ := fun p ↦
    cauchyJetColumn nodes orders (fun q ↦ (primeLogSupport q : ℂ)) p s
  let term : Nat.Primes → PrimeLogBoundedGauge → ℂ := fun p u ↦
    (primeDyadicWeight (fun q ↦ u q) p : ℂ) * kernel p
  let B : ℝ := ‖u₀‖ + 1
  let major : Nat.Primes → ℝ := fun p ↦
    ‖(primeDyadicWeight (fun _ ↦ B) p : ℂ)‖ * ((z.im)⁻¹ ^ k)
  have hmajor : Summable major :=
    (summable_norm_primeDyadicWeight (fun _ ↦ B) B (fun _ ↦ le_rfl)).mul_right _
  have hterm : ∀ p, Continuous (term p) := by
    intro p
    have heval : Continuous (fun u : PrimeLogBoundedGauge ↦ u p) :=
      (lipschitz_eval_const p).continuous
    have hreal : Continuous
        (fun u : PrimeLogBoundedGauge ↦ primeDyadicWeight (fun q ↦ u q) p) := by
      exact continuous_const.mul (Real.continuous_exp.comp heval)
    exact (Complex.continuous_ofReal.comp hreal).mul continuous_const
  have hbound : ∀ p u, u ∈ Metric.closedBall u₀ 1 → ‖term p u‖ ≤ major p := by
    intro p u hu
    have hdistp : dist (u p) (u₀ p) ≤ 1 :=
      (dist_coe_le_dist p).trans hu
    have hup : u p ≤ u₀ p + 1 := by
      rw [Real.dist_eq] at hdistp
      linarith [le_abs_self (u p - u₀ p)]
    have hu₀p : u₀ p ≤ ‖u₀‖ :=
      (le_abs_self (u₀ p)).trans (norm_coe_le_norm u₀ p)
    have huB : u p ≤ B := by
      simp only [B]
      linarith
    have hweight :
        ‖(primeDyadicWeight (fun q ↦ u q) p : ℂ)‖ ≤
          ‖(primeDyadicWeight (fun _ ↦ B) p : ℂ)‖ := by
      simp only [primeDyadicWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_pow, abs_inv, abs_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr huB) (by positivity)
    have hkernel : ‖kernel p‖ ≤ (z.im)⁻¹ ^ k := by
      have hden : z.im ≤ ‖(primeLogSupport p : ℂ) - z‖ := by
        have him : |((primeLogSupport p : ℂ) - z).im| ≤
            ‖(primeLogSupport p : ℂ) - z‖ := Complex.abs_im_le_norm _
        have heq : ((primeLogSupport p : ℂ) - z).im = -z.im := by
          simp [Complex.sub_im]
        rw [heq, abs_neg, abs_of_pos (hupper s.1)] at him
        exact him
      simp only [kernel, cauchyJetColumn, z, k, norm_pow, norm_inv]
      gcongr
      exact hupper s.1
    simp only [term, major, norm_mul]
    exact mul_le_mul hweight hkernel (norm_nonneg _) (norm_nonneg _)
  have hcontOn : ContinuousOn (fun u : PrimeLogBoundedGauge ↦ ∑' p, term p u)
      (Metric.closedBall u₀ 1) :=
    continuousOn_tsum (fun p ↦ (hterm p).continuousOn) hmajor hbound
  have hcontAt := hcontOn.continuousAt (Metric.closedBall_mem_nhds u₀ (by norm_num))
  simpa [primeLogCauchyJetPacket, discreteCauchyJetPacket, term, kernel] using hcontAt

theorem continuous_primeLogCauchyJetPacket_boundedGauge_coordinate
    {ι : Type*} (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im)
    (orders : ι → ℕ) (s : Σ i, Fin (orders i)) :
    Continuous
      (fun u : PrimeLogBoundedGauge ↦
        primeLogCauchyJetPacket (fun p ↦ u p) nodes orders s) := by
  rw [continuous_iff_continuousAt]
  exact fun u ↦
    continuousAt_primeLogCauchyJetPacket_boundedGauge_coordinate
      nodes hupper orders s u

/-- On bounded gauges, actual iterated derivatives are the factorial diagonal scaling of the
normalized Cauchy packet. -/
theorem primeLogDifferentialJetPacket_boundedGauge_eq
    {ι : Type*} (u : PrimeLogBoundedGauge)
    (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im)
    (orders : ι → ℕ) (s : Σ i, Fin (orders i)) :
    primeLogDifferentialJetPacket (fun p ↦ u p) nodes orders s =
      (s.2.1.factorial : ℂ) *
        primeLogCauchyJetPacket (fun p ↦ u p) nodes orders s := by
  exact iteratedDeriv_primeLogHerglotz_eq_factorial_mul_packet
    (fun p ↦ u p) ‖u‖ (fun p ↦
      (le_abs_self (u p)).trans (norm_coe_le_norm u p))
    nodes hupper orders s

/-- Every actual prime-log differential-jet coordinate is continuous in the uniform gauge norm. -/
theorem continuous_primeLogDifferentialJetPacket_boundedGauge_coordinate
    {ι : Type*} (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im)
    (orders : ι → ℕ) (s : Σ i, Fin (orders i)) :
    Continuous
      (fun u : PrimeLogBoundedGauge ↦
        primeLogDifferentialJetPacket (fun p ↦ u p) nodes orders s) := by
  have hconst : Continuous
      (fun _ : PrimeLogBoundedGauge ↦ (s.2.1.factorial : ℂ)) :=
    continuous_const
  have h := hconst.mul
    (continuous_primeLogCauchyJetPacket_boundedGauge_coordinate nodes hupper orders s)
  convert h using 1
  funext u
  exact primeLogDifferentialJetPacket_boundedGauge_eq u nodes hupper orders s

/-- Actual translated differential jets, reshaped by evaluation row. -/
noncomputable def actualRowJetPacket
    {row ι : Type*} (nodes : row × ι → ℂ) (orders : ι → ℕ)
    (u : PrimeLogBoundedGauge) :
    row × (Σ i, Fin (orders i)) → ℂ :=
  fun x ↦ primeLogDifferentialJetPacket (fun p ↦ u p) nodes
    (fun y ↦ orders y.2) (rowJetIndexEquiv row ι orders x)

theorem continuous_actualRowJetPacket_coordinate
    {row ι : Type*} (nodes : row × ι → ℂ)
    (hupper : ∀ x, 0 < (nodes x).im) (orders : ι → ℕ)
    (x : row × (Σ i, Fin (orders i))) :
    Continuous (fun u : PrimeLogBoundedGauge ↦ actualRowJetPacket nodes orders u x) := by
  exact continuous_primeLogDifferentialJetPacket_boundedGauge_coordinate
    nodes hupper (fun y ↦ orders y.2) (rowJetIndexEquiv row ι orders x)

theorem continuous_actualRowJetPacket
    {row ι : Type*} (nodes : row × ι → ℂ)
    (hupper : ∀ x, 0 < (nodes x).im) (orders : ι → ℕ) :
    Continuous (actualRowJetPacket nodes orders :
      PrimeLogBoundedGauge → (row × (Σ i, Fin (orders i)) → ℂ)) := by
  exact continuous_pi fun x ↦
    continuous_actualRowJetPacket_coordinate nodes hupper orders x

/-- Gauges at which one fixed actual differential coefficient pattern loses evaluation rank. -/
def actualCoefficientPatternRankDefect
    {row ι : Type*} [Fintype row] [DecidableEq row]
    (nodes : row × ι → ℂ) (orders : ι → ℕ)
    (base : row → ℂ) (degree : row → ℕ)
    (jetExponent : row → ((Σ i, Fin (orders i)) →₀ ℕ)) :
    Set PrimeLogBoundedGauge :=
  (actualRowJetPacket nodes orders) ⁻¹'
    coefficientPatternRankDefect base degree jetExponent

/-- Every fixed finite actual differential coefficient-pattern defect is closed in the complete
bounded-gauge space. -/
theorem actualCoefficientPatternRankDefect_isClosed
    {row ι : Type*} [Fintype row] [DecidableEq row]
    (nodes : row × ι → ℂ) (hupper : ∀ x, 0 < (nodes x).im)
    (orders : ι → ℕ) (base : row → ℂ) (degree : row → ℕ)
    (jetExponent : row → ((Σ i, Fin (orders i)) →₀ ℕ)) :
    IsClosed (actualCoefficientPatternRankDefect nodes orders base degree jetExponent) := by
  exact (coefficientPatternRankDefect_isClosed base degree jetExponent).preimage
    (continuous_actualRowJetPacket nodes hupper orders)

end GaloisForLFunctions.HTGeometry
