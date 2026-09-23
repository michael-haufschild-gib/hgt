import GaloisForLFunctions.RHTower.AsymmetricHeatDoubleSum
import GaloisForLFunctions.RHTower.HurwitzZetaSmallShift
import GaloisForLFunctions.RHTower.MobiusFriableTaylorCoefficient
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability

/-!
# Theta residue of the reflected bi-heat pairing

The complementary Dirichlet orders in the reflected bi-heat pairing add to
`1 + epsilon`.  After reindexing the lattice by the additive difference, every
row has the same zeta pole.  This file subtracts that pole row by row and proves
that the remaining double series is normally convergent near `epsilon = 0`.
Consequently the pole-filled reflected pairing has the exact value

`sum k : ℤ, exp (-pi * x * k^(2 : ℕ))`

at the regulator origin.  No meromorphic-continuation interface is assumed.
-/

open Complex Filter Set Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Fixed geometric data for the reflected bi-heat residue problem. -/
structure ReflectedBiHeatDatum where
  z : ℂ
  x : ℝ
  z_re_pos : 0 < z.re
  z_re_lt_one : z.re < 1
  x_pos : 0 < x

/-- First complementary Dirichlet order. -/
def ReflectedBiHeatDatum.leftOrder (P : ReflectedBiHeatDatum) (epsilon : ℂ) : ℂ :=
  P.z + epsilon / 2

/-- Second complementary Dirichlet order. -/
def ReflectedBiHeatDatum.rightOrder (P : ReflectedBiHeatDatum) (epsilon : ℂ) : ℂ :=
  1 - P.z + epsilon / 2

theorem ReflectedBiHeatDatum.leftOrder_add_rightOrder
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) :
    P.leftOrder epsilon + P.rightOrder epsilon = 1 + epsilon := by
  simp [ReflectedBiHeatDatum.leftOrder, ReflectedBiHeatDatum.rightOrder]
  ring

/-- Common zeta-model term subtracted from every additive-difference row. -/
def reflectedBiHeatRowModel (epsilon : ℂ) (n : ℕ) : ℂ :=
  ((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-(1 + epsilon))

/-- Upper-triangular row, including its Gaussian difference weight. -/
def reflectedBiHeatUpperRowTerm
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) (q : ℕ × ℕ) : ℂ :=
  let k := q.1
  let n := q.2
  ((heatCoeff P.x (k : ℤ) : ℝ) : ℂ) *
    (((((n + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-P.leftOrder epsilon) *
      ((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.rightOrder epsilon) -
      reflectedBiHeatRowModel epsilon n)

/-- Strict-lower-triangular row, including its Gaussian difference weight. -/
def reflectedBiHeatLowerRowTerm
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) (q : ℕ × ℕ) : ℂ :=
  let k := q.1
  let n := q.2
  ((heatCoeff P.x (-((k : ℤ) + 1)) : ℝ) : ℂ) *
    (((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.leftOrder epsilon) *
      (((((n + k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.rightOrder epsilon) -
      reflectedBiHeatRowModel epsilon n)

/-- The row-renormalized reflected double-series term. -/
def reflectedBiHeatRegularTerm
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) :
    (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℂ
  | Sum.inl q => reflectedBiHeatUpperRowTerm P epsilon q
  | Sum.inr q => reflectedBiHeatLowerRowTerm P epsilon q

/-- Exact factorization of the upper row after subtracting its common zeta model. -/
theorem reflectedBiHeatUpperRow_sub_model_eq
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) (k n : ℕ) :
    (((((n + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-P.leftOrder epsilon) *
        ((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.rightOrder epsilon) -
      reflectedBiHeatRowModel epsilon n) =
      ((((((n : ℝ) + 1) + k : ℝ) : ℂ) ^ (-P.leftOrder epsilon) -
          ((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.leftOrder epsilon)) *
        ((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.rightOrder epsilon)) := by
  have hbase : ((((n : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hcast : ((((n + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) =
      ((((n : ℝ) + 1 + k : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hcast, reflectedBiHeatRowModel]
  have hadd := Complex.cpow_add (-P.leftOrder epsilon) (-P.rightOrder epsilon) hbase
  rw [show -(1 + epsilon) = -P.leftOrder epsilon + -P.rightOrder epsilon by
    calc
      -(1 + epsilon) = -(P.leftOrder epsilon + P.rightOrder epsilon) := by
        rw [P.leftOrder_add_rightOrder epsilon]
      _ = -P.leftOrder epsilon + -P.rightOrder epsilon := by ring, hadd]
  ring

/-- Exact factorization of the lower row after subtracting its common zeta model. -/
theorem reflectedBiHeatLowerRow_sub_model_eq
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) (k n : ℕ) :
    (((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.leftOrder epsilon) *
        (((((n + k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.rightOrder epsilon) -
      reflectedBiHeatRowModel epsilon n) =
      (((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.leftOrder epsilon) *
        ((((((n : ℝ) + 1) + (k + 1) : ℝ) : ℂ) ^ (-P.rightOrder epsilon) -
          ((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (-P.rightOrder epsilon)))) := by
  have hbase : ((((n : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hcast : (((((n + k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ)) =
      ((((n : ℝ) + 1 + (k + 1) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hcast, reflectedBiHeatRowModel]
  have hadd := Complex.cpow_add (-P.leftOrder epsilon) (-P.rightOrder epsilon) hbase
  rw [show -(1 + epsilon) = -P.leftOrder epsilon + -P.rightOrder epsilon by
    calc
      -(1 + epsilon) = -(P.leftOrder epsilon + P.rightOrder epsilon) := by
        rw [P.leftOrder_add_rightOrder epsilon]
      _ = -P.leftOrder epsilon + -P.rightOrder epsilon := by ring, hadd]
  ring

/-- Mean-value bound for an upper row remainder. -/
theorem norm_reflectedBiHeatUpperRowTerm_le
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hleft : 0 < (P.leftOrder epsilon).re) (k n : ℕ) :
    ‖reflectedBiHeatUpperRowTerm P epsilon (k, n)‖ ≤
      ‖P.leftOrder epsilon‖ * (k : ℝ) *
        ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
          (P.rightOrder epsilon).re - 1) * heatCoeff P.x (k : ℤ) := by
  rw [reflectedBiHeatUpperRowTerm, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (heatCoeff_pos P.x (k : ℤ)),
    reflectedBiHeatUpperRow_sub_model_eq, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have hmv := norm_cpow_shift_sub_le_of_nonneg
    (x := (n : ℝ) + 1) (b := (k : ℝ)) (by positivity) (Nat.cast_nonneg k) hleft
  have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpow : ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re - 1) *
      ((n : ℝ) + 1) ^ (-(P.rightOrder epsilon).re) =
      ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
        (P.rightOrder epsilon).re - 1) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  calc
    _ ≤ heatCoeff P.x (k : ℤ) *
          ((‖P.leftOrder epsilon‖ *
              ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re - 1) * (k : ℝ)) *
            ((n : ℝ) + 1) ^ (-(P.rightOrder epsilon).re)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hmv
                  (Real.rpow_nonneg hbase.le (-(P.rightOrder epsilon).re)))
                (heatCoeff_pos P.x (k : ℤ)).le
    _ = ‖P.leftOrder epsilon‖ * (k : ℝ) *
          (((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re - 1) *
            ((n : ℝ) + 1) ^ (-(P.rightOrder epsilon).re)) *
          heatCoeff P.x (k : ℤ) := by ring
    _ = ‖P.leftOrder epsilon‖ * (k : ℝ) *
          ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
            (P.rightOrder epsilon).re - 1) * heatCoeff P.x (k : ℤ) := by rw [hpow]

/-- Mean-value bound for a strict-lower row remainder. -/
theorem norm_reflectedBiHeatLowerRowTerm_le
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hright : 0 < (P.rightOrder epsilon).re) (k n : ℕ) :
    ‖reflectedBiHeatLowerRowTerm P epsilon (k, n)‖ ≤
      ‖P.rightOrder epsilon‖ * ((k : ℝ) + 1) *
        ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
          (P.rightOrder epsilon).re - 1) * heatCoeff P.x (-((k : ℤ) + 1)) := by
  rw [reflectedBiHeatLowerRowTerm, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (heatCoeff_pos P.x (-((k : ℤ) + 1))),
    reflectedBiHeatLowerRow_sub_model_eq, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have hmv := norm_cpow_shift_sub_le_of_nonneg
    (x := (n : ℝ) + 1) (b := ((k : ℝ) + 1)) (by positivity) (by positivity) hright
  have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpow : ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re) *
      ((n : ℝ) + 1) ^ (-(P.rightOrder epsilon).re - 1) =
      ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
        (P.rightOrder epsilon).re - 1) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  calc
    _ ≤ heatCoeff P.x (-((k : ℤ) + 1)) *
          (((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re) *
            (‖P.rightOrder epsilon‖ *
              ((n : ℝ) + 1) ^ (-(P.rightOrder epsilon).re - 1) *
              ((k : ℝ) + 1))) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hmv
                    (Real.rpow_nonneg hbase.le (-(P.leftOrder epsilon).re)))
                  (heatCoeff_pos P.x (-((k : ℤ) + 1))).le
    _ = ‖P.rightOrder epsilon‖ * ((k : ℝ) + 1) *
          (((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re) *
            ((n : ℝ) + 1) ^ (-(P.rightOrder epsilon).re - 1)) *
          heatCoeff P.x (-((k : ℤ) + 1)) := by ring
    _ = ‖P.rightOrder epsilon‖ * ((k : ℝ) + 1) *
          ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
            (P.rightOrder epsilon).re - 1) * heatCoeff P.x (-((k : ℤ) + 1)) := by rw [hpow]

/-- Natural Gaussian first moments are summable. -/
theorem summable_nat_mul_heatCoeff (P : ReflectedBiHeatDatum) :
    Summable (fun k : ℕ => (k : ℝ) * heatCoeff P.x (k : ℤ)) := by
  have h := GaloisForLFunctions.summable_pow_mul_exp_neg_nat_sq 1
    (mul_pos Real.pi_pos P.x_pos)
  refine h.congr fun k => ?_
  simp only [pow_one, heatCoeff]
  have hk : (((k : ℤ) : ℝ)) = (k : ℝ) := by norm_num
  rw [hk]
  ring

/-- Shifted natural Gaussian first moments are summable. -/
theorem summable_nat_add_one_mul_heatCoeff (P : ReflectedBiHeatDatum) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * heatCoeff P.x (-((k : ℤ) + 1))) := by
  have h := (summable_nat_add_iff
    (f := fun k : ℕ => (k : ℝ) * heatCoeff P.x (k : ℤ)) 1).mpr
      (summable_nat_mul_heatCoeff P)
  refine h.congr fun k => ?_
  rw [heatCoeff, heatCoeff]
  push_cast
  congr 2
  ring

/-! ## A normally convergent pole-free remainder near the regulator origin -/

/-- Radius of a closed regulator disc that keeps both complementary orders positive. -/
def ReflectedBiHeatDatum.residueRadius (P : ReflectedBiHeatDatum) : ℝ :=
  min P.z.re (1 - P.z.re)

theorem ReflectedBiHeatDatum.residueRadius_pos (P : ReflectedBiHeatDatum) :
    0 < P.residueRadius := by
  rw [ReflectedBiHeatDatum.residueRadius]
  exact lt_min P.z_re_pos (sub_pos.mpr P.z_re_lt_one)

theorem ReflectedBiHeatDatum.residueRadius_le_left (P : ReflectedBiHeatDatum) :
    P.residueRadius ≤ P.z.re := min_le_left _ _

theorem ReflectedBiHeatDatum.residueRadius_le_right (P : ReflectedBiHeatDatum) :
    P.residueRadius ≤ 1 - P.z.re := min_le_right _ _

theorem ReflectedBiHeatDatum.residueRadius_lt_one (P : ReflectedBiHeatDatum) :
    P.residueRadius < 1 :=
  lt_of_le_of_lt P.residueRadius_le_left P.z_re_lt_one

/-- One uniform coefficient bound for both shifted-power derivatives. -/
def ReflectedBiHeatDatum.residueCoeffBound (P : ReflectedBiHeatDatum) : ℝ :=
  ‖P.z‖ + ‖1 - P.z‖ + P.residueRadius

theorem ReflectedBiHeatDatum.residueCoeffBound_nonneg (P : ReflectedBiHeatDatum) :
    0 ≤ P.residueCoeffBound := by
  rw [ReflectedBiHeatDatum.residueCoeffBound]
  nlinarith [norm_nonneg P.z, norm_nonneg (1 - P.z), P.residueRadius_pos]

theorem ReflectedBiHeatDatum.neg_radius_le_re_of_mem_closedBall
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hepsilon : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    -P.residueRadius ≤ epsilon.re := by
  have hnorm : ‖epsilon‖ ≤ P.residueRadius := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hepsilon
  have habs : |epsilon.re| ≤ P.residueRadius :=
    (Complex.abs_re_le_norm epsilon).trans hnorm
  exact (abs_le.mp habs).1

theorem ReflectedBiHeatDatum.leftOrder_re_pos_of_mem_closedBall
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hepsilon : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    0 < (P.leftOrder epsilon).re := by
  have hre := P.neg_radius_le_re_of_mem_closedBall hepsilon
  have hr := P.residueRadius_le_left
  rw [ReflectedBiHeatDatum.leftOrder]
  norm_num [Complex.div_re]
  linarith [P.residueRadius_pos]

theorem ReflectedBiHeatDatum.rightOrder_re_pos_of_mem_closedBall
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hepsilon : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    0 < (P.rightOrder epsilon).re := by
  have hre := P.neg_radius_le_re_of_mem_closedBall hepsilon
  have hr := P.residueRadius_le_right
  rw [ReflectedBiHeatDatum.rightOrder]
  norm_num [Complex.div_re]
  linarith [P.residueRadius_pos]

theorem ReflectedBiHeatDatum.norm_leftOrder_le_residueCoeffBound
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hepsilon : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    ‖P.leftOrder epsilon‖ ≤ P.residueCoeffBound := by
  have hnorm : ‖epsilon‖ ≤ P.residueRadius := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hepsilon
  calc
    ‖P.leftOrder epsilon‖ ≤ ‖P.z‖ + ‖epsilon / 2‖ := by
      rw [ReflectedBiHeatDatum.leftOrder]
      exact norm_add_le _ _
    _ = ‖P.z‖ + ‖epsilon‖ / 2 := by rw [norm_div]; norm_num
    _ ≤ P.residueCoeffBound := by
      rw [ReflectedBiHeatDatum.residueCoeffBound]
      nlinarith [norm_nonneg (1 - P.z), P.residueRadius_pos]

theorem ReflectedBiHeatDatum.norm_rightOrder_le_residueCoeffBound
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hepsilon : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    ‖P.rightOrder epsilon‖ ≤ P.residueCoeffBound := by
  have hnorm : ‖epsilon‖ ≤ P.residueRadius := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hepsilon
  calc
    ‖P.rightOrder epsilon‖ ≤ ‖1 - P.z‖ + ‖epsilon / 2‖ := by
      rw [ReflectedBiHeatDatum.rightOrder]
      exact norm_add_le _ _
    _ = ‖1 - P.z‖ + ‖epsilon‖ / 2 := by rw [norm_div]; norm_num
    _ ≤ P.residueCoeffBound := by
      rw [ReflectedBiHeatDatum.residueCoeffBound]
      nlinarith [norm_nonneg P.z, P.residueRadius_pos]

/-- Uniform summable majorant for the row-renormalized series. -/
def reflectedBiHeatRegularMajorant (P : ReflectedBiHeatDatum) :
    (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℝ
  | Sum.inl q => P.residueCoeffBound *
      ((q.1 : ℝ) * heatCoeff P.x (q.1 : ℤ)) *
      ((q.2 : ℝ) + 1) ^ (-(2 - P.residueRadius))
  | Sum.inr q => P.residueCoeffBound *
      (((q.1 : ℝ) + 1) * heatCoeff P.x (-((q.1 : ℤ) + 1))) *
      ((q.2 : ℝ) + 1) ^ (-(2 - P.residueRadius))

theorem summable_reflectedBiHeatRegularMajorant (P : ReflectedBiHeatDatum) :
    Summable (reflectedBiHeatRegularMajorant P) := by
  have hbase : Summable (fun n : ℕ =>
      ((n : ℝ) + 1) ^ (-(2 - P.residueRadius))) :=
    summable_nat_add_one_rpow_neg (by linarith [P.residueRadius_lt_one])
  have hbase_nonneg : ∀ n : ℕ,
      0 ≤ ((n : ℝ) + 1) ^ (-(2 - P.residueRadius)) := fun n =>
    Real.rpow_nonneg (by positivity) _
  apply Summable.sum
  · change Summable (fun q : ℕ × ℕ => P.residueCoeffBound *
        ((q.1 : ℝ) * heatCoeff P.x (q.1 : ℤ)) *
        ((q.2 : ℝ) + 1) ^ (-(2 - P.residueRadius)))
    have hk := (summable_nat_mul_heatCoeff P).mul_left P.residueCoeffBound
    exact hk.mul_of_nonneg hbase
      (fun k => mul_nonneg P.residueCoeffBound_nonneg
        (mul_nonneg (Nat.cast_nonneg k) (heatCoeff_pos P.x _).le)) hbase_nonneg
  · change Summable (fun q : ℕ × ℕ => P.residueCoeffBound *
        (((q.1 : ℝ) + 1) * heatCoeff P.x (-((q.1 : ℤ) + 1))) *
        ((q.2 : ℝ) + 1) ^ (-(2 - P.residueRadius)))
    have hk := (summable_nat_add_one_mul_heatCoeff P).mul_left P.residueCoeffBound
    exact hk.mul_of_nonneg hbase
      (fun k => mul_nonneg P.residueCoeffBound_nonneg
        (mul_nonneg (by positivity) (heatCoeff_pos P.x _).le)) hbase_nonneg

theorem norm_reflectedBiHeatRegularTerm_le_majorant
    (P : ReflectedBiHeatDatum) (q : (ℕ × ℕ) ⊕ (ℕ × ℕ)) {epsilon : ℂ}
    (hepsilon : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    ‖reflectedBiHeatRegularTerm P epsilon q‖ ≤
      reflectedBiHeatRegularMajorant P q := by
  have hre := P.neg_radius_le_re_of_mem_closedBall hepsilon
  have hsum : (P.leftOrder epsilon).re + (P.rightOrder epsilon).re =
      1 + epsilon.re := by
    simpa using congrArg Complex.re (P.leftOrder_add_rightOrder epsilon)
  rcases q with ⟨k, n⟩ | ⟨k, n⟩
  · rw [reflectedBiHeatRegularTerm, reflectedBiHeatRegularMajorant]
    refine (norm_reflectedBiHeatUpperRowTerm_le P
      (P.leftOrder_re_pos_of_mem_closedBall hepsilon) k n).trans ?_
    have hpow : ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
          (P.rightOrder epsilon).re - 1) ≤
        ((n : ℝ) + 1) ^ (-(2 - P.residueRadius)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by simp)
      linarith [hsum]
    have hcoeff : ‖P.leftOrder epsilon‖ * (k : ℝ) ≤
        P.residueCoeffBound * (k : ℝ) :=
      mul_le_mul_of_nonneg_right (P.norm_leftOrder_le_residueCoeffBound hepsilon)
        (Nat.cast_nonneg k)
    have hfinal := mul_le_mul_of_nonneg_right
      (mul_le_mul hcoeff hpow
        (Real.rpow_nonneg (by positivity)
          (-(P.leftOrder epsilon).re - (P.rightOrder epsilon).re - 1))
        (mul_nonneg P.residueCoeffBound_nonneg (Nat.cast_nonneg k)))
      (heatCoeff_pos P.x (k : ℤ)).le
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hfinal
  · rw [reflectedBiHeatRegularTerm, reflectedBiHeatRegularMajorant]
    refine (norm_reflectedBiHeatLowerRowTerm_le P
      (P.rightOrder_re_pos_of_mem_closedBall hepsilon) k n).trans ?_
    have hpow : ((n : ℝ) + 1) ^ (-(P.leftOrder epsilon).re -
          (P.rightOrder epsilon).re - 1) ≤
        ((n : ℝ) + 1) ^ (-(2 - P.residueRadius)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by simp)
      linarith [hsum]
    have hk0 : 0 ≤ (k : ℝ) + 1 := by positivity
    have hcoeff : ‖P.rightOrder epsilon‖ * ((k : ℝ) + 1) ≤
        P.residueCoeffBound * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (P.norm_rightOrder_le_residueCoeffBound hepsilon) hk0
    have hfinal := mul_le_mul_of_nonneg_right
      (mul_le_mul hcoeff hpow
        (Real.rpow_nonneg (by positivity)
          (-(P.leftOrder epsilon).re - (P.rightOrder epsilon).re - 1))
        (mul_nonneg P.residueCoeffBound_nonneg hk0))
      (heatCoeff_pos P.x (-((k : ℤ) + 1))).le
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- A fixed positive-real base to a continuous complex exponent is continuous. -/
theorem continuous_ofReal_cpow_comp {c : ℝ} (hc : 0 < c)
    (f : ℂ → ℂ) (hf : Continuous f) :
    Continuous (fun epsilon => ((c : ℝ) : ℂ) ^ (f epsilon)) := by
  rw [continuous_iff_continuousAt]
  intro epsilon
  exact (continuousAt_const_cpow
    (Complex.ofReal_ne_zero.mpr hc.ne')).comp hf.continuousAt

/-- Each pole-free row term is continuous in the complex regulator. -/
theorem continuous_reflectedBiHeatRegularTerm
    (P : ReflectedBiHeatDatum) (q : (ℕ × ℕ) ⊕ (ℕ × ℕ)) :
    Continuous (fun epsilon => reflectedBiHeatRegularTerm P epsilon q) := by
  rcases q with ⟨k, n⟩ | ⟨k, n⟩
  · simp only [reflectedBiHeatRegularTerm, reflectedBiHeatUpperRowTerm,
      reflectedBiHeatRowModel]
    have hleft := continuous_ofReal_cpow_comp
      (c := ((n + k : ℕ) : ℝ) + 1) (by positivity)
      (fun epsilon => -P.leftOrder epsilon) (by
        unfold ReflectedBiHeatDatum.leftOrder
        fun_prop)
    have hright := continuous_ofReal_cpow_comp
      (c := (n : ℝ) + 1) (by positivity)
      (fun epsilon => -P.rightOrder epsilon) (by
        unfold ReflectedBiHeatDatum.rightOrder
        fun_prop)
    have hmodel := continuous_ofReal_cpow_comp
      (c := (n : ℝ) + 1) (by positivity)
      (fun epsilon => -(1 + epsilon)) (by fun_prop)
    exact continuous_const.mul ((hleft.mul hright).sub hmodel)
  · simp only [reflectedBiHeatRegularTerm, reflectedBiHeatLowerRowTerm,
      reflectedBiHeatRowModel]
    have hleft := continuous_ofReal_cpow_comp
      (c := (n : ℝ) + 1) (by positivity)
      (fun epsilon => -P.leftOrder epsilon) (by
        unfold ReflectedBiHeatDatum.leftOrder
        fun_prop)
    have hright := continuous_ofReal_cpow_comp
      (c := ((n + k + 1 : ℕ) : ℝ) + 1) (by positivity)
      (fun epsilon => -P.rightOrder epsilon) (by
        unfold ReflectedBiHeatDatum.rightOrder
        fun_prop)
    have hmodel := continuous_ofReal_cpow_comp
      (c := (n : ℝ) + 1) (by positivity)
      (fun epsilon => -(1 + epsilon)) (by fun_prop)
    exact continuous_const.mul ((hleft.mul hright).sub hmodel)

/-- Normally convergent pole-free part of the reflected pairing. -/
def reflectedBiHeatRegularSum (P : ReflectedBiHeatDatum) (epsilon : ℂ) : ℂ :=
  ∑' q, reflectedBiHeatRegularTerm P epsilon q

theorem continuousOn_reflectedBiHeatRegularSum (P : ReflectedBiHeatDatum) :
    ContinuousOn (reflectedBiHeatRegularSum P)
      (Metric.closedBall 0 P.residueRadius) := by
  have huniform := tendstoUniformlyOn_tsum
    (summable_reflectedBiHeatRegularMajorant P)
    (fun q epsilon hepsilon =>
      norm_reflectedBiHeatRegularTerm_le_majorant P q hepsilon)
  exact huniform.continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun S =>
      continuousOn_finsetSum S fun q _ =>
        (continuous_reflectedBiHeatRegularTerm P q).continuousOn))

theorem continuousWithinAt_reflectedBiHeatRegularSum_zero (P : ReflectedBiHeatDatum) :
    ContinuousWithinAt (reflectedBiHeatRegularSum P)
      (Metric.closedBall 0 P.residueRadius) 0 := by
  apply continuousOn_reflectedBiHeatRegularSum P
  simp [P.residueRadius_pos.le]

/-! ## Exact positive-regulator decomposition and pole fill -/

/-- Row orientation used by the regular terms: difference first, smaller index second. -/
def reflectedBiHeatRowEquiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ :=
  {
    toFun := fun q => match q with
      | Sum.inl p => (p.2 + p.1, p.2)
      | Sum.inr p => (p.2, p.2 + p.1 + 1)
    invFun := fun p =>
      if p.2 ≤ p.1 then Sum.inl (p.1 - p.2, p.2)
      else Sum.inr (p.2 - p.1 - 1, p.1)
    left_inv := by
      intro q
      rcases q with ⟨k, n⟩ | ⟨k, n⟩ <;> simp <;> omega
    right_inv := by
      intro p
      rcases p with ⟨m, n⟩
      by_cases h : n ≤ m <;> simp [h] <;> omega
  }

theorem reflectedBiHeatRowEquiv_inl (k n : ℕ) :
    reflectedBiHeatRowEquiv (Sum.inl (k, n)) = (n + k, n) := rfl

theorem reflectedBiHeatRowEquiv_inr (k n : ℕ) :
    reflectedBiHeatRowEquiv (Sum.inr (k, n)) = (n, n + k + 1) := rfl

/-- Pole model carried by each additive-difference row. -/
def reflectedBiHeatPoleTerm
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) :
    (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℂ
  | Sum.inl q => ((heatCoeff P.x (q.1 : ℤ) : ℝ) : ℂ) *
      reflectedBiHeatRowModel epsilon q.2
  | Sum.inr q => ((heatCoeff P.x (-((q.1 : ℤ) + 1)) : ℝ) : ℂ) *
      reflectedBiHeatRowModel epsilon q.2

/-- The regulated reflected double sum, before pole filling. -/
def reflectedBiHeatPairSum (P : ReflectedBiHeatDatum) (epsilon : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,
    asymmetricHeatPairTerm (P.leftOrder epsilon) (P.rightOrder epsilon) P.x p

theorem reflectedBiHeatPairTerm_comp_rowEquiv_eq_regular_add_pole
    (P : ReflectedBiHeatDatum) (epsilon : ℂ)
    (q : (ℕ × ℕ) ⊕ (ℕ × ℕ)) :
    asymmetricHeatPairTerm (P.leftOrder epsilon) (P.rightOrder epsilon) P.x
        (reflectedBiHeatRowEquiv q) =
      reflectedBiHeatRegularTerm P epsilon q +
        reflectedBiHeatPoleTerm P epsilon q := by
  rcases q with ⟨k, n⟩ | ⟨k, n⟩
  · rw [reflectedBiHeatRowEquiv_inl]
    simp only [
      reflectedBiHeatRegularTerm, reflectedBiHeatUpperRowTerm,
      reflectedBiHeatPoleTerm, asymmetricHeatPairTerm]
    have hk : ((n + k : ℕ) : ℤ) - (n : ℤ) = (k : ℤ) := by push_cast; ring
    rw [hk]
    push_cast
    ring
  · rw [reflectedBiHeatRowEquiv_inr]
    simp only [
      reflectedBiHeatRegularTerm, reflectedBiHeatLowerRowTerm,
      reflectedBiHeatPoleTerm, asymmetricHeatPairTerm]
    have hk : (n : ℤ) - ((n + k + 1 : ℕ) : ℤ) = -((k : ℤ) + 1) := by
      push_cast
      ring
    rw [hk]
    push_cast
    ring

/-- The common row model sums to the shifted zeta function. -/
theorem hasSum_reflectedBiHeatRowModel {epsilon : ℂ} (hepsilon : 0 < epsilon.re) :
    HasSum (reflectedBiHeatRowModel epsilon) (riemannZeta (1 + epsilon)) := by
  have hz := hasSum_riemannZeta_shift (w := 1 + epsilon) (by simp; linarith)
  refine hz.congr_fun fun n => ?_
  rw [reflectedBiHeatRowModel, Complex.cpow_neg]
  simp only [one_div]
  congr 2
  push_cast
  ring

/-- Canonical split of the integer lattice into nonnegative and strictly negative rays. -/
def signedNatEquiv : ℕ ⊕ ℕ ≃ ℤ where
  toFun
    | Sum.inl k => (k : ℤ)
    | Sum.inr k => -((k : ℤ) + 1)
  invFun k := if 0 ≤ k then Sum.inl k.toNat else Sum.inr ((-k - 1).toNat)
  left_inv q := by
    rcases q with k | k
    · simp
    · have hneg : ¬ 0 ≤ -((k : ℤ) + 1) := by omega
      have heq : -(-((k : ℤ) + 1)) - 1 = (k : ℤ) := by ring
      change (if 0 ≤ -((k : ℤ) + 1) then
          Sum.inl (-((k : ℤ) + 1)).toNat
        else Sum.inr (-(-((k : ℤ) + 1)) - 1).toNat) = Sum.inr k
      rw [if_neg hneg, heq]
      simp
  right_inv k := by
    by_cases hk : 0 ≤ k
    · simp [hk, Int.toNat_of_nonneg hk]
    · have hkneg : k < 0 := lt_of_not_ge hk
      have hnonneg : 0 ≤ -k - 1 := by omega
      change (match (if 0 ≤ k then Sum.inl k.toNat
        else Sum.inr (-k - 1).toNat) with
        | Sum.inl n => (n : ℤ)
        | Sum.inr n => -((n : ℤ) + 1)) = k
      rw [if_neg hk]
      change -((((-k - 1).toNat : ℕ) : ℤ) + 1) = k
      rw [Int.toNat_of_nonneg hnonneg]
      ring

theorem signedNatEquiv_inl (k : ℕ) : signedNatEquiv (Sum.inl k) = (k : ℤ) := rfl

theorem signedNatEquiv_inr (k : ℕ) :
    signedNatEquiv (Sum.inr k) = -((k : ℤ) + 1) := rfl

/-- Separate the signed row label from the within-row natural index. -/
def reflectedBiHeatPoleRayEquiv :
    (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ (ℕ ⊕ ℕ) × ℕ where
  toFun
    | Sum.inl q => (Sum.inl q.1, q.2)
    | Sum.inr q => (Sum.inr q.1, q.2)
  invFun
    | (Sum.inl k, n) => Sum.inl (k, n)
    | (Sum.inr k, n) => Sum.inr (k, n)
  left_inv q := by rcases q with q | q <;> rfl
  right_inv q := by rcases q with ⟨k | k, n⟩ <;> rfl

theorem reflectedBiHeatPoleRayEquiv_symm_inl (k n : ℕ) :
    reflectedBiHeatPoleRayEquiv.symm (Sum.inl k, n) = Sum.inl (k, n) := rfl

theorem reflectedBiHeatPoleRayEquiv_symm_inr (k n : ℕ) :
    reflectedBiHeatPoleRayEquiv.symm (Sum.inr k, n) = Sum.inr (k, n) := rfl

theorem summable_reflectedBiHeatRegularTerm_on_residueDisc
    (P : ReflectedBiHeatDatum) {epsilon : ℂ}
    (hepsilon : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    Summable (reflectedBiHeatRegularTerm P epsilon) :=
  Summable.of_norm_bounded (summable_reflectedBiHeatRegularMajorant P)
    (fun q => norm_reflectedBiHeatRegularTerm_le_majorant P q hepsilon)

set_option maxHeartbeats 1000000 in
theorem tsum_reflectedBiHeatPoleTerm
    (P : ReflectedBiHeatDatum) {epsilon : ℂ} (hepsilon : 0 < epsilon.re)
    (hsum : Summable (reflectedBiHeatPoleTerm P epsilon)) :
    ∑' q, reflectedBiHeatPoleTerm P epsilon q =
      ((heatCoeffSum P.x : ℝ) : ℂ) * riemannZeta (1 + epsilon) := by
  have hmodel := hasSum_reflectedBiHeatRowModel hepsilon
  have hray : Summable (fun q : (ℕ ⊕ ℕ) × ℕ =>
      ((heatCoeff P.x (signedNatEquiv q.1) : ℝ) : ℂ) *
        reflectedBiHeatRowModel epsilon q.2) := by
    have hcomp := hsum.comp_injective reflectedBiHeatPoleRayEquiv.symm.injective
    refine hcomp.congr fun q => ?_
    rcases q with ⟨k | k, n⟩
    · simp only [Function.comp_apply]
      rw [reflectedBiHeatPoleRayEquiv_symm_inl, reflectedBiHeatPoleTerm,
        signedNatEquiv_inl]
    · simp only [Function.comp_apply]
      rw [reflectedBiHeatPoleRayEquiv_symm_inr, reflectedBiHeatPoleTerm,
        signedNatEquiv_inr]
  have hheatReal : Summable (fun q : ℕ ⊕ ℕ => heatCoeff P.x (signedNatEquiv q)) :=
    (summable_heatCoeff P.x_pos).comp_injective signedNatEquiv.injective
  have hheat : Summable (fun q : ℕ ⊕ ℕ =>
      ((heatCoeff P.x (signedNatEquiv q) : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hheatReal
  calc
    (∑' q, reflectedBiHeatPoleTerm P epsilon q) =
        ∑' q : (ℕ ⊕ ℕ) × ℕ,
          reflectedBiHeatPoleTerm P epsilon (reflectedBiHeatPoleRayEquiv.symm q) :=
      (reflectedBiHeatPoleRayEquiv.symm.tsum_eq
        (reflectedBiHeatPoleTerm P epsilon)).symm
    _ = ∑' q : (ℕ ⊕ ℕ) × ℕ,
        ((heatCoeff P.x (signedNatEquiv q.1) : ℝ) : ℂ) *
          reflectedBiHeatRowModel epsilon q.2 := by
      apply tsum_congr
      intro q
      rcases q with ⟨k | k, n⟩
      · rw [reflectedBiHeatPoleRayEquiv_symm_inl, reflectedBiHeatPoleTerm,
          signedNatEquiv_inl]
      · rw [reflectedBiHeatPoleRayEquiv_symm_inr, reflectedBiHeatPoleTerm,
          signedNatEquiv_inr]
    _ = ∑' q : ℕ ⊕ ℕ, ∑' n : ℕ,
        ((heatCoeff P.x (signedNatEquiv q) : ℝ) : ℂ) *
          reflectedBiHeatRowModel epsilon n := hray.tsum_prod
    _ = ((heatCoeffSum P.x : ℝ) : ℂ) * riemannZeta (1 + epsilon) := by
      have hinner : ∀ q : ℕ ⊕ ℕ, (∑' n : ℕ,
          ((heatCoeff P.x (signedNatEquiv q) : ℝ) : ℂ) *
            reflectedBiHeatRowModel epsilon n) =
          ((heatCoeff P.x (signedNatEquiv q) : ℝ) : ℂ) *
            riemannZeta (1 + epsilon) := by
        intro q
        rw [← hmodel.tsum_eq]
        exact Summable.tsum_mul_left _ hmodel.summable
      rw [tsum_congr hinner, Summable.tsum_mul_right _ hheat]
      have hsigned := signedNatEquiv.tsum_eq (fun k : ℤ => heatCoeff P.x k)
      have hcast : (∑' q : ℕ ⊕ ℕ,
          ((heatCoeff P.x (signedNatEquiv q) : ℝ) : ℂ)) =
          ((heatCoeffSum P.x : ℝ) : ℂ) := by
        rw [← Complex.ofReal_tsum]
        rw [hsigned]
        rfl
      rw [hcast]

theorem reflectedBiHeatPairSum_eq_zeta_pole_add_regular
    (P : ReflectedBiHeatDatum) {epsilon : ℂ} (hepsilon : 0 < epsilon.re)
    (hdisc : epsilon ∈ Metric.closedBall 0 P.residueRadius) :
    reflectedBiHeatPairSum P epsilon =
      ((heatCoeffSum P.x : ℝ) : ℂ) * riemannZeta (1 + epsilon) +
        reflectedBiHeatRegularSum P epsilon := by
  have hleft0 : 0 ≤ (P.leftOrder epsilon).re :=
    (P.leftOrder_re_pos_of_mem_closedBall hdisc).le
  have hright0 : 0 ≤ (P.rightOrder epsilon).re :=
    (P.rightOrder_re_pos_of_mem_closedBall hdisc).le
  have hsumre : 1 < (P.leftOrder epsilon).re + (P.rightOrder epsilon).re := by
    have h : (P.leftOrder epsilon).re + (P.rightOrder epsilon).re =
        1 + epsilon.re := by
      simpa using congrArg Complex.re (P.leftOrder_add_rightOrder epsilon)
    linarith
  have horig := summable_asymmetricHeatPairTerm hleft0 hright0 hsumre P.x_pos
  have hrow : Summable (fun q =>
      asymmetricHeatPairTerm (P.leftOrder epsilon) (P.rightOrder epsilon) P.x
        (reflectedBiHeatRowEquiv q)) :=
    horig.comp_injective reflectedBiHeatRowEquiv.injective
  have hregular := summable_reflectedBiHeatRegularTerm_on_residueDisc P hdisc
  have hrowEq : (fun q =>
      asymmetricHeatPairTerm (P.leftOrder epsilon) (P.rightOrder epsilon) P.x
        (reflectedBiHeatRowEquiv q)) =
      fun q => reflectedBiHeatRegularTerm P epsilon q +
        reflectedBiHeatPoleTerm P epsilon q := by
    funext q
    exact reflectedBiHeatPairTerm_comp_rowEquiv_eq_regular_add_pole P epsilon q
  have hpole : Summable (reflectedBiHeatPoleTerm P epsilon) := by
    have hadd : Summable (fun q => reflectedBiHeatRegularTerm P epsilon q +
        reflectedBiHeatPoleTerm P epsilon q) := hrow.congr (fun q => congrFun hrowEq q)
    exact (hadd.sub hregular).congr fun q => by ring
  rw [reflectedBiHeatPairSum, ← reflectedBiHeatRowEquiv.tsum_eq]
  calc
    (∑' q, asymmetricHeatPairTerm (P.leftOrder epsilon) (P.rightOrder epsilon) P.x
        (reflectedBiHeatRowEquiv q)) =
        ∑' q, (reflectedBiHeatRegularTerm P epsilon q +
          reflectedBiHeatPoleTerm P epsilon q) := tsum_congr fun q =>
            reflectedBiHeatPairTerm_comp_rowEquiv_eq_regular_add_pole P epsilon q
    _ = reflectedBiHeatRegularSum P epsilon +
        ∑' q, reflectedBiHeatPoleTerm P epsilon q := hregular.tsum_add hpole
    _ = ((heatCoeffSum P.x : ℝ) : ℂ) * riemannZeta (1 + epsilon) +
        reflectedBiHeatRegularSum P epsilon := by
          rw [tsum_reflectedBiHeatPoleTerm P hepsilon hpole]
          ring

/-- Forget the positive regulator while retaining its fixed geometric data. -/
def ReflectedBiHeatRegulator.toDatum (Q : ReflectedBiHeatRegulator) :
    ReflectedBiHeatDatum where
  z := Q.z
  x := Q.x
  z_re_pos := Q.z_re_pos
  z_re_lt_one := Q.z_re_lt_one
  x_pos := Q.x_pos

/-- The row-renormalized sum is the literal regulated double sum from the card. -/
theorem reflectedBiHeatPairSum_eq_tsum_reflectedBiHeatPairTerm
    (Q : ReflectedBiHeatRegulator) :
    reflectedBiHeatPairSum Q.toDatum Q.epsilon =
      ∑' p, reflectedBiHeatPairTerm Q p := by
  apply tsum_congr
  intro p
  rfl

/-- The regulator filter approaching zero from the open right half-plane. -/
def reflectedRegulatorZero : Filter ℂ :=
  nhdsWithin 0 {epsilon : ℂ | 0 < epsilon.re}

theorem reflectedRegulatorZero_le_punctured :
    reflectedRegulatorZero ≤ 𝓝[≠] (0 : ℂ) := by
  apply le_inf nhdsWithin_le_nhds
  apply le_principal_iff.mpr
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  simp only [mem_compl_iff, mem_singleton_iff]
  intro hzero
  rw [hzero] at hepsilon
  simp at hepsilon

theorem reflectedRegulatorZero_eventually_mem_residueDisc
    (P : ReflectedBiHeatDatum) :
    ∀ᶠ epsilon in reflectedRegulatorZero,
      epsilon ∈ Metric.closedBall 0 P.residueRadius := by
  have hball : Metric.ball (0 : ℂ) P.residueRadius ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 P.residueRadius_pos
  have hball' : ∀ᶠ epsilon in reflectedRegulatorZero,
      epsilon ∈ Metric.ball (0 : ℂ) P.residueRadius :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hball
  filter_upwards [hball'] with epsilon hepsilon
  exact Metric.ball_subset_closedBall hepsilon

theorem reflectedRegulatorZero_le_residueDisc
    (P : ReflectedBiHeatDatum) :
    reflectedRegulatorZero ≤
      nhdsWithin 0 (Metric.closedBall 0 P.residueRadius) := by
  apply le_inf nhdsWithin_le_nhds
  exact le_principal_iff.mpr
    (reflectedRegulatorZero_eventually_mem_residueDisc P)

/-- **Exact theta residue.** The reflected bi-heat double sum has a simple pole at the symmetric
regulator origin, and its pole-filled value is the full Gaussian theta sum.  The limit is taken in
the complex regulator half-plane, not merely on the positive real ray. -/
theorem tendsto_epsilon_mul_reflectedBiHeatPairSum_theta
    (P : ReflectedBiHeatDatum) :
    Tendsto (fun epsilon => epsilon * reflectedBiHeatPairSum P epsilon)
      reflectedRegulatorZero (𝓝 ((heatCoeffSum P.x : ℝ) : ℂ)) := by
  have hepsilon : Tendsto (fun epsilon : ℂ => epsilon)
      reflectedRegulatorZero (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hzeta : Tendsto (fun epsilon : ℂ =>
      epsilon * riemannZeta (1 + epsilon)) reflectedRegulatorZero (𝓝 1) :=
    tendsto_mul_riemannZeta_add_one.mono_left reflectedRegulatorZero_le_punctured
  have hregular : Tendsto (reflectedBiHeatRegularSum P)
      reflectedRegulatorZero (𝓝 (reflectedBiHeatRegularSum P 0)) :=
    (continuousWithinAt_reflectedBiHeatRegularSum_zero P).mono_left
      (reflectedRegulatorZero_le_residueDisc P)
  have hregularZero : Tendsto (fun epsilon =>
      epsilon * reflectedBiHeatRegularSum P epsilon)
      reflectedRegulatorZero (𝓝 0) := by
    have h := hepsilon.mul hregular
    simpa using h
  have hmain : Tendsto (fun epsilon =>
      ((heatCoeffSum P.x : ℝ) : ℂ) *
          (epsilon * riemannZeta (1 + epsilon)) +
        epsilon * reflectedBiHeatRegularSum P epsilon)
      reflectedRegulatorZero (𝓝 ((heatCoeffSum P.x : ℝ) : ℂ)) := by
    have hconst : Tendsto
        (fun _ : ℂ => ((heatCoeffSum P.x : ℝ) : ℂ))
        reflectedRegulatorZero (𝓝 ((heatCoeffSum P.x : ℝ) : ℂ)) :=
      tendsto_const_nhds
    have h := (hconst.mul hzeta).add hregularZero
    simpa using h
  have heq : (fun epsilon => epsilon * reflectedBiHeatPairSum P epsilon) =ᶠ[
      reflectedRegulatorZero] fun epsilon =>
        ((heatCoeffSum P.x : ℝ) : ℂ) *
            (epsilon * riemannZeta (1 + epsilon)) +
          epsilon * reflectedBiHeatRegularSum P epsilon := by
    filter_upwards [self_mem_nhdsWithin,
      reflectedRegulatorZero_eventually_mem_residueDisc P] with epsilon hpositive hdisc
    rw [reflectedBiHeatPairSum_eq_zeta_pole_add_regular P hpositive hdisc]
    ring
  exact hmain.congr' heq.symm

/-- Premise-free residue capstone for every admissible reflected geometry. -/
theorem reflectedBiHeatThetaResidue_capstone :
    ∀ P : ReflectedBiHeatDatum,
      Tendsto (fun epsilon => epsilon * reflectedBiHeatPairSum P epsilon)
        reflectedRegulatorZero (𝓝 ((heatCoeffSum P.x : ℝ) : ℂ)) := by
  intro P
  exact tendsto_epsilon_mul_reflectedBiHeatPairSum_theta P

/-! ## Canonical finite part on the positive real regulator ray -/

theorem continuousAt_reflectedBiHeatRegularSum_zero (P : ReflectedBiHeatDatum) :
    ContinuousAt (reflectedBiHeatRegularSum P) 0 := by
  apply (continuousWithinAt_reflectedBiHeatRegularSum_zero P).continuousAt
  exact Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : ℂ) P.residueRadius_pos)
    Metric.ball_subset_closedBall

theorem tendsto_one_add_realRegulator :
    Tendsto (fun epsilon : ℝ => 1 + epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun epsilon : ℝ => 1 + epsilon)
        (𝓝 (0 : ℝ)) (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    simpa using hepsilon

/-- Canonical row-subtraction finite part of the reflected double sum. -/
def reflectedBiHeatFinitePart (P : ReflectedBiHeatDatum) : ℂ :=
  ((heatCoeffSum P.x : ℝ) : ℂ) *
      ((Real.eulerMascheroniConstant : ℝ) : ℂ) +
    reflectedBiHeatRegularSum P 0

/-- The exact theta pole subtraction has the canonical Euler--Mascheroni finite part. -/
theorem tendsto_reflectedBiHeatPairSum_sub_thetaPole_finitePart
    (P : ReflectedBiHeatDatum) :
    Tendsto (fun epsilon : ℝ =>
      reflectedBiHeatPairSum P (epsilon : ℂ) -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatFinitePart P)) := by
  have hzetaRaw := tendsto_riemannZeta_sub_pole_real.comp
    tendsto_one_add_realRegulator
  have hzeta : Tendsto (fun epsilon : ℝ =>
      riemannZeta (1 + (epsilon : ℂ)) - 1 / (epsilon : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    simpa [Function.comp_def] using hzetaRaw
  have hregular : Tendsto (fun epsilon : ℝ =>
      reflectedBiHeatRegularSum P (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatRegularSum P 0)) := by
    have hofReal : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (continuousAt_reflectedBiHeatRegularSum_zero P).tendsto.comp hofReal
  have hconst : Tendsto
      (fun _ : ℝ => ((heatCoeffSum P.x : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((heatCoeffSum P.x : ℝ) : ℂ)) := tendsto_const_nhds
  have hmain : Tendsto (fun epsilon : ℝ =>
      ((heatCoeffSum P.x : ℝ) : ℂ) *
          (riemannZeta (1 + (epsilon : ℂ)) - 1 / (epsilon : ℂ)) +
        reflectedBiHeatRegularSum P (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatFinitePart P)) := by
    have h := (hconst.mul hzeta).add hregular
    simpa [reflectedBiHeatFinitePart] using h
  have hofReal : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hclosed : Metric.closedBall (0 : ℂ) P.residueRadius ∈ 𝓝 (0 : ℂ) :=
    Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : ℂ) P.residueRadius_pos)
      Metric.ball_subset_closedBall
  have hdisc : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (epsilon : ℂ) ∈ Metric.closedBall 0 P.residueRadius :=
    hofReal.eventually hclosed
  have heq : (fun epsilon : ℝ =>
      reflectedBiHeatPairSum P (epsilon : ℂ) -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun epsilon => ((heatCoeffSum P.x : ℝ) : ℂ) *
          (riemannZeta (1 + (epsilon : ℂ)) - 1 / (epsilon : ℂ)) +
        reflectedBiHeatRegularSum P (epsilon : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, hdisc] with epsilon hpositive hdisc'
    have hre : 0 < ((epsilon : ℝ) : ℂ).re := by simpa using hpositive
    rw [reflectedBiHeatPairSum_eq_zeta_pole_add_regular P hre hdisc']
    ring
  exact hmain.congr' heq.symm

/-- Premise-free canonical finite-part capstone. -/
theorem reflectedBiHeatFinitePart_capstone :
    ∀ P : ReflectedBiHeatDatum,
      Tendsto (fun epsilon : ℝ =>
        reflectedBiHeatPairSum P (epsilon : ℂ) -
          ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatFinitePart P)) := by
  intro P
  exact tendsto_reflectedBiHeatPairSum_sub_thetaPole_finitePart P

end RHTower
