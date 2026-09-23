import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! # Sharp finite logarithmic Laplace-score bounds retaining alternating coefficients -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000

/-- The scalar recurrence underlying logarithmic differentiation of tilted moments. -/
def laplaceCoolingJet : ℕ → ℕ → ℝ → ℝ
  | 0, m, z => z^m
  | n+1, m, z => 2*(m : ℝ)*laplaceCoolingJet n m z - 2*laplaceCoolingJet n (m+1) z

/-- Exact order-0 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_0 (z : ℝ) :
    laplaceCoolingJet 0 0 z = (1 : ℝ)*(z)^(0 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-0 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_0_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(0 : ℕ)*laplaceCoolingJet 0 0 z ∧
      (-1 : ℝ)^(0 : ℕ)*laplaceCoolingJet 0 0 z ≤ (2*z)^(0 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_0]
  constructor
  · have heq : (-1 : ℝ)^(0 : ℕ)*((1 : ℝ)*(z)^(0 : ℕ)) =
        (1 : ℝ)*(z-18)^(0 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(0 : ℕ)-(-1 : ℝ)^(0 : ℕ)*((1 : ℝ)*(z)^(0 : ℕ)) =
        (0 : ℝ) := by ring
    have h : 0 ≤ (2*z)^(0 : ℕ)-(-1 : ℝ)^(0 : ℕ)*((1 : ℝ)*(z)^(0 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-1 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_1 (z : ℝ) :
    laplaceCoolingJet 1 0 z = (-2 : ℝ)*(z)^(1 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-1 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_1_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(1 : ℕ)*laplaceCoolingJet 1 0 z ∧
      (-1 : ℝ)^(1 : ℕ)*laplaceCoolingJet 1 0 z ≤ (2*z)^(1 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_1]
  constructor
  · have heq : (-1 : ℝ)^(1 : ℕ)*((-2 : ℝ)*(z)^(1 : ℕ)) =
        (36 : ℝ)*(z-18)^(0 : ℕ) + (2 : ℝ)*(z-18)^(1 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(1 : ℕ)-(-1 : ℝ)^(1 : ℕ)*((-2 : ℝ)*(z)^(1 : ℕ)) =
        (0 : ℝ) := by ring
    have h : 0 ≤ (2*z)^(1 : ℕ)-(-1 : ℝ)^(1 : ℕ)*((-2 : ℝ)*(z)^(1 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-2 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_2 (z : ℝ) :
    laplaceCoolingJet 2 0 z = (-4 : ℝ)*(z)^(1 : ℕ) + (4 : ℝ)*(z)^(2 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-2 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_2_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(2 : ℕ)*laplaceCoolingJet 2 0 z ∧
      (-1 : ℝ)^(2 : ℕ)*laplaceCoolingJet 2 0 z ≤ (2*z)^(2 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_2]
  constructor
  · have heq : (-1 : ℝ)^(2 : ℕ)*((-4 : ℝ)*(z)^(1 : ℕ) + (4 : ℝ)*(z)^(2 : ℕ)) =
        (1224 : ℝ)*(z-18)^(0 : ℕ) + (140 : ℝ)*(z-18)^(1 : ℕ) + (4 : ℝ)*(z-18)^(2 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(2 : ℕ)-(-1 : ℝ)^(2 : ℕ)*((-4 : ℝ)*(z)^(1 : ℕ) + (4 : ℝ)*(z)^(2 : ℕ)) =
        (72 : ℝ)*(z-18)^(0 : ℕ) + (4 : ℝ)*(z-18)^(1 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(2 : ℕ)-(-1 : ℝ)^(2 : ℕ)*((-4 : ℝ)*(z)^(1 : ℕ) + (4 : ℝ)*(z)^(2 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-3 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_3 (z : ℝ) :
    laplaceCoolingJet 3 0 z = (-8 : ℝ)*(z)^(1 : ℕ) + (24 : ℝ)*(z)^(2 : ℕ) + (-8 : ℝ)*(z)^(3 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-3 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_3_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(3 : ℕ)*laplaceCoolingJet 3 0 z ∧
      (-1 : ℝ)^(3 : ℕ)*laplaceCoolingJet 3 0 z ≤ (2*z)^(3 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_3]
  constructor
  · have heq : (-1 : ℝ)^(3 : ℕ)*((-8 : ℝ)*(z)^(1 : ℕ) + (24 : ℝ)*(z)^(2 : ℕ) + (-8 : ℝ)*(z)^(3 : ℕ)) =
        (39024 : ℝ)*(z-18)^(0 : ℕ) + (6920 : ℝ)*(z-18)^(1 : ℕ) + (408 : ℝ)*(z-18)^(2 : ℕ) + (8 : ℝ)*(z-18)^(3 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(3 : ℕ)-(-1 : ℝ)^(3 : ℕ)*((-8 : ℝ)*(z)^(1 : ℕ) + (24 : ℝ)*(z)^(2 : ℕ) + (-8 : ℝ)*(z)^(3 : ℕ)) =
        (7632 : ℝ)*(z-18)^(0 : ℕ) + (856 : ℝ)*(z-18)^(1 : ℕ) + (24 : ℝ)*(z-18)^(2 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(3 : ℕ)-(-1 : ℝ)^(3 : ℕ)*((-8 : ℝ)*(z)^(1 : ℕ) + (24 : ℝ)*(z)^(2 : ℕ) + (-8 : ℝ)*(z)^(3 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-4 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_4 (z : ℝ) :
    laplaceCoolingJet 4 0 z = (-16 : ℝ)*(z)^(1 : ℕ) + (112 : ℝ)*(z)^(2 : ℕ) + (-96 : ℝ)*(z)^(3 : ℕ) + (16 : ℝ)*(z)^(4 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-4 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_4_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(4 : ℕ)*laplaceCoolingJet 4 0 z ∧
      (-1 : ℝ)^(4 : ℕ)*laplaceCoolingJet 4 0 z ≤ (2*z)^(4 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_4]
  constructor
  · have heq : (-1 : ℝ)^(4 : ℕ)*((-16 : ℝ)*(z)^(1 : ℕ) + (112 : ℝ)*(z)^(2 : ℕ) + (-96 : ℝ)*(z)^(3 : ℕ) + (16 : ℝ)*(z)^(4 : ℕ)) =
        (1155744 : ℝ)*(z-18)^(0 : ℕ) + (283952 : ℝ)*(z-18)^(1 : ℕ) + (26032 : ℝ)*(z-18)^(2 : ℕ) + (1056 : ℝ)*(z-18)^(3 : ℕ) + (16 : ℝ)*(z-18)^(4 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(4 : ℕ)-(-1 : ℝ)^(4 : ℕ)*((-16 : ℝ)*(z)^(1 : ℕ) + (112 : ℝ)*(z)^(2 : ℕ) + (-96 : ℝ)*(z)^(3 : ℕ) + (16 : ℝ)*(z)^(4 : ℕ)) =
        (523872 : ℝ)*(z-18)^(0 : ℕ) + (89296 : ℝ)*(z-18)^(1 : ℕ) + (5072 : ℝ)*(z-18)^(2 : ℕ) + (96 : ℝ)*(z-18)^(3 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(4 : ℕ)-(-1 : ℝ)^(4 : ℕ)*((-16 : ℝ)*(z)^(1 : ℕ) + (112 : ℝ)*(z)^(2 : ℕ) + (-96 : ℝ)*(z)^(3 : ℕ) + (16 : ℝ)*(z)^(4 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-5 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_5 (z : ℝ) :
    laplaceCoolingJet 5 0 z = (-32 : ℝ)*(z)^(1 : ℕ) + (480 : ℝ)*(z)^(2 : ℕ) + (-800 : ℝ)*(z)^(3 : ℕ) + (320 : ℝ)*(z)^(4 : ℕ) + (-32 : ℝ)*(z)^(5 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-5 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_5_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(5 : ℕ)*laplaceCoolingJet 5 0 z ∧
      (-1 : ℝ)^(5 : ℕ)*laplaceCoolingJet 5 0 z ≤ (2*z)^(5 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_5]
  constructor
  · have heq : (-1 : ℝ)^(5 : ℕ)*((-32 : ℝ)*(z)^(1 : ℕ) + (480 : ℝ)*(z)^(2 : ℕ) + (-800 : ℝ)*(z)^(3 : ℕ) + (320 : ℝ)*(z)^(4 : ℕ) + (-32 : ℝ)*(z)^(5 : ℕ)) =
        (31384512 : ℝ)*(z-18)^(0 : ℕ) + (10091552 : ℝ)*(z-18)^(1 : ℕ) + (1286880 : ℝ)*(z-18)^(2 : ℕ) + (81440 : ℝ)*(z-18)^(3 : ℕ) + (2560 : ℝ)*(z-18)^(4 : ℕ) + (32 : ℝ)*(z-18)^(5 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(5 : ℕ)-(-1 : ℝ)^(5 : ℕ)*((-32 : ℝ)*(z)^(1 : ℕ) + (480 : ℝ)*(z)^(2 : ℕ) + (-800 : ℝ)*(z)^(3 : ℕ) + (320 : ℝ)*(z)^(4 : ℕ) + (-32 : ℝ)*(z)^(5 : ℕ)) =
        (29081664 : ℝ)*(z-18)^(0 : ℕ) + (6704608 : ℝ)*(z-18)^(1 : ℕ) + (579360 : ℝ)*(z-18)^(2 : ℕ) + (22240 : ℝ)*(z-18)^(3 : ℕ) + (320 : ℝ)*(z-18)^(4 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(5 : ℕ)-(-1 : ℝ)^(5 : ℕ)*((-32 : ℝ)*(z)^(1 : ℕ) + (480 : ℝ)*(z)^(2 : ℕ) + (-800 : ℝ)*(z)^(3 : ℕ) + (320 : ℝ)*(z)^(4 : ℕ) + (-32 : ℝ)*(z)^(5 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-6 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_6 (z : ℝ) :
    laplaceCoolingJet 6 0 z = (-64 : ℝ)*(z)^(1 : ℕ) + (1984 : ℝ)*(z)^(2 : ℕ) + (-5760 : ℝ)*(z)^(3 : ℕ) + (4160 : ℝ)*(z)^(4 : ℕ) + (-960 : ℝ)*(z)^(5 : ℕ) + (64 : ℝ)*(z)^(6 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-6 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_6_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(6 : ℕ)*laplaceCoolingJet 6 0 z ∧
      (-1 : ℝ)^(6 : ℕ)*laplaceCoolingJet 6 0 z ≤ (2*z)^(6 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_6]
  constructor
  · have heq : (-1 : ℝ)^(6 : ℕ)*((-64 : ℝ)*(z)^(1 : ℕ) + (1984 : ℝ)*(z)^(2 : ℕ) + (-5760 : ℝ)*(z)^(3 : ℕ) + (4160 : ℝ)*(z)^(4 : ℕ) + (-960 : ℝ)*(z)^(5 : ℕ) + (64 : ℝ)*(z)^(6 : ℕ)) =
        (766546560 : ℝ)*(z-18)^(0 : ℕ) + (313226432 : ℝ)*(z-18)^(1 : ℕ) + (52567744 : ℝ)*(z-18)^(2 : ℕ) + (4648320 : ℝ)*(z-18)^(3 : ℕ) + (228800 : ℝ)*(z-18)^(4 : ℕ) + (5952 : ℝ)*(z-18)^(5 : ℕ) + (64 : ℝ)*(z-18)^(6 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(6 : ℕ)-(-1 : ℝ)^(6 : ℕ)*((-64 : ℝ)*(z)^(1 : ℕ) + (1984 : ℝ)*(z)^(2 : ℕ) + (-5760 : ℝ)*(z)^(3 : ℕ) + (4160 : ℝ)*(z)^(4 : ℕ) + (-960 : ℝ)*(z)^(5 : ℕ) + (64 : ℝ)*(z)^(6 : ℕ)) =
        (1410235776 : ℝ)*(z-18)^(0 : ℕ) + (412367680 : ℝ)*(z-18)^(1 : ℕ) + (48209216 : ℝ)*(z-18)^(2 : ℕ) + (2816640 : ℝ)*(z-18)^(3 : ℕ) + (82240 : ℝ)*(z-18)^(4 : ℕ) + (960 : ℝ)*(z-18)^(5 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(6 : ℕ)-(-1 : ℝ)^(6 : ℕ)*((-64 : ℝ)*(z)^(1 : ℕ) + (1984 : ℝ)*(z)^(2 : ℕ) + (-5760 : ℝ)*(z)^(3 : ℕ) + (4160 : ℝ)*(z)^(4 : ℕ) + (-960 : ℝ)*(z)^(5 : ℕ) + (64 : ℝ)*(z)^(6 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-7 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_7 (z : ℝ) :
    laplaceCoolingJet 7 0 z = (-128 : ℝ)*(z)^(1 : ℕ) + (8064 : ℝ)*(z)^(2 : ℕ) + (-38528 : ℝ)*(z)^(3 : ℕ) + (44800 : ℝ)*(z)^(4 : ℕ) + (-17920 : ℝ)*(z)^(5 : ℕ) + (2688 : ℝ)*(z)^(6 : ℕ) + (-128 : ℝ)*(z)^(7 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-7 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_7_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(7 : ℕ)*laplaceCoolingJet 7 0 z ∧
      (-1 : ℝ)^(7 : ℕ)*laplaceCoolingJet 7 0 z ≤ (2*z)^(7 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_7]
  constructor
  · have heq : (-1 : ℝ)^(7 : ℕ)*((-128 : ℝ)*(z)^(1 : ℕ) + (8064 : ℝ)*(z)^(2 : ℕ) + (-38528 : ℝ)*(z)^(3 : ℕ) + (44800 : ℝ)*(z)^(4 : ℕ) + (-17920 : ℝ)*(z)^(5 : ℕ) + (2688 : ℝ)*(z)^(6 : ℕ) + (-128 : ℝ)*(z)^(7 : ℕ)) =
        (16319524608 : ℝ)*(z-18)^(0 : ℕ) + (8397914240 : ℝ)*(z-18)^(1 : ℕ) + (1806602112 : ℝ)*(z-18)^(2 : ℕ) + (211637888 : ℝ)*(z-18)^(3 : ℕ) + (14631680 : ℝ)*(z-18)^(4 : ℕ) + (598528 : ℝ)*(z-18)^(5 : ℕ) + (13440 : ℝ)*(z-18)^(6 : ℕ) + (128 : ℝ)*(z-18)^(7 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(7 : ℕ)-(-1 : ℝ)^(7 : ℕ)*((-128 : ℝ)*(z)^(1 : ℕ) + (8064 : ℝ)*(z)^(2 : ℕ) + (-38528 : ℝ)*(z)^(3 : ℕ) + (44800 : ℝ)*(z)^(4 : ℕ) + (-17920 : ℝ)*(z)^(5 : ℕ) + (2688 : ℝ)*(z)^(6 : ℕ) + (-128 : ℝ)*(z)^(7 : ℕ)) =
        (62044639488 : ℝ)*(z-18)^(0 : ℕ) + (22077038464 : ℝ)*(z-18)^(1 : ℕ) + (3272556672 : ℝ)*(z-18)^(2 : ℕ) + (258654592 : ℝ)*(z-18)^(3 : ℕ) + (11495680 : ℝ)*(z-18)^(4 : ℕ) + (272384 : ℝ)*(z-18)^(5 : ℕ) + (2688 : ℝ)*(z-18)^(6 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(7 : ℕ)-(-1 : ℝ)^(7 : ℕ)*((-128 : ℝ)*(z)^(1 : ℕ) + (8064 : ℝ)*(z)^(2 : ℕ) + (-38528 : ℝ)*(z)^(3 : ℕ) + (44800 : ℝ)*(z)^(4 : ℕ) + (-17920 : ℝ)*(z)^(5 : ℕ) + (2688 : ℝ)*(z)^(6 : ℕ) + (-128 : ℝ)*(z)^(7 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-8 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_8 (z : ℝ) :
    laplaceCoolingJet 8 0 z = (-256 : ℝ)*(z)^(1 : ℕ) + (32512 : ℝ)*(z)^(2 : ℕ) + (-247296 : ℝ)*(z)^(3 : ℕ) + (435456 : ℝ)*(z)^(4 : ℕ) + (-268800 : ℝ)*(z)^(5 : ℕ) + (68096 : ℝ)*(z)^(6 : ℕ) + (-7168 : ℝ)*(z)^(7 : ℕ) + (256 : ℝ)*(z)^(8 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-8 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_8_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(8 : ℕ)*laplaceCoolingJet 8 0 z ∧
      (-1 : ℝ)^(8 : ℕ)*laplaceCoolingJet 8 0 z ≤ (2*z)^(8 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_8]
  constructor
  · have heq : (-1 : ℝ)^(8 : ℕ)*((-256 : ℝ)*(z)^(1 : ℕ) + (32512 : ℝ)*(z)^(2 : ℕ) + (-247296 : ℝ)*(z)^(3 : ℕ) + (435456 : ℝ)*(z)^(4 : ℕ) + (-268800 : ℝ)*(z)^(5 : ℕ) + (68096 : ℝ)*(z)^(6 : ℕ) + (-7168 : ℝ)*(z)^(7 : ℕ) + (256 : ℝ)*(z)^(8 : ℕ)) =
        (285177973248 : ℝ)*(z-18)^(0 : ℕ) + (188092781312 : ℝ)*(z-18)^(1 : ℕ) + (51750204160 : ℝ)*(z-18)^(2 : ℕ) + (7855378944 : ℝ)*(z-18)^(3 : ℕ) + (725227776 : ℝ)*(z-18)^(4 : ℕ) + (41922048 : ℝ)*(z-18)^(5 : ℕ) + (1487360 : ℝ)*(z-18)^(6 : ℕ) + (29696 : ℝ)*(z-18)^(7 : ℕ) + (256 : ℝ)*(z-18)^(8 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(8 : ℕ)-(-1 : ℝ)^(8 : ℕ)*((-256 : ℝ)*(z)^(1 : ℕ) + (32512 : ℝ)*(z)^(2 : ℕ) + (-247296 : ℝ)*(z)^(3 : ℕ) + (435456 : ℝ)*(z)^(4 : ℕ) + (-268800 : ℝ)*(z)^(5 : ℕ) + (68096 : ℝ)*(z)^(6 : ℕ) + (-7168 : ℝ)*(z)^(7 : ℕ) + (256 : ℝ)*(z)^(8 : ℕ)) =
        (2535931934208 : ℝ)*(z-18)^(0 : ℕ) + (1065733844224 : ℝ)*(z-18)^(1 : ℕ) + (192049417472 : ℝ)*(z-18)^(2 : ℕ) + (19233467904 : ℝ)*(z-18)^(3 : ℕ) + (1155942144 : ℝ)*(z-18)^(4 : ℕ) + (41685504 : ℝ)*(z-18)^(5 : ℕ) + (835072 : ℝ)*(z-18)^(6 : ℕ) + (7168 : ℝ)*(z-18)^(7 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(8 : ℕ)-(-1 : ℝ)^(8 : ℕ)*((-256 : ℝ)*(z)^(1 : ℕ) + (32512 : ℝ)*(z)^(2 : ℕ) + (-247296 : ℝ)*(z)^(3 : ℕ) + (435456 : ℝ)*(z)^(4 : ℕ) + (-268800 : ℝ)*(z)^(5 : ℕ) + (68096 : ℝ)*(z)^(6 : ℕ) + (-7168 : ℝ)*(z)^(7 : ℕ) + (256 : ℝ)*(z)^(8 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-9 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_9 (z : ℝ) :
    laplaceCoolingJet 9 0 z = (-512 : ℝ)*(z)^(1 : ℕ) + (130560 : ℝ)*(z)^(2 : ℕ) + (-1548800 : ℝ)*(z)^(3 : ℕ) + (3978240 : ℝ)*(z)^(4 : ℕ) + (-3558912 : ℝ)*(z)^(5 : ℕ) + (1354752 : ℝ)*(z)^(6 : ℕ) + (-236544 : ℝ)*(z)^(7 : ℕ) + (18432 : ℝ)*(z)^(8 : ℕ) + (-512 : ℝ)*(z)^(9 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-9 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_9_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(9 : ℕ)*laplaceCoolingJet 9 0 z ∧
      (-1 : ℝ)^(9 : ℕ)*laplaceCoolingJet 9 0 z ≤ (2*z)^(9 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_9]
  constructor
  · have heq : (-1 : ℝ)^(9 : ℕ)*((-512 : ℝ)*(z)^(1 : ℕ) + (130560 : ℝ)*(z)^(2 : ℕ) + (-1548800 : ℝ)*(z)^(3 : ℕ) + (3978240 : ℝ)*(z)^(4 : ℕ) + (-3558912 : ℝ)*(z)^(5 : ℕ) + (1354752 : ℝ)*(z)^(6 : ℕ) + (-236544 : ℝ)*(z)^(7 : ℕ) + (18432 : ℝ)*(z)^(8 : ℕ) + (-512 : ℝ)*(z)^(9 : ℕ)) =
        (3495066909696 : ℝ)*(z-18)^(0 : ℕ) + (3239495811584 : ℝ)*(z-18)^(1 : ℕ) + (1183811169792 : ℝ)*(z-18)^(2 : ℕ) + (234728976896 : ℝ)*(z-18)^(3 : ℕ) + (28471166976 : ℝ)*(z-18)^(4 : ℕ) + (2219159040 : ℝ)*(z-18)^(5 : ℕ) + (112057344 : ℝ)*(z-18)^(6 : ℕ) + (3554304 : ℝ)*(z-18)^(7 : ℕ) + (64512 : ℝ)*(z-18)^(8 : ℕ) + (512 : ℝ)*(z-18)^(9 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(9 : ℕ)-(-1 : ℝ)^(9 : ℕ)*((-512 : ℝ)*(z)^(1 : ℕ) + (130560 : ℝ)*(z)^(2 : ℕ) + (-1548800 : ℝ)*(z)^(3 : ℕ) + (3978240 : ℝ)*(z)^(4 : ℕ) + (-3558912 : ℝ)*(z)^(5 : ℕ) + (1354752 : ℝ)*(z)^(6 : ℕ) + (-236544 : ℝ)*(z)^(7 : ℕ) + (18432 : ℝ)*(z)^(8 : ℕ) + (-512 : ℝ)*(z)^(9 : ℕ)) =
        (98064889758720 : ℝ)*(z-18)^(0 : ℕ) + (47540482522624 : ℝ)*(z-18)^(1 : ℕ) + (10100628460032 : ℝ)*(z-18)^(2 : ℕ) + (1228068752896 : ℝ)*(z-18)^(3 : ℕ) + (93428643840 : ℝ)*(z-18)^(4 : ℕ) + (4553052672 : ℝ)*(z-18)^(5 : ℕ) + (138765312 : ℝ)*(z-18)^(6 : ℕ) + (2417664 : ℝ)*(z-18)^(7 : ℕ) + (18432 : ℝ)*(z-18)^(8 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(9 : ℕ)-(-1 : ℝ)^(9 : ℕ)*((-512 : ℝ)*(z)^(1 : ℕ) + (130560 : ℝ)*(z)^(2 : ℕ) + (-1548800 : ℝ)*(z)^(3 : ℕ) + (3978240 : ℝ)*(z)^(4 : ℕ) + (-3558912 : ℝ)*(z)^(5 : ℕ) + (1354752 : ℝ)*(z)^(6 : ℕ) + (-236544 : ℝ)*(z)^(7 : ℕ) + (18432 : ℝ)*(z)^(8 : ℕ) + (-512 : ℝ)*(z)^(9 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Exact order-10 scalar score, including all alternating lower coefficients. -/
theorem laplaceCoolingJet_10 (z : ℝ) :
    laplaceCoolingJet 10 0 z = (-1024 : ℝ)*(z)^(1 : ℕ) + (523264 : ℝ)*(z)^(2 : ℕ) + (-9553920 : ℝ)*(z)^(3 : ℕ) + (34923520 : ℝ)*(z)^(4 : ℕ) + (-43545600 : ℝ)*(z)^(5 : ℕ) + (23374848 : ℝ)*(z)^(6 : ℕ) + (-6021120 : ℝ)*(z)^(7 : ℕ) + (768000 : ℝ)*(z)^(8 : ℕ) + (-46080 : ℝ)*(z)^(9 : ℕ) + (1024 : ℝ)*(z)^(10 : ℕ) := by
  norm_num [laplaceCoolingJet]
  <;> ring

/-- The signed order-10 score is bounded by its leading monomial beyond eighteen. -/
theorem laplaceCoolingJet_10_bounds {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^(10 : ℕ)*laplaceCoolingJet 10 0 z ∧
      (-1 : ℝ)^(10 : ℕ)*laplaceCoolingJet 10 0 z ≤ (2*z)^(10 : ℕ) := by
  have hy : 0 ≤ z-18 := by linarith
  rw [laplaceCoolingJet_10]
  constructor
  · have heq : (-1 : ℝ)^(10 : ℕ)*((-1024 : ℝ)*(z)^(1 : ℕ) + (523264 : ℝ)*(z)^(2 : ℕ) + (-9553920 : ℝ)*(z)^(3 : ℕ) + (34923520 : ℝ)*(z)^(4 : ℕ) + (-43545600 : ℝ)*(z)^(5 : ℕ) + (23374848 : ℝ)*(z)^(6 : ℕ) + (-6021120 : ℝ)*(z)^(7 : ℕ) + (768000 : ℝ)*(z)^(8 : ℕ) + (-46080 : ℝ)*(z)^(9 : ℕ) + (1024 : ℝ)*(z)^(10 : ℕ)) =
        (9200559532032 : ℝ)*(z-18)^(0 : ℕ) + (31898587188224 : ℝ)*(z-18)^(1 : ℕ) + (19010219551744 : ℝ)*(z-18)^(2 : ℕ) + (5309643601920 : ℝ)*(z-18)^(3 : ℕ) + (867202001920 : ℝ)*(z-18)^(4 : ℕ) + (90436082688 : ℝ)*(z-18)^(5 : ℕ) + (6232009728 : ℝ)*(z-18)^(6 : ℕ) + (283729920 : ℝ)*(z-18)^(7 : ℕ) + (8232960 : ℝ)*(z-18)^(8 : ℕ) + (138240 : ℝ)*(z-18)^(9 : ℕ) + (1024 : ℝ)*(z-18)^(10 : ℕ) := by ring
    rw [heq] <;> positivity
  · have heq : (2*z)^(10 : ℕ)-(-1 : ℝ)^(10 : ℕ)*((-1024 : ℝ)*(z)^(1 : ℕ) + (523264 : ℝ)*(z)^(2 : ℕ) + (-9553920 : ℝ)*(z)^(3 : ℕ) + (34923520 : ℝ)*(z)^(4 : ℕ) + (-43545600 : ℝ)*(z)^(5 : ℕ) + (23374848 : ℝ)*(z)^(6 : ℕ) + (-6021120 : ℝ)*(z)^(7 : ℕ) + (768000 : ℝ)*(z)^(8 : ℕ) + (-46080 : ℝ)*(z)^(9 : ℕ) + (1024 : ℝ)*(z)^(10 : ℕ)) =
        (3646957880530944 : ℝ)*(z-18)^(0 : ℕ) + (1999300546180096 : ℝ)*(z-18)^(1 : ℕ) + (488789563790336 : ℝ)*(z-18)^(2 : ℕ) + (69919953930240 : ℝ)*(z-18)^(3 : ℕ) + (6446786647040 : ℝ)*(z-18)^(4 : ℕ) + (397163160576 : ℝ)*(z-18)^(5 : ℕ) + (16342029312 : ℝ)*(z-18)^(6 : ℕ) + (432906240 : ℝ)*(z-18)^(7 : ℕ) + (6696960 : ℝ)*(z-18)^(8 : ℕ) + (46080 : ℝ)*(z-18)^(9 : ℕ) := by ring
    have h : 0 ≤ (2*z)^(10 : ℕ)-(-1 : ℝ)^(10 : ℕ)*((-1024 : ℝ)*(z)^(1 : ℕ) + (523264 : ℝ)*(z)^(2 : ℕ) + (-9553920 : ℝ)*(z)^(3 : ℕ) + (34923520 : ℝ)*(z)^(4 : ℕ) + (-43545600 : ℝ)*(z)^(5 : ℕ) + (23374848 : ℝ)*(z)^(6 : ℕ) + (-6021120 : ℝ)*(z)^(7 : ℕ) + (768000 : ℝ)*(z)^(8 : ℕ) + (-46080 : ℝ)*(z)^(9 : ℕ) + (1024 : ℝ)*(z)^(10 : ℕ)) := by
      rw [heq] <;> positivity
    linarith only [h]

/-- Uniform leading-monomial control through the tenth derivative. -/
theorem laplaceCoolingJet_signed_bounds {n : ℕ} (hn : n ≤ 10) {z : ℝ} (hz : 18 ≤ z) :
    0 ≤ (-1 : ℝ)^n*laplaceCoolingJet n 0 z ∧
      (-1 : ℝ)^n*laplaceCoolingJet n 0 z ≤ (2*z)^n := by
  interval_cases n
  · exact laplaceCoolingJet_0_bounds hz
  · exact laplaceCoolingJet_1_bounds hz
  · exact laplaceCoolingJet_2_bounds hz
  · exact laplaceCoolingJet_3_bounds hz
  · exact laplaceCoolingJet_4_bounds hz
  · exact laplaceCoolingJet_5_bounds hz
  · exact laplaceCoolingJet_6_bounds hz
  · exact laplaceCoolingJet_7_bounds hz
  · exact laplaceCoolingJet_8_bounds hz
  · exact laplaceCoolingJet_9_bounds hz
  · exact laplaceCoolingJet_10_bounds hz

/-- Absolute values retain the sharp leading-monomial estimate through order ten. -/
theorem abs_laplaceCoolingJet_le {n : ℕ} (hn : n ≤ 10) {z : ℝ} (hz : 18 ≤ z) :
    |laplaceCoolingJet n 0 z| ≤ (2*z)^n := by
  have h := laplaceCoolingJet_signed_bounds hn hz
  have heq : |laplaceCoolingJet n 0 z| = (-1 : ℝ)^n*laplaceCoolingJet n 0 z := by
    rw [← abs_of_nonneg h.1, abs_mul, abs_pow]
    norm_num
  rw [heq]
  exact h.2

end
end HTGeometry
