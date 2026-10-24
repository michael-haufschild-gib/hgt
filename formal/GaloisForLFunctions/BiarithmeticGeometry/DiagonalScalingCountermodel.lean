import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.PNat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Diagonal scaling does not determine a cofactor metric

A cyclic three-dimensional representation has exact power-law orbit norms and the usual
cofactor packet contraction, but its mixed kernel is not homogeneous. Averaging its three
conjugate metrics gives an exact stationary repair with unchanged diagonal values.
-/

noncomputable section

namespace GaloisForLFunctions.BiarithmeticGeometry

abbrev CyclicTriple := ℝ × ℝ × ℝ

/-- A positive metric with one distinguished mixed coordinate. -/
def cyclicMetric : CyclicTriple →ₗ[ℝ] CyclicTriple →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2 +
        (x.1 * y.2.1 + x.2.1 * y.1) / 3
      map_add' := by intros; dsimp; ring
      map_smul' := by intros; dsimp; ring }
  map_add' := by intros; apply LinearMap.ext; intro z; dsimp; ring
  map_smul' := by intros; apply LinearMap.ext; intro z; dsimp; ring

theorem cyclicMetric_apply (x y : CyclicTriple) :
    cyclicMetric x y = x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2 +
      (x.1 * y.2.1 + x.2.1 * y.1) / 3 := rfl

def cyclicLengthSq (x : CyclicTriple) : ℝ := x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2

theorem cyclicMetric_bounds (x : CyclicTriple) :
    (2 / 3 : ℝ) * cyclicLengthSq x ≤ cyclicMetric x x ∧
      cyclicMetric x x ≤ (4 / 3 : ℝ) * cyclicLengthSq x := by
  have hplus := sq_nonneg (x.1 + x.2.1)
  have hminus := sq_nonneg (x.1 - x.2.1)
  have hlast := sq_nonneg x.2.2
  simp only [cyclicMetric_apply, cyclicLengthSq]
  constructor <;> nlinarith only [hplus, hminus, hlast]

theorem cyclicMetric_nonneg (x : CyclicTriple) : 0 ≤ cyclicMetric x x := by
  have hlen : 0 ≤ cyclicLengthSq x := by unfold cyclicLengthSq; positivity
  exact (mul_nonneg (by norm_num) hlen).trans (cyclicMetric_bounds x).1

def cyclicTurn : Module.End ℝ CyclicTriple where
  toFun x := (x.2.2, x.1, x.2.1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem cyclicTurn_lengthSq (x : CyclicTriple) :
    cyclicLengthSq (cyclicTurn x) = cyclicLengthSq x := by
  unfold cyclicLengthSq cyclicTurn
  dsimp
  ring

theorem cyclicTurn_pow_lengthSq (r : ℕ) (x : CyclicTriple) :
    cyclicLengthSq ((cyclicTurn ^ r) x) = cyclicLengthSq x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, cyclicTurn_lengthSq, ih]

/-- Every cyclic permutation distorts this metric by at most two. -/
theorem cyclicMetric_turn_pow_le (r : ℕ) (x : CyclicTriple) :
    cyclicMetric ((cyclicTurn ^ r) x) ((cyclicTurn ^ r) x) ≤ 2 * cyclicMetric x x := by
  have hupper := (cyclicMetric_bounds ((cyclicTurn ^ r) x)).2
  rw [cyclicTurn_pow_lengthSq] at hupper
  have hlower := (cyclicMetric_bounds x).1
  linarith only [hupper, hlower]

def cyclicOrigin : CyclicTriple := (1, 0, 0)

theorem cyclicTurn_pow_origin (r : ℕ) :
    (cyclicTurn ^ r) cyclicOrigin = (1, 0, 0) ∨
    (cyclicTurn ^ r) cyclicOrigin = (0, 1, 0) ∨
    (cyclicTurn ^ r) cyclicOrigin = (0, 0, 1) := by
  induction r with
  | zero => exact Or.inl rfl
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    rcases ih with h | h | h
    · rw [h]; exact Or.inr (Or.inl rfl)
    · rw [h]; exact Or.inr (Or.inr rfl)
    · rw [h]; exact Or.inl rfl

theorem cyclicMetric_orbit_self (r : ℕ) :
    cyclicMetric ((cyclicTurn ^ r) cyclicOrigin) ((cyclicTurn ^ r) cyclicOrigin) = 1 := by
  rcases cyclicTurn_pow_origin r with h | h | h <;>
    rw [h, cyclicMetric_apply] <;> norm_num

theorem abs_cyclicMetric_orbit_le (r s : ℕ) :
    |cyclicMetric ((cyclicTurn ^ r) cyclicOrigin) ((cyclicTurn ^ s) cyclicOrigin)| ≤ 1 := by
  rcases cyclicTurn_pow_origin r with h | h | h <;>
    rcases cyclicTurn_pow_origin s with k | k | k <;>
      rw [h, k, cyclicMetric_apply] <;> norm_num

/-- The 2-adic valuation drives a finite cyclic action, while all dilations contract. -/
def cyclicDilation (p : ℕ+) : Module.End ℝ CyclicTriple :=
  (1 / (p : ℝ)) • cyclicTurn ^ padicValNat 2 (p : ℕ)

def cyclicVector (j : ℕ+) : CyclicTriple :=
  (1 / (j : ℝ)) • (cyclicTurn ^ padicValNat 2 (j : ℕ)) cyclicOrigin

def cyclicKernel (j k : ℕ+) : ℝ := cyclicMetric (cyclicVector j) (cyclicVector k)

theorem cyclicDilation_mul (p q : ℕ+) :
    cyclicDilation p * cyclicDilation q = cyclicDilation (p * q) := by
  have hval := padicValNat.mul (p.ne_zero) (q.ne_zero) (p := 2)
  simp only [cyclicDilation, PNat.mul_coe, Nat.cast_mul, hval, pow_add,
    one_div, mul_inv, smul_mul_smul_comm]

theorem cyclicDilation_vector (p j : ℕ+) :
    cyclicDilation p (cyclicVector j) = cyclicVector (p * j) := by
  have h := congrArg (fun L : Module.End ℝ CyclicTriple => L cyclicOrigin)
    (cyclicDilation_mul p j)
  exact h

theorem cyclicMetric_dilation (p : ℕ+) (x : CyclicTriple) :
    cyclicMetric (cyclicDilation p x) (cyclicDilation p x) =
      (1 / (p : ℝ)) ^ 2 *
        cyclicMetric ((cyclicTurn ^ padicValNat 2 (p : ℕ)) x)
          ((cyclicTurn ^ padicValNat 2 (p : ℕ)) x) := by
  simp only [cyclicDilation, LinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

/-- The packet contraction is `1/p`, despite failure of homogeneous mixed scaling. -/
theorem cyclicMetric_dilation_le (p : ℕ+) (x : CyclicTriple) :
    cyclicMetric (cyclicDilation p x) (cyclicDilation p x) ≤
      (1 / (p : ℝ)) * cyclicMetric x x := by
  by_cases hp : p = 1
  · subst p
    simp [cyclicDilation]
  · have hp2 : (2 : ℝ) ≤ p := by
      have : 2 ≤ (p : ℕ) := by
        have := p.pos
        have hp1 : (p : ℕ) ≠ 1 := fun h => hp (Subtype.ext h)
        omega
      exact_mod_cast this
    have hp0 : (0 : ℝ) < p := by positivity
    have hfactor : (1 / (p : ℝ)) ^ 2 * 2 ≤ 1 / (p : ℝ) := by
      calc
        _ = (1 / (p : ℝ)) * (2 / (p : ℝ)) := by ring
        _ ≤ (1 / (p : ℝ)) * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one hp0).mpr hp2) (by positivity)
        _ = _ := mul_one _
    rw [cyclicMetric_dilation]
    calc
      _ ≤ (1 / (p : ℝ)) ^ 2 * (2 * cyclicMetric x x) :=
        mul_le_mul_of_nonneg_left (cyclicMetric_turn_pow_le _ x) (sq_nonneg _)
      _ = ((1 / (p : ℝ)) ^ 2 * 2) * cyclicMetric x x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (cyclicMetric_nonneg x)

theorem cyclicKernel_diagonal (j : ℕ+) : cyclicKernel j j = (1 / (j : ℝ)) ^ 2 := by
  simp only [cyclicKernel, cyclicVector, map_smul, LinearMap.smul_apply,
    smul_eq_mul, cyclicMetric_orbit_self]
  ring

theorem abs_cyclicKernel_le (j k : ℕ+) :
    |cyclicKernel j k| ≤ (1 / (j : ℝ)) * (1 / (k : ℝ)) := by
  have hj : 0 ≤ 1 / (j : ℝ) := by positivity
  have hk : 0 ≤ 1 / (k : ℝ) := by positivity
  simp only [cyclicKernel, cyclicVector, map_smul, LinearMap.smul_apply,
    smul_eq_mul, abs_mul, abs_of_nonneg hj, abs_of_nonneg hk]
  calc
    _ = ((1 / (j : ℝ)) * (1 / (k : ℝ))) *
        |cyclicMetric ((cyclicTurn ^ padicValNat 2 (j : ℕ)) cyclicOrigin)
          ((cyclicTurn ^ padicValNat 2 (k : ℕ)) cyclicOrigin)| := by ring
    _ ≤ ((1 / (j : ℝ)) * (1 / (k : ℝ))) * 1 :=
      mul_le_mul_of_nonneg_left (abs_cyclicMetric_orbit_le _ _) (mul_nonneg hj hk)
    _ = _ := mul_one _

/-- The model satisfies the usual critical cofactor radius, with a stronger inverse-linear bound. -/
theorem abs_cyclicKernel_le_critical_radius (j k : ℕ+) :
    |cyclicKernel j k| ≤ (1 / Real.sqrt (j : ℝ)) * (1 / Real.sqrt (k : ℝ)) := by
  have hbound (p : ℕ+) : 1 / (p : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by
    have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.pos
    have hs := Real.one_le_sqrt.mpr hp
    have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p)
    have hsle : Real.sqrt (p : ℝ) ≤ p := by nlinarith only [hs, hs2]
    exact one_div_le_one_div_of_le (by positivity) hsle
  exact (abs_cyclicKernel_le j k).trans
    (mul_le_mul (hbound j) (hbound k) (by positivity) (by positivity))

theorem cyclicKernel_symm (j k : ℕ+) : cyclicKernel j k = cyclicKernel k j := by
  simp only [cyclicKernel, cyclicMetric_apply]
  ring

theorem cyclicKernel_packet (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * cyclicKernel j k) =
      cyclicMetric (∑ j ∈ S, c j • cyclicVector j) (∑ j ∈ S, c j • cyclicVector j) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [cyclicKernel, cyclicMetric_apply]
  ring

theorem cyclicKernel_packet_nonneg (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * cyclicKernel j k := by
  rw [cyclicKernel_packet]
  exact cyclicMetric_nonneg _

theorem cyclicKernel_packet_dilation_le (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * cyclicKernel (p * j) (p * k)) ≤
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * cyclicKernel j k) := by
  have hleft : (∑ j ∈ S, ∑ k ∈ S, c j * c k * cyclicKernel (p * j) (p * k)) =
      cyclicMetric (cyclicDilation p (∑ j ∈ S, c j • cyclicVector j))
        (cyclicDilation p (∑ j ∈ S, c j • cyclicVector j)) := by
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      cyclicDilation_vector, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [cyclicKernel, cyclicMetric_apply]
    ring
  rw [hleft, cyclicKernel_packet]
  exact cyclicMetric_dilation_le p _

theorem cyclicKernel_one_two : cyclicKernel 1 2 = 1 / 6 := by
  norm_num [cyclicKernel, cyclicVector, cyclicOrigin, cyclicMetric_apply, cyclicTurn,
    padicValNat_self]

theorem cyclicKernel_two_four : cyclicKernel 2 4 = 0 := by
  have h4 : padicValNat 2 4 = 2 := by
    simpa using padicValNat.prime_pow (p := 2) 2
  norm_num [cyclicKernel, cyclicVector, cyclicOrigin, cyclicMetric_apply, cyclicTurn,
    padicValNat_self, h4, pow_two, Module.End.mul_apply]

/-- Exact diagonal power laws and all packet contractions do not force mixed homogeneity. -/
theorem cyclicKernel_not_homogeneous :
    cyclicKernel (2 * 1) (2 * 2) ≠ (1 / (2 : ℝ)) ^ 2 * cyclicKernel 1 2 := by
  norm_num only [mul_one, show (2 : ℕ+) * 2 = 4 from rfl,
    cyclicKernel_two_four, cyclicKernel_one_two]

/-- The stronger contraction suggested by diagonal scaling also fails on a mixed vector. -/
theorem cyclicDilation_two_not_quarter_contractive :
    (1 / 4 : ℝ) * cyclicMetric (1, 0, 1) (1, 0, 1) <
      cyclicMetric (cyclicDilation 2 (1, 0, 1)) (cyclicDilation 2 (1, 0, 1)) := by
  norm_num [cyclicDilation, cyclicMetric_apply, cyclicTurn, padicValNat_self]

/-- Three cofactor vectors already span the whole representation. -/
theorem cyclicVector_cyclic (x : CyclicTriple) :
    ∃ a b c : ℝ, x = a • cyclicVector 1 + b • cyclicVector 2 + c • cyclicVector 4 := by
  have h4 : padicValNat 2 4 = 2 := by
    simpa using padicValNat.prime_pow (p := 2) 2
  refine ⟨x.1, 2 * x.2.1, 4 * x.2.2, ?_⟩
  ext <;> norm_num [cyclicVector, cyclicOrigin, cyclicTurn, padicValNat_self,
    h4, pow_two, Module.End.mul_apply] <;> ring

/-- Averaging the finite orbit of metrics restores the missing stationarity. -/
def stationaryCyclicMetric (x y : CyclicTriple) : ℝ :=
  (cyclicMetric x y + cyclicMetric (cyclicTurn x) (cyclicTurn y) +
    cyclicMetric (cyclicTurn (cyclicTurn x)) (cyclicTurn (cyclicTurn y))) / 3

theorem stationaryCyclicMetric_turn (x y : CyclicTriple) :
    stationaryCyclicMetric (cyclicTurn x) (cyclicTurn y) = stationaryCyclicMetric x y := by
  simp only [stationaryCyclicMetric, cyclicMetric_apply, cyclicTurn, LinearMap.coe_mk,
    AddHom.coe_mk]
  ring

theorem stationaryCyclicMetric_turn_pow (r : ℕ) (x y : CyclicTriple) :
    stationaryCyclicMetric ((cyclicTurn ^ r) x) ((cyclicTurn ^ r) y) =
      stationaryCyclicMetric x y := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      stationaryCyclicMetric_turn, ih]

theorem stationaryCyclicMetric_smul (a b : ℝ) (x y : CyclicTriple) :
    stationaryCyclicMetric (a • x) (b • y) = a * b * stationaryCyclicMetric x y := by
  simp only [stationaryCyclicMetric, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem stationaryCyclicMetric_bounds (x : CyclicTriple) :
    (2 / 3 : ℝ) * cyclicLengthSq x ≤ stationaryCyclicMetric x x ∧
      stationaryCyclicMetric x x ≤ (4 / 3 : ℝ) * cyclicLengthSq x := by
  obtain ⟨h0, h0'⟩ := cyclicMetric_bounds x
  obtain ⟨h1, h1'⟩ := cyclicMetric_bounds (cyclicTurn x)
  obtain ⟨h2, h2'⟩ := cyclicMetric_bounds (cyclicTurn (cyclicTurn x))
  simp only [cyclicTurn_lengthSq] at h1 h1' h2 h2'
  unfold stationaryCyclicMetric
  constructor <;> linarith only [h0, h0', h1, h1', h2, h2']

def stationaryCyclicKernel (j k : ℕ+) : ℝ :=
  stationaryCyclicMetric (cyclicVector j) (cyclicVector k)

/-- The averaged metric supplies full homogeneous covariance for the same dilation action. -/
theorem stationaryCyclicKernel_homogeneous (p j k : ℕ+) :
    stationaryCyclicKernel (p * j) (p * k) =
      (1 / (p : ℝ)) ^ 2 * stationaryCyclicKernel j k := by
  unfold stationaryCyclicKernel
  rw [← cyclicDilation_vector, ← cyclicDilation_vector]
  simp only [cyclicDilation, LinearMap.smul_apply, stationaryCyclicMetric_smul,
    stationaryCyclicMetric_turn_pow]
  ring

/-- Stationary repair preserves every diagonal cofactor norm. -/
theorem stationaryCyclicKernel_diagonal (j : ℕ+) :
    stationaryCyclicKernel j j = cyclicKernel j j := by
  rw [cyclicKernel_diagonal]
  unfold stationaryCyclicKernel cyclicVector
  rw [stationaryCyclicMetric_smul, stationaryCyclicMetric_turn_pow]
  norm_num [stationaryCyclicMetric, cyclicOrigin, cyclicTurn, cyclicMetric_apply]
  ring

end GaloisForLFunctions.BiarithmeticGeometry
