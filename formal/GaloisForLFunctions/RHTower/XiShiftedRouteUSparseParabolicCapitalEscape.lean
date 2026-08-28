import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceAllDegreeCapital

/-!
# Sparse parabolic escape from Route U source capital

Current Route U scalar laws do not force nonsummable cost along a cofinal strict-frontier
subsequence.  This module gives one closed exact witness.  Degree `2^k` is observed at its
quadratic mass, fixed-degree flux differentiates to positive finite source action, adjacent degree
connectors obey the established coercive scale, and the all-degree account has strict reserve.
Renormalized pointwise action still diverges, while the selected entry fluxes form a geometric
summable series.

The theorem is a no-go for the present cofinal source-capital inference, not a countermodel to the
literal shifted-Xi moment sequence.
-/

open Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Exponentially sparse cofinal degree schedule. -/
def routeUSparseEscapeDegree (k : ℕ) : ℕ := 2 ^ k

/-- Exact quadratic mass attached to the sparse degree. -/
def routeUSparseEscapeMass (k : ℕ) : ℝ :=
  (routeUSparseEscapeDegree k : ℝ) ^ 2

/-- Model cumulative source flux. -/
def routeUSparseEscapeFlux (n : ℕ) (y : ℝ) : ℝ :=
  (n : ℝ) / y

/-- Model positive source action. -/
def routeUSparseEscapeAction (n : ℕ) (y : ℝ) : ℝ :=
  (n : ℝ) / y ^ 2

/-- **Closed sparse-parabolic escape.**  All present scalar source-capital mechanisms coexist
with geometrically summable entry budgets on a cofinal quadratic schedule. -/
theorem routeUSparseParabolicCapitalEscape :
    (∀ k : ℕ, 0 < routeUSparseEscapeDegree k) ∧
    (∀ k : ℕ,
      routeUSparseEscapeMass k = (routeUSparseEscapeDegree k : ℝ) ^ 2) ∧
    Tendsto routeUSparseEscapeDegree atTop atTop ∧
    Tendsto routeUSparseEscapeMass atTop atTop ∧
    (∀ n : ℕ, 0 < n → ∀ y : ℝ, 0 < y →
      HasDerivAt (routeUSparseEscapeFlux n)
        (-routeUSparseEscapeAction n y) y) ∧
    (∀ n : ℕ, 0 < n → ∀ y : ℝ, 0 < y →
      (routeUSparseEscapeFlux (n + 1) y - routeUSparseEscapeFlux n y) ^ 2 <
        (3 / 2 : ℝ) * routeUSparseEscapeAction (n + 1) y) ∧
    (∀ n : ℕ, 0 < n → ∀ y : ℝ, 0 < y →
      2 * routeUSparseEscapeAction n y =
        ((n : ℝ) - 1) / y ^ 2 + ((n : ℝ) + 1) / y ^ 2 ∧
      0 < ((n : ℝ) + 1) / y ^ 2) ∧
    Tendsto (fun k : ℕ =>
      routeUSparseEscapeMass k ^ 2 *
        routeUSparseEscapeAction (routeUSparseEscapeDegree k)
          (routeUSparseEscapeMass k)) atTop atTop ∧
    (∀ k : ℕ,
      routeUSparseEscapeFlux (routeUSparseEscapeDegree k)
          (routeUSparseEscapeMass k) = (1 / 2 : ℝ) ^ k) ∧
    Summable (fun k : ℕ =>
      routeUSparseEscapeFlux (routeUSparseEscapeDegree k)
        (routeUSparseEscapeMass k)) := by
  constructor
  · intro k
    exact pow_pos (by norm_num) k
  constructor
  · intro k
    rfl
  constructor
  · exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  constructor
  · have hpow : Tendsto (fun k : ℕ => (4 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    convert hpow using 1
    funext k
    simp [routeUSparseEscapeMass, routeUSparseEscapeDegree, Nat.cast_pow,
      ← mul_pow, pow_two]
    norm_num
  constructor
  · intro n hn y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have h := (hasDerivAt_inv hy0).const_mul (n : ℝ)
    change HasDerivAt (fun z : ℝ => (n : ℝ) * z⁻¹)
      (-((n : ℝ) * (y ^ 2)⁻¹)) y
    simpa only [mul_neg, neg_mul] using h
  constructor
  · intro n hn y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hn1 : (1 : ℝ) < (3 / 2 : ℝ) * (n + 1 : ℕ) := by
      push_cast
      nlinarith
    rw [routeUSparseEscapeFlux, routeUSparseEscapeFlux,
      routeUSparseEscapeAction]
    have hdiff : ((n + 1 : ℕ) : ℝ) / y - (n : ℝ) / y = 1 / y := by
      push_cast
      field_simp
      ring
    rw [hdiff]
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
    calc
      (1 / y) ^ 2 = 1 / y ^ 2 := by field_simp
      _ < ((3 / 2 : ℝ) * (n + 1 : ℕ)) / y ^ 2 := by gcongr
      _ = (3 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ) / y ^ 2) := by ring
  constructor
  · intro n hn y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    constructor
    · rw [routeUSparseEscapeAction]
      field_simp
      ring
    · positivity
  constructor
  · have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    convert hpow using 1
    funext k
    simp only [routeUSparseEscapeMass, routeUSparseEscapeDegree,
      routeUSparseEscapeAction, Nat.cast_pow, Nat.cast_ofNat]
    have hk : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  constructor
  · intro k
    simp only [routeUSparseEscapeFlux, routeUSparseEscapeMass,
      routeUSparseEscapeDegree, Nat.cast_pow, Nat.cast_ofNat, div_pow]
    have hk : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    simp
  · have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact hgeom.congr fun k => by
      simp only [routeUSparseEscapeFlux, routeUSparseEscapeMass,
        routeUSparseEscapeDegree, Nat.cast_pow, Nat.cast_ofNat, div_pow]
      have hk : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      simp

end

end RHTower
