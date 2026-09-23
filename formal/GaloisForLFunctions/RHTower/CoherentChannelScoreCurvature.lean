import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# The coherent channel score and curvature law

Normalizing a positive weight family `p` to the probability law `μ_n = p_n / P` turns the first two
logarithmic derivatives of `P` into the mean score and the total curvature of the law:

`P₁/P = 𝔼_μ s`,  `(P₀P₂ − P₁²)/P² = 𝔼_μ c + Var_μ(s)`,

where `s_n = −p_n'/p_n` and `c_n = p_n''/p_n − s_n²`.  The completed curvature of a difference of
two such families is then the exact mismatch form

`Δ = (A − P)(A v_A − P v_P) − A P (m_A − m_P)²`.

Both statements are algebraic identities; only nonvanishing of the individual weights and of the
totals is used.
-/

namespace RHTower

noncomputable section

variable {ι : Type*}

/-- The channel score `s_n = −p_n'/p_n`. -/
def channelScore (p d1 : ι → ℝ) (n : ι) : ℝ := -d1 n / p n

/-- The channel curvature `c_n = p_n''/p_n − s_n²`. -/
def channelCurvature (p d1 d2 : ι → ℝ) (n : ι) : ℝ :=
  d2 n / p n - channelScore p d1 n ^ (2 : ℕ)

/-- The normalized channel weight `μ_n = p_n / P`. -/
def channelWeight (P : ℝ) (p : ι → ℝ) (n : ι) : ℝ := p n / P

theorem channelWeight_mul_score {P : ℝ} {p d1 : ι → ℝ} {n : ι} (hp : p n ≠ 0) :
    channelWeight P p n * channelScore p d1 n = -d1 n / P := by
  rw [channelWeight, channelScore]
  field_simp

theorem channelWeight_mul_curvature {P : ℝ} {p d1 d2 : ι → ℝ} {n : ι} (hp : p n ≠ 0) :
    channelWeight P p n * channelCurvature p d1 d2 n
      = d2 n / P - channelWeight P p n * channelScore p d1 n ^ (2 : ℕ) := by
  rw [channelWeight, channelCurvature]
  field_simp

/-! ## The finite law -/

/-- **(24.191), first half.**  The normalized first logarithmic derivative is the mean score. -/
theorem channel_mean_score (s : Finset ι) (P : ℝ) (p d1 : ι → ℝ)
    (hp : ∀ n ∈ s, p n ≠ 0) :
    (-∑ n ∈ s, d1 n) / P
      = ∑ n ∈ s, channelWeight P p n * channelScore p d1 n := by
  rw [Finset.sum_congr rfl fun n hn => channelWeight_mul_score (P := P) (d1 := d1) (hp n hn)]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]

/-- **(24.191), second half.**  The normalized second logarithmic determinant is the mean
curvature plus the score variance. -/
theorem channel_curvature_variance (s : Finset ι) (P : ℝ) (p d1 d2 : ι → ℝ)
    (hp : ∀ n ∈ s, p n ≠ 0) (hP : P ≠ 0) :
    (P * (∑ n ∈ s, d2 n) - (∑ n ∈ s, d1 n) ^ (2 : ℕ)) / P ^ (2 : ℕ)
      = (∑ n ∈ s, channelWeight P p n * channelCurvature p d1 d2 n)
        + ((∑ n ∈ s, channelWeight P p n * channelScore p d1 n ^ (2 : ℕ))
          - (∑ n ∈ s, channelWeight P p n * channelScore p d1 n) ^ (2 : ℕ)) := by
  have hcurv : (∑ n ∈ s, channelWeight P p n * channelCurvature p d1 d2 n)
      = (∑ n ∈ s, d2 n) / P - ∑ n ∈ s, channelWeight P p n * channelScore p d1 n ^ (2 : ℕ) := by
    rw [Finset.sum_congr rfl fun n hn =>
      channelWeight_mul_curvature (P := P) (d1 := d1) (d2 := d2) (hp n hn)]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  have hmean : (∑ n ∈ s, channelWeight P p n * channelScore p d1 n)
      = (-∑ n ∈ s, d1 n) / P := (channel_mean_score s P p d1 hp).symm
  rw [hcurv, hmean]
  field_simp
  ring

/-! ## The completed curvature -/

/-- **(24.192) The completed curvature is a mismatch form.**  With `H = A − P`, the exact
curvature `(A₀A₂ − A₁²) − (A₀P₂ + A₂P₀ − 2A₁P₁) + (P₀P₂ − P₁²)` of `(24.148)` is
`H(A v_A − P v_P) − A P (m_A − m_P)²`. -/
theorem completedCurvature_eq_mismatch (A0 A1 A2 P0 P1 P2 : ℝ) (hA : A0 ≠ 0) (hP : P0 ≠ 0) :
    (A0 * A2 - A1 ^ (2 : ℕ)) - (A0 * P2 + A2 * P0 - 2 * A1 * P1) + (P0 * P2 - P1 ^ (2 : ℕ))
      = (A0 - P0) * (A0 * (A2 / A0 - (A1 / A0) ^ (2 : ℕ)) - P0 * (P2 / P0 - (P1 / P0) ^ (2 : ℕ)))
        - A0 * P0 * (A1 / A0 - P1 / P0) ^ (2 : ℕ) := by
  field_simp
  ring

/-! ## The summable law -/

/-- **(24.191) for an absolutely convergent channel family.** -/
theorem channel_curvature_variance_tsum (P : ℝ) (p d1 d2 : ι → ℝ)
    (hp : ∀ n, p n ≠ 0) (hP : P ≠ 0) (hd2 : Summable d2)
    (hsq : Summable fun n => channelWeight P p n * channelScore p d1 n ^ (2 : ℕ)) :
    (P * (∑' n, d2 n) - (∑' n, d1 n) ^ (2 : ℕ)) / P ^ (2 : ℕ)
      = (∑' n, channelWeight P p n * channelCurvature p d1 d2 n)
        + ((∑' n, channelWeight P p n * channelScore p d1 n ^ (2 : ℕ))
          - (∑' n, channelWeight P p n * channelScore p d1 n) ^ (2 : ℕ)) := by
  have hmean : (∑' n, channelWeight P p n * channelScore p d1 n) = (-∑' n, d1 n) / P := by
    rw [tsum_congr fun n => channelWeight_mul_score (P := P) (d1 := d1) (hp n)]
    rw [tsum_div_const, tsum_neg]
  have hd2P : Summable fun n => d2 n / P := hd2.div_const P
  have hcurv : (∑' n, channelWeight P p n * channelCurvature p d1 d2 n)
      = (∑' n, d2 n) / P - ∑' n, channelWeight P p n * channelScore p d1 n ^ (2 : ℕ) := by
    rw [tsum_congr fun n =>
      channelWeight_mul_curvature (P := P) (d1 := d1) (d2 := d2) (hp n)]
    rw [hd2P.tsum_sub hsq, tsum_div_const]
  rw [hcurv, hmean]
  field_simp
  ring

end

end RHTower
