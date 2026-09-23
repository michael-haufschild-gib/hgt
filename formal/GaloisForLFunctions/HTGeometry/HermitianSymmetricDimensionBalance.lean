import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Nat

/-!
# Dimension balance in the irreducible compact Hermitian symmetric families

For an irreducible compact Hermitian symmetric space `G/K` write `dim K` for the real dimension of
the isotropy algebra and `dim (G/K)` for the real dimension of the tangent (forbidden) block.  This
file records the dimension functions of the six families and settles, for each of them, whether the
two dimensions can agree.

Every statement below is an unconditional arithmetic theorem about the displayed dimension
function of one named family.  The *completeness* of the six-family list is Cartan's classification
and is a classical input; it is deliberately not encoded here, and no theorem in this file quantifies
over "all irreducible compact Hermitian symmetric spaces".
-/

namespace GaloisForLFunctions.HTGeometry

namespace HermitianSymmetricDimension

/-- Isotropy dimension of `AIII`: `dim s(u(p) ⊕ u(q)) = p² + q² − 1`. -/
def aiiiIsotropy (p q : ℕ) : ℕ := p ^ (2 : ℕ) + q ^ (2 : ℕ) - 1

/-- Tangent dimension of `AIII`: `dim M_{p,q}(ℂ) = 2pq`. -/
def aiiiTangent (p q : ℕ) : ℕ := 2 * p * q

/-- Isotropy dimension of `BDI`: `dim (so(n) ⊕ so(2)) = n(n−1)/2 + 1`. -/
def bdiIsotropy (n : ℕ) : ℕ := n * (n - 1) / 2 + 1

/-- Tangent dimension of `BDI`: `dim (SO(n+2)/(SO(n) × SO(2))) = 2n`. -/
def bdiTangent (n : ℕ) : ℕ := 2 * n

/-- Isotropy dimension of `CI`: `dim u(n) = n²`. -/
def ciIsotropy (n : ℕ) : ℕ := n ^ (2 : ℕ)

/-- Tangent dimension of `CI`: `dim (Sp(n)/U(n)) = n(n+1)`. -/
def ciTangent (n : ℕ) : ℕ := n * (n + 1)

/-- Isotropy dimension of `DIII`: `dim u(n) = n²`. -/
def diiiIsotropy (n : ℕ) : ℕ := n ^ (2 : ℕ)

/-- Tangent dimension of `DIII`: `dim (SO(2n)/U(n)) = n(n−1)`. -/
def diiiTangent (n : ℕ) : ℕ := n * (n - 1)

/-- Isotropy dimension of `EIII`: `dim (spin(10) ⊕ u(1)) = 46`. -/
def eiiiIsotropy : ℕ := 46

/-- Tangent dimension of `EIII`: `dim (E₆/(Spin(10)·U(1))) = 32`. -/
def eiiiTangent : ℕ := 32

/-- Isotropy dimension of `EVII`: `dim (e₆ ⊕ u(1)) = 79`. -/
def eviiIsotropy : ℕ := 79

/-- Tangent dimension of `EVII`: `dim (E₇/(E₆·U(1))) = 54`. -/
def eviiTangent : ℕ := 54

/-- **`BDI` is never balanced.**  Doubling the isotropy formula turns the balance equation into
`n² − 5n + 2 = 0`, which has no solution in the natural numbers. -/
theorem bdi_not_balanced (n : ℕ) : bdiIsotropy n ≠ bdiTangent n := by
  intro h
  unfold bdiIsotropy bdiTangent at h
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self n
  rw [hk] at h
  have hdouble : n * (n - 1) + 2 = 4 * n := by rw [hk]; omega
  rcases Nat.lt_or_ge n 6 with hsmall | hbig
  · interval_cases n <;> omega
  · have hstep : 5 * n ≤ n * (n - 1) := by
      have h5 : 5 ≤ n - 1 := by omega
      calc 5 * n = n * 5 := by ring
        _ ≤ n * (n - 1) := Nat.mul_le_mul_left n h5
    omega

/-- **`CI` is never balanced in positive rank.** -/
theorem ci_not_balanced {n : ℕ} (hn : 0 < n) : ciIsotropy n ≠ ciTangent n := by
  intro h
  unfold ciIsotropy ciTangent at h
  have : n ^ (2 : ℕ) + n = n * (n + 1) := by ring
  omega

/-- **`DIII` is never balanced in positive rank.** -/
theorem diii_not_balanced {n : ℕ} (hn : 0 < n) : diiiIsotropy n ≠ diiiTangent n := by
  intro h
  unfold diiiIsotropy diiiTangent at h
  have hlt : n * (n - 1) < n ^ (2 : ℕ) := by
    have : n * (n - 1) + n = n ^ (2 : ℕ) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  omega

/-- **`EIII` is not balanced.** -/
theorem eiii_not_balanced : eiiiIsotropy ≠ eiiiTangent := by decide

/-- **`EVII` is not balanced.** -/
theorem evii_not_balanced : eviiIsotropy ≠ eviiTangent := by decide

/-- **`AIII` balance is consecutiveness.**  Among the `AIII` family with `p > q` the balanced
members are exactly those with `p = q + 1`, that is `SU(2q+1)/S(U(q+1) × U(q))`. -/
theorem aiii_balanced_iff (p q : ℕ) (hpq : q < p) :
    aiiiIsotropy p q = aiiiTangent p q ↔ p = q + 1 := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, 1 ≤ d ∧ p = q + d := ⟨p - q, by omega, by omega⟩
  unfold aiiiIsotropy aiiiTangent
  have hexp : (q + d) ^ (2 : ℕ) + q ^ (2 : ℕ) = 2 * (q + d) * q + d ^ (2 : ℕ) := by ring
  have hd2 : 1 ≤ d ^ (2 : ℕ) := Nat.one_le_pow _ _ (by omega)
  rw [hexp]
  set A : ℕ := 2 * (q + d) * q with hA
  constructor
  · intro h
    have hd1 : d ^ (2 : ℕ) = 1 := by omega
    rw [pow_two] at hd1
    have hdle : d ≤ 1 := by
      by_contra hcon
      have hlt : 2 ≤ d := by omega
      have : 2 * 2 ≤ d * d := Nat.mul_le_mul hlt hlt
      omega
    have : d = 1 := le_antisymm hdle hd
    omega
  · intro h
    have hdone : d = 1 := by omega
    subst hdone
    omega

/-- **The balanced rank-two `AIII` member.**  A balanced `AIII` pair of rank two has `q = 2` and
`p = 3`, so its transvection group is `SU(5)`. -/
theorem aiii_balanced_rank_two (p q : ℕ) (hq : 2 ≤ q) (hpq : q < p)
    (hbal : aiiiIsotropy p q = aiiiTangent p q) (hrank : min p q = 2) :
    p = 3 ∧ q = 2 ∧ p + q = 5 := by
  have hcons : p = q + 1 := (aiii_balanced_iff p q hpq).1 hbal
  have hmin : min p q = q := min_eq_right (le_of_lt hpq)
  rw [hmin] at hrank
  subst hrank
  omega

end HermitianSymmetricDimension

end GaloisForLFunctions.HTGeometry
