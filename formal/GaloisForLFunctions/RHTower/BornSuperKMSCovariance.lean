import GaloisForLFunctions.RHTower.BornEtaGrading

/-!
# Dilation covariance of the graded Born weights: the diagonal super-KMS shadow

On the half-dilated system the dilation isometry `μ_k : |n⟩ ↦ |kn⟩` is rescaled by the
modular flow, `σ_t(μ_k) = k^{it/2}·μ_k`, so a KMS functional at inverse temperature `β`
must be `k^{-β/2}`-covariant along each `μ_k`.  This module proves the diagonal shadow of
that covariance for the graded Gibbs data, unconditionally and on the whole temperature
strip: the `k`-dilated graded doublet weights sum to `k^{-β/2}` times the parity
supertrace.  For odd `k` the dilation also preserves the parity grading, so the covariance
is fully graded; the `2`-dilation kills the sign on its image — the two-twist that makes
`μ₂` the grading's partner rather than a graded symmetry.
-/

noncomputable section

namespace RHTower

/-- The `k`-dilated graded doublet summand: the supertrace weight of the dilated pair
`{k(2n+1), k(2n+2)}` at inverse temperature `β` in the half-dilated gauge. -/
def dilatedBornSupertraceTerm (k : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  ((k * (2 * n + 1) : ℕ) : ℝ) ^ (-(β / 2)) - ((k * (2 * n + 2) : ℕ) : ℝ) ^ (-(β / 2))

theorem dilatedBornSupertraceTerm_eq {k : ℕ} (hk : 0 < k) (β : ℝ) (n : ℕ) :
    dilatedBornSupertraceTerm k β n = (k : ℝ) ^ (-(β / 2)) * bornSupertraceTerm β n := by
  unfold dilatedBornSupertraceTerm bornSupertraceTerm
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- **Dilation super-KMS covariance on the strip.**  For every `k ≥ 1` and every inverse
temperature, the dilated graded weights sum to `k^{-β/2}` times the parity supertrace: the
diagonal shadow of the KMS covariance of the graded Gibbs functional along the dilation
semigroup, valid on the whole strip where only the supertrace converges. -/
theorem tsum_dilatedBornSupertraceTerm {k : ℕ} (hk : 0 < k) (β : ℝ) :
    ∑' n : ℕ, dilatedBornSupertraceTerm k β n
      = (k : ℝ) ^ (-(β / 2)) * bornSupertrace β := by
  rw [show (fun n : ℕ => dilatedBornSupertraceTerm k β n)
      = fun n : ℕ => (k : ℝ) ^ (-(β / 2)) * bornSupertraceTerm β n
    from funext fun n => dilatedBornSupertraceTerm_eq hk β n]
  rw [tsum_mul_left, bornSupertrace]

/-- Odd dilations preserve the parity grading: `(-1)^{kn} = (-1)^n` for odd `k`.  Together
with the covariance this makes every odd `μ_k` a graded KMS symmetry of the diagonal
data. -/
theorem gradedSign_mul_odd {k : ℕ} (hk : Odd k) (n : ℕ) :
    ((-1 : ℝ)) ^ (k * n) = (-1) ^ n := by
  rw [pow_mul, hk.neg_one_pow]

/-- The `2`-dilation kills the sign: `(-1)^{2n} = 1` — the `μ₂` pushforward inverts the
grading on half of its image; the two-twist that pairs `μ₂` with the grading instead of
making it a graded symmetry. -/
theorem gradedSign_mul_two (n : ℕ) : ((-1 : ℝ)) ^ (2 * n) = 1 := by
  rw [pow_mul]
  norm_num

end RHTower
