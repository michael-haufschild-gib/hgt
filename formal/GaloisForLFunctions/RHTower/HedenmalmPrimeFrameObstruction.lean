import GaloisForLFunctions.RHTower.HedenmalmTwoPrimeNormalFrame
import GaloisForLFunctions.HTGeometry.KroneckerApproxRecurrence

/-!
# The prime frame has no Hilbert frame lower bound

After removing the common first-order decay the prime multipliers are the pure sines
`b_p(t) = 2 p^{-1/2} sin(t log p / 2)`.  Unique factorization makes the prime logarithms
rationally independent, so Kronecker recurrence returns all of their phases simultaneously to
zero at arbitrarily large times.  Hence for every finite set of primes the diagonal sum
`∑ b_p(t)²` has infimum zero along arbitrarily large times: the algebraic prime rank of the `Xi`
normal line is not a Hilbert frame rank.
-/

open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions

namespace HedenmalmThetaSource

/-- The sine is dominated by the distance of the character from one. -/
theorem abs_sin_le_norm_expChar_sub_one (x : ℝ) :
    |Real.sin x| ≤ ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖ := by
  have h := norm_expChar_sub_sq x 0
  have h0 : Complex.exp (((0 : ℝ) : ℝ) * Complex.I) = 1 := by simp
  rw [h0, sub_zero] at h
  have hpyth := Real.sin_sq_add_cos_sq x
  have hnn : (0 : ℝ) ≤ ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖ := norm_nonneg _
  nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x, abs_nonneg (Real.sin x),
    sq_abs (Real.sin x)]

theorem sq_frameSymbol_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : |Real.sin (t * Real.log n / 2)| ≤ ε) :
    frameSymbol n t ^ 2 ≤ 4 * ε ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hpow0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have habs : |frameSymbol n t| ≤ 2 * ε := by
    rw [frameSymbol, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (n:ℝ) ^ (-(1/2:ℝ)))]
    nlinarith [abs_nonneg (Real.sin (t * Real.log n / 2))]
  nlinarith [abs_nonneg (frameSymbol n t), sq_abs (frameSymbol n t)]

/-- **The finite prime frame has no uniform lower bound.**  For every finite set of primes and
every tolerance there are arbitrarily large times at which the whole diagonal sum of squares is
below the tolerance. -/
theorem exists_gt_sum_sq_frameSymbol_lt (P : Finset Nat.Primes) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ ∑ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2 < δ := by
  classical
  set ε : ℝ := Real.sqrt (δ / (4 * ((P.card : ℝ) + 1))) with hεdef
  have hden : (0 : ℝ) < 4 * ((P.card : ℝ) + 1) := by positivity
  have hquot : (0 : ℝ) < δ / (4 * ((P.card : ℝ) + 1)) := div_pos hδ hden
  have hε : 0 < ε := Real.sqrt_pos.mpr hquot
  have hεsq : ε ^ 2 = δ / (4 * ((P.card : ℝ) + 1)) := Real.sq_sqrt hquot.le
  have hind : LinearIndependent ℚ (fun p : {x // x ∈ P} => Real.log ((p : Nat.Primes) : ℕ)) :=
    linearIndependent_log_primes.comp (fun p : {x // x ∈ P} => (p : Nat.Primes))
      Subtype.val_injective
  obtain ⟨s, hs, hclose⟩ := kronecker_approx_atTop hind (fun _ => (0 : ℝ)) hε (T / 2)
  refine ⟨2 * s, by linarith, ?_⟩
  have hbound : ∀ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) (2 * s) ^ 2 ≤ 4 * ε ^ 2 := by
    intro p hp
    have hj := hclose ⟨p, hp⟩
    have h0 : Complex.exp (((0 : ℝ) : ℝ) * Complex.I) = 1 := by simp
    rw [h0] at hj
    have hexp : expChar (Real.log ((p : Nat.Primes) : ℕ)) s
        = Complex.exp (((Real.log ((p : Nat.Primes) : ℕ) * s : ℝ) : ℝ) * Complex.I) := rfl
    rw [hexp] at hj
    have hsin : |Real.sin (Real.log ((p : Nat.Primes) : ℕ) * s)| ≤ ε :=
      le_of_lt (lt_of_le_of_lt (abs_sin_le_norm_expChar_sub_one _) hj)
    have hn : 1 ≤ ((p : Nat.Primes) : ℕ) := (p : Nat.Primes).2.one_lt.le
    refine sq_frameSymbol_le hn (2 * s) hε.le ?_
    rw [show 2 * s * Real.log ((p : Nat.Primes) : ℕ) / 2
        = Real.log ((p : Nat.Primes) : ℕ) * s by ring]
    exact hsin
  calc ∑ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) (2 * s) ^ 2
      ≤ ∑ _p ∈ P, 4 * ε ^ 2 := Finset.sum_le_sum hbound
    _ = (P.card : ℝ) * (4 * ε ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ < δ := by
        rw [hεsq]
        have hcard : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
        rw [div_eq_inv_mul]
        field_simp
        nlinarith

end HedenmalmThetaSource

end

end RHTower
