import GaloisForLFunctions.RHTower.CCMShiftedXiCancellation
import GaloisForLFunctions.RHTower.XiDeck

/-!
# The local pole jet of a Xi-cancelled shifted-zeta term

At a right-half Xi zero of multiplicity `m`, the corresponding cancelled
shifted-zeta term has a zero of order exactly `m - 1`.  This is the local,
multiplicity-safe input for the rectangular shifted-zeta contradiction.
-/

open Complex Filter Function Metric Set

namespace RHTower

noncomputable section

/-- The multiplicity of the Xi zero underlying a right-half divisor copy. -/
def xiRightMultiplicity (q : XiRightZeroCopy) : ℕ :=
  (analyticOrderAt xi (q.1.1 : ℂ)).toNat

theorem xiRightMultiplicity_pos (q : XiRightZeroCopy) :
    0 < xiRightMultiplicity q := by
  apply Nat.pos_of_ne_zero
  unfold xiRightMultiplicity
  exact xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support q.1.1)

/-- Near its shifted pole, a Xi-cancelled shifted-zeta term is exactly the
`(m - 1)`-st power of the local coordinate times a nonvanishing analytic Xi
cofactor and the pole-filled zeta factor. -/
theorem exists_xiShiftedZetaCancelledTerm_local_factorization
    (q : XiRightZeroCopy) :
    ∃ R > 0, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball (q.1.1 : ℂ) R) ∧
      (∀ z ∈ ball (q.1.1 : ℂ) R, h z ≠ 0) ∧
      ∀ s : ℂ, s - 1 / 2 ∈ ball (q.1.1 : ℂ) R →
        xiShiftedZetaCancelledTerm q s =
          (s - xiRightShiftedPole q) ^ (xiRightMultiplicity q - 1) *
            h (s - 1 / 2) *
              regularizedRiemannZeta (s - xiRightCenteredZero q) := by
  obtain ⟨R, hR, h, hhan, hh0, hfact⟩ := xi_peel_ball (q.1.1 : ℂ)
  refine ⟨R, hR, h, hhan, hh0, ?_⟩
  intro s hs
  have hcoord : (s - 1 / 2) - (q.1.1 : ℂ) = s - xiRightShiftedPole q := by
    rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
    ring
  by_cases hsp : s = xiRightShiftedPole q
  · subst s
    rw [xiShiftedZetaCancelledTerm, Function.update_self,
      xiRightShiftedPole_sub_half, xiRightShiftedPole_sub_centeredZero,
      regularizedRiemannZeta_one]
    have hball : (q.1.1 : ℂ) ∈ ball (q.1.1 : ℂ) R := mem_ball_self hR
    have heq : xi =ᶠ[nhds (q.1.1 : ℂ)]
        fun z => (z - (q.1.1 : ℂ)) ^ xiRightMultiplicity q * h z := by
      filter_upwards [isOpen_ball.mem_nhds hball] with z hz
      simpa [xiRightMultiplicity] using hfact z hz
    have hderiv : deriv xi (q.1.1 : ℂ) =
        deriv (fun z => (z - (q.1.1 : ℂ)) ^ xiRightMultiplicity q * h z)
          (q.1.1 : ℂ) := heq.deriv_eq
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (xiRightMultiplicity_pos q))
    rw [hk] at hderiv ⊢
    cases k with
    | zero =>
        rw [hderiv]
        have hh := (hhan (q.1.1 : ℂ) hball).differentiableAt.hasDerivAt
        simpa using
          ((((hasDerivAt_id (q.1.1 : ℂ)).sub_const (q.1.1 : ℂ)).pow 1).mul hh).deriv
    | succ k =>
        rw [hderiv]
        have hh := (hhan (q.1.1 : ℂ) hball).differentiableAt.hasDerivAt
        simpa using
          ((((hasDerivAt_id (q.1.1 : ℂ)).sub_const (q.1.1 : ℂ)).pow (k + 2)).mul hh).deriv
  · rw [xiShiftedZetaCancelledTerm, Function.update_of_ne hsp,
      hfact (s - 1 / 2) hs, regularizedRiemannZeta_of_ne_one]
    · rw [hcoord]
      have hm := xiRightMultiplicity_pos q
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      change (s - xiRightShiftedPole q) ^ xiRightMultiplicity q *
          h (s - 1 / 2) * riemannZeta (s - xiRightCenteredZero q) = _
      rw [hk]
      simp only [Nat.succ_sub_one]
      rw [pow_succ, xiRightShiftedPole]
      ring
    · intro hz
      apply hsp
      rw [xiRightShiftedPole]
      linear_combination hz

end

end RHTower
