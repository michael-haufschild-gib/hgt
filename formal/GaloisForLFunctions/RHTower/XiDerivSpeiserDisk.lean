import GaloisForLFunctions.RHTower.XiLogDerivRePositiveStrict
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Zeros of `ξ'` off the critical line lie in Speiser disks

For a zero `ρ` of `ξ`, the Speiser disk is the closed disk with centre `1/2 + i Im ρ` and radius
`|Re ρ − 1/2|`.

**Theorem** (`exists_xi_zero_disk_of_deriv_xi_eq_zero`). Every zero `s` of `ξ'` with
`Re s ≠ 1/2` lies in the Speiser disk of some zero `ρ` of `ξ`:
`(Re s − 1/2)² + (Im s − Im ρ)² ≤ (Re ρ − 1/2)²`.

**Proof.**
- Right of the line and outside all disks, the strict disk criterion gives `Re ξ'/ξ(s) > 0`
  (`re_logDeriv_xi_pos_of_disk_bound`). In particular `ξ'(s) ≠ 0` there.
- The left half follows from `ξ(1 − s) = ξ(s)`.

Consequently `RH` puts every zero of `ξ'` on the critical line (`deriv_xi_zero_re_eq_half_of_re_zeros`).
-/

open Complex

namespace RHTower

noncomputable section

/-- Right of the line, a zero of `ξ'` lies in a Speiser disk. -/
theorem exists_xi_zero_disk_of_deriv_xi_eq_zero_right {s : ℂ} (hs : 1 / 2 < s.re)
    (hd : deriv xi s = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
  by_cases hxi : xi s = 0
  · exact ⟨s, hxi, by simp⟩
  by_contra hno
  push Not at hno
  have hpos := re_logDeriv_xi_pos_of_disk_bound hs hxi fun q =>
    hno (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)
  rw [logDeriv_apply, hd, zero_div, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- **Zeros of `ξ'` off the line lie in Speiser disks.** -/
theorem exists_xi_zero_disk_of_deriv_xi_eq_zero {s : ℂ} (hs : s.re ≠ 1 / 2)
    (hd : deriv xi s = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
  rcases lt_or_gt_of_ne hs with h | h
  · -- reflect through `ξ(1 − s) = ξ(s)`
    have hrefl : deriv xi (1 - s) = 0 := by
      have hfun : (fun z => xi (1 - z)) = xi := funext xi_one_sub
      have hcomp : deriv (fun z => xi (1 - z)) s = -deriv xi (1 - s) := by
        have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
          simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
        have h2 : HasDerivAt (fun z => xi (1 - z)) (deriv xi (1 - s) * -1) s :=
          (xi_differentiable (1 - s)).hasDerivAt.comp s h1
        rw [h2.deriv]; ring
      rw [hfun] at hcomp
      rw [hd] at hcomp
      linear_combination hcomp
    obtain ⟨ρ, hρ, hdisk⟩ := exists_xi_zero_disk_of_deriv_xi_eq_zero_right (s := 1 - s)
      (by simp; linarith) hrefl
    refine ⟨1 - ρ, by rw [xi_one_sub]; exact hρ, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at hdisk ⊢
    nlinarith [hdisk]
  · exact exists_xi_zero_disk_of_deriv_xi_eq_zero_right h hd

/-- **RH puts the zeros of `ξ'` on the line.** If every zero of `ξ` has `Re = 1/2`, so does every
zero of `ξ'`. -/
theorem deriv_xi_zero_re_eq_half_of_re_zeros (hRH : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2) {s : ℂ}
    (hd : deriv xi s = 0) : s.re = 1 / 2 := by
  by_contra hs
  obtain ⟨ρ, hρ, hdisk⟩ := exists_xi_zero_disk_of_deriv_xi_eq_zero hs hd
  rw [hRH ρ hρ, sub_self, zero_pow two_ne_zero] at hdisk
  have : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hs
  have := pow_pos (abs_pos.mpr this) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (s.im - ρ.im)]

end

end RHTower
