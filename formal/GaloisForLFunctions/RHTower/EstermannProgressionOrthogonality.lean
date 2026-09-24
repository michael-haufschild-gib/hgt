import GaloisForLFunctions.RHTower.EstermannMeanZeroTwist
import GaloisForLFunctions.RHTower.HurwitzFiniteExpansion

/-!
# Additive orthogonality: twisted divisor sums assemble the divisor sum in a progression

Summing the smoothed twisted divisor sums over all residues `a` mod `q` against the conjugate
character `e(−ab/q)` detects the progression `N ≡ b (mod q)`:

`∑_{a mod q} e(−ab/q) ∑_N d(N) e(aN/q) e^{-Nx} = q · ∑_{N ≡ b (q)} d(N) e^{-Nx}`.

This is exact, for every modulus, and is the bridge from the Estermann layer to divisor sums in
arithmetic progressions.  The interchange of the finite character sum with the infinite divisor sum
is justified by absolute convergence, `d(N) ≤ N + 1` against the geometric factor `e^{-Nx}`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The smoothed twisted divisor terms are absolutely summable for every positive `x`. -/
theorem summable_estermannSmoothedTerm (q : ℕ) [NeZero q] (a : ZMod q) {x : ℝ} (hx : 0 < x) :
    Summable (fun N : ℕ => estermannCoeff q a N * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ))) := by
  set r : ℝ := Real.exp (-x) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0, hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun N : ℕ => ((N : ℝ) + 1) * r ^ N) := by
    have h1 : Summable (fun N : ℕ => (N : ℝ) * r ^ N) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr1
    have h2 : Summable (fun N : ℕ => r ^ N) := summable_geometric_of_lt_one hr0 (by
      rw [Real.norm_eq_abs, abs_of_nonneg hr0] at hr1; exact hr1)
    exact (h1.add h2).congr (fun N => by ring)
  refine Summable.of_norm_bounded hgeo (fun N => ?_)
  have hcoeff : ‖estermannCoeff q a N‖ ≤ (N : ℝ) + 1 := by
    rw [norm_estermannCoeff]
    have hsub : N.divisors ⊆ Finset.range (N + 1) := by
      intro d hd
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.divisor_le hd)
    have hcard : (N.divisors.card : ℝ) ≤ ((Finset.range (N + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    simpa using hcard
  have hexp : ‖Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ))‖ = r ^ N := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [hr, ← Real.exp_nat_mul]
    ring_nf
  rw [norm_mul, hexp]
  exact mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- **Additive orthogonality.**  The character average of the smoothed twisted divisor sums is
`q` times the smoothed divisor sum over the progression `N ≡ b (mod q)`. -/
theorem sum_twist_eq_progression (q : ℕ) [NeZero q] (b : ZMod q) {x : ℝ} (hx : 0 < x) :
    ∑ a : ZMod q, (ZMod.stdAddChar (-(a * b)) : ℂ) * estermannSmoothedSum q a x
      = (q : ℂ) * ∑' N : ℕ,
          (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
            Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)) := by
  classical
  have hsummable : ∀ a : ZMod q,
      Summable (fun N : ℕ => (ZMod.stdAddChar (-(a * b)) : ℂ) *
        (estermannCoeff q a N * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))) :=
    fun a => (summable_estermannSmoothedTerm q a hx).mul_left _
  have hswap : (∑ a : ZMod q, (ZMod.stdAddChar (-(a * b)) : ℂ) * estermannSmoothedSum q a x)
      = ∑' N : ℕ, ∑ a : ZMod q, (ZMod.stdAddChar (-(a * b)) : ℂ) *
          (estermannCoeff q a N * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ))) := by
    have hHS := hasSum_sum (fun (a : ZMod q) (_ : a ∈ Finset.univ) => (hsummable a).hasSum)
    rw [hHS.tsum_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [estermannSmoothedSum, ← tsum_mul_left]
  rw [hswap, ← tsum_mul_left]
  refine tsum_congr (fun N => ?_)
  have hchar : ∀ a : ZMod q, (ZMod.stdAddChar (-(a * b)) : ℂ) *
      (estermannCoeff q a N * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
      = ((N.divisors.card : ℂ) * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ))) *
        (ZMod.stdAddChar (a * ((N : ZMod q) - b)) : ℂ) := by
    intro a
    rw [estermannCoeff]
    have hadd : (ZMod.stdAddChar (a * ((N : ZMod q) - b)) : ℂ)
        = (ZMod.stdAddChar (-(a * b)) : ℂ) * (ZMod.stdAddChar (a * (N : ZMod q)) : ℂ) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [hadd]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hchar a), ← Finset.mul_sum]
  have hsum : (∑ a : ZMod q, (ZMod.stdAddChar (a * ((N : ZMod q) - b)) : ℂ))
      = if (N : ZMod q) - b = 0 then (q : ℂ) else 0 := sum_stdAddChar_mul q _
  rw [hsum]
  by_cases hNb : (N : ZMod q) = b
  · have h1 : (N : ZMod q) - b = 0 := sub_eq_zero.mpr hNb
    rw [if_pos h1, if_pos hNb]
    ring
  · have h1 : ¬ ((N : ZMod q) - b = 0) := fun h => hNb (sub_eq_zero.mp h)
    rw [if_neg h1, if_neg hNb]
    ring

end

end RHTower
