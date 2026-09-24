import GaloisForLFunctions.RHTower.EstermannProgressionOrthogonality

/-!
# The smoothed divisor sum in a progression to a prime modulus

Additive orthogonality writes `q · ∑_{N ≡ b (q)} d(N) e^{-Nx}` as a character average of the
smoothed twisted divisor sums.  For a prime modulus every nonzero twist is a unit, so the average
splits into the untwisted term `a = 0` and a weighted sum over the units.  Since the main term of
the twisted sum does not depend on the twist, the unit part contributes
`(∑_a w(a)) · (γ − log x − 2 log q)/(qx)` up to `O(x^{-1/2})`, and for a nonzero residue `b` the
weight sum is the Ramanujan sum `c_q(b) = −1`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Weighted twist expansion, main term retained.**  Because the main term is independent of the
twist, an arbitrary weight on the units reproduces it with the factor `∑_a w(a)`. -/
theorem exists_bound_norm_estermann_weighted (q : ℕ) [NeZero q] (w : (ZMod q)ˣ → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(∑ a : (ZMod q)ˣ, w a * estermannSmoothedSum q (a : ZMod q) x)
          - (∑ a : (ZMod q)ˣ, w a) * estermannSmoothedMain q x‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  classical
  choose C hC hbound using
    fun a : (ZMod q)ˣ => exists_bound_norm_estermannSmoothedSum_sub_main q a
  refine ⟨∑ a : (ZMod q)ˣ, ‖w a‖ * C a, ?_, fun x hx => ?_⟩
  · exact Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (hC a))
  · have hsplit : (∑ a : (ZMod q)ˣ, w a * estermannSmoothedSum q (a : ZMod q) x)
        - (∑ a : (ZMod q)ˣ, w a) * estermannSmoothedMain q x
        = ∑ a : (ZMod q)ˣ, w a *
            (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hsplit]
    have hterm : ∀ a : (ZMod q)ˣ,
        ‖w a * (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x)‖
          ≤ (‖w a‖ * C a) * x ^ (-(1 / 2 : ℝ)) := by
      intro a
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hbound a x hx) (norm_nonneg _)
    calc ‖∑ a : (ZMod q)ˣ, w a *
            (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x)‖
        ≤ ∑ a : (ZMod q)ˣ, ‖w a *
            (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ a : (ZMod q)ˣ, (‖w a‖ * C a) * x ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_le_sum (fun a _ => hterm a)
      _ = (∑ a : (ZMod q)ˣ, ‖w a‖ * C a) * x ^ (-(1 / 2 : ℝ)) := by
          rw [← Finset.sum_mul]

/-- The untwisted smoothed divisor sum is the zero twist. -/
theorem estermannSmoothedSum_zero (q : ℕ) [NeZero q] (x : ℝ) :
    estermannSmoothedSum q (0 : ZMod q) x
      = ∑' N : ℕ, ((N.divisors.card : ℂ)) * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)) := by
  rw [estermannSmoothedSum]
  refine tsum_congr (fun N => ?_)
  have h0 : ((ZMod.stdAddChar (0 : ZMod q)) : ℂ) = 1 := by simp
  rw [estermannCoeff, zero_mul, h0, mul_one]

/-- For a prime modulus the residue sum splits into the zero term and the unit sum. -/
private theorem sum_zmod_eq_add_sum_units {q : ℕ} [Fact q.Prime] (f : ZMod q → ℂ) :
    ∑ a : ZMod q, f a = f 0 + ∑ a : (ZMod q)ˣ, f (a : ZMod q) := by
  classical
  have hinj : ∀ u ∈ (Finset.univ : Finset (ZMod q)ˣ), ∀ v ∈ (Finset.univ : Finset (ZMod q)ˣ),
      (u : ZMod q) = (v : ZMod q) → u = v := fun u _ v _ h => Units.ext h
  have himg : (Finset.univ : Finset (ZMod q)ˣ).image (fun u : (ZMod q)ˣ => (u : ZMod q))
      = (Finset.univ : Finset (ZMod q)).erase 0 := by
    ext a
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨u, -, rfl⟩
      exact u.ne_zero
    · intro ha
      exact ⟨Units.mk0 a ha, rfl⟩
  have h1 : ∑ a : (ZMod q)ˣ, f (a : ZMod q)
      = ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0, f a := by
    rw [← himg, Finset.sum_image hinj]
  rw [h1]
  exact (Finset.add_sum_erase _ f (Finset.mem_univ 0)).symm

/-- **The smoothed divisor sum in a progression to a prime modulus.**  For `b ≢ 0 (mod q)`,

`q ∑_{N ≡ b (q)} d(N) e^{-Nx} = ∑_N d(N) e^{-Nx} − (γ − log x − 2 log q)/(qx) + O(x^{-1/2})`.

The subtracted term is the twist-independent main term weighted by the Ramanujan sum
`c_q(b) = −1`. -/
theorem exists_bound_norm_estermann_prime_progression (q : ℕ) [hq : Fact q.Prime]
    (b : ZMod q) (hb : b ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
            Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
          - ((∑' N : ℕ, ((N.divisors.card : ℂ)) * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
              - estermannSmoothedMain q x)‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  haveI : NeZero q := ⟨hq.out.pos.ne'⟩
  obtain ⟨C, hC, hbound⟩ := exists_bound_norm_estermann_weighted q
    (fun a : (ZMod q)ˣ => ((ZMod.stdAddChar (-((a : ZMod q) * b))) : ℂ))
  refine ⟨C, hC, fun x hx => ?_⟩
  have horth := sum_twist_eq_progression q b hx
  have hsplit := sum_zmod_eq_add_sum_units
    (fun a : ZMod q => ((ZMod.stdAddChar (-(a * b))) : ℂ) * estermannSmoothedSum q a x)
  have hzero : ((ZMod.stdAddChar (0 : ZMod q)) : ℂ) = 1 := by simp
  have hall : (∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ)) = 0 := by
    have h := sum_stdAddChar_mul q (-b)
    rw [if_neg (by simpa using hb)] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun a _ => by rw [show a * (-b) = -(a * b) by ring])
  have hw : (∑ a : (ZMod q)ˣ, ((ZMod.stdAddChar (-((a : ZMod q) * b))) : ℂ)) = -1 := by
    have hsp := sum_zmod_eq_add_sum_units (fun a : ZMod q => ((ZMod.stdAddChar (-(a * b))) : ℂ))
    rw [hall] at hsp
    simp only [zero_mul, neg_zero] at hsp
    rw [hzero] at hsp
    linear_combination -hsp
  have hS0 : ((ZMod.stdAddChar (-((0 : ZMod q) * b))) : ℂ) * estermannSmoothedSum q 0 x
      = ∑' N : ℕ, ((N.divisors.card : ℂ)) * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)) := by
    rw [zero_mul, neg_zero, hzero, one_mul, estermannSmoothedSum_zero]
  have hkey := hbound x hx
  rw [hw] at hkey
  have htarget : (q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
        Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
        - ((∑' N : ℕ, ((N.divisors.card : ℂ)) * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
            - estermannSmoothedMain q x)
      = (∑ a : (ZMod q)ˣ, ((ZMod.stdAddChar (-((a : ZMod q) * b))) : ℂ) *
          estermannSmoothedSum q (a : ZMod q) x) - (-1) * estermannSmoothedMain q x := by
    rw [← horth, hsplit, hS0]
    ring
  rw [htarget]
  exact hkey


end

end RHTower
