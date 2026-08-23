import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff

/-!
# Vaughan's identity

Truncating `Λ` at `U` and `μ` at `V` and writing `−ζ'/ζ` as
`F − ζFG − ζ'G + (−ζ'/ζ − F)(1 − ζG)` is a ring identity in arithmetic functions once
`Λ ∗ ζ = log` is known.  Above `U` the first term vanishes, leaving one type-I sum, one triple
convolution, and a type-II bilinear form whose second variable is supported above `V`.
-/

namespace RHTower.Sieve

open ArithmeticFunction

noncomputable section

/-- The truncation of an arithmetic function to arguments at most `U`. -/
def truncAF (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

@[simp] theorem truncAF_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncAF f U n = if n ≤ U then f n else 0 := rfl

theorem truncAF_apply_of_gt {f : ArithmeticFunction ℝ} {U n : ℕ} (h : U < n) :
    truncAF f U n = 0 := by
  rw [truncAF_apply, if_neg (by omega)]

/-- **Vaughan's identity**, as an identity of arithmetic functions. -/
theorem vaughan_identity (U V : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ)
      = truncAF vonMangoldt U
        - (zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
            * truncAF (moebius : ArithmeticFunction ℝ) V
        + ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V
        + (vonMangoldt - truncAF vonMangoldt U)
            * (1 - (zeta : ArithmeticFunction ℝ)
                * truncAF (moebius : ArithmeticFunction ℝ) V) := by
  have hkey : (vonMangoldt : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ)
      = ArithmeticFunction.log := vonMangoldt_mul_zeta
  linear_combination (truncAF (moebius : ArithmeticFunction ℝ) V) * hkey

/-- **Vaughan's identity above the truncation.**  The first term of the identity drops out. -/
theorem vaughan_apply_of_gt {U V n : ℕ} (hn : U < n) :
    (vonMangoldt : ArithmeticFunction ℝ) n
      = -((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
            * truncAF (moebius : ArithmeticFunction ℝ) V) n
        + (ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n
        + ((vonMangoldt - truncAF vonMangoldt U)
            * (1 - (zeta : ArithmeticFunction ℝ)
                * truncAF (moebius : ArithmeticFunction ℝ) V)) n := by
  have h := congrArg (fun g : ArithmeticFunction ℝ => g n) (vaughan_identity U V)
  have hfull : (truncAF vonMangoldt U
        - (zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
            * truncAF (moebius : ArithmeticFunction ℝ) V
        + ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V
        + (vonMangoldt - truncAF vonMangoldt U)
            * (1 - (zeta : ArithmeticFunction ℝ)
                * truncAF (moebius : ArithmeticFunction ℝ) V)) n
      = truncAF vonMangoldt U n
        - ((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
            * truncAF (moebius : ArithmeticFunction ℝ) V) n
        + (ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n
        + ((vonMangoldt - truncAF vonMangoldt U)
            * (1 - (zeta : ArithmeticFunction ℝ)
                * truncAF (moebius : ArithmeticFunction ℝ) V)) n := rfl
  rw [hfull, truncAF_apply_of_gt hn] at h
  linarith [h]

/-- The type-II second factor is supported above `V`. -/
theorem one_sub_zeta_mul_truncAF_moebius_apply_eq_zero {V k : ℕ} (hk : 1 ≤ k) (hkV : k ≤ V) :
    ((1 : ArithmeticFunction ℝ) - (zeta : ArithmeticFunction ℝ)
        * truncAF (moebius : ArithmeticFunction ℝ) V) k = 0 := by
  have hconv : ((zeta : ArithmeticFunction ℝ)
      * truncAF (moebius : ArithmeticFunction ℝ) V) k
      = ∑ i ∈ k.divisors, truncAF (moebius : ArithmeticFunction ℝ) V i :=
    coe_zeta_mul_apply
  have hsame : ∑ i ∈ k.divisors, truncAF (moebius : ArithmeticFunction ℝ) V i
      = ∑ i ∈ k.divisors, ((moebius : ArithmeticFunction ℝ)) i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hile : i ≤ k := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hi)
    rw [truncAF_apply, if_pos (by omega)]
  have hmu : ∑ i ∈ k.divisors, ((moebius : ArithmeticFunction ℝ)) i
      = ((1 : ArithmeticFunction ℝ)) k := by
    rw [← coe_mul_zeta_apply (f := (moebius : ArithmeticFunction ℝ)) (x := k),
      coe_moebius_mul_coe_zeta]
  have hsub : ((1 : ArithmeticFunction ℝ) - (zeta : ArithmeticFunction ℝ)
        * truncAF (moebius : ArithmeticFunction ℝ) V) k
      = ((1 : ArithmeticFunction ℝ)) k
        - ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) V) k := rfl
  rw [hsub, hconv, hsame, hmu, sub_self]

end

end RHTower.Sieve
