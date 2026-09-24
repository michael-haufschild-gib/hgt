import GaloisForLFunctions.RHTower.EstermannPrimeProgression

/-!
# Scaled twists reduce the modulus

A twist `a` mod `q` that is divisible by `d`, where `d ∣ q`, is the same additive character as the
reduced twist `a/d` mod `q/d`, because `e((d m) N / (d q')) = e(m N / q')` exactly.  Writing
`d = gcd(a, q)` this is the reduction of an arbitrary residue twist to a unit twist of a smaller
modulus, which is what the Estermann main term `(γ − log x − 2 log q)/(qx)` is sensitive to: the
main term of a scaled twist is the main term of the reduced modulus, not of `q`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The standard additive character is invariant under simultaneously scaling the argument and the
modulus. -/
theorem stdAddChar_scale {q d q' : ℕ} [NeZero q] [NeZero q'] (hq : q = d * q') (j : ℤ) :
    ((ZMod.stdAddChar (((d * j : ℤ)) : ZMod q)) : ℂ)
      = ((ZMod.stdAddChar ((j : ℤ) : ZMod q')) : ℂ) := by
  subst hq
  have hd : d ≠ 0 := by
    intro h
    exact (NeZero.ne (d * q')) (by rw [h, zero_mul])
  have hdC : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hq'C : ((q' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q')
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

/-- A scaled twist has the same divisor coefficients as the reduced twist. -/
theorem estermannCoeff_scale {q d q' : ℕ} [NeZero q] [NeZero q'] (hq : q = d * q')
    (m : ℤ) (N : ℕ) :
    estermannCoeff q (((d * m : ℤ)) : ZMod q) N = estermannCoeff q' ((m : ℤ) : ZMod q') N := by
  have hL : (((d * m : ℤ)) : ZMod q) * ((N : ℕ) : ZMod q)
      = (((d * (m * N) : ℤ)) : ZMod q) := by push_cast; ring
  have hR : ((m : ℤ) : ZMod q') * ((N : ℕ) : ZMod q')
      = (((m * N : ℤ)) : ZMod q') := by push_cast; ring
  rw [estermannCoeff, estermannCoeff, hL, hR]
  congr 1
  exact stdAddChar_scale hq (m * N)

/-- **Scaled twists reduce the modulus.**  The smoothed twisted divisor sum at a twist divisible by
`d` is the smoothed twisted divisor sum at the reduced modulus. -/
theorem estermannSmoothedSum_scale {q d q' : ℕ} [NeZero q] [NeZero q'] (hq : q = d * q')
    (m : ℤ) (x : ℝ) :
    estermannSmoothedSum q (((d * m : ℤ)) : ZMod q) x
      = estermannSmoothedSum q' ((m : ℤ) : ZMod q') x := by
  rw [estermannSmoothedSum, estermannSmoothedSum]
  exact tsum_congr (fun N => by rw [estermannCoeff_scale hq m N])

end

end RHTower
