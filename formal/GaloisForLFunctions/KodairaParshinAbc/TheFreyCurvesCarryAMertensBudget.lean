import GaloisForLFunctions.KodairaParshinAbc.WeilBoundsForTheQuinticAndFreyCurves
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensBudgetOfAnEllipticCurveIsStrictHasse

/-!
# The Frey curves carry a Mertens budget

For an elliptic curve `E` over `F_p` with trace `a = p + 1 - #E(F_p)`, the Mertens row of
`1/Z_E` has a linear energy budget exactly under the strict Hasse bound `a² < 4p`
(`ArithmeticCorrespondencePositivity.ellipticMertens_budget_iff`).  Over a prime field the
Hasse bound is automatically strict: `a² = 4p` would make `p = (a/2)²` a square.

Hence every elliptic curve over `F_p`, `p` odd, has Mertens energy
`Σ_{m ≤ M} μ_E(m)²/p^m = 2 #E(F_p)² M / (4p - a²) + O(1)`, and in particular so has the reduction
of the Frey curve `y² = x(x-a)(x+b)` of a primitive triple at every odd prime `p ∤ ab(a+b)`.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

open GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- An integer square is never four times a prime. -/
theorem sq_ne_four_mul_prime {t : ℤ} {p : ℕ} (hp : p.Prime) : t ^ 2 ≠ 4 * (p : ℤ) := by
  intro h
  have h2 : (2 : ℤ) ∣ t := by
    have : (2 : ℤ) ∣ t ^ 2 := ⟨2 * p, by rw [h]; ring⟩
    exact Int.prime_two.dvd_of_dvd_pow this
  obtain ⟨s, rfl⟩ := h2
  have hs : s ^ 2 = (p : ℤ) := by linarith
  have hs' : s.natAbs ^ 2 = p := by
    have := congrArg Int.natAbs hs
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at this
  exact Nat.Prime.not_prime_pow (le_refl 2) (hs' ▸ hp)

/-- The trace of Frobenius `p + 1 - #W(F_p)` of a Weierstrass curve over `F_p`. -/
def frobeniusTrace {p : ℕ} (W : WeierstrassCurve (ZMod p)) : ℤ :=
  (p : ℤ) + 1 - Nat.card W.toAffine.Point

/-- **Hasse is strict over prime fields**: `a_p² < 4p` for every elliptic curve over `F_p`,
`p` odd. -/
theorem frobeniusTrace_sq_lt {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] :
    ((frobeniusTrace W : ℝ)) ^ 2 < 4 * p := by
  have h := RHTower.EllipticHasse.abs_natCard_point_sub_le W (by rwa [ZMod.ringChar_zmod_n])
  rw [ZMod.card] at h
  have habs : |(frobeniusTrace W : ℝ)| ≤ 2 * Real.sqrt p := by
    rw [frobeniusTrace]
    push_cast
    rw [abs_sub_comm]
    exact h
  have hle : ((frobeniusTrace W : ℝ)) ^ 2 ≤ 4 * p := by
    have h0 : 0 ≤ 2 * Real.sqrt p := by positivity
    calc ((frobeniusTrace W : ℝ)) ^ 2 = |(frobeniusTrace W : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * Real.sqrt p) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 4 * p := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  refine lt_of_le_of_ne hle fun heq => sq_ne_four_mul_prime hp.out (t := frobeniusTrace W) ?_
  exact_mod_cast heq

/-- **Every elliptic curve over `F_p` has a Mertens budget**: its Mertens energy is
`2 (p + 1 - a)² M / (4p - a²) + O(1)`. -/
theorem ellipticCurve_mertensBudget {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] :
    ∃ C : ℝ, ∀ M : ℕ,
      |ellipticMertensEnergy (frobeniusTrace W) p M -
          2 * ((p : ℝ) + 1 - frobeniusTrace W) ^ 2 * M / (4 * p - (frobeniusTrace W : ℝ) ^ 2)| ≤
        C :=
  abs_ellipticMertensEnergy_sub_le (by exact_mod_cast (Fact.out : p.Prime).pos)
    (frobeniusTrace_sq_lt hp2 W)

/-- **The Frey curves carry a Mertens budget** at every odd prime `p ∤ ab(a+b)`. -/
theorem freyCurve_mertensBudget {a b : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    ∃ C : ℝ, ∀ M : ℕ,
      |ellipticMertensEnergy (frobeniusTrace ((freyCurve a b).map (Int.castRingHom (ZMod p)))) p M -
          2 * ((p : ℝ) + 1 - frobeniusTrace ((freyCurve a b).map (Int.castRingHom (ZMod p)))) ^ 2 *
              M / (4 * p - (frobeniusTrace ((freyCurve a b).map
                (Int.castRingHom (ZMod p))) : ℝ) ^ 2)| ≤ C := by
  haveI := freyCurve_map_isElliptic hp2 habc
  exact ellipticCurve_mertensBudget hp2 _

end GaloisForLFunctions.KodairaParshinAbc
