import GaloisForLFunctions.RHTower.DirichletCharacterCoprimePrimitiveProduct
import GaloisForLFunctions.RHTower.QuadraticJacobiSum
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Primitive twists by the quadratic character of a new odd prime. -/

noncomputable section

namespace QH

def J (q n : ℕ) : ℂ := ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

theorem quadraticCharacter_eq_J (p : RHTower.OddPrime) (n : ℕ) :
    RHTower.oddPrimeQuadraticCharacter p (n : ZMod p.1) = J p.1 n := by
  unfold J
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  simp [RHTower.oddPrimeQuadraticCharacter, legendreSym]

theorem twist_prim (f q : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f) (hξ : ξ.IsPrimitive)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqf : ¬ q ∣ f) :
    ∃ ψ : DirichletCharacter ℂ (f * q), ψ.IsPrimitive ∧ ψ ≠ 1 ∧
      ∀ n : ℕ, ψ (n : ZMod (f * q)) = ξ (n : ZMod f) * J q n := by
  let p : RHTower.OddPrime := ⟨q, hq, hq2⟩
  let η : DirichletCharacter ℂ q := RHTower.oddPrimeQuadraticCharacter p
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : NeZero (f * q) := ⟨mul_ne_zero (NeZero.ne f) hq.ne_zero⟩
  have hcop : f.Coprime q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqf).symm
  let hfL : f ∣ f * q := Nat.dvd_mul_right f q
  let hqL : q ∣ f * q := Nat.dvd_mul_left q f
  let ψ := ξ.changeLevel hfL * η.changeLevel hqL
  have hprim : ψ.IsPrimitive := RHTower.lifted_coprime_product_isPrimitive ξ η hcop hξ
    (RHTower.oddPrimeQuadraticCharacter_isPrimitive p)
  refine ⟨ψ, hprim, ?_, fun n => ?_⟩
  · intro he
    rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hprim
    have hlarge := hq.one_lt.trans_le (Nat.le_of_dvd (NeZero.pos (f * q)) hqL)
    exact (ne_of_lt hlarge) hprim
  · by_cases hu : IsUnit (n : ZMod (f * q))
    · obtain ⟨u, hu'⟩ := hu
      rw [show ψ = ξ.changeLevel hfL * η.changeLevel hqL from rfl, MulChar.mul_apply,
        ← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd,
        DirichletCharacter.changeLevel_eq_cast_of_dvd, hu',
        ZMod.cast_natCast hfL, ZMod.cast_natCast hqL]
      congr 1
      exact quadraticCharacter_eq_J p n
    · rw [MulChar.map_nonunit _ hu]
      have hc : ¬ n.Coprime (f * q) := fun h => hu ((ZMod.isUnit_iff_coprime n _).2 h)
      by_cases hf : n.Coprime f
      · have hnq : ¬ n.Coprime q := fun h => hc (Nat.Coprime.mul_right hf h)
        have hz : jacobiSym (n : ℤ) q = 0 := by
          rw [jacobiSym.eq_zero_iff_not_coprime]
          simpa [Int.gcd_natCast_natCast] using hnq
        simp [J, hz]
      · have hz : ξ (n : ZMod f) = 0 :=
          MulChar.map_nonunit _ (fun h => hf ((ZMod.isUnit_iff_coprime n _).1 h))
        simp [hz]

theorem twist_prim_exponent (f q i : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f)
    (hξ : ξ.IsPrimitive) (hq : q.Prime) (h2 : q ≠ 2) (hf : ¬ q ∣ f) (hi : i ≤ 1) :
    ∃ (M : ℕ) (ψ : DirichletCharacter ℂ M), M = f * q ^ i ∧ ψ.IsPrimitive ∧
      ∀ n : ℕ, ψ (n : ZMod M) = ξ (n : ZMod f) * J q n ^ i := by
  interval_cases i
  · exact ⟨f, ξ, by simp, hξ, fun n => by simp⟩
  · obtain ⟨ψ, hψ, -, hval⟩ := twist_prim f q ξ hξ hq h2 hf
    exact ⟨f * q, ψ, by simp, hψ, fun n => by simpa using hval n⟩

end QH
