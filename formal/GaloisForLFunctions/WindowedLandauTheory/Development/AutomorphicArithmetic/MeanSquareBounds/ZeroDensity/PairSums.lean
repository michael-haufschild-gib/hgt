import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.ZeroDensity.Definitions
import GaloisForLFunctions.RHTower.DirichletCharacterPartialSumBound

/-! Orthogonality bounds for two distinct primitive characters. -/

open Complex Finset

noncomputable section

namespace QH.ZeroDensity

scoped instance (p p' : PC) : NeZero ((p.1 + 1) * (p'.1 + 1)) := ⟨by positivity⟩

def mulLevel (p p' : PC) : DirichletCharacter ℂ ((p.1 + 1) * (p'.1 + 1)) :=
  DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2 *
    (DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2)⁻¹

theorem mulLevel_ne_one (p p' : PC) (hp : p.2.IsPrimitive) (hp' : p'.2.IsPrimitive) (hne : p ≠ p') :
    mulLevel p p' ≠ 1 := by
  intro h
  have h1 := mul_inv_eq_one.mp h
  have hc := congrArg DirichletCharacter.conductor h1
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    hp, hp'] at hc
  obtain ⟨N, χ⟩ := p
  obtain ⟨N', χ'⟩ := p'
  simp only [add_left_inj] at hc
  subst hc
  apply hne
  have := DirichletCharacter.changeLevel_injective (dvd_mul_right (N + 1) (N + 1)) h1
  exact congrArg (Sigma.mk N) this

theorem mulLevel_apply (p p' : PC) (n : ℕ) :
    mulLevel p p' (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n * (starRingEnd ℂ) (cv p' n) := by
  by_cases hu : IsUnit (n : ZMod ((p.1 + 1) * (p'.1 + 1)))
  · obtain ⟨u, hu⟩ := hu
    have e1 : DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_right _ _)]
      rfl
    have e2 : DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p' n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_left _ _)]
      rfl
    have hn : ‖DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1)))‖ = 1 := by
      rw [← hu]
      exact DirichletCharacter.unit_norm_eq_one _ u
    unfold mulLevel
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', e1, Complex.inv_eq_conj hn, e2]
  · rw [MulChar.map_nonunit _ hu]
    rw [ZMod.isUnit_iff_coprime] at hu
    by_cases h1 : n.Coprime (p.1 + 1)
    · have h2 : ¬ n.Coprime (p'.1 + 1) := fun h2 => hu (Nat.Coprime.mul_right h1 h2)
      have h3 : cv p' n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, map_zero, mul_zero]
    · have h3 : cv p n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, zero_mul]

theorem pair_sum_bound : PairSum := by
  intro p p' hp hp' hne M
  have h := RHTower.norm_dirichletCharacter_sum_range_le (mulLevel p p') (mulLevel_ne_one p p' hp hp' hne) M
  simpa only [mulLevel_apply] using h

end QH.ZeroDensity
