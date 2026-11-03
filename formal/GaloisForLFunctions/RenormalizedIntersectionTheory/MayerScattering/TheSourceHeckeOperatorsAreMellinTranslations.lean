import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheHeckeEquivariantCompletion
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheEisensteinPeriodIsAHeckeEigenfunctionForEveryPrime

/-!
# Source Hecke operators are Mellin translations, for every prime

For every prime `p` the source Hecke operator `T_{p,s}` (the `p + 1`-cone operator of
`lewisHeckeOperator`) minus the identity is the Mellin translation `F_pH = √p H(· + log p)`:

* on completed periods `Φ_H(s, a)` (`lewisHeckeOperator_windowMellinPeriod`):
  `T_{p,s}Φ_H − Φ_H = Φ_{F_pH}` across `0 < Re s < ½`;
* on the completed resonant space (`windowResonanceMap_heckePull_intertwines`): the coordinate of
  `F_pH` at a resonance `s` is the coordinate of `H` times the eigenvalue `p^{1−2s}` of `T_{p,s} − Id`
  on the resonant period `ψ_s` — the Hecke multiplier `D_p` of the completion.

At `p = 2` the cone operator is the source operator `T₂` (`lewisHeckeOperator_two`).
-/

noncomputable section
open Complex
open GaloisForLFunctions CohomologyOfWindowsOfSpecZ ArithmeticPolarization WindowTowerOfSpecZ

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

variable {p : ℕ} [hp : Fact p.Prime]

/-- **`T_p − Id` is the Mellin translation on completed periods**:
`T_{p,s}Φ_H − Φ_H = Φ_{F_pH}`, every prime `p`, `0 < Re s < ½`. -/
theorem lewisHeckeOperator_windowMellinPeriod (H : ℝ → ℝ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 / 2) {a : ℝ} (ha : 0 < a) :
    lewisHeckeOperator p s (windowMellinPeriod H s) a - windowMellinPeriod H s a =
      windowMellinPeriod (heckePull p H) s a := by
  have he := eisensteinLewisPeriod_lewisHecke (p := p) hs0 hs1 ha
  have hpull := tr_heckePull H hp.out.one_lt.le (2 * s)
  unfold windowMellinPeriod
  rw [lewisHeckeOperator_const_mul, he, hpull]
  ring

/-- **The window pull and the source operator share the eigenvalue on each resonance line**:
`𝓦(F_pH)_s ψ_s(a) = 𝓦(H)_s (T_{p,s} − Id)ψ_s(a)`; both act by `p^{1−2s}`. -/
theorem windowResonanceMap_heckePull_intertwines {A : ℝ} (H : windowTests A)
    (s : upperMayerResonances) {a : ℝ} (ha : 0 < a) :
    windowResonanceMap (A + Real.log p) (heckePullTest hp.out.one_lt.le H) s *
        resonantLewisPeriod s.1 a =
      windowResonanceMap A H s *
        (lewisHeckeOperator p s.1 (fun x => resonantLewisPeriod s.1 x) a -
          resonantLewisPeriod s.1 a) := by
  rw [windowResonanceMap_heckePull, resonantLewisPeriod_lewisHecke s.2.2 ha]
  change (p : ℂ) ^ (1 - 2 * s.1) * windowResonanceMap A H s * resonantLewisPeriod s.1 a = _
  ring

omit hp in
/-- The four cones of determinant two. -/
theorem heckeSet_two :
    heckeSet 2 = {(2, 0, 0, 1), (1, 0, 0, 2), (1, 1, 0, 2), (2, 0, 1, 1)} := by
  ext ⟨a, b, c, d⟩
  simp only [heckeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq, Nat.cast_ofNat]
  constructor
  · rintro ⟨⟨⟨ha0, ha2⟩, ⟨hb0, hb2⟩, ⟨hc0, hc2⟩, ⟨hd0, hd2⟩⟩, hM⟩
    have hca := hM.c_lt
    have hbd := hM.b_lt
    have hdet := hM.det
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> omega
  · rintro (h | h | h | h) <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;>
      exact ⟨by norm_num, ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

omit hp in
/-- **At `p = 2` the cone operator is the source operator `T₂`.** -/
theorem lewisHeckeOperator_two (s : ℂ) (f : ℝ → ℂ) (a : ℝ) :
    lewisHeckeOperator 2 s f a = lewisHeckeT2 s f a := by
  rw [lewisHeckeOperator, heckeSet_two, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, lewisHeckeT2]
  simp only [Int.cast_ofNat, Int.cast_one, Int.cast_zero, zero_mul, zero_add, one_mul, add_zero,
    Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_ofNat, mul_comm (2 : ℝ) a, div_one]
  ring

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
