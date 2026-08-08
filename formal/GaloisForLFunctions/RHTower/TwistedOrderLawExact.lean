import GaloisForLFunctions.RHTower.TwistedMertensLittlewood
import GaloisForLFunctions.RHTower.DirichletCompletedLConjugate
import GaloisForLFunctions.HTGeometry.LogOrderLimsupBound

/-!
# The exact twisted mixed additive zero-abscissa law

The zero-abscissa Littlewood estimate closes the upper half of the companion order law, so for every
nontrivial primitive Dirichlet character the mixed even additive convolution of the twisted Mertens
function has the exact logarithmic order

`Λ_{χ,k} = 2k(1 + Θ_χ) - 1`     (`limsup_mertens_eq_zeroAbscissa`).

Two consequences are recorded.  Since `Θ_χ ≥ 1/2` unconditionally, every mixed even order has
near-critical **positive** excursions
`C_{χ,k}(N) ≥ (N+1)^{3k-1-ε}` at infinitely many `N`
(`frequently_rpow_le_twistedMertensEvenConvolution`).  And the exact law converts the generalized
Riemann hypothesis for `L(·,χ)` into the single arithmetic identity `Λ_{χ,k} = 3k - 1`
(`dirichletGRH_iff_limsup_mertens_eq`).

The reflection `Θ_χ = 1/2 ↔ GRH_χ` uses the functional equation together with conjugation
symmetry, which sends a zero of `L(·,χ)` at `ρ` to a zero at `conj (1 - ρ)`.
-/

open Complex Filter
open scoped ArithmeticFunction.Moebius LSeries.notation Topology BigOperators

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Unconditional near-critical positive excursions `(D4a)`.** -/
theorem frequently_rpow_le_twistedMertensEvenConvolution {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ M : ℕ in atTop,
      ((M : ℝ) + 1) ^ (3 * ((j : ℝ) + 1) - 1 - ε)
        ≤ (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set α : ℝ := 3 * ((j : ℝ) + 1) - 1 - ε with hαdef
  set lam : ℝ := max α 0 with hlamdef
  have hlam0 : 0 ≤ lam := le_max_right _ _
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hkR : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by linarith
  have hev : ∀ᶠ M : ℕ in atTop,
      (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re
        ≤ ((M : ℝ) + 1) ^ lam := by
    filter_upwards [hcon] with M hM
    have hbase : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) M
      linarith
    refine le_trans (le_of_lt (not_le.mp hM)) ?_
    exact Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
  obtain ⟨C, hC0, hCbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_global_subpower_of_eventually_le hlam0 hev
  have hΘ := half_le_zeroAbscissa hχ hprim
  have hshift : (lam + 1) / (2 * ((j : ℝ) + 1)) - 1 < zeroAbscissa χ := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hkR]
    rcases le_or_gt α 0 with h | h
    · rw [hlamdef, max_eq_right h]
      nlinarith
    · rw [hlamdef, max_eq_left h.le, hαdef]
      nlinarith
  have hmax : max ((lam + 1) / (2 * ((j : ℝ) + 1)) - 1) 0 < zeroAbscissa χ :=
    max_lt hshift (zeroAbscissa_pos hχ hprim)
  obtain ⟨ρ, hzero, hρre⟩ := exists_zero_lt_re hχ hprim hmax
  have hpos : 0 < ρ.re := lt_of_le_of_lt (le_max_right _ _) hρre
  have hlt : (lam + 1) / (2 * (((j + 1 : ℕ) : ℝ))) - 1 < ρ.re := by
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact lt_of_le_of_lt (le_max_left _ _) hρre
  exact not_mertensSubpower_of_LFunction_eq_zero hχ (Nat.succ_pos j) hlam0 hC0 hzero hpos hlt
    hCbound

/-! ### The generalized Riemann hypothesis form -/

/-- The generalized Riemann hypothesis for a single Dirichlet `L`-function. -/
def DirichletGRH (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2

omit [NeZero N] in
theorem gammaFactor_ne_zero_of_re_pos {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hev | hod
  · rw [hev.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hod.gammaFactor_def]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.one_re]
    linarith

theorem completedLFunction_eq_zero_of_LFunction_eq_zero {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hpos : 0 < ρ.re) :
    DirichletCharacter.completedLFunction χ ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hρ0)
  rw [hzero] at hdiv
  have hγ : DirichletCharacter.gammaFactor χ ρ ≠ 0 := gammaFactor_ne_zero_of_re_pos hpos
  field_simp at hdiv
  simpa using hdiv.symm

/-- **Reflection of a zero across the critical line.**  Combining the functional equation with
conjugation symmetry sends a zero of `L(·,χ)` in the open strip to a zero at `conj (1 - ρ)`. -/
theorem LFunction_eq_zero_conj_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hpos : 0 < ρ.re) (hlt : ρ.re < 1) :
    DirichletCharacter.LFunction χ ((starRingEnd ℂ) (1 - ρ)) = 0 := by
  have hΛ : DirichletCharacter.completedLFunction χ ρ = 0 :=
    completedLFunction_eq_zero_of_LFunction_eq_zero hzero hpos
  have hFE := hprim.completedLFunction_one_sub (1 - ρ)
  rw [show (1 : ℂ) - (1 - ρ) = ρ by ring, hΛ] at hFE
  have hNne : ((N : ℂ)) ^ (((1 : ℂ) - ρ) - 1 / 2) ≠ 0 := by
    refine fun h => ?_
    rw [Complex.cpow_eq_zero_iff] at h
    exact (Nat.cast_ne_zero.mpr (NeZero.ne N)) h.1
  have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ (1 - ρ) = 0 := by
    rcases mul_eq_zero.mp hFE.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hNne
      · exact absurd h' (rootNumber_ne_zero hprim)
    · exact h
  have hconj := conj_completedLFunction hχ ((starRingEnd ℂ) (1 - ρ))
  rw [Complex.conj_conj, hΛinv] at hconj
  have hzero2 : DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) (1 - ρ)) = 0 := by
    have hc := congrArg (starRingEnd ℂ) hconj
    simpa using hc
  have hre : ((starRingEnd ℂ) (1 - ρ)).re = 1 - ρ.re := by simp
  have hposConj : 0 < ((starRingEnd ℂ) (1 - ρ)).re := by rw [hre]; linarith
  have hne0 : (starRingEnd ℂ) (1 - ρ) ≠ 0 := by
    intro h
    rw [h] at hposConj
    simp at hposConj
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ
    ((starRingEnd ℂ) (1 - ρ)) (Or.inl hne0)
  rw [hdiv, hzero2, zero_div]

theorem zeroAbscissa_eq_half_iff_dirichletGRH {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    zeroAbscissa χ = 1 / 2 ↔ DirichletGRH χ := by
  constructor
  · intro h ρ hzero hpos hlt
    have hupper : ρ.re ≤ 1 / 2 := by
      rw [← h]
      exact re_le_zeroAbscissa hχ hzero
    have hrefl := LFunction_eq_zero_conj_one_sub hχ hprim hzero hpos hlt
    have hre : ((starRingEnd ℂ) (1 - ρ)).re = 1 - ρ.re := by simp
    have hle := re_le_zeroAbscissa hχ hrefl
    rw [hre, h] at hle
    linarith
  · intro hGRH
    refine le_antisymm (csSup_le (zeroReSet_nonempty hχ hprim) fun x hx => ?_)
      (half_le_zeroAbscissa hχ hprim)
    obtain ⟨ρ, hzero, rfl⟩ := hx
    rcases le_or_gt ρ.re 0 with h | h
    · linarith
    · have hlt : ρ.re < 1 := by
        by_contra hcon
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
          (not_lt.mp hcon) hzero
      exact le_of_eq (hGRH ρ hzero h hlt)

/-- **The GRH form `(D4)`.**  For one, hence every, `k ≥ 1`, the generalized Riemann hypothesis for
`L(·,χ)` is equivalent to the mixed even additive order being exactly `3k - 1`. -/
theorem dirichletGRH_iff_limsup_mertens_eq {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (j : ℕ) :
    DirichletGRH χ ↔
      Filter.limsup
        (fun M => Real.log
            (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
          / Real.log ((M : ℝ) + 1)) atTop
        = 3 * ((j : ℝ) + 1) - 1 := by
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [limsup_mertens_eq_zeroAbscissa hχ hprim]
  rw [← zeroAbscissa_eq_half_iff_dirichletGRH hχ hprim]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have hc : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by linarith
    nlinarith [h]

end RHTower
