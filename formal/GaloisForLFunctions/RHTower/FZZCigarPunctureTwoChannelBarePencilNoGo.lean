import GaloisForLFunctions.RHTower.FZZCigarPunctureGramDarkSelfEnergyClassification
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# FZZ puncture fixed two-channel bare-pencil no-go

A fixed two-channel interior matrix with a fixed nonzero dark coupling row has
at most one real dark eigenenergy.  The canonical dark vector gives an exact
two-equation classification, and adding the affine FZZ continuum condition adds
only the transverse Plücker minor.

Hardy's theorem in the corpus supplies two distinct positive real zeros of the
centered completed function.  Consequently no such fixed two-channel spectral
pencil can carry every positive `XiC` zero, unconditionally.  A viable FZZ
producer therefore needs genuine energy dependence beyond `A₀-EI`, a moving
dark coupling, or an infinite-dimensional dark sector.
-/

open Complex

namespace RHTower

noncomputable section

/-- Nonzero eigenvector of a fixed two-channel interior matrix lying in a fixed coupling kernel. -/
def FZZPunctureTwoChannelBareDarkEigenmode
    (E : ℝ) (a b c d p q : ℂ) : Prop :=
  (p ≠ 0 ∨ q ≠ 0) ∧
    ∃ x0 x1 : ℂ,
      (x0 ≠ 0 ∨ x1 ≠ 0) ∧
        p * x0 + q * x1 = 0 ∧
          a * x0 + b * x1 = (E : ℂ) * x0 ∧
            c * x0 + d * x1 = (E : ℂ) * x1

/-- Exact canonical-dark-vector classification of the fixed bare spectral pencil. -/
theorem fzzPunctureTwoChannelBareDarkEigenmode_iff
    (E : ℝ) (a b c d p q : ℂ) :
    FZZPunctureTwoChannelBareDarkEigenmode E a b c d p q ↔
      (p ≠ 0 ∨ q ≠ 0) ∧
        a * q - b * p = (E : ℂ) * q ∧
          c * q - d * p = -(E : ℂ) * p := by
  constructor
  · rintro ⟨hpq, x0, x1, hx, hrow, hfirst, hsecond⟩
    refine ⟨hpq, ?_, ?_⟩
    · rcases hx with hx0 | hx1
      · apply (mul_left_cancel₀ hx0)
        linear_combination q * hfirst - b * hrow
      · apply (mul_left_cancel₀ hx1)
        linear_combination -p * hfirst + a * hrow - (E : ℂ) * hrow
    · rcases hx with hx0 | hx1
      · apply (mul_left_cancel₀ hx0)
        linear_combination q * hsecond - d * hrow + (E : ℂ) * hrow
      · apply (mul_left_cancel₀ hx1)
        linear_combination -p * hsecond + c * hrow
  · rintro ⟨hpq, hfirst, hsecond⟩
    refine ⟨hpq, q, -p, ?_, ?_, ?_, ?_⟩
    · rcases hpq with hp | hq
      · exact Or.inr (neg_ne_zero.mpr hp)
      · exact Or.inl hq
    · ring
    · linear_combination hfirst
    · linear_combination hsecond

/-- A fixed one-dimensional dark sector can carry at most one bare eigenenergy. -/
theorem fzzPunctureTwoChannelBareDarkEigenmode_energy_unique
    {E F : ℝ} {a b c d p q : ℂ}
    (hE : FZZPunctureTwoChannelBareDarkEigenmode E a b c d p q)
    (hF : FZZPunctureTwoChannelBareDarkEigenmode F a b c d p q) :
    E = F := by
  have hEc := (fzzPunctureTwoChannelBareDarkEigenmode_iff E a b c d p q).mp hE
  have hFc := (fzzPunctureTwoChannelBareDarkEigenmode_iff F a b c d p q).mp hF
  rcases hEc.1 with hp | hq
  · have hcast : (E : ℂ) = (F : ℂ) := by
      apply (mul_right_cancel₀ hp)
      have hneg : -(E : ℂ) * p = -(F : ℂ) * p :=
        hEc.2.2.symm.trans hFc.2.2
      apply neg_injective
      simpa only [neg_mul] using hneg
    exact_mod_cast hcast
  · have hcast : (E : ℂ) = (F : ℂ) := by
      apply (mul_right_cancel₀ hq)
      exact hEc.2.1.symm.trans hFc.2.1
    exact_mod_cast hcast

/-- A bare dark eigenmode together with its coupling-sourced affine continuum point mode. -/
def FZZPunctureTwoChannelBarePencilPointMode
    (E : ℝ) (a b c d p q d0 d1 : ℂ) : Prop :=
  FZZPunctureTwoChannelBareDarkEigenmode E a b c d p q ∧
    FZZPunctureTwoChannelInternalRowPointMode E p q p q d0 d1

/-- Exact bare-pencil FZZ occurrence law: two interior equations plus transverse slope. -/
theorem fzzPunctureTwoChannelBarePencilPointMode_iff
    (E : ℝ) (a b c d p q d0 d1 : ℂ) :
    FZZPunctureTwoChannelBarePencilPointMode E a b c d p q d0 d1 ↔
      (p ≠ 0 ∨ q ≠ 0) ∧
        a * q - b * p = (E : ℂ) * q ∧
          c * q - d * p = -(E : ℂ) * p ∧
            q * d0 - p * d1 ≠ 0 := by
  rw [FZZPunctureTwoChannelBarePencilPointMode,
    fzzPunctureTwoChannelBareDarkEigenmode_iff,
    fzzPunctureCouplingSourcedTwoChannelPointMode_iff]
  aesop

/-- Fixed two-channel bare-pencil point modes have a unique real energy. -/
theorem fzzPunctureTwoChannelBarePencilPointMode_energy_unique
    {E F : ℝ} {a b c d p q d0 d1 : ℂ}
    (hE : FZZPunctureTwoChannelBarePencilPointMode E a b c d p q d0 d1)
    (hF : FZZPunctureTwoChannelBarePencilPointMode F a b c d p q d0 d1) :
    E = F :=
  fzzPunctureTwoChannelBareDarkEigenmode_energy_unique hE.1 hF.1

/-- Proposed completeness of one fixed two-channel bare pencil for positive real `XiC` zeros. -/
def FZZPunctureTwoChannelBarePencilXiComplete
    (a b c d p q d0 d1 : ℂ) : Prop :=
  ∀ E : ℝ,
    0 < E → XiC (E : ℂ) = 0 →
      FZZPunctureTwoChannelBarePencilPointMode E a b c d p q d0 d1

/-- No fixed two-channel bare pencil can cover even the two unconditional Hardy zeros. -/
theorem not_fzzPunctureTwoChannelBarePencilXiComplete
    (a b c d p q d0 d1 : ℂ) :
    ¬ FZZPunctureTwoChannelBarePencilXiComplete a b c d p q d0 d1 := by
  intro hcomplete
  obtain ⟨E, F, hEpos, hFpos, hEF, hEz, hFz⟩ :=
    exists_two_distinct_positive_real_XiC_zeros
  have hEmode := hcomplete E hEpos hEz
  have hFmode := hcomplete F hFpos hFz
  exact hEF (fzzPunctureTwoChannelBarePencilPointMode_energy_unique hEmode hFmode)

end

end RHTower
