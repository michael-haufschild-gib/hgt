import GaloisForLFunctions.RHTower.FZZCigarPunctureL2DilationNoGo
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDampingSemigroup

/-!
# Regular rank-one occurrence no-go for the FZZ puncture

Standard dilation has continuous spectrum, so the next minimal FZZ occurrence model is a rank-one
Friedrichs coupling. This file solves its local embedded-mode equation exactly for a unit box form
factor around arbitrary target energy `E`.

If the form factor is nonzero at `E`, every formal solution contains a `1 / (x - E)` pole. Its
squared norm has a nonintegrable inverse-square singularity, forcing coupling coefficient and state
to vanish. Thus even target-adapted regular rank-one coupling cannot complete the FZZ divisor.

The obstruction is sharp. Multiplying form factor by `(x - E)` cancels pole and produces an
explicit nonzero `L²` formal state. Hence viable embedded occurrence requires a source-derived
node at target energy or a genuinely singular/non-rank-one mechanism. Because fitting such nodes
to Xi ordinates would merely feed zeros into operator, remaining FZZ problem is deriving nodal
set coefficient-faithfully from winding-condensate dynamics.

The general Fermi-golden-rule mechanism is classical. Exact FZZ-puncture specialization and its
sharp nodal survivor are the new route statement.

`[NEW] [NO-GO] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Unit regular continuum form factor on one energy interval above target. -/
def fzzPunctureBoxFormFactor (E x : ℝ) : ℂ :=
  (Ioo E (E + 1)).indicator (fun _ => (1 : ℂ)) x

theorem fzzPunctureBoxFormFactor_memLp (E : ℝ) :
    MemLp (fzzPunctureBoxFormFactor E) 2 volume := by
  exact memLp_indicator_const (μ := volume) 2 measurableSet_Ioo (1 : ℂ)
    (Or.inr (by simp))

/-- Representative-level continuum equation forced by a rank-one eigenvalue equation. -/
def fzzPunctureBoxRankOneEigenEquation
    (E : ℝ) (alpha : ℂ) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 volume ∧
    ∀ᵐ x : ℝ ∂volume,
      (((x - E : ℝ) : ℂ) * f x) + alpha * fzzPunctureBoxFormFactor E x = 0

/-- Nonzero regular continuum coefficient would create forbidden inverse-square pole. -/
theorem fzzPunctureBoxRankOneEigenEquation_alpha_eq_zero
    (E : ℝ) (alpha : ℂ) (f : ℝ → ℂ)
    (h : fzzPunctureBoxRankOneEigenEquation E alpha f) :
    alpha = 0 := by
  rcases h with ⟨hf, heq⟩
  by_contra halpha
  have halphaNorm : 0 < ‖alpha‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr halpha)
  have hfint : Integrable (fun x : ℝ => ‖f x‖ ^ 2) :=
    hf.integrable_norm_pow (by norm_num)
  have heqRestricted :
      (fun x : ℝ => ‖f x‖ ^ 2) =ᵐ[volume.restrict (Ioo E (E + 1))]
        (fun x : ℝ => ‖alpha‖ ^ 2 * (x - E) ^ (-2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae heq]
      with x hx hxeq
    have hx0 : 0 < x - E := sub_pos.mpr hx.1
    have hden : (((x - E : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx0)
    have hfx : f x = -alpha / ((x - E : ℝ) : ℂ) := by
      apply (eq_div_iff hden).2
      have hprod : ((x - E : ℝ) : ℂ) * f x = -alpha := by
        simp [fzzPunctureBoxFormFactor, hx] at hxeq
        push_cast
        linear_combination hxeq
      simpa [mul_comm] using hprod
    rw [hfx, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0]
    rw [Real.rpow_neg (le_of_lt hx0)]
    norm_num [Real.rpow_two]
    field_simp
  have hscaled : IntegrableOn
      (fun x : ℝ => ‖alpha‖ ^ 2 * (x - E) ^ (-2 : ℝ))
      (Ioo E (E + 1)) := by
    exact hfint.integrableOn.congr heqRestricted
  have hinv : Integrable (fun x : ℝ => (x - E) ^ (-2 : ℝ))
      (volume.restrict (Ioo E (E + 1))) := by
    have hc : ‖alpha‖ ^ 2 ≠ 0 := ne_of_gt halphaNorm
    have hmul := hscaled.const_mul (‖alpha‖ ^ 2)⁻¹
    simpa [hc] using hmul
  exact routeP_not_integrableOn_translated_inverseSquare E hinv

/-- Exact classification: regular box rank-one equation has only zero coefficient and zero state. -/
theorem fzzPunctureBoxRankOneEigenEquation_classification
    (E : ℝ) (alpha : ℂ) (f : ℝ → ℂ)
    (h : fzzPunctureBoxRankOneEigenEquation E alpha f) :
    alpha = 0 ∧ f =ᵐ[volume] (0 : ℝ → ℂ) := by
  have halpha := fzzPunctureBoxRankOneEigenEquation_alpha_eq_zero E alpha f h
  refine ⟨halpha, ?_⟩
  rcases h with ⟨_, heq⟩
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ E := (volume : Measure ℝ).ae_ne E
  filter_upwards [heq, hne] with x hxeq hxne
  rw [halpha] at hxeq
  simp only [zero_mul, add_zero] at hxeq
  have hcoef : (((x - E : ℝ) : ℂ)) ≠ 0 := by
    exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hxne)
  exact (mul_eq_zero.mp hxeq).resolve_left hcoef

/-- Nonzero normalizable point mode for regular box rank-one continuum equation. -/
def FZZPunctureBoxRankOnePointMode (E : ℝ) : Prop :=
  ∃ (alpha : ℂ) (f : ℝ → ℂ),
    fzzPunctureBoxRankOneEigenEquation E alpha f ∧
      ¬ f =ᵐ[volume] (0 : ℝ → ℂ)

/-- Regular nonvanishing rank-one coupling has no embedded point mode at any real energy. -/
theorem not_FZZPunctureBoxRankOnePointMode (E : ℝ) :
    ¬ FZZPunctureBoxRankOnePointMode E := by
  rintro ⟨alpha, f, heq, hf⟩
  exact hf (fzzPunctureBoxRankOneEigenEquation_classification E alpha f heq).2

/-- First-order nodal form factor, the exact regularity boundary exposed by no-go. -/
def fzzPunctureNodalBoxFormFactor (E x : ℝ) : ℂ :=
  ((x - E : ℝ) : ℂ) * fzzPunctureBoxFormFactor E x

/-- Formal state after node cancels continuum resolvent pole. -/
def fzzPunctureNodalBoxFormalState (E x : ℝ) : ℂ :=
  -fzzPunctureBoxFormFactor E x

theorem fzzPunctureNodalBoxFormalState_memLp (E : ℝ) :
    MemLp (fzzPunctureNodalBoxFormalState E) 2 volume := by
  exact (fzzPunctureBoxFormFactor_memLp E).neg

/-- Nodal form factor cancels eigenvalue pole pointwise. -/
theorem fzzPunctureNodalBoxFormalState_equation (E x : ℝ) :
    (((x - E : ℝ) : ℂ) * fzzPunctureNodalBoxFormalState E x) +
      fzzPunctureNodalBoxFormFactor E x = 0 := by
  simp [fzzPunctureNodalBoxFormalState, fzzPunctureNodalBoxFormFactor]

/-- Nodal survivor is a genuinely nonzero `L²` state. -/
theorem fzzPunctureNodalBoxFormalState_ne_ae_zero (E : ℝ) :
    ¬ fzzPunctureNodalBoxFormalState E =ᵐ[volume] (0 : ℝ → ℂ) := by
  intro hzero
  have hzero' : fzzPunctureNodalBoxFormalState E =ᵐ[
      volume.restrict (Ioo E (E + 1))] (0 : ℝ → ℂ) :=
    ae_restrict_of_ae hzero
  have hfalse : ∀ᵐ x : ℝ ∂volume.restrict (Ioo E (E + 1)), False := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hzero'] with x hx hxzero
    simp [fzzPunctureNodalBoxFormalState, fzzPunctureBoxFormFactor, hx] at hxzero
  have hmeasure : (volume.restrict (Ioo E (E + 1))) Set.univ = 0 := by
    simpa using ae_iff.mp hfalse
  have hinterval : volume (Ioo E (E + 1)) = 0 := by
    rw [Measure.restrict_apply_univ] at hmeasure
    exact hmeasure
  rw [Real.volume_Ioo] at hinterval
  norm_num at hinterval

/-- Completeness strengthening that asks regular rank-one point modes to carry every nontrivial
FZZ Mellin zero. -/
def FZZPunctureBoxRankOneComplete : Prop :=
  ∀ rho : ℂ,
    fzzCigarContinuumMellinDivisor rho = 0 →
    (¬ ∃ n : ℕ, rho = -2 * ((n : ℂ) + 1)) →
    ∃ E : ℝ,
      rho = fzzPunctureHorizonDilationSpectralParameter E ∧
        FZZPunctureBoxRankOnePointMode E

/-- Regular target-adapted rank-one coupling cannot complete FZZ Mellin divisor. -/
theorem not_FZZPunctureBoxRankOneComplete :
    ¬ FZZPunctureBoxRankOneComplete := by
  intro hcomplete
  obtain ⟨rho, hre0, _, hz⟩ := exists_riemannZeta_zero_mem_openStrip
  have hnontriv : ¬ ∃ n : ℕ, rho = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    norm_num [Complex.mul_re] at hre
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨E, _, hmode⟩ := hcomplete rho hz hnontriv
  exact not_FZZPunctureBoxRankOnePointMode E hmode

end

end RHTower
