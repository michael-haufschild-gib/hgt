import GaloisForLFunctions.RHTower.AngularEnergyQuantization

/-!
# The critical-line Poisson potential and its unit bump

The angular energy is quantized, but it is only defined at zeros. Moving the base point onto the
critical line turns it into a function of one real variable and keeps the quantum.

For `t : ℝ` define

  `U(t) = Σ_ρ (Re ρ − 1/2)² / ((Re ρ − 1/2)² + (t − Im ρ)²)`,

the sum over the divisor of `ξ`. Writing `δ = Re ρ − 1/2` for the displacement of a zero, the
summand is `π|δ|` times the Poisson kernel of the half plane at height `|δ|`, centred at `Im ρ`.
Equivalently, and this is the whole point,

  `summand(t) = 1 / (1 + ((t − Im ρ)/δ)²)`,

a bump of height exactly `1` and width exactly `|δ|`. On-line zeros contribute nothing.

Two consequences:

* `U(Im ρ) ≥ 1` for every off-line zero, since that zero's own bump is at its peak there. The height
  does not depend on `δ`: a zero at distance `10⁻¹⁰⁰` from the line produces a bump just as tall as
  one at distance `1/2`, only narrower. Hence `U ≡ 0` under the hypothesis and `sup U ≥ 1` otherwise,
  and the hypothesis is the *threshold* `U < 1`.

* Because the bump keeps unit height while its width shrinks, its `L¹` mass `π|δ|` goes to zero.
  Every criterion that reads the divisor through an average — a mean value over a window, a mollified
  moment, a smoothed counting function — measures mass, not height, and therefore loses a near-line
  counterexample no matter how fine the window, while `U` retains it exactly. This is an object-level
  account of why averaged criteria in this field stall a fixed factor short of the target.
-/

open Complex

namespace RHTower

noncomputable section

/-- The contribution of one zero to the critical-line potential. -/
def poissonBumpTerm (t : ℝ) (ρ : XiDivisorSupport) : ℝ :=
  ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ)
    / (((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (ρ : ℂ).im) ^ (2 : ℕ))

/-- The critical-line Poisson potential of the off-line part of the divisor. -/
def poissonPotential (t : ℝ) : ℝ := ∑' ρ, poissonBumpTerm t ρ

theorem poissonBumpTerm_nonneg (t : ℝ) (ρ : XiDivisorSupport) : 0 ≤ poissonBumpTerm t ρ :=
  div_nonneg (sq_nonneg _) (by positivity)

/-- Each bump is dominated by a fixed Cauchy weight, uniformly in the displacement. -/
theorem poissonBumpTerm_le (t : ℝ) (ρ : XiDivisorSupport) :
    poissonBumpTerm t ρ ≤ 2 * ((1 : ℝ) / (1 + (t - (ρ : ℂ).im) ^ (2 : ℕ))) := by
  obtain ⟨h0, h1⟩ := xiDivisorSupport_re_mem ρ
  set d : ℝ := ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) with hd
  set u : ℝ := (t - (ρ : ℂ).im) ^ (2 : ℕ) with hu
  have hd0 : 0 ≤ d := sq_nonneg _
  have hu0 : 0 ≤ u := sq_nonneg _
  have hdle : d ≤ 1 := by
    rw [hd]; nlinarith
  rw [poissonBumpTerm, ← hd, ← hu, div_le_iff₀ (by positivity), mul_comm]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

theorem summable_poissonBumpTerm (t : ℝ) : Summable (fun ρ => poissonBumpTerm t ρ) :=
  Summable.of_nonneg_of_le (poissonBumpTerm_nonneg t) (poissonBumpTerm_le t)
    ((summable_supportWeight t).mul_left 2)

theorem poissonPotential_nonneg (t : ℝ) : 0 ≤ poissonPotential t :=
  tsum_nonneg (poissonBumpTerm_nonneg t)

/-- **Scale invariance.** Each off-line zero contributes a bump of height one and width `|δ|`. -/
theorem poissonBumpTerm_eq_scaled {ρ : XiDivisorSupport} (h : (ρ : ℂ).re ≠ 1 / 2) (t : ℝ) :
    poissonBumpTerm t ρ = 1 / (1 + ((t - (ρ : ℂ).im) / ((ρ : ℂ).re - 1 / 2)) ^ (2 : ℕ)) := by
  have hδ : (ρ : ℂ).re - 1 / 2 ≠ 0 := sub_ne_zero.mpr h
  rw [poissonBumpTerm, div_pow, div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-- On the critical line the bump is identically zero. -/
theorem poissonBumpTerm_of_re_eq_half {ρ : XiDivisorSupport} (h : (ρ : ℂ).re = 1 / 2) (t : ℝ) :
    poissonBumpTerm t ρ = 0 := by
  rw [poissonBumpTerm, h]
  norm_num

/-- **The quantum.** At the ordinate of an off-line zero its own bump is at full height one,
whatever its distance to the critical line. -/
theorem poissonBumpTerm_self {ρ : XiDivisorSupport} (h : (ρ : ℂ).re ≠ 1 / 2) :
    poissonBumpTerm ((ρ : ℂ).im) ρ = 1 := by
  have hδ : ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h)
  rw [poissonBumpTerm]
  simp only [sub_self]
  rw [show ((0 : ℝ)) ^ (2 : ℕ) = 0 by norm_num, add_zero, div_self hδ]

/-- **Every off-line zero forces a unit of potential at its own ordinate.** -/
theorem one_le_poissonPotential {ρ : XiDivisorSupport} (h : (ρ : ℂ).re ≠ 1 / 2) :
    1 ≤ poissonPotential ((ρ : ℂ).im) := by
  have hle := (summable_poissonBumpTerm ((ρ : ℂ).im)).le_tsum ρ
    (fun b _ => poissonBumpTerm_nonneg _ b)
  rwa [poissonBumpTerm_self h] at hle

theorem poissonPotential_eq_zero_of_riemannHypothesis (h : RiemannHypothesis) (t : ℝ) :
    poissonPotential t = 0 := by
  have hhalf : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 := fun ρ =>
    (supportPartner_eq_self_iff ρ).mp (riemannHypothesis_iff_supportPartner_eq_id.mp h ρ)
  rw [poissonPotential]
  simp [fun ρ => poissonBumpTerm_of_re_eq_half (hhalf ρ) t]

/-- **The threshold criterion.** The hypothesis is equivalent to a uniform strict bound below one
on a single explicit function of one real variable. -/
theorem riemannHypothesis_iff_forall_poissonPotential_lt_one :
    RiemannHypothesis ↔ ∀ t : ℝ, poissonPotential t < 1 := by
  constructor
  · intro h t
    rw [poissonPotential_eq_zero_of_riemannHypothesis h t]
    norm_num
  · intro h
    refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
    by_contra hc
    exact absurd (one_le_poissonPotential hc) (not_le.mpr (h ((ρ : ℂ).im)))

theorem riemannHypothesis_iff_forall_poissonPotential_eq_zero :
    RiemannHypothesis ↔ ∀ t : ℝ, poissonPotential t = 0 := by
  constructor
  · exact poissonPotential_eq_zero_of_riemannHypothesis
  · intro h
    refine riemannHypothesis_iff_forall_poissonPotential_lt_one.mpr fun t => ?_
    rw [h t]
    norm_num

/-- **The gap.** The potential never takes all its values in the open interval `(0,1)`. -/
theorem poissonPotential_eq_zero_of_forall_lt_one (h : ∀ t : ℝ, poissonPotential t < 1) (t : ℝ) :
    poissonPotential t = 0 :=
  poissonPotential_eq_zero_of_riemannHypothesis
    (riemannHypothesis_iff_forall_poissonPotential_lt_one.mpr h) t

end

end RHTower
