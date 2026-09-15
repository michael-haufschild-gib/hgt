import GaloisForLFunctions.RHTower.XiMassRapidityMassPhase
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Two-rapidity geometry of mass-phase correlations

The diagonal restriction of a correlation between distinct mass frequencies has
phase `(h-k) sinh t`, hence is nonstationary.  This apparent cancellation does
not control the actual square of the rapidity integral: it has two independent
rapidity variables.  In the timelike region that full two-variable phase has a
stationary pair, one stationary rapidity for each frequency.  Therefore a
covariance proof needs a genuine diagonal-localization mechanism (or another
way to remove the stationary pair); pointwise diagonal cancellation alone is
not a bilinear estimate.
-/

namespace RHTower

noncomputable section

/-- Phase in the product of two mass rapidity modes, before any diagonal
restriction of the two rapidity variables. -/
def xiMassTwoRapidityCorrelationPhase (u h k t s : ℝ) : ℝ :=
  (u * Real.cosh t + h * Real.sinh t) -
    (u * Real.cosh s + k * Real.sinh s)

/-- Stationarity equations for the two independent rapidities of a mass-mode
correlation. -/
def XiMassTwoRapidityCorrelationStationary (u h k t s : ℝ) : Prop :=
  u * Real.sinh t + h * Real.cosh t = 0 ∧
    u * Real.sinh s + k * Real.cosh s = 0

/-- On the artificial diagonal, the common timelike part cancels exactly. -/
theorem xiMassTwoRapidityCorrelationPhase_diagonal
    (u h k t : ℝ) :
    xiMassTwoRapidityCorrelationPhase u h k t t = (h - k) * Real.sinh t := by
  rw [xiMassTwoRapidityCorrelationPhase]
  ring

/-- The diagonal relative phase is nonstationary for distinct frequencies. -/
theorem hasDerivAt_xiMassTwoRapidityCorrelationPhase_diagonal
    (h k t : ℝ) :
    HasDerivAt (fun x : ℝ => (h - k) * Real.sinh x)
      ((h - k) * Real.cosh t) t := by
  simpa using (Real.hasDerivAt_sinh t).const_mul (h - k)

theorem xiMassTwoRapidityCorrelationPhase_diagonal_deriv_ne_zero
    {h k t : ℝ} (hhk : h ≠ k) :
    (h - k) * Real.cosh t ≠ 0 := by
  exact mul_ne_zero (sub_ne_zero.mpr hhk) (ne_of_gt (Real.cosh_pos t))

/-- **Two-rapidity stationary-pair obstruction.**  The unrestricted
two-variable correlation phase remains stationary throughout the timelike
region. -/
theorem exists_xiMassTwoRapidityCorrelationStationary
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) :
    ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s := by
  refine ⟨-timelikeRapidity u h, -timelikeRapidity u k, ?_, ?_⟩
  · exact (massPhase_timelike_stationary_iff hu hh hhu _).mpr rfl
  · exact (massPhase_timelike_stationary_iff hu hk hku _).mpr rfl

/-- The stationary pair of two distinct frequencies is strictly off the
same-rapidity diagonal.  Thus an independently justified diagonal localization
would eliminate every off-diagonal timelike stationary pair. -/
theorem XiMassTwoRapidityCorrelationStationary.rapidities_ne_of_frequency_ne
    {u h k t s : ℝ} (hstat : XiMassTwoRapidityCorrelationStationary u h k t s)
    (hhk : h ≠ k) : t ≠ s := by
  intro hts
  subst s
  rcases hstat with ⟨ht, hs⟩
  have hprod : (h - k) * Real.cosh t = 0 := by
    linarith
  exact hhk (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
    (ne_of_gt (Real.cosh_pos t))))

/-- A two-rapidity stationary pair reverses the order of its frequencies. -/
theorem XiMassTwoRapidityCorrelationStationary.rapidities_order_reverse_of_frequency_lt
    {u h k t s : ℝ} (hu : 0 < u)
    (hstat : XiMassTwoRapidityCorrelationStationary u h k t s) (hhk : h < k) :
    s < t := by
  rcases hstat with ⟨ht, hs⟩
  have htanh_t : Real.tanh t = -h / u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hu.ne', (Real.cosh_pos t).ne']
    linarith
  have htanh_s : Real.tanh s = -k / u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hu.ne', (Real.cosh_pos s).ne']
    linarith
  have hratio : Real.tanh s < Real.tanh t := by
    calc
      Real.tanh s = -k / u := htanh_s
      _ < -h / u := by
        rw [div_lt_iff₀ hu]
        field_simp [hu.ne']
        linarith
      _ = Real.tanh t := htanh_t.symm
  by_contra hst
  exact (not_le_of_gt hratio)
    (HTGeometry.tanh_strictMono.monotone (le_of_not_gt hst))

/-- Distinct-frequency stationary pairs lie strictly in the anti-ordered rapidity cone. -/
theorem XiMassTwoRapidityCorrelationStationary.frequency_rapidity_orientation_neg
    {u h k t s : ℝ} (hu : 0 < u)
    (hstat : XiMassTwoRapidityCorrelationStationary u h k t s) (hhk : h ≠ k) :
    (h - k) * (t - s) < 0 := by
  rcases lt_or_gt_of_ne hhk with hlt | hgt
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt)
      (sub_pos.mpr (hstat.rapidities_order_reverse_of_frequency_lt hu hlt))
  · have hrev : XiMassTwoRapidityCorrelationStationary u k h s t :=
      ⟨hstat.2, hstat.1⟩
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hgt)
      (sub_neg.mpr (hrev.rapidities_order_reverse_of_frequency_lt hu hgt))

/-- Every stationary pair at unequal frequencies is excluded by same-order causal support. -/
theorem not_exists_xiMassTwoRapidityCorrelationStationary_of_same_order
    {u h k : ℝ} (hu : 0 < u) (hhk : h ≠ k) :
    ¬ ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧
      0 ≤ (h - k) * (t - s) := by
  rintro ⟨t, s, hstat, horient⟩
  exact (not_le_of_gt
    (hstat.frequency_rapidity_orientation_neg hu hhk)) horient

/-- The rapidity triangle opposite to frequency order contains no stationary pair. -/
theorem not_exists_xiMassTwoRapidityCorrelationStationary_of_frequency_lt_and_rapidity_le
    {u h k : ℝ} (hu : 0 < u) (hhk : h < k) :
    ¬ ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧ t ≤ s := by
  rintro ⟨t, s, hstat, hts⟩
  exact (not_le_of_gt
    (hstat.rapidities_order_reverse_of_frequency_lt hu hhk)) hts

/-- Strictly ordered timelike frequencies have a stationary pair in the opposite rapidity
triangle.  Frequency order alone therefore cannot remove the two-rapidity saddle. -/
theorem exists_xiMassTwoRapidityCorrelationStationary_with_rapidities_order_reverse
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) (hhk : h < k) :
    ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧ s < t := by
  obtain ⟨t, s, hstat⟩ :=
    exists_xiMassTwoRapidityCorrelationStationary hu hh hk hhu hku
  exact ⟨t, s, hstat,
    hstat.rapidities_order_reverse_of_frequency_lt hu hhk⟩

end

end RHTower
