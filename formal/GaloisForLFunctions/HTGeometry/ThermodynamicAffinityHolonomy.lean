import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy
import GaloisForLFunctions.HTGeometry.FiniteKMSFluctuationDissipation

/-!
# Thermodynamic affinity as observable clock holonomy

For two positive oriented values `forward` and `reverse`, nonequilibrium thermodynamics assigns
the current `forward - reverse` and the affinity `log (forward / reverse)`. Their product is the
edge entropy-production value. It is nonnegative, is strictly positive exactly when the two
orientations differ, and is unchanged when the edge is reversed.

The ratio `rate u w / rate w u` is also a multiplicative clock calibration. Reversal is automatic,
so the static clock-integrability theorem becomes the Kolmogorov/Wegscheider cycle criterion:
global detailed balance is equivalent to unit rate-ratio holonomy on every closed observable walk.
A nonunit loop has a positive residue rather than only a no-go: some observable edge has strictly
positive entropy production.

Finally, the finite KMS specialization identifies the existing dissipative transition intensity
with entropy production divided by inverse temperature. This imports no temporal evolution: all
statements are pointwise identities between observable values.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Logarithmic thermodynamic force carried by a pair of oriented positive values. -/
def thermodynamicAffinity (forward reverse : ℝ) : ℝ :=
  Real.log (forward / reverse)

/-- Static entropy-production value: oriented current times logarithmic affinity. -/
def entropyProductionValue (forward reverse : ℝ) : ℝ :=
  (forward - reverse) * thermodynamicAffinity forward reverse

/-- Reversing an edge reverses its thermodynamic affinity. -/
theorem thermodynamicAffinity_reverse {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    thermodynamicAffinity reverse forward =
      -thermodynamicAffinity forward reverse := by
  rw [thermodynamicAffinity, thermodynamicAffinity,
    Real.log_div hr.ne' hf.ne', Real.log_div hf.ne' hr.ne']
  ring

/-- Affinities telescope through an intermediate positive calibration value. -/
theorem thermodynamicAffinity_compose {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    thermodynamicAffinity x y + thermodynamicAffinity y z =
      thermodynamicAffinity x z := by
  rw [thermodynamicAffinity, thermodynamicAffinity, thermodynamicAffinity,
    Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hz.ne',
    Real.log_div hx.ne' hz.ne']
  ring

/-- Entropy production forgets orientation: both the current and affinity change sign. -/
theorem entropyProductionValue_reverse {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    entropyProductionValue reverse forward =
      entropyProductionValue forward reverse := by
  rw [entropyProductionValue, entropyProductionValue,
    thermodynamicAffinity_reverse hf hr]
  ring

/-- Current and affinity have the same weak sign. This is the edgewise second-law inequality. -/
theorem entropyProductionValue_nonneg {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    0 ≤ entropyProductionValue forward reverse := by
  rcases le_total forward reverse with hfr | hrf
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hfr)
      (Real.log_nonpos (div_nonneg hf.le hr.le) ((div_le_one hr).2 hfr))
  · exact mul_nonneg (sub_nonneg.mpr hrf)
      (Real.log_nonneg ((one_le_div₀ hr).2 hrf))

/-- Entropy production is strict exactly when the two oriented values differ. -/
theorem entropyProductionValue_pos_iff_ne {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    0 < entropyProductionValue forward reverse ↔ forward ≠ reverse := by
  constructor
  · intro hpos heq
    subst reverse
    simp [entropyProductionValue, thermodynamicAffinity] at hpos
  · intro hne
    rcases lt_or_gt_of_ne hne with hfr | hrf
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr hfr)
        (Real.log_neg (div_pos hf hr) ((div_lt_one hr).2 hfr))
    · exact mul_pos (sub_pos.mpr hrf)
        (Real.log_pos ((one_lt_div hr).2 hrf))

/-- Zero entropy production is exactly local detailed balance. -/
theorem entropyProductionValue_eq_zero_iff_eq {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    entropyProductionValue forward reverse = 0 ↔ forward = reverse := by
  constructor
  · intro hzero
    by_contra hne
    exact (ne_of_gt ((entropyProductionValue_pos_iff_ne hf hr).2 hne)) hzero
  · rintro rfl
    simp [entropyProductionValue]

/-- Multiplicative calibration obtained from a nonzero directed rate field. -/
def rateRatioCalibration {V : Type*} (rate : V → V → ℝ)
    (hrate : ∀ u w, rate u w ≠ 0) : V → V → ℝˣ :=
  fun u w => Units.mk0 (rate u w) (hrate u w) /
    Units.mk0 (rate w u) (hrate w u)

/-- A rate ratio automatically inverts when its observable edge is reversed. -/
theorem rateRatioCalibration_reversible {V : Type*} (G : SimpleGraph V)
    (rate : V → V → ℝ) (hrate : ∀ u w, rate u w ≠ 0) :
    ClockCalibrationReversible G (rateRatioCalibration rate hrate) := by
  intro u w huw
  simp [rateRatioCalibration]

/-- A locally balanced edge has unit multiplicative calibration. -/
theorem rateRatioCalibration_eq_one_of_symmetric {V : Type*}
    (rate : V → V → ℝ) (hrate : ∀ u w, rate u w ≠ 0)
    {u w : V} (hsymm : rate u w = rate w u) :
    rateRatioCalibration rate hrate u w = 1 := by
  apply Units.ext
  simp [rateRatioCalibration, hsymm]

/-- Local detailed balance makes the rate-ratio transport of every walk trivial. -/
theorem clockWalkTransport_rateRatio_eq_one_of_symmetric
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, rate u w ≠ 0)
    (hsymm : ∀ {u w}, G.Adj u w → rate u w = rate w u)
    {u w : V} (p : G.Walk u w) :
    clockWalkTransport (rateRatioCalibration rate hrate) p = 1 := by
  induction p with
  | nil => rfl
  | @cons u w x h p ih =>
      rw [clockWalkTransport_cons,
        rateRatioCalibration_eq_one_of_symmetric rate hrate (hsymm h), ih,
        one_mul]

/-- It is enough that detailed balance hold on the edges actually used by the walk. -/
theorem clockWalkTransport_rateRatio_eq_one_of_symmetric_on_walk
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, rate u w ≠ 0)
    {u w : V} (p : G.Walk u w)
    (hsymm : ∀ {a b}, s(a, b) ∈ p.edges → rate a b = rate b a) :
    clockWalkTransport (rateRatioCalibration rate hrate) p = 1 := by
  revert hsymm
  induction p with
  | nil => intro hsymm; rfl
  | @cons u w x h p ih =>
      intro hsymm
      rw [clockWalkTransport_cons,
        rateRatioCalibration_eq_one_of_symmetric rate hrate
          (hsymm (by simp)),
        ih (fun hab => hsymm (by simp [hab])), one_mul]

/-- **Kolmogorov/Wegscheider clock criterion.** On a connected observable graph, a nonzero rate
field admits one global multiplicative detailed-balance potential exactly when every closed
rate-ratio holonomy is the unit. -/
theorem rateRatioCalibration_exact_iff_flat {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (rate : V → V → ℝ)
    (hrate : ∀ u w, rate u w ≠ 0) :
    ClockCalibrationExact G (rateRatioCalibration rate hrate) ↔
      ClockCalibrationFlat G (rateRatioCalibration rate hrate) :=
  clockCalibrationExact_iff_flat hG _
    (rateRatioCalibration_reversible G rate hrate)

/-- A nonunit rate-ratio loop has a strictly positive observable residue: at least one edge used
by that loop violates detailed balance and has positive entropy production. -/
theorem exists_adjacent_entropyProductionValue_pos_of_nontrivial_holonomy
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w)
    {u : V} (p : G.Walk u u)
    (hhol : clockWalkTransport
      (rateRatioCalibration rate (fun a b => (hrate a b).ne')) p ≠ 1) :
    ∃ a b, s(a, b) ∈ p.edges ∧
      0 < entropyProductionValue (rate a b) (rate b a) := by
  by_contra hnone
  push Not at hnone
  have hsymm : ∀ {a b}, s(a, b) ∈ p.edges → rate a b = rate b a := by
    intro a b hab
    have hnonpos := hnone a b hab
    by_contra hne
    exact (not_lt_of_ge hnonpos) ((entropyProductionValue_pos_iff_ne
      (hrate a b) (hrate b a)).2 hne)
  exact hhol (clockWalkTransport_rateRatio_eq_one_of_symmetric_on_walk
    rate (fun a b => (hrate a b).ne') p hsymm)

/-- KMS entropy production: commutator current times the logarithmic Gibbs-population affinity.
The population ratio, rather than the transition ratio, gives the continuous zero-amplitude
extension of the standard formula. -/
def finiteKMSEntropyProductionTransitionIntensity
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (a b : α) : ℝ :=
  _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β energy amplitude a b *
    thermodynamicAffinity
      (_root_.HTGeometry.finiteGibbsStateWeight β energy b)
      (_root_.HTGeometry.finiteGibbsStateWeight β energy a)

/-- Exact ratio of two finite Gibbs population values. -/
theorem finiteGibbsStateWeight_ratio
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a b : α) :
    _root_.HTGeometry.finiteGibbsStateWeight β energy b /
        _root_.HTGeometry.finiteGibbsStateWeight β energy a =
      Real.exp (β * (energy a - energy b)) := by
  letI : Nonempty α := ⟨a⟩
  rw [_root_.HTGeometry.finiteGibbsStateWeight,
    _root_.HTGeometry.finiteGibbsStateWeight]
  have hZ : _root_.HTGeometry.finiteGibbsPartition β energy ≠ 0 :=
    (_root_.HTGeometry.finiteGibbsPartition_pos β energy).ne'
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

/-- The Gibbs population affinity is exactly inverse temperature times the energy gap. -/
theorem thermodynamicAffinity_finiteGibbsStateWeight
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a b : α) :
    thermodynamicAffinity
        (_root_.HTGeometry.finiteGibbsStateWeight β energy b)
        (_root_.HTGeometry.finiteGibbsStateWeight β energy a) =
      β * (energy a - energy b) := by
  rw [thermodynamicAffinity, finiteGibbsStateWeight_ratio, Real.log_exp]

/-- For a Hermitian observable, KMS entropy production is the elementary edge entropy-production
value of the two endpoint Gibbs populations, weighted by the transition probability. -/
theorem finiteKMSEntropyProductionTransitionIntensity_eq_entropyProductionValue_mul_normSq
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α) :
    finiteKMSEntropyProductionTransitionIntensity β energy amplitude a b =
      entropyProductionValue
          (_root_.HTGeometry.finiteGibbsStateWeight β energy b)
          (_root_.HTGeometry.finiteGibbsStateWeight β energy a) *
        Complex.normSq (amplitude a b) := by
  rw [finiteKMSEntropyProductionTransitionIntensity,
    _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity_eq_stateWeight_sub_mul_normSq
      β energy amplitude hHermitian,
    entropyProductionValue]
  ring

/-- Existing finite KMS dissipative intensity is entropy production divided by inverse
temperature; equivalently entropy production is `β` times the dissipative spectral value. -/
theorem finiteKMSEntropyProductionTransitionIntensity_eq_beta_mul_dissipative
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α) :
    finiteKMSEntropyProductionTransitionIntensity β energy amplitude a b =
      β * _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity
        β energy amplitude a b := by
  rw [finiteKMSEntropyProductionTransitionIntensity,
    thermodynamicAffinity_finiteGibbsStateWeight,
    _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity_eq_gap_mul_commutator
      β energy amplitude hHermitian]
  ring

/-- KMS entropy production is nonnegative at every inverse temperature. The sign change of the
dissipative intensity at negative temperature is compensated by the sign of `β`. -/
theorem finiteKMSEntropyProductionTransitionIntensity_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α) :
    0 ≤ finiteKMSEntropyProductionTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSEntropyProductionTransitionIntensity_eq_entropyProductionValue_mul_normSq
    β energy amplitude hHermitian]
  exact mul_nonneg
    (entropyProductionValue_nonneg
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy b)
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy a))
    (Complex.normSq_nonneg _)

/-- KMS entropy production is symmetric under transition reversal, so it detects the presence but
not the orientation of a directed current. -/
theorem finiteKMSEntropyProductionTransitionIntensity_symm
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α) :
    finiteKMSEntropyProductionTransitionIntensity β energy amplitude a b =
      finiteKMSEntropyProductionTransitionIntensity β energy amplitude b a := by
  rw [finiteKMSEntropyProductionTransitionIntensity_eq_beta_mul_dissipative
      β energy amplitude hHermitian,
    finiteKMSEntropyProductionTransitionIntensity_eq_beta_mul_dissipative
      β energy amplitude hHermitian,
    _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity_symm
      β energy amplitude hHermitian]

end

end GaloisForLFunctions.HTGeometry
