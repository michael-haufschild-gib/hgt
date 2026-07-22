import GaloisForLFunctions.RHTower.CCMSoninFiniteWordFaithfulness
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace

/-!
# Canonical cyclic trace on the faithful Sonin principal-shell semigroup

The corpus already contains two ingredients which had not been connected.  The logarithmic
crossed-product model has its canonical degree-zero cyclic trace, while the exact CCM--Sonin
principal algebra has a faithful zero/live tropical normal form.  This file transports the
logarithmic trace law to that exact normal-state product.

A live window contributes logarithmic shell width only in translation degree zero.  The key
theorem proves this weight is cyclic under the exact, generally noncommutative state product.
It is Calkin-invariant by faithful normal-form uniqueness and extends to a cyclic bilinear pairing
on the finite-support algebraic state core.  On genuine CCM Gram factors it is exactly diagonal:
the off-diagonal source/target factors vanish and a diagonal scale `r` contributes `log r`.
Consequently the existing unsquared Euler coefficient gives the exact von--Mangoldt flux.

This closes the principal cyclic/source-value connector.  It does not yet extend the trace across
the Sonin principal-relative ideal or attach the Burnol archimedean finite part.
-/

noncomputable section

namespace RHTower

/-- Logarithmic coefficient of a canonical live Sonin window. -/
def soninLiveWindowCyclicLogWeight {a : ℝ} (d : SoninLiveWindow a) : ℝ :=
  if d.scale = 1 then Real.log d.ceiling - Real.log d.floor else 0

/-- Canonical logarithmic trace on the zero/live Sonin normal-state semigroup. -/
def soninWindowStateCyclicLogTrace {a : ℝ} : SoninWindowState a → ℝ
  | .zero => 0
  | .live d => soninLiveWindowCyclicLogWeight d

private theorem second_scale_eq_inv_of_mul_eq_one {a : ℝ}
    (d e : SoninLiveWindow a) (hscale : d.scale * e.scale = 1) :
    e.scale = d.scale⁻¹ := by
  calc
    e.scale = 1 * e.scale := by rw [one_mul]
    _ = (d.scale⁻¹ * d.scale) * e.scale := by
      rw [inv_mul_cancel₀ d.scale_pos.ne']
    _ = d.scale⁻¹ * (d.scale * e.scale) := by rw [mul_assoc]
    _ = d.scale⁻¹ := by rw [hscale, mul_one]

private theorem soninLiveComposeFloor_eq_raw_of_scale_mul_eq_one
    {a : ℝ} (d e : SoninLiveWindow a)
    (hscale : d.scale * e.scale = 1) :
    soninLiveComposeFloor d e =
      min (max d.floor (d.scale⁻¹ * e.floor))
        (min d.ceiling (d.scale⁻¹ * e.ceiling)) := by
  have heScale := second_scale_eq_inv_of_mul_eq_one d e hscale
  have heFloor : a ≤ d.scale⁻¹ * e.floor := by
    simpa [heScale] using e.domain_le
  have heCeiling : a ≤ d.scale⁻¹ * e.ceiling :=
    heFloor.trans (mul_le_mul_of_nonneg_left e.floor_lt_ceiling.le
      (inv_pos.mpr d.scale_pos).le)
  have hdCeiling : a ≤ d.ceiling :=
    d.base_le_floor.trans d.floor_lt_ceiling.le
  have hraw : a ≤
      min (max d.floor (d.scale⁻¹ * e.floor))
        (min d.ceiling (d.scale⁻¹ * e.ceiling)) := by
    exact le_min (d.base_le_floor.trans (le_max_left _ _))
      (le_min hdCeiling heCeiling)
  unfold soninLiveComposeFloor soninWindowComposeNormalizedFloor
    soninWindowNormalizedFloor soninWindowComposeFloor
    soninWindowComposeCeiling
  rw [hscale, inv_one, one_mul, max_eq_left hraw]
  exact min_eq_left (min_le_right _ _)

private theorem soninLiveComposeCeiling_swap_of_scale_mul_eq_one
    {a : ℝ} (d e : SoninLiveWindow a)
    (hscale : d.scale * e.scale = 1) :
    soninLiveComposeCeiling e d =
      d.scale * soninLiveComposeCeiling d e := by
  have heScale := second_scale_eq_inv_of_mul_eq_one d e hscale
  have hx0 : 0 ≤ d.scale := d.scale_pos.le
  unfold soninLiveComposeCeiling soninWindowComposeCeiling
  rw [heScale, inv_inv, mul_min_of_nonneg _ _ hx0]
  have hcancel : d.scale * (d.scale⁻¹ * e.ceiling) = e.ceiling := by
    field_simp [d.scale_pos.ne']
  rw [hcancel, min_comm]

private theorem soninLiveComposeFloor_swap_of_scale_mul_eq_one
    {a : ℝ} (d e : SoninLiveWindow a)
    (hscale : d.scale * e.scale = 1) :
    soninLiveComposeFloor e d =
      d.scale * soninLiveComposeFloor d e := by
  have heScale := second_scale_eq_inv_of_mul_eq_one d e hscale
  have hscale' : e.scale * d.scale = 1 := by simpa [mul_comm] using hscale
  rw [soninLiveComposeFloor_eq_raw_of_scale_mul_eq_one d e hscale,
    soninLiveComposeFloor_eq_raw_of_scale_mul_eq_one e d hscale']
  have hx0 : 0 ≤ d.scale := d.scale_pos.le
  rw [heScale, inv_inv, mul_min_of_nonneg _ _ hx0,
    mul_max_of_nonneg _ _ hx0, mul_min_of_nonneg _ _ hx0]
  have hcancelF : d.scale * (d.scale⁻¹ * e.floor) = e.floor := by
    field_simp [d.scale_pos.ne']
  have hcancelC : d.scale * (d.scale⁻¹ * e.ceiling) = e.ceiling := by
    field_simp [d.scale_pos.ne']
  rw [hcancelF, hcancelC, max_comm e.floor (d.scale * d.floor),
    min_comm e.ceiling (d.scale * d.ceiling)]

/-- **Exact tropical Sonin trace law.**  Logarithmic identity-degree shell weight is cyclic under
the faithful zero/live state product. -/
theorem soninWindowStateCyclicLogTrace_compose_comm
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    soninWindowStateCyclicLogTrace (composeSoninWindowStates s t) =
      soninWindowStateCyclicLogTrace (composeSoninWindowStates t s) := by
  cases s with
  | zero => simp [composeSoninWindowStates, soninWindowStateCyclicLogTrace]
  | live d =>
    cases t with
    | zero => simp [composeSoninWindowStates, soninWindowStateCyclicLogTrace]
    | live e =>
      by_cases hscale : d.scale * e.scale = 1
      · have hscale' : e.scale * d.scale = 1 := by simpa [mul_comm] using hscale
        have hC := soninLiveComposeCeiling_swap_of_scale_mul_eq_one d e hscale
        have hF := soninLiveComposeFloor_swap_of_scale_mul_eq_one d e hscale
        by_cases hlive : soninLiveComposeFloor d e < soninLiveComposeCeiling d e
        · have hlive' : soninLiveComposeFloor e d < soninLiveComposeCeiling e d := by
            rw [hC, hF]
            exact mul_lt_mul_of_pos_left hlive d.scale_pos
          have hFpos : 0 < soninLiveComposeFloor d e :=
            lt_of_lt_of_le ha (base_le_soninLiveComposeFloor_of_lt d e hlive)
          have hCpos : 0 < soninLiveComposeCeiling d e :=
            hFpos.trans hlive
          simp only [composeSoninWindowStates, composeSoninLiveWindows, dif_pos hlive,
            dif_pos hlive', soninWindowStateCyclicLogTrace,
            soninLiveWindowCyclicLogWeight, soninLiveComposeScale, hscale, hscale',
            if_pos]
          rw [hC, hF, Real.log_mul d.scale_pos.ne' hCpos.ne',
            Real.log_mul d.scale_pos.ne' hFpos.ne']
          ring
        · have hlive' : ¬ soninLiveComposeFloor e d < soninLiveComposeCeiling e d := by
            intro h
            apply hlive
            rw [hC, hF] at h
            exact lt_of_mul_lt_mul_left h d.scale_pos.le
          simp [composeSoninWindowStates, composeSoninLiveWindows, hlive, hlive',
            soninWindowStateCyclicLogTrace]
      · have hscale' : e.scale * d.scale ≠ 1 := by simpa [mul_comm] using hscale
        by_cases hlive : soninLiveComposeFloor d e < soninLiveComposeCeiling d e <;>
          by_cases hlive' : soninLiveComposeFloor e d < soninLiveComposeCeiling e d <;>
          simp [composeSoninWindowStates, composeSoninLiveWindows, hlive, hlive',
            soninWindowStateCyclicLogTrace, soninLiveWindowCyclicLogWeight,
            soninLiveComposeScale, hscale, hscale']

/-- The normal-state logarithmic trace depends only on the represented Calkin class. -/
theorem soninWindowStateCyclicLogTrace_eq_of_operator_compactEq
    {a : ℝ} (ha : 0 < a) {s t : SoninWindowState a}
    (h : s.operator =ₖ t.operator) :
    soninWindowStateCyclicLogTrace s = soninWindowStateCyclicLogTrace t := by
  rw [(s.operator_compactEq_iff ha t).mp h]

/-- Three-factor cyclicity follows from exact associativity of the normal-state product. -/
theorem soninWindowStateCyclicLogTrace_rotate_three
    {a : ℝ} (ha : 0 < a) (r s t : SoninWindowState a) :
    soninWindowStateCyclicLogTrace
        (composeSoninWindowStates (composeSoninWindowStates r s) t) =
      soninWindowStateCyclicLogTrace
        (composeSoninWindowStates (composeSoninWindowStates s t) r) := by
  rw [composeSoninWindowStates_assoc ha]
  exact soninWindowStateCyclicLogTrace_compose_comm ha r
    (composeSoninWindowStates s t)

/-- Bilinear trace pairing on the finite algebraic normal-state core. -/
def soninWindowStatePairCyclicTrace {a : ℝ}
    (A B : SoninWindowState a →₀ ℂ) : ℂ :=
  ∑ s ∈ A.support, ∑ t ∈ B.support,
    A s * B t * (soninWindowStateCyclicLogTrace
      (composeSoninWindowStates s t) : ℂ)

/-- The logarithmic normal-state pairing is cyclic on the full finite-support core. -/
theorem soninWindowStatePairCyclicTrace_comm
    {a : ℝ} (ha : 0 < a) (A B : SoninWindowState a →₀ ℂ) :
    soninWindowStatePairCyclicTrace A B =
      soninWindowStatePairCyclicTrace B A := by
  rw [soninWindowStatePairCyclicTrace, soninWindowStatePairCyclicTrace,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro s hs
  rw [soninWindowStateCyclicLogTrace_compose_comm ha s t]
  ring

/-- Diagonal CCM Gram datum at one scale. -/
def soninDiagonalGramFactor (r : ℝ) (hr : 1 < r) : SoninGramFactor where
  source := r
  target := r
  source_gt_one := hr
  target_gt_one := hr

/-- Principal logarithmic trace of one genuine CCM Gram factor. -/
def soninGramFactorPrincipalCyclicTrace
    (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) : ℝ :=
  soninWindowStateCyclicLogTrace (SoninWindowState.live (g.liveWindow a ha))

/-- **CCM Gram diagonalization.**  The principal cyclic trace vanishes between distinct scales
and returns logarithmic source length on the diagonal. -/
theorem soninGramFactorPrincipalCyclicTrace_eq_ite
    (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) :
    soninGramFactorPrincipalCyclicTrace a ha g =
      if g.source = g.target then Real.log g.source else 0 := by
  rcases g with ⟨s, t, hs, ht⟩
  have hs0 : 0 < s := zero_lt_one.trans hs
  simp only [soninGramFactorPrincipalCyclicTrace, SoninGramFactor.liveWindow,
    soninWindowStateCyclicLogTrace, soninLiveWindowCyclicLogWeight]
  by_cases hst : s = t
  · subst t
    have hscale : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0.ne'
    have hsource : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
    rw [if_pos rfl, hscale, if_pos rfl, hsource, one_mul, max_self,
      Real.log_mul hs0.ne' ha.ne']
    ring
  · have hscale : s⁻¹ * t ≠ 1 := by
      intro h
      apply hst
      calc
        s = s * 1 := by rw [mul_one]
        _ = s * (s⁻¹ * t) := by rw [h]
        _ = t := by field_simp [hs0.ne']
    rw [if_neg hst, if_neg hscale]

/-- A diagonal CCM Gram factor contributes exact orbital length, independently of aperture. -/
theorem soninGramFactorPrincipalCyclicTrace_diagonal_eq_log
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) :
    soninGramFactorPrincipalCyclicTrace a ha (soninDiagonalGramFactor r hr) =
      Real.log r := by
  rw [soninGramFactorPrincipalCyclicTrace_eq_ite]
  simp [soninDiagonalGramFactor]

/-- Principal normal-state trace density at one prime-power mode. -/
def soninPrimePowerPrincipalCyclicTraceDensity (pk : Nat.Primes × ℕ) : ℂ :=
  soninSemilocalLogPrimePowerCoefficient pk *
    (soninGramFactorPrincipalCyclicTrace 1 zero_lt_one
      (soninDiagonalGramFactor (soninSemilocalPrimePowerScale pk)
        (one_lt_soninSemilocalPrimePowerScale pk)) : ℂ)

/-- **Exact finite-place source law.**  The faithful principal normal form recovers the unsquared
von--Mangoldt coefficient, without a guessed response normalization. -/
theorem soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient
    (pk : Nat.Primes × ℕ) :
    soninPrimePowerPrincipalCyclicTraceDensity pk =
      soninSemilocalPrimeFluxCoefficient pk := by
  rw [soninPrimePowerPrincipalCyclicTraceDensity,
    soninGramFactorPrincipalCyclicTrace_diagonal_eq_log,
    soninSemilocalPrimeFluxCoefficient,
    soninSemilocalLogScaleLength_eq_log_scale]

end RHTower
