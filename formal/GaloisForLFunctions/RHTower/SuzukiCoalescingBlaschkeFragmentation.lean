import GaloisForLFunctions.RHTower.SuzukiCoalescingHalfPlaneNormality
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGroupDelay

/-!
# Sharp rational-inner fragmentation at a coalescing Suzuki anchor

The first disk jet controls a radial budget, not Blaschke degree.  This module constructs the exact
countermodel from Theorem D: one forced origin zero followed by `N` coincident shallow Blaschke
turns centered at a prescribed boundary point.  The radius is the positive real `N`th root of
`κ`, so the carrier has value zero and derivative exactly `κ` at the disk anchor for every `N`.

The half-plane pullback has the exact moving normalization `Θ(ic)=0` and
`2ic Θ'(ic)=κ`.  Meanwhile the conserved fragmentation law

`N(1-κ^(1/N)) ≤ -log κ`

is proved without asymptotics: arbitrarily large Blaschke degree can be hidden inside one fixed
first-jet budget.  Boundary innerness is connected to the existing finite-Blaschke library.  No
claim about Suzuki's literal source is made here.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

def suzukiBlaschkeFragmentRadius (κ : ℝ) (N : ℕ) : ℝ :=
  κ ^ (1 / (N : ℝ))

theorem suzukiBlaschkeFragmentRadius_pos
    {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    0 < suzukiBlaschkeFragmentRadius κ N :=
  Real.rpow_pos_of_pos hκ _

theorem suzukiBlaschkeFragmentRadius_lt_one
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {N : ℕ} (hN : 0 < N) :
    suzukiBlaschkeFragmentRadius κ N < 1 := by
  apply Real.rpow_lt_one hκ0 hκ1
  positivity

theorem suzukiBlaschkeFragmentRadius_pow
    {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) :
    suzukiBlaschkeFragmentRadius κ N ^ N = κ := by
  rw [suzukiBlaschkeFragmentRadius, ← Real.rpow_natCast,
    ← Real.rpow_mul hκ.le]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [one_div, inv_mul_cancel₀ hN0, Real.rpow_one]

/-- The repeated shallow Blaschke section centered at the physical boundary point `ζ`. -/
def suzukiCenteredBlaschkeSection (ζ : ℂ) (r : ℝ) (w : ℂ) : ℂ :=
  (-(starRingEnd ℂ) ζ) *
    ((w - (r : ℂ) * ζ) /
      (1 - (starRingEnd ℂ) ((r : ℂ) * ζ) * w))

/-- Disk countermodel with one forced origin zero and `N` coincident shallow turns. -/
def suzukiFragmentedDiskCarrier (ζ : ℂ) (r : ℝ) (N : ℕ) (w : ℂ) : ℂ :=
  w * suzukiCenteredBlaschkeSection ζ r w ^ N

theorem star_mul_self_eq_one_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (starRingEnd ℂ) ζ * ζ = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]
  norm_num

theorem suzukiCenteredBlaschkeSection_zero
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r : ℝ) :
    suzukiCenteredBlaschkeSection ζ r 0 = r := by
  rw [suzukiCenteredBlaschkeSection]
  simp only [mul_zero, sub_zero, zero_sub, div_one]
  rw [show (-(starRingEnd ℂ) ζ) * (-((r : ℂ) * ζ)) =
      (r : ℂ) * ((starRingEnd ℂ) ζ * ζ) by ring,
    star_mul_self_eq_one_of_norm_eq_one hζ, mul_one]

theorem suzukiCenteredBlaschkeSection_eq_paperFormula
    (ζ : ℂ) (r : ℝ) (w : ℂ) :
    suzukiCenteredBlaschkeSection ζ r w =
      (starRingEnd ℂ) ζ *
        (((r : ℂ) * ζ - w) /
          (1 - (r : ℂ) * (starRingEnd ℂ) ζ * w)) := by
  rw [suzukiCenteredBlaschkeSection]
  rw [map_mul, Complex.conj_ofReal]
  ring

theorem norm_suzukiCenteredBlaschkeSection_eq_one
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ = 1) :
    ‖suzukiCenteredBlaschkeSection ζ r w‖ = 1 := by
  rw [suzukiCenteredBlaschkeSection, norm_mul, norm_neg, Complex.norm_conj, hζ]
  have ha : ‖(r : ℂ) * ζ‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hζ, mul_one]
    exact hr1
  have hfac := GaloisForLFunctions.HTGeometry.norm_blaschkeFactor_eq_one ha hw
  simpa [Complex.star_def] using hfac

theorem norm_suzukiFragmentedDiskCarrier_eq_one
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖suzukiFragmentedDiskCarrier ζ r N w‖ = 1 := by
  rw [suzukiFragmentedDiskCarrier, norm_mul, norm_pow,
    norm_suzukiCenteredBlaschkeSection_eq_one hζ hr0 hr1 hw, hw]
  simp

theorem suzukiFragmentedDiskCarrier_zero (ζ : ℂ) (r : ℝ) (N : ℕ) :
    suzukiFragmentedDiskCarrier ζ r N 0 = 0 := by
  simp [suzukiFragmentedDiskCarrier]

theorem differentiableAt_suzukiCenteredBlaschkeSection_zero
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    DifferentiableAt ℂ (suzukiCenteredBlaschkeSection ζ r) 0 := by
  have ha : ‖(r : ℂ) * ζ‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hζ, mul_one]
    exact hr1
  rw [show suzukiCenteredBlaschkeSection ζ r = fun w =>
      (-(starRingEnd ℂ) ζ) *
        ((w - (r : ℂ) * ζ) /
          (1 - (starRingEnd ℂ) ((r : ℂ) * ζ) * w)) by rfl]
  fun_prop (disch := exact
    GaloisForLFunctions.HTGeometry.blaschkeFactor_den_ne_zero ha (by norm_num))

theorem deriv_suzukiFragmentedDiskCarrier_zero
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) :
    deriv (suzukiFragmentedDiskCarrier ζ r N) 0 = (r : ℂ) ^ N := by
  have hsec := differentiableAt_suzukiCenteredBlaschkeSection_zero hζ hr0 hr1
  have hmul := (hasDerivAt_id (0 : ℂ)).mul (hsec.pow N).hasDerivAt
  change HasDerivAt
    (fun w : ℂ => w * suzukiCenteredBlaschkeSection ζ r w ^ N)
    _ 0 at hmul
  have hmul' : HasDerivAt
      (fun w : ℂ => w * suzukiCenteredBlaschkeSection ζ r w ^ N)
      ((r : ℂ) ^ N) 0 := by
    convert hmul using 1
    simp [suzukiCenteredBlaschkeSection_zero hζ]
  exact hmul'.deriv

theorem deriv_suzukiFragmentedDiskCarrier_radius_zero
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {N : ℕ} (hN : 0 < N) :
    deriv
      (suzukiFragmentedDiskCarrier ζ (suzukiBlaschkeFragmentRadius κ N) N) 0 =
        (κ : ℂ) := by
  rw [deriv_suzukiFragmentedDiskCarrier_zero hζ
    (suzukiBlaschkeFragmentRadius_pos hκ0 N).le
    (suzukiBlaschkeFragmentRadius_lt_one hκ0.le hκ1 hN),
    ← ofReal_pow, suzukiBlaschkeFragmentRadius_pow hκ0 hN]

theorem suzukiBlaschkeFragment_radialBudget
    {κ : ℝ} (hκ0 : 0 < κ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * (1 - suzukiBlaschkeFragmentRadius κ N) ≤ -Real.log κ := by
  let r := suzukiBlaschkeFragmentRadius κ N
  have hr0 : 0 < r := suzukiBlaschkeFragmentRadius_pos hκ0 N
  have hlog : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hlogr : Real.log r = (1 / (N : ℝ)) * Real.log κ := by
    change Real.log (suzukiBlaschkeFragmentRadius κ N) = _
    rw [suzukiBlaschkeFragmentRadius, Real.log_rpow hκ0]
  calc
    (N : ℝ) * (1 - r) ≤ (N : ℝ) * (-Real.log r) := by
      gcongr
      linarith
    _ = -Real.log κ := by
      rw [hlogr]
      field_simp [hNpos.ne']

/-- Upper-half-plane realization of the fragmented rational-inner disk carrier. -/
def suzukiFragmentedHalfPlaneCarrier
    (ζ : ℂ) (r : ℝ) (N : ℕ) (c : ℝ) (z : ℂ) : ℂ :=
  suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c z)

theorem suzukiCoalescingCayley_anchor {c : ℝ} (hc : 0 < c) :
    suzukiCoalescingCayley c ((c : ℂ) * I) = 0 := by
  rw [suzukiCoalescingCayley]
  have hden : (c : ℂ) * I + (c : ℂ) * I ≠ 0 := by
    ring_nf
    exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hc.ne') I_ne_zero) (by norm_num)
  rw [sub_self, zero_div]

theorem suzukiFragmentedHalfPlaneCarrier_anchor
    {c : ℝ} (hc : 0 < c) (ζ : ℂ) (r : ℝ) (N : ℕ) :
    suzukiFragmentedHalfPlaneCarrier ζ r N c ((c : ℂ) * I) = 0 := by
  rw [suzukiFragmentedHalfPlaneCarrier, suzukiCoalescingCayley_anchor hc,
    suzukiFragmentedDiskCarrier_zero]

theorem hasDerivAt_suzukiCoalescingCayley_anchor
    {c : ℝ} (hc : 0 < c) :
    HasDerivAt (suzukiCoalescingCayley c) (1 / (2 * (c : ℂ) * I))
      ((c : ℂ) * I) := by
  let z0 : ℂ := (c : ℂ) * I
  have hnum : HasDerivAt (fun z : ℂ => z - z0) 1 z0 :=
    (hasDerivAt_id z0).sub_const z0
  have hden : HasDerivAt (fun z : ℂ => z + z0) 1 z0 :=
    (hasDerivAt_id z0).add_const z0
  have htwo : z0 + z0 ≠ 0 := by
    dsimp [z0]
    ring_nf
    exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hc.ne') I_ne_zero) (by norm_num)
  have h := hnum.div hden htwo
  change HasDerivAt (fun z : ℂ => (z - z0) / (z + z0))
    (1 / (2 * (c : ℂ) * I)) z0
  convert! h using 1
  dsimp [z0]
  field_simp [hc.ne', I_ne_zero]
  ring

theorem two_mul_anchor_mul_deriv_suzukiFragmentedHalfPlaneCarrier
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) {c : ℝ} (hc : 0 < c) :
    2 * (c : ℂ) * I *
        deriv (suzukiFragmentedHalfPlaneCarrier ζ r N c) ((c : ℂ) * I) =
      (r : ℂ) ^ N := by
  have houter : DifferentiableAt ℂ (suzukiFragmentedDiskCarrier ζ r N) 0 := by
    unfold suzukiFragmentedDiskCarrier
    exact differentiableAt_id.mul
      ((differentiableAt_suzukiCenteredBlaschkeSection_zero hζ hr0 hr1).pow N)
  have houter' : DifferentiableAt ℂ (suzukiFragmentedDiskCarrier ζ r N)
      (suzukiCoalescingCayley c ((c : ℂ) * I)) := by
    simpa [suzukiCoalescingCayley_anchor hc] using houter
  have hcomp := houter'.hasDerivAt.comp ((c : ℂ) * I)
    (hasDerivAt_suzukiCoalescingCayley_anchor hc)
  have h := hcomp.deriv
  rw [show deriv (suzukiFragmentedHalfPlaneCarrier ζ r N c) ((c : ℂ) * I) =
      deriv (suzukiFragmentedDiskCarrier ζ r N) 0 *
        (1 / (2 * (c : ℂ) * I)) by
    change deriv
      (suzukiFragmentedDiskCarrier ζ r N ∘ suzukiCoalescingCayley c)
        ((c : ℂ) * I) = _
    simpa [suzukiCoalescingCayley_anchor hc] using h]
  rw [deriv_suzukiFragmentedDiskCarrier_zero hζ hr0 hr1]
  have hden : 2 * (c : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hc.ne')) I_ne_zero
  field_simp [hden, hc.ne']

end

end RHTower
