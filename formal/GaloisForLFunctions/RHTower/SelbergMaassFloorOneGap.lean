import GaloisForLFunctions.RHTower.SelbergMaassStripHardyGap

/-!
# No exceptional eigenvalue for `Γ(N)` with `N ≤ 25`

Let `f` be a Maass cusp form for `Γ(N)` with eigenvalue `λ ∈ (0, 1/4)`. Sum the deck
translates, write `s(y)` for the unit-strip slice mass and `g(y)` for the slice gradient, and
set `κ = 2π/N`, `a = √3/2`, `w = 1/a - 1`.

* **Hardy balance with floor one.** The ground-state inequality `g ≥ Qm + (hs)'` with
  `h = α/y - κ` holds for every `α`. Integrated over `[1, ∞)` it gives
  `α(1 - α + 2κ) ∫₁^∞ m + (κ - α) s(1) ≤ ∫₁^∞ g` (`floor_one_hardy`). For `α < κ` the
  boundary term at the floor is a gain.
* **Band trace inequality.** The vertical ground state bounds `-s' ≤ cs + g/c`. Integrating
  down from height one and against `dy/y²` over `[a, 1]` gives
  `(1 - wc) ∫_a^1 m ≤ w s(1) + (w/c) ∫_a^1 g` (`band_trace`).
* **Covering.** The high strip `[-1/2, 1/2] × (1, ∞)` lies inside the modular cell, so its
  energy is at most `λ M` (`high_le`). The whole strip above `a` carries at most twice the cell
  energy (`rect_le`) and at least the cell mass (`cell_le_rect`).

With `t = κ - α = 49/1000` and `c = 11/10` these combine to
`w q M_high + t(1 - wc) M_band ≤ w(1 + t/c) λ M`. For `κ ≥ 2π/25`, both `q = α(1 - α + 2κ)` and
`t(1 - wc)/w` exceed `(1 + t/c)/4`, which contradicts `λ < 1/4` (`closing_chain`,
`floor_one_contradiction`). Hence `Γ(N)` has no exceptional eigenvalue for `1 ≤ N ≤ 25`
(`level_le_twentyfive_no_exceptional`).
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff

namespace GaloisForLFunctions.RHTower.SelbergMaassFloorOneGap

open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassFullGradient
  SelbergMaassTraceMass SelbergMaassFullCurvatureBudget SelbergMaassCellCurvature
  SelbergMaassMean SelbergModularDomainSlices SelbergMaassCurvatureTransport
  SelbergModularStripComparison SelbergMaassStripSlice SelbergMaassStripGap
  SelbergMaassFlux SelbergMaassParseval SelbergMaassFourier SelbergMaassStripHardyGap

noncomputable section

variable (N : ℕ) {lam : Ioo (0 : ℝ) (1 / 4)}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- Horizontal gradient slice of the strip. -/
def gS (y : ℝ) : ℝ := ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), planarGradient N f (x, y)

/-- Horizontal mass slice of the strip. -/
def mS (y : ℝ) : ℝ := ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y)

theorem gS_integrable : IntegrableOn (gS N f) (Ici arcFloor) :=
  rectangle_slices_integrable (rectangle_gradient_integrable N lam f)

theorem mS_integrable : IntegrableOn (mS N f) (Ici arcFloor) :=
  rectangle_slices_integrable (rectangle_mass_integrable N lam f)

theorem gS_nonneg (y : ℝ) : 0 ≤ gS N f y :=
  setIntegral_nonneg measurableSet_Icc (fun _ _ => gradientDensity_nonneg N f _)

theorem mS_nonneg (y : ℝ) : 0 ≤ mS N f y :=
  setIntegral_nonneg measurableSet_Icc (fun _ _ => massDensity_nonneg N f _)

theorem one_ge_arcFloor : arcFloor ≤ 1 := arcHeight_le_one ⟨by norm_num, le_rfl⟩

/-- **Hardy balance with floor one.** For `0 ≤ α ≤ κ`,
`α(1 - α + 2κ) ∫₁^R m + (κ - α) s(1) - κ s(R) ≤ ∫₁^∞ g`. -/
theorem floor_one_finite (α : ℝ) (hα : 0 ≤ α) {R : ℝ} (hR : 1 ≤ R) :
    α * (1 - α + 2 * (2 * Real.pi / (N + 1 : ℕ))) * (∫ y in (1 : ℝ)..R, mS N f y) +
        (2 * Real.pi / (N + 1 : ℕ) - α) * SelbergMaassStripHardyGap.sliceMass N f 1 -
          2 * Real.pi / (N + 1 : ℕ) * SelbergMaassStripHardyGap.sliceMass N f R ≤
      ∫ y in Ioi (1 : ℝ), gS N f y := by
  set κ : ℝ := 2 * Real.pi / (N + 1 : ℕ) with hκdef
  have hκ : 0 ≤ κ := by positivity
  have hsub : Ici (1 : ℝ) ⊆ Ici arcFloor := Ici_subset_Ici.mpr one_ge_arcFloor
  have hg : IntegrableOn (gS N f) (Ici 1) := (gS_integrable N f).mono_set hsub
  have hm : IntegrableOn (mS N f) (Ici 1) := (mS_integrable N f).mono_set hsub
  let Q : ℝ → ℝ := fun y => α * (1 - α) + 2 * α * κ * y
  let h : ℝ → ℝ := fun y => α / y - κ
  let G : ℝ → ℝ := fun y => h y * SelbergMaassStripHardyGap.sliceMass N f y
  let G' : ℝ → ℝ := fun y => α * -(y ^ 2)⁻¹ * SelbergMaassStripHardyGap.sliceMass N f y +
    h y * (2 * ∑ q : Deck N, flux N (quotientForm N f q) y)
  let φ : ℝ → ℝ := fun y => gS N f y - Q y * mS N f y
  have hGd : ∀ y, 0 < y → HasDerivAt G (G' y) y := by
    intro y hy
    have hh : HasDerivAt h (α * -(y ^ 2)⁻¹) y := by
      have := ((hasDerivAt_inv hy.ne').const_mul α).sub_const κ
      simpa [h, div_eq_mul_inv] using this
    exact hh.mul (density_slice_mass_hasDerivAt N f hy)
  have hIcc : Icc 1 R ⊆ Ici (1 : ℝ) := Icc_subset_Ici_self
  have hφi : IntegrableOn φ (Icc 1 R) := by
    have hQm : IntegrableOn (fun y => Q y * mS N f y) (Icc 1 R) :=
      (hm.mono_set hIcc).continuousOn_mul (by fun_prop) isCompact_Icc
    exact (hg.mono_set hIcc).sub hQm
  have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (g := G) (g' := G')
    (φ := φ) hR
    (fun y hy => (hGd y (one_pos.trans_le hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => (hGd y (one_pos.trans hy.1)).hasDerivWithinAt) hφi
    (by
      intro y hy
      have hy0 : 0 < y := one_pos.trans hy.1
      have hs := slice_ground_state N lam f (h y) hy0
      have hgy : gS N f y = sliceGradient N f y := gslice_eq N f hy0
      have hmy : mS N f y = SelbergMaassStripHardyGap.sliceMass N f y / y ^ (2 : ℕ) := mslice_eq N f hy0
      have hid : Q y * mS N f y = (κ ^ 2 - h y ^ 2 + α / y ^ 2) * SelbergMaassStripHardyGap.sliceMass N f y := by
        rw [hmy]
        simp only [Q, h]
        field_simp
        ring
      simp only [φ, G']
      rw [hid, hgy]
      have hr : α * -(y ^ 2)⁻¹ * SelbergMaassStripHardyGap.sliceMass N f y = -(α / y ^ 2 * SelbergMaassStripHardyGap.sliceMass N f y) := by
        ring
      rw [hr]
      nlinarith [hs])
  have hG1 : G 1 = -(κ - α) * SelbergMaassStripHardyGap.sliceMass N f 1 := by
    simp only [G, h]
    ring
  have hGR : -(κ * SelbergMaassStripHardyGap.sliceMass N f R) ≤ G R := by
    have hR0 : 0 < R := one_pos.trans_le hR
    have hS := SelbergMaassStripHardyGap.sliceMass_nonneg N f R
    have : 0 ≤ α / R * SelbergMaassStripHardyGap.sliceMass N f R := mul_nonneg (div_nonneg hα hR0.le) hS
    simp only [G, h]
    nlinarith
  have hgi : IntervalIntegrable (gS N f) volume 1 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr (hg.mono_set hIcc)
  have hQmi : IntervalIntegrable (fun y => Q y * mS N f y) volume 1 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr
      ((hm.mono_set hIcc).continuousOn_mul (by fun_prop) isCompact_Icc)
  have hmi : IntervalIntegrable (mS N f) volume 1 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr (hm.mono_set hIcc)
  have hsplit : (∫ y in (1 : ℝ)..R, φ y) = (∫ y in (1 : ℝ)..R, gS N f y) -
      ∫ y in (1 : ℝ)..R, Q y * mS N f y :=
    intervalIntegral.integral_sub hgi hQmi
  have hlow : α * (1 - α + 2 * κ) * (∫ y in (1 : ℝ)..R, mS N f y) ≤
      ∫ y in (1 : ℝ)..R, Q y * mS N f y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR (hmi.const_mul _) hQmi
    intro y hy
    have hQ : α * (1 - α + 2 * κ) ≤ Q y := by
      simp only [Q]
      have : α * κ * 1 ≤ α * κ * y := mul_le_mul_of_nonneg_left hy.1 (mul_nonneg hα hκ)
      nlinarith
    exact mul_le_mul_of_nonneg_right hQ (mS_nonneg N f y)
  have hgle : (∫ y in (1 : ℝ)..R, gS N f y) ≤ ∫ y in Ioi (1 : ℝ), gS N f y := by
    rw [intervalIntegral.integral_of_le hR]
    exact setIntegral_mono_set (hg.mono_set Ioi_subset_Ici_self)
      (Eventually.of_forall (gS_nonneg N f)) (Ioc_subset_Ioi_self.eventuallyLE)
  rw [hsplit, hG1] at hmain
  linarith

/-- **Hardy balance with floor one**, at infinite height:
`α(1 - α + 2κ) ∫₁^∞ m + (κ - α) s(1) ≤ ∫₁^∞ g`. -/
theorem floor_one_hardy (α : ℝ) (hα : 0 ≤ α) :
    α * (1 - α + 2 * (2 * Real.pi / (N + 1 : ℕ))) * (∫ y in Ioi (1 : ℝ), mS N f y) +
        (2 * Real.pi / (N + 1 : ℕ) - α) * SelbergMaassStripHardyGap.sliceMass N f 1 ≤
      ∫ y in Ioi (1 : ℝ), gS N f y := by
  have hsub : Ioi (1 : ℝ) ⊆ Ici arcFloor := Ioi_subset_Ici one_ge_arcFloor
  have hm : IntegrableOn (mS N f) (Ioi 1) := (mS_integrable N f).mono_set hsub
  have hlim : Tendsto (fun R => α * (1 - α + 2 * (2 * Real.pi / (N + 1 : ℕ))) *
      (∫ y in (1 : ℝ)..R, mS N f y) +
        (2 * Real.pi / (N + 1 : ℕ) - α) * SelbergMaassStripHardyGap.sliceMass N f 1 -
          2 * Real.pi / (N + 1 : ℕ) * SelbergMaassStripHardyGap.sliceMass N f R) atTop
      (𝓝 (α * (1 - α + 2 * (2 * Real.pi / (N + 1 : ℕ))) * (∫ y in Ioi (1 : ℝ), mS N f y) +
        (2 * Real.pi / (N + 1 : ℕ) - α) * SelbergMaassStripHardyGap.sliceMass N f 1 -
          2 * Real.pi / (N + 1 : ℕ) * 0)) :=
    ((((intervalIntegral_tendsto_integral_Ioi 1 hm tendsto_id).const_mul _).add_const _).sub
      ((sliceMass_tendsto N f).const_mul _))
  rw [mul_zero, sub_zero] at hlim
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact floor_one_finite N f α hα hR

/-- The vertical ground state bounds the downward slice-mass derivative:
`-s'(y) ≤ c s(y) + g(y)/c` for every `c > 0`. -/
theorem neg_deriv_le (c : ℝ) (hc : 0 < c) {y : ℝ} (hy : 0 < y) :
    -(2 * ∑ q : Deck N, flux N (quotientForm N f q) y) ≤
      c * SelbergMaassStripHardyGap.sliceMass N f y + sliceGradient N f y / c := by
  rw [SelbergMaassStripHardyGap.sliceMass, density_integral_eq_sum_mass N f hy, sliceGradient,
    gradient_integral_eq_sum N f hy, Finset.mul_sum, Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  have h1 := vertical_ground_state N (quotientForm N f q) (-c) hy
  have h2 := horizontalEnergy_ge_first_frequency N lam (quotientForm N f q) hy
  have h3 := mass_nonneg N (quotientForm N f q) hy
  have hH : 0 ≤ horizontalEnergy N (quotientForm N f q) y :=
    le_trans (mul_nonneg (sq_nonneg _) h3) h2
  rw [gradientEnergy_eq_add]
  rw [show c * mass N (quotientForm N f q) y +
      (horizontalEnergy N (quotientForm N f q) y + verticalEnergy N (quotientForm N f q) y) / c =
      (c ^ 2 * mass N (quotientForm N f q) y + horizontalEnergy N (quotientForm N f q) y +
        verticalEnergy N (quotientForm N f q) y) / c by field_simp; ring]
  rw [le_div_iff₀ hc]
  nlinarith

theorem integral_inv_sq_band :
    (∫ y in arcFloor..1, (y ^ (2 : ℕ))⁻¹) = 1 / arcFloor - 1 := by
  have ha := arcFloor_pos
  have hderiv : ∀ y ∈ uIcc arcFloor 1, HasDerivAt (fun y : ℝ => -y⁻¹) ((y ^ (2 : ℕ))⁻¹) y := by
    intro y hy
    rw [uIcc_of_le one_ge_arcFloor] at hy
    have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
    have := (hasDerivAt_inv hy0).neg
    rw [neg_neg] at this
    exact this
  have hcont : ContinuousOn (fun y : ℝ => (y ^ (2 : ℕ))⁻¹) (uIcc arcFloor 1) := by
    rw [uIcc_of_le one_ge_arcFloor]
    exact continuousOn_of_forall_continuousAt fun y hy =>
      (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (ha.trans_le hy.1).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [inv_one]
  rw [one_div]
  ring

/-- **Band trace inequality.** On the band `[√3/2, 1]`,
`(1 - w₀c) M_band ≤ w₀ s(1) + (w₀/c) E_band` with `w₀ = 1/a - 1` and any `c > 0`. -/
theorem band_trace (c : ℝ) (hc : 0 < c) :
    (1 - (1 / arcFloor - 1) * c) * (∫ y in arcFloor..1, mS N f y) ≤
      (1 / arcFloor - 1) * SelbergMaassStripHardyGap.sliceMass N f 1 +
        (1 / arcFloor - 1) / c * ∫ y in arcFloor..1, gS N f y := by
  set a := arcFloor with hadef
  have ha : 0 < a := arcFloor_pos
  have ha1 : a ≤ 1 := one_ge_arcFloor
  set s := SelbergMaassStripHardyGap.sliceMass N f with hsdef
  have hsd : ∀ y, 0 < y → HasDerivAt s (2 * ∑ q : Deck N, flux N (quotientForm N f q) y) y :=
    fun y hy => density_slice_mass_hasDerivAt N f hy
  have hscont : ContinuousOn s (Icc a 1) := fun y hy =>
    (hsd y (ha.trans_le hy.1)).continuousAt.continuousWithinAt
  have hs0 : ∀ y, 0 ≤ s y := SelbergMaassStripHardyGap.sliceMass_nonneg N f
  have hgI : IntegrableOn (gS N f) (Icc a 1) := (gS_integrable N f).mono_set Icc_subset_Ici_self
  have hmI : IntegrableOn (mS N f) (Icc a 1) := (mS_integrable N f).mono_set Icc_subset_Ici_self
  let φ : ℝ → ℝ := fun u => c * s u + gS N f u / c
  have hφI : IntegrableOn φ (Icc a 1) :=
    ((hscont.integrableOn_compact isCompact_Icc).const_mul c).add (hgI.div_const c)
  have hφ0 : ∀ u, 0 ≤ φ u := fun u =>
    add_nonneg (mul_nonneg hc.le (hs0 u)) (div_nonneg (gS_nonneg N f u) hc.le)
  set K := ∫ u in a..1, φ u with hKdef
  -- pointwise trace bound
  have hpt : ∀ y ∈ Icc a 1, s y ≤ s 1 + K := by
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      (g := fun u => -s u) (g' := fun u => -(2 * ∑ q : Deck N, flux N (quotientForm N f q) u))
      (φ := φ) hy.2
      (fun u hu => (hsd u (hy0.trans_le hu.1)).neg.continuousAt.continuousWithinAt)
      (fun u hu => (hsd u (hy0.trans hu.1)).neg.hasDerivWithinAt)
      (hφI.mono_set (Icc_subset_Icc hy.1 le_rfl))
      (by
        intro u hu
        have hu0 : 0 < u := hy0.trans hu.1
        have h1 := neg_deriv_le N f c hc hu0
        have h2 : gS N f u = sliceGradient N f u := gslice_eq N f hu0
        simp only [φ, h2]
        exact h1)
    have hmono : (∫ u in y..1, φ u) ≤ K := by
      apply intervalIntegral.integral_mono_interval hy.1 hy.2 le_rfl
      · exact Eventually.of_forall hφ0
      · exact (intervalIntegrable_iff_integrableOn_Icc_of_le ha1).mpr hφI
    linarith
  -- integrate against dy/y²
  have hinv := integral_inv_sq_band
  have hmass : (∫ y in a..1, mS N f y) ≤ (s 1 + K) * (1 / a - 1) := by
    rw [← hinv, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ha1
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ha1).mpr hmI)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ha1]
      exact continuousOn_const.mul (continuousOn_of_forall_continuousAt fun y hy =>
        (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (ha.trans_le hy.1).ne'))
    · intro y hy
      have hy0 : 0 < y := ha.trans_le hy.1
      rw [show mS N f y = s y / y ^ (2 : ℕ) from mslice_eq N f hy0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hpt y hy) (inv_nonneg.mpr (sq_nonneg y))
  -- K in terms of the band mass and energy
  have hsI : IntervalIntegrable s volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha1).mpr (hscont.integrableOn_compact isCompact_Icc)
  have hgI' : IntervalIntegrable (gS N f) volume a 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha1).mpr hgI
  have hK : K = c * (∫ u in a..1, s u) + (∫ u in a..1, gS N f u) / c := by
    rw [hKdef, intervalIntegral.integral_add (hsI.const_mul c) (hgI'.div_const c),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  have hsm : (∫ u in a..1, s u) ≤ ∫ u in a..1, mS N f u := by
    apply intervalIntegral.integral_mono_on ha1 hsI
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ha1).mpr hmI)
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    rw [show mS N f y = s y / y ^ (2 : ℕ) from mslice_eq N f hy0]
    have hy2 : y ^ (2 : ℕ) ≤ 1 := by nlinarith [hy.2]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hs0 y]
  have hw : 0 ≤ 1 / a - 1 := by rw [sub_nonneg, le_div_iff₀ ha]; linarith
  rw [hK] at hmass
  have := mul_le_mul_of_nonneg_left hsm (mul_nonneg hw hc.le)
  have e : (1 / a - 1) / c * (∫ u in a..1, gS N f u) =
      (1 / a - 1) * ((∫ u in a..1, gS N f u) / c) := by ring
  rw [e]
  nlinarith

/-- Splitting the strip integral at height one. -/
theorem split_at_one {F : ℝ → ℝ} (hF : IntegrableOn F (Ici arcFloor)) :
    (∫ y in Ici arcFloor, F y) = (∫ y in arcFloor..1, F y) + ∫ y in Ioi (1 : ℝ), F y := by
  have hdisj : Disjoint (Ioc arcFloor 1) (Ioi (1 : ℝ)) :=
    disjoint_left.mpr fun x hx hx' => (not_lt.mpr hx.2) (show (1 : ℝ) < x from hx')
  rw [integral_Ici_eq_integral_Ioi, ← Ioc_union_Ioi_eq_Ioi one_ge_arcFloor,
    setIntegral_union (s := Ioc arcFloor 1) (t := Ioi (1 : ℝ)) hdisj measurableSet_Ioi
      (hF.mono_set (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self))
      (hF.mono_set (Ioi_subset_Ici one_ge_arcFloor)),
    intervalIntegral.integral_of_le one_ge_arcFloor]

/-- The high strip `[-1/2, 1/2] × (1, ∞)`. -/
def highStrip : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi 1

theorem highStrip_subset_rectangle : highStrip ⊆ rectangle := fun _ hp =>
  ⟨hp.1, one_ge_arcFloor.trans (le_of_lt hp.2)⟩

theorem highStrip_subset_full : highStrip ⊆ fullDomain := fun _ hp =>
  ⟨hp.1, (arcHeight_le_one hp.1).trans (le_of_lt hp.2)⟩

/-- Fubini on the high strip. -/
theorem high_eq : (∫ y in Ioi (1 : ℝ), gS N f y) = ∫ p in highStrip, planarGradient N f p := by
  have hH : MeasurableSet highStrip := measurableSet_Icc.prod measurableSet_Ioi
  have hi : IntegrableOn (highStrip.indicator (planarGradient N f)) rectangle :=
    (rectangle_gradient_integrable N lam f).indicator hH
  have h := rectangle_integral hi
  rw [setIntegral_indicator hH, inter_eq_right.mpr highStrip_subset_rectangle] at h
  rw [h]
  have hslice : ∀ y, (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), highStrip.indicator (planarGradient N f) (x, y)) =
      (Ioi (1 : ℝ)).indicator (gS N f) y := by
    intro y
    by_cases hy : y ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hy]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact indicator_of_mem (show (x, y) ∈ highStrip from ⟨hx, hy⟩) _
    · rw [indicator_of_notMem hy]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x _
      exact indicator_of_notMem (f := planarGradient N f) (fun (h' : (x, y) ∈ highStrip) => hy h'.2)
  simp_rw [hslice]
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ici one_ge_arcFloor)]

/-- The high strip lies in the modular cell, so its energy is at most `λ M_F`. -/
theorem high_le : (∫ y in Ioi (1 : ℝ), gS N f y) ≤
    (lam : ℝ) * ∫ p in fullDomain, massDensity N f p := by
  rw [high_eq N f, ← full_gradient_identity N lam f]
  exact setIntegral_mono_set (full_gradient_integrable N lam f)
    (Eventually.of_forall fun p => gradientDensity_nonneg N f _)
    (Eventually.of_forall highStrip_subset_full)

/-- The strip energy is at most twice the cell energy. -/
theorem rect_le : (∫ y in Ici arcFloor, gS N f y) ≤
    2 * ((lam : ℝ) * ∫ p in fullDomain, massDensity N f p) := by
  have hupper := integral_strip_le_twice (cell_gradient_integrable N lam f)
    (hyperbolicGradient_nonneg N f) (hyperbolicGradient_invariant N f S)
  rw [strip_gradient_identity, cell_gradient_identity,
    rectangle_integral (rectangle_gradient_integrable N lam f)] at hupper
  exact hupper

/-- The cell mass is at most the strip mass. -/
theorem cell_le_rect : (∫ p in fullDomain, massDensity N f p) ≤ ∫ y in Ici arcFloor, mS N f y := by
  have hmass := setIntegral_mono_set
    (integrable_strip (cell_mass_integrable N lam f) (density_invariant N f S))
    (Eventually.of_forall (density_nonneg N f)) (Eventually.of_forall fd_subset_strip)
  change (∫ z : ℍ in fd, density N f z) ≤ ∫ z in strip, density N f z at hmass
  rw [cell_mass_identity, strip_mass_identity,
    rectangle_integral (rectangle_mass_integrable N lam f)] at hmass
  exact hmass

/-- The closing inequality chain with `t = 49/1000`, `c = 11/10`: the floor-one Hardy balance
`qM_h + t s₁ ≤ E_h`, the band trace inequality `(1 - wc)M_b ≤ w s₁ + (w/c)E_b`, the covering bounds
`E_b + E_h ≤ 2λM`, `E_h ≤ λM`, `M ≤ M_b + M_h` and `q ≥ (1 + t/c)/4`,
`t(1 - wc) ≥ w(1 + t/c)/4` are incompatible with `λ < 1/4` and `M > 0`. -/
theorem closing_chain {w q L M Mh Mb Eh Eb s1 : ℝ} (hw0 : 0 < w)
    (hq : (1 + 49 / 1000 / (11 / 10)) / 4 ≤ q)
    (hβ : w * ((1 + 49 / 1000 / (11 / 10)) / 4) ≤ 49 / 1000 * (1 - w * (11 / 10)))
    (hH : q * Mh + 49 / 1000 * s1 ≤ Eh)
    (hB : (1 - w * (11 / 10)) * Mb ≤ w * s1 + w / (11 / 10) * Eb)
    (hR : Eb + Eh ≤ 2 * (L * M)) (hHi : Eh ≤ L * M) (hM : M ≤ Mb + Mh) (hpos : 0 < M)
    (hL : L < 1 / 4) (hMh : 0 ≤ Mh) (hMb : 0 ≤ Mb) : False := by
  have h1 := mul_le_mul_of_nonneg_left hH hw0.le
  have h2 := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ 49 / 1000 by norm_num)
  have hEbR : Eb ≤ 2 * (L * M) - Eh := by linarith
  have h3 : 49 / 1000 * (w / (11 / 10) * Eb) ≤ 49 / 1000 * (w / (11 / 10) * (2 * (L * M) - Eh)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEbR (by positivity)) (by norm_num)
  have h4 : w * (1 - 49 / 1000 / (11 / 10)) * Eh ≤ w * (1 - 49 / 1000 / (11 / 10)) * (L * M) :=
    mul_le_mul_of_nonneg_left hHi (mul_nonneg hw0.le (by norm_num))
  have hchain : w * q * Mh + 49 / 1000 * (1 - w * (11 / 10)) * Mb ≤
      w * (1 + 49 / 1000 / (11 / 10)) * (L * M) := by
    nlinarith
  have k1 : w * ((1 + 49 / 1000 / (11 / 10)) / 4) * Mh ≤ w * q * Mh :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hw0.le) hMh
  have k2 : w * ((1 + 49 / 1000 / (11 / 10)) / 4) * Mb ≤ 49 / 1000 * (1 - w * (11 / 10)) * Mb :=
    mul_le_mul_of_nonneg_right hβ hMb
  have hEF : L * M < M / 4 := by nlinarith
  have hup : w * (1 + 49 / 1000 / (11 / 10)) * (L * M) <
      w * (1 + 49 / 1000 / (11 / 10)) * (M / 4) :=
    mul_lt_mul_of_pos_left hEF (mul_pos hw0 (by norm_num))
  have hfin : w * (1 + 49 / 1000 / (11 / 10)) * (M / 4) ≤
      w * ((1 + 49 / 1000 / (11 / 10)) / 4) * (Mh + Mb) := by
    have e : w * (1 + 49 / 1000 / (11 / 10)) * (M / 4) =
        w * ((1 + 49 / 1000 / (11 / 10)) / 4) * M := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hw0.le (by norm_num))
  nlinarith

include f in
/-- **No exceptional eigenvalue at principal level at most 25.** The floor-one Hardy balance,
the band trace inequality and the strip/cell comparisons, with `t = 49/1000`, `c = 11/10` and
`α = κ - t`, satisfy the closing chain for `κ = 2π/(N+1) ≥ 2π/25`. -/
theorem floor_one_contradiction (hN : N + 1 ≤ 25) : False := by
  have ha2 : arcFloor ^ (2 : ℕ) = 3 / 4 := arcFloor_sq
  have ha0 : 0 < arcFloor := arcFloor_pos
  have ha866 : (866 / 1000 : ℝ) ≤ arcFloor := by nlinarith
  have ha1 : arcFloor < 1 := by nlinarith
  have hw0 : 0 < 1 / arcFloor - 1 := by
    rw [sub_pos, lt_div_iff₀ ha0]; linarith
  have hw1 : 1 / arcFloor - 1 ≤ 1548 / 10000 := by
    rw [sub_le_iff_le_add, div_le_iff₀ ha0]; nlinarith
  have hN0 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hN25 : ((N + 1 : ℕ) : ℝ) ≤ 25 := by exact_mod_cast hN
  have hκ : (2513 / 10000 : ℝ) ≤ 2 * Real.pi / (N + 1 : ℕ) := by
    rw [le_div_iff₀ hN0]
    have := Real.pi_gt_d6
    nlinarith
  have hα : 0 ≤ 2 * Real.pi / (N + 1 : ℕ) - 49 / 1000 := by linarith
  have hH := floor_one_hardy N f _ hα
  rw [show 2 * Real.pi / (N + 1 : ℕ) - (2 * Real.pi / (N + 1 : ℕ) - 49 / 1000) = 49 / 1000 by ring]
    at hH
  have hB := band_trace N f (11 / 10) (by norm_num)
  have hsE := split_at_one (gS_integrable N f)
  have hsM := split_at_one (mS_integrable N f)
  have hR := rect_le N f
  have hHi := high_le N f
  have hM := cell_le_rect N f
  refine closing_chain hw0 ?_ ?_ hH hB (by linarith) hHi (by linarith) (full_mass_pos N lam f)
    lam.2.2 (setIntegral_nonneg measurableSet_Ioi fun y _ => mS_nonneg N f y)
    (intervalIntegral.integral_nonneg one_ge_arcFloor fun y _ => mS_nonneg N f y)
  · nlinarith
  · nlinarith

/-- **Selberg's eigenvalue conjecture for `Γ(N+1)`, `N + 1 ≤ 25`.** -/
theorem level_le_twentyfive_no_exceptional (N : ℕ) (hN : N + 1 ≤ 25) (l : Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (l : ℝ)) :=
  ⟨fun g => floor_one_contradiction N g hN⟩

end

end GaloisForLFunctions.RHTower.SelbergMaassFloorOneGap
