import GaloisForLFunctions.RHTower.WeilProducerZetaQuotientBohrRecurrence
import GaloisForLFunctions.RHTower.FiniteDirichletCriticalNonannihilation
import GaloisForLFunctions.BlackHoleRingdown.TheInverseXiContour
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# A factor with a Dirichlet series is pure

A factor of `ξ` with a Dirichlet series is a function `F`, given by an absolutely convergent
Dirichlet series on a right half-plane and bounded and holomorphic on `Re s > x`, whose zeros there
are zeros of `ξ`. This module shows that such a factor has all its zeros on the critical line. The
zeros of `ζ` off the line are the zeros of no bounded Dirichlet series: the exceptional set has no
arithmetic constituent of this kind.

* `exists_thick_zero_shifts_of_almostPeriodic`, `exists_thick_zero_shifts`: a zero `ρ₀` of `F`
  recurs. `F` is almost periodic on closed substrips (Bohr), so along a relatively dense set of
  shifts `τ` the minimum modulus principle gives a zero in the disc about `ρ₀ + iτ`, and a whole
  interval of shifts carries a zero into the larger disc. In the same way a lower bound on one
  horizontal segment recurs (`exists_good_heights_of_almostPeriodic`).
* `exists_zetaZeroShiftSet_density_zero`: for `ρ₀` in the open strip off the line, the shifts that
  carry a zero of `ζ` into a small disc about `ρ₀ + iτ` have density zero; right of the line this is
  the zero density estimate `N(σ, T) = o(T)`, left of it the reflection `s ↦ 1 - s̄`.
* `exists_zero_not_xi_zero_of_re_ne_half`: hence a bounded Dirichlet series with a zero off the
  critical line has a zero that `ξ` does not have.
* `re_eq_half_of_zeros_subset_xi`: a factor with a Dirichlet series is pure.
* `exists_zero_dirichletPolynomial_not_xi_zero`,
  `re_eq_half_of_dirichletPolynomial_zeros_subset_xi`: a Dirichlet polynomial whose zeros are zeros
  of `ξ` has all its zeros on the critical line, on both sides of which it is bounded.
-/

open Complex Filter Topology Set Metric MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

/-! ### Recurrence of a zero -/

/-- **A zero of an almost periodic function recurs.** Let `F` be holomorphic on `Re z > x`, not
identically zero, and almost periodic on a strip about the line through a zero `ρ₀`. Every interval
of some length `L` contains a shift `τ` such that each `t` within `d` of `τ` carries a zero of `F`
into the disc of radius `r` about `ρ₀ + it`: an almost period carries a zero into a small disc by
the minimum modulus principle, and a whole interval of shifts carries it into the larger disc. -/
theorem exists_thick_zero_shifts_of_almostPeriodic {F : ℂ → ℂ} {x : ℝ}
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hFne : ∃ z₁ : ℂ, x < z₁.re ∧ F z₁ ≠ 0)
    {ρ₀ : ℂ} (hρx : x < ρ₀.re) (hFρ : F ρ₀ = 0) {R : ℝ} (hR : 0 < R)
    (hAP : IsStripAlmostPeriodicOn F ρ₀.re R) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℝ, 0 < L ∧ ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, ∃ τ ∈ Icc a (a + L),
      Ioo (τ - d) (τ + d) ⊆
        {t : ℝ | ∃ z ∈ ball ρ₀ r, x < (z + t * I).re ∧ F (z + t * I) = 0} := by
  have hUopen : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {z : ℂ | x < z.re} := (convex_halfSpace_re_gt x).isPreconnected
  have han : AnalyticOnNhd ℂ F {z : ℂ | x < z.re} := hF.analyticOnNhd hUopen
  -- the zero is isolated
  have hne : ∀ᶠ z in 𝓝[≠] ρ₀, F z ≠ 0 := by
    refine (han ρ₀ hρx).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => ?_
    obtain ⟨z₁, hz₁, hz₁0⟩ := hFne
    exact hz₁0 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hρx h hz₁)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r' : ℝ := min (r₁ / 2) (min r (min ((ρ₀.re - x) / 2) R)) with hrdef
  have hr' : 0 < r' := lt_min (by linarith) (lt_min hr (lt_min (by linarith) hR))
  have hrr₁ : r' < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hr'r : r' ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hr4 : r' ≤ (ρ₀.re - x) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr5 : r' ≤ R := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set ρ : ℝ := r' / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  -- the zero-free circle and its floor
  have hsphU : ∀ z ∈ closedBall ρ₀ ρ, x < z.re := by
    intro z hz
    have h := abs_le.mp ((abs_re_le_norm (z - ρ₀)).trans (mem_closedBall_iff_norm.mp hz))
    rw [sub_re] at h
    linarith [h.1]
  have hsph : ∀ z ∈ sphere ρ₀ ρ, F z ≠ 0 := by
    intro z hz
    have hd : dist z ρ₀ = ρ := mem_sphere.mp hz
    have hzρ : z ≠ ρ₀ := by
      intro h
      rw [h, dist_self] at hd
      linarith
    exact hball (by rw [hd]; linarith) hzρ
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere ρ₀ ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le)
    (hF.continuousOn.mono fun z hz => hsphU z (sphere_subset_closedBall hz)).norm
  have hm0 : 0 < ‖F z₁‖ := norm_pos_iff.mpr (hsph z₁ hz₁)
  have hm : ∀ z ∈ sphere ρ₀ ρ, ‖F z₁‖ ≤ ‖F z‖ := fun z hz => isMinOn_iff.mp hmin z hz
  -- almost periods to the precision of the floor
  obtain ⟨L, hL, hτ⟩ := hAP (‖F z₁‖ / 3) (by positivity)
  have hstrip : ∀ z ∈ closedBall ρ₀ ρ, |z.re - ρ₀.re| ≤ R := by
    intro z hz
    have h := (abs_re_le_norm (z - ρ₀)).trans (mem_closedBall_iff_norm.mp hz)
    rw [sub_re] at h
    linarith
  refine ⟨L, hL, ρ, hρ, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτF⟩ := hτ a
  refine ⟨τ, hτmem, fun t ht => ?_⟩
  -- an almost period carries a zero, by the minimum modulus principle
  have hdiff : DifferentiableOn ℂ (fun s => F (s + τ * I)) (closedBall ρ₀ ρ) := by
    intro s hs
    have hs' : x < (s + τ * I).re := by simpa using hsphU s hs
    exact (((hF _ hs').differentiableAt (hUopen.mem_nhds hs')).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  obtain ⟨z, hz, hz0⟩ := DeBruijn.exists_zero_of_norm_lt_sphere_on hρ hdiff fun z hz => by
    have h1 := hτF ρ₀ (hstrip ρ₀ (mem_closedBall_self hρ.le))
    rw [hFρ, sub_zero] at h1
    have h2 := hτF z (hstrip z (sphere_subset_closedBall hz))
    have h3 := hm z hz
    have h4 := norm_sub_norm_le (F z) (F (z + τ * I))
    rw [norm_sub_rev] at h4
    show ‖F (ρ₀ + τ * I)‖ < ‖F (z + τ * I)‖
    linarith
  have hzx : x < (z + τ * I).re := by simpa using hsphU z (ball_subset_closedBall hz)
  have hpt : z - ((t - τ : ℝ) : ℂ) * I + (t : ℂ) * I = z + τ * I := by
    push_cast
    ring
  refine ⟨z - ((t - τ : ℝ) : ℂ) * I, ?_, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    calc ‖z - ((t - τ : ℝ) : ℂ) * I - ρ₀‖ ≤ ‖z - ρ₀‖ + ‖((t - τ : ℝ) : ℂ) * I‖ := by
          rw [show z - ((t - τ : ℝ) : ℂ) * I - ρ₀ = (z - ρ₀) - ((t - τ : ℝ) : ℂ) * I by ring]
          exact norm_sub_le _ _
      _ < ρ + ρ := by
          refine add_lt_add (mem_ball_iff_norm.mp hz) ?_
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact abs_sub_lt_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      _ = r' := by rw [hρdef]; ring
      _ ≤ r := hr'r
  · rw [hpt]
    exact hzx
  · rw [hpt]
    exact hz0

/-- **A zero of a bounded Dirichlet series recurs.** Every interval of some length `L` contains a
shift `τ` such that each `t` within `d` of `τ` carries a zero of `F` into the disc of radius `r`
about `ρ₀ + it`. -/
theorem exists_thick_zero_shifts {f : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M : ℝ}
    (hsum : LSeriesSummable f (u₀ : ℂ)) (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re})
    (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M) (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries f z)
    (hFne : ∃ z₁ : ℂ, x < z₁.re ∧ F z₁ ≠ 0) {ρ₀ : ℂ} (hρx : x < ρ₀.re) (hFρ : F ρ₀ = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ L : ℝ, 0 < L ∧ ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, ∃ τ ∈ Icc a (a + L),
      Ioo (τ - d) (τ + d) ⊆
        {t : ℝ | ∃ z ∈ ball ρ₀ r, x < (z + t * I).re ∧ F (z + t * I) = 0} := by
  set R : ℝ := min ((ρ₀.re - x) / 2) 1 with hRdef
  have hR0 : 0 < R := lt_min (by linarith) one_pos
  have hR1 : R ≤ 1 := min_le_right _ _
  have hR2 : R ≤ (ρ₀.re - x) / 2 := min_le_left _ _
  have hu1 : ρ₀.re + 1 ≤ max (u₀ + 1) (ρ₀.re + 1) := le_max_right _ _
  -- Bohr: almost periodicity on the strip `Re ρ₀ − R ≤ Re z ≤ max (u₀ + 1) (Re ρ₀ + 1)`
  have hAP : IsStripAlmostPeriodicOn F ρ₀.re R := by
    intro ε hε
    obtain ⟨L, hL, hτ⟩ := GaloisForLFunctions.isStripAlmostPeriodicOn_of_bounded_LSeries
      (x := x) (l' := ρ₀.re - R) (u := max (u₀ + 1) (ρ₀.re + 1)) (by linarith) (by linarith)
      (by linarith [le_max_left (u₀ + 1) (ρ₀.re + 1)]) hsum hF hM hFL ε hε
    refine ⟨L, hL, fun a => ?_⟩
    obtain ⟨τ, hτmem, hτF⟩ := hτ a
    refine ⟨τ, hτmem, fun z hz => hτF z ?_⟩
    have h := abs_le.mp hz
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  exact exists_thick_zero_shifts_of_almostPeriodic hF hFne hρx hFρ hR0 hAP hr

/-- **A lower bound on a horizontal segment recurs.** If `F` is almost periodic on the strip
`|Re z − σ| ≤ R` and does not vanish on the segment of the strip at one height `T₀`, then
`‖F‖ ≥ μ > 0` on the segments at heights met in every interval of a fixed length. -/
theorem exists_good_heights_of_almostPeriodic {F : ℂ → ℂ} (hF : Continuous F) {σ R T₀ : ℝ}
    (hAP : IsStripAlmostPeriodicOn F σ R)
    (hseg : ∀ x : ℝ, |x - σ| ≤ R → F ((x : ℂ) + T₀ * I) ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ L : ℝ, ∀ y : ℝ, ∃ T ∈ Icc y (y + L), ∀ z : ℂ, |z.re - σ| ≤ R →
      z.im = T → μ ≤ ‖F z‖ := by
  rcases lt_or_ge R 0 with hR | hR
  · exact ⟨1, one_pos, 0, fun y => ⟨y, ⟨le_rfl, by linarith⟩, fun z hz _ =>
      absurd ((abs_nonneg _).trans hz) (not_le.mpr hR)⟩⟩
  have hmem : ∀ x : ℝ, |x - σ| ≤ R ↔ x ∈ Icc (σ - R) (σ + R) := fun x => by
    rw [abs_le, mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hcont : Continuous fun x : ℝ => ‖F ((x : ℂ) + T₀ * I)‖ :=
    (hF.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + T₀ * I)).norm
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : σ - R ≤ σ + R)) (hcont.continuousOn (s := Icc (σ - R) (σ + R)))
  have hm₀pos : 0 < ‖F ((x₀ : ℂ) + T₀ * I)‖ := norm_pos_iff.mpr (hseg x₀ ((hmem x₀).mpr hx₀))
  obtain ⟨L, -, hτ⟩ := hAP (‖F ((x₀ : ℂ) + T₀ * I)‖ / 2) (by positivity)
  refine ⟨_, half_pos hm₀pos, L, fun y => ?_⟩
  obtain ⟨τ, hτmem, hτD⟩ := hτ (y - T₀)
  refine ⟨T₀ + τ, ⟨by linarith [hτmem.1], by linarith [hτmem.2]⟩, fun z hz hzT => ?_⟩
  have hzform : z = ((z.re : ℝ) : ℂ) + T₀ * I + τ * I := by
    apply Complex.ext <;> simp [hzT]
  have h1 := hτD (((z.re : ℝ) : ℂ) + T₀ * I) (by simpa using hz)
  have h2 := isMinOn_iff.mp hmin z.re ((hmem z.re).mp hz)
  have h3 := norm_sub_norm_le (F (((z.re : ℝ) : ℂ) + T₀ * I))
    (F (((z.re : ℝ) : ℂ) + T₀ * I + τ * I))
  rw [norm_sub_rev] at h3
  rw [hzform]
  linarith

/-! ### Zeros of `ζ` off the line have density zero, on both sides -/

/-- The zeros of `ζ` in the open strip are symmetric under `s ↦ 1 - s̄`. -/
theorem riemannZeta_one_sub_conj_eq_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1)
    (hw : riemannZeta w = 0) : riemannZeta (1 - conj w) = 0 := by
  have hne : ∀ n : ℕ, w ≠ -n := fun n h => by
    rw [h] at h0
    simp at h0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw1 : w ≠ 1 := fun h => by
    rw [h, Complex.one_re] at h1
    exact lt_irrefl _ h1
  have h := riemannZeta_one_sub hne hw1
  rw [hw, mul_zero] at h
  have hc : (1 : ℂ) - conj w = conj (1 - w) := by simp
  rw [hc, riemannZeta_conj, h, map_zero]

/-- The shifts carrying a zero into a disc are those of the reflected disc. -/
theorem zetaZeroShiftSet_subset_reflect {ρ₀ : ℂ} {r : ℝ} (hr : r ≤ ρ₀.re) (hr1 : ρ₀.re + r ≤ 1) :
    zetaZeroShiftSet ρ₀ r ⊆ zetaZeroShiftSet (1 - conj ρ₀) r := by
  rintro τ ⟨z, hz, hζ⟩
  have h := abs_lt.mp ((abs_re_le_norm (z - ρ₀)).trans_lt (mem_ball_iff_norm.mp hz))
  rw [sub_re] at h
  refine ⟨1 - conj z, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm,
      show (1 - conj z) - (1 - conj ρ₀) = -conj (z - ρ₀) by rw [map_sub]; ring, norm_neg,
      RCLike.norm_conj]
    exact mem_ball_iff_norm.mp hz
  · have hw := riemannZeta_one_sub_conj_eq_zero (w := z + τ * I)
      (by simp; linarith [h.1]) (by simp; linarith [h.2]) hζ
    have hpt : (1 : ℂ) - conj (z + τ * I) = 1 - conj z + τ * I := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rwa [hpt] at hw

/-- **Zero shifts have density zero on both sides of the line.** -/
theorem exists_zetaZeroShiftSet_density_zero {ρ₀ : ℂ} (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1)
    (hne : ρ₀.re ≠ 1 / 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ κ : ℝ, 0 < κ →
      ∀ᶠ T in atTop, volume (zetaZeroShiftSet ρ₀ r ∩ Icc 0 T) ≤ ENNReal.ofReal (κ * T) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- left of the line: reflect to the right
    have hre : (1 - conj ρ₀).re = 1 - ρ₀.re := by simp
    have hrpos : 0 < min ((1 / 2 - ρ₀.re) / 2) (ρ₀.re / 2) := lt_min (by linarith) (by linarith)
    refine ⟨_, hrpos, fun κ hκ => ?_⟩
    have hup := zetaZeroShiftSet_density_zero (ρ₀ := 1 - conj ρ₀) hrpos
      (by rw [hre]; exact (min_le_left _ _).trans (le_of_eq (by ring)))
      (by rw [hre]; exact (min_le_right _ _).trans (le_of_eq (by ring))) hκ
    have hmr := min_le_right ((1 / 2 - ρ₀.re) / 2) (ρ₀.re / 2)
    filter_upwards [hup] with T hT
    exact (measure_mono (inter_subset_inter_left _
      (zetaZeroShiftSet_subset_reflect (by linarith) (by linarith)))).trans hT
  · exact ⟨_, lt_min (by linarith) (by linarith), fun κ hκ =>
      zetaZeroShiftSet_density_zero (lt_min (by linarith) (by linarith)) (min_le_left _ _)
        (min_le_right _ _) hκ⟩

/-! ### Purity of a factor -/

/-- **A bounded Dirichlet series with a zero off the critical line has a zero that `ξ` does not
have.** Its zeros recur with positive lower density, and the zeros of `ζ` off the line have density
zero. -/
theorem exists_zero_not_xi_zero_of_re_ne_half {f : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M : ℝ}
    (hsum : LSeriesSummable f (u₀ : ℂ)) (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re})
    (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M) (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries f z)
    (hFne : ∃ z₁ : ℂ, x < z₁.re ∧ F z₁ ≠ 0) {ρ₀ : ℂ} (hρx : x < ρ₀.re) (hFρ : F ρ₀ = 0)
    (hne : ρ₀.re ≠ 1 / 2) :
    ∃ z : ℂ, x < z.re ∧ F z = 0 ∧ xi z ≠ 0 := by
  by_contra hcon
  have hall : ∀ z : ℂ, x < z.re → F z = 0 → xi z = 0 := fun z hz hz0 => by
    by_contra hxi
    exact hcon ⟨z, hz, hz0, hxi⟩
  have hxi : xi ρ₀ = 0 := hall ρ₀ hρx hFρ
  obtain ⟨r, hr, hdens⟩ := exists_zetaZeroShiftSet_density_zero (re_pos_of_xi_eq_zero hxi)
    (re_lt_one_of_xi_eq_zero hxi) hne
  obtain ⟨L, hL, d, hd, hthick⟩ := exists_thick_zero_shifts hsum hF hM hFL hFne hρx hFρ hr
  have hthick' : ∀ a : ℝ, ∃ τ ∈ Icc a (a + L), Ioo (τ - d) (τ + d) ⊆ zetaZeroShiftSet ρ₀ r := by
    intro a
    obtain ⟨τ, hτ, hsub⟩ := hthick a
    refine ⟨τ, hτ, fun t ht => ?_⟩
    obtain ⟨z, hz, hzx, hz0⟩ := hsub ht
    have hxiz := hall _ hzx hz0
    exact ⟨z, hz, (xi_eq_zero_iff (re_pos_of_xi_eq_zero hxiz) fun h => by
      have := re_lt_one_of_xi_eq_zero hxiz
      rw [h, Complex.one_re] at this
      exact lt_irrefl _ this).mp hxiz⟩
  -- positive lower density against density zero
  have hlow := eventually_le_volume_of_relativelyDense hL hd hthick'
  have hκ0 : 0 < d / (L + 2 * d) := by positivity
  have hup := hdens (d / (L + 2 * d) / 2) (by positivity)
  obtain ⟨T, hT1, hT2, hT0⟩ := (hlow.and (hup.and (eventually_gt_atTop 0))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith [mul_pos hκ0 hT0]

/-- **A factor with a Dirichlet series is pure.** If every zero of a bounded Dirichlet series in
`Re s > x` is a zero of `ξ`, all of them lie on the critical line. -/
theorem re_eq_half_of_zeros_subset_xi {f : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M : ℝ}
    (hsum : LSeriesSummable f (u₀ : ℂ)) (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re})
    (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M) (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries f z)
    (hFne : ∃ z₁ : ℂ, x < z₁.re ∧ F z₁ ≠ 0)
    (hzero : ∀ z : ℂ, x < z.re → F z = 0 → xi z = 0) {ρ₀ : ℂ} (hρx : x < ρ₀.re)
    (hFρ : F ρ₀ = 0) : ρ₀.re = 1 / 2 := by
  by_contra hne
  obtain ⟨z, hzx, hz0, hxi⟩ :=
    exists_zero_not_xi_zero_of_re_ne_half hsum hF hM hFL hFne hρx hFρ hne
  exact hxi (hzero z hzx hz0)

/-! ### Dirichlet polynomials -/

/-- A Dirichlet polynomial is bounded on every right half-plane. -/
theorem norm_finiteDirichletPolynomial_le (a : ℕ →₀ ℂ) (ha : a 0 = 0) {x : ℝ} {s : ℂ}
    (hs : x < s.re) :
    ‖finiteDirichletPolynomial a s‖ ≤ ∑ n ∈ a.support, ‖a n‖ * (n : ℝ) ^ (-x) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => (Finsupp.mem_support_iff.mp hn) (h ▸ ha)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn0) (by linarith)) (norm_nonneg _)

/-- **A Dirichlet polynomial with a zero off the critical line has a zero that `ξ` does not
have.** -/
theorem exists_zero_dirichletPolynomial_not_xi_zero (a : ℕ →₀ ℂ) (ha : a 0 = 0) (hne : a ≠ 0)
    {ρ₀ : ℂ} (hρ : finiteDirichletPolynomial a ρ₀ = 0) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ z : ℂ, finiteDirichletPolynomial a z = 0 ∧ xi z ≠ 0 := by
  have hdiff := differentiable_finiteDirichletPolynomial a ha
  have hsum : LSeriesSummable (fun n => a n) ((ρ₀.re : ℝ) : ℂ) :=
    summable_of_ne_finset_zero (s := a.support) fun n hn => by
      rw [LSeries.term_def₀ ha, Finsupp.notMem_support_iff.mp hn, zero_mul]
  -- the polynomial does not vanish identically right of `Re ρ₀ - 1`
  have hFne : ∃ z₁ : ℂ, ρ₀.re - 1 < z₁.re ∧ finiteDirichletPolynomial a z₁ ≠ 0 := by
    by_contra hcon
    refine finiteDirichletPolynomial_ne_zero a ha hne (funext fun s => ?_)
    have han : AnalyticOnNhd ℂ (finiteDirichletPolynomial a) univ :=
      hdiff.differentiableOn.analyticOnNhd isOpen_univ
    have hev : finiteDirichletPolynomial a =ᶠ[𝓝 ρ₀] 0 := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show ρ₀.re - 1 < ρ₀.re by linarith)] with z hz
      by_contra hz0
      exact hcon ⟨z, hz, hz0⟩
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hev
      (mem_univ s)
  obtain ⟨z, -, hz0, hxi⟩ := exists_zero_not_xi_zero_of_re_ne_half (x := ρ₀.re - 1)
    hsum hdiff.differentiableOn (fun z hz => norm_finiteDirichletPolynomial_le a ha hz)
    (fun z _ => finiteDirichletPolynomial_eq_LSeries a ha z) hFne (by linarith) hρ hre
  exact ⟨z, hz0, hxi⟩

/-- **A Dirichlet polynomial whose zeros are zeros of `ξ` has all its zeros on the critical
line.** -/
theorem re_eq_half_of_dirichletPolynomial_zeros_subset_xi (a : ℕ →₀ ℂ) (ha : a 0 = 0)
    (hne : a ≠ 0) (hzero : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → xi z = 0) {ρ₀ : ℂ}
    (hρ : finiteDirichletPolynomial a ρ₀ = 0) : ρ₀.re = 1 / 2 := by
  by_contra hre
  obtain ⟨z, hz0, hxi⟩ := exists_zero_dirichletPolynomial_not_xi_zero a ha hne hρ hre
  exact hxi (hzero z hz0)

end GaloisForLFunctions.InfiniteRankPurityTheory
