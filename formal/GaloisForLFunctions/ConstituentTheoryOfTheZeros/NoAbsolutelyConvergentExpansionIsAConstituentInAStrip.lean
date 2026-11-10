import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentDirichletSeriesIsAConstituent
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicUniformLimit
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum

/-!
# No absolutely convergent expansion is a constituent in a strip

Let `F(s) = Σ_q c(q) q^s`, `q` over the positive rationals, converge absolutely on the closed strip
`|Re s − ½| ≤ ω`, `F ≢ 0`. The scales may be of both sizes, so `F` need not be defined outside the
strip: Dirichlet series, their reflections, and sums such as `Σ c_j cosh((s − ½) log q_j)`, whose
values on the critical line are real, are all of this form.

**Theorem** (`expansion_ne_zero_of_strip_zeros_subset_xi`). If every zero of `F` in the open strip
is a zero of `ξ`, then `F` has no zero in the open strip.

Beyond the core `expansion_ne_zero_of_zeros_cancelled` this needs, for functions that live on a
strip only:

* almost periodicity (`isStripAlmostPeriodicOn_expansion`): an expansion is a uniform limit on the
  closed strip of its finite parts, which are exponential sums;
* recurrence of a zero (`exists_thick_zero_shifts_on_strip`) and purity
  (`re_eq_half_of_expansion_strip_zeros_subset_xi`): a zero off the line recurs with positive
  density inside the strip, against the density zero of the zeros of `ζ` near its vertical line.
-/

open Complex Filter Topology Set Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

variable {c : PosRat → ℂ}

/-! ### Almost periodicity -/

theorem PosRat.cpow_eq_exp (q : PosRat) (z : ℂ) : q.cpow z = Complex.exp (((q.log : ℝ) : ℂ) * z) := by
  unfold PosRat.cpow PosRat.log
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr q.toReal_pos.ne'),
    Complex.ofReal_log q.toReal_pos.le]

/-- A finite part of an expansion is an exponential sum with real frequencies. -/
theorem exists_expSum_eq_finsetSum (c : PosRat → ℂ) (T : Finset PosRat) :
    ∃ (n : ℕ) (a : Fin n → ℂ) (lam : Fin n → ℝ),
      ∀ z : ℂ, expSum a lam z = ∑ q ∈ T, c q * q.cpow z := by
  refine ⟨T.card, fun k => c (T.equivFin.symm k), fun k => (T.equivFin.symm k : PosRat).log,
    fun z => ?_⟩
  unfold expSum
  rw [← Finset.sum_coe_sort T fun q => c q * q.cpow z,
    ← Equiv.sum_comp T.equivFin.symm fun x : ↥T => c x * (x : PosRat).cpow z]
  exact Finset.sum_congr rfl fun k _ => by rw [PosRat.cpow_eq_exp]

/-- **An absolutely convergent expansion is almost periodic on its closed strip.** -/
theorem isStripAlmostPeriodicOn_expansion {σ R : ℝ} (hc : WSummable (σ - R) (σ + R) c) :
    IsStripAlmostPeriodicOn (expansion c) σ R := by
  refine isStripAlmostPeriodicOn_of_uniform_approx fun ε hε => ?_
  -- a finite set carrying all but `ε` of the weighted coefficients
  have ha0 : ∀ q, 0 ≤ ‖c q‖ * stripWeight (σ - R) (σ + R) q := fun q =>
    mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le
  have htend : Tendsto (fun T : Finset PosRat => ∑ q ∈ T, ‖c q‖ * stripWeight (σ - R) (σ + R) q)
      atTop (𝓝 (∑' q, ‖c q‖ * stripWeight (σ - R) (σ + R) q)) := hc.hasSum
  obtain ⟨T, hT⟩ := (htend.eventually (lt_mem_nhds (show
    (∑' q, ‖c q‖ * stripWeight (σ - R) (σ + R) q) - ε <
      ∑' q, ‖c q‖ * stripWeight (σ - R) (σ + R) q by linarith))).exists
  obtain ⟨n, a, lam, hG⟩ := exists_expSum_eq_finsetSum c T
  refine ⟨expSum a lam, isStripAlmostPeriodic_expSum a lam σ (R + 1) R (by linarith),
    fun z hz => ?_⟩
  have hz' := abs_le.mp (show |z.re - σ| ≤ R from hz)
  have h₁ : σ - R ≤ z.re := by linarith [hz'.1]
  have h₂ : z.re ≤ σ + R := by linarith [hz'.2]
  have he : HasSum (fun q => c q * q.cpow z) (expansion c z) := (hc.summable_term h₁ h₂).hasSum
  have hfin : HasSum (fun q => if q ∈ T then c q * q.cpow z else 0)
      (∑ q ∈ T, c q * q.cpow z) := by
    have h : HasSum (fun q => if q ∈ T then c q * q.cpow z else 0)
        (∑ q ∈ T, if q ∈ T then c q * q.cpow z else 0) :=
      hasSum_sum_of_ne_finset_zero fun q hq => if_neg hq
    rwa [Finset.sum_congr rfl fun q hq => if_pos hq] at h
  have hind : HasSum (fun q => if q ∈ T then ‖c q‖ * stripWeight (σ - R) (σ + R) q else 0)
      (∑ q ∈ T, ‖c q‖ * stripWeight (σ - R) (σ + R) q) := by
    have h : HasSum (fun q => if q ∈ T then ‖c q‖ * stripWeight (σ - R) (σ + R) q else 0)
        (∑ q ∈ T, if q ∈ T then ‖c q‖ * stripWeight (σ - R) (σ + R) q else 0) :=
      hasSum_sum_of_ne_finset_zero fun q hq => if_neg hq
    rwa [Finset.sum_congr rfl fun q hq => if_pos hq] at h
  have hbound := (he.sub hfin).norm_le_of_bounded (hc.hasSum.sub hind) fun q => by
    by_cases hq : q ∈ T
    · rw [if_pos hq, if_pos hq, sub_self, sub_self, norm_zero]
    · rw [if_neg hq, if_neg hq, sub_zero, sub_zero]
      exact norm_term_le c h₁ h₂ q
  rw [hG z]
  linarith

/-! ### Recurrence of a zero in a strip -/

/-- **A zero of a function almost periodic on a strip recurs.** Let `F` be holomorphic on the open
strip `τ₁ < Re z < τ₂`, not identically zero, and almost periodic on a closed strip about the line
through a zero `ρ₀`. Every interval of some length `L` contains a shift `τ` such that each `t`
within `d` of `τ` carries a zero of `F` into the disc of radius `r` about `ρ₀ + it`. -/
theorem exists_thick_zero_shifts_on_strip {F : ℂ → ℂ} {τ₁ τ₂ : ℝ}
    (hF : DifferentiableOn ℂ F {z : ℂ | τ₁ < z.re ∧ z.re < τ₂})
    (hFne : ∃ z₁ : ℂ, (τ₁ < z₁.re ∧ z₁.re < τ₂) ∧ F z₁ ≠ 0) {ρ₀ : ℂ} (hρ1 : τ₁ < ρ₀.re)
    (hρ2 : ρ₀.re < τ₂) (hFρ : F ρ₀ = 0) {R : ℝ} (hR : 0 < R)
    (hAP : IsStripAlmostPeriodicOn F ρ₀.re R) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℝ, 0 < L ∧ ∃ d : ℝ, 0 < d ∧ ∀ y : ℝ, ∃ τ ∈ Icc y (y + L),
      Ioo (τ - d) (τ + d) ⊆ {t : ℝ | ∃ z ∈ ball ρ₀ r, F (z + t * I) = 0} := by
  have hUopen := isOpen_openStrip τ₁ τ₂
  have han : AnalyticOnNhd ℂ F {z : ℂ | τ₁ < z.re ∧ z.re < τ₂} := hF.analyticOnNhd hUopen
  -- the zero is isolated
  have hne : ∀ᶠ z in 𝓝[≠] ρ₀, F z ≠ 0 := by
    refine (han ρ₀ ⟨hρ1, hρ2⟩).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => ?_
    obtain ⟨z₁, hz₁, hz₁0⟩ := hFne
    exact hz₁0 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_openStrip τ₁ τ₂) ⟨hρ1, hρ2⟩ h hz₁)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  have hgap : 0 < min (ρ₀.re - τ₁) (τ₂ - ρ₀.re) / 2 := by
    have : 0 < min (ρ₀.re - τ₁) (τ₂ - ρ₀.re) := lt_min (by linarith) (by linarith)
    positivity
  set r' : ℝ := min (r₁ / 2) (min r (min (min (ρ₀.re - τ₁) (τ₂ - ρ₀.re) / 2) R)) with hrdef
  have hr' : 0 < r' := lt_min (by linarith) (lt_min hr (lt_min hgap hR))
  have hrr₁ : r' < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hr'r : r' ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hr4 : r' ≤ min (ρ₀.re - τ₁) (τ₂ - ρ₀.re) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr5 : r' ≤ R := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr4a : r' < ρ₀.re - τ₁ := by
    have h := min_le_left (ρ₀.re - τ₁) (τ₂ - ρ₀.re)
    have : 0 < ρ₀.re - τ₁ := by linarith
    linarith
  have hr4b : r' < τ₂ - ρ₀.re := by
    have h := min_le_right (ρ₀.re - τ₁) (τ₂ - ρ₀.re)
    have : 0 < τ₂ - ρ₀.re := by linarith
    linarith
  set ρ : ℝ := r' / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  -- the zero-free circle and its floor
  have hsphU : ∀ z ∈ closedBall ρ₀ ρ, τ₁ < z.re ∧ z.re < τ₂ := by
    intro z hz
    have h := abs_le.mp ((abs_re_le_norm (z - ρ₀)).trans (mem_closedBall_iff_norm.mp hz))
    rw [sub_re] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
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
  refine ⟨L, hL, ρ, hρ, fun y => ?_⟩
  obtain ⟨τ, hτmem, hτF⟩ := hτ y
  refine ⟨τ, hτmem, fun t ht => ?_⟩
  -- an almost period carries a zero, by the minimum modulus principle
  have hdiff : DifferentiableOn ℂ (fun s => F (s + τ * I)) (closedBall ρ₀ ρ) := by
    intro s hs
    have hs' : τ₁ < (s + τ * I).re ∧ (s + τ * I).re < τ₂ := by simpa using hsphU s hs
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
  have hpt : z - ((t - τ : ℝ) : ℂ) * I + (t : ℂ) * I = z + τ * I := by
    push_cast
    ring
  refine ⟨z - ((t - τ : ℝ) : ℂ) * I, ?_, ?_⟩
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
    exact hz0

/-! ### Purity and the theorem -/

/-- **A constituent in a strip is pure.** If every zero of an absolutely convergent expansion in
a strip about the critical line is a zero of `ξ`, they all lie on the line. -/
theorem re_eq_half_of_expansion_strip_zeros_subset_xi {ω : ℝ}
    (hc : WSummable (1 / 2 - ω) (1 / 2 + ω) c) (hne : c ≠ 0)
    (hzero : ∀ s : ℂ, |s.re - 1 / 2| < ω → expansion c s = 0 → xi s = 0) {ρ₀ : ℂ}
    (hρ : |ρ₀.re - 1 / 2| < ω) (hρ0 : expansion c ρ₀ = 0) : ρ₀.re = 1 / 2 := by
  by_contra hne'
  have hω0 : 0 < ω := lt_of_le_of_lt (abs_nonneg _) hρ
  have hxi := hzero ρ₀ hρ hρ0
  obtain ⟨r, hr, hdens⟩ := exists_zetaZeroShiftSet_density_zero (re_pos_of_xi_eq_zero hxi)
    (re_lt_one_of_xi_eq_zero hxi) hne'
  have hρ' := abs_lt.mp hρ
  -- a point of the strip where the expansion does not vanish
  have hFne : ∃ z₁ : ℂ, (1 / 2 - ω < z₁.re ∧ z₁.re < 1 / 2 + ω) ∧ expansion c z₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (eq_zero_of_expansion_eq_zero (le_refl (1 / 2 : ℝ))
      (hc.mono (by linarith) le_rfl (by linarith)) fun z h1 h2 => ?_)
    have hre : z.re = 1 / 2 := le_antisymm h2 h1
    exact hcon z ⟨by rw [hre]; linarith, by rw [hre]; linarith⟩
  set R : ℝ := (ω - |ρ₀.re - 1 / 2|) / 2 with hR
  have hRpos : 0 < R := by
    rw [hR]
    linarith
  have hAP : IsStripAlmostPeriodicOn (expansion c) ρ₀.re R :=
    isStripAlmostPeriodicOn_expansion (hc.mono
      (by rcases abs_cases (ρ₀.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;> rw [hR, hab] <;> linarith)
      (by linarith)
      (by rcases abs_cases (ρ₀.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;> rw [hR, hab] <;> linarith))
  set r' : ℝ := min r (ω - |ρ₀.re - 1 / 2|) with hr'
  have hr'pos : 0 < r' := lt_min hr (by linarith)
  obtain ⟨L, hL, d, hd, hthick⟩ := exists_thick_zero_shifts_on_strip
    (differentiableOn_expansion hc) hFne (by linarith [hρ'.1]) (by linarith [hρ'.2]) hρ0 hRpos
    hAP hr'pos
  have hthick' : ∀ y : ℝ, ∃ τ ∈ Icc y (y + L), Ioo (τ - d) (τ + d) ⊆ zetaZeroShiftSet ρ₀ r := by
    intro y
    obtain ⟨τ, hτ, hsub⟩ := hthick y
    refine ⟨τ, hτ, fun t ht => ?_⟩
    obtain ⟨z, hz, hz0⟩ := hsub ht
    have hzr : ‖z - ρ₀‖ < r' := mem_ball_iff_norm.mp hz
    have hzre := abs_lt.mp ((abs_re_le_norm (z - ρ₀)).trans_lt hzr)
    rw [sub_re] at hzre
    have hre : (z + (t : ℂ) * I).re = z.re := by simp
    have hstrip : |(z + (t : ℂ) * I).re - 1 / 2| < ω := by
      rw [hre]
      have h2 : r' ≤ ω - |ρ₀.re - 1 / 2| := min_le_right _ _
      rcases abs_cases (ρ₀.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;>
        rw [hab] at h2 <;> rw [abs_lt] <;> constructor <;> linarith [hzre.1, hzre.2]
    have hxiz := hzero _ hstrip hz0
    refine ⟨z, ball_subset_ball (min_le_left _ _) hz, ?_⟩
    exact (xi_eq_zero_iff (re_pos_of_xi_eq_zero hxiz) fun h => by
      have := re_lt_one_of_xi_eq_zero hxiz
      rw [h, one_re] at this
      exact lt_irrefl _ this).mp hxiz
  -- positive lower density against density zero
  have hlow := eventually_le_volume_of_relativelyDense hL hd hthick'
  have hκ0 : 0 < d / (L + 2 * d) := by positivity
  have hup := hdens (d / (L + 2 * d) / 2) (by positivity)
  obtain ⟨T, hT1, hT2, hT0⟩ := (hlow.and (hup.and (eventually_gt_atTop 0))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith [mul_pos hκ0 hT0]

/-- **No absolutely convergent expansion is a constituent with a zero, in a strip.** Let
`F(s) = Σ_q c(q) q^s`, over the positive rationals, converge absolutely on the closed strip
`|Re s − ½| ≤ ω`, `0 < ω ≤ ½`, and not vanish identically. If every zero of `F` in the open strip
is a zero of `ξ`, then `F` has no zero in the open strip. -/
theorem expansion_ne_zero_of_strip_zeros_subset_xi {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (hc : WSummable (1 / 2 - ω) (1 / 2 + ω) c) (hne : c ≠ 0)
    (hzero : ∀ s : ℂ, |s.re - 1 / 2| < ω → expansion c s = 0 → xi s = 0) {s : ℂ}
    (hs : |s.re - 1 / 2| < ω) : expansion c s ≠ 0 := by
  have hω2 : 2 * (ω / 2) = ω := by ring
  refine expansion_ne_zero_of_zeros_cancelled (η := ω / 2) (by positivity) (by linarith)
    (by rwa [hω2])
    (isStripAlmostPeriodicOn_expansion (hc.mono (by linarith) (by linarith) (by linarith)))
    (fun z hz hre hz0 => ?_) (fun z hre hz0 => ?_) hne (by rwa [hω2])
  · rw [hω2] at hz
    exact hre (re_eq_half_of_expansion_strip_zeros_subset_xi hc hne hzero hz hz0)
  · have hz : |z.re - 1 / 2| < ω := by rw [hre, sub_self, abs_zero]; exact hω0
    have hxiz := hzero z hz hz0
    exact (xi_eq_zero_iff (by rw [hre]; norm_num) fun h => by
      have := re_lt_one_of_xi_eq_zero hxiz
      rw [h, one_re] at this
      exact lt_irrefl _ this).mp hxiz

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
