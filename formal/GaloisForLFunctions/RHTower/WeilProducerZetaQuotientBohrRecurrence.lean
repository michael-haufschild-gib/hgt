import GaloisForLFunctions.RHTower.WeilProducerReciprocalZetaAtomOrder
import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver
import GaloisForLFunctions.RHTower.LiouvilleEvenIndexPositiveRecurrence
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.HTGeometry.BoundedStripAlmostPeriodicThreeLines
import GaloisForLFunctions.HTGeometry.BohrPrimeLinearInequality

/-!
# Bounded zeta quotients force zero-free half-planes (the Bohr route)

Let `lam` be a full-cone producer and `G = 1/F_lam` the continuation of
`exp(−Σ_{n≥2} lam(n) n^{−s}/log n)` to `Re s > ½`.  The **zeta quotient** `ζ·G = ζ/F_lam` is,
on `Re s > 1`, the Dirichlet series `Σ (1 ⋆ μ_lam)(n) n^{−s}`.  It extends holomorphically to
`Re s > ½`, and its zeros there are exactly the zeros of `ζ`.

**Theorem** (`riemannZeta_ne_zero_of_bounded_zetaQuotient`).  If `|ζ(s) G(s)| ≤ M` on `Re s > x`
(`x ≥ ½`), then `ζ` has no zeros in `Re s > x`.

**Proof.**
1. *Bohr.*  A Dirichlet series with a bounded holomorphic continuation to `Re s > x` is almost
   periodic on every closed substrip (`isStripAlmostPeriodicOn_of_bounded_LSeries`, three lines).
2. *Recurrence.*  If `ζ(ρ₀) = 0`, `Re ρ₀ > x`, the quotient vanishes at `ρ₀`.  Along its
   relatively dense almost periods `τ` the minimum modulus principle gives a zero of the
   quotient, hence of `ζ`, in `B(ρ₀ + iτ, r/2)`.  So the shifts `τ` carrying a zero of `ζ` into
   `B(ρ₀ + iτ, r)` contain a relatively dense family of intervals of length `r`, and they have
   positive lower density (`eventually_le_volume_of_relativelyDense`).
3. *Density.*  Those shifts have density zero, because zeros right of a fixed line are `o(T)`
   (`zetaZeroShiftSet_density_zero`, from `eventually_zeroCount_fixedSigma_le`).

The same argument gives the general zero-set principle
(`riemannZeta_ne_zero_of_bounded_of_zeroSet`): a Dirichlet series bounded on `Re s > x` whose
zeros there are zeros of `ζ`, and which vanishes at every zero of `ζ` there, forces `ζ` to be
zero-free on `Re s > x`.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- The shifts `τ` for which `ζ` has a zero in the translated disc `B(ρ₀ + iτ, r)`. -/
def zetaZeroShiftSet (ρ₀ : ℂ) (r : ℝ) : Set ℝ :=
  {τ : ℝ | ∃ z ∈ ball ρ₀ r, riemannZeta (z + τ * I) = 0}

/-- **Zero shifts on one window.** For every `δ > 0`, for all large `V` the shifts in
`[(V − Im ρ₀)/2, V]` that carry a zero of `ζ` into `B(ρ₀ + iτ, r)` have measure at most `δ V`. -/
theorem eventually_volume_zetaZeroShiftSet_window_le {ρ₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ V in atTop, volume (zetaZeroShiftSet ρ₀ r ∩
      Icc ((V - ρ₀.im) / 2) V) ≤ ENNReal.ofReal (δ * V) := by
  classical
  set γ₀ := ρ₀.im
  set E := zetaZeroShiftSet ρ₀ r
  have hre : ∀ s ∈ closedBall ρ₀ r, ρ₀.re - r ≤ s.re ∧ s.re < 1 := by
    intro s hs
    have h := abs_le.mp ((abs_re_le_norm (s - ρ₀)).trans (mem_closedBall_iff_norm.mp hs))
    rw [sub_re] at h
    constructor <;> linarith [h.1, h.2]
  have hσ : (1 : ℝ) / 2 < ρ₀.re - r := by linarith
  have hlin : Tendsto (fun V : ℝ => 2 * (V + γ₀)) atTop atTop :=
    (tendsto_atTop_add_const_right _ γ₀ tendsto_id).const_mul_atTop two_pos
  have hε' : 0 < δ / (4 * r) := by positivity
  filter_upwards [hlin.eventually (eventually_zeroCount_fixedSigma_le hσ hε'),
    hlin.eventually (eventually_ge_atTop (100 : ℝ)),
    eventually_ge_atTop ((2 + 2 * r + δ * |γ₀| / 4) / (3 * δ / 4))] with V hV hV100 hVbig
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hV
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zσ := Z.filter (fun w => ρ₀.re - r ≤ w.re)
  have hcover : Icc ((V - γ₀) / 2) V ⊆ (Icc ((V - γ₀) / 2) (T₁ - γ₀ + r) ∪
      Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r)) ∪ Icc (T₂ - γ₀ - r) V := by
    intro x hx
    rcases le_total x (T₁ - γ₀ + r) with h | h
    · exact Or.inl (Or.inl ⟨hx.1, h⟩)
    rcases le_total x (T₂ - γ₀ - r) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr ⟨h', hx.2⟩
  have hmid : E ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r) ⊆
      ⋃ w ∈ Zσ, Icc (w.im - γ₀ - r) (w.im - γ₀ + r) := by
    intro τ ⟨hτE, hτ⟩
    obtain ⟨z, hz, hz0⟩ := hτE
    have hzre := hre z (ball_subset_closedBall hz)
    have hzim := abs_le.mp ((abs_im_le_norm (z - ρ₀)).trans (mem_ball_iff_norm.mp hz).le)
    rw [sub_im] at hzim
    set w := z + τ * I with hw
    have hwre : w.re = z.re := by simp [hw]
    have hwim : w.im = z.im + τ := by simp [hw]
    have hwZ : w ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le, hwre,
        hwim]
      exact ⟨⟨⟨by linarith [hzre.1], by linarith [hzre.2]⟩,
        ⟨by linarith [hτ.1, hzim.1], by linarith [hτ.2, hzim.2]⟩⟩, hz0⟩
    refine mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hwZ, by rw [hwre]; exact hzre.1⟩, ?_⟩
    rw [hwim]
    exact ⟨by linarith [hzim.2], by linarith [hzim.1]⟩
  have hcard : (Zσ.card : ℝ) ≤ ∑ w ∈ Zσ, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
  have hvmid : volume (E ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r)) ≤
      ENNReal.ofReal (2 * r * (δ / (4 * r) * (T₂ - T₁))) :=
    calc volume (E ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r))
        ≤ volume (⋃ w ∈ Zσ, Icc (w.im - γ₀ - r) (w.im - γ₀ + r)) := measure_mono hmid
      _ ≤ ∑ w ∈ Zσ, volume (Icc (w.im - γ₀ - r) (w.im - γ₀ + r)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ w ∈ Zσ, ENNReal.ofReal (2 * r) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Real.volume_Icc]
          congr 1
          ring
      _ = ENNReal.ofReal (2 * r * Zσ.card) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), mul_comm]
      _ ≤ ENNReal.ofReal (2 * r * (δ / (4 * r) * (T₂ - T₁))) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hcard.trans (hc Z hZ)) (by positivity))
  have hlo : volume (Icc ((V - γ₀) / 2) (T₁ - γ₀ + r)) ≤ ENNReal.ofReal (1 + r) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith [hT₁.2])
  have hhi : volume (Icc (T₂ - γ₀ - r) V) ≤ ENNReal.ofReal (1 + r) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith [hT₂.1])
  have hlen : T₂ - T₁ ≤ (V + γ₀) / 2 := by linarith [hT₁.1, hT₂.2]
  have hmid' : 2 * r * (δ / (4 * r) * (T₂ - T₁)) = δ / 2 * (T₂ - T₁) := by
    field_simp
    ring
  have hγ : -|γ₀| ≤ γ₀ := neg_abs_le γ₀
  have hVbig' : 2 + 2 * r + δ * |γ₀| / 4 ≤ 3 * δ / 4 * V := by
    rw [div_le_iff₀ (by positivity)] at hVbig
    linarith
  calc volume (E ∩ Icc ((V - γ₀) / 2) V)
      ≤ volume ((E ∩ Icc ((V - γ₀) / 2) (T₁ - γ₀ + r) ∪ E ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r)) ∪
          E ∩ Icc (T₂ - γ₀ - r) V) := by
        refine measure_mono ?_
        rw [← inter_union_distrib_left, ← inter_union_distrib_left]
        exact inter_subset_inter_right _ hcover
    _ ≤ (volume (Icc ((V - γ₀) / 2) (T₁ - γ₀ + r)) +
          volume (E ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r))) + volume (Icc (T₂ - γ₀ - r) V) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_mono inter_subset_right) le_rfl)) (measure_mono inter_subset_right))
    _ ≤ (ENNReal.ofReal (1 + r) + ENNReal.ofReal (δ / 2 * (T₂ - T₁))) + ENNReal.ofReal (1 + r) :=
        add_le_add (add_le_add hlo (hmid' ▸ hvmid)) hhi
    _ = ENNReal.ofReal ((1 + r) + δ / 2 * (T₂ - T₁) + (1 + r)) := by
        have hmid0 : 0 ≤ δ / 2 * (T₂ - T₁) := mul_nonneg (by positivity) (by linarith)
        rw [← ENNReal.ofReal_add (by positivity) hmid0, ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal (δ * V) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := mul_le_mul_of_nonneg_left hlen hδ.le
        have h2 := mul_le_mul_of_nonneg_left (le_abs_self γ₀) hδ.le
        linarith


/-- **Zero shifts have density zero.** -/
theorem zetaZeroShiftSet_density_zero {ρ₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T in atTop, volume (zetaZeroShiftSet ρ₀ r ∩ Icc 0 T) ≤ ENNReal.ofReal (κ * T) :=
  eventually_volume_inter_Icc_le_of_window
    (fun _ hδ => eventually_volume_zetaZeroShiftSet_window_le hr hr2 hr3 hδ) hκ

/-- **Relatively dense thick sets have positive lower density.**  If every interval `[a, a + L]`
contains a point `τ` with `(τ − d, τ + d) ⊆ E`, then `|E ∩ [0, T]| ≥ d T/(L + 2d)` for large
`T`. -/
theorem eventually_le_volume_of_relativelyDense {E : Set ℝ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (hE : ∀ a : ℝ, ∃ τ ∈ Icc a (a + L), Ioo (τ - d) (τ + d) ⊆ E) :
    ∀ᶠ T in atTop, ENNReal.ofReal (d / (L + 2 * d) * T) ≤ volume (E ∩ Icc 0 T) := by
  classical
  choose τ hτI hτE using hE
  set D : ℝ := L + 2 * d with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  filter_upwards [eventually_ge_atTop (4 * D)] with T hT
  set K : ℕ := ⌊T / D⌋₊ - 1 with hK
  have hfl : (4 : ℝ) ≤ ⌊T / D⌋₊ := by
    have h4 : (4 : ℝ) ≤ T / D := by rw [le_div_iff₀ hD0]; linarith
    exact_mod_cast Nat.le_floor (by exact_mod_cast h4)
  have hKr : (K : ℝ) = ⌊T / D⌋₊ - 1 := by
    rw [hK, Nat.cast_sub (by exact_mod_cast (by linarith : (1 : ℝ) ≤ ⌊T / D⌋₊))]; simp
  have hflT : (⌊T / D⌋₊ : ℝ) ≤ T / D := Nat.floor_le (div_nonneg (by linarith) hD0.le)
  set I : ℕ → Set ℝ := fun k => Ioo (τ (k * D) - d) (τ (k * D) + d) with hIdef
  have hsub : ∀ k ∈ Finset.Icc 1 K, I k ⊆ E ∩ Icc 0 T := by
    intro k hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkK' : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have h1 := (hτI (k * D)).1
    have h2 := (hτI (k * D)).2
    intro t ht
    refine ⟨hτE _ ht, ?_, ?_⟩
    · have : D ≤ k * D := by nlinarith
      linarith [ht.1]
    · have hkD : k * D + L + d ≤ (K + 1) * D := by nlinarith
      have hKD : ((K : ℝ) + 1) * D ≤ T := by
        rw [hKr]
        have := (le_div_iff₀ hD0).mp hflT
        linarith
      linarith [ht.2]
  have hdisj : (↑(Finset.Icc 1 K) : Set ℕ).PairwiseDisjoint I := by
    intro j _ k _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · refine Set.disjoint_left.mpr fun t htj htk => ?_
      have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
      have e1 := (hτI (j * D)).2
      have e2 := (hτI (k * D)).1
      have : j * D + L + 2 * d ≤ k * D := by nlinarith
      linarith [htj.2, htk.1]
    · refine Set.disjoint_left.mpr fun t htj htk => ?_
      have hjk' : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
      have e1 := (hτI (k * D)).2
      have e2 := (hτI (j * D)).1
      have : k * D + L + 2 * d ≤ j * D := by nlinarith
      linarith [htj.1, htk.2]
  have hunion : volume (⋃ k ∈ Finset.Icc 1 K, I k) = ∑ k ∈ Finset.Icc 1 K, volume (I k) :=
    measure_biUnion_finset hdisj fun k _ => measurableSet_Ioo
  have hvol : ∀ k, volume (I k) = ENNReal.ofReal (2 * d) := fun k => by
    rw [hIdef, Real.volume_Ioo]; congr 1; ring
  have hsum : ∑ k ∈ Finset.Icc 1 K, volume (I k) = ENNReal.ofReal (2 * d * K) := by
    simp only [hvol, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    rw [mul_comm, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * d), ENNReal.ofReal_natCast]
  calc ENNReal.ofReal (d / D * T) ≤ ENNReal.ofReal (2 * d * K) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hKr]
        have h1 : T / D - 1 < ⌊T / D⌋₊ := by
          have := Nat.lt_floor_add_one (T / D); linarith
        have h2 : d / D * T = d * (T / D) := by ring
        rw [h2]
        have h3 : T / D ≥ 4 := by rw [ge_iff_le, le_div_iff₀ hD0]; linarith
        nlinarith
    _ = volume (⋃ k ∈ Finset.Icc 1 K, I k) := by rw [hunion, hsum]
    _ ≤ volume (E ∩ Icc 0 T) := measure_mono (iUnion₂_subset hsub)

/-- **Bohr zero-set principle.**  Let `F` be holomorphic and bounded on `Re s > x` (`x ≥ ½`),
equal there on `Re s > u₀` to an absolutely convergent Dirichlet series, and not identically
zero.  If `F` vanishes at every zero of `ζ` in `x < Re s < 1` and every zero of `F` in `Re s > x`
is a zero of `ζ`, then `ζ` has no zeros in `Re s > x`. -/
theorem riemannZeta_ne_zero_of_bounded_of_zeroSet {f : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M : ℝ}
    (hx : 1 / 2 ≤ x) (hsum : LSeriesSummable f (u₀ : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries f z) (hFne : ∃ z₁ : ℂ, x < z₁.re ∧ F z₁ ≠ 0)
    (hzeta : ∀ z : ℂ, x < z.re → z.re < 1 → riemannZeta z = 0 → F z = 0)
    (hzero : ∀ z : ℂ, x < z.re → F z = 0 → riemannZeta z = 0) :
    ∀ s : ℂ, x < s.re → riemannZeta s ≠ 0 := by
  intro ρ₀ hρx hρ0
  have hρ1 : ρ₀.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ0
  have hFρ : F ρ₀ = 0 := hzeta ρ₀ hρx hρ1 hρ0
  set U : Set ℂ := {z : ℂ | x < z.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt x).isPreconnected
  have han : AnalyticOnNhd ℂ F U := hF.analyticOnNhd hUopen
  have hne : ∀ᶠ z in 𝓝[≠] ρ₀, F z ≠ 0 := by
    refine (han ρ₀ hρx).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => ?_
    obtain ⟨z₁, hz₁, hz₁0⟩ := hFne
    exact hz₁0 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hρx h hz₁)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r : ℝ := min (r₁ / 2) (min ((ρ₀.re - 1 / 2) / 2) (min ((1 - ρ₀.re) / 2) ((ρ₀.re - x) / 2)))
    with hrdef
  have hr : 0 < r := lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith)
    (by linarith)))
  have hrr₁ : r < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hr2 : r ≤ (ρ₀.re - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (1 - ρ₀.re) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr4 : r ≤ (ρ₀.re - x) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set ρ : ℝ := r / 2 with hρdef
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
    have hzρ : z ≠ ρ₀ := by intro h; rw [h, dist_self] at hd; linarith
    exact hball (by rw [hd]; linarith) hzρ
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere ρ₀ ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le)
    (hF.continuousOn.mono fun z hz => hsphU z (sphere_subset_closedBall hz)).norm
  set m : ℝ := ‖F z₁‖ with hmdef
  have hm0 : 0 < m := norm_pos_iff.mpr (hsph z₁ hz₁)
  have hm : ∀ z ∈ sphere ρ₀ ρ, m ≤ ‖F z‖ := fun z hz => isMinOn_iff.mp hmin z hz
  -- almost periodicity on a strip around the disc
  set l' : ℝ := ρ₀.re - ρ with hl'
  set u : ℝ := max (u₀ + 1) (ρ₀.re + 1) with hu
  have hxl' : x < l' := by rw [hl']; linarith
  have hl'u : l' ≤ u := by rw [hl', hu]; linarith [le_max_right (u₀ + 1) (ρ₀.re + 1)]
  have hap := GaloisForLFunctions.isStripAlmostPeriodicOn_of_bounded_LSeries hxl' hl'u
    (by rw [hu]; linarith [le_max_left (u₀ + 1) (ρ₀.re + 1)]) hsum hF hM hFL (m / 3) (by positivity)
  obtain ⟨L, hL, hτ⟩ := hap
  have hstrip : ∀ z ∈ closedBall ρ₀ ρ, |z.re - (l' + u) / 2| ≤ (u - l') / 2 := by
    intro z hz
    have h := abs_le.mp ((abs_re_le_norm (z - ρ₀)).trans (mem_closedBall_iff_norm.mp hz))
    rw [sub_re] at h
    have hu1 : ρ₀.re + 1 ≤ u := le_max_right _ _
    refine abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  -- every almost period carries a zero of `ζ`, and so does a whole interval around it
  have hthick : ∀ a : ℝ, ∃ τ ∈ Icc a (a + L), Ioo (τ - ρ) (τ + ρ) ⊆ zetaZeroShiftSet ρ₀ r := by
    intro a
    obtain ⟨τ, hτmem, hτF⟩ := hτ a
    refine ⟨τ, hτmem, fun t ht => ?_⟩
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
    have hζ : riemannZeta (z + τ * I) = 0 := hzero _ hzx hz0
    refine ⟨z - ((t - τ : ℝ) : ℂ) * I, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      calc ‖z - ((t - τ : ℝ) : ℂ) * I - ρ₀‖ ≤ ‖z - ρ₀‖ + ‖((t - τ : ℝ) : ℂ) * I‖ := by
            rw [show z - ((t - τ : ℝ) : ℂ) * I - ρ₀ = (z - ρ₀) - ((t - τ : ℝ) : ℂ) * I by ring]
            exact norm_sub_le _ _
        _ < ρ + ρ := by
            refine add_lt_add (mem_ball_iff_norm.mp hz) ?_
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact abs_sub_lt_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
        _ = r := by rw [hρdef]; ring
    · rw [show z - ((t - τ : ℝ) : ℂ) * I + (t : ℂ) * I = z + τ * I by push_cast; ring]
      exact hζ
  -- positive lower density against density zero
  have hlow := eventually_le_volume_of_relativelyDense hL hρ hthick
  set κ : ℝ := ρ / (L + 2 * ρ) with hκ
  have hκ0 : 0 < κ := by positivity
  have hup := zetaZeroShiftSet_density_zero hr hr2 hr3 (κ := κ / 2) (by positivity)
  obtain ⟨T, hT1, hT2, hT0⟩ := (hlow.and (hup.and (eventually_gt_atTop 0))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith

namespace WeilSpectral

open WeilHerglotz

/-- The producer's reciprocal zeta function in primitive form, with the holomorphic zeta
quotient `c ζ̃(s) e^{P(s)}` (`ζ̃(s) = (s − 1)ζ(s)` entire). -/
theorem exists_zetaQuotient_primitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ (c : ℂ) (P : ℂ → ℂ), c ≠ 0 ∧
      (∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P
        (zetaArchimedeanDatum s - weilContinuation hW s) s) ∧
      ∀ s : ℂ, 1 < s.re → c * ((s - 1) * cexp (P s)) =
        cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s) := by
  set lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0 with hlam'
  have hH := herglotzWeilPositive_of_weilPositiveFull hW
  have hAd : DifferentiableOn ℂ zetaArchimedeanDatum {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith
  have hΦid : ∀ s : ℂ, 1 < s.re → weilContinuation hW s =
      zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (fun n => (lam' n : ℂ)) s := by
    intro s hs
    rw [weilContinuation_eq hW hs, weilFunction, zetaArchimedeanDatum]
    rfl
  exact exists_reciprocalZeta_primitive hH (by simp [hlam']) hAd (differentiableOn_weilContinuation hW)
    hΦid

/-- **A bounded zeta quotient forces a zero-free half-plane.**  For a full-cone producer `lam`, let
`G` be the continuation of `1/F_lam = exp(−Σ_{n≥2} lam(n) n^{−s}/log n)` to `Re s > ½`.  If
`|ζ(s) G(s)| ≤ M` on `Re s > x` (`s ≠ 1`, `x ≥ ½`), then `ζ` has no zeros in `Re s > x`. -/
theorem riemannZeta_ne_zero_of_bounded_zetaQuotient {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ x M : ℝ, 1 / 2 ≤ x → (∀ s : ℂ, x < s.re → s ≠ 1 → ‖riemannZeta s * G s‖ ≤ M) →
        ∀ s : ℂ, x < s.re → riemannZeta s ≠ 0 := by
  set lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0 with hlam'
  obtain ⟨c, P, hc0, hPd, hGL⟩ := exists_zetaQuotient_primitive hW
  set G : ℂ → ℂ := fun s => c * ((s - 1) * cexp (P s)) with hGdef
  refine ⟨G, fun s hs => ((((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul
    c).differentiableAt.differentiableWithinAt, hGL, fun x M hx hB => ?_⟩
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam' n| / (n : ℝ) ^ σ :=
    (herglotzWeilPositive_of_weilPositiveFull hW).summable
  set F : ℂ → ℂ := fun s => c * zetaEntire s * cexp (P s) with hFdef
  have hFG : ∀ s : ℂ, s ≠ 1 → F s = riemannZeta s * G s := by
    intro s hs
    simp only [hFdef, hGdef]
    rw [zetaEntire_eq hs]
    ring
  have hFd : DifferentiableOn ℂ F {z : ℂ | x < z.re} := by
    intro s hs
    have hs' : 1 / 2 < s.re := lt_of_le_of_lt hx hs
    exact (((differentiable_zetaEntire s).const_mul c).mul
      (hPd s hs').differentiableAt.cexp).differentiableWithinAt
  set f : ℕ → ℂ := LSeries.convolution 1 (producerMobius lam') with hfdef
  have h2 : (1 : ℝ) < ((2 : ℝ) : ℂ).re := by simp
  have hsumf : LSeriesSummable f ((2 : ℝ) : ℂ) :=
    (LSeriesSummable_one_iff.mpr h2).convolution (LSeries_producerMobius hsum h2).1
  have hFL : ∀ z : ℂ, (2 : ℝ) < z.re → F z = LSeries f z := by
    intro z hz
    have hz1 : 1 < z.re := by linarith
    have hzne : z ≠ 1 := by intro h; rw [h] at hz1; simp at hz1
    obtain ⟨hμs, hμ⟩ := LSeries_producerMobius hsum hz1
    rw [hFG z hzne, hfdef, LSeries_convolution' (LSeriesSummable_one_iff.mpr hz1) hμs,
      LSeries_one_eq_riemannZeta hz1, hμ, ← hGL z hz1]
  have hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M := by
    intro z hz
    rcases eq_or_ne z 1 with rfl | hz1
    · have hcont : ContinuousAt F 1 := (hFd.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)).continuousAt
      have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), ‖F s‖ ≤ M := by
        have hopen : {s : ℂ | x < s.re} ∈ 𝓝 (1 : ℂ) :=
          (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hopen] with s hs hsx
        rw [hFG s hs]
        exact hB s hsx hs
      exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds).norm hev
    · rw [hFG z hz1]
      exact hB z hz hz1
  have hFne : ∃ z₁ : ℂ, x < z₁.re ∧ F z₁ ≠ 0 := by
    refine ⟨((x + 1 : ℝ) : ℂ), by simp, ?_⟩
    have hre : 1 ≤ (((x + 1 : ℝ) : ℂ)).re := by simp; linarith
    have hne1 : ((x + 1 : ℝ) : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    simp only [hFdef]
    rw [zetaEntire_eq hne1]
    refine mul_ne_zero (mul_ne_zero hc0 (mul_ne_zero (sub_ne_zero.mpr hne1)
      (riemannZeta_ne_zero_of_one_le_re hre))) (Complex.exp_ne_zero _)
  have hzeta : ∀ z : ℂ, x < z.re → z.re < 1 → riemannZeta z = 0 → F z = 0 := by
    intro z _ hz1 hz0
    have hne : z ≠ 1 := by intro h; rw [h] at hz1; simp at hz1
    rw [hFG z hne, hz0, zero_mul]
  have hzero : ∀ z : ℂ, x < z.re → F z = 0 → riemannZeta z = 0 := by
    intro z _ hz0
    have hE : zetaEntire z = 0 := by
      simp only [hFdef] at hz0
      rcases mul_eq_zero.mp hz0 with h | h
      · exact (mul_eq_zero.mp h).resolve_left hc0
      · exact absurd h (Complex.exp_ne_zero _)
    have hne : z ≠ 1 := by intro h; rw [h, zetaEntire_one] at hE; exact one_ne_zero hE
    rw [zetaEntire_eq hne] at hE
    exact (mul_eq_zero.mp hE).resolve_left (sub_ne_zero.mpr hne)
  exact riemannZeta_ne_zero_of_bounded_of_zeroSet hx hsumf hFd hM hFL hFne hzeta hzero

/-- Two continuations of `1/F_lam` to `Re s > ½` agree there. -/
theorem eqOn_of_reciprocalZeta_continuation {G G' L : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hG' : DifferentiableOn ℂ G' {s : ℂ | 1 / 2 < s.re})
    (hGL : ∀ s : ℂ, 1 < s.re → G s = cexp (-L s)) (hG'L : ∀ s : ℂ, 1 < s.re → G' s = cexp (-L s)) :
    EqOn G G' {s : ℂ | 1 / 2 < s.re} := by
  have hUopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  refine (hG.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
    (hG'.analyticOnNhd hUopen) (convex_halfSpace_re_gt (1 / 2)).isPreconnected h2 ?_
  have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hV.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  rw [hGL z hz, hG'L z hz]

/-- **RH as boundedness of a zeta quotient (the Bohr route).**  The Riemann hypothesis holds iff
some full-cone producer `lam` has a zeta quotient `ζ/F_lam = ζ·G` that is bounded on every
half-plane `Re s > x`, `x > ½` (abscissa of boundedness `≤ ½`). -/
theorem riemannHypothesis_iff_exists_bounded_zetaQuotient :
    RiemannHypothesis ↔ ∃ (lam : ℕ → ℝ) (G : ℂ → ℂ), WeilPositiveFull lam ∧
      DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ x : ℝ, 1 / 2 < x → ∃ M : ℝ, ∀ s : ℂ, x < s.re → s ≠ 1 → ‖riemannZeta s * G s‖ ≤ M := by
  constructor
  · intro hRH
    set Λr : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) with hΛr
    have hW : WeilPositiveFull Λr := weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
    set lam' : ℕ → ℝ := fun n => if 2 ≤ n then Λr n else 0 with hlam'
    have hlamΛ : (fun n => (lam' n : ℂ)) = fun n => (ArithmeticFunction.vonMangoldt n : ℂ) := by
      funext n
      simp only [hlam', hΛr]
      split_ifs with h
      · rfl
      · interval_cases n <;> simp
    obtain ⟨c, P, hc0, hPd, hGL⟩ := exists_zetaQuotient_primitive hW
    set G : ℂ → ℂ := fun s => c * ((s - 1) * cexp (P s)) with hGdef
    have hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} := fun s hs =>
      ((((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul
        c).differentiableAt.differentiableWithinAt
    refine ⟨Λr, G, hW, hGd, hGL, ?_⟩
    have hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam' n| / (n : ℝ) ^ σ :=
      (herglotzWeilPositive_of_weilPositiveFull hW).summable
    have h1 : lam' 1 = 0 := by simp [hlam']
    set L : ℂ → ℂ := LSeries (logZetaCoeff lam') with hLdef
    set H : ℂ → ℂ := fun s => riemannZeta s * cexp (-L s) with hHdef
    set U : Set ℂ := {z : ℂ | 1 < z.re} with hUdef
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hHd : ∀ s ∈ U, HasDerivAt H 0 s := by
      intro s hs
      have hs1 : 1 < s.re := hs
      have hne : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
      have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs1.le
      have hζ := (differentiableAt_riemannZeta hne).hasDerivAt
      have hL := hasDerivAt_LSeries_logZetaCoeff hsum h1 hs1
      refine (hζ.mul hL.neg.cexp).congr_deriv ?_
      rw [hlamΛ, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1]
      field_simp
      ring
    have h2U : (2 : ℂ) ∈ U := by show (1 : ℝ) < (2 : ℂ).re; norm_num
    have hconst : EqOn H (fun _ => H 2) U := hUo.eqOn_of_deriv_eq
      (convex_halfSpace_re_gt 1).isPreconnected
      (fun s hs => (hHd s hs).differentiableAt.differentiableWithinAt)
      (differentiableOn_const (H 2))
      (fun s hs => by rw [(hHd s hs).deriv, deriv_const]) h2U rfl
    set F : ℂ → ℂ := fun s => c * zetaEntire s * cexp (P s) with hFdef
    have hFG : ∀ s : ℂ, s ≠ 1 → F s = riemannZeta s * G s := by
      intro s hs
      simp only [hFdef, hGdef]
      rw [zetaEntire_eq hs]
      ring
    have hUh : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} := fun s hs =>
      (((differentiable_zetaEntire s).const_mul c).mul
        (hPd s hs).differentiableAt.cexp).differentiableWithinAt
    have hFconst : EqOn F (fun _ => H 2) {s : ℂ | 1 / 2 < s.re} := by
      have h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
      refine (hFd.analyticOnNhd hUh).eqOn_of_preconnected_of_eventuallyEq
        (analyticOnNhd_const) (convex_halfSpace_re_gt (1 / 2)).isPreconnected h2 ?_
      filter_upwards [hUo.mem_nhds h2U] with z hz
      have hz1 : 1 < z.re := hz
      have hzne : z ≠ 1 := by intro h; rw [h] at hz1; simp at hz1
      rw [hFG z hzne, show G z = cexp (-L z) from hGL z hz1]
      exact hconst hz
    intro x hx
    refine ⟨‖H 2‖, fun s hs hs1 => ?_⟩
    have hs' : 1 / 2 < s.re := lt_trans hx hs
    rw [← hFG s hs1, hFconst hs']
  · rintro ⟨lam, G, hW, hGd, hGL, hbd⟩
    obtain ⟨G₀, hG₀d, hG₀L, hdet⟩ := riemannZeta_ne_zero_of_bounded_zetaQuotient hW
    have heq := eqOn_of_reciprocalZeta_continuation hGd hG₀d hGL hG₀L
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
    intro s hs
    set x : ℝ := (1 / 2 + s.re) / 2 with hxdef
    have hx : 1 / 2 < x := by rw [hxdef]; linarith
    obtain ⟨M, hM⟩ := hbd x hx
    refine hdet x M hx.le (fun z hz hz1 => ?_) s (by rw [hxdef]; linarith)
    rw [← heq (show 1 / 2 < z.re by linarith)]
    exact hM z hz hz1

end WeilSpectral

/-- The divisor pairs of a prime. -/
theorem divisorsAntidiagonal_of_prime {p : ℕ} (hp : p.Prime) :
    p.divisorsAntidiagonal = {(1, p), (p, 1)} := by
  ext ⟨a, b⟩
  simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hab, -⟩
    have ha : a ∣ p := ⟨b, hab.symm⟩
    rcases hp.eq_one_or_self_of_dvd a ha with rfl | rfl
    · left; exact ⟨rfl, by simpa using hab⟩
    · right
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos (by rw [hab, mul_one])⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hp.ne_zero]

/-- At a prime the Dirichlet exponential is the identity: `exp⋆(f)(p) = f(p)`. -/
theorem dirichletExp_prime {f : ℕ → ℂ} (h0 : f 0 = 0) (h1 : f 1 = 0) {p : ℕ} (hp : p.Prime) :
    GaloisForLFunctions.HTGeometry.dirichletExp f p = f p := by
  open GaloisForLFunctions.HTGeometry in
  have hpow1 : ∀ n : ℕ, n ≠ 0 → dirichletConvPow f 1 n = f n := by
    intro n hn
    rw [dirichletConvPow_succ, LSeries.convolution_def]
    beta_reduce
    rw [Finset.sum_eq_single (n, 1)]
    · simp [dirichletConvPow_zero_apply]
    · intro q hq hne
      rw [Nat.mem_divisorsAntidiagonal] at hq
      have : q.2 ≠ 1 := by
        intro h2
        apply hne
        ext
        · simpa [h2] using hq.1
        · exact h2
      simp [dirichletConvPow_zero_apply, this]
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩) h
  have hpowk : ∀ j : ℕ, dirichletConvPow f (j + 2) p = 0 := by
    intro j
    rw [dirichletConvPow_succ, LSeries.convolution_def]
    beta_reduce
    rw [divisorsAntidiagonal_of_prime hp]
    rw [Finset.sum_insert (by simp [hp.one_lt.ne']), Finset.sum_singleton]
    rw [h1, zero_mul, dirichletConvPow_eq_zero_of_lt h0 h1 (j + 1) 1
      (Nat.one_lt_two_pow (by omega)), mul_zero, add_zero]
  rw [dirichletExp, Finset.sum_eq_single 1]
  · rw [hpow1 p hp.ne_zero]; simp
  · intro k _ hk1
    rcases k with _ | _ | j
    · simp [dirichletConvPow_zero_apply, hp.one_lt.ne']
    · exact absurd rfl hk1
    · rw [hpowk j, zero_div]
  · intro h; exact absurd (Finset.mem_range.mpr (by have := hp.two_le; omega)) h

namespace WeilSpectral

/-- **Bohr's inequality for the zeta quotient.**  For a full-cone producer `lam` with
`|ζ(s)/F_lam(s)| ≤ M` on `Re s > x` (`x ≥ ½`), the prime deviation is absolutely summable on every
line `Re s = σ > x`: `Σ_{p ∈ P} |lam(p) − log p| / log p · p^{−σ} ≤ 2M` for every finite set of
primes `P`. -/
theorem sum_prime_deviation_le_of_bounded_zetaQuotient {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ x M : ℝ, 1 / 2 ≤ x → (∀ s : ℂ, x < s.re → s ≠ 1 → ‖riemannZeta s * G s‖ ≤ M) →
        ∀ σ : ℝ, x < σ → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∑ p ∈ P, |lam p - Real.log p| / Real.log p * (p : ℝ) ^ (-σ) ≤ 2 * M := by
  set lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0 with hlam'
  obtain ⟨c, P₀, hc0, hPd, hGL⟩ := exists_zetaQuotient_primitive hW
  set G : ℂ → ℂ := fun s => c * ((s - 1) * cexp (P₀ s)) with hGdef
  refine ⟨G, fun s hs => ((((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul
    c).differentiableAt.differentiableWithinAt, hGL, fun x M hx hB σ hσ P hP => ?_⟩
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam' n| / (n : ℝ) ^ σ :=
    (herglotzWeilPositive_of_weilPositiveFull hW).summable
  set F : ℂ → ℂ := fun s => c * zetaEntire s * cexp (P₀ s) with hFdef
  have hFG : ∀ s : ℂ, s ≠ 1 → F s = riemannZeta s * G s := by
    intro s hs
    simp only [hFdef, hGdef]
    rw [zetaEntire_eq hs]
    ring
  have hFd : DifferentiableOn ℂ F {z : ℂ | x < z.re} := by
    intro s hs
    have hs' : 1 / 2 < s.re := lt_of_le_of_lt hx hs
    exact (((differentiable_zetaEntire s).const_mul c).mul
      (hPd s hs').differentiableAt.cexp).differentiableWithinAt
  have hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M := by
    intro z hz
    rcases eq_or_ne z 1 with rfl | hz1
    · have hcont : ContinuousAt F 1 := (hFd.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)).continuousAt
      have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), ‖F s‖ ≤ M := by
        have hopen : {s : ℂ | x < s.re} ∈ 𝓝 (1 : ℂ) :=
          (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hopen] with s hs hsx
        rw [hFG s hs]
        exact hB s hsx hs
      exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds).norm hev
    · rw [hFG z hz1]
      exact hB z hz hz1
  set f : ℕ → ℂ := LSeries.convolution 1 (producerMobius lam') with hfdef
  set σ' : ℝ := max 3 (σ + 1) with hσ'
  have hσσ' : σ ≤ σ' := le_trans (by linarith) (le_max_right _ _)
  have h3 : (1 : ℝ) < ((σ' : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]; linarith [le_max_left 3 (σ + 1)]
  have hsumf : LSeriesSummable f ((σ' : ℝ) : ℂ) :=
    (LSeriesSummable_one_iff.mpr h3).convolution (LSeries_producerMobius hsum h3).1
  have hFL : ∀ t : ℝ, F (((σ' : ℝ) : ℂ) + (t : ℂ) * I) =
      LSeries f (((σ' : ℝ) : ℂ) + (t : ℂ) * I) := by
    intro t
    set z : ℂ := ((σ' : ℝ) : ℂ) + (t : ℂ) * I
    have hz1 : 1 < z.re := by simpa [z] using h3
    have hzne : z ≠ 1 := by intro h; rw [h] at hz1; simp at hz1
    obtain ⟨hμs, hμ⟩ := LSeries_producerMobius hsum hz1
    rw [hFG z hzne, hfdef, LSeries_convolution' (LSeriesSummable_one_iff.mpr hz1) hμs,
      LSeries_one_eq_riemannZeta hz1, hμ, ← hGL z hz1]
  have hstrip : {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ'} ⊆ {z : ℂ | x < z.re} :=
    fun z hz => lt_of_lt_of_le hσ hz.1
  have hbohr := GaloisForLFunctions.BohrPrime.sum_norm_prime_coeff_le hσσ' (hFd.mono hstrip)
    (fun z h1 _ => hM z (lt_of_lt_of_le hσ h1)) hsumf hFL hP
  -- the prime coefficients of the zeta quotient
  have h0 : (fun n => -logZetaCoeff lam' n) 0 = 0 := by simp [logZetaCoeff, hlam']
  have h1 : (fun n => -logZetaCoeff lam' n) 1 = 0 := by simp [logZetaCoeff, hlam']
  have hcoef : ∀ p ∈ P, ‖f p‖ = |lam p - Real.log p| / Real.log p := by
    intro p hp
    have hpp := hP p hp
    have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hfp : f p = 1 - ((lam p / Real.log p : ℝ) : ℂ) := by
      rw [hfdef, LSeries.convolution_def]
      simp only
      rw [divisorsAntidiagonal_of_prime hpp, Finset.sum_insert (by simp [hpp.one_lt.ne']),
        Finset.sum_singleton]
      simp only [Pi.one_apply, one_mul]
      simp only [producerMobius]
      rw [dirichletExp_prime h0 h1 hpp, GaloisForLFunctions.HTGeometry.dirichletExp_one h0 h1]
      simp only [logZetaCoeff, hlam', if_pos hpp.two_le]
      ring
    rw [hfp, show (1 : ℂ) - ((lam p / Real.log p : ℝ) : ℂ) =
      (((Real.log p - lam p) / Real.log p : ℝ) : ℂ) by
        push_cast; rw [sub_div, div_self (by exact_mod_cast hlog.ne')],
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlog, abs_sub_comm]
  calc ∑ p ∈ P, |lam p - Real.log p| / Real.log p * (p : ℝ) ^ (-σ)
      = ∑ p ∈ P, ‖f p‖ * (p : ℝ) ^ (-σ) :=
        Finset.sum_congr rfl fun p hp => by rw [hcoef p hp]
    _ ≤ 2 * M := hbohr

end WeilSpectral

end

end RHTower
