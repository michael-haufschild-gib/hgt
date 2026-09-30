import GaloisForLFunctions.RHTower.ZetaFixedSigmaDensity
import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative

/-!
# Self-recurrence of `ζ` around an off-line zero has density zero

Let `ρ₀` be a zero of `ζ` with `½ < Re ρ₀ < 1`, and let `r > 0` be so small that the closed disc
`K = B̄(ρ₀, r)` lies in `½ + r ≤ Re s < 1` and `ζ` has no zero on its boundary circle; put
`m = min_{∂K} |ζ| > 0`.  If `sup_K |ζ(s + iτ) − ζ(s)| < m/2`, then `g(s) = ζ(s + iτ)` satisfies
`|g(ρ₀)| < m/2 < |g|` on `∂K`, so the minimum modulus principle gives a zero `w` of `ζ` in the
translated disc `K + iτ`, with `Re w > Re ρ₀ − r > ½`.  Such a zero absorbs only the shifts `τ` with
`|Im w − Im ρ₀ − τ| ≤ r`, so on a Littlewood window the set of return shifts has measure at most `2r`
times the number of zeros with `Re w ≥ Re ρ₀ − r`, which is `o(T)`
(`eventually_zeroCount_fixedSigma_le`).  Summing over dyadic windows,

  `|{τ ∈ [0, T] : sup_K |ζ(s + iτ) − ζ(s)| < m/2}| = o(T)`
  (`exists_zetaSelfReturn_density_zero`).

Consequently Bagchi's strong recurrence of `ζ` implies the Riemann hypothesis, already when it is
asked only for closed discs of the right half-strip and only with positive upper density
(`riemannHypothesis_of_zetaDiscRecurrent`, `riemannHypothesis_of_zetaStronglyRecurrent`).
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- The shifts `τ` at which `ζ` returns to itself within `ε`, uniformly on `K`. -/
def zetaReturnSet (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∀ s ∈ K, ‖riemannZeta (s + τ * I) - riemannZeta s‖ < ε}

/-- **Bagchi's strong recurrence of `ζ`.** For every compact `K` in `½ < Re s < 1` and every
`ε > 0`, the return shifts in `[0, T]` have positive lower density. -/
def ZetaStronglyRecurrent : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1) → ∀ ε > 0,
    ∃ κ > 0, ∀ᶠ T in atTop, ENNReal.ofReal (κ * T) ≤ volume (zetaReturnSet K ε ∩ Icc 0 T)

/-- **Disc recurrence of `ζ`.** For every closed disc in `½ < Re s < 1` and every `ε > 0`, the
return shifts in `[0, T]` have positive upper density. -/
def ZetaDiscRecurrent : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → (∀ s ∈ closedBall c r, 1 / 2 < s.re ∧ s.re < 1) → ∀ ε > 0,
    ∃ κ > 0, ∃ᶠ T in atTop,
      ENNReal.ofReal (κ * T) ≤ volume (zetaReturnSet (closedBall c r) ε ∩ Icc 0 T)

theorem ZetaStronglyRecurrent.zetaDiscRecurrent (h : ZetaStronglyRecurrent) :
    ZetaDiscRecurrent := fun c r _ hK ε hε =>
  let ⟨κ, hκ, hT⟩ := h _ (isCompact_closedBall c r) hK ε hε
  ⟨κ, hκ, hT.frequently⟩

/-- **A return shift transports the zero.** If `ρ₀` is a zero of `ζ`, `|ζ| ≥ m` on the circle
`|s − ρ₀| = r`, the disc lies in `Re s < 1`, and `τ` is a return shift within `m/2` on the disc, then
`ζ` vanishes in the translated open disc. -/
theorem exists_zero_of_mem_zetaReturnSet {ρ₀ : ℂ} {r m τ : ℝ} (hr : 0 < r)
    (hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1) (hρ₀ : riemannZeta ρ₀ = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖riemannZeta z‖)
    (hτ : τ ∈ zetaReturnSet (closedBall ρ₀ r) (m / 2)) :
    ∃ z ∈ ball ρ₀ r, riemannZeta (z + τ * I) = 0 := by
  have hdiff : DifferentiableOn ℂ (fun s => riemannZeta (s + τ * I)) (closedBall ρ₀ r) := by
    intro s hs
    have hne : s + τ * I ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, one_re] at h'
      linarith [hre s hs]
    exact ((differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  refine DeBruijn.exists_zero_of_norm_lt_sphere_on hr hdiff fun z hz => ?_
  have h1 := hτ ρ₀ (mem_closedBall_self hr.le)
  rw [hρ₀, sub_zero] at h1
  have h2 := hτ z (sphere_subset_closedBall hz)
  have h3 := hm z hz
  have h4 := norm_sub_norm_le (riemannZeta z) (riemannZeta (z + τ * I))
  rw [norm_sub_rev] at h4
  linarith

/-- **An isolating disc around an off-line zero.** There is a radius `r ≤ (Re ρ₀ − ½)/2`,
`r ≤ (1 − Re ρ₀)/2`, and a floor `m > 0` for `|ζ|` on the circle `|s − ρ₀| = r`. -/
theorem exists_zetaIsolatingDisc {ρ₀ : ℂ} (h1 : 1 / 2 < ρ₀.re) (h2 : ρ₀.re < 1) :
    ∃ r > 0, r ≤ (ρ₀.re - 1 / 2) / 2 ∧ r ≤ (1 - ρ₀.re) / 2 ∧
      ∃ m > 0, ∀ z ∈ sphere ρ₀ r, m ≤ ‖riemannZeta z‖ := by
  have hρ1 : ρ₀ ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have han : AnalyticAt ℂ riemannZeta ρ₀ := hdiff.analyticAt (isOpen_ne.mem_nhds hρ1)
  have hne : ∀ᶠ z in 𝓝[≠] ρ₀, riemannZeta z ≠ 0 := by
    refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => ?_
    exact analyticOrderAt_riemannZeta_ne_top_of_ne_one hρ1 (analyticOrderAt_eq_top.mpr h)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r := min (r₁ / 2) (min ((ρ₀.re - 1 / 2) / 2) ((1 - ρ₀.re) / 2)) with hrdef
  have hr : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hrr₁ : r < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hr2 : r ≤ (ρ₀.re - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (1 - ρ₀.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsph : ∀ z ∈ sphere ρ₀ r, riemannZeta z ≠ 0 ∧ z ≠ 1 := by
    intro z hz
    have hd : dist z ρ₀ = r := mem_sphere.mp hz
    have hzρ : z ≠ ρ₀ := by intro h; rw [h, dist_self] at hd; linarith
    refine ⟨hball (by rw [hd]; exact hrr₁) hzρ, fun h => ?_⟩
    have hre := abs_re_le_norm (z - ρ₀)
    rw [← dist_eq_norm, hd, h, sub_re, one_re] at hre
    have := le_abs_self (1 - ρ₀.re)
    linarith
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere ρ₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (fun z hz => (differentiableAt_riemannZeta (hsph z hz).2).continuousAt.continuousWithinAt.norm)
  exact ⟨r, hr, hr2, hr3, ‖riemannZeta z₁‖, norm_pos_iff.mpr (hsph z₁ hz₁).1,
    fun z hz => hmin hz⟩

/-- **Return shifts on one window.** For every `δ > 0`, for all large `V` the return shifts in
`[(V − Im ρ₀)/2, V]` have measure at most `δ V`. -/
theorem eventually_volume_zetaReturnSet_window_le {ρ₀ : ℂ} {r m : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2) (hρ₀ : riemannZeta ρ₀ = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖riemannZeta z‖) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ V in atTop, volume (zetaReturnSet (closedBall ρ₀ r) (m / 2) ∩
      Icc ((V - ρ₀.im) / 2) V) ≤ ENNReal.ofReal (δ * V) := by
  classical
  set γ₀ := ρ₀.im
  set E := zetaReturnSet (closedBall ρ₀ r) (m / 2)
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
    obtain ⟨z, hz, hz0⟩ := exists_zero_of_mem_zetaReturnSet hr (fun s hs => (hre s hs).2) hρ₀
      hm hτE
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

/-- **Density zero from dyadic windows.** If for every `δ > 0` the part of `E` in
`[(V − γ)/2, V]` eventually has measure `≤ δ V`, then `E` has density zero in `[0, T]`. -/
theorem eventually_volume_inter_Icc_le_of_window {E : Set ℝ} {γ : ℝ}
    (hwin : ∀ δ > 0, ∀ᶠ V in atTop, volume (E ∩ Icc ((V - γ) / 2) V) ≤ ENNReal.ofReal (δ * V))
    {κ : ℝ} (hκ : 0 < κ) : ∀ᶠ T in atTop, volume (E ∩ Icc 0 T) ≤ ENNReal.ofReal (κ * T) := by
  set δ := κ / 8 with hδdef
  have hδ : 0 < δ := by positivity
  set A := |γ| * (1 + δ)
  have hA : 0 ≤ A := by positivity
  have hstep : ∀ q : ℕ, ∀ᶠ V in atTop,
      volume (E ∩ Icc 0 V) ≤ ENNReal.ofReal (V / 2 ^ q + q * A + 2 * δ * V) := by
    intro q
    induction q with
    | zero =>
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
      calc volume (E ∩ Icc 0 V) ≤ volume (Icc 0 V) := measure_mono inter_subset_right
        _ = ENNReal.ofReal V := by rw [Real.volume_Icc, sub_zero]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by simp; positivity)
    | succ q ih =>
      obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ih
      filter_upwards [hwin δ hδ, eventually_ge_atTop (2 * max W₀ 0 + |γ|)] with V hV hVbig
      have hγ := le_abs_self γ
      have hγ' := neg_abs_le γ
      have hW : W₀ ≤ (V - γ) / 2 := by linarith [le_max_left W₀ 0]
      have hW0 : 0 ≤ (V - γ) / 2 := by linarith [le_max_right W₀ 0]
      have hV0 : 0 ≤ V := by linarith [le_max_right W₀ 0, abs_nonneg γ]
      have h1 := hW₀ _ hW
      have hsplit : E ∩ Icc 0 V ⊆ E ∩ Icc 0 ((V - γ) / 2) ∪ E ∩ Icc ((V - γ) / 2) V := by
        rw [← inter_union_distrib_left]
        refine inter_subset_inter_right _ fun x hx => ?_
        rcases le_total x ((V - γ) / 2) with h | h
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr ⟨h, hx.2⟩
      have hpow : (0 : ℝ) < 2 ^ (q + 1) := by positivity
      have hpow' : (2 : ℝ) ^ (q + 1) = 2 * 2 ^ q := by ring
      have hkey : (V - γ) / 2 / 2 ^ q + q * A + 2 * δ * ((V - γ) / 2) + δ * V ≤
          V / 2 ^ (q + 1) + ((q + 1 : ℕ) : ℝ) * A + 2 * δ * V := by
        have e1 : (V - γ) / 2 / 2 ^ q = V / 2 ^ (q + 1) - γ / 2 ^ (q + 1) := by
          rw [hpow']; field_simp
        have e2 : -(γ / 2 ^ (q + 1)) ≤ |γ| := (neg_le_abs _).trans (by
          rw [abs_div, abs_of_pos hpow]
          exact div_le_self (abs_nonneg γ) (one_le_pow₀ (by norm_num)))
        rw [e1]
        push_cast
        nlinarith [abs_nonneg γ]
      calc volume (E ∩ Icc 0 V)
          ≤ volume (E ∩ Icc 0 ((V - γ) / 2)) + volume (E ∩ Icc ((V - γ) / 2) V) :=
            (measure_mono hsplit).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal ((V - γ) / 2 / 2 ^ q + q * A + 2 * δ * ((V - γ) / 2)) +
              ENNReal.ofReal (δ * V) := add_le_add h1 hV
        _ = ENNReal.ofReal ((V - γ) / 2 / 2 ^ q + q * A + 2 * δ * ((V - γ) / 2) + δ * V) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hkey
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one (show 0 < κ / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  filter_upwards [hstep q, eventually_ge_atTop (4 * q * A / κ), eventually_ge_atTop (0 : ℝ)]
    with T hT hTbig hT0
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : T / 2 ^ q ≤ κ / 4 * T := by
    rw [div_eq_mul_one_div, one_div, ← inv_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (by rw [inv_eq_one_div]; exact hq.le) hT0
  have h2 : q * A ≤ κ / 4 * T := by
    rw [div_le_iff₀ hκ] at hTbig
    linarith
  have h3 := mul_nonneg hκ.le hT0
  rw [hδdef]
  linarith

/-- **Self-recurrence around an off-line zero has density zero.** For every zero `ρ₀` of `ζ` with
`½ < Re ρ₀ < 1` there are a closed disc `B̄(ρ₀, r)` inside `½ < Re s < 1` and an `ε > 0` such
that the shifts `τ ∈ [0, T]` with `sup_{B̄(ρ₀, r)} |ζ(s + iτ) − ζ(s)| < ε` have measure `o(T)`. -/
theorem exists_zetaSelfReturn_density_zero {ρ₀ : ℂ} (hρ₀ : riemannZeta ρ₀ = 0)
    (h1 : 1 / 2 < ρ₀.re) (h2 : ρ₀.re < 1) :
    ∃ r > 0, (∀ s ∈ closedBall ρ₀ r, 1 / 2 < s.re ∧ s.re < 1) ∧ ∃ ε > 0, ∀ κ > 0,
      ∀ᶠ T in atTop,
        volume (zetaReturnSet (closedBall ρ₀ r) ε ∩ Icc 0 T) ≤ ENNReal.ofReal (κ * T) := by
  obtain ⟨r, hr, hr2, hr3, m, hm0, hm⟩ := exists_zetaIsolatingDisc h1 h2
  refine ⟨r, hr, fun s hs => ?_, m / 2, by positivity, fun κ hκ =>
    eventually_volume_inter_Icc_le_of_window
      (fun δ hδ => eventually_volume_zetaReturnSet_window_le hr hr2 hr3 hρ₀ hm hδ) hκ⟩
  have h := abs_le.mp ((abs_re_le_norm (s - ρ₀)).trans (mem_closedBall_iff_norm.mp hs))
  rw [sub_re] at h
  constructor <;> linarith [h.1, h.2]

/-- **Disc recurrence of `ζ` implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_zetaDiscRecurrent (h : ZetaDiscRecurrent) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs1 hs2 hs0
  obtain ⟨r, hr, hK, ε, hε, hdens⟩ := exists_zetaSelfReturn_density_zero hs0 hs1 hs2
  obtain ⟨κ, hκ, hfreq⟩ := h s r hr hK ε hε
  obtain ⟨T, hT1, hT2, hT0⟩ :=
    (hfreq.and_eventually ((hdens (κ / 2) (by positivity)).and (eventually_gt_atTop 0))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith

/-- **Bagchi's criterion, sufficient direction.** Strong recurrence of `ζ` implies the Riemann
hypothesis. -/
theorem riemannHypothesis_of_zetaStronglyRecurrent (h : ZetaStronglyRecurrent) :
    RiemannHypothesis :=
  riemannHypothesis_of_zetaDiscRecurrent h.zetaDiscRecurrent

end

end RHTower
