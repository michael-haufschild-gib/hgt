import GaloisForLFunctions.SquareRootThreshold.CountingInputsDoNotBoundTheLocalCount
import GaloisForLFunctions.RHTower.ZetaOffLineMomentExplicit
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.SquareRootThreshold.TheOffLineSecondMomentIsLittleO

/-!
# The local count holds for almost all heights

For the zeros of `ζ`, the local count at scale `δ` fails with any constant `C` only on a set of
heights of density zero (`eventually_volume_zeta_localCount_gt_le`): for all large `T`,

  `|{t ∈ [T, 2T] : #disc(½ + δ + it, δ) > C(δ log t + 1)}| ≤ T/(C√(δ log T))`.

**Proof.**  The disc about `½ + δ + it` is tangent to the critical line, so a zero of depth
`η = Re ρ − ½` lies in it only for `|t − Im ρ| ≤ √(2δη₊)`: a critical zero is seen at one height.
Fubini and Markov (`volume_localCount_gt_le_sqrt`) bound the measure by
`Σ_ρ m_ρ 2√(2δη₊)/(C(δ log T + 1))`.  Cauchy–Schwarz gives
`(Σ m 2√(2δη₊))² ≤ 8δ N(T − 1, 2T + 1) Σ m η₊` (`sq_sum_sqrt_le`), with `N ≤ (T/5) log T` from
Riemann–von Mangoldt and the off-line first moment `Σ m η₊ ≤ (21/100)(2T + 1)`
(`eventually_offLineMoment_le`).  Hence the sum is `≤ T√(δ log T)`.

With `CountingInputsDoNotBoundTheLocalCount`: no counting input gives the local count at every
height, but the zeros of `ζ` satisfy it on a set of density one, through the off-line first moment.

**The depth mass in density** (`eventually_volume_rightDepthMass_gt_le`).  For every `W > 0`
the right-half depth mass `Σ_{Re ρ > ½} m (Re ρ − ½)²` of the windows `(S − 1, S + 1]` is `≤ W` off a
set of centres `S ∈ [T − 1, 2T + 1]` of measure `o(T)`: Markov with the second moment `o(V)`
(`tendsto_offLineSecondMoment_div`).
-/

open Complex Set Zeta23

namespace RHTower.LocalCountFalsifier

noncomputable section

open Classical

/-- **Tangency.**  A zero of depth `η` lies in the disc about `½ + δ + it` only for
`|t − Im ρ| ≤ √(2δη₊)`. -/
theorem abs_sub_im_le_of_mem_disc {δ t : ℝ} {ρ : ℂ}
    (h : ρ ∈ Metric.closedBall (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ) (hδ : 0 < δ) :
    |ρ.im - t| ≤ Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0) := by
  have hd : ‖ρ - (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ δ := by
    rw [← Complex.dist_eq]; exact Metric.mem_closedBall.mp h
  have hsq : ‖ρ - (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
      = (ρ.re - 1 / 2 - δ) ^ 2 + (ρ.im - t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
    ring
  have h2 : (ρ.re - 1 / 2 - δ) ^ 2 + (ρ.im - t) ^ 2 ≤ δ ^ 2 := by
    rw [← hsq]; exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  refine Real.abs_le_sqrt ?_
  rcases le_or_gt (ρ.re - 1 / 2) 0 with hη | hη
  · rw [max_eq_right hη]; nlinarith
  · rw [max_eq_left hη.le]; nlinarith

/-- **Fubini–Markov with tangency.**  For `0 < δ ≤ ½`, `C > 0`, `T > 1`, the heights `t ∈ [T, 2T]`
violating the local count with constant `C` have measure at most
`Σ_ρ m_ρ 2√(2δη₊)/(C(δ log T + 1))`, over the zeros of `(T − 1, 2T + 1]`. -/
theorem volume_localCount_gt_le_sqrt (Z : ZeroConfig) {δ C T : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2) (hC : 0 < C) (hT : 1 < T) :
    MeasureTheory.volume {t ∈ Icc T (2 * T) |
        C * (δ * Real.log t + 1) < discCount Z (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ}
      ≤ ENNReal.ofReal ((∑ ρ ∈ (Z.finite_window (T - 1) (2 * T + 1)).toFinset,
          (Z.mult ρ : ℝ) * (2 * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0)))
          / (C * (δ * Real.log T + 1))) := by
  set F := (Z.finite_window (T - 1) (2 * T + 1)).toFinset with hF
  set c : ℝ → ℂ := fun t => ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I with hc
  set s : ℂ → ℝ := fun ρ => Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0) with hs
  set B : ℂ → Set ℝ := fun ρ => {t | ρ ∈ Metric.closedBall (c t) δ} with hBdef
  have hcont : Continuous c := by rw [hc]; fun_prop
  have hB : ∀ ρ, MeasurableSet (B ρ) := fun ρ =>
    (isClosed_le (continuous_const.dist hcont) continuous_const).measurableSet
  have hBsub : ∀ ρ, B ρ ⊆ Icc (ρ.im - s ρ) (ρ.im + s ρ) := by
    intro ρ t ht
    have := abs_le.mp (abs_sub_im_le_of_mem_disc ht hδ0)
    exact ⟨by linarith, by linarith⟩
  set g : ℝ → ENNReal := fun t => ∑ ρ ∈ F, (B ρ).indicator (fun _ => (Z.mult ρ : ENNReal)) t with hg
  have hgm : Measurable g := Finset.measurable_sum _ fun ρ _ => measurable_const.indicator (hB ρ)
  have hcount : ∀ t ∈ Icc T (2 * T), ((discCount Z (c t) δ : ℕ) : ENNReal) = g t := by
    intro t ht
    rw [discCount_eq_sum Z hδ ht, hg, Nat.cast_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Set.indicator_apply, hBdef, Set.mem_setOf_eq]
    split_ifs <;> simp
  have hint : ∫⁻ t in Icc T (2 * T), g t
      ≤ ∑ ρ ∈ F, (Z.mult ρ : ENNReal) * ENNReal.ofReal (2 * s ρ) := by
    rw [hg, MeasureTheory.lintegral_finsetSum _ fun ρ _ => measurable_const.indicator (hB ρ)]
    refine Finset.sum_le_sum fun ρ _ => ?_
    rw [MeasureTheory.lintegral_indicator_const (hB ρ)]
    gcongr
    calc (MeasureTheory.volume.restrict (Icc T (2 * T))) (B ρ) ≤ MeasureTheory.volume (B ρ) :=
          MeasureTheory.Measure.restrict_le_self _
      _ ≤ MeasureTheory.volume (Icc (ρ.im - s ρ) (ρ.im + s ρ)) :=
          MeasureTheory.measure_mono (hBsub ρ)
      _ = ENNReal.ofReal (2 * s ρ) := by rw [Real.volume_Icc]; ring_nf
  have hL : 0 < Real.log T := Real.log_pos hT
  set M : ℝ := C * (δ * Real.log T + 1) with hM
  have hM0 : 0 < M := by positivity
  have hset : {t ∈ Icc T (2 * T) | C * (δ * Real.log t + 1) < discCount Z (c t) δ}
      ⊆ {t | ENNReal.ofReal M ≤ g t} ∩ Icc T (2 * T) := by
    rintro t ⟨ht, hlt⟩
    refine ⟨?_, ht⟩
    have hlog : Real.log T ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    have hMle : M ≤ (discCount Z (c t) δ : ℝ) := by
      have : M ≤ C * (δ * Real.log t + 1) := by rw [hM]; gcongr
      linarith
    show ENNReal.ofReal M ≤ g t
    rw [← hcount t ht, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hMle
  have hs0 : ∀ ρ, 0 ≤ s ρ := fun ρ => Real.sqrt_nonneg _
  have hsumF : ∑ ρ ∈ F, (Z.mult ρ : ENNReal) * ENNReal.ofReal (2 * s ρ)
      = ENNReal.ofReal (∑ ρ ∈ F, (Z.mult ρ : ℝ) * (2 * s ρ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun ρ _ =>
      mul_nonneg (Nat.cast_nonneg _) (by linarith [hs0 ρ])]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc MeasureTheory.volume {t ∈ Icc T (2 * T) | C * (δ * Real.log t + 1) < discCount Z (c t) δ}
      ≤ MeasureTheory.volume ({t | ENNReal.ofReal M ≤ g t} ∩ Icc T (2 * T)) :=
        MeasureTheory.measure_mono hset
    _ = (MeasureTheory.volume.restrict (Icc T (2 * T))) {t | ENNReal.ofReal M ≤ g t} :=
        (MeasureTheory.Measure.restrict_apply' measurableSet_Icc).symm
    _ ≤ (∫⁻ t in Icc T (2 * T), g t) / ENNReal.ofReal M :=
        MeasureTheory.meas_ge_le_lintegral_div hgm.aemeasurable
          (by simpa using hM0) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (∑ ρ ∈ F, (Z.mult ρ : ℝ) * (2 * s ρ)) / ENNReal.ofReal M := by
        rw [← hsumF]; gcongr
    _ = _ := (ENNReal.ofReal_div_of_pos hM0).symm

/-- **Cauchy–Schwarz.**  `(Σ m 2√(2δη₊))² ≤ 8δ (Σ m)(Σ m η₊)`. -/
theorem sq_sum_sqrt_le (F : Finset ℂ) (m : ℂ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ ρ ∈ F, (m ρ : ℝ) * (2 * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0))) ^ 2
      ≤ 8 * δ * (∑ ρ ∈ F, (m ρ : ℝ)) * ∑ ρ ∈ F, (m ρ : ℝ) * max (ρ.re - 1 / 2) 0 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun ρ => Real.sqrt (m ρ))
    (fun ρ => 2 * Real.sqrt (m ρ) * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0))
  have hm : ∀ ρ, Real.sqrt (m ρ) * Real.sqrt (m ρ) = (m ρ : ℝ) := fun ρ =>
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hx : ∀ ρ : ℂ, 0 ≤ 2 * δ * max (ρ.re - 1 / 2) 0 := fun ρ => by positivity
  have e1 : ∀ ρ, Real.sqrt (m ρ) * (2 * Real.sqrt (m ρ) * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0))
      = (m ρ : ℝ) * (2 * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0)) := fun ρ => by
    rw [show Real.sqrt (m ρ) * (2 * Real.sqrt (m ρ) * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0))
      = (Real.sqrt (m ρ) * Real.sqrt (m ρ))
        * (2 * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0)) by ring,
      hm ρ]
  have e2 : ∀ ρ, Real.sqrt (m ρ) ^ 2 = (m ρ : ℝ) := fun ρ => Real.sq_sqrt (Nat.cast_nonneg _)
  have e3 : ∀ ρ, (2 * Real.sqrt (m ρ) * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0)) ^ 2
      = 8 * δ * ((m ρ : ℝ) * max (ρ.re - 1 / 2) 0) := fun ρ => by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (hx ρ)]; ring
  simp only [e1, e2, e3, ← Finset.mul_sum] at hcs
  linarith

/-- The off-line part of a window sum is bounded by the corpus off-line moment. -/
theorem sum_mult_max_le_offLineMoment {T : ℝ} (hT : 1 ≤ T) :
    ∑ ρ ∈ (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)).toFinset,
        (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0
      ≤ offLineMoment (2 * T + 1) := by
  set F := (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)).toFinset with hF
  have hsplit : ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0
      = ∑ ρ ∈ F.filter (fun ρ => 1 / 2 < ρ.re),
          ((analyticOrderAt xi ρ).toNat : ℝ) * (ρ.re - 1 / 2) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    split_ifs with h
    · rw [max_eq_left (by linarith)]
      have hc : ρ ∈ zetaZeroConfig.carrier := ((Set.Finite.mem_toFinset _).mp hρ).1
      have := WeilConditional.mult_eq_analyticOrderNatAt ⟨ρ, hc⟩
      simp only at this
      rw [this, analyticOrderNatAt]
    · rw [max_eq_right (by linarith), mul_zero]
  rw [hsplit, offLineMoment]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z hz _ => offLineMoment_term_nonneg hz
  intro ρ hρ
  obtain ⟨hρF, hre⟩ := Finset.mem_filter.mp hρ
  obtain ⟨hc, hlo, hhi⟩ := (Set.Finite.mem_toFinset _).mp hρF
  obtain ⟨hxi, -, hre1⟩ :=
    CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hc
  rw [mem_boxFinsetLe]
  exact ⟨hre, hre1, by linarith, hhi, hxi⟩

/-- **The local count holds for almost all heights.**  For `0 < δ ≤ ½` and `C > 0`, for all large
`T`, the heights `t ∈ [T, 2T]` where the disc about `½ + δ + it` holds more than `C(δ log t + 1)`
zeros of `ζ` have measure at most `T/(C√(δ log T))`. -/
theorem eventually_volume_zeta_localCount_gt_le {δ C : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hC : 0 < C) :
    ∀ᶠ T in Filter.atTop, MeasureTheory.volume {t ∈ Icc T (2 * T) |
        C * (δ * Real.log t + 1) <
          discCount zetaZeroConfig (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ}
      ≤ ENNReal.ofReal (T / (C * Real.sqrt (δ * Real.log T))) := by
  obtain ⟨K, hK⟩ := exists_N_window_le riemannVonMangoldt_zeta
  obtain ⟨V₀, hV₀⟩ := Filter.eventually_atTop.mp ZetaGateProductAFE.eventually_offLineMoment_le
  filter_upwards [hK, Filter.eventually_ge_atTop (30 * |K| + 21 + |V₀|),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with T hNT hT hL1
  have hMom := hV₀ (2 * T + 1) (by linarith [le_abs_self V₀, abs_nonneg K, abs_nonneg V₀])
  have hT1 : 1 < T := by linarith [abs_nonneg K, abs_nonneg V₀]
  have hL : 0 < Real.log T := by linarith
  set F := (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)).toFinset with hF
  set S := ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * (2 * Real.sqrt (2 * δ * max (ρ.re - 1 / 2) 0))
    with hS
  refine (volume_localCount_gt_le_sqrt zetaZeroConfig hδ0 hδ hC hT1).trans
    (ENNReal.ofReal_le_ofReal ?_)
  -- the window count and the off-line moment
  have hN : ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) = zetaZeroConfig.N (T - 1) (2 * T + 1) := by
    rw [ZeroConfig.N, ZeroConfig.window, finsum_mem_eq_finite_toFinset_sum _
      (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)), Nat.cast_sum]
  have hNle : (zetaZeroConfig.N (T - 1) (2 * T + 1) : ℝ) ≤ T / 5 * Real.log T := by
    have h2π : T / (2 * Real.pi) ≤ T / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]
    have hKT : |K| * Real.log T ≤ T / 30 * Real.log T :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg V₀]) hL.le
    nlinarith [mul_le_mul_of_nonneg_right h2π hL.le, le_abs_self K]
  have hmom := (sum_mult_max_le_offLineMoment (T := T) (by linarith)).trans hMom
  have hmom' : ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ≤ 43 / 100 * T := by
    linarith [abs_nonneg K, abs_nonneg V₀]
  have hmom0 : 0 ≤ ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 :=
    Finset.sum_nonneg fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  have hN0 : 0 ≤ ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) :=
    Finset.sum_nonneg fun ρ _ => Nat.cast_nonneg _
  -- `S² ≤ T² δ log T`, so `S ≤ T√(δ log T)`
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun ρ _ =>
    mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hS2 : S ^ 2 ≤ (T * Real.sqrt (δ * Real.log T)) ^ 2 := by
    have hcs := sq_sum_sqrt_le F zetaZeroConfig.mult hδ0.le
    rw [← hS] at hcs
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hN] at hcs hN0
    have h1 : (zetaZeroConfig.N (T - 1) (2 * T + 1) : ℝ)
        * ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0
        ≤ T / 5 * Real.log T * (43 / 100 * T) :=
      mul_le_mul hNle hmom' hmom0 (by positivity)
    nlinarith
  have hSle : S ≤ T * Real.sqrt (δ * Real.log T) :=
    (pow_le_pow_iff_left₀ hS0 (by positivity) (by norm_num)).mp hS2
  -- divide by `C(δ log T + 1) ≥ Cδ log T`
  have hx : 0 < δ * Real.log T := by positivity
  have hsx : 0 < Real.sqrt (δ * Real.log T) := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt (δ * Real.log T) * Real.sqrt (δ * Real.log T) = δ * Real.log T :=
    Real.mul_self_sqrt hx.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc S * (C * Real.sqrt (δ * Real.log T))
      ≤ T * Real.sqrt (δ * Real.log T) * (C * Real.sqrt (δ * Real.log T)) :=
        mul_le_mul_of_nonneg_right hSle (by positivity)
    _ = T * (C * (δ * Real.log T)) := by
        rw [show T * Real.sqrt (δ * Real.log T) * (C * Real.sqrt (δ * Real.log T))
          = T * C * (Real.sqrt (δ * Real.log T) * Real.sqrt (δ * Real.log T)) by ring, hsq]
        ring
    _ ≤ T * (C * (δ * Real.log T + 1)) := by nlinarith

/-! ## The depth mass in density -/

/-- The right-half depth mass `Σ m (Re ρ − ½)₊²` of the window `(S − 1, S + 1]`. -/
def rightDepthMass (Z : ZeroConfig) (S : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ Z.window (S - 1) (S + 1), (Z.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2

/-- On `S ∈ [T − 1, 2T + 1]` the depth mass is a finite sum of indicators of intervals of
length `2`. -/
theorem rightDepthMass_eq_sum (Z : ZeroConfig) {T S : ℝ} (hS : S ∈ Icc (T - 1) (2 * T + 1)) :
    rightDepthMass Z S = ∑ ρ ∈ (Z.finite_window (T - 2) (2 * T + 2)).toFinset,
      (Ico (ρ.im - 1) (ρ.im + 1)).indicator
        (fun _ => (Z.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2) S := by
  set F := (Z.finite_window (T - 2) (2 * T + 2)).toFinset with hF
  have hsub : Z.window (S - 1) (S + 1) ⊆ Z.window (T - 2) (2 * T + 2) := by
    rintro ρ ⟨hc, h1, h2⟩
    exact ⟨hc, by linarith [hS.1], by linarith [hS.2]⟩
  have hfinS := Z.finite_window (S - 1) (S + 1)
  show (∑ᶠ ρ ∈ Z.carrier ∩ {ρ | S - 1 < ρ.im ∧ ρ.im ≤ S + 1},
    (Z.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfinS,
    ← Finset.sum_filter_add_sum_filter_not F (fun ρ => ρ ∈ Z.window (S - 1) (S + 1))]
  have h0 : ∑ ρ ∈ F.filter (fun ρ => ρ ∉ Z.window (S - 1) (S + 1)),
      (Ico (ρ.im - 1) (ρ.im + 1)).indicator
        (fun _ => (Z.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2) S = 0 := by
    refine Finset.sum_eq_zero fun ρ hρ => ?_
    obtain ⟨hρF, hρw⟩ := Finset.mem_filter.mp hρ
    rw [Set.indicator_of_notMem]
    intro hSB
    apply hρw
    have hρw' := (Set.Finite.mem_toFinset _).mp hρF
    exact ⟨hρw'.1, by linarith [hSB.2], by linarith [hSB.1]⟩
  rw [h0, add_zero]
  refine Finset.sum_congr ?_ fun ρ hρ => ?_
  · ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, hF]
    exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
  · rw [Finset.mem_filter] at hρ
    rw [Set.indicator_of_mem]
    exact ⟨by linarith [hρ.2.2.2], by linarith [hρ.2.2.1]⟩

/-- The window sum of `m (Re ρ − ½)₊²` is at most the second moment. -/
theorem sum_window_le_offLineSecondMoment {T : ℝ} (hT : 2 ≤ T) :
    ∑ ρ ∈ (zetaZeroConfig.finite_window (T - 2) (2 * T + 2)).toFinset,
        (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2
      ≤ offLineSecondMoment (2 * T + 2) := by
  set F := (zetaZeroConfig.finite_window (T - 2) (2 * T + 2)).toFinset with hF
  have hsplit : ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2
      = ∑ ρ ∈ F.filter (fun ρ => 1 / 2 < ρ.re),
          ((analyticOrderAt xi ρ).toNat : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    split_ifs with h
    · have hc : ρ ∈ zetaZeroConfig.carrier := ((Set.Finite.mem_toFinset _).mp hρ).1
      have := WeilConditional.mult_eq_analyticOrderNatAt ⟨ρ, hc⟩
      simp only at this
      rw [this, analyticOrderNatAt]
    · rw [max_eq_right (by linarith), sq, mul_zero, mul_zero]
  rw [hsplit, offLineSecondMoment]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z _ _ => by positivity
  intro ρ hρ
  obtain ⟨hρF, hre⟩ := Finset.mem_filter.mp hρ
  obtain ⟨hc, hlo, hhi⟩ := (Set.Finite.mem_toFinset _).mp hρF
  obtain ⟨hxi, hre0, hre1⟩ :=
    CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hc
  rw [mem_stripFinsetPos]
  exact ⟨hre0, hre1, by linarith, hhi, hxi⟩

/-- **The depth-weighted local input holds for almost all window centres.**  For `W > 0` and
`ε > 0`, for all large `T`, the centres `S ∈ [T − 1, 2T + 1]` whose window `(S − 1, S + 1]` has
right-half depth mass `> W` have measure `≤ εT`. -/
theorem eventually_volume_rightDepthMass_gt_le {W ε : ℝ} (hW : 0 < W) (hε : 0 < ε) :
    ∀ᶠ T in atTop, MeasureTheory.volume
      {S ∈ Icc (T - 1) (2 * T + 1) | W < rightDepthMass zetaZeroConfig S}
        ≤ ENNReal.ofReal (ε * T) := by
  set δ := ε * W / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  have hmom : ∀ᶠ T : ℝ in atTop, offLineSecondMoment (2 * T + 2) ≤ δ * (2 * T + 2) := by
    have h := (tendsto_offLineSecondMoment_div.eventually (gt_mem_nhds hδ0)).and
      (eventually_gt_atTop (0 : ℝ))
    have hlin : Tendsto (fun T : ℝ => 2 * T + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 (tendsto_id.const_mul_atTop (by norm_num))
    filter_upwards [hlin.eventually h] with T hT
    obtain ⟨h1, h2⟩ := hT
    rw [div_lt_iff₀ h2] at h1
    exact h1.le
  filter_upwards [hmom, eventually_ge_atTop (2 : ℝ)] with T hmT hT2
  set F := (zetaZeroConfig.finite_window (T - 2) (2 * T + 2)).toFinset with hF
  set w : ℂ → ℝ := fun ρ => (zetaZeroConfig.mult ρ : ℝ) * max (ρ.re - 1 / 2) 0 ^ 2 with hw
  have hw0 : ∀ ρ, 0 ≤ w ρ := fun ρ => by positivity
  set g : ℝ → ENNReal := fun S => ∑ ρ ∈ F,
    (Ico (ρ.im - 1) (ρ.im + 1)).indicator (fun _ => ENNReal.ofReal (w ρ)) S with hg
  have hgm : Measurable g := Finset.measurable_sum _ fun ρ _ =>
    measurable_const.indicator measurableSet_Ico
  have hgS : ∀ S ∈ Icc (T - 1) (2 * T + 1),
      ENNReal.ofReal (rightDepthMass zetaZeroConfig S) = g S := by
    intro S hS
    rw [rightDepthMass_eq_sum zetaZeroConfig hS, ENNReal.ofReal_sum_of_nonneg fun ρ _ =>
      Set.indicator_nonneg (fun _ _ => hw0 ρ) _]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hint : ∫⁻ S in Icc (T - 1) (2 * T + 1), g S ≤ ENNReal.ofReal (2 * ∑ ρ ∈ F, w ρ) := by
    rw [hg, MeasureTheory.lintegral_finsetSum _ fun ρ _ =>
      measurable_const.indicator measurableSet_Ico]
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun ρ _ => by linarith [hw0 ρ]]
    refine Finset.sum_le_sum fun ρ _ => ?_
    rw [MeasureTheory.lintegral_indicator_const measurableSet_Ico]
    calc ENNReal.ofReal (w ρ) * (MeasureTheory.volume.restrict (Icc (T - 1) (2 * T + 1)))
          (Ico (ρ.im - 1) (ρ.im + 1))
        ≤ ENNReal.ofReal (w ρ) * MeasureTheory.volume (Ico (ρ.im - 1) (ρ.im + 1)) := by
          gcongr; exact MeasureTheory.Measure.restrict_le_self _
      _ = ENNReal.ofReal (2 * w ρ) := by
          rw [Real.volume_Ico, ← ENNReal.ofReal_mul (hw0 ρ)]; ring_nf
  have hset : {S ∈ Icc (T - 1) (2 * T + 1) | W < rightDepthMass zetaZeroConfig S}
      ⊆ {S | ENNReal.ofReal W ≤ g S} ∩ Icc (T - 1) (2 * T + 1) := by
    rintro S ⟨hS, hlt⟩
    exact ⟨by rw [Set.mem_setOf_eq, ← hgS S hS]; exact ENNReal.ofReal_le_ofReal hlt.le, hS⟩
  have hsum := sum_window_le_offLineSecondMoment hT2
  calc MeasureTheory.volume {S ∈ Icc (T - 1) (2 * T + 1) | W < rightDepthMass zetaZeroConfig S}
      ≤ MeasureTheory.volume ({S | ENNReal.ofReal W ≤ g S} ∩ Icc (T - 1) (2 * T + 1)) :=
        MeasureTheory.measure_mono hset
    _ = (MeasureTheory.volume.restrict (Icc (T - 1) (2 * T + 1))) {S | ENNReal.ofReal W ≤ g S} :=
        (MeasureTheory.Measure.restrict_apply' measurableSet_Icc).symm
    _ ≤ (∫⁻ S in Icc (T - 1) (2 * T + 1), g S) / ENNReal.ofReal W :=
        MeasureTheory.meas_ge_le_lintegral_div hgm.aemeasurable (by simpa using hW)
          ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * ∑ ρ ∈ F, w ρ) / ENNReal.ofReal W := by gcongr
    _ = ENNReal.ofReal (2 * ∑ ρ ∈ F, w ρ / W) := by
        rw [← ENNReal.ofReal_div_of_pos hW, mul_div_assoc]
    _ ≤ ENNReal.ofReal (ε * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ hW]
        have : 2 * ∑ ρ ∈ F, w ρ ≤ 2 * (δ * (2 * T + 2)) := by
          have := hsum.trans hmT; linarith
        rw [hδ] at this
        nlinarith

end

end RHTower.LocalCountFalsifier
