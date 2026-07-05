/-
Floor-failure time density: transferring the model small-ball bound to the line.

The Steinhaus small-ball law `block_smallball_condition` bounds the *ensemble* measure
of the floor-failure event `{‖w + ∑ aₙ Xₙ‖ ≤ t₀}`. This module carries that bound to the
*deterministic* vertical line via Kronecker–Weyl equidistribution, controlling the Cesàro
upper time density of the analogous failure event `{τ : ‖F(τ)‖ ≤ t₀}`.

The L² Bohr transfer (`tendsto_secondMoment_average_steinhaus`) reaches only upper tails —
the second moment cannot see a small-ball lower tail. The indicator transfer here needs the
equidistribution engine instead:

* `cesaroUpperDensity` — `limsup_T (1/T)∫₀ᵀ f`, the upper time density of a real observable.
* `realTrig_time_average_tendsto` / `cesaroUpperDensity_realTrig` — for a real function whose
  complexification is a finite phase polynomial, the Cesàro average converges to the real
  part of the zero-frequency coefficient sum (its mean). This is `trig_time_average` pushed
  through `Complex.ofReal`.
* `cesaroUpperDensity_mono` — a nonnegative observable dominated by one with convergent
  average has no larger upper density (`limsup` monotonicity over the window integral).
* `cesaroUpperDensity_le_of_realTrigMajorant` — the transfer: any nonnegative observable
  under a real trigonometric majorant has upper density at most the majorant's mean.
* `floorFailure_timeDensity_le` — the composite. With a real trigonometric majorant of the
  line failure indicator whose mean approximates the model floor-failure measure to within
  `δ`, the upper time density is at most the four-phase small-ball constant plus `δ`. The
  model measure is discharged by `block_smallball_condition`; equidistribution moves it to
  the line.
-/
import GaloisForLFunctions.RHTower.WeylEquidistribution
import GaloisForLFunctions.RHTower.RouteBBlockStep
import GaloisForLFunctions.RHTower.BohrTransfer

open MeasureTheory intervalIntegral Filter Topology Complex
open scoped Classical

namespace RHTower.Weyl

/-- The Cesàro upper time density of a real observable along the vertical flow. -/
noncomputable def cesaroUpperDensity (f : ℝ → ℝ) : ℝ :=
  Filter.limsup (fun T : ℝ => T⁻¹ * ∫ τ in (0:ℝ)..T, f τ) atTop

/-- **Weyl density identity (tendsto form).** For a real function whose complexification is
a finite phase polynomial, the Cesàro time average converges to the real part of the mean —
the zero-frequency coefficient sum. Obtained from `trig_time_average` by pushing the average
through `Complex.ofReal` and taking real parts. -/
theorem realTrig_time_average_tendsto {ι : Type*} (s : Finset ι) (θ : ι → ℝ) (c : ι → ℂ)
    (g : ℝ → ℝ) (hG : ∀ τ : ℝ, (g τ : ℂ) = ∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑τ)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ τ in (0:ℝ)..T, g τ) atTop
      (𝓝 ((∑ i ∈ s.filter (fun i => θ i = 0), c i).re)) := by
  have hW := trig_time_average s θ c
  have hint : ∀ T : ℝ,
      ∫ τ in (0:ℝ)..T, ∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑τ)
        = ((∫ τ in (0:ℝ)..T, g τ : ℝ) : ℂ) := by
    intro T
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro τ _
    exact (hG τ).symm
  have hcast : ∀ T : ℝ,
      (↑T)⁻¹ * ∫ τ in (0:ℝ)..T, ∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑τ)
        = (((T⁻¹ * ∫ τ in (0:ℝ)..T, g τ : ℝ)) : ℂ) := by
    intro T
    rw [hint T]; push_cast; ring
  simp_rw [hcast] at hW
  have := (Complex.continuous_re.tendsto _).comp hW
  simpa only [Function.comp_def, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.ofReal_re] using this

/-- The Cesàro upper density of a real trigonometric observable equals the real part of its
mean. -/
theorem cesaroUpperDensity_realTrig {ι : Type*} (s : Finset ι) (θ : ι → ℝ) (c : ι → ℂ)
    (g : ℝ → ℝ) (hG : ∀ τ : ℝ, (g τ : ℂ) = ∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑τ)) :
    cesaroUpperDensity g = (∑ i ∈ s.filter (fun i => θ i = 0), c i).re :=
  (realTrig_time_average_tendsto s θ c g hG).limsup_eq

/-- Monotonicity of the Cesàro upper density: a nonnegative observable dominated by one whose
window average converges has no larger upper density. -/
theorem cesaroUpperDensity_mono (f g : ℝ → ℝ)
    (hf0 : ∀ τ, 0 ≤ f τ) (hfg : f ≤ g)
    (hf : ∀ T : ℝ, IntervalIntegrable f volume 0 T)
    (hg : ∀ T : ℝ, IntervalIntegrable g volume 0 T)
    {L : ℝ}
    (hgconv : Tendsto (fun T : ℝ => T⁻¹ * ∫ τ in (0:ℝ)..T, g τ) atTop (𝓝 L)) :
    cesaroUpperDensity f ≤ cesaroUpperDensity g := by
  refine Filter.limsup_le_limsup ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hint : (∫ τ in (0:ℝ)..T, f τ) ≤ ∫ τ in (0:ℝ)..T, g τ :=
      intervalIntegral.integral_mono (le_of_lt hT) (hf T) (hg T) hfg
    exact mul_le_mul_of_nonneg_left hint (le_of_lt (inv_pos.mpr hT))
  · refine IsCoboundedUnder.of_frequently_ge (a := 0) (Eventually.frequently ?_)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hnn : (0:ℝ) ≤ ∫ τ in (0:ℝ)..T, f τ :=
      intervalIntegral.integral_nonneg (le_of_lt hT) (fun x _ => hf0 x)
    exact mul_nonneg (le_of_lt (inv_pos.mpr hT)) hnn
  · exact hgconv.isBoundedUnder_le

/-- **Density transfer.** A nonnegative observable dominated by a real trigonometric
polynomial has Cesàro upper density at most the polynomial's mean. Equidistribution of the
majorant fixes the mean; monotonicity of the upper density does the rest. -/
theorem cesaroUpperDensity_le_of_realTrigMajorant {ι : Type*}
    (s : Finset ι) (θ : ι → ℝ) (c : ι → ℂ) (g : ℝ → ℝ)
    (hG : ∀ τ : ℝ, (g τ : ℂ) = ∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑τ))
    (f : ℝ → ℝ) (hf0 : ∀ τ, 0 ≤ f τ) (hfg : f ≤ g)
    (hf : ∀ T : ℝ, IntervalIntegrable f volume 0 T) :
    cesaroUpperDensity f ≤ (∑ i ∈ s.filter (fun i => θ i = 0), c i).re := by
  have hgeq : g = fun τ : ℝ => (∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑τ)).re := by
    funext τ; rw [← hG τ]; exact (Complex.ofReal_re (g τ)).symm
  have hgcont : Continuous g := by rw [hgeq]; fun_prop
  have hg_int : ∀ T : ℝ, IntervalIntegrable g volume 0 T :=
    fun T => hgcont.intervalIntegrable 0 T
  have hgt := realTrig_time_average_tendsto s θ c g hG
  calc cesaroUpperDensity f
      ≤ cesaroUpperDensity g := cesaroUpperDensity_mono f g hf0 hfg hf hg_int hgt
    _ = (∑ i ∈ s.filter (fun i => θ i = 0), c i).re := cesaroUpperDensity_realTrig s θ c g hG

open RHTower in
/-- Continuity of the Dirichlet polynomial in the vertical variable. -/
theorem continuous_dpoly (a : ℕ → ℝ) (s : Finset ℕ) :
    Continuous (fun τ : ℝ => dpoly a s τ) := by
  unfold dpoly cterm
  apply continuous_finsetSum
  intro n _
  fun_prop

open RHTower in
/-- **Unconditional second-moment floor-failure density bound (degree-one majorant).**
Any `[0,1]`-observable supported on the vertical floor-failure set `{‖F‖ ≤ t₀}` has Cesàro
upper time density at most `(B² − ∑ aₙ²)/(B² − t₀²)`, where `B` bounds the carrier. The
degree-one majorant `g = (B² − ‖F‖²)/(B² − t₀²)` dominates the indicator (`g ≥ 1` on the
failure set, `g ≥ 0` off it); its time mean is fixed by the second-moment Bohr transfer
`tendsto_secondMoment_average`. This is the base rung of the polynomial-majorant tower: a
degree-`d` majorant refines the second moment to the full small-ball law. -/
theorem cesaroUpperDensity_secondMoment_le
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (a : ℕ → ℝ) (t₀ B : ℝ)
    (hB0 : 0 ≤ t₀) (htB : t₀ < B)
    (hBbound : ∀ τ : ℝ, ‖dpoly a s τ‖ ≤ B)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a s τ‖ → fail τ = 0)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T) :
    cesaroUpperDensity fail ≤ (B ^ 2 - ∑ n ∈ s, (a n) ^ 2) / (B ^ 2 - t₀ ^ 2) := by
  have hden : 0 < B ^ 2 - t₀ ^ 2 := by nlinarith
  set D := B ^ 2 - t₀ ^ 2 with hDdef
  have hDne : D ≠ 0 := ne_of_gt hden
  set g : ℝ → ℝ := fun τ => (B ^ 2 - ‖dpoly a s τ‖ ^ 2) / D with hgdef
  have hdcont : Continuous (fun τ : ℝ => ‖dpoly a s τ‖ ^ 2) := by
    have := continuous_dpoly a s
    fun_prop
  have hg_int : ∀ T : ℝ, IntervalIntegrable g volume 0 T := by
    intro T
    have : Continuous g := by rw [hgdef]; fun_prop
    exact this.intervalIntegrable 0 T
  have hsm : Tendsto (fun T : ℝ => (∫ t in (0:ℝ)..T, ‖dpoly a s t‖ ^ 2) / T) atTop
      (𝓝 (∑ n ∈ s, (a n) ^ 2)) := by
    have := tendsto_secondMoment_average a s 0 hs
    simpa only [zero_add] using this
  have hgavg : ∀ᶠ T : ℝ in atTop,
      T⁻¹ * ∫ τ in (0:ℝ)..T, g τ
        = D⁻¹ * (B ^ 2 - (∫ t in (0:ℝ)..T, ‖dpoly a s t‖ ^ 2) / T) := by
    filter_upwards [eventually_ne_atTop (0:ℝ)] with T hT
    have hint2 : IntervalIntegrable (fun τ : ℝ => ‖dpoly a s τ‖ ^ 2) volume 0 T :=
      hdcont.intervalIntegrable 0 T
    rw [hgdef]
    dsimp only
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_const) hint2,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    field_simp
  have hgconv : Tendsto (fun T : ℝ => T⁻¹ * ∫ τ in (0:ℝ)..T, g τ) atTop
      (𝓝 (D⁻¹ * (B ^ 2 - ∑ n ∈ s, (a n) ^ 2))) := by
    have hcore : Tendsto
        (fun T : ℝ => D⁻¹ * (B ^ 2 - (∫ t in (0:ℝ)..T, ‖dpoly a s t‖ ^ 2) / T)) atTop
        (𝓝 (D⁻¹ * (B ^ 2 - ∑ n ∈ s, (a n) ^ 2))) :=
      (hsm.const_sub (B ^ 2)).const_mul D⁻¹
    refine hcore.congr' ?_
    filter_upwards [hgavg] with T hTeq
    exact hTeq.symm
  have hgdens : cesaroUpperDensity g = D⁻¹ * (B ^ 2 - ∑ n ∈ s, (a n) ^ 2) :=
    hgconv.limsup_eq
  have hfg : fail ≤ g := by
    intro τ
    rw [hgdef]
    dsimp only
    by_cases hc : ‖dpoly a s τ‖ ≤ t₀
    · have hsq : ‖dpoly a s τ‖ ^ 2 ≤ t₀ ^ 2 := by nlinarith [norm_nonneg (dpoly a s τ)]
      have hge1 : (1 : ℝ) ≤ (B ^ 2 - ‖dpoly a s τ‖ ^ 2) / D := by
        rw [le_div_iff₀ hden, hDdef]; nlinarith
      exact le_trans (hfle1 τ) hge1
    · have hc' : t₀ < ‖dpoly a s τ‖ := not_le.mp hc
      rw [hfsupp τ hc']
      have hsqB : ‖dpoly a s τ‖ ^ 2 ≤ B ^ 2 := by
        nlinarith [norm_nonneg (dpoly a s τ), hBbound τ]
      apply div_nonneg _ (le_of_lt hden)
      linarith
  calc cesaroUpperDensity fail
      ≤ cesaroUpperDensity g :=
        cesaroUpperDensity_mono fail g hfail0 hfg hfail_int hg_int hgconv
    _ = D⁻¹ * (B ^ 2 - ∑ n ∈ s, (a n) ^ 2) := hgdens
    _ = (B ^ 2 - ∑ n ∈ s, (a n) ^ 2) / (B ^ 2 - t₀ ^ 2) := by
        rw [hDdef]; ring

end RHTower.Weyl

namespace RHTower.SteinhausModel

open RHTower.Weyl MeasureTheory Filter Topology

/-- **Floor-failure time density from the model small-ball law.** The Cesàro upper time
density of any nonnegative observable `fail` on the vertical line, dominated by a real
trigonometric majorant `g` whose mean approximates the model floor-failure measure to within
`δ`, is at most the four-phase small-ball constant `(2π)⁻⁴·M` plus `δ`. The ensemble measure
of the floor-failure event is discharged by `block_smallball_condition`; equidistribution of
the majorant transfers it to the deterministic line. -/
theorem floorFailure_timeDensity_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℝ) (w : ℂ) (t₀ : ℝ)
    (p1 p2 p3 p4 : ℕ) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (hp3 : p3 ∈ s) (hp4 : p4 ∈ s)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4) (M : ENNReal) (hMtop : M ≠ ⊤)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θC in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θB in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θA in Set.Icc (0:ℝ) (2*Real.pi),
          {θ' : ℝ | ‖V + (a p1:ℂ) * Complex.exp ((θD:ℂ)*Complex.I)
              + (a p2:ℂ) * Complex.exp ((θC:ℂ)*Complex.I)
              + (a p3:ℂ) * Complex.exp ((θB:ℂ)*Complex.I)
              + (a p4:ℂ) * Complex.exp ((θ':ℂ)*Complex.I)‖ ≤ t₀}.indicator
            (fun _ => (1:ENNReal)) θA) ≤ M)
    {ι : Type*} (idx : Finset ι) (θ : ι → ℝ) (c : ι → ℂ) (g : ℝ → ℝ)
    (hG : ∀ τ : ℝ, (g τ : ℂ) = ∑ i ∈ idx, c i * Complex.exp (θ i * Complex.I * ↑τ))
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfg : fail ≤ g)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T) (δ : ℝ)
    (hmq : (∑ i ∈ idx.filter (fun i => θ i = 0), c i).re
        ≤ (steinhausMeasure {ω : Omega | ‖w + ∑ n ∈ s, (a n:ℂ) * X n ω‖ ≤ t₀}).toReal + δ) :
    cesaroUpperDensity fail ≤ (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M).toReal + δ := by
  have hdens : cesaroUpperDensity fail
      ≤ (∑ i ∈ idx.filter (fun i => θ i = 0), c i).re :=
    cesaroUpperDensity_le_of_realTrigMajorant idx θ c g hG fail hfail0 hfg hfail_int
  have hmodel := block_smallball_condition s hs a w t₀ p1 p2 p3 p4 hp1 hp2 hp3 hp4
    h12 h13 h14 h23 h24 h34 M hM
  have hfin : steinhausMeasure {ω : Omega | ‖w + ∑ n ∈ s, (a n:ℂ) * X n ω‖ ≤ t₀} ≠ ⊤ :=
    measure_ne_top _ _
  have hRHStop : ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hMtop
  have htoReal : (steinhausMeasure {ω : Omega | ‖w + ∑ n ∈ s, (a n:ℂ) * X n ω‖ ≤ t₀}).toReal
      ≤ (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M).toReal :=
    (ENNReal.toReal_le_toReal hfin hRHStop).mpr hmodel
  linarith [hdens, hmq, htoReal]

end RHTower.SteinhausModel
