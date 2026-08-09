import Mathlib

/-!
# Exact contraction of the dyadic Haar coboundary

The positive-ray representative of the fixed Burnol sub-window atom is

`f₀(t) = ({t} - {2t}) / t`.

The causal dyadic Euler inverse `T₂ f(t) = ∑_{n ≥ 1} 2^{-n} f(t/2ⁿ)` contracts it to the single
fractional-part source:

`T₂ f₀(t) = -{t}/t`.

Each dyadic term is the increment of `{t/2ⁿ}/t`, so the series telescopes; the tail is exactly a
geometric series because `{t/2ⁿ} = t/2ⁿ` once `2ⁿ` exceeds `t`.  The same remainder controls the
`L²` statement: the squared remainder integrates to at most `2·2^{-N}` over the positive ray, so
the dyadic partial sums converge to `-{t}/t` in `L²(0,∞)` as well.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-- The positive-ray Haar coboundary source `f₀(t) = ({t} - {2t})/t`. -/
def burnolHaarCoboundarySource (t : ℝ) : ℝ := (Int.fract t - Int.fract (2 * t)) / t

/-- The dyadic partial-sum remainder `{t/2^N}/t`. -/
def burnolDyadicRemainder (N : ℕ) (t : ℝ) : ℝ := Int.fract (t / 2 ^ N) / t

@[simp] theorem burnolDyadicRemainder_zero (t : ℝ) :
    burnolDyadicRemainder 0 t = Int.fract t / t := by
  rw [burnolDyadicRemainder, pow_zero, div_one]

/-- Each dyadic term is one increment of the remainder. -/
theorem burnolDyadicTerm_eq {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) * burnolHaarCoboundarySource (t / 2 ^ (n + 1)) =
      burnolDyadicRemainder (n + 1) t - burnolDyadicRemainder n t := by
  have hpow : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hinv : (1 / 2 : ℝ) ^ (n + 1) * 2 ^ (n + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have h2 : (2 : ℝ) * (t / 2 ^ (n + 1)) = t / 2 ^ n := by
    field_simp
    ring
  rw [burnolHaarCoboundarySource, h2, burnolDyadicRemainder, burnolDyadicRemainder]
  set F1 : ℝ := Int.fract (t / 2 ^ (n + 1)) with hF1
  set F2 : ℝ := Int.fract (t / 2 ^ n) with hF2
  rw [div_div_eq_mul_div, div_sub_div_same,
    show (1 / 2 : ℝ) ^ (n + 1) * ((F1 - F2) * 2 ^ (n + 1) / t) =
      ((1 / 2 : ℝ) ^ (n + 1) * 2 ^ (n + 1)) * ((F1 - F2) / t) by ring, hinv, one_mul]

/-- Beyond the dyadic scale of `t` the remainder is exactly geometric. -/
theorem burnolDyadicRemainder_of_lt {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : t < 2 ^ n) :
    burnolDyadicRemainder n t = (1 / 2 : ℝ) ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hfr : Int.fract (t / 2 ^ n) = t / 2 ^ n := by
    refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
    rw [div_lt_one hpow]
    exact hn
  rw [burnolDyadicRemainder, hfr]
  field_simp
  rw [← mul_pow]
  norm_num

/-- **Exact dyadic coboundary contraction.**  The causal dyadic ladder contracts the two-scale Haar
coboundary to the single fractional-part source. -/
theorem hasSum_burnolDyadicContraction {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) *
        burnolHaarCoboundarySource (t / 2 ^ (n + 1))) (-(Int.fract t) / t) := by
  set f : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 1) *
    burnolHaarCoboundarySource (t / 2 ^ (n + 1)) with hf
  obtain ⟨N, hN⟩ : ∃ N : ℕ, t < 2 ^ N := by
    refine ⟨⌈t⌉₊, ?_⟩
    have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2 : (⌈t⌉₊ : ℝ) < 2 ^ (⌈t⌉₊ : ℕ) := by
      exact_mod_cast Nat.lt_two_pow_self
    linarith
  have hmono : ∀ n : ℕ, N ≤ n → t < 2 ^ n := by
    intro n hn
    have : (2 : ℝ) ^ N ≤ 2 ^ n := by
      exact pow_le_pow_right₀ (by norm_num) hn
    linarith
  have htail : ∀ n : ℕ, f (n + N) = -((1 / 2 : ℝ) ^ (n + N + 1)) := by
    intro n
    rw [hf]
    simp only
    rw [burnolDyadicTerm_eq ht (n + N),
      burnolDyadicRemainder_of_lt ht (hmono (n + N + 1) (by omega)),
      burnolDyadicRemainder_of_lt ht (hmono (n + N) (by omega))]
    ring
  have hgeom : HasSum (fun n : ℕ => -((1 / 2 : ℝ) ^ (n + N + 1))) (-((1 / 2 : ℝ) ^ N)) := by
    have hbase : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) ((1 - 1 / 2 : ℝ)⁻¹) :=
      hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
    have hscaled := hbase.mul_left (-((1 / 2 : ℝ) ^ (N + 1)))
    have hfun : (fun n : ℕ => -((1 / 2 : ℝ) ^ (N + 1)) * (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => -((1 / 2 : ℝ) ^ (n + N + 1)) := by
      funext n
      rw [neg_mul, ← pow_add]
      congr 2
      omega
    have hval : -((1 / 2 : ℝ) ^ (N + 1)) * (1 - 1 / 2 : ℝ)⁻¹ = -((1 / 2 : ℝ) ^ N) := by
      rw [pow_succ]
      norm_num
      ring
    rw [← hfun, ← hval]
    exact hscaled
  have h1 : HasSum (fun n : ℕ => f (n + N)) (-((1 / 2 : ℝ) ^ N)) := by
    simpa only [htail] using hgeom
  have h2 := (hasSum_nat_add_iff (f := f) N).mp h1
  have hsum : ∑ i ∈ Finset.range N, f i =
      burnolDyadicRemainder N t - burnolDyadicRemainder 0 t := by
    rw [Finset.sum_congr rfl (fun i _ => burnolDyadicTerm_eq ht i)]
    exact Finset.sum_range_sub (fun i => burnolDyadicRemainder i t) N
  rw [hsum, burnolDyadicRemainder_of_lt ht hN, burnolDyadicRemainder_zero,
    show -((1 / 2 : ℝ) ^ N) + ((1 / 2 : ℝ) ^ N - Int.fract t / t) = -(Int.fract t) / t by ring] at h2
  exact h2

/-! ## The `L²` statement -/

theorem burnolFract_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Int.fract x ≤ x := by
  have hfl : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have hcast : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hfl
  have hfr : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
  rw [hfr]
  linarith

/-- **The dyadic remainder has square integral at most `2·2^{-N}` on the positive ray.** -/
theorem lintegral_burnolDyadicRemainder_sq_le (N : ℕ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (burnolDyadicRemainder N t ^ 2) ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) := by
  have hc : (0 : ℝ) < 2 ^ N := by positivity
  have hdisj : Disjoint (Ioc (0 : ℝ) (2 ^ N)) (Ioi ((2 : ℝ) ^ N)) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx' (not_lt.mpr hx.2)
  -- the near piece
  have hnear : ∫⁻ t in Ioc (0 : ℝ) (2 ^ N),
      ENNReal.ofReal (burnolDyadicRemainder N t ^ 2) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
    have hb : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (2 ^ N))),
        ENNReal.ofReal (burnolDyadicRemainder N t ^ 2) ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ N) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      refine ENNReal.ofReal_le_ofReal ?_
      have htpos : (0 : ℝ) < t := ht.1
      have hfr0 : 0 ≤ Int.fract (t / 2 ^ N) := Int.fract_nonneg _
      have hfrle : Int.fract (t / 2 ^ N) ≤ t / 2 ^ N :=
        burnolFract_le_self_of_nonneg (by positivity)
      have hstep : burnolDyadicRemainder N t ≤ (1 / 2 : ℝ) ^ N := by
        have h1 : Int.fract (t / 2 ^ N) * 2 ^ N ≤ t := by
          have h := mul_le_mul_of_nonneg_right hfrle hc.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at h
        rw [burnolDyadicRemainder, div_pow, one_pow,
          div_le_div_iff₀ htpos (by positivity : (0 : ℝ) < 2 ^ N)]
        linarith
      have hnn : 0 ≤ burnolDyadicRemainder N t := by
        rw [burnolDyadicRemainder]
        positivity
      have hsq : burnolDyadicRemainder N t ^ 2 ≤ ((1 / 2 : ℝ) ^ N) ^ 2 :=
        pow_le_pow_left₀ hnn hstep 2
      calc burnolDyadicRemainder N t ^ 2 ≤ ((1 / 2 : ℝ) ^ N) ^ 2 := hsq
        _ = (1 / 4 : ℝ) ^ N := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    refine (lintegral_mono_ae hb).trans ?_
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_pow]
    norm_num
  -- the far piece
  have hfar : ∫⁻ t in Ioi ((2 : ℝ) ^ N),
      ENNReal.ofReal (burnolDyadicRemainder N t ^ 2) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
    have hint : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi ((2 : ℝ) ^ N)) volume :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hc
    have hval : ∫ t in Ioi ((2 : ℝ) ^ N), t ^ (-2 : ℝ) = ((2 : ℝ) ^ N)⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hc,
        show (-2 : ℝ) + 1 = -((1 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc.le,
        Real.rpow_natCast, pow_one]
      field_simp
      norm_num
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi ((2 : ℝ) ^ N))] fun t : ℝ => t ^ (-2 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (le_of_lt (lt_trans hc ht)) _
    have hlint : ∫⁻ t in Ioi ((2 : ℝ) ^ N), ENNReal.ofReal (t ^ (-2 : ℝ)) =
        ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) := by
      rw [← hval, ofReal_integral_eq_lintegral_ofReal hint hnn]
    have hb : ∀ᵐ t ∂(volume.restrict (Ioi ((2 : ℝ) ^ N))),
        ENNReal.ofReal (burnolDyadicRemainder N t ^ 2) ≤ ENNReal.ofReal (t ^ (-2 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      refine ENNReal.ofReal_le_ofReal ?_
      have htpos : (0 : ℝ) < t := lt_trans hc ht
      have hrp : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg htpos.le,
          Real.rpow_natCast]
      rw [hrp, burnolDyadicRemainder, div_pow]
      have hfr1 : Int.fract (t / 2 ^ N) < 1 := Int.fract_lt_one _
      have hfr0 : 0 ≤ Int.fract (t / 2 ^ N) := Int.fract_nonneg _
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : Int.fract (t / 2 ^ N) ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg t)]
    refine (lintegral_mono_ae hb).trans ?_
    rw [hlint]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_pow, one_pow]
    exact le_of_eq (by rw [one_div])
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (burnolDyadicRemainder N t ^ 2)
      = ∫⁻ t in (Ioc (0 : ℝ) (2 ^ N) ∪ Ioi ((2 : ℝ) ^ N)),
          ENNReal.ofReal (burnolDyadicRemainder N t ^ 2) := by
        rw [Set.Ioc_union_Ioi_eq_Ioi hc.le]
    _ = (∫⁻ t in Ioc (0 : ℝ) (2 ^ N), ENNReal.ofReal (burnolDyadicRemainder N t ^ 2)) +
          ∫⁻ t in Ioi ((2 : ℝ) ^ N), ENNReal.ofReal (burnolDyadicRemainder N t ^ 2) :=
        lintegral_union measurableSet_Ioi hdisj
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ N) + ENNReal.ofReal ((1 / 2 : ℝ) ^ N) :=
        add_le_add hnear hfar
    _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- The dyadic partial-sum error is exactly the remainder. -/
theorem burnolDyadicPartialSum_sub {t : ℝ} (ht : 0 < t) (M : ℕ) :
    (∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ (n + 1) *
        burnolHaarCoboundarySource (t / 2 ^ (n + 1))) - (-(Int.fract t) / t) =
      burnolDyadicRemainder M t := by
  rw [Finset.sum_congr rfl (fun i _ => burnolDyadicTerm_eq ht i),
    Finset.sum_range_sub (fun i => burnolDyadicRemainder i t) M, burnolDyadicRemainder_zero]
  ring

/-- **`L²` convergence of the dyadic contraction on the positive ray.** -/
theorem tendsto_lintegral_burnolDyadicPartialSum_error :
    Tendsto (fun M : ℕ => ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (((∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ (n + 1) *
          burnolHaarCoboundarySource (t / 2 ^ (n + 1))) - (-(Int.fract t) / t)) ^ 2))
      atTop (𝓝 0) := by
  have hrewrite : ∀ M : ℕ,
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (((∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ (n + 1) *
          burnolHaarCoboundarySource (t / 2 ^ (n + 1))) - (-(Int.fract t) / t)) ^ 2)) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (burnolDyadicRemainder M t ^ 2) := by
    intro M
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [burnolDyadicPartialSum_sub ht M]
  have hbound : Tendsto (fun M : ℕ => ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ M)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun M : ℕ => (1 / 2 : ℝ) ^ M) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hreal : Tendsto (fun M : ℕ => 2 * (1 / 2 : ℝ) ^ M) atTop (𝓝 (2 * 0)) :=
      hpow.const_mul 2
    rw [mul_zero] at hreal
    have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    rw [ENNReal.ofReal_zero] at hcomp
    exact hcomp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun M => bot_le) (fun M => ?_)
  rw [hrewrite M]
  exact lintegral_burnolDyadicRemainder_sq_le M

end RHTower
