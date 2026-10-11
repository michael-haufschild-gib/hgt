import GaloisForLFunctions.RHTower.WeilLinearTwistQuantization

/-!
# Linear lock phases on sparse windows are quantized

Let `G` be a Herglotz producer for the weights `lam`.  Suppose that the lower-line lock is linear
only on a sequence of windows,

`G(1 − s) = κ_j e^{iη(−τ)} G(s)`,  `s = ½ + 2iτ`,  `−Y_j ≤ τ ≤ −X_j`,

with `X_j → ∞`, windows of super-polynomial length (`Y_j ≥ (1 + X_j)^p` eventually, for every
`p`), and bounded constants `κ_j`.  Outside the windows the lock is arbitrary.

**Theorem** (`windowed_linear_lock_quantization`).  Then `e^{−η/2}` is a natural number; in
particular `η ≤ 0` (`windowed_linear_lock_slope_nonpos`).  The same holds when the window lock
carries the monotone sublinear twist of `linear_twist_quantization_profile`,
`G(1 − s) = κ_j e^{iη(−τ)} Ψ(C(−τ)) G(s)` (`windowed_linear_lock_quantization_profile`); a global
lock is the case of any windows, so this contains `linear_twist_quantization_profile`.

The global linear lock of `linear_twist_quantization` is the case of one window `[1, ∞)`.  Here the
lock phase may have any behaviour between the windows, so the non-integer spectral mass of the
producer need not have a density.

**Proof.**  Assume `e^{−η/2} ∉ ℕ`.
* Along every `ε → 0⁺`, the reflected radial integral `R(ε) = ε ∫_{t<0} φ*(t) k(2t, ε + i) dt`
  tends to `2β ≠ 0` (`tendsto_lower_reflected_radial`), and the fully twisted integral
  `L(ε) = ε ∫_{t<0} φ_η(t) k(2t, ε + i) dt` tends to `0` (`tendsto_twisted_far_nonres_profile`).
* On the `j`-th window `φ* = κ_j φ_η`.  Off the window both are `O((1 + |t|)^N)` and
  `‖k(2t, ε + i)‖ ≤ 3e^{−ε|t|}`.  With `ε_j = (1 + X_j)^{−(N+2)}` the part `−X_j < t < 0` costs
  `O(1/(1 + X_j))`, and the part `t < −Y_j` costs `O((1 + X_j)^{N(N+2)} e^{−(1+X_j)/2})`.
* So `R(ε_j) − κ_j L(ε_j) → 0` and `R(ε_j) → 0`, a contradiction.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- The kernel at `ε + i`: `‖k(2t, ε + i)‖ ≤ 3e^{−ε|t|}` for `0 < ε ≤ 1`. -/
theorem norm_pairKernel_eps_one_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    ‖pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)‖ ≤ 3 * Real.exp (-(ε * |t|)) := by
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  have hre : τ.re = ε := by simp [hτ]
  have him : τ.im = 1 := by simp [hτ]
  have hτre : 0 < τ.re := by rw [hre]; exact hε
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    rw [him, abs_one] at h; exact h
  have hτ2 : ‖τ‖ ≤ 2 := by
    have h := norm_add_le (ε : ℂ) (((1 : ℕ) : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Nat.cast_one, norm_one,
      Real.norm_eq_abs, abs_of_pos hε] at h
    have e : τ = (ε : ℂ) + 1 * I := by rw [hτ, Nat.cast_one]
    rw [e]; linarith
  have hτ0 : 0 < ‖τ‖ := by linarith
  refine (norm_pairKernel_two_mul_le t hτre).trans ?_
  have h1 : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
  have h2 : Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|)) ≤ Real.exp (-(ε * |t|)) := by
    apply Real.exp_le_exp.mpr
    rw [hre]
    have hq : ε ≤ 2 * (ε / ‖τ‖) := by
      rw [mul_div_assoc', le_div_iff₀ hτ0]; nlinarith
    nlinarith [abs_nonneg t]
  have h0 : 0 ≤ ‖τ‖ ^ (-(1 / 2 : ℝ)) := by positivity
  calc 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|))
      ≤ 3 * 1 * Real.exp (-(ε * |t|)) := by gcongr
    _ = 3 * Real.exp (-(ε * |t|)) := by ring

/-- `(1 + x)^N e^{−εx} ≤ (2(N+1)/ε)^N e^{−εx/2}` for `x ≥ 0`, `0 < ε ≤ 1`. -/
theorem pow_mul_exp_le_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ N * Real.exp (-(ε * x)) ≤
      (2 * ((N : ℝ) + 1) / ε) ^ N * Real.exp (-(ε * x / 2)) := by
  set c : ℝ := 2 * ((N : ℝ) + 1) with hc
  have hc2 : 2 ≤ c := by rw [hc]; have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  have hc0 : 0 < c := by linarith
  have hcε : 1 ≤ c / ε := by rw [le_div_iff₀ hε]; linarith
  have hlin : 1 + x ≤ c / ε * Real.exp (ε * x / c) := by
    have he := Real.add_one_le_exp (ε * x / c)
    have hx' : c / ε * (ε * x / c + 1) = x + c / ε := by field_simp
    calc 1 + x ≤ x + c / ε := by linarith
      _ = c / ε * (ε * x / c + 1) := hx'.symm
      _ ≤ c / ε * Real.exp (ε * x / c) := by gcongr
  have hpow : (1 + x) ^ N ≤ (c / ε) ^ N * Real.exp (N * (ε * x / c)) := by
    rw [Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hlin N
  have hexp : Real.exp (N * (ε * x / c)) * Real.exp (-(ε * x)) ≤ Real.exp (-(ε * x / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hNc : (N : ℝ) / c ≤ 1 / 2 := by
      rw [div_le_iff₀ hc0, hc]; linarith
    have hεx : 0 ≤ ε * x := by positivity
    have : (N : ℝ) * (ε * x / c) = (N / c) * (ε * x) := by ring
    rw [this]; nlinarith
  calc (1 + x) ^ N * Real.exp (-(ε * x))
      ≤ (c / ε) ^ N * Real.exp (N * (ε * x / c)) * Real.exp (-(ε * x)) := by gcongr
    _ = (c / ε) ^ N * (Real.exp (N * (ε * x / c)) * Real.exp (-(ε * x))) := by ring
    _ ≤ (c / ε) ^ N * Real.exp (-(ε * x / 2)) := by gcongr


/-- Pointwise size of the window defect: `‖φ*(t)k − κ w(t)φ_η(t)k‖ ≤ M (1+|t|)^N e^{−ε|t|}`. -/
theorem norm_window_defect_le {G : ℂ → ℂ} {η K₀ CB Mw : ℝ} {N : ℕ} {κ : ℂ} {w : ℝ → ℂ}
    (hκ : ‖κ‖ ≤ K₀) (hw : ∀ t, ‖w t‖ ≤ Mw) (hCB : 0 ≤ CB)
    (hpoly : ∀ τ : ℝ, ‖phiG G τ‖ ≤ CB * (1 + |τ|) ^ N ∧ ‖gG G τ‖ ≤ CB * (1 + |τ|) ^ N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    ‖phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) -
        κ * (w t * (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)))‖ ≤
      3 * ((2 + K₀ * Mw) * CB) * ((1 + |t|) ^ N * Real.exp (-(ε * |t|))) := by
  have hK₀ : 0 ≤ K₀ := (norm_nonneg _).trans hκ
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hw 0)
  set k := pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)
  have hk := norm_pairKernel_eps_one_le hε hε1 t
  have hP : (0 : ℝ) ≤ (1 + |t|) ^ N := by positivity
  have hstar : ‖phiStar G t‖ ≤ 2 * CB * (1 + |t|) ^ N := by
    rw [← phiG_sub_gG]
    refine (norm_sub_le _ _).trans ?_
    linarith [(hpoly t).1, (hpoly t).2]
  have htw : ‖phiG (twistG η G) t‖ ≤ CB * (1 + |t|) ^ N := by
    rw [norm_phiG_twistG]; exact (hpoly t).1
  have hk0 : 0 ≤ ‖k‖ := norm_nonneg _
  calc ‖phiStar G t * k - κ * (w t * (phiG (twistG η G) t * k))‖
      ≤ ‖phiStar G t‖ * ‖k‖ + ‖κ‖ * (‖w t‖ * (‖phiG (twistG η G) t‖ * ‖k‖)) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
    _ ≤ (2 * CB * (1 + |t|) ^ N) * (3 * Real.exp (-(ε * |t|))) +
          K₀ * (Mw * ((CB * (1 + |t|) ^ N) * (3 * Real.exp (-(ε * |t|))))) := by
        gcongr; exact hw t
    _ = 3 * ((2 + K₀ * Mw) * CB) * ((1 + |t|) ^ N * Real.exp (-(ε * |t|))) := by ring

/-- **The window estimate.**  If the lock is `κ e^{iη(−τ)} w(τ)` on `−Y ≤ τ ≤ −X`, with `‖w‖ ≤ M_w`,
the reflected radial integral and `κ` times the weighted twisted one differ by at most
`M ε X (1 + X)^N + 2M (c/ε)^N e^{−εY/2}`, `M = 3(2 + K₀M_w)C_B`, `c = 2(N + 1)`. -/
theorem norm_reflected_sub_twisted_le {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    {η K₀ CB Mw X Y : ℝ} {N : ℕ} {κ : ℂ} {w : ℝ → ℂ} (hκ : ‖κ‖ ≤ K₀)
    (hwm : AEStronglyMeasurable w volume) (hw : ∀ t, ‖w t‖ ≤ Mw) (hCB : 0 ≤ CB)
    (hpoly : ∀ τ : ℝ, ‖phiG G τ‖ ≤ CB * (1 + |τ|) ^ N ∧ ‖gG G τ‖ ≤ CB * (1 + |τ|) ^ N)
    (hX0 : 0 ≤ X) (hXY : X ≤ Y)
    (hlock : ∀ τ : ℝ, -Y ≤ τ → τ ≤ -X →
      G (1 - lineS τ) = κ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * w τ * G (lineS τ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖(ε : ℂ) * (∫ t in Iio (0 : ℝ),
          phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)) -
        κ * ((ε : ℂ) * ∫ t in Iio (0 : ℝ),
          w t * (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)))‖ ≤
      3 * ((2 + K₀ * Mw) * CB) * (ε * X * (1 + X) ^ N) +
        2 * (3 * ((2 + K₀ * Mw) * CB)) *
          ((2 * ((N : ℝ) + 1) / ε) ^ N * Real.exp (-(ε * Y / 2))) := by
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  set M : ℝ := 3 * ((2 + K₀ * Mw) * CB) with hM
  set c : ℝ := 2 * ((N : ℝ) + 1) with hc
  have hK₀ : 0 ≤ K₀ := (norm_nonneg _).trans hκ
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hw 0)
  have hM0 : 0 ≤ M := by positivity
  have hτre : 0 < τ.re := by simp [hτ]; exact hε
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  set D : ℝ → ℂ := fun t => phiStar G t * pairKernel (2 * t) τ -
    κ * (w t * (phiG (twistG η G) t * pairKernel (2 * t) τ)) with hD
  have hDbound : ∀ t, ‖D t‖ ≤ M * ((1 + |t|) ^ N * Real.exp (-(ε * |t|))) := fun t =>
    norm_window_defect_le hκ hw hCB hpoly hε hε1 t
  -- continuity and integrability
  have hcont_star : Continuous (phiStar G) := by
    have : phiStar G = fun t => phiG G t - gG G t := by funext t; rw [phiG_sub_gG]
    rw [this]; exact (continuous_phiG hGc).sub (continuous_gG hGc)
  have hcont_tw : Continuous (phiG (twistG η G)) :=
    continuous_phiG (fun s hs => continuousAt_twistG hGc η hs)
  have hk_cont := continuous_pairKernel_two_mul hτ0
  have hdom := (integrable_one_add_abs_pow_mul_exp hε N).const_mul (3 * (2 * CB))
  have hint_star : Integrable fun t => phiStar G t * pairKernel (2 * t) τ := by
    refine hdom.mono' (hcont_star.mul hk_cont).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    have h1 : ‖phiStar G t‖ ≤ 2 * CB * (1 + |t|) ^ N := by
      rw [← phiG_sub_gG]
      refine (norm_sub_le _ _).trans ?_
      linarith [(hpoly t).1, (hpoly t).2]
    have h2 := norm_pairKernel_eps_one_le hε hε1 t
    calc ‖phiStar G t‖ * ‖pairKernel (2 * t) τ‖
        ≤ (2 * CB * (1 + |t|) ^ N) * (3 * Real.exp (-(ε * |t|))) := by gcongr
      _ = 3 * (2 * CB) * ((1 + |t|) ^ N * Real.exp (-(ε * |t|))) := by ring
  have hint_tw : Integrable fun t => phiG (twistG η G) t * pairKernel (2 * t) τ := by
    refine ((integrable_one_add_abs_pow_mul_exp hε N).const_mul (3 * CB)).mono'
      (hcont_tw.mul hk_cont).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_phiG_twistG]
    have h2 := norm_pairKernel_eps_one_le hε hε1 t
    calc ‖phiG G t‖ * ‖pairKernel (2 * t) τ‖
        ≤ (CB * (1 + |t|) ^ N) * (3 * Real.exp (-(ε * |t|))) := by
          gcongr; exact (hpoly t).1
      _ = 3 * CB * ((1 + |t|) ^ N * Real.exp (-(ε * |t|))) := by ring
  have hint_w : Integrable fun t => w t * (phiG (twistG η G) t * pairKernel (2 * t) τ) :=
    hint_tw.bdd_mul hwm (c := Mw) (Eventually.of_forall fun t => hw t)
  have hDint : Integrable D := hint_star.sub (hint_w.const_mul κ)
  -- the defect vanishes on the window
  have hwin : ∀ t, -Y ≤ t → t ≤ -X → D t = 0 := by
    intro t h1 h2
    have hs : phiStar G t = κ * (w t * phiG (twistG η G) t) := by
      rw [phiG_twistG, linTwist_lineS]
      simp only [phiStar, phiG]
      rw [hlock t h1 h2]
      ring
    simp only [hD, hs]; ring
  -- the difference is the integral of the defect
  have hdiff : (ε : ℂ) * (∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) -
      κ * ((ε : ℂ) * ∫ t in Iio (0 : ℝ), w t * (phiG (twistG η G) t * pairKernel (2 * t) τ)) =
      (ε : ℂ) * ∫ t in Iio (0 : ℝ), D t := by
    have hI : ∫ t in Iio (0 : ℝ), D t = (∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) -
        ∫ t in Iio (0 : ℝ), κ * (w t * (phiG (twistG η G) t * pairKernel (2 * t) τ)) :=
      integral_sub hint_star.integrableOn (hint_w.const_mul κ).integrableOn
    rw [hI, integral_const_mul]
    ring
  -- split off the window
  have hsplit : ∫ t in Iio (0 : ℝ), D t =
      (∫ t in Iio (-Y), D t) + ∫ t in Ioo (-X) 0, D t := by
    have hpt : ∀ t ∈ Iio (0 : ℝ), D t =
        (Iio (-Y)).indicator D t + (Ioo (-X) 0).indicator D t := by
      intro t ht
      have ht0 : t < 0 := ht
      by_cases h1 : t < -Y
      · have h2 : t ∉ Ioo (-X) 0 := fun h => by linarith [h.1]
        rw [Set.indicator_of_mem (show t ∈ Iio (-Y) from h1), Set.indicator_of_notMem h2,
          add_zero]
      · by_cases h3 : -X < t
        · rw [Set.indicator_of_notMem (show t ∉ Iio (-Y) from h1),
            Set.indicator_of_mem (show t ∈ Ioo (-X) 0 from ⟨h3, ht0⟩), zero_add]
        · rw [Set.indicator_of_notMem (show t ∉ Iio (-Y) from h1),
            Set.indicator_of_notMem (show t ∉ Ioo (-X) 0 from fun h => h3 h.1), add_zero]
          exact hwin t (le_of_not_gt h1) (le_of_not_gt h3)
    rw [setIntegral_congr_fun measurableSet_Iio hpt,
      integral_add ((hDint.indicator measurableSet_Iio).integrableOn)
        ((hDint.indicator measurableSet_Ioo).integrableOn),
      setIntegral_indicator measurableSet_Iio, setIntegral_indicator measurableSet_Ioo]
    have e1 : Iio (0 : ℝ) ∩ Iio (-Y) = Iio (-Y) := by
      ext t; simp only [mem_inter_iff, mem_Iio]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨by linarith, h⟩
    have e2 : Iio (0 : ℝ) ∩ Ioo (-X) 0 = Ioo (-X) 0 := by
      ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioo]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨h.2, h⟩
    rw [e1, e2]
  -- the near piece
  have hnear : ‖∫ t in Ioo (-X) 0, D t‖ ≤ M * (1 + X) ^ N * X := by
    have hvol : volume.real (Ioo (-X) (0 : ℝ)) = X := by
      rw [Real.volume_real_Ioo_of_le (by linarith)]; ring
    have h : ‖∫ t in Ioo (-X) (0 : ℝ), D t‖ ≤ M * (1 + X) ^ N * volume.real (Ioo (-X) (0 : ℝ)) :=
      norm_setIntegral_le_of_norm_le_const measure_Ioo_lt_top (fun t ht => ?_)
    · rwa [hvol] at h
    · have ht1 : |t| ≤ X := by
        rw [abs_of_neg ht.2]; linarith [ht.1]
      refine (hDbound t).trans ?_
      have hp : (1 + |t|) ^ N ≤ (1 + X) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have he : Real.exp (-(ε * |t|)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := abs_nonneg t; nlinarith
      calc M * ((1 + |t|) ^ N * Real.exp (-(ε * |t|))) ≤ M * ((1 + X) ^ N * 1) := by
            gcongr
        _ = M * (1 + X) ^ N := by ring
  -- the far piece
  have hfar : ‖∫ t in Iio (-Y), D t‖ ≤
      M * (c / ε) ^ N * (Real.exp (ε / 2 * -Y) / (ε / 2)) := by
    have hε2 : 0 < ε / 2 := by positivity
    have hgint : IntegrableOn (fun t : ℝ => M * (c / ε) ^ N * Real.exp (ε / 2 * t)) (Iio (-Y)) :=
      ((integrableOn_exp_mul_Iic hε2 (-Y)).mono_set Iio_subset_Iic_self).const_mul _
    have h : ‖∫ t in Iio (-Y), D t‖ ≤ ∫ t in Iio (-Y), M * (c / ε) ^ N * Real.exp (ε / 2 * t) :=
      norm_integral_le_of_norm_le hgint
        ((ae_restrict_iff' measurableSet_Iio).mpr (Eventually.of_forall fun t ht => ?_))
    · refine h.trans (le_of_eq ?_)
      rw [integral_const_mul, ← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic hε2]
    · have ht0 : t < 0 := lt_of_lt_of_le ht (by linarith)
      have habs : |t| = -t := abs_of_neg ht0
      refine (hDbound t).trans ?_
      have hpw := pow_mul_exp_le_half hε hε1 N (abs_nonneg t)
      rw [habs] at hpw ⊢
      have e : Real.exp (-(ε * -t / 2)) = Real.exp (ε / 2 * t) := by congr 1; ring
      rw [e] at hpw
      calc M * ((1 + -t) ^ N * Real.exp (-(ε * -t))) ≤ M * ((c / ε) ^ N * Real.exp (ε / 2 * t)) :=
            mul_le_mul_of_nonneg_left hpw hM0
        _ = M * (c / ε) ^ N * Real.exp (ε / 2 * t) := by ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, hsplit]
  have htri := norm_add_le (∫ t in Iio (-Y), D t) (∫ t in Ioo (-X) 0, D t)
  have hexp : Real.exp (ε / 2 * -Y) = Real.exp (-(ε * Y / 2)) := by congr 1; ring
  calc ε * ‖(∫ t in Iio (-Y), D t) + ∫ t in Ioo (-X) 0, D t‖
      ≤ ε * (M * (c / ε) ^ N * (Real.exp (ε / 2 * -Y) / (ε / 2)) + M * (1 + X) ^ N * X) := by
        gcongr; exact htri.trans (add_le_add hfar hnear)
    _ = M * (ε * X * (1 + X) ^ N) + 2 * M * ((c / ε) ^ N * Real.exp (-(ε * Y / 2))) := by
        rw [hexp]; field_simp; ring


/-- Without resonance at height `1`, the twisted radial integral with a monotone sublinear profile
`Ψ(C(−t))` vanishes in the limit. -/
theorem tendsto_twisted_radial_nonres_profile {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (η : ℝ) (hres : ∀ n : ℕ, (n : ℝ) ≠ Real.exp (-(η / 2)))
    {C : ℝ → ℝ} (hC : Monotone C) {α K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {Ψ ψ : ℝ → ℂ} {L M : ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ) (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0))
    (hΨc : Continuous Ψ) (hΨb : ∀ v, ‖Ψ v‖ ≤ M) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ), Ψ (C (-t)) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hpoly' : ∀ t : ℝ, ‖phiG (twistG η G) t‖ ≤ CB * (1 + |t|) ^ N := fun t => by
    rw [norm_phiG_twistG]; exact (hpoly t).1
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hΨb 0)
  have hfar := tendsto_twisted_far_nonres_profile hsl hΦd hΦre hid hGc hGd hG2 η (m := 1) le_rfl
    (fun n hn => hres n (by rw [hn, Nat.cast_one, one_mul])) hC hα0 hα1 hK hgrowth hL hψm hψL hΨ
  have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, Ψ (C (-t)) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
    refine (tendsto_eps_mul_setIntegral_Ioo (h := fun t => Ψ (C (-t)) * phiG (twistG η G) t)
      (B := M * (CB * 2 ^ N)) (fun t ht => ?_) le_rfl).congr fun ε => ?_
    · rw [norm_mul]
      have hta : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have h3 : (1 + |t|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      exact mul_le_mul (hΨb _) ((hpoly' t).trans (by gcongr)) (norm_nonneg _) hM0
    · simp only [mul_assoc]
  have hsum := hfar.add hnear
  rw [add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have hε' : (0 : ℝ) < ε := hε
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  have hτre : 0 < τ.re := by simp [hτ]; exact hε'
  have hphik := integrable_phiG_twistG_mul_pairKernel hsl hΦre hid hGc hGd hG2 η hτre
  have hΨm : AEStronglyMeasurable (fun t : ℝ => Ψ (C (-t))) volume :=
    (hΨc.measurable.comp (hC.measurable.comp measurable_neg)).aestronglyMeasurable
  have hint := hphik.bdd_mul hΨm (c := M) (Eventually.of_forall fun t => hΨb _)
  have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
    ext t
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro h
      by_cases h1 : t ≤ -1
      · exact Or.inl h1
      · exact Or.inr ⟨by linarith, h⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
    Set.disjoint_left.mpr fun t h1 h2 => by
      simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
  simp only
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioo hint.integrableOn hint.integrableOn]
  ring

/-- The bound `M/(1+x) + 2M c^N (1+x)^{(N+2)N} e^{−(1+x)/2}` tends to `0`. -/
theorem tendsto_window_bound (M c : ℝ) (N : ℕ) :
    Tendsto (fun x : ℝ => M / (1 + x) +
      2 * M * c ^ N * ((1 + x) ^ ((N + 2) * N) * Real.exp (-((1 + x) / 2)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 1 + x) atTop atTop := tendsto_atTop_add_const_left _ 1 tendsto_id
  have hA : Tendsto (fun x : ℝ => M / (1 + x)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop h1
  set K := (N + 2) * N
  have hB : Tendsto (fun x : ℝ => (1 + x) ^ K * Real.exp (-((1 + x) / 2))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => (1 + x) / 2) atTop atTop := h1.atTop_div_const (by norm_num)
    have h3 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp h2).const_mul ((2 : ℝ) ^ K)
    rw [mul_zero] at h3
    refine h3.congr fun x => ?_
    simp only [Function.comp]
    rw [div_pow, ← mul_assoc, mul_div_cancel₀ _ (by positivity)]
  have hC := hB.const_mul (2 * M * c ^ N)
  rw [mul_zero] at hC
  simpa using hA.add hC

/-- **Twisted linear lock phases on sparse windows are quantized.**  Let `G` be a Herglotz producer.
Suppose that on windows `−Y_j ≤ τ ≤ −X_j`, with `X_j → ∞` and `Y_j ≥ (1 + X_j)^p` eventually for
every `p`, `G(1 − s) = κ_j e^{iη(−τ)} Ψ(C(−τ)) G(s)` (`s = ½ + 2iτ`), with `‖κ_j‖ ≤ K₀`, `C`
monotone with `C(x) ≤ K x^α` (`α < 1`), and `Ψ` a bounded profile.  Then `e^{−η/2}` is a natural
number.  Outside the windows the lock is arbitrary. -/
theorem windowed_linear_lock_quantization_profile {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {Ψ ψ : ℝ → ℂ} {L M : ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ) (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0))
    (hΨc : Continuous Ψ) (hΨb : ∀ v, ‖Ψ v‖ ≤ M)
    {η K₀ : ℝ} {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (((η * (-τ) : ℝ) : ℂ) * I) * Ψ (C (-τ)) * G (lineS τ)) :
    ∃ n : ℕ, (n : ℝ) = Real.exp (-(η / 2)) := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  by_contra hres
  push Not at hres
  have hpi := Real.pi_pos
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hidT hGc hGd hG2
  have hK₀ : 0 ≤ K₀ := (norm_nonneg _).trans (hκ 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hΨb 0)
  -- the growth exponent in `(0, 1)`
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  set α' : ℝ := max α (1 / 2) with hα'
  set K' : ℝ := |K| + 1 with hK'
  have hα'0 : 0 < α' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hα'1 : α' < 1 := max_lt hα1 (by norm_num)
  have hC' : ∀ x : ℝ, 1 ≤ x → C x ≤ K' * x ^ α' := by
    intro x hx
    have h1 : x ^ α ≤ x ^ α' := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    have h0 : 0 ≤ x ^ α := Real.rpow_nonneg (by linarith) _
    have h2 := hCK x hx
    have h3 : K * x ^ α ≤ |K| * x ^ α := mul_le_mul_of_nonneg_right (le_abs_self K) h0
    have h4 : |K| * x ^ α ≤ K' * x ^ α' := by
      rw [hK']; nlinarith [abs_nonneg K]
    linarith
  set w : ℝ → ℂ := fun τ => Ψ (C (-τ)) with hw
  have hwm : AEStronglyMeasurable w volume :=
    (hΨc.measurable.comp (hC.measurable.comp measurable_neg)).aestronglyMeasurable
  have hwb : ∀ t, ‖w t‖ ≤ M := fun t => hΨb _
  set R : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) with hR
  set Lw : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ), w t *
    (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)) with hLw
  have hLlim : Tendsto Lw (𝓝[>] 0) (𝓝 0) :=
    tendsto_twisted_radial_nonres_profile hsl hΦd hΦre hidT hGc hGd hG2 η hres hC hα'0 hα'1
      (by positivity) hC' hL hψm hψL hΨ hΨc hΨb
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
    have h := (tendsto_lower_reflected_radial hsl hΦre hidT hGc hGd hG2 (le_refl 1)).const_mul
      ((2 * Real.pi : ℝ) : ℂ)
    have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) = 2 * betaG G := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      push_cast; field_simp
    rw [hval] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    simp only [hR]
    linear_combination ((ε : ℂ) * ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) * h2pi
  -- the sequence `ε_j = (1 + X_j)^{−(N+2)}`
  set e : ℕ → ℝ := fun j => ((1 + X j) ^ (N + 2))⁻¹ with he
  have hXnn : ∀ᶠ j in atTop, 0 ≤ X j := hX.eventually_ge_atTop 0
  have he_pos : ∀ᶠ j in atTop, 0 < e j := hXnn.mono fun j hj => by
    simp only [he]; positivity
  have he_le : ∀ᶠ j in atTop, e j ≤ 1 := hXnn.mono fun j hj => by
    simp only [he]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have he0 : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (1 + X j) ^ (N + 2)) atTop atTop :=
      (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ 1 hX)
    exact h1.inv_tendsto_atTop
  have he_within : Tendsto e atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨he0, he_pos⟩
  have hRe := hRlim.comp he_within
  have hLe := hLlim.comp he_within
  -- the window defect along the sequence
  set c : ℝ := 2 * ((N : ℝ) + 1) with hc
  set Md : ℝ := 3 * ((2 + K₀ * M) * CB) with hMd
  have hMd0 : 0 ≤ Md := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ᶠ j in atTop, ‖R (e j) - κ j * Lw (e j)‖ ≤ Md / (1 + X j) +
      2 * Md * c ^ N * ((1 + X j) ^ ((N + 2) * N) * Real.exp (-((1 + X j) / 2))) := by
    filter_upwards [hXnn, hY 1, hY (N + 3), he_pos, he_le] with j hj hY1 hYN hej hej1
    have hXY : X j ≤ Y j := by rw [pow_one] at hY1; linarith
    have hest := norm_reflected_sub_twisted_le hGc (η := η) (hκ j) hwm hwb hCB hpoly hj hXY
      (hlock j) hej hej1
    refine hest.trans ?_
    have hP : 0 < 1 + X j := by linarith
    have hPN : 0 < (1 + X j) ^ (N + 2) := by positivity
    have t1 : e j * X j * (1 + X j) ^ N ≤ 1 / (1 + X j) := by
      simp only [he]
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_div_iff₀ hPN hP, one_mul]
      calc X j * (1 + X j) ^ N * (1 + X j) ≤ (1 + X j) * (1 + X j) ^ N * (1 + X j) := by
            gcongr; linarith
        _ = (1 + X j) ^ (N + 2) := by ring
    have heY : 1 + X j ≤ e j * Y j := by
      simp only [he]
      rw [inv_mul_eq_div, le_div_iff₀ hPN]
      calc (1 + X j) * (1 + X j) ^ (N + 2) = (1 + X j) ^ (N + 3) := by ring
        _ ≤ Y j := hYN
    have hcpow : (c / e j) ^ N = c ^ N * (1 + X j) ^ ((N + 2) * N) := by
      simp only [he]; rw [div_inv_eq_mul, mul_pow, pow_mul]
    have hexp : Real.exp (-(e j * Y j / 2)) ≤ Real.exp (-((1 + X j) / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Md * (e j * X j * (1 + X j) ^ N) + 2 * Md * ((c / e j) ^ N * Real.exp (-(e j * Y j / 2)))
        ≤ Md * (1 / (1 + X j)) +
            2 * Md * ((c ^ N * (1 + X j) ^ ((N + 2) * N)) * Real.exp (-((1 + X j) / 2))) := by
          rw [hcpow]; gcongr
      _ = Md / (1 + X j) +
            2 * Md * c ^ N * ((1 + X j) ^ ((N + 2) * N) * Real.exp (-((1 + X j) / 2))) := by
          ring
  have hdef : Tendsto (fun j => R (e j) - κ j * Lw (e j)) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound ((tendsto_window_bound Md c N).comp hX)
  have hκL : Tendsto (fun j => κ j * Lw (e j)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) ((hLe.norm.const_mul K₀).trans (by simp))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hκ j) (norm_nonneg _)
  have hR0 : Tendsto (fun j => R (e j)) atTop (𝓝 0) := by
    have := hdef.add hκL
    rw [add_zero] at this
    exact this.congr fun j => by ring
  have h0 : (2 : ℂ) * betaG G = 0 := tendsto_nhds_unique hRe hR0
  exact hβ ((mul_eq_zero.mp h0).resolve_left two_ne_zero)

/-- **Linear lock phases on sparse windows are quantized** (no sublinear twist). -/
theorem windowed_linear_lock_quantization {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {η K₀ : ℝ} {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (((η * (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    ∃ n : ℕ, (n : ℝ) = Real.exp (-(η / 2)) :=
  windowed_linear_lock_quantization_profile hsl hΦd hΦre hid hGc hGd hG2 (C := fun _ => 0)
    monotone_const ⟨1 / 2, 1, by norm_num, fun x hx => by positivity⟩ (Ψ := fun _ => (1 : ℂ))
    (ψ := fun _ => 0) (L := 0) (M := 1) le_rfl measurable_const (fun x => by simp)
    (fun u v _ => by simp) continuous_const (fun v => by simp) hX hY hκ
    (fun j τ h1 h2 => by rw [hlock j τ h1 h2, mul_one])

/-- **A positive linear slope on sparse windows is impossible.** -/
theorem windowed_linear_lock_slope_nonpos {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {η K₀ : ℝ} {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (((η * (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    η ≤ 0 := by
  obtain ⟨n, hn⟩ := windowed_linear_lock_quantization hsl hΦd hΦre hid hGc hGd hG2 hX hY hκ hlock
  have hpos : (0 : ℝ) < n := by rw [hn]; exact Real.exp_pos _
  have h1 : (1 : ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hpos
    exact_mod_cast this
  have h2 : 0 ≤ -(η / 2) := by
    rw [← Real.exp_le_exp, Real.exp_zero, ← hn]; exact h1
  linarith

end

end AbelianTwist

end RHTower
