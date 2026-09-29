import GaloisForLFunctions.HTGeometry.StrelitzSecondJetGap
import GaloisForLFunctions.HTGeometry.StrelitzCircleJetCalculus
import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# The circle bootstrap for order-two logarithmic-jet relations

Let `f` be entire, `u = z f'/f`, `v = z u'`, and let `Q(z; f, u, v) = 0` off the zeros of `f` for a
nonzero `Q ∈ ℂ[z][F, U, V]`.  Call the circle `|z| = r` *clean* when `|f|` exceeds the threshold
`(1 + r)^E (N + 2)^E (3/κ)`, `|v| ≤ ρ`, and the circle average of `u` lies within `1/4` of a
large real number `N`.  If one circle `|z| = r₀` is clean, then so is every larger circle:

* the angular derivative of `u` is `i v`, so `u` stays within `1/2` of `N` on a clean circle;
* the second-jet gap of `Q` then halves the bound for `v`, which keeps `|v| < ρ` nearby;
* the circle average of `u` is locally constant across zero-free annuli;
* along radii `d log |f| / d log r = Re u ≥ N - 1/2`, which outgrows the threshold.

Integrating `Re u ≤ N + 1/2` along radii gives `|f(z)| = O(|z|^{N + 1/2})`, and Cauchy's estimate
makes `f` a polynomial of degree at most `N + 1/2`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Complex Metric Set Filter Topology Real

variable {f : ℂ → ℂ}

/-- The size threshold for `|f|` on the circle of radius `r`. -/
def strelitzCircleThreshold (E : ℕ) (N κ r : ℝ) : ℝ :=
  (1 + r) ^ E * (N + 2) ^ E * (3 / κ)

/-- The second-jet gap property of a relation `Q` at exponent `E`, radius `ρ` and tolerance `κ`. -/
def StrelitzJetGap (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) (E : ℕ) (ρ κ : ℝ) : Prop :=
  ∀ (z F U V : ℂ) (B : ℝ),
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q = 0 →
    1 ≤ ‖z‖ → 1 ≤ ‖F‖ → 1 ≤ ‖U‖ → ‖U‖ ≤ B → ‖V‖ ≤ ρ →
    (1 + ‖z‖) ^ E * B ^ E / ‖F‖ + B ^ E / ‖z‖ + 1 / ‖U‖ ≤ κ →
    ‖V‖ ≤ ρ / 2

theorem strelitzCircleThreshold_pos {E : ℕ} {N κ r : ℝ} (hN : 0 ≤ N) (hκ : 0 < κ)
    (hr : 0 ≤ r) : 0 < strelitzCircleThreshold E N κ r := by
  unfold strelitzCircleThreshold
  have : 0 < 1 + r := by linarith
  have : 0 < N + 2 := by linarith
  positivity

/-- **One-circle improvement.**  On a clean circle beyond `r₀`, the first jet is within `1/2` of
`N` and the second-jet gap halves the bound for the second jet. -/
theorem strelitzCircle_improve (hf : Differentiable ℂ f)
    {Q : MvPolynomial (Fin 3) (Polynomial ℂ)}
    (hrel : ∀ z, f z ≠ 0 → MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      ![f z, eulerLogDeriv f z, eulerLogDerivSecond f z] Q = 0)
    {E : ℕ} {ρ κ : ℝ} (hρ : 0 < ρ) (hρπ : 3 * π * ρ ≤ 1 / 4) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hgap : StrelitzJetGap Q E ρ κ) {r₀ N r : ℝ} (hr₀ : 1 ≤ r₀) (hN : 3 / κ + 1 ≤ N)
    (hr₀N : 3 * (N + 2) ^ E / κ ≤ r₀) (hr : r₀ ≤ r)
    (hcirc : ∀ z ∈ sphere (0 : ℂ) r,
      strelitzCircleThreshold E N κ r ≤ ‖f z‖ ∧ ‖eulerLogDerivSecond f z‖ ≤ ρ)
    (hmean : ‖circleAverage (eulerLogDeriv f) 0 r - N‖ ≤ 1 / 4) :
    ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0 ∧ ‖eulerLogDeriv f z - N‖ ≤ 1 / 2 ∧
      ‖eulerLogDerivSecond f z‖ ≤ ρ / 2 := by
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hr0 : 0 < r := by linarith
  have h3κ : 0 < 3 / κ := by positivity
  have h3κ3 : 3 ≤ 3 / κ := by rw [le_div_iff₀ hκ]; linarith
  have hN1 : 1 ≤ N := by linarith
  have hB1 : 1 ≤ N + 2 := by linarith
  have hGpos : 0 < strelitzCircleThreshold E N κ r :=
    strelitzCircleThreshold_pos (by linarith) hκ hr0.le
  have hG1 : 1 ≤ strelitzCircleThreshold E N κ r := by
    unfold strelitzCircleThreshold
    have h1 : 1 ≤ (1 + r) ^ E := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ (N + 2) ^ E := one_le_pow₀ hB1
    have h3 : 1 ≤ 3 / κ := by rw [le_div_iff₀ hκ]; linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ (1 + r) ^ E * (N + 2) ^ E * (3 / κ) := by gcongr
  have hne : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0 := fun z hz h => by
    have := (hcirc z hz).1
    rw [h, norm_zero] at this
    linarith
  intro z hz
  have hzr : ‖z‖ = r := by simpa using hz
  have hosc := norm_eulerLogDeriv_sub_circleAverage_le hf hr0 hρ.le
    (fun w hw => ⟨hne w hw, (hcirc w hw).2⟩) hz
  have hu : ‖eulerLogDeriv f z - N‖ ≤ 1 / 2 := by
    calc ‖eulerLogDeriv f z - N‖
        ≤ ‖eulerLogDeriv f z - circleAverage (eulerLogDeriv f) 0 r‖ +
            ‖circleAverage (eulerLogDeriv f) 0 r - N‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add (hosc.trans hρπ) hmean
      _ = 1 / 2 := by norm_num
  have hNnorm : ‖(N : ℂ)‖ = N := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hulo : N - 1 / 2 ≤ ‖eulerLogDeriv f z‖ := by
    have h := norm_sub_norm_le (N : ℂ) (eulerLogDeriv f z)
    rw [norm_sub_rev, hNnorm] at h
    linarith
  have huhi : ‖eulerLogDeriv f z‖ ≤ N + 2 := by
    have h := norm_sub_norm_le (eulerLogDeriv f z) (N : ℂ)
    rw [hNnorm] at h
    linarith
  refine ⟨hne z hz, hu, ?_⟩
  have hfz := (hcirc z hz).1
  refine hgap z (f z) (eulerLogDeriv f z) (eulerLogDerivSecond f z) (N + 2) (hrel z (hne z hz))
    (by rw [hzr]; exact hr1) (hG1.trans hfz) (by linarith) huhi (hcirc z hz).2 ?_
  have h1 : (1 + ‖z‖) ^ E * (N + 2) ^ E / ‖f z‖ ≤ κ / 3 := by
    rw [hzr, div_le_iff₀ (hGpos.trans_le hfz)]
    calc (1 + r) ^ E * (N + 2) ^ E = κ / 3 * strelitzCircleThreshold E N κ r := by
          unfold strelitzCircleThreshold
          field_simp
      _ ≤ κ / 3 * ‖f z‖ := mul_le_mul_of_nonneg_left hfz (by positivity)
  have h2 : (N + 2) ^ E / ‖z‖ ≤ κ / 3 := by
    rw [hzr, div_le_iff₀ hr0]
    rw [div_le_iff₀ hκ] at hr₀N
    nlinarith
  have h3 : 1 / ‖eulerLogDeriv f z‖ ≤ κ / 3 := by
    rw [div_le_iff₀ (by linarith)]
    have h3u : 3 / κ ≤ ‖eulerLogDeriv f z‖ := by linarith
    calc (1 : ℝ) = κ / 3 * (3 / κ) := by field_simp
      _ ≤ κ / 3 * ‖eulerLogDeriv f z‖ := mul_le_mul_of_nonneg_left h3u (by positivity)
  linarith

/-- **Continuous induction in the radius.**  If the circle of radius `r₀` is clean, then every
circle of radius `r ≥ r₀` is clean with the same `N`. -/
theorem strelitzCircle_bootstrap (hf : Differentiable ℂ f)
    {Q : MvPolynomial (Fin 3) (Polynomial ℂ)}
    (hrel : ∀ z, f z ≠ 0 → MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      ![f z, eulerLogDeriv f z, eulerLogDerivSecond f z] Q = 0)
    {E : ℕ} {ρ κ : ℝ} (hρ : 0 < ρ) (hρπ : 3 * π * ρ ≤ 1 / 4) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hgap : StrelitzJetGap Q E ρ κ) {r₀ N : ℝ} (hr₀ : 1 ≤ r₀) (hNE : (E : ℝ) + 1 ≤ N)
    (hN : 3 / κ + 1 ≤ N) (hr₀N : 3 * (N + 2) ^ E / κ ≤ r₀)
    (hinit : ∀ z ∈ sphere (0 : ℂ) r₀, strelitzCircleThreshold E N κ r₀ ≤ ‖f z‖ ∧
      ‖eulerLogDeriv f z - N‖ ≤ 1 / 4 ∧ ‖eulerLogDerivSecond f z‖ ≤ ρ) :
    ∀ r, r₀ ≤ r →
      (∀ z ∈ sphere (0 : ℂ) r,
        strelitzCircleThreshold E N κ r ≤ ‖f z‖ ∧ ‖eulerLogDerivSecond f z‖ ≤ ρ) ∧
      ‖circleAverage (eulerLogDeriv f) 0 r - N‖ ≤ 1 / 4 := by
  set G : ℝ → ℝ := strelitzCircleThreshold E N κ with hGdef
  set S : Set ℝ := {r | (∀ z ∈ sphere (0 : ℂ) r, G r ≤ ‖f z‖ ∧
      ‖eulerLogDerivSecond f z‖ ≤ ρ) ∧ ‖circleAverage (eulerLogDeriv f) 0 r - N‖ ≤ 1 / 4}
    with hS
  have h3κ : 0 < 3 / κ := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hGpos : ∀ r, 0 ≤ r → 0 < G r := fun r hr => strelitzCircleThreshold_pos hN0 hκ hr
  have hGcont : Continuous G := by
    show Continuous fun r => (1 + r) ^ E * (N + 2) ^ E * (3 / κ)
    fun_prop
  have hr₀0 : 0 < r₀ := by linarith
  intro r hr
  suffices hsub : Icc r₀ r ⊆ S from hsub ⟨hr, le_rfl⟩
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
  · -- closedness
    apply isClosed_of_closure_subset
    intro x hx
    have hxI : x ∈ Icc r₀ r := by
      have h := closure_mono inter_subset_right hx
      rwa [closure_Icc] at h
    refine ⟨?_, hxI⟩
    obtain ⟨y, hyS, hy⟩ := mem_closure_iff_seq_limit.mp hx
    have hx0 : 0 < x := by linarith [hxI.1]
    have hyr : ∀ n, 0 < y n := fun n => by linarith [(hyS n).2.1]
    have hcirc : ∀ z ∈ sphere (0 : ℂ) x, G x ≤ ‖f z‖ ∧ ‖eulerLogDerivSecond f z‖ ≤ ρ := by
      intro z hz
      have hzx : ‖z‖ = x := by simpa using hz
      set zs : ℕ → ℂ := fun n => ((y n / x : ℝ) : ℂ) * z with hzsdef
      have hzs : ∀ n, zs n ∈ sphere (0 : ℂ) (y n) := fun n => by
        rw [mem_sphere_zero_iff_norm]
        simp only [hzsdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, hzx]
        rw [abs_of_pos (div_pos (hyr n) hx0)]
        field_simp
      have hzs_t : Tendsto zs atTop (𝓝 z) := by
        have h1 : Tendsto (fun n => y n / x) atTop (𝓝 (x / x)) := hy.div_const x
        rw [div_self hx0.ne'] at h1
        have h2 : Tendsto (fun n => ((y n / x : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 1).comp h1
        have h3 := h2.mul_const z
        rw [Complex.ofReal_one, one_mul] at h3
        exact h3
      have hfG : G x ≤ ‖f z‖ :=
        le_of_tendsto_of_tendsto' ((hGcont.tendsto x).comp hy)
          ((hf.continuous.tendsto z).comp hzs_t).norm fun n => ((hyS n).1.1 _ (hzs n)).1
      refine ⟨hfG, ?_⟩
      have hfz : f z ≠ 0 := fun h => by
        rw [h, norm_zero] at hfG
        linarith [hGpos x hx0.le]
      exact le_of_tendsto' ((continuousAt_eulerLogDerivSecond hf hfz).tendsto.comp hzs_t).norm
        fun n => ((hyS n).1.1 _ (hzs n)).2
    refine ⟨hcirc, ?_⟩
    have hne : ∀ z ∈ sphere (0 : ℂ) x, f z ≠ 0 := fun z hz h => by
      have := (hcirc z hz).1
      rw [h, norm_zero] at this
      linarith [hGpos x hx0.le]
    obtain ⟨δ, hδ, hloc⟩ := exists_pos_circleAverage_eulerLogDeriv_eq hf hx0 hne
    have hev : ∀ᶠ n in atTop, dist (y n) x < δ := Metric.tendsto_nhds.mp hy δ hδ
    obtain ⟨n, hn⟩ := hev.exists
    rw [Real.dist_eq] at hn
    rw [← (hloc (y n) hn).2]
    exact (hyS n).1.2
  · -- the initial circle
    refine ⟨fun z hz => ⟨(hinit z hz).1, (hinit z hz).2.2⟩, ?_⟩
    refine norm_circleAverage_eulerLogDeriv_sub_le hf hr₀0 fun z hz => ⟨fun h => ?_,
      (hinit z hz).2.1⟩
    have := (hinit z hz).1
    rw [h, norm_zero] at this
    linarith [hGpos r₀ hr₀0.le]
  · -- the step to the right
    rintro R ⟨hRS, hRI⟩
    have hR0 : 0 < R := by linarith [hRI.1]
    have himp := strelitzCircle_improve hf hrel hρ hρπ hκ hκ1 hgap hr₀ hN hr₀N hRI.1
      hRS.1 hRS.2
    set O : Set ℂ := {z | f z ≠ 0 ∧ ‖eulerLogDerivSecond f z‖ < ρ} with hOdef
    have hO : IsOpen O := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hfz, hvz⟩
      exact (hf.continuous.continuousAt.eventually_ne hfz).and
        (Filter.Tendsto.eventually_lt_const hvz (continuousAt_eulerLogDerivSecond hf hfz).norm)
    have hsubO : sphere (0 : ℂ) R ⊆ O := fun z hz =>
      ⟨(himp z hz).1, by linarith [(himp z hz).2.2]⟩
    obtain ⟨δ₁, hδ₁, hO₁⟩ := exists_pos_forall_mem_of_sphere_subset hO hR0 hsubO
    obtain ⟨δ₂, hδ₂, hloc⟩ :=
      exists_pos_circleAverage_eulerLogDeriv_eq hf hR0 fun z hz => (himp z hz).1
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    refine ⟨R + min δ₁ δ₂, by simp only [mem_Ioi]; linarith [lt_min hδ₁ hδ₂], ?_⟩
    intro y hy
    have hyR : R < y := hy.1
    have hyδ : y - R < min δ₁ δ₂ := by linarith [hy.2]
    have hgood : ∀ z : ℂ, R ≤ ‖z‖ → ‖z‖ ≤ y →
        f z ≠ 0 ∧ ‖eulerLogDerivSecond f z‖ < ρ ∧ ‖eulerLogDeriv f z - N‖ ≤ 1 / 2 := by
      intro z hz1 hz2
      set t := ‖z‖ with ht
      have ht0 : 0 < t := by linarith
      have htO : ∀ w ∈ sphere (0 : ℂ) t, w ∈ O := fun w hw => by
        refine hO₁ w ?_
        have hwt : ‖w‖ = t := by simpa using hw
        rw [hwt, abs_of_nonneg (by linarith)]
        linarith [min_le_left δ₁ δ₂]
      have hmeant : circleAverage (eulerLogDeriv f) 0 t = circleAverage (eulerLogDeriv f) 0 R :=
        (hloc t (by rw [abs_of_nonneg (by linarith)]; linarith [min_le_right δ₁ δ₂])).2
      have hzt : z ∈ sphere (0 : ℂ) t := by simp [ht]
      have hosc := norm_eulerLogDeriv_sub_circleAverage_le hf ht0 hρ.le
        (fun w hw => ⟨(htO w hw).1, (htO w hw).2.le⟩) hzt
      refine ⟨(htO z hzt).1, (htO z hzt).2, ?_⟩
      rw [hmeant] at hosc
      calc ‖eulerLogDeriv f z - N‖
          ≤ ‖eulerLogDeriv f z - circleAverage (eulerLogDeriv f) 0 R‖ +
              ‖circleAverage (eulerLogDeriv f) 0 R - N‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1 / 4 + 1 / 4 := add_le_add (hosc.trans hρπ) hRS.2
        _ = 1 / 2 := by norm_num
    have hre : ∀ z : ℂ, R ≤ ‖z‖ → ‖z‖ ≤ y → f z ≠ 0 ∧
        N - 1 / 2 ≤ (eulerLogDeriv f z).re ∧ (eulerLogDeriv f z).re ≤ N + 1 / 2 := by
      intro z hz1 hz2
      obtain ⟨hfz, -, hu⟩ := hgood z hz1 hz2
      have h := (Complex.abs_re_le_norm (eulerLogDeriv f z - N)).trans hu
      rw [Complex.sub_re, Complex.ofReal_re, abs_le] at h
      exact ⟨hfz, by linarith [h.1], by linarith [h.2]⟩
    refine ⟨fun z hz => ?_, ?_⟩
    · have hzy : ‖z‖ = y := by simpa using hz
      refine ⟨?_, (hgood z (by rw [hzy]; exact hyR.le) hzy.le).2.1.le⟩
      have hy0 : 0 < y := by linarith
      set w : ℂ := ((R / y : ℝ) : ℂ) * z with hwdef
      have hw : ‖w‖ = R := by
        simp only [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, hzy]
        rw [abs_of_pos (div_pos hR0 hy0)]
        field_simp
      have hwz : ((y / R : ℝ) : ℂ) * w = z := by
        simp only [hwdef]
        rw [← mul_assoc, ← Complex.ofReal_mul, show y / R * (R / y) = 1 by field_simp]
        simp
      have hrad := (log_norm_radial_sub_bounds hf hR0 hyR.le hw hre).1
      rw [hwz] at hrad
      have hfw : G R ≤ ‖f w‖ := (hRS.1 w (by simpa using hw)).1
      have hfz0 : 0 < ‖f z‖ :=
        norm_pos_iff.mpr (hgood z (by rw [hzy]; exact hyR.le) hzy.le).1
      rw [← Real.log_le_log_iff (hGpos y hy0.le) hfz0]
      have hB0 : 0 < N + 2 := by linarith
      have hlogG' : ∀ r : ℝ, 0 ≤ r → Real.log (G r) =
          (E : ℝ) * Real.log (1 + r) + (E : ℝ) * Real.log (N + 2) + Real.log (3 / κ) := by
        intro r hr
        have h1r : 0 < 1 + r := by linarith
        show Real.log ((1 + r) ^ E * (N + 2) ^ E * (3 / κ)) = _
        rw [Real.log_mul (by positivity) h3κ.ne', Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow]
      have hlogG : Real.log (G y) - Real.log (G R) =
          (E : ℝ) * (Real.log (1 + y) - Real.log (1 + R)) := by
        rw [hlogG' y hy0.le, hlogG' R hR0.le]
        ring
      have h1R : Real.log (1 + y) - Real.log (1 + R) ≤ Real.log y - Real.log R := by
        rw [← Real.log_div (by linarith) (by linarith), ← Real.log_div hy0.ne' hR0.ne']
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ (by linarith) hR0]
        nlinarith
      have hEN : (E : ℝ) ≤ N - 1 / 2 := by linarith
      have hlogpos : 0 ≤ Real.log y - Real.log R := by
        linarith [Real.log_le_log hR0 hyR.le]
      have hlogGR : Real.log (G R) ≤ Real.log ‖f w‖ := Real.log_le_log (hGpos R hR0.le) hfw
      have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
      have hm1 := mul_le_mul_of_nonneg_left h1R hE0
      have hm2 := mul_le_mul_of_nonneg_right hEN hlogpos
      linarith
    · rw [(hloc y (by rw [abs_of_nonneg (by linarith)]; linarith [min_le_right δ₁ δ₂])).2]
      exact hRS.2

/-- **Clean circles force polynomials.**  An entire solution of an order-two logarithmic-jet
relation with a clean circle beyond the thresholds has vanishing Taylor coefficients above
`N + 1/2`. -/
theorem iteratedDeriv_eq_zero_of_strelitzCleanCircle (hf : Differentiable ℂ f)
    {Q : MvPolynomial (Fin 3) (Polynomial ℂ)}
    (hrel : ∀ z, f z ≠ 0 → MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      ![f z, eulerLogDeriv f z, eulerLogDerivSecond f z] Q = 0)
    {E : ℕ} {ρ κ : ℝ} (hρ : 0 < ρ) (hρπ : 3 * π * ρ ≤ 1 / 4) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hgap : StrelitzJetGap Q E ρ κ) {r₀ N : ℝ} (hr₀ : 1 ≤ r₀) (hNE : (E : ℝ) + 1 ≤ N)
    (hN : 3 / κ + 1 ≤ N) (hr₀N : 3 * (N + 2) ^ E / κ ≤ r₀)
    (hinit : ∀ z ∈ sphere (0 : ℂ) r₀, strelitzCircleThreshold E N κ r₀ ≤ ‖f z‖ ∧
      ‖eulerLogDeriv f z - N‖ ≤ 1 / 4 ∧ ‖eulerLogDerivSecond f z‖ ≤ ρ) :
    ∀ n : ℕ, N + 1 / 2 < n → iteratedDeriv n f 0 = 0 := by
  have hboot := strelitzCircle_bootstrap hf hrel hρ hρπ hκ hκ1 hgap hr₀ hNE hN hr₀N hinit
  have hr₀0 : 0 < r₀ := by linarith
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_sphere (0 : ℂ) r₀).exists_bound_of_continuousOn hf.continuous.continuousOn
  have hre : ∀ r, r₀ ≤ r → ∀ z : ℂ, r₀ ≤ ‖z‖ → ‖z‖ ≤ r → f z ≠ 0 ∧
      N - 1 / 2 ≤ (eulerLogDeriv f z).re ∧ (eulerLogDeriv f z).re ≤ N + 1 / 2 := by
    intro r _ z hz1 _
    have hS := hboot ‖z‖ hz1
    obtain ⟨hfz, hu, -⟩ := strelitzCircle_improve hf hrel hρ hρπ hκ hκ1 hgap hr₀ hN hr₀N hz1
      hS.1 hS.2 z (by simp)
    have h := (Complex.abs_re_le_norm (eulerLogDeriv f z - N)).trans hu
    rw [Complex.sub_re, Complex.ofReal_re, abs_le] at h
    exact ⟨hfz, by linarith [h.1], by linarith [h.2]⟩
  have hgrowth : ∀ r, r₀ ≤ r → ∀ z ∈ sphere (0 : ℂ) r,
      ‖f z‖ ≤ M₀ * (r / r₀) ^ (N + 1 / 2) := by
    intro r hr z hz
    have hzr : ‖z‖ = r := by simpa using hz
    have hr0 : 0 < r := by linarith
    set w : ℂ := ((r₀ / r : ℝ) : ℂ) * z with hwdef
    have hw : ‖w‖ = r₀ := by
      simp only [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, hzr]
      rw [abs_of_pos (div_pos hr₀0 hr0)]
      field_simp
    have hwz : ((r / r₀ : ℝ) : ℂ) * w = z := by
      simp only [hwdef]
      rw [← mul_assoc, ← Complex.ofReal_mul, show r / r₀ * (r₀ / r) = 1 by field_simp]
      simp
    have hrad := (log_norm_radial_sub_bounds hf hr₀0 hr hw (hre r hr)).2
    rw [hwz] at hrad
    have hfz0 : 0 < ‖f z‖ := norm_pos_iff.mpr (hre r hr z (by rw [hzr]; exact hr) hzr.le).1
    have hfw0 : 0 < ‖f w‖ := norm_pos_iff.mpr (hre r hr w (by rw [hw]) (by rw [hw]; exact hr)).1
    have hpow : (r / r₀) ^ (N + 1 / 2) =
        Real.exp ((N + 1 / 2) * (Real.log r - Real.log r₀)) := by
      rw [Real.rpow_def_of_pos (div_pos hr0 hr₀0), Real.log_div hr0.ne' hr₀0.ne', mul_comm]
    calc ‖f z‖ = Real.exp (Real.log ‖f z‖) := (Real.exp_log hfz0).symm
      _ ≤ Real.exp (Real.log ‖f w‖ + (N + 1 / 2) * (Real.log r - Real.log r₀)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ‖f w‖ * (r / r₀) ^ (N + 1 / 2) := by rw [Real.exp_add, Real.exp_log hfw0, hpow]
      _ ≤ M₀ * (r / r₀) ^ (N + 1 / 2) :=
          mul_le_mul_of_nonneg_right (hM₀ w (by simpa using hw)) (by positivity)
  intro n hn
  by_contra hne
  set a := ‖iteratedDeriv n f 0 / (n.factorial : ℂ)‖ with ha_def
  have ha : 0 < a :=
    norm_pos_iff.mpr (div_ne_zero hne (Nat.cast_ne_zero.mpr n.factorial_ne_zero))
  have hkey : ∀ t : ℝ, 1 ≤ t → a * r₀ ^ n ≤ M₀ * t ^ (-((n : ℝ) - (N + 1 / 2))) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have h := taylorCoeff_norm_mul_pow_le hf (r := r₀ * t) (by positivity)
      (hgrowth (r₀ * t) (by nlinarith)) n
    rw [show r₀ * t / r₀ = t by field_simp, mul_pow] at h
    have htn : 0 < t ^ n := by positivity
    rw [Real.rpow_neg ht0.le, Real.rpow_sub ht0, Real.rpow_natCast, inv_div, ← mul_div_assoc,
      le_div_iff₀ htn]
    linarith [h]
  have hlim : Tendsto (fun t : ℝ => M₀ * t ^ (-((n : ℝ) - (N + 1 / 2)))) atTop (𝓝 (M₀ * 0)) :=
    (tendsto_rpow_neg_atTop (by linarith)).const_mul M₀
  rw [mul_zero] at hlim
  have hev := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < a * r₀ ^ n))
  obtain ⟨t, ht⟩ := (hev.and (eventually_ge_atTop 1)).exists
  linarith [hkey t ht.2, ht.1]

end

end GaloisForLFunctions.HTGeometry
