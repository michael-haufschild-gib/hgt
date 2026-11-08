import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanFrobeniusIsAHyperbolicGreenFunction

/-!
# The archimedean self-energy of a smooth probe is logarithmic

The damped archimedean profile `K_r(x) = e^{−|x|/2}/(1 − r²e^{−2|x|}) = Σ_k r^{2k} e^{−(2k+½)|x|}`
(`archDamped`) is the `ℍ³` Green function of `TheArchimedeanFrobeniusIsAHyperbolicGreenFunction`,
damped. Integrated against a smooth probe it has the following exact structure.

* **Self-energy** (`hasSum_selfEnergy`, `selfEnergy_bounds`). The total mass
  `Z(r) = ∫ K_r = Σ_k r^{2k}·2/(2k + ½)` satisfies
  `log(1/(1 − r²)) + 4 − π²/24 ≤ Z(r) ≤ log(1/(1 − r²)) + 4`: a logarithmic divergence, the
  self-energy of a line charge in three dimensions (`tendsto_selfEnergy_atTop`).
* **Splitting** (`integral_archDamped_mul_eq`). For an integrable `g`,
  `∫ K_r g = g(0)·Z(r) − ∫ K_r (g(0) − g)`.
* **The jump energy converges** (`tendsto_integral_archDamped_mul`). If `h ≥ 0` and `ω h` is
  integrable, `ω(x) = e^{−|x|/2}/(1 − e^{−2|x|})` the archimedean Lévy density, then
  `∫ K_r h → ∫ ω h` as `r → 1`.
* **Renormalization** (`tendsto_renormalized_selfEnergy`). For `g` with `g(0) − g ≥ 0` (every
  autocorrelation `g(x) = ∫ f(t) f(t + x) dt`, since `g(0) − g(x) = ½∫ (f(t) − f(t+x))²`),
  `∫ K_r g − g(0) Z(r) → −∫ ω (g(0) − g)`.

So the archimedean place, damped as an `ℍ³` propagator, needs exactly one counterterm, the diagonal
`g(0) Z(r)` with `Z(r) ∼ log(1/(1 − r²))`; what remains in the limit is minus the archimedean Lévy
jump energy, the off-diagonal part of Weil's archimedean term. The divergence is universal (it sees
the probe only through `g(0) = ‖f‖²`), which is why the diagonal of Weil's form is a
renormalization and carries no sign of its own.
-/

open Real Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

/-- The total mass `Z(r) = ∫ K_r` of the damped archimedean profile. -/
def selfEnergy (r : ℝ) : ℝ := ∫ x, archDamped r x

theorem integral_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) : ∫ x, Real.exp (-(a * |x|)) = 2 / a := by
  have h := integral_comp_abs (f := fun y => Real.exp (-(a * y)))
  simp only at h
  rw [h]
  have h2 := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at h2
  rw [show (fun x : ℝ => Real.exp (-(a * x))) = fun x => Real.exp (-a * x) from
    funext fun x => by ring_nf, h2]
  field_simp

theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable fun x : ℝ => Real.exp (-(a * |x|)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(a * |x|))) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic ha 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (mem_Iic.mp hx)]; ring_nf
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(a * |x|))) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun (fun x hx => ?_)
      measurableSet_Ioi
    simp only [abs_of_pos (mem_Ioi.mp hx)]; ring_nf
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- The terms of the damped profile. -/
theorem archDamped_term_eq (r : ℝ) (k : ℕ) (x : ℝ) :
    r ^ (2 * k) * Real.exp (-(2 * k + 1 / 2) * |x|) =
      r ^ (2 * k) * Real.exp (-((2 * k + 1 / 2) * |x|)) := by ring_nf

theorem archDamped_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) : 0 ≤ archDamped r x :=
  (hasSum_archDamped hr0 hr1 x).nonneg fun k => by positivity

/-- **The self-energy as a series.** `Z(r) = Σ_k r^{2k} · 2/(2k + ½)`. -/
theorem hasSum_selfEnergy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => r ^ (2 * k) * (2 / (2 * k + 1 / 2))) (selfEnergy r) := by
  set F : ℕ → ℝ → ℝ := fun k x => r ^ (2 * k) * Real.exp (-((2 * k + 1 / 2) * |x|))
  have hpos : ∀ k : ℕ, (0 : ℝ) < 2 * k + 1 / 2 := fun k => by positivity
  have hF_int : ∀ k, Integrable (F k) := fun k =>
    (integrable_exp_neg_mul_abs (hpos k)).const_mul _
  have hF_val : ∀ k, ∫ x, F k x = r ^ (2 * k) * (2 / (2 * k + 1 / 2)) := fun k => by
    simp only [F]; rw [integral_const_mul, integral_exp_neg_mul_abs (hpos k)]
  have hF_norm : ∀ k, ∫ x, ‖F k x‖ = r ^ (2 * k) * (2 / (2 * k + 1 / 2)) := fun k => by
    rw [← hF_val k]
    congr 1; funext x
    exact Real.norm_of_nonneg (by positivity)
  have hsum : Summable fun k : ℕ => r ^ (2 * k) * (2 / (2 * k + 1 / 2)) := by
    have hg : Summable fun k : ℕ => (r ^ 2) ^ k * 4 :=
      (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_right 4
    refine hg.of_nonneg_of_le (fun k => by positivity) fun k => ?_
    rw [← pow_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ (hpos k)]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := hasSum_integral_of_summable_integral_norm hF_int (by simpa only [hF_norm] using hsum)
  simp only [hF_val] at h
  convert h using 1
  unfold selfEnergy
  congr 1; funext x
  rw [← (hasSum_archDamped hr0 hr1 x).tsum_eq]
  exact tsum_congr fun k => archDamped_term_eq r k x

/-- **The self-energy is logarithmic.** `log(1/(1 − r²)) + 4 − π²/24 ≤ Z(r) ≤ log(1/(1 − r²)) + 4`. -/
theorem selfEnergy_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    -Real.log (1 - r ^ 2) + 4 - π ^ 2 / 24 ≤ selfEnergy r ∧
      selfEnergy r ≤ -Real.log (1 - r ^ 2) + 4 := by
  have hq : |r ^ 2| < 1 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  have hlog := hasSum_pow_div_log_of_abs_lt_one hq
  have hZ := hasSum_selfEnergy hr0 hr1
  -- split off the term `k = 0`
  have hZ' : HasSum (fun k : ℕ => r ^ (2 * (k + 1)) * (2 / (2 * ((k + 1 : ℕ) : ℝ) + 1 / 2)))
      (selfEnergy r - 4) := by
    have := (hasSum_nat_add_iff' 1).mpr hZ
    simpa [Finset.sum_range_one] using this
  have hz2 := hasSum_zeta_two
  have hz2' : HasSum (fun k : ℕ => (r ^ 2) ^ (k + 1) * (1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2)))
      (∑' k : ℕ, (r ^ 2) ^ (k + 1) * (1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2))) := by
    refine Summable.hasSum ?_
    have hs : Summable fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 :=
      (summable_nat_add_iff 1).mpr hz2.summable
    refine (hs.mul_left (1 / 4)).of_nonneg_of_le (fun k => by positivity) fun k => ?_
    have hrk : (r ^ 2) ^ (k + 1) ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith)
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [show (1 : ℝ) / 4 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) = 1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2) by
      field_simp]
    exact mul_le_of_le_one_left (by positivity) hrk
  have hbound2 : ∑' k : ℕ, (r ^ 2) ^ (k + 1) * (1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2)) ≤ π ^ 2 / 24 := by
    have hs : HasSum (fun k : ℕ => (1 / 4 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) ((1 / 4) * (π ^ 2 / 6)) := by
      have := (hasSum_nat_add_iff' 1).mpr hz2
      simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, div_zero, sub_zero] at this
      exact this.mul_left (1 / 4)
    refine (hasSum_le (fun k => ?_) hz2' hs).trans (le_of_eq (by ring))
    have hrk : (r ^ 2) ^ (k + 1) ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith)
    rw [show (1 / 4 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) = 1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2) by
      field_simp]
    exact mul_le_of_le_one_left (by positivity) hrk
  constructor
  · -- `4/(4k+1) ≥ 1/k − 1/(4k²)`
    have hle := hasSum_le (fun k : ℕ => ?_) (hlog.sub hz2') hZ'
    · linarith
    · have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      rw [show (2 : ℕ) * (k + 1) = 2 * (k + 1) from rfl, pow_mul, Nat.cast_succ]
      push_cast at hk ⊢
      have hq0 : 0 ≤ (r ^ 2) ^ (k + 1) := by positivity
      rw [← mul_sub]
      refine mul_le_mul_of_nonneg_left ?_ hq0
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
  · -- `4/(4k+1) ≤ 1/k`
    have hle := hasSum_le (fun k : ℕ => ?_) hZ' hlog
    · linarith
    · have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      rw [pow_mul, Nat.cast_succ]
      push_cast at hk ⊢
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- **The self-energy diverges** as `r → 1`. -/
theorem tendsto_selfEnergy_atTop : Tendsto selfEnergy (𝓝[<] 1) atTop := by
  have hlog : Tendsto (fun r : ℝ => -Real.log (1 - r ^ 2) + 4 - π ^ 2 / 24) (𝓝[<] 1) atTop := by
    have h1 : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Continuous fun r : ℝ => 1 - r ^ 2 := by fun_prop
        simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
      · have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
          nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
        filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
        exact mem_Ioi.mpr (by nlinarith [mem_Iio.mp hr1])
    have h2 := (Real.tendsto_log_nhdsGT_zero.comp h1).neg
    simp only [Function.comp_def] at h2
    exact (tendsto_neg_atBot_atTop.comp h2).atTop_add tendsto_const_nhds |>.congr fun r => by
      simp [Function.comp_def]; ring
  refine tendsto_atTop_mono' _ ?_ hlog
  have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
  exact (selfEnergy_bounds hr0.le (mem_Iio.mp hr1)).1

/-! ## The jump energy and the renormalized self-energy -/

theorem archDamped_le_archProfile {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {x : ℝ} (hx : x ≠ 0) :
    archDamped r x ≤ archProfile |x| := by
  have hax : 0 < |x| := abs_pos.mpr hx
  have he : Real.exp (-2 * |x|) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  unfold archDamped archProfile
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith)
  nlinarith [Real.exp_pos (-2 * |x|)]

theorem archDamped_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    archDamped r x ≤ (1 - r ^ 2)⁻¹ := by
  have he1 : Real.exp (-|x| / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x])
  have he2 : Real.exp (-2 * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x])
  have hr2 : r ^ 2 < 1 := by nlinarith
  unfold archDamped
  rw [div_le_iff₀ (by nlinarith [Real.exp_pos (-2 * |x|)]), inv_mul_eq_div,
    le_div_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (-2 * |x|), Real.exp_pos (-|x| / 2)]

theorem continuous_archDamped {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Continuous (archDamped r) := by
  unfold archDamped
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => ?_
  have he2 : Real.exp (-2 * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x])
  nlinarith [Real.exp_pos (-2 * |x|)]

theorem tendsto_archDamped {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun r => archDamped r x) (𝓝 1) (𝓝 (archProfile |x|)) := by
  have hax : 0 < |x| := abs_pos.mpr hx
  have hden : 1 - (1 : ℝ) ^ 2 * Real.exp (-2 * |x|) ≠ 0 := by
    rw [one_pow, one_mul]; exact one_sub_exp_neg_two_mul_ne_zero hax.ne'
  have hc : ContinuousAt (fun r : ℝ => archDamped r x) 1 := by
    unfold archDamped
    exact continuousAt_const.div (by fun_prop) hden
  have hv : archDamped 1 x = archProfile |x| := by
    unfold archDamped archProfile; rw [one_pow, one_mul]
  rw [← hv]
  exact hc.tendsto

/-- **The jump energy converges to the archimedean Lévy energy.** -/
theorem tendsto_integral_archDamped_mul {h : ℝ → ℝ} (hh : AEStronglyMeasurable h) (hnn : ∀ x, 0 ≤ h x)
    (hint : Integrable fun x => archProfile |x| * h x) :
    Tendsto (fun r => ∫ x, archDamped r x * h x) (𝓝[<] 1) (𝓝 (∫ x, archProfile |x| * h x)) := by
  have hae : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [ae_iff]; simp
  have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine tendsto_integral_filter_of_dominated_convergence (fun x => archProfile |x| * h x) ?_ ?_ hint ?_
  · filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
    exact (continuous_archDamped hr0.le (mem_Iio.mp hr1)).aestronglyMeasurable.mul hh
  · filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
    filter_upwards [hae] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (archDamped_nonneg hr0.le (mem_Iio.mp hr1) x) (hnn x))]
    exact mul_le_mul_of_nonneg_right (archDamped_le_archProfile hr0.le (mem_Iio.mp hr1).le hx) (hnn x)
  · filter_upwards [hae] with x hx
    exact ((tendsto_archDamped hx).mono_left nhdsWithin_le_nhds).mul_const _

theorem integrable_archDamped {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Integrable (archDamped r) := by
  have hint := (integrable_exp_neg_mul_abs (a := 1 / 2) (by norm_num)).const_mul (1 - r ^ 2)⁻¹
  refine hint.mono' (continuous_archDamped hr0 hr1).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (archDamped_nonneg hr0 hr1 x)]
  have hr2 : r ^ 2 < 1 := by nlinarith
  have he2 : Real.exp (-2 * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x])
  unfold archDamped
  rw [div_le_iff₀ (by nlinarith [Real.exp_pos (-2 * |x|)]),
    show -(1 / 2 * |x|) = -|x| / 2 by ring]
  have hpos : 0 < (1 - r ^ 2)⁻¹ := inv_pos.mpr (by linarith)
  have hmul : (1 - r ^ 2)⁻¹ * (1 - r ^ 2) = 1 := inv_mul_cancel₀ (by linarith)
  nlinarith [Real.exp_pos (-|x| / 2), Real.exp_pos (-2 * |x|)]

/-- **Splitting off the diagonal.** `∫ K_r g = g(0) Z(r) − ∫ K_r (g(0) − g)`. -/
theorem integral_archDamped_mul_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {g : ℝ → ℝ} (hg : Integrable g) :
    ∫ x, archDamped r x * g x = g 0 * selfEnergy r - ∫ x, archDamped r x * (g 0 - g x) := by
  have hK := integrable_archDamped hr0 hr1
  have hKg : Integrable fun x => archDamped r x * g x :=
    hg.bdd_mul (continuous_archDamped hr0 hr1).aestronglyMeasurable
      ⟨(1 - r ^ 2)⁻¹, fun x => by
        rw [Real.norm_of_nonneg (archDamped_nonneg hr0 hr1 x)]; exact archDamped_le_inv hr0 hr1 x⟩
  have hsplit : (fun x => archDamped r x * (g 0 - g x)) =
      fun x => g 0 * archDamped r x - archDamped r x * g x := funext fun x => by ring
  rw [hsplit, integral_sub (hK.const_mul _) hKg, integral_const_mul, selfEnergy]
  ring

/-- **The renormalized self-energy.** For `g` integrable with `g(0) − g ≥ 0` and finite Lévy energy,
`∫ K_r g − g(0) Z(r) → −∫ ω (g(0) − g)`. -/
theorem tendsto_renormalized_selfEnergy {g : ℝ → ℝ} (hg : Integrable g) (hnn : ∀ x, g x ≤ g 0)
    (hint : Integrable fun x => archProfile |x| * (g 0 - g x)) :
    Tendsto (fun r => ∫ x, archDamped r x * g x - g 0 * selfEnergy r) (𝓝[<] 1)
      (𝓝 (-∫ x, archProfile |x| * (g 0 - g x))) := by
  have h := (tendsto_integral_archDamped_mul (hg.aestronglyMeasurable.const_sub (g 0))
    (fun x => sub_nonneg.mpr (hnn x)) hint).neg
  refine h.congr' ?_
  have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
  rw [integral_archDamped_mul_eq hr0.le (mem_Iio.mp hr1) hg]
  ring

end GaloisForLFunctions.SurfaceOfSpecZ
