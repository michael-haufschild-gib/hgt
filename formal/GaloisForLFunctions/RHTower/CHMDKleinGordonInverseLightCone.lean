import GaloisForLFunctions.RHTower.CHMDArchimedeanBoundarySingularity

/-!
# CHMD: Cramér's theorem in Klein–Gordon coordinates through the inverse light cone

The light-cone identity at mass² `= −2` inverts the one at mass² `= 2`: for `w² = r² + 2`,

`cos(z r) = cos(z w) + z² ∫_0^1 B(−2z²(1−t²)) cos(z t w) dt`   (`cos_mul_eq_inverseLightCone`).

Summing over the zeros with `r = γ_ρ`, `w = √(γ_ρ² + 2)` gives, on the time strip,

`Φ₀(z) = L⁻¹[Φ](z) = Φ(z) + z² ∫_0^1 B(−2z²(1−t²)) Φ(zt) dt`
(`masslessZeroWave_eq_inverseLightConeTransmuteC`),

so the Klein–Gordon causal wave `Φ` determines the massless wave by an explicit Volterra operator,
and `L`, `L⁻¹` are mutually inverse on the pair (`inverseLightConeTransmuteC_lightConeTransmuteC`,
`lightConeTransmuteC_inverseLightConeTransmuteC`).

**Cramér's theorem in Klein–Gordon coordinates** (`kgZeroWave_inverseLightCone_cramer`).  The function
`L⁻¹[Φ]`, built from the Klein–Gordon zero-side wave alone, continues beyond the unit strip,
holomorphic at every `v` with `|Im v| < 3/2`, `Re v ≠ 0` other than the prime points, and has a
simple pole — meromorphic of order `−1` — at each of `±log n ± i` (`Λ(n) ≠ 0`), with residue
`s₂ (2i/π) Λ(n)/√n` at `s₁ log n + s₂ i`.  The inverse light cone removes exactly the dispersive
Bessel tail, which is what turns these poles into pole-plus-logarithm singularities of `Φ` itself
(`not_meromorphicAt_kgZeroWave_four`).

A simple pole is certified by the removable-singularity theorem: a function holomorphic on a punctured
neighbourhood with `(z − p) F(z) → R ≠ 0` is meromorphic of order `−1`
(`meromorphicAt_order_eq_neg_one_of_tendsto`).
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDGrowthCollapse

/-! ## The inverse light-cone transmutation -/

/-- The inverse light-cone transmutation `L⁻¹[A](z) = A(z) + z² ∫_0^1 B(−2z²(1−t²)) A(zt) dt`. -/
def inverseLightConeTransmuteC (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  A z + z ^ 2 * ∫ t in (0 : ℝ)..1, lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * A (z * t)

theorem norm_lightConeBessel_inverse_light_cone_le (z : ℂ) {t : ℝ} (ht : |t| ≤ 1) :
    ‖lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2))‖ ≤ Real.exp (‖z‖ ^ 2 / 2) := by
  refine (norm_lightConeBessel_le _).trans (Real.exp_le_exp.mpr ?_)
  have ht2 : |1 - t ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg t, sq_abs t, abs_le.mp ht]
  rw [norm_mul, norm_mul, norm_pow, show (1 - (t : ℂ) ^ 2) = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, show ‖(-2 : ℂ)‖ = 2 by norm_num]
  have := mul_le_mul_of_nonneg_left ht2 (by positivity : (0 : ℝ) ≤ 2 * ‖z‖ ^ 2)
  linarith

/-- **The inverse light-cone identity**: for `w² = r² + 2`,
`cos(z r) = cos(z w) + z² ∫_0^1 B(−2z²(1−t²)) cos(z t w) dt`. -/
theorem cos_mul_eq_inverseLightCone (z r w : ℂ) (hw : w ^ 2 = r ^ 2 + 2) :
    Complex.cos (z * r) = Complex.cos (z * w) +
      z ^ 2 * ∫ t in (0 : ℝ)..1,
        lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * Complex.cos (z * t * w) := by
  have h := cos_mul_eq_lightCone z w (-2) r (by rw [hw]; ring)
  set g : ℝ → ℂ := fun t => lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
    Complex.cos (z * w * t) with hg
  have hgc : Continuous g := by
    simp only [hg]
    exact (differentiable_lightConeBessel.continuous.comp (by fun_prop)).mul (by fun_prop)
  have heven : ∀ t, g (-t) = g t := by
    intro t; simp only [hg]; push_cast
    rw [neg_sq, show z * w * -(t : ℂ) = -(z * w * t) by ring, Complex.cos_neg]
  have hsym : ∫ t in (-1 : ℝ)..0, g t = ∫ t in (0 : ℝ)..1, g t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) g
    simp only [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t _ => heven t
  have hsplit : ∫ t in (-1 : ℝ)..1, g t = 2 * ∫ t in (0 : ℝ)..1, g t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _), hsym]
    ring
  have hcomm : (∫ t in (0 : ℝ)..1, lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      Complex.cos (z * t * w)) = ∫ t in (0 : ℝ)..1, g t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hg]
    rw [mul_right_comm z (t : ℂ) w]
  rw [hcomm]
  have h' : Complex.cos (z * r) = Complex.cos (z * w) - -2 * z ^ 2 / 4 * ∫ t in (-1 : ℝ)..1, g t := h
  rw [h', hsplit]
  ring

/-! ## The zero side -/

theorem summable_kgZeroTerm {z : ℂ} (hz : |z.im| < 1) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * kgFreq ρ) * kgWeight ρ) :=
  Summable.of_norm_bounded
    ((summable_mult_mul_exp_neg_abs_re (by linarith : (0 : ℝ) < 1 - |z.im|)).mul_left
      (sechConst * Real.exp (|z.re| / 2 + 5 / 2 * |z.im|)))
    fun ρ => norm_kgTerm_le' le_rfl (abs_nonneg _) le_rfl ρ

/-- **The massless wave is the inverse transmutation of the Klein–Gordon wave** on `|Im z| < 1`. -/
theorem masslessZeroWave_eq_inverseLightConeTransmuteC {z : ℂ} (hz : |z.im| < 1) :
    masslessZeroWave z = inverseLightConeTransmuteC kgZeroWave z := by
  haveI : Countable zetaZeroConfig.carrier := WeilConditional.countable_carrier.to_subtype
  set F : zetaZeroConfig.carrier → ℝ → ℂ := fun ρ t =>
    lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      ((zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * t * kgFreq ρ) * kgWeight ρ)) with hF
  have hint : HasSum (fun ρ => ∫ t in (0 : ℝ)..1, F ρ t)
      (∫ t in (0 : ℝ)..1, lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
        kgZeroWave (z * t)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun ρ _ => Real.exp (‖z‖ ^ 2 / 2) * (sechConst * Real.exp (|z.re| / 2 + 5 / 2 * |z.im|) *
        ((zetaZeroConfig.mult ρ : ℝ) * Real.exp (-((1 - |z.im|) *
          |(Zeta23.gammaOf (ρ : ℂ)).re|)))))
      (fun ρ => (Continuous.aestronglyMeasurable (by
        simp only [hF]
        exact (differentiable_lightConeBessel.continuous.comp (by fun_prop)).mul (by fun_prop))))
      (fun ρ => Eventually.of_forall fun t ht => ?_)
      (Eventually.of_forall fun _ _ =>
        (((summable_mult_mul_exp_neg_abs_re (by linarith : (0 : ℝ) < 1 - |z.im|)).mul_left
          (sechConst * Real.exp (|z.re| / 2 + 5 / 2 * |z.im|))).mul_left
            (Real.exp (‖z‖ ^ 2 / 2))))
      intervalIntegrable_const
      (Eventually.of_forall fun t ht => ?_)
    · rw [Set.uIoc_of_le zero_le_one] at ht
      have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      simp only [hF]
      rw [norm_mul]
      refine mul_le_mul (norm_lightConeBessel_inverse_light_cone_le z hta)
        (norm_kgTerm_le' (z := z * t) ?_ (abs_nonneg _) ?_ ρ) (norm_nonneg _) (Real.exp_pos _).le
      · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hta
      · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hta
    · have hzt : |(z * t).im| < 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul]
        have : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        nlinarith [abs_nonneg z.im, abs_nonneg t]
      exact ((summable_kgZeroTerm hzt).hasSum).mul_left _
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ) =
        (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * kgFreq ρ) * kgWeight ρ) +
          z ^ 2 * ∫ t in (0 : ℝ)..1, F ρ t := by
    intro ρ
    rw [cos_mul_eq_inverseLightCone z _ _ (kgFreq_sq ρ)]
    simp only [hF]
    rw [show (fun t : ℝ => lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
        ((zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * t * kgFreq ρ) * kgWeight ρ))) =
        fun t : ℝ => ((zetaZeroConfig.mult ρ : ℂ) * kgWeight ρ) *
          (lightConeBessel (-2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * Complex.cos (z * t * kgFreq ρ)) by
        funext t; ring,
      intervalIntegral.integral_const_mul]
    ring
  have hs := summable_kgZeroTerm hz
  unfold masslessZeroWave inverseLightConeTransmuteC kgZeroWave
  simp_rw [hterm]
  rw [hs.tsum_add (hint.summable.mul_left _), tsum_mul_left, hint.tsum_eq]
  rfl

theorem mul_ofReal_mem_strip {z : ℂ} (hz : |z.im| < 1) {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) :
    |(z * t).im| < 1 := by
  rw [uIcc_of_le zero_le_one] at ht
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul,
    abs_of_nonneg ht.1]
  nlinarith [abs_nonneg z.im, ht.1, ht.2]

/-- `L⁻¹ ∘ L` is the identity on the massless wave over the time strip. -/
theorem inverseLightConeTransmuteC_lightConeTransmuteC {z : ℂ} (hz : |z.im| < 1) :
    inverseLightConeTransmuteC (lightConeTransmuteC masslessZeroWave) z = masslessZeroWave z := by
  rw [masslessZeroWave_eq_inverseLightConeTransmuteC hz]
  unfold inverseLightConeTransmuteC
  rw [← kgZeroWave_eq_lightConeTransmuteC hz]
  congr 2
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [← kgZeroWave_eq_lightConeTransmuteC (mul_ofReal_mem_strip hz ht)]

/-- `L ∘ L⁻¹` is the identity on the Klein–Gordon wave over the time strip. -/
theorem lightConeTransmuteC_inverseLightConeTransmuteC {z : ℂ} (hz : |z.im| < 1) :
    lightConeTransmuteC (inverseLightConeTransmuteC kgZeroWave) z = kgZeroWave z := by
  rw [kgZeroWave_eq_lightConeTransmuteC hz]
  unfold lightConeTransmuteC
  rw [← masslessZeroWave_eq_inverseLightConeTransmuteC hz]
  congr 2
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [← masslessZeroWave_eq_inverseLightConeTransmuteC (mul_ofReal_mem_strip hz ht)]

/-! ## Simple poles -/

/-- **Simple poles from residues.**  A function holomorphic on a punctured neighbourhood of `p` with
`(z − p) F(z) → R ≠ 0` is meromorphic at `p` of order `−1` (removable-singularity theorem applied to
`(z − p) F(z)`). -/
theorem meromorphicAt_order_eq_neg_one_of_tendsto {F : ℂ → ℂ} {p R : ℂ} (hR : R ≠ 0)
    (hd : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ F z)
    (h : Tendsto (fun z => (z - p) * F z) (𝓝[≠] p) (𝓝 R)) :
    MeromorphicAt F p ∧ meromorphicOrderAt F p = -1 := by
  classical
  set g : ℂ → ℂ := Function.update (fun z => (z - p) * F z) p R with hg
  have hgc : ContinuousAt g p := continuousAt_update_same.mpr h
  have hgd : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ g z := by
    filter_upwards [hd, self_mem_nhdsWithin] with z hz hzp
    have heq : (fun w => (w - p) * F w) =ᶠ[𝓝 z] g := by
      filter_upwards [isOpen_ne.mem_nhds hzp] with w hw
      simp only [hg, Function.update_of_ne hw]
    exact ((differentiableAt_id.sub_const p).mul hz).congr_of_eventuallyEq heq.symm
  have hga : AnalyticAt ℂ g p :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc
  have hgp : g p = R := by simp only [hg, Function.update_self]
  have hM : MeromorphicAt F p := by
    have hA : AnalyticAt ℂ (fun z => (z - p) * g z) p :=
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - p) p).mul hga
    refine ⟨2, hA.congr (Eventually.of_forall fun z => ?_)⟩
    show (z - p) * g z = (z - p) ^ 2 • F z
    by_cases hz : z = p
    · rw [hz, sub_self, zero_mul, zero_pow two_ne_zero, zero_smul]
    · simp only [hg, Function.update_of_ne hz, smul_eq_mul]; ring
  refine ⟨hM, (meromorphicOrderAt_eq_int_iff hM).mpr ⟨g, hga, by rw [hgp]; exact hR, ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z - p ≠ 0 := sub_ne_zero.mpr hz
  simp only [hg, Function.update_of_ne hz, smul_eq_mul, zpow_neg, zpow_one]
  field_simp

theorem eq_of_abs_eq_of_abs_sub_lt {a b : ℝ} (h : |a| = |b|) (h' : |a - b| < |b|) : a = b := by
  rcases abs_eq_abs.mp h with h | h
  · exact h
  · rw [h, show -b - b = -(2 * b) by ring, abs_neg, abs_mul, abs_two] at h'
    linarith [abs_nonneg b]

/-- Near a prime point every other point is regular for the massless continuation. -/
theorem eventually_regular_near_primePoint {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {q : ℂ}
    (hre : |q.re| = Real.log n) (him : |q.im| = 1) :
    ∀ᶠ v in 𝓝[≠] q, |v.im| < 3 / 2 ∧ v.re ≠ 0 ∧ AvoidsPrimePoints v := by
  have hlog := half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)
  set L := Real.log n with hL
  set N := ⌈Real.exp (L + 1)⌉₊
  have hlogN : ∀ m : ℕ, N < m → L + 1 < Real.log m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hm)
    rw [Real.lt_log_iff_exp_lt hm0]
    exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hm)
  set T : Set ℝ := (fun m : ℕ => Real.log m) '' {m | m ≤ N ∧ chmdPrimeWeight m ≠ 0 ∧ m ≠ n}
  have hTfin : T.Finite := ((Set.finite_Iic N).subset fun m hm => hm.1).image _
  have hLT : L ∉ T := by
    rintro ⟨m, ⟨-, hwm, hmn⟩, hm⟩
    have hm2 := two_le_of_chmdPrimeWeight_ne_zero hwm
    have hn2 := two_le_of_chmdPrimeWeight_ne_zero hw
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < m)))
      (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < n))) hm
    exact hmn (by exact_mod_cast this)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hTfin.isClosed.isOpen_compl L hLT
  set r := min δ (min (1 / 2) (L / 2)) with hr
  have hr0 : 0 < r := lt_min hδ (lt_min (by norm_num) (by linarith))
  have hr1 : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr2 : r ≤ L / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hrδ : r ≤ δ := min_le_left _ _
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds q hr0), self_mem_nhdsWithin]
    with v hv hvq
  have hd : ‖v - q‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hv
  have hdre : |v.re - q.re| < r :=
    lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hd
  have hdim : |v.im - q.im| < r :=
    lt_of_le_of_lt (by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _) hd
  have hvre : |(|v.re|) - L| < r := by
    rw [← hre]; exact lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) hdre
  have hvim : |(|v.im|) - 1| < r := by
    rw [← him]; exact lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) hdim
  refine ⟨by linarith [(abs_lt.mp hvim).2], fun h0 => ?_, fun m hwm => ?_⟩
  · rw [h0, abs_zero] at hvre
    rw [zero_sub, abs_neg, abs_of_pos (by linarith)] at hvre
    linarith
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    by_cases hmn : m = n
    · rw [hmn, ← hL, ← hre] at h1
      rw [← him] at h2
      have e1 := eq_of_abs_eq_of_abs_sub_lt h1 (by rw [hre]; linarith)
      have e2 := eq_of_abs_eq_of_abs_sub_lt h2 (by rw [him]; linarith)
      exact hvq (Complex.ext e1 e2)
    · by_cases hmN : m ≤ N
      · have hmem : Real.log m ∈ ball L δ := by
          rw [Metric.mem_ball, Real.dist_eq, ← h1]; linarith
        exact hball hmem ⟨m, ⟨hmN, hwm, hmn⟩, rfl⟩
      · have := hlogN m (not_le.mp hmN)
        rw [← h1] at this
        linarith [(abs_lt.mp hvre).2]

/-- **The massless continuation has a simple pole at every prime point** `±log n ± i`. -/
theorem masslessBoundaryWave_simple_pole {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {q : ℂ}
    (hre : |q.re| = Real.log n) (him : |q.im| = 1) :
    MeromorphicAt masslessBoundaryWave q ∧ meromorphicOrderAt masslessBoundaryWave q = -1 := by
  obtain ⟨L, hL, hlim⟩ := exists_residue_masslessBoundaryWave hw hre him
  refine meromorphicAt_order_eq_neg_one_of_tendsto hL ?_ hlim
  filter_upwards [eventually_regular_near_primePoint hw hre him] with v hv
  exact (analyticAt_masslessBoundaryWave (Or.inr hv)).differentiableAt

/-! ## Cramér's theorem in Klein–Gordon coordinates -/

/-- **Cramér's theorem in Klein–Gordon coordinates.**  The inverse light-cone transform
`L⁻¹[Φ](z) = Φ(z) + z² ∫_0^1 B(−2z²(1−t²)) Φ(zt) dt` of the Klein–Gordon zero-side wave
`Φ(z) = Σ_ρ m_ρ cos(z√(γ_ρ² + 2)) sech²(γ_ρ/2)` continues from the time strip `|Im z| < 1` to a
function `F` holomorphic at every `v` with `|Im v| < 3/2`, `Re v ≠ 0`, other than the prime points,
and `F` has a simple pole (meromorphic of order `−1`) at each of `±log n ± i` with `Λ(n) ≠ 0`, with
residue `s₂ (2i/π) Λ(n)/√n` at `s₁ log n + s₂ i`. -/
theorem kgZeroWave_inverseLightCone_cramer :
    ∃ F : ℂ → ℂ,
      (∀ z : ℂ, |z.im| < 1 → inverseLightConeTransmuteC kgZeroWave z = F z) ∧
      (∀ v : ℂ, |v.im| < 1 ∨ (|v.im| < 3 / 2 ∧ v.re ≠ 0 ∧ AvoidsPrimePoints v) →
        AnalyticAt ℂ F v) ∧
      (∀ n : ℕ, chmdPrimeWeight n ≠ 0 → ∀ q : ℂ, |q.re| = Real.log n → |q.im| = 1 →
        MeromorphicAt F q ∧ meromorphicOrderAt F q = -1) ∧
      (∀ n : ℕ, chmdPrimeWeight n ≠ 0 →
        Tendsto (fun v => (v - ((Real.log n : ℂ) + I)) * F v)
          (𝓝[≠] ((Real.log n : ℂ) + I)) (𝓝 (2 * I / π * chmdPrimeWeight n)) ∧
        Tendsto (fun v => (v - ((Real.log n : ℂ) - I)) * F v)
          (𝓝[≠] ((Real.log n : ℂ) - I)) (𝓝 (-(2 * I / π * chmdPrimeWeight n))) ∧
        Tendsto (fun v => (v - (-(Real.log n : ℂ) + I)) * F v)
          (𝓝[≠] (-(Real.log n : ℂ) + I)) (𝓝 (2 * I / π * chmdPrimeWeight n)) ∧
        Tendsto (fun v => (v - (-(Real.log n : ℂ) - I)) * F v)
          (𝓝[≠] (-(Real.log n : ℂ) - I)) (𝓝 (-(2 * I / π * chmdPrimeWeight n)))) :=
  ⟨masslessBoundaryWave,
    fun _ hz => (masslessZeroWave_eq_inverseLightConeTransmuteC hz).symm.trans
      (masslessBoundaryWave_of_strip hz).symm,
    fun _ hv => analyticAt_masslessBoundaryWave hv,
    fun _ hw _ hre him => masslessBoundaryWave_simple_pole hw hre him,
    fun _ hw => tendsto_masslessBoundaryWave_residue hw⟩

end RHTower.CHMDLightCone
