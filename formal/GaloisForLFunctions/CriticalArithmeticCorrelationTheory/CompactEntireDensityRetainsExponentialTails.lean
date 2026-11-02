import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireExpandingTaylor

/-!
# Exponential lower tails from compact Fourier support

Cauchy approximation converts exponential type into a Taylor degree proportional to the
observation distance. Remez then forces positive density on a fixed proportion of a distant
interval. Applying this to the entire spectral density avoids any pointwise Fourier-zero
restriction.
-/

noncomputable section

open MeasureTheory Set Polynomial Filter RiemannGaussian
open scoped Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

set_option autoImplicit false

private theorem polynomial_approximation_retains_mass {g : ℝ → ℝ}
    (hg : Continuous g) (hgn : ∀ t, 0 ≤ g t) (P : ℝ[X]) {n : ℕ}
    (hdeg : P.natDegree ≤ n) {c z h : ℝ} (hc : 0 < c) (hz : |z| ≤ c)
    (hh : 0 < h) (hanchor : h ≤ g z)
    (happrox : ∀ t, |t| ≤ 2 * c →
      |P.eval t - g t| ≤ h / (4 * (48 * Real.exp 1) ^ n)) :
    h * c / (16 * (48 * Real.exp 1) ^ n) ≤ ∫ t in Ioo c (2 * c), g t := by
  let q : ℝ := 48 * Real.exp 1
  have hq1 : 1 ≤ q := by
    have he := Real.add_one_le_exp (1 : ℝ)
    dsimp only [q]
    linarith
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hpow : 0 < q ^ n := pow_pos hq _
  have hpow1 : 1 ≤ q ^ n := one_le_pow₀ hq1
  let ε := h / (2 * q ^ n)
  let δ := h / (4 * q ^ n)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδh : δ ≤ h / 4 := by
    dsimp only [δ]
    apply div_le_div_of_nonneg_left hh.le (by norm_num)
    nlinarith only [hpow1]
  have hε : ε * q ^ n < |P.eval z| := by
    have herr := happrox z (hz.trans (by linarith))
    change |P.eval z - g z| ≤ δ at herr
    have hlo := (abs_le.mp herr).1
    have heq : ε * q ^ n = h / 2 := by
      dsimp only [ε]
      field_simp
    rw [heq]
    linarith only [hlo, hδh, hanchor, le_abs_self (P.eval z), hh]
  have hremez := HTGeometry.volume_sublevel_comp_le P hdeg
    (g := fun t : ℝ => t) (a := c) (c := 2 * c) (lam := 1) (b := 3 * c)
    (ε := ε) (q := q) zero_lt_one (by positivity) hq
    (by intros; simp only [one_mul]; exact le_rfl)
    (z := z) (by
      intro t ht
      rw [abs_le] at hz ⊢
      constructor <;> linarith only [hz.1, hz.2, ht.1, ht.2, hc]) hε
  have hbad : (volume {t ∈ Ioo c (2 * c) | |P.eval t| ≤ ε}).toReal ≤ c / 4 := by
    refine hremez.trans_eq ?_
    dsimp only [q]
    field_simp
    ring
  let G := {t ∈ Ioo c (2 * c) | ε < |P.eval t|}
  have hGsub : G ⊆ Ioo c (2 * c) := fun _ ht => ht.1
  have hGmeas : MeasurableSet G :=
    measurableSet_Ioo.inter (measurableSet_lt measurable_const P.continuous.abs.measurable)
  have hcover : Ioo c (2 * c) ⊆ G ∪ {t ∈ Ioo c (2 * c) | |P.eval t| ≤ ε} := by
    intro t ht
    by_cases hp : ε < |P.eval t|
    · exact Or.inl ⟨ht, hp⟩
    · exact Or.inr ⟨ht, le_of_not_gt hp⟩
  have hfinG : volume G ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hGsub)
  have hfinS : volume {t ∈ Ioo c (2 * c) | |P.eval t| ≤ ε} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono fun _ ht => ht.1)
  have hvol := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinG, hfinS⟩)
    ((measure_mono hcover).trans (measure_union_le _ _))
  rw [ENNReal.toReal_add hfinG hfinS, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * c - c)] at hvol
  have hgood : c / 4 ≤ (volume G).toReal := by linarith only [hvol, hbad, hc]
  have hptw : ∀ t ∈ G, δ ≤ g t := by
    intro t ht
    have habs : |t| ≤ 2 * c := by
      rw [abs_of_pos (hc.trans ht.1.1)]
      exact ht.1.2.le
    have herr := happrox t habs
    change |P.eval t - g t| ≤ δ at herr
    have htriangle : |P.eval t| ≤ δ + g t := by
      calc
        _ ≤ |P.eval t - g t| + |g t| := by
          simpa only [sub_add_cancel] using abs_add_le (P.eval t - g t) (g t)
        _ ≤ δ + g t := by rw [abs_of_nonneg (hgn t)]; exact add_le_add herr le_rfl
    have heδ : ε = 2 * δ := by dsimp only [ε, δ]; ring
    have hεt := ht.2
    rw [heδ] at hεt
    linarith only [hεt, htriangle]
  have hint : IntegrableOn g (Ioo c (2 * c)) :=
    hg.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hlow : δ * (volume G).toReal ≤ ∫ t in G, g t := by
    have hs := setIntegral_mono_on (μ := volume) (s := G)
      (integrableOn_const hfinG) (hint.mono_set hGsub) hGmeas hptw
    rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def] at hs
    exact hs
  have hmono : (∫ t in G, g t) ≤ ∫ t in Ioo c (2 * c), g t :=
    setIntegral_mono_set hint (Eventually.of_forall hgn) (Eventually.of_forall hGsub)
  calc
    _ = δ * (c / 4) := by dsimp only [δ, q]; ring
    _ ≤ δ * (volume G).toReal := mul_le_mul_of_nonneg_left hgood hδ
    _ ≤ _ := hlow.trans hmono

private theorem entire_density_taylor_error {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hreal : ∀ t : ℝ, (f (t : ℂ)).im = 0)
    {M B c h : ℝ} (hM : 0 < M) (_hB : 0 ≤ B) (hc : 0 < c)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp (B * ‖z‖)) {n : ℕ}
    (hbudget : 8 * M * Real.exp (B * (4 * (48 * Real.exp 1) * c)) ≤ h * 2 ^ n) :
    ∀ t : ℝ, |t| ≤ 2 * c →
      |(entireRealTaylorPolynomial f n).eval t - (f (t : ℂ)).re| ≤
        h / (4 * (48 * Real.exp 1) ^ n) := by
  let q : ℝ := 48 * Real.exp 1
  let R := 4 * q * c
  have hq1 : 1 ≤ q := by
    have he := Real.add_one_le_exp (1 : ℝ)
    dsimp only [q]
    linarith
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hR : 0 < R := by dsimp only [R]; positivity
  intro t ht
  have htR : ‖(t : ℂ)‖ < R := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    dsimp only [R]
    nlinarith only [ht, hc, hq1]
  have hratio : ‖(t : ℂ)‖ / R ≤ 1 / (2 * q) := by
    rw [Complex.norm_real, Real.norm_eq_abs, div_le_div_iff₀ hR (by positivity)]
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ 2 * q)]
  have hhalf : (1 : ℝ) / (2 * q) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith only [hq1]
  have hden : (1 : ℝ) / 2 ≤ 1 - ‖(t : ℂ)‖ / R := by
    linarith only [hratio.trans hhalf]
  have hcomplex := entire_cauchyPowerSeries_partialSum_remainder_le_of_sphere_bound
    hf (M := M * Real.exp (B * R)) hR
    (fun z hz => by simpa only [hz] using hgrowth z) htR n
  have heval :
      Complex.ofReal ((entireRealTaylorPolynomial f n).eval t) =
        (cauchyPowerSeries f 0 1).partialSum n (t : ℂ) := by
    rw [← entireRealTaylorPolynomial_map_eval hf hreal]
    rw [Polynomial.eval_map]
    exact (Polynomial.eval₂_at_apply Complex.ofRealHom t).symm
  have hrealbound : |(entireRealTaylorPolynomial f n).eval t - (f (t : ℂ)).re| ≤
      ‖(cauchyPowerSeries f 0 1).partialSum n (t : ℂ) - f (t : ℂ)‖ := by
    rw [← heval]
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (Complex.ofReal ((entireRealTaylorPolynomial f n).eval t) - f (t : ℂ))
  have hnum : 0 ≤ M * Real.exp (B * R) * (‖(t : ℂ)‖ / R) ^ n := by positivity
  have hscalar : 2 * (M * Real.exp (B * R)) / (2 : ℝ) ^ n ≤ h / 4 := by
    rw [div_le_iff₀ (by positivity)]
    change 8 * M * Real.exp (B * R) ≤ h * 2 ^ n at hbudget
    nlinarith only [hbudget]
  calc
    _ ≤ _ := hrealbound.trans hcomplex
    _ ≤ (M * Real.exp (B * R) * (‖(t : ℂ)‖ / R) ^ n) / (1 / 2) :=
      div_le_div_of_nonneg_left hnum (by norm_num) hden
    _ ≤ (M * Real.exp (B * R) * (1 / (2 * q)) ^ n) / (1 / 2) := by
      gcongr
    _ = (2 * (M * Real.exp (B * R)) / (2 : ℝ) ^ n) / q ^ n := by
      rw [div_pow, one_pow, mul_pow]
      ring
    _ ≤ (h / 4) / q ^ n := div_le_div_of_nonneg_right hscalar (pow_pos hq _).le
    _ = _ := by dsimp only [q]; ring

private theorem entire_density_interval_mass {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hreal : ∀ t : ℝ, (f (t : ℂ)).im = 0)
    (hpos : ∀ t : ℝ, 0 ≤ (f (t : ℂ)).re) {M B c z h : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hc : 0 < c) (hz : |z| ≤ c)
    (hh : 0 < h) (hanchor : h ≤ (f (z : ℂ)).re)
    (hgrowth : ∀ w : ℂ, ‖f w‖ ≤ M * Real.exp (B * ‖w‖)) {n : ℕ}
    (hbudget : 8 * M * Real.exp (B * (4 * (48 * Real.exp 1) * c)) ≤ h * 2 ^ n) :
    h * c / (16 * (48 * Real.exp 1) ^ n) ≤
      ∫ t in Ioo c (2 * c), (f (t : ℂ)).re := by
  have hfc : Continuous f := hf.continuous
  apply polynomial_approximation_retains_mass
    (by fun_prop) hpos
    (entireRealTaylorPolynomial f n) (entireRealTaylorPolynomial_natDegree_le f n)
    hc hz hh hanchor
  exact entire_density_taylor_error hf hreal hM hB hc hgrowth hbudget

private theorem exponential_density_degree_choice {M B h c : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hh : 0 < h) (hc : 0 < c)
    (hlog : Real.log (8 * M / h) ≤ c) :
    let q : ℝ := 48 * Real.exp 1
    let D : ℝ := (4 * q * B + 1) / Real.log 2
    let n : ℕ := ⌈D * c⌉₊
    8 * M * Real.exp (B * (4 * q * c)) ≤ h * 2 ^ n ∧
      q ^ n ≤ q * Real.exp ((D * Real.log q) * c) := by
  let q : ℝ := 48 * Real.exp 1
  let D : ℝ := (4 * q * B + 1) / Real.log 2
  let n : ℕ := ⌈D * c⌉₊
  have hq1 : 1 < q := by
    have he := Real.add_one_le_exp (1 : ℝ)
    dsimp only [q]
    linarith
  have hq : 0 < q := zero_lt_one.trans hq1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hnlo : D * c ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) ≤ D * c + 1 := (Nat.ceil_lt_add_one (mul_pos hD hc).le).le
  have hpow : Real.exp ((4 * q * B + 1) * c) ≤ (2 : ℝ) ^ n := by
    calc
      _ = Real.exp ((D * c) * Real.log 2) := by
        congr 1
        dsimp only [D]
        field_simp
      _ ≤ Real.exp ((n : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnlo hlog2.le)
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hfactor : 8 * M ≤ h * Real.exp c := by
    have he : 8 * M / h ≤ Real.exp c := by
      calc
        _ = Real.exp (Real.log (8 * M / h)) := (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlog
    have hm := (div_le_iff₀ hh).mp he
    simpa only [mul_comm h] using hm
  constructor
  · calc
      8 * M * Real.exp (B * (4 * q * c)) ≤
          (h * Real.exp c) * Real.exp (B * (4 * q * c)) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ = h * Real.exp ((4 * q * B + 1) * c) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hh.le
  · calc
      q ^ n = Real.exp ((n : ℝ) * Real.log q) := by
        rw [Real.exp_nat_mul, Real.exp_log hq]
      _ ≤ Real.exp ((D * c + 1) * Real.log q) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnhi (Real.log_pos hq1).le)
      _ = Real.exp (Real.log q + (D * Real.log q) * c) := by congr 1; ring
      _ = _ := by rw [Real.exp_add, Real.exp_log hq]

/-- A nonzero, nonnegative entire density of fixed exponential type has an exponential
integrated lower tail. The rate depends only on its exponential type. -/
theorem exists_exponential_lower_tail_of_entire_nonnegative {B : ℝ} (hB : 0 ≤ B) :
    ∃ b : ℝ, 0 < b ∧ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ t : ℝ, (f (t : ℂ)).im = 0) → (∀ t : ℝ, 0 ≤ (f (t : ℂ)).re) →
      (∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp (B * ‖z‖)) →
      (∃ z : ℝ, 0 < (f (z : ℂ)).re) →
      (∀ c : ℝ, IntegrableOn (fun t : ℝ => (f (t : ℂ)).re) (Ioi c)) →
      ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 ≤ c →
        a * Real.exp (-b * c) ≤ ∫ t in Ioi c, (f (t : ℂ)).re := by
  let q : ℝ := 48 * Real.exp 1
  let D : ℝ := (4 * q * B + 1) / Real.log 2
  let b := D * Real.log q
  have hq1 : 1 < q := by
    have he := Real.add_one_le_exp (1 : ℝ)
    dsimp only [q]
    linarith
  have hq : 0 < q := zero_lt_one.trans hq1
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos (by positivity) (Real.log_pos (by norm_num))
  have hb : 0 < b := mul_pos hD (Real.log_pos hq1)
  refine ⟨b, hb, ?_⟩
  intro f hf hreal hpos hbound hwitness hint
  obtain ⟨M, hM, hgrowth⟩ := hbound
  obtain ⟨z, hzpos⟩ := hwitness
  let h := (f (z : ℂ)).re
  have hh : 0 < h := hzpos
  let C := max 1 (max |z| (Real.log (8 * M / h)))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCz : |z| ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hClog : Real.log (8 * M / h) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  let a₀ := h / (16 * q)
  have ha₀ : 0 < a₀ := by dsimp only [a₀]; positivity
  have hlarge (c : ℝ) (hcC : C ≤ c) :
      a₀ * Real.exp (-b * c) ≤ ∫ t in Ioi c, (f (t : ℂ)).re := by
    have hc1 : 1 ≤ c := hC1.trans hcC
    have hc : 0 < c := zero_lt_one.trans_le hc1
    let n : ℕ := ⌈D * c⌉₊
    obtain ⟨hbudget, hdegree⟩ := exponential_density_degree_choice hM hB hh hc (hClog.trans hcC)
    change 8 * M * Real.exp (B * (4 * q * c)) ≤ h * 2 ^ n at hbudget
    change q ^ n ≤ q * Real.exp (b * c) at hdegree
    have hmass := entire_density_interval_mass hf hreal hpos hM hB hc
      (hCz.trans hcC) hh (le_refl h) hgrowth hbudget
    have hmono : (∫ t in Ioo c (2 * c), (f (t : ℂ)).re) ≤
        ∫ t in Ioi c, (f (t : ℂ)).re :=
      setIntegral_mono_set (hint c) (Eventually.of_forall hpos)
        (Eventually.of_forall fun _ ht => ht.1)
    calc
      a₀ * Real.exp (-b * c) = h / (16 * (q * Real.exp (b * c))) := by
        dsimp only [a₀]
        rw [show -b * c = -(b * c) by ring, Real.exp_neg]
        ring
      _ ≤ h / (16 * q ^ n) := div_le_div_of_nonneg_left hh.le (by positivity)
        (mul_le_mul_of_nonneg_left hdegree (by norm_num))
      _ ≤ h * c / (16 * q ^ n) := div_le_div_of_nonneg_right
        (le_mul_of_one_le_right hh.le hc1) (by positivity)
      _ ≤ _ := hmass.trans hmono
  let a := a₀ * Real.exp (-b * C)
  have ha : 0 < a := mul_pos ha₀ (Real.exp_pos _)
  have hexp (c : ℝ) (hc : 0 ≤ c) : Real.exp (-b * c) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) hc)
      _ = 1 := Real.exp_zero
  have haa₀ : a ≤ a₀ := by
    calc
      a ≤ a₀ * 1 := mul_le_mul_of_nonneg_left (hexp C (zero_le_one.trans hC1)) ha₀.le
      _ = _ := mul_one _
  refine ⟨a, ha, ?_⟩
  intro c hc
  by_cases hCc : C ≤ c
  · exact (mul_le_mul_of_nonneg_right haa₀ (Real.exp_pos _).le).trans (hlarge c hCc)
  · have hcC : c ≤ C := (lt_of_not_ge hCc).le
    calc
      a * Real.exp (-b * c) ≤ a * 1 := mul_le_mul_of_nonneg_left (hexp c hc) ha.le
      _ = a₀ * Real.exp (-b * C) := mul_one _
      _ ≤ ∫ t in Ioi C, (f (t : ℂ)).re := hlarge C le_rfl
      _ ≤ _ := setIntegral_mono_set (hint c) (Eventually.of_forall hpos)
        (Eventually.of_forall (Ioi_subset_Ioi hcC))

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
