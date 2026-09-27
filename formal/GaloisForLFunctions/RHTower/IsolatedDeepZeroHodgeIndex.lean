import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# An isolated deep zero violates the level-`a` Hodge index

The level-`a` Hodge index of a zero configuration is Weil positivity on the polar-constrained
tests: `C²` functions supported in `[-a, a]` with `h_f(i/2) = h_f(-i/2) = 0`
(`HodgeIndexAtLevel`).  Here the deep-zero test `e^{-iγ₀u} sinh(δu)(a² - u²)₊^{5/2}` of
`IsolatedDeepZeroWeilDetection` is moved into this subspace, and its Weil form stays negative.

* **Polar correction.**  Add `c₁ψ + c₂φ` with `ψ = (a² - u²)₊^{5/2}` even and
  `φ = sinh(u/2)ψ` odd.  Their polar values are `(α, α)` and `(-β, β)`, with
  `α = ∫ ψ cosh(u/2) ≥ a(3a²/4)^{5/2}` and `β = ∫ φ sinh(u/2) > 0`, so
  `c₁ = -(H₊ + H₋)/(2α)`, `c₂ = (H₊ - H₋)/(2β)` cancel the polar values `H_±` of the deep-zero
  test.
* **Size of the correction.**  At height `γ₀` the polar values are
  `|H_±| ≤ e^{a/2}·4N/(1 + |γ₀|)²`, so the corrected norm is `G ≤ N·ε` with
  `ε = polarCorrectionBound a γ₀ = O(e^{a/2}/(1 + |γ₀|)²)`.
* **Cost.**  Expanding the Weil summand and summing over unit windows costs at most
  `768 e^a A₀ log(|γ₀| + 3)(NG + G²)`.

Hence the level-`a` Hodge index forces every sufficiently deep zero to have another off-line
zero within ordinate distance `R`, provided `|γ₀|` is large compared with `e^{3a/4}`.  This is
stated for `ζ` with the unconditional local zero count.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Even tests and the weight `(a² - u²)₊^{5/2}` -/

theorem integral_even_mul_sinh {s : ℝ → ℝ} (heven : ∀ u, s (-u) = s u) (δ : ℝ) :
    ∫ u, s u * Real.sinh (δ * u) = 0 := by
  have h := integral_neg_eq_self (fun u => s u * Real.sinh (δ * u)) volume
  simp only [heven, mul_neg, Real.sinh_neg] at h
  rw [integral_neg] at h
  linarith

theorem integral_even_mul_exp {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (heven : ∀ u, s (-u) = s u) (δ : ℝ) :
    ∫ u, s u * Real.exp (δ * u) = ∫ u, s u * Real.cosh (δ * u) := by
  have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hsupp
  have hi1 : Integrable (fun u => s u * Real.cosh (δ * u)) :=
    (hs.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have hi2 : Integrable (fun u => s u * Real.sinh (δ * u)) :=
    (hs.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have h : (fun u => s u * Real.exp (δ * u)) =
      fun u => s u * Real.cosh (δ * u) + s u * Real.sinh (δ * u) := by
    funext u; rw [← mul_add, Real.cosh_add_sinh]
  rw [h, integral_add hi1 hi2, integral_even_mul_sinh heven, add_zero]

theorem integral_even_mul_exp_neg {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (heven : ∀ u, s (-u) = s u) (δ : ℝ) :
    ∫ u, s u * Real.exp (-(δ * u)) = ∫ u, s u * Real.cosh (δ * u) := by
  have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hsupp
  have hi1 : Integrable (fun u => s u * Real.cosh (δ * u)) :=
    (hs.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have hi2 : Integrable (fun u => s u * Real.sinh (δ * u)) :=
    (hs.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have h : (fun u => s u * Real.exp (-(δ * u))) =
      fun u => s u * Real.cosh (δ * u) - s u * Real.sinh (δ * u) := by
    funext u; rw [← mul_sub, Real.cosh_sub_sinh]
  rw [h, integral_sub hi1 hi2, integral_even_mul_sinh heven, sub_zero]

/-- The transform of an even real test at `∓iδ` is `∫ s(u) cosh(δu)`. -/
theorem paperFT_even_neg_I_mul {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (heven : ∀ u, s (-u) = s u) (δ : ℝ) :
    paperFT (fun u => (s u : ℂ)) (-(I * δ)) = ((∫ u, s u * Real.cosh (δ * u) : ℝ) : ℂ) := by
  rw [paperFT_def, ← integral_even_mul_exp hs hsupp heven δ, ← integral_complex_ofReal]
  congr 1 with u
  have hI : I * I = -1 := Complex.I_mul_I
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  linear_combination (-(δ : ℂ) * u) * hI

theorem paperFT_even_I_mul {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (heven : ∀ u, s (-u) = s u) (δ : ℝ) :
    paperFT (fun u => (s u : ℂ)) (I * δ) = ((∫ u, s u * Real.cosh (δ * u) : ℝ) : ℂ) := by
  rw [paperFT_def, ← integral_even_mul_exp_neg hs hsupp heven δ, ← integral_complex_ofReal]
  congr 1 with u
  have hI : I * I = -1 := Complex.I_mul_I
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  linear_combination ((δ : ℂ) * u) * hI

theorem sinhTestWeight_contDiff (a : ℝ) : ContDiff ℝ 2 (sinhTestWeight a) := by
  have h52 : ContDiff ℝ 2 (fun x : ℝ => x ^ (5 / 2 : ℝ)) := by
    have := Real.contDiff_rpow_const_of_le (n := 2) (p := 5 / 2) (by norm_num)
    exact_mod_cast this
  exact h52.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem sinhTestWeight_even (a u : ℝ) : sinhTestWeight a (-u) = sinhTestWeight a u := by
  simp only [sinhTestWeight, neg_sq]

theorem sinhTestWeight_eq_zero {a u : ℝ} (ha : 0 ≤ a) (hu : a < |u|) : sinhTestWeight a u = 0 := by
  have h : a ^ 2 - u ^ 2 < 0 := by nlinarith [abs_nonneg u, sq_abs u]
  rw [sinhTestWeight, rpow_five_halves_of_neg h]

theorem sinhTestWeight_supp {a : ℝ} (ha : 0 ≤ a) : ∀ u, sinhTestWeight a u ≠ 0 → |u| ≤ a := by
  intro u hu
  by_contra h
  exact hu (sinhTestWeight_eq_zero ha (lt_of_not_ge h))

/-- The second derivative of the weight. -/
def sinhTestWeightDeriv2 (a u : ℝ) : ℝ :=
  -5 * (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) + 15 * u ^ 2 * (a ^ 2 - u ^ 2) ^ (1 / 2 : ℝ)

theorem deriv_sinhTestWeight (a : ℝ) :
    deriv (sinhTestWeight a) = fun u => -(2 * u) * (5 / 2) * (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) := by
  funext u
  have hw := hasDerivAt_sub_sq_rpow a (5 / 2) (by norm_num) u
  rw [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at hw
  exact hw.deriv

theorem hasDerivAt_deriv_sinhTestWeight (a u : ℝ) :
    HasDerivAt (deriv (sinhTestWeight a)) (sinhTestWeightDeriv2 a u) u := by
  rw [deriv_sinhTestWeight]
  have h3 := hasDerivAt_sub_sq_rpow a (3 / 2) (by norm_num) u
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at h3
  have hq : HasDerivAt (fun u : ℝ => -(2 * u) * (5 / 2)) (-(2 * 1) * (5 / 2)) u :=
    (((hasDerivAt_id u).const_mul 2).neg).mul_const (5 / 2 : ℝ)
  refine (hq.mul h3).congr_deriv ?_
  simp only [sinhTestWeightDeriv2]
  ring

theorem deriv_deriv_ofReal_sinhTestWeight (a : ℝ) :
    deriv (deriv (fun u => (sinhTestWeight a u : ℂ))) =
      fun u => ((sinhTestWeightDeriv2 a u : ℝ) : ℂ) := by
  have hd1 : ∀ u, HasDerivAt (sinhTestWeight a) (deriv (sinhTestWeight a) u) u := fun u =>
    ((sinhTestWeight_contDiff a).differentiable (by norm_num) u).hasDerivAt
  have h1 : deriv (fun u => (sinhTestWeight a u : ℂ)) =
      fun u => ((deriv (sinhTestWeight a) u : ℝ) : ℂ) :=
    funext fun u => ((hd1 u).ofReal_comp).deriv
  rw [h1]
  funext u
  exact ((hasDerivAt_deriv_sinhTestWeight a u).ofReal_comp).deriv

theorem abs_sinhTestWeight_le {a u : ℝ} (ha : 0 ≤ a) (hu : |u| ≤ a) :
    |sinhTestWeight a u| ≤ a ^ 5 := by
  obtain ⟨hψ0, hψ⟩ := rpow_sub_sq_le ha hu (show (0 : ℝ) ≤ 5 / 2 by norm_num)
  rw [show (2 * (5 / 2) : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hψ
  rw [abs_of_nonneg (sinhTestWeight_nonneg a u)]
  exact hψ

theorem abs_sinhTestWeightDeriv2_le {a u : ℝ} (ha : 0 ≤ a) (hu : |u| ≤ a) :
    |sinhTestWeightDeriv2 a u| ≤ 20 * a ^ 3 := by
  obtain ⟨p3a, p3b⟩ := rpow_sub_sq_le ha hu (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  obtain ⟨p1a, p1b⟩ := rpow_sub_sq_le ha hu (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [show (2 * (3 / 2) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at p3b
  rw [show (2 * (1 / 2) : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_one] at p1b
  have hu2 : u ^ 2 ≤ a ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  unfold sinhTestWeightDeriv2
  set p3 := (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ)
  set p1 := (a ^ 2 - u ^ 2) ^ (1 / 2 : ℝ)
  have h2 : |-5 * p3 + 15 * u ^ 2 * p1| ≤ 5 * p3 + 15 * u ^ 2 * p1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg u]
  have h3 : u ^ 2 * p1 ≤ a ^ 2 * a := mul_le_mul hu2 p1b p1a (sq_nonneg a)
  nlinarith

theorem sinhTestWeightDeriv2_eq_zero {a u : ℝ} (ha : 0 ≤ a) (hu : a < |u|) :
    sinhTestWeightDeriv2 a u = 0 := by
  have hopen : IsOpen {v : ℝ | a < |v|} := isOpen_lt continuous_const continuous_abs
  have hev : sinhTestWeight a =ᶠ[nhds u] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hu) fun v hv => sinhTestWeight_eq_zero ha hv
  rw [← (hasDerivAt_deriv_sinhTestWeight a u).deriv, hev.deriv.deriv_eq]
  simp

theorem testNorm_sinhTestWeight_le {a : ℝ} (ha : 0 ≤ a) :
    testNorm (sinhTestWeight a) ≤ 2 * a * (a ^ 5 + 20 * a ^ 3) := by
  unfold testNorm
  rw [deriv_deriv_ofReal_sinhTestWeight]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have h1 : ∫ u, |sinhTestWeight a u| ≤ 2 * a * a ^ 5 :=
    integral_le_of_bound_on_Icc ha (fun _ => abs_nonneg _)
      (fun u hu => abs_sinhTestWeight_le ha hu)
      (fun u hu => by rw [sinhTestWeight_eq_zero ha hu, abs_zero])
  have h2 : ∫ u, |sinhTestWeightDeriv2 a u| ≤ 2 * a * (20 * a ^ 3) :=
    integral_le_of_bound_on_Icc ha (fun _ => abs_nonneg _)
      (fun u hu => abs_sinhTestWeightDeriv2_le ha hu)
      (fun u hu => by rw [sinhTestWeightDeriv2_eq_zero ha hu, abs_zero])
  linarith

/-- `∫ (a² - u²)₊^{5/2} cosh(u/2) ≥ a (3a²/4)^{5/2}`. -/
theorem sinhTestWeight_cosh_energy_ge {a : ℝ} (ha : 0 < a) :
    a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ) ≤ ∫ u, sinhTestWeight a u * Real.cosh (1 / 2 * u) := by
  set c := (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ) with hc
  have hg0 : ∀ u, 0 ≤ sinhTestWeight a u * Real.cosh (1 / 2 * u) := fun u =>
    mul_nonneg (sinhTestWeight_nonneg a u) (Real.cosh_pos _).le
  have hcont : Continuous (fun u => sinhTestWeight a u * Real.cosh (1 / 2 * u)) :=
    (sinhTestWeight_contDiff a).continuous.mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hint : Integrable (fun u => sinhTestWeight a u * Real.cosh (1 / 2 * u)) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp ha.le)).mul_right
  have hsub : ∫ u in Icc (-(a / 2)) (a / 2), c ≤
      ∫ u in Icc (-(a / 2)) (a / 2), sinhTestWeight a u * Real.cosh (1 / 2 * u) := by
    refine setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne (by simp))
      hcont.integrableOn_Icc measurableSet_Icc fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := hu
    have hp : 3 * a ^ 2 / 4 ≤ a ^ 2 - u ^ 2 := by nlinarith
    have hψ : c ≤ sinhTestWeight a u :=
      Real.rpow_le_rpow (by positivity) hp (by norm_num)
    calc c = c * 1 := (mul_one c).symm
      _ ≤ sinhTestWeight a u * Real.cosh (1 / 2 * u) :=
          mul_le_mul hψ (Real.one_le_cosh _) zero_le_one (sinhTestWeight_nonneg a u)
  have hle : ∫ u in Icc (-(a / 2)) (a / 2), sinhTestWeight a u * Real.cosh (1 / 2 * u) ≤
      ∫ u, sinhTestWeight a u * Real.cosh (1 / 2 * u) :=
    setIntegral_le_integral hint (Eventually.of_forall hg0)
  rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
    max_eq_left (by linarith)] at hsub
  have : a / 2 - -(a / 2) = a := by ring
  rw [this] at hsub
  exact hsub.trans hle

/-! ### The polar-corrected test -/

theorem integrable_mul_cexp {c : ℝ → ℂ} (hc : Continuous c) (hcs : HasCompactSupport c) (z : ℂ) :
    Integrable (fun u : ℝ => c u * cexp (I * z * u)) :=
  (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right

/-- The test `e^{-iγ₀u}s(u) + c₁φ₁(u) + c₂φ₂(u)`. -/
def polarCorrectedTest (γ₀ : ℝ) (s φ₁ φ₂ : ℝ → ℝ) (c₁ c₂ : ℂ) : ℝ → ℂ :=
  fun u => modulatedTest γ₀ s u + c₁ * (φ₁ u : ℂ) + c₂ * (φ₂ u : ℂ)

theorem continuous_modulatedTest (γ₀ : ℝ) {s : ℝ → ℝ} (hs : Continuous s) :
    Continuous (modulatedTest γ₀ s) := by
  unfold modulatedTest
  fun_prop

theorem hasCompactSupport_modulatedTest (γ₀ : ℝ) {s : ℝ → ℝ} {a : ℝ}
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) : HasCompactSupport (modulatedTest γ₀ s) :=
  hasCompactSupport_of_support_subset_abs fun u hu =>
    hsupp u fun h => hu (by simp [modulatedTest, h])

theorem hasCompactSupport_ofReal_of_abs {φ : ℝ → ℝ} {a : ℝ} (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) :
    HasCompactSupport (fun u => (φ u : ℂ)) :=
  hasCompactSupport_of_support_subset_abs fun u hu => hsupp u fun h => hu (by simp [h])

theorem paperFT_polarCorrectedTest {γ₀ a : ℝ} {s φ₁ φ₂ : ℝ → ℝ} (hs : Continuous s)
    (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hss : ∀ u, s u ≠ 0 → |u| ≤ a)
    (h1s : ∀ u, φ₁ u ≠ 0 → |u| ≤ a) (h2s : ∀ u, φ₂ u ≠ 0 → |u| ≤ a) (c₁ c₂ z : ℂ) :
    paperFT (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂) z =
      paperFT (modulatedTest γ₀ s) z + c₁ * paperFT (fun u => (φ₁ u : ℂ)) z +
        c₂ * paperFT (fun u => (φ₂ u : ℂ)) z := by
  have iA : Integrable (fun u : ℝ => modulatedTest γ₀ s u * cexp (I * z * u)) :=
    integrable_mul_cexp (continuous_modulatedTest γ₀ hs) (hasCompactSupport_modulatedTest γ₀ hss) z
  have iB : Integrable (fun u : ℝ => c₁ * ((φ₁ u : ℂ) * cexp (I * z * u))) :=
    (integrable_mul_cexp (Complex.continuous_ofReal.comp hφ₁)
      (hasCompactSupport_ofReal_of_abs h1s) z).const_mul c₁
  have iC : Integrable (fun u : ℝ => c₂ * ((φ₂ u : ℂ) * cexp (I * z * u))) :=
    (integrable_mul_cexp (Complex.continuous_ofReal.comp hφ₂)
      (hasCompactSupport_ofReal_of_abs h2s) z).const_mul c₂
  have iAB : Integrable (fun u : ℝ => modulatedTest γ₀ s u * cexp (I * z * u) +
      c₁ * ((φ₁ u : ℂ) * cexp (I * z * u))) := iA.add iB
  have h : (fun u => polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u * cexp (I * z * u)) =
      fun u => (modulatedTest γ₀ s u * cexp (I * z * u) +
        c₁ * ((φ₁ u : ℂ) * cexp (I * z * u))) + c₂ * ((φ₂ u : ℂ) * cexp (I * z * u)) := by
    funext u; simp only [polarCorrectedTest]; ring
  simp only [paperFT_def]
  rw [h, integral_add iAB iC, integral_add iA iB, integral_const_mul, integral_const_mul]

/-- Pure algebra of the polar correction: the change of `m A conj A'` when `A, A'` are moved by
`B, B'`. -/
theorem norm_polar_expansion_le {A A' B B' : ℂ} {m E N G D₀ D ea : ℝ} (hm : 0 ≤ m)
    (hN : 0 ≤ N) (hG : 0 ≤ G) (hE : 0 ≤ E) (hE2 : E ^ 2 ≤ ea) (hD₀ : 1 ≤ D₀) (hD : 1 ≤ D)
    (hA : ‖A‖ ≤ E * (4 * N) / D₀ ^ 2) (hA' : ‖A'‖ ≤ E * (4 * N) / D₀ ^ 2)
    (hB : ‖B‖ ≤ E * (4 * G) / D ^ 2) (hB' : ‖B'‖ ≤ E * (4 * G) / D ^ 2) :
    m * ‖A * conj B' + B * conj A' + B * conj B'‖ ≤
      16 * ea * (N * G + G ^ 2) * (m / D₀ ^ 3 + m / D ^ 3) := by
  have hsum : ‖A * conj B' + B * conj A' + B * conj B'‖ ≤
      ‖A‖ * ‖B'‖ + ‖B‖ * ‖A'‖ + ‖B‖ * ‖B'‖ := by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans ?_) ?_
    · rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    · rw [norm_mul, Complex.norm_conj]
  have hD₀0 : 0 < D₀ := by linarith
  have hD0 : 0 < D := by linarith
  set p := 1 / D₀ ^ 2 with hp
  set q := 1 / D ^ 2 with hq
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; nlinarith
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by positivity)]; nlinarith
  have hp3 : p ^ 2 ≤ 1 / D₀ ^ 3 := by
    rw [hp, div_pow, one_pow, ← pow_mul]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hD₀ (by norm_num))
  have hq3 : q ^ 2 ≤ 1 / D ^ 3 := by
    rw [hq, div_pow, one_pow, ← pow_mul]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hD (by norm_num))
  have hA2 : ‖A‖ ≤ 4 * E * N * p := by rw [hp]; convert hA using 1; ring
  have hA'2 : ‖A'‖ ≤ 4 * E * N * p := by rw [hp]; convert hA' using 1; ring
  have hB2 : ‖B‖ ≤ 4 * E * G * q := by rw [hq]; convert hB using 1; ring
  have hB'2 : ‖B'‖ ≤ 4 * E * G * q := by rw [hq]; convert hB' using 1; ring
  have hbd : ‖A‖ * ‖B'‖ + ‖B‖ * ‖A'‖ + ‖B‖ * ‖B'‖ ≤
      (4 * E * N * p) * (4 * E * G * q) + (4 * E * G * q) * (4 * E * N * p) +
        (4 * E * G * q) * (4 * E * G * q) := by
    gcongr
  have hamgm : 2 * (p * q) ≤ p ^ 2 + q ^ 2 := by nlinarith [sq_nonneg (p - q)]
  have hkey : (4 * E * N * p) * (4 * E * G * q) + (4 * E * G * q) * (4 * E * N * p) +
      (4 * E * G * q) * (4 * E * G * q) = E ^ 2 * (16 * (N * G) * (2 * (p * q)) + 16 * G ^ 2 * q ^ 2) := by
    ring
  have hin : 16 * (N * G) * (2 * (p * q)) + 16 * G ^ 2 * q ^ 2 ≤
      16 * (N * G + G ^ 2) * (1 / D₀ ^ 3 + 1 / D ^ 3) := by
    have hNG : 0 ≤ N * G := mul_nonneg hN hG
    have h1 : 2 * (p * q) ≤ 1 / D₀ ^ 3 + 1 / D ^ 3 := by linarith
    have h2 : q ^ 2 ≤ 1 / D₀ ^ 3 + 1 / D ^ 3 := by
      have : 0 ≤ 1 / D₀ ^ 3 := by positivity
      linarith
    have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
    nlinarith [mul_le_mul_of_nonneg_left h1 hNG, mul_le_mul_of_nonneg_left h2 hG2]
  have hin0 : 0 ≤ 16 * (N * G) * (2 * (p * q)) + 16 * G ^ 2 * q ^ 2 := by positivity
  have hfin : E ^ 2 * (16 * (N * G) * (2 * (p * q)) + 16 * G ^ 2 * q ^ 2) ≤
      ea * (16 * (N * G + G ^ 2) * (1 / D₀ ^ 3 + 1 / D ^ 3)) :=
    mul_le_mul hE2 hin hin0 ((sq_nonneg E).trans hE2)
  calc m * ‖A * conj B' + B * conj A' + B * conj B'‖
      ≤ m * (ea * (16 * (N * G + G ^ 2) * (1 / D₀ ^ 3 + 1 / D ^ 3))) := by
        gcongr
        exact hsum.trans (hbd.trans (hkey ▸ hfin))
    _ = 16 * ea * (N * G + G ^ 2) * (m / D₀ ^ 3 + m / D ^ 3) := by ring

theorem Wsummand_sub_eq_of_paperFT (Z : ZeroConfig) {F f₀ : ℝ → ℂ} {ρ : ℂ} {A A' B B' : ℂ}
    (hF : paperFT F (gammaOf ρ) = A + B) (hF' : paperFT F (conj (gammaOf ρ)) = A' + B')
    (hf : paperFT f₀ (gammaOf ρ) = A) (hf' : paperFT f₀ (conj (gammaOf ρ)) = A') :
    Z.Wsummand F F ρ - Z.Wsummand f₀ f₀ ρ = (Z.mult ρ : ℂ) * (A * conj B' + B * conj A' + B * conj B') := by
  rw [ZeroConfig.Wsummand, ZeroConfig.Wsummand, hF, hF', hf, hf', map_add]
  ring

/-- The change of the Weil summand under the polar correction. -/
theorem norm_Wsummand_polarCorrected_sub_le (Z : ZeroConfig) (γ₀ : ℝ) {a : ℝ} (ha : 0 ≤ a)
    {s φ₁ φ₂ : ℝ → ℝ} (hs : ContDiff ℝ 2 s) (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂)
    (hss : ∀ u, s u ≠ 0 → |u| ≤ a) (h1s : ∀ u, φ₁ u ≠ 0 → |u| ≤ a)
    (h2s : ∀ u, φ₂ u ≠ 0 → |u| ≤ a) (c₁ c₂ : ℂ) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    ‖Z.Wsummand (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂) (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂) ρ -
        Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ‖ ≤
      16 * Real.exp a * (testNorm s * (‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂) +
          (‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂) ^ 2) *
        ((Z.mult ρ : ℝ) / (1 + |ρ.im - γ₀|) ^ 3 + (Z.mult ρ : ℝ) / (1 + |ρ.im - 0|) ^ 3) := by
  have hN0 := testNorm_nonneg s
  have hG0 : 0 ≤ ‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂ := by
    have := testNorm_nonneg φ₁; have := testNorm_nonneg φ₂; positivity
  have hE2 := exp_abs_half_sub_sq_le (Z.strip ρ hρ) ha
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hxre : (gammaOf ρ).re = ρ.im := WeilEF.gammaOf_re ρ
  have hxim : (gammaOf ρ).im = 1 / 2 - ρ.re := WeilEF.gammaOf_im ρ
  have hS : ContDiff ℝ 2 (fun u => (s u : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  have hSs : ∀ u, (fun u => (s u : ℂ)) u ≠ 0 → |u| ≤ a := fun u hu =>
    hss u (fun h => hu (by simp [h]))
  have hΦ₁ : ContDiff ℝ 2 (fun u => (φ₁ u : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ₁
  have hΦ₁s : ∀ u, (fun u => (φ₁ u : ℂ)) u ≠ 0 → |u| ≤ a := fun u hu =>
    h1s u (fun h => hu (by simp [h]))
  have hΦ₂ : ContDiff ℝ 2 (fun u => (φ₂ u : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ₂
  have hΦ₂s : ∀ u, (fun u => (φ₂ u : ℂ)) u ≠ 0 → |u| ≤ a := fun u hu =>
    h2s u (fun h => hu (by simp [h]))
  have hA : ∀ y : ℂ, y.re = ρ.im → |y.im| = |1 / 2 - ρ.re| →
      ‖paperFT (modulatedTest γ₀ s) y‖ ≤
        Real.exp (|1 / 2 - ρ.re| * a) * (4 * testNorm s) / (1 + |ρ.im - γ₀|) ^ 2 := by
    intro y hyre hyim
    have := norm_paperFT_le_decay hS hSs (y - γ₀)
    unfold modulatedTest
    rw [paperFT_modulate]
    have e1 : (y - (γ₀ : ℂ)).re = ρ.im - γ₀ := by simp [hyre]
    have e2 : |(y - (γ₀ : ℂ)).im| = |1 / 2 - ρ.re| := by simp [hyim]
    rw [e1, e2] at this
    exact this
  have hB : ∀ y : ℂ, y.re = ρ.im → |y.im| = |1 / 2 - ρ.re| →
      ‖c₁ * paperFT (fun u => (φ₁ u : ℂ)) y + c₂ * paperFT (fun u => (φ₂ u : ℂ)) y‖ ≤
        Real.exp (|1 / 2 - ρ.re| * a) * (4 * (‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂)) /
          (1 + |ρ.im - 0|) ^ 2 := by
    intro y hyre hyim
    have h1 := norm_paperFT_le_decay hΦ₁ hΦ₁s y
    have h2 := norm_paperFT_le_decay hΦ₂ hΦ₂s y
    rw [hyre, hyim, ← sub_zero ρ.im] at h1 h2
    change _ ≤ Real.exp _ * (4 * testNorm φ₁) / _ at h1
    change _ ≤ Real.exp _ * (4 * testNorm φ₂) / _ at h2
    calc ‖c₁ * paperFT (fun u => (φ₁ u : ℂ)) y + c₂ * paperFT (fun u => (φ₂ u : ℂ)) y‖
        ≤ ‖c₁‖ * ‖paperFT (fun u => (φ₁ u : ℂ)) y‖ + ‖c₂‖ * ‖paperFT (fun u => (φ₂ u : ℂ)) y‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖c₁‖ * (Real.exp (|1 / 2 - ρ.re| * a) * (4 * testNorm φ₁) / (1 + |ρ.im - 0|) ^ 2) +
            ‖c₂‖ * (Real.exp (|1 / 2 - ρ.re| * a) * (4 * testNorm φ₂) / (1 + |ρ.im - 0|) ^ 2) := by
          gcongr
      _ = _ := by ring
  have hconjre : (conj (gammaOf ρ)).re = ρ.im := by rw [Complex.conj_re, hxre]
  have hconjim : |(conj (gammaOf ρ)).im| = |1 / 2 - ρ.re| := by
    rw [Complex.conj_im, abs_neg, hxim]
  have hdiff := Wsummand_sub_eq_of_paperFT Z
    (A := paperFT (modulatedTest γ₀ s) (gammaOf ρ))
    (A' := paperFT (modulatedTest γ₀ s) (conj (gammaOf ρ)))
    (B := c₁ * paperFT (fun u => (φ₁ u : ℂ)) (gammaOf ρ) +
      c₂ * paperFT (fun u => (φ₂ u : ℂ)) (gammaOf ρ))
    (B' := c₁ * paperFT (fun u => (φ₁ u : ℂ)) (conj (gammaOf ρ)) +
      c₂ * paperFT (fun u => (φ₂ u : ℂ)) (conj (gammaOf ρ)))
    ((paperFT_polarCorrectedTest (γ₀ := γ₀) hs.continuous hφ₁.continuous hφ₂.continuous hss h1s
      h2s c₁ c₂ (gammaOf ρ)).trans (by ring))
    ((paperFT_polarCorrectedTest (γ₀ := γ₀) hs.continuous hφ₁.continuous hφ₂.continuous hss h1s
      h2s c₁ c₂ (conj (gammaOf ρ))).trans (by ring)) rfl rfl
  rw [hdiff, norm_mul, Complex.norm_natCast]
  exact norm_polar_expansion_le hm hN0 hG0 (Real.exp_pos _).le hE2
    (by linarith [abs_nonneg (ρ.im - γ₀)]) (by linarith [abs_nonneg (ρ.im - 0)])
    (hA _ hxre (by rw [hxim])) (hA _ hconjre hconjim) (hB _ hxre (by rw [hxim]))
    (hB _ hconjre hconjim)

/-- Summed cost of the polar correction. -/
theorem re_W_polarCorrected_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (γ₀ : ℝ) {a : ℝ}
    (ha : 0 ≤ a) {s φ₁ φ₂ : ℝ → ℝ} (hs : ContDiff ℝ 2 s) (hφ₁ : ContDiff ℝ 2 φ₁)
    (hφ₂ : ContDiff ℝ 2 φ₂) (hss : ∀ u, s u ≠ 0 → |u| ≤ a) (h1s : ∀ u, φ₁ u ≠ 0 → |u| ≤ a)
    (h2s : ∀ u, φ₂ u ≠ 0 → |u| ≤ a) (c₁ c₂ : ℂ) :
    (Z.W (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂) (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂)).re ≤
      (Z.W (modulatedTest γ₀ s) (modulatedTest γ₀ s)).re +
        768 * Real.exp a * A₀ * Real.log (|γ₀| + 3) *
          (testNorm s * (‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂) +
            (‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂) ^ 2) := by
  obtain ⟨hw₀, hle₀⟩ := window_tsum_le Z hA₀ hloc γ₀
  obtain ⟨hw₁, hle₁⟩ := window_tsum_le Z hA₀ hloc 0
  set M := testNorm s * (‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂) +
    (‖c₁‖ * testNorm φ₁ + ‖c₂‖ * testNorm φ₂) ^ 2 with hM
  have hM0 : 0 ≤ M := by
    have := testNorm_nonneg s; have := testNorm_nonneg φ₁; have := testNorm_nonneg φ₂
    positivity
  set F := polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ with hFdef
  set f₀ := modulatedTest γ₀ s with hf₀def
  set d : Z.carrier → ℂ := fun ρ => Z.Wsummand F F ρ - Z.Wsummand f₀ f₀ ρ with hd
  set b : Z.carrier → ℝ := fun ρ => 16 * Real.exp a * M *
    ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 + (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3)
    with hb
  have hbsum : Summable b := (hw₀.add hw₁).mul_left _
  have hdb : ∀ ρ, ‖d ρ‖ ≤ b ρ := fun ρ =>
    norm_Wsummand_polarCorrected_sub_le Z γ₀ ha hs hφ₁ hφ₂ hss h1s h2s c₁ c₂ ρ.2
  have hdsum : Summable d := Summable.of_norm_bounded hbsum hdb
  have h0sum : Summable (fun ρ : Z.carrier => Z.Wsummand f₀ f₀ ρ) :=
    Summable.of_norm_bounded (hw₀.mul_left _) fun ρ =>
      norm_Wsummand_modulatedTest_le_weight Z γ₀ ha hs hss ρ.2
  have hsplit : Z.W F F = Z.W f₀ f₀ + ∑' ρ, d ρ := by
    rw [ZeroConfig.W, ZeroConfig.W, ← Summable.tsum_add h0sum hdsum]
    congr 1 with ρ
    simp only [hd]
    ring
  have hnorm : ‖∑' ρ, d ρ‖ ≤ ∑' ρ, b ρ :=
    (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdb hbsum)).trans
      (Summable.tsum_le_tsum hdb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdb hbsum)
        hbsum)
  have hbt : ∑' ρ, b ρ ≤ 16 * Real.exp a * M * (24 * A₀ * Real.log (|γ₀| + 3) +
      24 * A₀ * Real.log (|(0 : ℝ)| + 3)) := by
    rw [hb, tsum_mul_left, Summable.tsum_add hw₀ hw₁]
    exact mul_le_mul_of_nonneg_left (add_le_add hle₀ hle₁) (by positivity)
  have hlog : Real.log (|(0 : ℝ)| + 3) ≤ Real.log (|γ₀| + 3) := by
    apply Real.log_le_log (by norm_num)
    rw [abs_zero]
    linarith [abs_nonneg γ₀]
  rw [hsplit, Complex.add_re]
  have hre : (∑' ρ, d ρ).re ≤ ‖∑' ρ, d ρ‖ := Complex.re_le_norm _
  have hA0 : 0 ≤ A₀ := by linarith
  have : 16 * Real.exp a * M * (24 * A₀ * Real.log (|γ₀| + 3) + 24 * A₀ * Real.log (|(0 : ℝ)| + 3)) ≤
      768 * Real.exp a * A₀ * Real.log (|γ₀| + 3) * M := by
    have h16 : 0 ≤ 16 * Real.exp a * M := by positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 24 * A₀)) h16
    nlinarith
  linarith

/-- Weil positivity on the polar-constrained subspace: the level-`a` Hodge index. -/
def HodgeIndexAtLevel (Z : ZeroConfig) (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 → 0 ≤ (Z.W f f).re

/-- `2a cosh(δa)(a⁵ + δ²a⁵ + 10δa⁴ + 20a³)`, the norm bound of the deep-zero test. -/
def deepZeroNormBound (a δ : ℝ) : ℝ :=
  2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)

/-- `w (wa)^{5/2} sinh²(δ(a - 2w))`, the energy bound of the deep-zero test. -/
def deepZeroEnergyBound (a δ w : ℝ) : ℝ :=
  w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2

/-- The relative size of the polar correction at height `γ₀`. -/
def polarCorrectionBound (a γ₀ : ℝ) : ℝ :=
  4 * Real.exp (a / 2) *
    (2 * a * (a ^ 5 + 20 * a ^ 3) / (a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ)) +
      deepZeroNormBound a (1 / 2) / deepZeroEnergyBound a (1 / 2) (a / 4)) / (1 + |γ₀|) ^ 2

theorem deepZeroEnergyBound_pos {a δ w : ℝ} (hδ : 0 < δ) (hw : 0 < w) (hwa : w < a / 2) :
    0 < deepZeroEnergyBound a δ w := by
  have ha : 0 < a := by linarith
  unfold deepZeroEnergyBound
  have : 0 < Real.sinh (δ * (a - 2 * w)) := Real.sinh_pos_iff.mpr (by nlinarith)
  positivity

theorem norm_paperFT_modulatedTest_polar_le {γ₀ a : ℝ} {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s)
    (hss : ∀ u, s u ≠ 0 → |u| ≤ a) (σ : ℝ) (hσ : |σ| = 1 / 2) :
    ‖paperFT (modulatedTest γ₀ s) (I * σ)‖ ≤
      Real.exp (a / 2) * (4 * testNorm s) / (1 + |γ₀|) ^ 2 := by
  have hS : ContDiff ℝ 2 (fun u => (s u : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  have hSs : ∀ u, (fun u => (s u : ℂ)) u ≠ 0 → |u| ≤ a := fun u hu =>
    hss u (fun h => hu (by simp [h]))
  have := norm_paperFT_le_decay hS hSs (I * σ - γ₀)
  unfold modulatedTest
  rw [paperFT_modulate]
  have e1 : |(I * (σ : ℂ) - (γ₀ : ℂ)).re| = |γ₀| := by simp
  have e2 : |(I * (σ : ℂ) - (γ₀ : ℂ)).im| * a = a / 2 := by simp [hσ]; ring
  rw [e1, e2] at this
  exact this

theorem polarCorrectedTest_contDiff (γ₀ : ℝ) {s φ₁ φ₂ : ℝ → ℝ} (hs : ContDiff ℝ 2 s)
    (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) (c₁ c₂ : ℂ) :
    ContDiff ℝ 2 (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂) := by
  unfold polarCorrectedTest
  exact ((modulatedTest_contDiff γ₀ hs).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ₁))).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ₂))

theorem tsupport_polarCorrectedTest_subset (γ₀ : ℝ) {a : ℝ} {s φ₁ φ₂ : ℝ → ℝ}
    (hss : ∀ u, s u ≠ 0 → |u| ≤ a) (h1s : ∀ u, φ₁ u ≠ 0 → |u| ≤ a)
    (h2s : ∀ u, φ₂ u ≠ 0 → |u| ≤ a) (c₁ c₂ : ℂ) :
    tsupport (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂) ⊆ Icc (-a) a := by
  refine tsupport_subset_of_support_subset_abs fun u hu => ?_
  by_contra hlt
  apply hu
  have e0 : s u = 0 := by by_contra h; exact hlt (hss u h)
  have e1 : φ₁ u = 0 := by by_contra h; exact hlt (h1s u h)
  have e2 : φ₂ u = 0 := by by_contra h; exact hlt (h2s u h)
  simp only [polarCorrectedTest, modulatedTest, e0, e1, e2, Complex.ofReal_zero, mul_zero,
    add_zero]

/-- The coefficients `c₁ = -(H₊ + H₋)/(2α)`, `c₂ = (H₊ - H₋)/(2β)` cancel both polar values. -/
theorem polarCorrectedTest_polar_zero {γ₀ a : ℝ} {s φ₁ φ₂ : ℝ → ℝ} (hs : Continuous s)
    (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hss : ∀ u, s u ≠ 0 → |u| ≤ a)
    (h1s : ∀ u, φ₁ u ≠ 0 → |u| ≤ a) (h2s : ∀ u, φ₂ u ≠ 0 → |u| ≤ a) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hp1 : paperFT (fun u => (φ₁ u : ℂ)) (I / 2) = α)
    (hm1 : paperFT (fun u => (φ₁ u : ℂ)) (-(I / 2)) = α)
    (hp2 : paperFT (fun u => (φ₂ u : ℂ)) (I / 2) = -(β : ℂ))
    (hm2 : paperFT (fun u => (φ₂ u : ℂ)) (-(I / 2)) = β) :
    paperFT (polarCorrectedTest γ₀ s φ₁ φ₂
        (-(paperFT (modulatedTest γ₀ s) (I / 2) + paperFT (modulatedTest γ₀ s) (-(I / 2))) /
          (2 * α))
        ((paperFT (modulatedTest γ₀ s) (I / 2) - paperFT (modulatedTest γ₀ s) (-(I / 2))) /
          (2 * β))) (I / 2) = 0 ∧
    paperFT (polarCorrectedTest γ₀ s φ₁ φ₂
        (-(paperFT (modulatedTest γ₀ s) (I / 2) + paperFT (modulatedTest γ₀ s) (-(I / 2))) /
          (2 * α))
        ((paperFT (modulatedTest γ₀ s) (I / 2) - paperFT (modulatedTest γ₀ s) (-(I / 2))) /
          (2 * β))) (-(I / 2)) = 0 := by
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  constructor
  · rw [paperFT_polarCorrectedTest hs hφ₁ hφ₂ hss h1s h2s, hp1, hp2]
    field_simp
    ring
  · rw [paperFT_polarCorrectedTest hs hφ₁ hφ₂ hss h1s h2s, hm1, hm2]
    field_simp
    ring

theorem polarCorrection_coeff_bound {Hp Hm : ℂ} {α β H N₁ N₂ N₁b N₂b αb βb : ℝ}
    (hαb0 : 0 < αb) (hβb0 : 0 < βb) (hαb : αb ≤ α) (hβb : βb ≤ β) (hHp : ‖Hp‖ ≤ H)
    (hHm : ‖Hm‖ ≤ H) (hN1 : N₁ ≤ N₁b) (hN2 : N₂ ≤ N₂b) (hN10 : 0 ≤ N₁) (hN20 : 0 ≤ N₂) :
    ‖-(Hp + Hm) / (2 * (α : ℂ))‖ * N₁ + ‖(Hp - Hm) / (2 * (β : ℂ))‖ * N₂ ≤
      H * (N₁b / αb + N₂b / βb) := by
  have hα0 : 0 < α := hαb0.trans_le hαb
  have hβ0 : 0 < β := hβb0.trans_le hβb
  have hH0 : 0 ≤ H := (norm_nonneg _).trans hHp
  have hc₁ : ‖-(Hp + Hm) / (2 * (α : ℂ))‖ ≤ H / α := by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hα0, div_le_div_iff₀ (by positivity) hα0]
    have := norm_add_le Hp Hm
    nlinarith
  have hc₂ : ‖(Hp - Hm) / (2 * (β : ℂ))‖ ≤ H / β := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hβ0, div_le_div_iff₀ (by positivity) hβ0]
    have := norm_sub_le Hp Hm
    nlinarith
  have hN1b0 : 0 ≤ N₁b := hN10.trans hN1
  have hN2b0 : 0 ≤ N₂b := hN20.trans hN2
  have e1 : ‖-(Hp + Hm) / (2 * (α : ℂ))‖ * N₁ ≤ H * (N₁b / αb) :=
    calc ‖-(Hp + Hm) / (2 * (α : ℂ))‖ * N₁ ≤ (H / α) * N₁b :=
          mul_le_mul hc₁ hN1 hN10 (by positivity)
      _ ≤ (H / αb) * N₁b := by gcongr
      _ = H * (N₁b / αb) := by ring
  have e2 : ‖(Hp - Hm) / (2 * (β : ℂ))‖ * N₂ ≤ H * (N₂b / βb) :=
    calc ‖(Hp - Hm) / (2 * (β : ℂ))‖ * N₂ ≤ (H / β) * N₂b :=
          mul_le_mul hc₂ hN2 hN20 (by positivity)
      _ ≤ (H / βb) * N₂b := by gcongr
      _ = H * (N₂b / βb) := by ring
  linarith

theorem polarCorrection_cost_le {N G Nb ε : ℝ} (hN0 : 0 ≤ N) (hNb : N ≤ Nb) (hG0 : 0 ≤ G)
    (hG : G ≤ N * ε) (hε0 : 0 ≤ ε) : N * G + G ^ 2 ≤ Nb ^ 2 * (ε + ε ^ 2) := by
  have h1 : N * G ≤ N * (N * ε) := mul_le_mul_of_nonneg_left hG hN0
  have h2 : G ^ 2 ≤ (N * ε) ^ 2 := pow_le_pow_left₀ hG0 hG 2
  have h3 : N ^ 2 ≤ Nb ^ 2 := pow_le_pow_left₀ hN0 hNb 2
  have h5 : N ^ 2 * (ε + ε ^ 2) ≤ Nb ^ 2 * (ε + ε ^ 2) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  nlinarith

theorem deepZeroNormBound_nonneg {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    0 ≤ deepZeroNormBound a δ := by
  unfold deepZeroNormBound
  have := Real.cosh_pos (δ * a)
  positivity

theorem polarCorrectionBound_nonneg {a : ℝ} (ha : 0 < a) (γ₀ : ℝ) :
    0 ≤ polarCorrectionBound a γ₀ := by
  unfold polarCorrectionBound
  have h1 := deepZeroNormBound_nonneg (a := a) (δ := 1 / 2) ha.le (by norm_num)
  have h2 := deepZeroEnergyBound_pos (a := a) (δ := 1 / 2) (w := a / 4) (by norm_num)
    (by positivity) (by linarith)
  positivity

/-- Weil form of the polar-corrected deep-zero test. -/
theorem re_W_hodge_test_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hiso : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R → ρ.re = 1 / 2)
    (c₁ c₂ : ℂ)
    (hG : ‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2)) ≤
      testNorm (sinhTest a δ) * polarCorrectionBound a ρ₀.im) :
    (Z.W (polarCorrectedTest ρ₀.im (sinhTest a δ) (sinhTestWeight a) (sinhTest a (1 / 2)) c₁ c₂)
        (polarCorrectedTest ρ₀.im (sinhTest a δ) (sinhTestWeight a) (sinhTest a (1 / 2))
          c₁ c₂)).re ≤
      -2 * deepZeroEnergyBound a δ w ^ 2 +
        (384 * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
            (1 + Real.exp a / (1 + R)) +
          768 * Real.exp a * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
            (polarCorrectionBound a ρ₀.im + polarCorrectionBound a ρ₀.im ^ 2)) := by
  have ha : 0 < a := by linarith
  have hmaster := re_W_modulatedTest_le_of_isolated Z hA₀ hloc hρ₀ hδ hre ha.le hR hiso
    (sinhTest_contDiff a δ) (sinhTest_odd a δ) (sinhTest_supp ha.le)
  have hcorr := re_W_polarCorrected_le Z hA₀ hloc ρ₀.im ha.le (sinhTest_contDiff a δ)
    (sinhTestWeight_contDiff a) (sinhTest_contDiff a (1 / 2)) (sinhTest_supp ha.le)
    (sinhTestWeight_supp ha.le) (sinhTest_supp ha.le) c₁ c₂
  have hN0 := testNorm_nonneg (sinhTest a δ)
  have hNb : testNorm (sinhTest a δ) ≤ deepZeroNormBound a δ := testNorm_sinhTest_le ha.le hδ.le
  have hG0 : 0 ≤ ‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2)) := by
    have := testNorm_nonneg (sinhTestWeight a); have := testNorm_nonneg (sinhTest a (1 / 2))
    positivity
  have hcost := polarCorrection_cost_le hN0 hNb hG0 hG (polarCorrectionBound_nonneg ha ρ₀.im)
  have hP := sinhTest_energy_ge (a := a) hδ hw hwa
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hPl0 : 0 ≤ deepZeroEnergyBound a δ w := by unfold deepZeroEnergyBound; positivity
  have hP2 : deepZeroEnergyBound a δ w ^ 2 ≤ (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 :=
    pow_le_pow_left₀ hPl0 hP 2
  have hL : 0 ≤ Real.log (|ρ₀.im| + 3) := (zero_le_one).trans (one_le_log_abs_add_three ρ₀.im)
  have hA0 : 0 ≤ A₀ := by linarith
  have hK : 0 ≤ 1 + Real.exp a / (1 + R) := by positivity
  have h1 : -2 * (Z.mult ρ₀ : ℝ) * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 ≤
      -2 * deepZeroEnergyBound a δ w ^ 2 := by
    nlinarith [sq_nonneg (∫ u, sinhTest a δ u * Real.sinh (δ * u))]
  have h2 : 384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm (sinhTest a δ) ^ 2 *
        (1 + Real.exp a / (1 + R)) ≤
      384 * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
        (1 + Real.exp a / (1 + R)) := by
    have := pow_le_pow_left₀ hN0 hNb 2
    gcongr
  have h3 : 768 * Real.exp a * A₀ * Real.log (|ρ₀.im| + 3) *
        (testNorm (sinhTest a δ) * (‖c₁‖ * testNorm (sinhTestWeight a) +
          ‖c₂‖ * testNorm (sinhTest a (1 / 2))) +
          (‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2))) ^ 2) ≤
      768 * Real.exp a * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
        (polarCorrectionBound a ρ₀.im + polarCorrectionBound a ρ₀.im ^ 2) := by
    rw [mul_assoc (768 * Real.exp a * A₀ * Real.log (|ρ₀.im| + 3)) (deepZeroNormBound a δ ^ 2)]
    gcongr
  linarith

/-- **An isolated deep zero violates the level-`a` Hodge index.**  Under the isolation
hypothesis, and a size condition that adds the polar-correction cost to that of
`exists_re_W_neg_of_isolated_deep_zero`, a `C²` test supported in `[-a, a]` with
`h_f(±i/2) = 0` has negative Weil form.  The test is the deep-zero test corrected by multiples of
`(a² - u²)₊^{5/2}` and `sinh(u/2)(a² - u²)₊^{5/2}` that cancel its two polar values; relative to
the test, their size is `O(e^{a/2}/(1 + |γ₀|)²)`. -/
theorem exists_hodge_violation_of_isolated_deep_zero (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hiso : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R → ρ.re = 1 / 2)
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
          (1 + Real.exp a / (1 + R)) +
        768 * Real.exp a * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
          (polarCorrectionBound a ρ₀.im + polarCorrectionBound a ρ₀.im ^ 2) <
      2 * deepZeroEnergyBound a δ w ^ 2) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ (Z.W f f).re < 0 := by
  have ha : 0 < a := by linarith
  have hIhalf : I * ((1 / 2 : ℝ) : ℂ) = I / 2 := by push_cast; ring
  have hαb := sinhTestWeight_cosh_energy_ge ha
  have hβb : deepZeroEnergyBound a (1 / 2) (a / 4) ≤
      ∫ u, sinhTest a (1 / 2) u * Real.sinh (1 / 2 * u) :=
    sinhTest_energy_ge (a := a) (δ := 1 / 2) (w := a / 4) (by norm_num) (by positivity) le_rfl
  have hαb0 : 0 < a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ) := by positivity
  have hβb0 : 0 < deepZeroEnergyBound a (1 / 2) (a / 4) :=
    deepZeroEnergyBound_pos (by norm_num) (by positivity) (by linarith)
  have hp1 := paperFT_even_I_mul (sinhTestWeight_contDiff a).continuous
    (sinhTestWeight_supp ha.le) (sinhTestWeight_even a) (1 / 2)
  have hm1 := paperFT_even_neg_I_mul (sinhTestWeight_contDiff a).continuous
    (sinhTestWeight_supp ha.le) (sinhTestWeight_even a) (1 / 2)
  have hp2 := paperFT_odd_I_mul (sinhTest_contDiff a (1 / 2)).continuous
    (sinhTest_supp (a := a) (δ := 1 / 2) ha.le) (sinhTest_odd a (1 / 2)) (1 / 2)
  have hm2 := paperFT_odd_neg_I_mul (sinhTest_contDiff a (1 / 2)).continuous
    (sinhTest_supp (a := a) (δ := 1 / 2) ha.le) (sinhTest_odd a (1 / 2)) (1 / 2)
  rw [hIhalf] at hp1 hm1 hp2 hm2
  obtain ⟨hpol1, hpol2⟩ := polarCorrectedTest_polar_zero (γ₀ := ρ₀.im)
    (sinhTest_contDiff a δ).continuous (sinhTestWeight_contDiff a).continuous
    (sinhTest_contDiff a (1 / 2)).continuous (sinhTest_supp ha.le) (sinhTestWeight_supp ha.le)
    (sinhTest_supp ha.le) (hαb0.trans_le hαb).ne' (hβb0.trans_le hβb).ne' hp1 hm1 hp2 hm2
  have hHp := norm_paperFT_modulatedTest_polar_le (γ₀ := ρ₀.im) (sinhTest_contDiff a δ)
    (sinhTest_supp ha.le) (1 / 2) (by norm_num)
  have hHm := norm_paperFT_modulatedTest_polar_le (γ₀ := ρ₀.im) (sinhTest_contDiff a δ)
    (sinhTest_supp ha.le) (-(1 / 2)) (by norm_num)
  rw [hIhalf] at hHp
  rw [show I * ((-(1 / 2) : ℝ) : ℂ) = -(I / 2) by push_cast; ring] at hHm
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℂ, c =
      -(paperFT (modulatedTest ρ₀.im (sinhTest a δ)) (I / 2) +
          paperFT (modulatedTest ρ₀.im (sinhTest a δ)) (-(I / 2))) /
        (2 * ((∫ u, sinhTestWeight a u * Real.cosh (1 / 2 * u) : ℝ) : ℂ)) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℂ, c =
      (paperFT (modulatedTest ρ₀.im (sinhTest a δ)) (I / 2) -
          paperFT (modulatedTest ρ₀.im (sinhTest a δ)) (-(I / 2))) /
        (2 * ((∫ u, sinhTest a (1 / 2) u * Real.sinh (1 / 2 * u) : ℝ) : ℂ)) := ⟨_, rfl⟩
  rw [← hc₁, ← hc₂] at hpol1 hpol2
  have hG := polarCorrection_coeff_bound hαb0 hβb0 hαb hβb hHp hHm
    (testNorm_sinhTestWeight_le ha.le) (testNorm_sinhTest_le ha.le (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (testNorm_nonneg _) (testNorm_nonneg _)
  rw [← hc₁, ← hc₂] at hG
  have hG' : ‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2)) ≤
      testNorm (sinhTest a δ) * polarCorrectionBound a ρ₀.im := by
    refine hG.trans (le_of_eq ?_)
    unfold polarCorrectionBound deepZeroNormBound
    ring
  refine ⟨polarCorrectedTest ρ₀.im (sinhTest a δ) (sinhTestWeight a) (sinhTest a (1 / 2)) c₁ c₂,
    polarCorrectedTest_contDiff ρ₀.im (sinhTest_contDiff a δ)
      (sinhTestWeight_contDiff a) (sinhTest_contDiff a (1 / 2)) c₁ c₂,
    tsupport_polarCorrectedTest_subset ρ₀.im (sinhTest_supp ha.le) (sinhTestWeight_supp ha.le)
      (sinhTest_supp ha.le) c₁ c₂, hpol1, hpol2, ?_⟩
  have := re_W_hodge_test_le Z hA₀ hloc hρ₀ hδ hre hR hw hwa hiso c₁ c₂ hG'
  linarith

/-- **The level-`a` Hodge index forces off-line companions.** -/
theorem exists_offLine_companion_of_hodge_index (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a : ℝ}
    (hodge : HodgeIndexAtLevel Z a)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
          (1 + Real.exp a / (1 + R)) +
        768 * Real.exp a * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
          (polarCorrectionBound a ρ₀.im + polarCorrectionBound a ρ₀.im ^ 2) <
      2 * deepZeroEnergyBound a δ w ^ 2) :
    ∃ ρ ∈ Z.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧ ρ.re ≠ 1 / 2 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ :=
    exists_hodge_violation_of_isolated_deep_zero Z hA₀ hloc hρ₀ hδ hre hR hw hwa h hbig
  exact absurd (hodge f hf hfs hp hm) (not_le.mpr hneg)

/-- The Hodge-index companion law for the nontrivial zeros of `ζ`. -/
theorem zeta_hodge_index_forces_offLine_companion :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ, HodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∀ δ : ℝ, 0 < δ → ρ₀.re = 1 / 2 + δ →
      ∀ R w : ℝ, 0 ≤ R → 0 < w → w ≤ a / 4 →
        384 * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
              (1 + Real.exp a / (1 + R)) +
            768 * Real.exp a * A₀ * Real.log (|ρ₀.im| + 3) * deepZeroNormBound a δ ^ 2 *
              (polarCorrectionBound a ρ₀.im + polarCorrectionBound a ρ₀.im ^ 2) <
          2 * deepZeroEnergyBound a δ w ^ 2 →
        ∃ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧
          ρ.re ≠ 1 / 2 := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun a hodge ρ₀ hρ₀ δ hδ hre R w hR hw hwa hbig =>
    exists_offLine_companion_of_hodge_index zetaZeroConfig hA₀ hloc hodge hρ₀ hδ hre hR hw hwa
      hbig⟩

end RHTower
