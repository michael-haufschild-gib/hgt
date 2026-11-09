import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheLandingLaw
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# The functional equation admits remainders that approach the line without landing

For any depths `0 < δ_n < ½` with `δ_n → 0` put `γ_n = (n + 1)²`, `α_n = δ_n + i γ_n` and

`G(s) = cosh(s − ½) · ∏_n (1 − (s − ½)²/α_n²)(1 − (s − ½)²/ᾱ_n²)`.

* `G` is entire (`differentiable_approachingModel`), satisfies the functional equation
  `G(1 − s) = G(s)` and reality `G(s̄) = conj G(s)`, and has exponential type
  (`norm_approachingModel_le`): `‖E_n(w)‖ ≤ exp(4‖w‖/γ_n)` from `1 + x² ≤ e^{2x}`.
* Its zeros are the critical-line zeros `½ + i(2k + 1)π/2` of the cosh factor, of linear density,
  and the quartets `½ ± δ_n ± iγ_n` (`approachingModel_eq_zero_iff`).
* The strip configuration of its zeros approaches the line but has infinitely many zeros off it
  (`exists_approachingModel_not_landingLaw`). So the functional equation, reality and order one
  do not imply the landing law `ZAL ⇒ FiniteOffLine`.
-/

open Complex Set Filter Topology
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-! ### The planted quartets -/

/-- Height `γ_n = (n + 1)²` of the `n`-th planted quartet. -/
def plantHeight (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

theorem one_le_plantHeight (n : ℕ) : 1 ≤ plantHeight n := by
  unfold plantHeight; nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem summable_inv_plantHeight : Summable fun n : ℕ => 1 / plantHeight n := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine h.congr fun n => ?_
  simp [plantHeight]

/-- The centred planted zero `α_n = δ_n + iγ_n`. -/
def plantZero (δ : ℕ → ℝ) (n : ℕ) : ℂ := (δ n : ℂ) + (plantHeight n : ℂ) * I

theorem plantZero_re (δ : ℕ → ℝ) (n : ℕ) : (plantZero δ n).re = δ n := by simp [plantZero]
theorem plantZero_im (δ : ℕ → ℝ) (n : ℕ) : (plantZero δ n).im = plantHeight n := by
  simp [plantZero]

theorem plantHeight_le_norm_plantZero (δ : ℕ → ℝ) (n : ℕ) : plantHeight n ≤ ‖plantZero δ n‖ := by
  have h := Complex.abs_im_le_norm (plantZero δ n)
  rwa [plantZero_im, abs_of_pos (by linarith [one_le_plantHeight n])] at h

theorem plantZero_ne_zero (δ : ℕ → ℝ) (n : ℕ) : plantZero δ n ≠ 0 := fun h => by
  have := plantHeight_le_norm_plantZero δ n
  rw [h, norm_zero] at this
  linarith [one_le_plantHeight n]

/-- Quartet factor `(1 − w²/α²)(1 − w²/ᾱ²)`, even in `w`, vanishing at `±α, ±ᾱ`. -/
def quartetFactor (δ : ℕ → ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  (1 - w ^ 2 / plantZero δ n ^ 2) * (1 - w ^ 2 / conj (plantZero δ n) ^ 2)

/-- `‖w²/α²‖ ≤ (‖w‖/γ)²` when `‖α‖ ≥ γ`. -/
theorem norm_sq_div_sq_le {w α : ℂ} {γ : ℝ} (hγ : 0 < γ) (hα : γ ≤ ‖α‖) :
    ‖w ^ 2 / α ^ 2‖ ≤ (‖w‖ / γ) ^ 2 := by
  rw [norm_div, norm_pow, norm_pow, div_pow]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hγ.le hα 2)

theorem norm_conj_plantZero (δ : ℕ → ℝ) (n : ℕ) : ‖conj (plantZero δ n)‖ = ‖plantZero δ n‖ :=
  Complex.norm_conj _

/-- Uniform bound `‖E_n(w) − 1‖ ≤ (2R² + R⁴)/γ_n` on `‖w‖ ≤ R`. -/
theorem norm_quartetFactor_sub_one_le (δ : ℕ → ℝ) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) {w : ℂ}
    (hw : ‖w‖ ≤ R) : ‖quartetFactor δ n w - 1‖ ≤ (2 * R ^ 2 + R ^ 4) * (1 / plantHeight n) := by
  have hγ1 := one_le_plantHeight n
  have hγ : 0 < plantHeight n := by linarith
  set a := w ^ 2 / plantZero δ n ^ 2
  set b := w ^ 2 / conj (plantZero δ n) ^ 2
  have hx : (‖w‖ / plantHeight n) ^ 2 ≤ R ^ 2 * (1 / plantHeight n) := by
    rw [div_pow, mul_one_div]
    refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg w) hw 2) hγ ?_
    nlinarith
  have ha : ‖a‖ ≤ R ^ 2 * (1 / plantHeight n) :=
    (norm_sq_div_sq_le hγ (plantHeight_le_norm_plantZero δ n)).trans hx
  have hb : ‖b‖ ≤ R ^ 2 * (1 / plantHeight n) :=
    (norm_sq_div_sq_le hγ ((plantHeight_le_norm_plantZero δ n).trans
      (norm_conj_plantZero δ n).ge)).trans hx
  have hinv : 1 / plantHeight n ≤ 1 := by rw [div_le_one hγ]; exact hγ1
  have hinv0 : 0 ≤ 1 / plantHeight n := by positivity
  have hab : ‖a‖ * ‖b‖ ≤ R ^ 4 * (1 / plantHeight n) := by
    calc ‖a‖ * ‖b‖ ≤ (R ^ 2 * (1 / plantHeight n)) * (R ^ 2 * (1 / plantHeight n)) :=
          mul_le_mul ha hb (norm_nonneg _) (by positivity)
      _ = R ^ 4 * (1 / plantHeight n) * (1 / plantHeight n) := by ring
      _ ≤ R ^ 4 * (1 / plantHeight n) * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = R ^ 4 * (1 / plantHeight n) := mul_one _
  have heq : quartetFactor δ n w - 1 = -a - b + a * b := by
    simp only [quartetFactor, a, b]; ring
  rw [heq]
  calc ‖-a - b + a * b‖ ≤ ‖a‖ + ‖b‖ + ‖a‖ * ‖b‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
        gcongr
        exact (norm_sub_le _ _).trans (by rw [norm_neg])
    _ ≤ (2 * R ^ 2 + R ^ 4) * (1 / plantHeight n) := by nlinarith

theorem summable_norm_quartetFactor_sub_one (δ : ℕ → ℝ) (w : ℂ) :
    Summable fun n => ‖quartetFactor δ n w - 1‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_quartetFactor_sub_one_le δ n (norm_nonneg w) le_rfl)
    (summable_inv_plantHeight.mul_left _)

theorem multipliable_quartetFactor (δ : ℕ → ℝ) (w : ℂ) :
    Multipliable fun n => quartetFactor δ n w := by
  have h := Complex.multipliable_one_add_of_summable
    (summable_norm_quartetFactor_sub_one δ w).of_norm
  simpa using h

/-! ### The quartet product -/

/-- `P(w) = ∏_n E_n(w)`. -/
def quartetProduct (δ : ℕ → ℝ) (w : ℂ) : ℂ := ∏' n, quartetFactor δ n w

theorem differentiable_quartetFactor (δ : ℕ → ℝ) (n : ℕ) : Differentiable ℂ (quartetFactor δ n) := by
  unfold quartetFactor; fun_prop

/-- **The quartet product converges locally uniformly.** -/
theorem hasProdLocallyUniformlyOn_quartetFactor (δ : ℕ → ℝ) :
    HasProdLocallyUniformlyOn (quartetFactor δ) (quartetProduct δ) univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_norm (E := ℂ)).continuousOn
  set R : ℝ := max C 0
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hprod := Summable.hasProdUniformlyOn_one_add hK
    (summable_inv_plantHeight.mul_left (2 * R ^ 2 + R ^ 4))
    (Eventually.of_forall fun n z hz => norm_quartetFactor_sub_one_le δ n hR (hKR z hz))
    (fun n => ((differentiable_quartetFactor δ n).continuous.sub continuous_const).continuousOn)
  have heq : (fun (n : ℕ) (z : ℂ) => 1 + (quartetFactor δ n z - 1)) = quartetFactor δ := by
    funext n z; ring
  have heq2 : (fun z : ℂ => ∏' n : ℕ, (1 + (quartetFactor δ n z - 1))) = quartetProduct δ := by
    funext z; exact tprod_congr fun n => by ring
  rwa [heq, heq2] at hprod

/-- **The quartet product is entire.** -/
theorem differentiable_quartetProduct (δ : ℕ → ℝ) : Differentiable ℂ (quartetProduct δ) := by
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_quartetFactor δ)
  have hd : ∀ᶠ S : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun z => ∏ n ∈ S, quartetFactor δ n z) univ :=
    Eventually.of_forall fun S => DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_quartetFactor δ n).differentiableOn
  have := ht.differentiableOn hd isOpen_univ
  exact fun z => this.differentiableAt (by simp)

theorem quartetProduct_neg (δ : ℕ → ℝ) (w : ℂ) : quartetProduct δ (-w) = quartetProduct δ w :=
  tprod_congr fun n => by simp [quartetFactor]

theorem quartetFactor_conj (δ : ℕ → ℝ) (n : ℕ) (w : ℂ) :
    quartetFactor δ n (conj w) = conj (quartetFactor δ n w) := by
  simp only [quartetFactor, map_mul, map_sub, map_one, map_div₀, map_pow, Complex.conj_conj]
  ring

theorem quartetProduct_conj (δ : ℕ → ℝ) (w : ℂ) :
    quartetProduct δ (conj w) = conj (quartetProduct δ w) := by
  have h := (multipliable_quartetFactor δ w).hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  rw [quartetProduct, ← h.tprod_eq]
  exact tprod_congr fun n => quartetFactor_conj δ n w

theorem quartetProduct_zero (δ : ℕ → ℝ) : quartetProduct δ 0 = 1 := by
  simp [quartetProduct, quartetFactor]

/-- `1 + x² ≤ e^{2x}` for `x ≥ 0`. -/
theorem one_add_sq_le_exp_two_mul {x : ℝ} (hx : 0 ≤ x) : 1 + x ^ 2 ≤ Real.exp (2 * x) := by
  have h := Real.add_one_le_exp x
  calc 1 + x ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
    _ ≤ Real.exp x ^ 2 := pow_le_pow_left₀ (by linarith) h 2
    _ = Real.exp (2 * x) := by rw [← Real.exp_nat_mul]; norm_num

/-- `‖E_n(w)‖ ≤ exp(4‖w‖/γ_n)`. -/
theorem norm_quartetFactor_le (δ : ℕ → ℝ) (n : ℕ) (w : ℂ) :
    ‖quartetFactor δ n w‖ ≤ Real.exp (4 * ‖w‖ * (1 / plantHeight n)) := by
  have hγ : 0 < plantHeight n := by linarith [one_le_plantHeight n]
  set x := ‖w‖ / plantHeight n
  have hx : 0 ≤ x := by positivity
  have hone : ∀ α : ℂ, plantHeight n ≤ ‖α‖ → ‖1 - w ^ 2 / α ^ 2‖ ≤ Real.exp (2 * x) := fun α hα =>
    calc ‖1 - w ^ 2 / α ^ 2‖ ≤ 1 + ‖w ^ 2 / α ^ 2‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_one]
      _ ≤ 1 + x ^ 2 := by gcongr; exact norm_sq_div_sq_le hγ hα
      _ ≤ Real.exp (2 * x) := one_add_sq_le_exp_two_mul hx
  rw [quartetFactor, norm_mul]
  calc _ ≤ Real.exp (2 * x) * Real.exp (2 * x) :=
        mul_le_mul (hone _ (plantHeight_le_norm_plantZero δ n))
          (hone _ ((plantHeight_le_norm_plantZero δ n).trans (norm_conj_plantZero δ n).ge))
          (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (4 * ‖w‖ * (1 / plantHeight n)) := by
        rw [← Real.exp_add]; congr 1; simp only [x]; ring

/-- **Exponential type of the quartet product.** -/
theorem norm_quartetProduct_le (δ : ℕ → ℝ) (w : ℂ) :
    ‖quartetProduct δ w‖ ≤ Real.exp (4 * ‖w‖ * ∑' n, 1 / plantHeight n) := by
  have hlim := ((multipliable_quartetFactor δ w).hasProd).norm
  refine le_of_tendsto' hlim fun S => ?_
  rw [norm_prod]
  calc ∏ n ∈ S, ‖quartetFactor δ n w‖
      ≤ ∏ n ∈ S, Real.exp (4 * ‖w‖ * (1 / plantHeight n)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun n _ => norm_quartetFactor_le δ n w
    _ = Real.exp (4 * ‖w‖ * ∑ n ∈ S, 1 / plantHeight n) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (4 * ‖w‖ * ∑' n, 1 / plantHeight n) := by
        gcongr
        exact summable_inv_plantHeight.sum_le_tsum S fun n _ =>
          by have := one_le_plantHeight n; positivity

theorem quartetFactor_eq_zero_iff (δ : ℕ → ℝ) (n : ℕ) (w : ℂ) :
    quartetFactor δ n w = 0 ↔
      w = plantZero δ n ∨ w = -plantZero δ n ∨ w = conj (plantZero δ n) ∨
        w = -conj (plantZero δ n) := by
  have h0 := plantZero_ne_zero δ n
  have h0' : conj (plantZero δ n) ≠ 0 := (map_ne_zero _).mpr h0
  simp only [quartetFactor, mul_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℂ)),
    div_eq_one_iff_eq (pow_ne_zero 2 h0), div_eq_one_iff_eq (pow_ne_zero 2 h0'),
    sq_eq_sq_iff_eq_or_eq_neg, or_assoc]

theorem quartetProduct_eq_zero_iff (δ : ℕ → ℝ) (w : ℂ) :
    quartetProduct δ w = 0 ↔ ∃ n, quartetFactor δ n w = 0 := by
  refine ⟨fun h => ?_, fun h => tprod_of_exists_eq_zero h⟩
  by_contra hne
  push Not at hne
  have := tprod_one_add_ne_zero_of_summable (f := fun n => quartetFactor δ n w - 1)
    (fun n => by simpa using hne n) (summable_norm_quartetFactor_sub_one δ w)
  exact this (by simpa [quartetProduct] using h)

/-! ### The approaching model -/

/-- `G(s) = cosh(s − ½) · P(s − ½)`. -/
def approachingModel (δ : ℕ → ℝ) (s : ℂ) : ℂ := Complex.cosh (s - 1 / 2) * quartetProduct δ (s - 1 / 2)

theorem differentiable_approachingModel (δ : ℕ → ℝ) : Differentiable ℂ (approachingModel δ) := by
  unfold approachingModel
  exact (Complex.differentiable_cosh.comp (differentiable_id.sub_const _)).mul
    ((differentiable_quartetProduct δ).comp (differentiable_id.sub_const _))

/-- **Functional equation.** -/
theorem approachingModel_one_sub (δ : ℕ → ℝ) (s : ℂ) :
    approachingModel δ (1 - s) = approachingModel δ s := by
  have h : (1 - s) - 1 / 2 = -(s - 1 / 2) := by ring
  rw [approachingModel, approachingModel, h, Complex.cosh_neg, quartetProduct_neg]

/-- **Reality.** -/
theorem approachingModel_conj (δ : ℕ → ℝ) (s : ℂ) :
    approachingModel δ (conj s) = conj (approachingModel δ s) := by
  have h : conj s - 1 / 2 = conj (s - 1 / 2) := by simp [map_sub, map_div₀]
  rw [approachingModel, approachingModel, h, Complex.cosh_conj, quartetProduct_conj, map_mul]

theorem approachingModel_half (δ : ℕ → ℝ) : approachingModel δ (1 / 2) = 1 := by
  simp [approachingModel, quartetProduct_zero]

/-- `‖cosh z‖ ≤ e^{‖z‖}`. -/
theorem norm_cosh_le_exp_norm (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  have h2 : (2 : ℂ) * Complex.cosh z = Complex.exp z + Complex.exp (-z) := Complex.two_cosh z
  have hc : Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 := by
    rw [← h2]; ring
  have h1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm z)
  have h3 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using Complex.neg_re_le_norm z)
  rw [hc, norm_div, Complex.norm_two]
  linarith [norm_add_le (Complex.exp z) (Complex.exp (-z))]

/-- **Order one**: `‖G(s)‖ ≤ C e^{B‖s‖}`. -/
theorem norm_approachingModel_le (δ : ℕ → ℝ) :
    ∃ C B : ℝ, ∀ s : ℂ, ‖approachingModel δ s‖ ≤ C * Real.exp (B * ‖s‖) := by
  set S := ∑' n, 1 / plantHeight n
  have hS : 0 ≤ S := tsum_nonneg fun n => by have := one_le_plantHeight n; positivity
  refine ⟨Real.exp ((1 + 4 * S) / 2), 1 + 4 * S, fun s => ?_⟩
  have hw : ‖s - 1 / 2‖ ≤ ‖s‖ + 1 / 2 := by
    refine (norm_sub_le _ _).trans ?_; norm_num
  rw [approachingModel, norm_mul]
  calc _ ≤ Real.exp ‖s - 1 / 2‖ * Real.exp (4 * ‖s - 1 / 2‖ * S) :=
        mul_le_mul (norm_cosh_le_exp_norm _) (norm_quartetProduct_le δ _) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = Real.exp ((1 + 4 * S) * ‖s - 1 / 2‖) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((1 + 4 * S) * (‖s‖ + 1 / 2)) := by
        gcongr
    _ = Real.exp ((1 + 4 * S) / 2) * Real.exp ((1 + 4 * S) * ‖s‖) := by
        rw [← Real.exp_add]; ring_nf

/-- The cosh factor vanishes only on the critical line. -/
theorem re_eq_zero_of_cosh_eq_zero {w : ℂ} (h : Complex.cosh w = 0) : w.re = 0 := by
  rw [← Complex.cos_mul_I] at h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hre := congrArg Complex.im hk
  have : (w * I).im = w.re := by simp
  rw [this] at hre
  rw [hre]
  simp

/-- **Linear-density critical-line zeros**: `G(½ + i(2k + 1)π/2) = 0`. -/
theorem approachingModel_critical_zero (δ : ℕ → ℝ) (k : ℤ) :
    approachingModel δ (1 / 2 + (((2 * k + 1) * Real.pi / 2 : ℝ) : ℂ) * I) = 0 := by
  rw [approachingModel, add_sub_cancel_left, Complex.cosh_mul_I]
  have : Complex.cos (((2 * k + 1) * Real.pi / 2 : ℝ) : ℂ) = 0 :=
    Complex.cos_eq_zero_iff.mpr ⟨k, by push_cast; ring⟩
  rw [this, zero_mul]

/-- **The zeros of `G`**: the critical line and the planted quartets `½ ± δ_n ± iγ_n`. -/
theorem approachingModel_eq_zero_iff (δ : ℕ → ℝ) (s : ℂ) :
    approachingModel δ s = 0 ↔
      Complex.cosh (s - 1 / 2) = 0 ∨
        ∃ n, s - 1 / 2 = plantZero δ n ∨ s - 1 / 2 = -plantZero δ n ∨
          s - 1 / 2 = conj (plantZero δ n) ∨ s - 1 / 2 = -conj (plantZero δ n) := by
  rw [approachingModel, mul_eq_zero, quartetProduct_eq_zero_iff]
  simp only [quartetFactor_eq_zero_iff]

/-- Real parts of the zeros of `G`: `½` or `½ ± δ_n`. -/
theorem re_of_approachingModel_eq_zero (δ : ℕ → ℝ) {s : ℂ} (hs : approachingModel δ s = 0) :
    s.re = 1 / 2 ∨ ∃ n, s.re = 1 / 2 + δ n ∨ s.re = 1 / 2 - δ n := by
  rcases (approachingModel_eq_zero_iff δ s).mp hs with h | ⟨n, h | h | h | h⟩
  · left
    have := re_eq_zero_of_cosh_eq_zero h
    simp at this; linarith
  all_goals
    right; refine ⟨n, ?_⟩
    have hre := congrArg Complex.re h
    simp [plantZero] at hre
  · left; linarith
  · right; linarith
  · left; linarith
  · right; linarith

/-! ### The strip configuration and the failure of landing -/

variable {δ : ℕ → ℝ}

/-- The strip configuration of the zeros of `G` (multiplicity one). -/
def approachingConfig (hδ0 : ∀ n, 0 < δ n) (hδ12 : ∀ n, δ n < 1 / 2) : ZeroConfig where
  carrier := {s | approachingModel δ s = 0}
  mult _ := 1
  one_le_mult _ _ := le_rfl
  strip s hs := by
    rcases re_of_approachingModel_eq_zero δ hs with h | ⟨n, h | h⟩ <;>
      constructor <;> linarith [hδ0 n, hδ12 n]
  reflect_mem s hs := by
    show approachingModel δ (1 - conj s) = 0
    rw [approachingModel_one_sub, approachingModel_conj, hs.out, map_zero]
  mult_reflect _ _ := rfl
  finite_window T₁ T₂ := by
    have hiso : ∀ z ∈ (univ : Set ℂ), ¬ (∀ᶠ w in 𝓝 z, approachingModel δ w = 0) := by
      intro z _ h
      have := ((differentiable_approachingModel δ).differentiableOn.analyticOnNhd
        isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ z) h (mem_univ (1 / 2 : ℂ))
      rw [approachingModel_half] at this
      exact one_ne_zero this
    refine (HTGeometry.finite_zeros_of_isCompact isOpen_univ
      (differentiable_approachingModel δ).differentiableOn hiso
      (isCompact_closedBall (0 : ℂ) (1 + |T₁| + |T₂|)) (subset_univ _)).subset ?_
    rintro s ⟨hs, h₁, h₂⟩
    refine ⟨?_, hs⟩
    rw [mem_closedBall, dist_zero_right]
    have hre : |s.re| ≤ 1 := by
      rcases re_of_approachingModel_eq_zero δ hs with h | ⟨n, h | h⟩ <;>
        rw [abs_le] <;> constructor <;> linarith [hδ0 n, hδ12 n]
    have him : |s.im| ≤ |T₁| + |T₂| := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le T₁, le_abs_self T₂, abs_nonneg T₁]
    linarith [Complex.norm_le_abs_re_add_abs_im s]

/-- **The functional equation admits a remainder that approaches the line without landing.** For
every depth sequence `0 < δ_n < ½` with `δ_n → 0`, the entire function `G` has the functional
equation, reality, exponential type, linear-density critical-line zeros, and a strip configuration
that approaches the line with infinitely many zeros off it. -/
theorem exists_approachingModel_not_landingLaw (hδ0 : ∀ n, 0 < δ n) (hδ12 : ∀ n, δ n < 1 / 2)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s, G (1 - s) = G s) ∧ (∀ s, G (conj s) = conj (G s)) ∧
      (∃ C B : ℝ, ∀ s, ‖G s‖ ≤ C * Real.exp (B * ‖s‖)) ∧
      (∀ k : ℤ, G (1 / 2 + (((2 * k + 1) * Real.pi / 2 : ℝ) : ℂ) * I) = 0) ∧
      ∃ Z : ZeroConfig, Z.carrier = {s | G s = 0} ∧ ApproachesLine Z ∧
        (rightOf Z 0).Infinite ∧ ¬ LandingLaw Z := by
  set Z := approachingConfig hδ0 hδ12
  -- the upper planted zeros `½ + α_n` are right of the line and pairwise distinct
  have hmem : ∀ n, (1 / 2 : ℂ) + plantZero δ n ∈ rightOf Z 0 := fun n => by
    refine ⟨(approachingModel_eq_zero_iff δ _).mpr (Or.inr ⟨n, Or.inl (by ring)⟩), ?_⟩
    simp only [add_re, plantZero_re]
    norm_num
    linarith [hδ0 n]
  have hinj : Function.Injective fun n => (1 / 2 : ℂ) + plantZero δ n := fun m n hmn => by
    have him := congrArg Complex.im hmn
    simp only [add_im, plantZero_im] at him
    norm_num at him
    have hpos : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) + 1 := fun k => by positivity
    have := (pow_left_injective₀ (hpos m) (hpos n) two_ne_zero) (by simpa [plantHeight] using him)
    exact_mod_cast (add_right_cancel this : (m : ℝ) = n)
  have hinf : (rightOf Z 0).Infinite :=
    (infinite_range_of_injective hinj).mono (range_subset_iff.mpr hmem)
  have hZAL : ApproachesLine Z := by
    intro h hh
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hδ.eventually (gt_mem_nhds hh))
    refine (((Finset.range N).finite_toSet.image fun n => (1 / 2 : ℂ) + plantZero δ n).union
      ((Finset.range N).finite_toSet.image fun n => (1 / 2 : ℂ) + conj (plantZero δ n))).subset ?_
    rintro s ⟨hs, hre⟩
    rcases (approachingModel_eq_zero_iff δ s).mp hs with hc | ⟨n, hn | hn | hn | hn⟩
    · have := re_eq_zero_of_cosh_eq_zero hc
      simp at this; linarith
    all_goals
      have hre' := congrArg Complex.re hn
      simp [plantZero] at hre'
    · have hnN : n < N := by
        by_contra hge; have := hN n (not_lt.mp hge); linarith
      exact Or.inl ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hnN), by rw [← hn]; ring⟩
    · linarith [hδ0 n]
    · have hnN : n < N := by
        by_contra hge; have := hN n (not_lt.mp hge); linarith
      exact Or.inr ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hnN), by rw [← hn]; ring⟩
    · linarith [hδ0 n]
  exact ⟨approachingModel δ, differentiable_approachingModel δ, approachingModel_one_sub δ,
    approachingModel_conj δ, norm_approachingModel_le δ, approachingModel_critical_zero δ,
    Z, rfl, hZAL, hinf, fun hL => hinf (hL hZAL)⟩

/-- A concrete instance: depths `δ_n = 1/(4(n + 1))`. -/
theorem exists_fe_function_approaching_without_landing :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s, G (1 - s) = G s) ∧ (∀ s, G (conj s) = conj (G s)) ∧
      (∃ C B : ℝ, ∀ s, ‖G s‖ ≤ C * Real.exp (B * ‖s‖)) ∧
      (∀ k : ℤ, G (1 / 2 + (((2 * k + 1) * Real.pi / 2 : ℝ) : ℂ) * I) = 0) ∧
      ∃ Z : ZeroConfig, Z.carrier = {s | G s = 0} ∧ ApproachesLine Z ∧
        (rightOf Z 0).Infinite ∧ ¬ LandingLaw Z := by
  refine exists_approachingModel_not_landingLaw (δ := fun n => 1 / (4 * ((n : ℝ) + 1)))
    (fun n => by positivity) (fun n => ?_) ?_
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h4 : Tendsto (fun n : ℕ => 4 * ((n : ℝ) + 1)) atTop atTop :=
      h.const_mul_atTop (by norm_num)
    simpa using h4.inv_tendsto_atTop

end GaloisForLFunctions.InfiniteRankWeilTheory
