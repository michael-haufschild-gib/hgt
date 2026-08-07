import Mathlib

/-!
# The exponential cone product

For two periods `a, b` in the upper half plane the double product

`Φ(z) = ∏_{j,k ≥ 0} (1 - e(j a + k b + z))`,   `e(w) = exp(2πi w)`,

converges absolutely and locally uniformly, because `‖e(j a + k b + z)‖` is a constant times
`A^j B^k` with `A = e^{-2π Im a} < 1` and `B = e^{-2π Im b} < 1`.  Its limit is entire and vanishes
exactly where one factor does, that is exactly on the quadrant-shaped set

`{z : ∃ j,k ≥ 0, ∃ m ∈ ℤ, z = m - j a - k b}`.

This product is the denominator of the elliptic gamma function; the numerator is the same product
evaluated at `a + b - z`.
-/

set_option maxHeartbeats 1000000

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology
open scoped BigOperators

/-! ### The additive character -/

/-- The additive character `e(w) = exp(2πi w)`. -/
noncomputable def expChar (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)

theorem norm_expChar (w : ℂ) : ‖expChar w‖ = Real.exp (-(2 * Real.pi) * w.im) := by
  rw [expChar, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem expChar_eq_one_iff (w : ℂ) : expChar w = 1 ↔ ∃ m : ℤ, w = (m : ℂ) := by
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  rw [expChar, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * w = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
      rw [hn]; ring
    exact mul_left_cancel₀ hne h2
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

/-! ### The cone product -/

/-- One factor of the cone product. -/
noncomputable def coneFactor (a b : ℂ) (n : ℕ × ℕ) (z : ℂ) : ℂ :=
  1 - expChar ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z)

/-- The exponential cone product over the first quadrant of exponent vectors. -/
noncomputable def coneProduct (a b : ℂ) (z : ℂ) : ℂ := ∏' n : ℕ × ℕ, coneFactor a b n z

theorem coneFactor_eq_zero_iff (a b : ℂ) (n : ℕ × ℕ) (z : ℂ) :
    coneFactor a b n z = 0 ↔ ∃ m : ℤ, (n.1 : ℂ) * a + (n.2 : ℂ) * b + z = (m : ℂ) := by
  rw [coneFactor, sub_eq_zero, eq_comm, expChar_eq_one_iff]

theorem differentiable_coneFactor (a b : ℂ) (n : ℕ × ℕ) :
    Differentiable ℂ (coneFactor a b n) := by
  unfold coneFactor expChar
  fun_prop

/-- The norm of one deviation term, in closed geometric form. -/
theorem norm_coneFactor_sub_one (a b : ℂ) (n : ℕ × ℕ) (z : ℂ) :
    ‖coneFactor a b n z - 1‖
      = Real.exp (-(2 * Real.pi) * z.im) * (Real.exp (-(2 * Real.pi) * a.im) ^ n.1
        * Real.exp (-(2 * Real.pi) * b.im) ^ n.2) := by
  have hsub : coneFactor a b n z - 1 = -expChar ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z) := by
    rw [coneFactor]; ring
  rw [hsub, norm_neg, norm_expChar]
  have him : ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z).im = n.1 * a.im + n.2 * b.im + z.im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [him, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Summability of the deviation terms. -/
theorem summable_norm_coneFactor_sub_one {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    Summable fun n : ℕ × ℕ => ‖coneFactor a b n z - 1‖ := by
  set A : ℝ := Real.exp (-(2 * Real.pi) * a.im) with hA
  set B : ℝ := Real.exp (-(2 * Real.pi) * b.im) with hB
  have hApos : 0 ≤ A := (Real.exp_pos _).le
  have hBpos : 0 ≤ B := (Real.exp_pos _).le
  have hA1 : A < 1 := by
    rw [hA, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hB1 : B < 1 := by
    rw [hB, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hgeo : Summable fun n : ℕ × ℕ => A ^ n.1 * B ^ n.2 :=
    Summable.mul_of_nonneg (summable_geometric_of_lt_one hApos hA1)
      (summable_geometric_of_lt_one hBpos hB1) (fun _ => pow_nonneg hApos _)
      (fun _ => pow_nonneg hBpos _)
  refine (hgeo.mul_left (Real.exp (-(2 * Real.pi) * z.im))).congr fun n => ?_
  rw [norm_coneFactor_sub_one]

theorem multipliable_coneFactor {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    Multipliable fun n : ℕ × ℕ => coneFactor a b n z := by
  have hs : Summable fun n : ℕ × ℕ => ‖coneFactor a b n z - 1‖ :=
    summable_norm_coneFactor_sub_one ha hb z
  have := multipliable_one_add_of_summable (f := fun n : ℕ × ℕ => coneFactor a b n z - 1) hs
  refine this.congr fun n => ?_
  ring

/-- **The cone product vanishes exactly where a factor does.** -/
theorem coneProduct_eq_zero_iff {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    coneProduct a b z = 0 ↔ ∃ n : ℕ × ℕ, coneFactor a b n z = 0 := by
  constructor
  · intro h
    by_contra hcon
    simp only [not_exists] at hcon
    have hne : ∀ n : ℕ × ℕ, 1 + (coneFactor a b n z - 1) ≠ 0 := by
      intro n
      have : (1 : ℂ) + (coneFactor a b n z - 1) = coneFactor a b n z := by ring
      rw [this]
      exact hcon n
    have hprod : ∏' n : ℕ × ℕ, (1 + (coneFactor a b n z - 1)) ≠ 0 :=
      tprod_one_add_ne_zero_of_summable hne (summable_norm_coneFactor_sub_one ha hb z)
    apply hprod
    rw [← h, coneProduct]
    exact tprod_congr fun n => by ring
  · intro h
    exact tprod_of_exists_eq_zero h

/-! ### Holomorphy -/

theorem hasProdLocallyUniformlyOn_coneFactor {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    HasProdLocallyUniformlyOn (coneFactor a b) (coneProduct a b) Set.univ := by
  classical
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_norm (E := ℂ)).continuousOn
  set R : ℝ := max C 0 with hR
  have hRnn : (0 : ℝ) ≤ R := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz =>
    (hC (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
  set A : ℝ := Real.exp (-(2 * Real.pi) * a.im) with hA
  set B : ℝ := Real.exp (-(2 * Real.pi) * b.im) with hB
  have hApos : 0 ≤ A := (Real.exp_pos _).le
  have hBpos : 0 ≤ B := (Real.exp_pos _).le
  have hA1 : A < 1 := by
    rw [hA, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hB1 : B < 1 := by
    rw [hB, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  set u : ℕ × ℕ → ℝ := fun n => Real.exp (2 * Real.pi * R) * (A ^ n.1 * B ^ n.2) with hu
  have husum : Summable u :=
    (Summable.mul_of_nonneg (summable_geometric_of_lt_one hApos hA1)
      (summable_geometric_of_lt_one hBpos hB1) (fun _ => pow_nonneg hApos _)
      (fun _ => pow_nonneg hBpos _)).mul_left _
  have hbound : ∀ᶠ n : ℕ × ℕ in cofinite, ∀ z ∈ K, ‖coneFactor a b n z - 1‖ ≤ u n := by
    refine Filter.Eventually.of_forall fun n z hz => ?_
    rw [norm_coneFactor_sub_one, hu]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have him : |z.im| ≤ R := (abs_im_le_norm z).trans (hKR z hz)
    nlinarith [Real.pi_pos, abs_le.mp him]
  have hcont : ∀ n : ℕ × ℕ, ContinuousOn (fun z => coneFactor a b n z - 1) K := fun n =>
    ((differentiable_coneFactor a b n).continuous.sub continuous_const).continuousOn
  have hprod := Summable.hasProdUniformlyOn_one_add hK husum hbound hcont
  have heq : (fun (n : ℕ × ℕ) (z : ℂ) => 1 + (coneFactor a b n z - 1)) = coneFactor a b := by
    funext n z; ring
  have heq2 : (fun z : ℂ => ∏' n : ℕ × ℕ, (1 + (coneFactor a b n z - 1))) = coneProduct a b := by
    funext z
    rw [coneProduct]
    exact tprod_congr fun n => by ring
  rw [heq, heq2] at hprod
  exact hprod

/-- **The cone product is entire.** -/
theorem differentiable_coneProduct {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    Differentiable ℂ (coneProduct a b) := by
  have ht : TendstoLocallyUniformlyOn
      (fun (S : Finset (ℕ × ℕ)) (z : ℂ) => ∏ n ∈ S, coneFactor a b n z)
      (coneProduct a b) atTop Set.univ :=
    hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      (hasProdLocallyUniformlyOn_coneFactor ha hb)
  have hd : ∀ᶠ S : Finset (ℕ × ℕ) in atTop,
      DifferentiableOn ℂ (fun z => ∏ n ∈ S, coneFactor a b n z) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_coneFactor a b n).differentiableOn
  have := ht.differentiableOn hd isOpen_univ
  exact fun z => (this.differentiableAt (by simp))

/-! ### The punctured product and simplicity of the zeros -/

/-- The cone product with one factor removed. -/
noncomputable def conePunctured (a b : ℂ) (n₀ : ℕ × ℕ) (z : ℂ) : ℂ :=
  ∏' n : ℕ × ℕ, (if n = n₀ then 1 else coneFactor a b n z)

theorem norm_conePunctured_term_le (a b : ℂ) (n₀ n : ℕ × ℕ) (z : ℂ) :
    ‖(if n = n₀ then 1 else coneFactor a b n z) - 1‖ ≤ ‖coneFactor a b n z - 1‖ := by
  by_cases h : n = n₀ <;> simp [h]

theorem summable_norm_conePunctured {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (n₀ : ℕ × ℕ) (z : ℂ) :
    Summable fun n : ℕ × ℕ => ‖(if n = n₀ then 1 else coneFactor a b n z) - 1‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_conePunctured_term_le a b n₀ · z)
    (summable_norm_coneFactor_sub_one ha hb z)

theorem multipliable_conePunctured {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (n₀ : ℕ × ℕ) (z : ℂ) :
    Multipliable fun n : ℕ × ℕ => (if n = n₀ then 1 else coneFactor a b n z) := by
  have := multipliable_one_add_of_summable
    (f := fun n : ℕ × ℕ => (if n = n₀ then 1 else coneFactor a b n z) - 1)
    (summable_norm_conePunctured ha hb n₀ z)
  refine this.congr fun n => ?_
  ring

/-- **Splitting off one factor.** -/
theorem coneProduct_eq_factor_mul_punctured {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (n₀ : ℕ × ℕ) (z : ℂ) :
    coneProduct a b z = coneFactor a b n₀ z * conePunctured a b n₀ z := by
  classical
  have hupd : Multipliable (Function.update (fun n : ℕ × ℕ => coneFactor a b n z) n₀ 1) := by
    refine (multipliable_conePunctured ha hb n₀ z).congr fun n => ?_
    by_cases h : n = n₀ <;> simp [h, Function.update]
  rw [coneProduct, conePunctured]
  exact Multipliable.tprod_eq_mul_tprod_ite' (f := fun n : ℕ × ℕ => coneFactor a b n z) n₀ hupd

/-- The punctured product does not vanish where every remaining factor is nonzero. -/
theorem conePunctured_ne_zero {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    {n₀ : ℕ × ℕ} {z : ℂ} (h : ∀ n : ℕ × ℕ, n ≠ n₀ → coneFactor a b n z ≠ 0) :
    conePunctured a b n₀ z ≠ 0 := by
  classical
  have hne : ∀ n : ℕ × ℕ, 1 + ((if n = n₀ then 1 else coneFactor a b n z) - 1) ≠ 0 := by
    intro n
    have heq : (1 : ℂ) + ((if n = n₀ then 1 else coneFactor a b n z) - 1)
        = (if n = n₀ then 1 else coneFactor a b n z) := by ring
    rw [heq]
    by_cases hn : n = n₀
    · simp [hn]
    · simpa [hn] using h n hn
  have hprod := tprod_one_add_ne_zero_of_summable hne (summable_norm_conePunctured ha hb n₀ z)
  intro hzero
  apply hprod
  rw [← hzero, conePunctured]
  exact tprod_congr fun n => by ring

theorem hasProdLocallyUniformlyOn_conePunctured {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (n₀ : ℕ × ℕ) :
    HasProdLocallyUniformlyOn (fun n z => if n = n₀ then 1 else coneFactor a b n z)
      (conePunctured a b n₀) Set.univ := by
  classical
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_norm (E := ℂ)).continuousOn
  set R : ℝ := max C 0 with hR
  have hRnn : (0 : ℝ) ≤ R := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz =>
    (hC (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
  set A : ℝ := Real.exp (-(2 * Real.pi) * a.im) with hA
  set B : ℝ := Real.exp (-(2 * Real.pi) * b.im) with hB
  have hApos : 0 ≤ A := (Real.exp_pos _).le
  have hBpos : 0 ≤ B := (Real.exp_pos _).le
  have hA1 : A < 1 := by rw [hA, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hB1 : B < 1 := by rw [hB, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  set u : ℕ × ℕ → ℝ := fun n => Real.exp (2 * Real.pi * R) * (A ^ n.1 * B ^ n.2) with hu
  have husum : Summable u :=
    (Summable.mul_of_nonneg (summable_geometric_of_lt_one hApos hA1)
      (summable_geometric_of_lt_one hBpos hB1) (fun _ => pow_nonneg hApos _)
      (fun _ => pow_nonneg hBpos _)).mul_left _
  have hbound : ∀ᶠ n : ℕ × ℕ in cofinite,
      ∀ z ∈ K, ‖(if n = n₀ then 1 else coneFactor a b n z) - 1‖ ≤ u n := by
    refine Filter.Eventually.of_forall fun n z hz => ?_
    refine (norm_conePunctured_term_le a b n₀ n z).trans ?_
    rw [norm_coneFactor_sub_one, hu]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have him : |z.im| ≤ R := (abs_im_le_norm z).trans (hKR z hz)
    nlinarith [Real.pi_pos, abs_le.mp him]
  have hcont : ∀ n : ℕ × ℕ,
      ContinuousOn (fun z => (if n = n₀ then 1 else coneFactor a b n z) - 1) K := by
    intro n
    by_cases h : n = n₀
    · have hfun : (fun z : ℂ => (if n = n₀ then (1 : ℂ) else coneFactor a b n z) - 1)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z; simp [h]
      rw [hfun]
      exact continuousOn_const
    · simp only [if_neg h]
      exact ((differentiable_coneFactor a b n).continuous.continuousOn).sub continuousOn_const
  have hprod := Summable.hasProdUniformlyOn_one_add hK husum hbound hcont
  have heq : (fun (n : ℕ × ℕ) (z : ℂ) => 1 + ((if n = n₀ then 1 else coneFactor a b n z) - 1))
      = fun n z => if n = n₀ then 1 else coneFactor a b n z := by
    funext n z; ring
  have heq2 : (fun z : ℂ => ∏' n : ℕ × ℕ, (1 + ((if n = n₀ then 1 else coneFactor a b n z) - 1)))
      = conePunctured a b n₀ := by
    funext z
    rw [conePunctured]
    exact tprod_congr fun n => by ring
  rw [heq, heq2] at hprod
  exact hprod

/-- The punctured product is entire. -/
theorem differentiable_conePunctured {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (n₀ : ℕ × ℕ) :
    Differentiable ℂ (conePunctured a b n₀) := by
  classical
  have ht : TendstoLocallyUniformlyOn
      (fun (S : Finset (ℕ × ℕ)) (z : ℂ) => ∏ n ∈ S, (if n = n₀ then 1 else coneFactor a b n z))
      (conePunctured a b n₀) atTop Set.univ :=
    hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      (hasProdLocallyUniformlyOn_conePunctured ha hb n₀)
  have hd : ∀ᶠ S : Finset (ℕ × ℕ) in atTop,
      DifferentiableOn ℂ (fun z => ∏ n ∈ S, (if n = n₀ then 1 else coneFactor a b n z))
        Set.univ := by
    filter_upwards with S
    refine DifferentiableOn.fun_finsetProd fun n _ => ?_
    by_cases h : n = n₀
    · have hfun : (fun z : ℂ => if n = n₀ then (1 : ℂ) else coneFactor a b n z)
          = fun _ : ℂ => (1 : ℂ) := by
        funext z; simp [h]
      rw [hfun]
      exact differentiableOn_const 1
    · simp only [if_neg h]
      exact (differentiable_coneFactor a b n).differentiableOn
  have := ht.differentiableOn hd isOpen_univ
  exact fun z => (this.differentiableAt (by simp))

/-! ### Simple zeros -/

theorem hasDerivAt_coneFactor (a b : ℂ) (n : ℕ × ℕ) (z : ℂ) :
    HasDerivAt (coneFactor a b n)
      (-(expChar ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z) * (2 * (Real.pi : ℂ) * Complex.I))) z := by
  have h1 : HasDerivAt
      (fun w : ℂ => 2 * (Real.pi : ℂ) * Complex.I * ((n.1 : ℂ) * a + (n.2 : ℂ) * b + w))
      (2 * (Real.pi : ℂ) * Complex.I) z := by
    simpa using (((hasDerivAt_id z).const_add ((n.1 : ℂ) * a + (n.2 : ℂ) * b)).const_mul
      (2 * (Real.pi : ℂ) * Complex.I))
  exact h1.cexp.const_sub 1

/-- **Every zero of a cone factor is simple.** -/
theorem analyticOrderAt_coneFactor_eq_one {a b : ℂ} {n : ℕ × ℕ} {z : ℂ}
    (h : coneFactor a b n z = 0) : analyticOrderAt (coneFactor a b n) z = 1 := by
  have hchar : expChar ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z) = 1 := by
    have := h
    rw [coneFactor, sub_eq_zero] at this
    exact this.symm
  have hderiv : deriv (coneFactor a b n) z = -(2 * (Real.pi : ℂ) * Complex.I) := by
    rw [(hasDerivAt_coneFactor a b n z).deriv, hchar, one_mul]
  have hne : deriv (coneFactor a b n) z ≠ 0 := by
    rw [hderiv]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi, Complex.I_ne_zero]
  have hiff := analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    ((differentiable_coneFactor a b n).analyticAt z) (n := 1)
  rw [Nat.cast_one] at hiff
  rw [hiff]
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    simpa using h
  · simpa [iteratedDeriv_one] using hne

/-- **The cone product has a simple zero at a point with exactly one vanishing factor.** -/
theorem analyticOrderAt_coneProduct_eq_one {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    {n₀ : ℕ × ℕ} {z : ℂ} (h0 : coneFactor a b n₀ z = 0)
    (huniq : ∀ n : ℕ × ℕ, n ≠ n₀ → coneFactor a b n z ≠ 0) :
    analyticOrderAt (coneProduct a b) z = 1 := by
  have hsplit : coneProduct a b = coneFactor a b n₀ * conePunctured a b n₀ := by
    funext w
    exact coneProduct_eq_factor_mul_punctured ha hb n₀ w
  rw [hsplit, analyticOrderAt_mul ((differentiable_coneFactor a b n₀).analyticAt z)
    ((differentiable_conePunctured ha hb n₀).analyticAt z),
    analyticOrderAt_coneFactor_eq_one h0,
    analyticOrderAt_eq_zero.mpr (Or.inr (conePunctured_ne_zero ha hb huniq))]
  simp

/-! ### The single-index product and the shift relations -/

/-- One factor of the single-index product. -/
noncomputable def singleFactor (b : ℂ) (k : ℕ) (z : ℂ) : ℂ := 1 - expChar ((k : ℂ) * b + z)

/-- The single-index product `∏_{k ≥ 0} (1 - e(k b + z))`. -/
noncomputable def singleProduct (b : ℂ) (z : ℂ) : ℂ := ∏' k : ℕ, singleFactor b k z

theorem norm_singleFactor_sub_one (b : ℂ) (k : ℕ) (z : ℂ) :
    ‖singleFactor b k z - 1‖
      = Real.exp (-(2 * Real.pi) * z.im) * Real.exp (-(2 * Real.pi) * b.im) ^ k := by
  have hsub : singleFactor b k z - 1 = -expChar ((k : ℂ) * b + z) := by
    rw [singleFactor]; ring
  rw [hsub, norm_neg, norm_expChar]
  have him : ((k : ℂ) * b + z).im = k * b.im + z.im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [him, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem summable_norm_singleFactor_sub_one {b : ℂ} (hb : 0 < b.im) (z : ℂ) :
    Summable fun k : ℕ => ‖singleFactor b k z - 1‖ := by
  set B : ℝ := Real.exp (-(2 * Real.pi) * b.im) with hB
  have hBpos : 0 ≤ B := (Real.exp_pos _).le
  have hB1 : B < 1 := by rw [hB, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  refine ((summable_geometric_of_lt_one hBpos hB1).mul_left
    (Real.exp (-(2 * Real.pi) * z.im))).congr fun k => ?_
  rw [norm_singleFactor_sub_one]

theorem multipliable_singleFactor {b : ℂ} (hb : 0 < b.im) (z : ℂ) :
    Multipliable fun k : ℕ => singleFactor b k z := by
  have := multipliable_one_add_of_summable
    (f := fun k : ℕ => singleFactor b k z - 1) (summable_norm_singleFactor_sub_one hb z)
  refine this.congr fun k => ?_
  ring

/-- **The single-index product shifts by one factor.** -/
theorem singleProduct_shift {b : ℂ} (hb : 0 < b.im) (z : ℂ) :
    singleProduct b z = (1 - expChar z) * singleProduct b (z + b) := by
  have hstep : (fun k : ℕ => singleFactor b (k + 1) z)
      = fun k : ℕ => singleFactor b k (z + b) := by
    funext k
    rw [singleFactor, singleFactor]
    congr 2
    push_cast
    ring
  have hm : Multipliable fun k : ℕ => singleFactor b (k + 1) z := by
    rw [hstep]
    exact multipliable_singleFactor hb _
  have h0 : singleFactor b 0 z = 1 - expChar z := by
    rw [singleFactor]
    norm_num
  show (∏' k : ℕ, singleFactor b k z) = (1 - expChar z) * ∏' k : ℕ, singleFactor b k (z + b)
  rw [tprod_eq_zero_mul' hm, hstep, h0]

/-- Fubini for the cone product: it is the product over `j` of shifted single-index products. -/
theorem hasProd_singleProduct_shifted {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    HasProd (fun j : ℕ => singleProduct b (z + (j : ℂ) * a)) (coneProduct a b z) := by
  have hbase : HasProd (fun n : ℕ × ℕ => coneFactor a b n z) (coneProduct a b z) :=
    (multipliable_coneFactor ha hb z).hasProd
  refine HasProd.prod_fiberwise hbase fun j => ?_
  have hfib : (fun k : ℕ => coneFactor a b (j, k) z)
      = fun k : ℕ => singleFactor b k (z + (j : ℂ) * a) := by
    funext k
    rw [coneFactor, singleFactor]
    congr 2
    ring
  rw [hfib]
  exact (multipliable_singleFactor hb _).hasProd

/-- **The cone product shifts by one single-index product.** -/
theorem coneProduct_shift {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    coneProduct a b z = singleProduct b z * coneProduct a b (z + a) := by
  have h1 := hasProd_singleProduct_shifted ha hb z
  have h2 := hasProd_singleProduct_shifted ha hb (z + a)
  have hstep : (fun j : ℕ => singleProduct b (z + ((j + 1 : ℕ) : ℂ) * a))
      = fun j : ℕ => singleProduct b (z + a + (j : ℂ) * a) := by
    funext j
    congr 1
    push_cast
    ring
  have hm : Multipliable fun j : ℕ => singleProduct b (z + ((j + 1 : ℕ) : ℂ) * a) := by
    rw [hstep]
    exact h2.multipliable
  rw [← h1.tprod_eq, tprod_eq_zero_mul' hm, hstep, h2.tprod_eq]
  congr 2
  push_cast
  ring

/-- The cone product is symmetric in its two periods. -/
theorem coneProduct_comm (a b : ℂ) (z : ℂ) : coneProduct a b z = coneProduct b a z := by
  rw [coneProduct, coneProduct]
  rw [← (Equiv.prodComm ℕ ℕ).tprod_eq (fun n : ℕ × ℕ => coneFactor b a n z)]
  refine tprod_congr fun n => ?_
  rw [coneFactor, coneFactor]
  congr 2
  simp [Equiv.prodComm]
  ring

end GaloisForLFunctions.HTGeometry
