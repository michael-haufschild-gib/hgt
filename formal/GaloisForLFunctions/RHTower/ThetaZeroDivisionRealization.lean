import GaloisForLFunctions.RHTower.ThetaRelativeSourceRigidity

/-!
# Successive complex zero divisions of the theta source and divisor quotients

* A complex zero division `T_α f(x) = α ∫₀^∞ sin(αt) f(|x|+t) dt` of a source bounded by `C k` is
  bounded by `C' e^{-2|x|} k(x)`; the first-atom tail of `k` absorbs `|sin(αt)| ≤ e^{|Im α| t}`.
* For a list `L` of zeros of `F = XiC` in the right half-plane, each used at most with its
  multiplicity, the successive divisions `G_L` of `k` satisfy `Ĝ_L(z) P_L(z) = F(z)` with
  `P_L(z) = ∏_{β ∈ L} (1 - z²/β²)`: at each step the remaining transform still vanishes at the divided
  zero because `P_L` vanishes there only to the order `count β L`.
* **Realization.**  For every polynomial `e` with `deg e ≤ |L|` some even theta-dominated source `u`
  has `û(z) P_L(z) = F(z) e(z²)`, with `u - c k = o(k)` at both ends and
  `c = e_{|L|} ∏_{β ∈ L} (-β²)`.  Peeling the factor of the first zero,
  `e(w) = e(β²) + (w - β²) e₁(w)` gives `u = e(β²) G_{β::L} - β² u₁`.
* The real part of an even source has transform `(û(z) + conj û(conj z))/2`.
-/
open MeasureTheory Set Filter Topology Complex

namespace RHTower

noncomputable section

/-! ## Relative bounds for zero divisions of theta-dominated sources -/

open HedenmalmThetaSource in
theorem norm_outwardSine_le_tail_of_le {f : ℝ → ℂ} (hf : ExpMomentSource f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C * thetaCuspFullSource x) (α : ℂ) {y : ℝ} (hy1 : 1 ≤ y)
    (hyα : |α.im| ≤ y) :
    ‖outwardSine α f y‖ ≤
      C * (2 * ‖α‖ * thetaEnvelopeUpper / (Real.pi * thetaEnvelopeLower)) *
        Real.exp (-(2 * y)) * thetaCuspFullSource y := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (thetaCuspFullSource_pos 0)
  set r := Real.pi * Real.exp (2 * y)
  set a := |α.im| - r
  have hr2 : 2 * |α.im| ≤ r := by
    have h1 := Real.add_one_le_exp (2 * y)
    have := Real.pi_gt_three
    have : 0 ≤ Real.exp (2 * y) := (Real.exp_pos _).le
    dsimp only [r]; nlinarith [abs_nonneg α.im]
  have hrpos : 0 < r := by positivity
  have ha : a < 0 := by dsimp only [a]; have := abs_nonneg α.im; linarith
  have hU := thetaEnvelopeUpper_pos
  have hL := thetaEnvelopeLower_pos
  have hE := thetaEnvelope_pos y
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖Complex.sin (α * t) * f (y + t)‖ ≤
      C * (thetaEnvelopeUpper * thetaEnvelope y * Real.exp (a * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul]
    have hs := norm_csin_mul_ofReal_le α t
    rw [abs_of_pos ht0] at hs
    have hk := thetaCuspFullSource_le_shift hy1 (by linarith : y ≤ y + t)
    rw [show y + t - y = t by ring] at hk
    calc ‖Complex.sin (α * t)‖ * ‖f (y + t)‖
        ≤ Real.exp (|α.im| * t) * (C * (thetaEnvelopeUpper * thetaEnvelope y *
            Real.exp (-r * t))) :=
          mul_le_mul hs ((hC _).trans (mul_le_mul_of_nonneg_left hk hC0)) (norm_nonneg _)
            (Real.exp_pos _).le
      _ = C * (thetaEnvelopeUpper * thetaEnvelope y * Real.exp (a * t)) := by
          rw [show a * t = |α.im| * t + -r * t by dsimp only [a]; ring, Real.exp_add]; ring
  have hint : IntegrableOn (fun t : ℝ => C * (thetaEnvelopeUpper * thetaEnvelope y *
      Real.exp (a * t))) (Ioi 0) := ((integrableOn_exp_mul_Ioi ha 0).const_mul _).const_mul _
  have hval : (∫ t in Ioi (0 : ℝ), C * (thetaEnvelopeUpper * thetaEnvelope y * Real.exp (a * t))) =
      C * (thetaEnvelopeUpper * thetaEnvelope y / (r - |α.im|)) := by
    rw [integral_const_mul, integral_const_mul, integral_exp_mul_Ioi ha 0]
    simp only [mul_zero, Real.exp_zero]
    rw [show a = -(r - |α.im|) by dsimp only [a]; ring, neg_div_neg_eq]
    ring
  have hEk := thetaCuspFullSource_ge_envelope (by linarith : (0 : ℝ) < y)
  unfold outwardSine
  rw [norm_mul]
  have hI : ‖∫ t in Ioi (0 : ℝ), Complex.sin (α * t) * f (y + t)‖ ≤
      C * (thetaEnvelopeUpper * thetaEnvelope y / (r - |α.im|)) := by
    rw [← hval]
    exact (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
      (hf.integrable_sin_shift α y).integrableOn.norm hint measurableSet_Ioi hbound)
  have hden : r / 2 ≤ r - |α.im| := by linarith
  have hEle : thetaEnvelope y ≤ thetaCuspFullSource y / thetaEnvelopeLower := by
    rw [le_div_iff₀ hL]; linarith
  calc ‖α‖ * ‖∫ t in Ioi (0 : ℝ), Complex.sin (α * t) * f (y + t)‖
      ≤ ‖α‖ * (C * (thetaEnvelopeUpper * thetaEnvelope y / (r - |α.im|))) :=
        mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ ≤ ‖α‖ * (C * (thetaEnvelopeUpper * (thetaCuspFullSource y / thetaEnvelopeLower) /
          (r / 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (div_le_div₀ (mul_nonneg hU.le
          (div_nonneg (thetaCuspFullSource_pos y).le hL.le)) (mul_le_mul_of_nonneg_left hEle hU.le)
          (by positivity) hden) hC0) (norm_nonneg _)
    _ = C * (2 * ‖α‖ * thetaEnvelopeUpper / (Real.pi * thetaEnvelopeLower)) *
          (1 / Real.exp (2 * y)) * thetaCuspFullSource y := by
        dsimp only [r]; field_simp
    _ = C * (2 * ‖α‖ * thetaEnvelopeUpper / (Real.pi * thetaEnvelopeLower)) *
          Real.exp (-(2 * y)) * thetaCuspFullSource y := by
        rw [Real.exp_neg, one_div]

/-- **Relative bound.**  A complex zero division of a theta-dominated source is bounded by
`C e^{-2|x|} k(x)`. -/
theorem exists_norm_zeroDivision_le_of_le {f : ℝ → ℂ} (hf : ExpMomentSource f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C * thetaCuspFullSource x) (α : ℂ) :
    ∃ C', 0 ≤ C' ∧ ∀ x, ‖zeroDivision α f x‖ ≤
      C' * Real.exp (-(2 * |x|)) * thetaCuspFullSource x := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (thetaCuspFullSource_pos 0)
  set x₁ := max 1 |α.im|
  set C₁ := C * (2 * ‖α‖ * HedenmalmThetaSource.thetaEnvelopeUpper /
    (Real.pi * HedenmalmThetaSource.thetaEnvelopeLower))
  have hC₁ : 0 ≤ C₁ := by
    have := HedenmalmThetaSource.thetaEnvelopeUpper_pos
    have := HedenmalmThetaSource.thetaEnvelopeLower_pos
    positivity
  have hcont : ContinuousOn (fun x => ‖zeroDivision α f x‖ /
      (Real.exp (-(2 * |x|)) * thetaCuspFullSource x)) (Icc (-x₁) x₁) := by
    refine Continuous.continuousOn ?_
    refine (continuous_zeroDivision hf α).norm.div
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (-(2 * |x|))).mul
        contDiff_thetaCuspFullSource.continuous) fun x => ?_
    exact (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos x)).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ M, le_max_of_le_left hC₁, fun x => ?_⟩
  have hpos : 0 < Real.exp (-(2 * |x|)) * thetaCuspFullSource x :=
    mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos x)
  by_cases hx : |x| ≤ x₁
  · have hmem : x ∈ Icc (-x₁) x₁ := abs_le.mp hx
    have h := hM x hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le),
      div_le_iff₀ hpos] at h
    calc ‖zeroDivision α f x‖ ≤ M * (Real.exp (-(2 * |x|)) * thetaCuspFullSource x) := h
      _ ≤ max C₁ M * (Real.exp (-(2 * |x|)) * thetaCuspFullSource x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
      _ = _ := by ring
  · replace hx := not_le.mp hx
    have h1 : 1 ≤ |x| := le_trans (le_max_left _ _) hx.le
    have h2 : |α.im| ≤ |x| := le_trans (le_max_right _ _) hx.le
    have h := norm_outwardSine_le_tail_of_le hf hC α h1 h2
    have hk : thetaCuspFullSource |x| = thetaCuspFullSource x := by
      rcases abs_choice x with h' | h' <;> rw [h']
      exact thetaCuspFullSource_neg x
    rw [hk] at h
    calc ‖zeroDivision α f x‖ ≤ C₁ * Real.exp (-(2 * |x|)) * thetaCuspFullSource x := h
      _ ≤ max C₁ M * Real.exp (-(2 * |x|)) * thetaCuspFullSource x := by
          have h3 : C₁ ≤ max C₁ M := le_max_left _ _
          nlinarith [mul_le_mul_of_nonneg_right h3 hpos.le]

theorem exists_norm_zeroDivision_le_mul_of_le {f : ℝ → ℂ} (hf : ExpMomentSource f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C * thetaCuspFullSource x) (α : ℂ) :
    ∃ C', ∀ x, ‖zeroDivision α f x‖ ≤ C' * thetaCuspFullSource x := by
  obtain ⟨C', hC'0, hC'⟩ := exists_norm_zeroDivision_le_of_le hf hC α
  refine ⟨C', fun x => (hC' x).trans ?_⟩
  have h1 : Real.exp (-(2 * |x|)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg x])
  have := thetaCuspFullSource_pos x
  nlinarith [mul_le_mul_of_nonneg_left h1 hC'0]

/-! ## Successive zero divisions along a list of zeros -/

/-- Successive zero divisions of the theta source `k` along a list of zeros. -/
def thetaListDivision : List ℂ → ℝ → ℂ
  | [] => thetaSourceC
  | β :: L => zeroDivision β (thetaListDivision L)

/-- The divisor `P_L(z) = ∏_{β ∈ L} (1 - z²/β²)`. -/
def listDivisor (L : List ℂ) (z : ℂ) : ℂ := (L.map fun β => 1 - z ^ 2 / β ^ 2).prod

theorem listDivisor_cons (β : ℂ) (L : List ℂ) (z : ℂ) :
    listDivisor (β :: L) z = (1 - z ^ 2 / β ^ 2) * listDivisor L z := by
  simp [listDivisor]

theorem listDivisor_nil (z : ℂ) : listDivisor [] z = 1 := by simp [listDivisor]

theorem differentiable_listDivisor (L : List ℂ) : Differentiable ℂ (listDivisor L) := by
  induction L with
  | nil =>
    have : listDivisor [] = fun _ => 1 := funext listDivisor_nil
    rw [this]; exact differentiable_const 1
  | cons β L ih =>
    have : listDivisor (β :: L) = fun z => (1 - z ^ 2 / β ^ 2) * listDivisor L z :=
      funext (listDivisor_cons β L)
    rw [this]
    exact ((differentiable_const _).sub ((differentiable_pow 2).div_const _)).mul ih

theorem listDivisor_neg (L : List ℂ) (z : ℂ) : listDivisor L (-z) = listDivisor L z := by
  simp [listDivisor]

theorem expMomentSource_thetaListDivision (L : List ℂ) :
    ExpMomentSource (thetaListDivision L) := by
  induction L with
  | nil => exact expMomentSource_thetaSourceC
  | cons β L ih => exact expMomentSource_zeroDivision ih β

theorem thetaListDivision_neg (L : List ℂ) (x : ℝ) :
    thetaListDivision L (-x) = thetaListDivision L x := by
  cases L with
  | nil => exact thetaSourceC_neg x
  | cons β L => exact zeroDivision_neg β _ x

theorem exists_norm_thetaListDivision_le (L : List ℂ) :
    ∃ C, ∀ x, ‖thetaListDivision L x‖ ≤ C * thetaCuspFullSource x := by
  induction L with
  | nil => exact ⟨1, fun x => by
      rw [show thetaListDivision [] x = thetaSourceC x from rfl, thetaSourceC, Complex.norm_real,
        Real.norm_of_nonneg (thetaCuspFullSource_pos x).le, one_mul]⟩
  | cons β L ih =>
    obtain ⟨C, hC⟩ := ih
    exact exists_norm_zeroDivision_le_mul_of_le (expMomentSource_thetaListDivision L) hC β

/-- Zero divisions along a nonempty list are small relative to `k` at both ends. -/
theorem tendsto_thetaListDivision_div (β : ℂ) (L : List ℂ) :
    Tendsto (fun x => ‖thetaListDivision (β :: L) x‖ / thetaCuspFullSource x) (cocompact ℝ)
      (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_norm_thetaListDivision_le L
  obtain ⟨C', hC'0, hC'⟩ :=
    exists_norm_zeroDivision_le_of_le (expMomentSource_thetaListDivision L) hC β
  have hlim : Tendsto (fun x : ℝ => C' * Real.exp (-(2 * |x|))) (cocompact ℝ) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop :=
      (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun x => Real.norm_eq_abs x
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(2 * |x|))) (cocompact ℝ) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).comp h)
    simpa using h2.const_mul C'
  refine squeeze_zero (fun x => div_nonneg (norm_nonneg _) (thetaCuspFullSource_pos x).le)
    (fun x => ?_) hlim
  rw [div_le_iff₀ (thetaCuspFullSource_pos x)]
  exact hC' x

/-! ## Orders of the divisor -/

theorem analyticOrderAt_one_sub_sq_div_sq {β β' : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re) :
    analyticOrderAt (fun z : ℂ => 1 - z ^ 2 / β' ^ 2) β = if β' = β then 1 else 0 := by
  have hA : AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 2 / β' ^ 2) β := by fun_prop
  have hβ'0 : β' ≠ 0 := fun h => by rw [h] at hβ'; simp at hβ'
  split_ifs with h
  · subst h
    rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, hA.analyticOrderAt_eq_natCast]
    refine ⟨fun z => -(z + β') / β' ^ 2, by fun_prop, ?_, Eventually.of_forall fun z => ?_⟩
    · have : β' + β' ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; linarith
      simp only
      exact div_ne_zero (neg_ne_zero.2 this) (pow_ne_zero 2 hβ'0)
    · simp only [pow_one, smul_eq_mul]
      field_simp
      ring
  · rw [hA.analyticOrderAt_eq_zero]
    intro h0
    have hsq : β ^ 2 = β' ^ 2 := by
      have := sub_eq_zero.1 h0
      field_simp at this
      exact this.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
    · exact h h1.symm
    · have := congrArg Complex.re h1; simp at this; linarith

theorem analyticOrderAt_listDivisor {β : ℂ} (hβ : 0 < β.re) (L : List ℂ)
    (hL : ∀ β' ∈ L, 0 < β'.re) : analyticOrderAt (listDivisor L) β = L.count β := by
  induction L with
  | nil =>
    rw [(differentiable_listDivisor []).analyticAt β |>.analyticOrderAt_eq_zero |>.2]
    · simp
    · simp [listDivisor_nil]
  | cons β' L ih =>
    have hfun : listDivisor (β' :: L) = (fun z : ℂ => 1 - z ^ 2 / β' ^ 2) * listDivisor L :=
      funext (listDivisor_cons β' L)
    rw [hfun, analyticOrderAt_mul (by fun_prop) ((differentiable_listDivisor L).analyticAt β),
      analyticOrderAt_one_sub_sq_div_sq hβ (hL β' (List.mem_cons_self)),
      ih fun b hb => hL b (List.mem_cons_of_mem _ hb), List.count_cons]
    rcases eq_or_ne β' β with h | h
    · subst h
      simp only [if_true, beq_self_eq_true]
      push_cast
      ring
    · simp [h]

/-! ## Admissible division lists and their transforms -/

theorem ExpMomentSource.add {f g : ℝ → ℂ} (hf : ExpMomentSource f) (hg : ExpMomentSource g) :
    ExpMomentSource fun x => f x + g x := by
  refine ⟨hf.continuous.add hg.continuous, fun c => ?_⟩
  refine ((hf.moment c).add (hg.moment c)).mono'
    (by have := hf.continuous; have := hg.continuous; fun_prop : Continuous fun x : ℝ =>
      Real.exp (c * |x|) * ‖f x + g x‖).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have := norm_add_le (f x) (g x)
  simp only [Pi.add_apply]
  nlinarith [Real.exp_pos (c * |x|)]

theorem ExpMomentSource.const_mul {f : ℝ → ℂ} (hf : ExpMomentSource f) (a : ℂ) :
    ExpMomentSource fun x => a * f x := by
  refine ⟨continuous_const.mul hf.continuous, fun c => ?_⟩
  refine ((hf.moment c).const_mul ‖a‖).congr (Eventually.of_forall fun x => ?_)
  simp only [norm_mul]
  ring

/-- Admissible division lists: zeros in the right half-plane, each used at most its multiplicity as
a zero of `F = XiC`. -/
def ThetaDivisionList (L : List ℂ) : Prop :=
  (∀ β ∈ L, 0 < β.re) ∧ ∀ β : ℂ, (L.count β : ℕ∞) ≤ analyticOrderAt XiC β

theorem ThetaDivisionList.tail {β : ℂ} {L : List ℂ} (h : ThetaDivisionList (β :: L)) :
    ThetaDivisionList L :=
  ⟨fun b hb => h.1 b (List.mem_cons_of_mem _ hb), fun b => le_trans
    (by exact_mod_cast (List.count_le_count_cons (a := b) (b := β) (l := L))) (h.2 b)⟩

/-- **Transform of successive zero divisions.**  `Ĝ_L(z) P_L(z) = F(z)`. -/
theorem sourceTransform_thetaListDivision_mul {L : List ℂ} (hL : ThetaDivisionList L) (z : ℂ) :
    sourceTransform (thetaListDivision L) z * listDivisor L z = XiC z := by
  induction L generalizing z with
  | nil =>
    rw [listDivisor_nil, mul_one]
    exact sourceTransform_thetaSourceC z
  | cons β L ih =>
    have hL' := hL.tail
    have hβ : 0 < β.re := hL.1 β List.mem_cons_self
    have hβ0 : β ≠ 0 := fun h => by rw [h] at hβ; simp at hβ
    set G := sourceTransform (thetaListDivision L)
    have hGd : Differentiable ℂ G :=
      (expMomentSource_thetaListDivision L).differentiable_sourceTransform
    have hGP : ∀ w, G w * listDivisor L w = XiC w := ih hL'
    have hGβ : G β = 0 := by
      have hord : analyticOrderAt XiC β = analyticOrderAt G β + L.count β := by
        rw [← analyticOrderAt_listDivisor hβ L hL'.1, ← analyticOrderAt_mul (hGd.analyticAt β)
          ((differentiable_listDivisor L).analyticAt β)]
        congr 1
        funext w
        exact (hGP w).symm
      have hcount := hL.2 β
      rw [List.count_cons_self, hord] at hcount
      by_contra hne
      rw [(hGd.analyticAt β).analyticOrderAt_eq_zero.2 hne, zero_add] at hcount
      have : ((L.count β + 1 : ℕ) : ℕ∞) ≤ (L.count β : ℕ∞) := by exact_mod_cast hcount
      norm_cast at this
      omega
    have hdiv : (β ^ 2 - z ^ 2) * sourceTransform (zeroDivision β (thetaListDivision L)) z =
        β ^ 2 * G z := by
      have h := (expMomentSource_thetaListDivision L).sourceTransform_zeroDivision
        (thetaListDivision_neg L) β z
      rw [h, show sourceTransform (thetaListDivision L) β = G β from rfl, hGβ, sub_zero]
    show sourceTransform (zeroDivision β (thetaListDivision L)) z * listDivisor (β :: L) z = XiC z
    rw [listDivisor_cons, ← hGP z]
    have hstep : sourceTransform (zeroDivision β (thetaListDivision L)) z * (1 - z ^ 2 / β ^ 2) =
        G z := by
      have hβ2 : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ0
      field_simp
      linear_combination hdiv
    rw [← mul_assoc, hstep]

/-! ## Realization of divisor quotients -/

theorem ExpMomentSource.mul_sub_mul {f g : ℝ → ℂ} (hf : ExpMomentSource f)
    (hg : ExpMomentSource g) (a b : ℂ) : ExpMomentSource fun x => a * f x - b * g x := by
  have h := (hf.const_mul a).add (hg.const_mul (-b))
  have heq : (fun x => a * f x + -b * g x) = fun x => a * f x - b * g x :=
    funext fun x => by ring
  rwa [heq] at h

theorem sourceTransform_sub_mul {f g : ℝ → ℂ} (hf : ExpMomentSource f) (hg : ExpMomentSource g)
    (a b z : ℂ) :
    sourceTransform (fun x => a * f x - b * g x) z = a * sourceTransform f z - b * sourceTransform g z := by
  have h := sourceTransform_add (hf.const_mul a) (hg.const_mul (-b)) z
  rw [sourceTransform_const_mul, sourceTransform_const_mul] at h
  rw [show (fun x => a * f x - b * g x) = fun x => a * f x + -b * g x from
    funext fun x => by ring, h]
  ring

/-- The partial-fraction combination of a family of divisions `D` along `L` realizing `e`:
`D_{β::L}^e = e(β²) D_{β::L} − β² D_L^{e₁}` with `e = e(β²) + (X − β²) e₁`, and `D_[]^e = e₀ D_[]`. -/
def listComb (D : List ℂ → ℝ → ℂ) : List ℂ → Polynomial ℂ → ℝ → ℂ
  | [], e => fun x => e.coeff 0 * D [] x
  | β :: L, e => fun x => e.eval (β ^ 2) * D (β :: L) x -
      β ^ 2 * listComb D L (e /ₘ (Polynomial.X - Polynomial.C (β ^ 2))) x

theorem listComb_nil (D : List ℂ → ℝ → ℂ) (e : Polynomial ℂ) :
    listComb D [] e = fun x => e.coeff 0 * D [] x := rfl

theorem listComb_cons (D : List ℂ → ℝ → ℂ) (β : ℂ) (L : List ℂ) (e : Polynomial ℂ) :
    listComb D (β :: L) e = fun x => e.eval (β ^ 2) * D (β :: L) x -
      β ^ 2 * listComb D L (e /ₘ (Polynomial.X - Polynomial.C (β ^ 2))) x := rfl

theorem natDegree_divByMonic_X_sub_C_le {e : Polynomial ℂ} {n : ℕ} (he : e.natDegree ≤ n + 1)
    (a : ℂ) : (e /ₘ (Polynomial.X - Polynomial.C a)).natDegree ≤ n := by
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C a), Polynomial.natDegree_X_sub_C]
  omega

theorem eq_C_add_X_sub_C_mul_divByMonic (e : Polynomial ℂ) (a : ℂ) :
    e = Polynomial.C (e.eval a) + (Polynomial.X - Polynomial.C a) *
      (e /ₘ (Polynomial.X - Polynomial.C a)) := by
  rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.modByMonic_add_div]

theorem coeff_succ_eq_coeff_divByMonic {e : Polynomial ℂ} {n : ℕ} (he : e.natDegree ≤ n + 1)
    (a : ℂ) : e.coeff (n + 1) = (e /ₘ (Polynomial.X - Polynomial.C a)).coeff n := by
  have h := congrArg (fun q : Polynomial ℂ => q.coeff (n + 1)) (eq_C_add_X_sub_C_mul_divByMonic e a)
  rw [h, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (Nat.succ_ne_zero _), zero_add,
    sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (by have := natDegree_divByMonic_X_sub_C_le he a; omega : (e /ₘ (Polynomial.X -
        Polynomial.C a)).natDegree < n + 1), mul_zero, sub_zero]

/-- **Realization of divisor quotients.**  For an admissible list `L` and a polynomial `e` of degree
at most `|L|`, the partial-fraction combination `u` of the successive divisions of `k` is an even
theta-dominated source with `û(z) P_L(z) = F(z) e(z²)`, and `u - c k = o(k)` at both ends with
`c = e_{|L|} ∏_{β ∈ L} (-β²)`. -/
theorem listComb_spec {L : List ℂ} (hL : ThetaDivisionList L)
    (e : Polynomial ℂ) (he : e.natDegree ≤ L.length) :
    ExpMomentSource (listComb thetaListDivision L e) ∧
      (∀ x, listComb thetaListDivision L e (-x) = listComb thetaListDivision L e x) ∧
      (∃ C, ∀ x, ‖listComb thetaListDivision L e x‖ ≤ C * thetaCuspFullSource x) ∧
      (∀ z, sourceTransform (listComb thetaListDivision L e) z * listDivisor L z =
        XiC z * e.eval (z ^ 2)) ∧
      Tendsto (fun x => ‖listComb thetaListDivision L e x -
        e.coeff L.length * (L.map fun β => -β ^ 2).prod * thetaSourceC x‖ /
          thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) := by
  induction L generalizing e with
  | nil =>
    have he0 : e = Polynomial.C (e.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero he
    rw [listComb_nil]
    refine ⟨expMomentSource_thetaSourceC.const_mul _,
      fun x => by simp only [thetaListDivision, thetaSourceC_neg], ⟨‖e.coeff 0‖, fun x => ?_⟩,
      fun z => ?_, ?_⟩
    · rw [norm_mul, thetaListDivision, thetaSourceC, Complex.norm_real, Real.norm_of_nonneg
        (thetaCuspFullSource_pos x).le]
    · rw [show (fun x => e.coeff 0 * thetaListDivision [] x) = fun x => e.coeff 0 * thetaSourceC x
        from rfl, sourceTransform_const_mul, sourceTransform_thetaSourceC, listDivisor_nil,
        mul_one, he0, Polynomial.eval_C, Polynomial.coeff_C_zero, mul_comm]
    · simp only [thetaListDivision, List.length_nil, List.map_nil, List.prod_nil, mul_one,
        sub_self, norm_zero, zero_div]
      exact tendsto_const_nhds
  | cons β L ih =>
    have hL' := hL.tail
    have hβ : 0 < β.re := hL.1 β List.mem_cons_self
    have hβ0 : β ≠ 0 := fun h => by rw [h] at hβ; simp at hβ
    rw [listComb_cons]
    set a := β ^ 2 with ha
    have ha0 : a ≠ 0 := pow_ne_zero 2 hβ0
    set e₁ := e /ₘ (Polynomial.X - Polynomial.C a)
    have hdec : e = Polynomial.C (e.eval a) + (Polynomial.X - Polynomial.C a) * e₁ :=
      eq_C_add_X_sub_C_mul_divByMonic e a
    have he₁ : e₁.natDegree ≤ L.length :=
      natDegree_divByMonic_X_sub_C_le (by simpa using he) a
    obtain ⟨hu₁m, hu₁e, ⟨C₁, hC₁⟩, hu₁T, hu₁lim⟩ := ih hL' e₁ he₁
    set u₁ := listComb thetaListDivision L e₁
    set sβ := thetaListDivision (β :: L)
    have hsm : ExpMomentSource sβ := expMomentSource_thetaListDivision (β :: L)
    obtain ⟨Cs, hCs⟩ := exists_norm_thetaListDivision_le (β :: L)
    refine ⟨hsm.mul_sub_mul hu₁m _ _, fun x => ?_,
      ⟨‖e.eval a‖ * Cs + ‖a‖ * C₁, fun x => ?_⟩, fun z => ?_, ?_⟩
    · simp only [sβ, thetaListDivision_neg, hu₁e]
    · calc ‖e.eval a * sβ x - a * u₁ x‖ ≤ ‖e.eval a‖ * ‖sβ x‖ + ‖a‖ * ‖u₁ x‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
        _ ≤ ‖e.eval a‖ * (Cs * thetaCuspFullSource x) + ‖a‖ * (C₁ * thetaCuspFullSource x) := by
            gcongr
            · exact hCs x
            · exact hC₁ x
        _ = _ := by ring
    · have hS := sourceTransform_thetaListDivision_mul hL z
      rw [listDivisor_cons] at hS
      have hU := hu₁T z
      have hE : e.eval (z ^ 2) = e.eval a + (z ^ 2 - a) * e₁.eval (z ^ 2) := by
        conv_lhs => rw [hdec]
        simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
          Polynomial.eval_sub, Polynomial.eval_X]
      have hA : a * (1 - z ^ 2 / a) = a - z ^ 2 := by field_simp
      rw [sourceTransform_sub_mul hsm hu₁m, listDivisor_cons]
      linear_combination e.eval a * hS - a * (1 - z ^ 2 / a) * hU - XiC z * hE -
        XiC z * e₁.eval (z ^ 2) * hA
    · have hcoeff : e.coeff (L.length + 1) = e₁.coeff L.length :=
        coeff_succ_eq_coeff_divByMonic (by simpa using he) a
      set c' := e₁.coeff L.length * (L.map fun β => -β ^ 2).prod
      have hrew : ∀ x, e.eval a * sβ x - a * u₁ x -
          e.coeff (β :: L).length * ((β :: L).map fun β => -β ^ 2).prod * thetaSourceC x =
          e.eval a * sβ x - a * (u₁ x - c' * thetaSourceC x) := by
        intro x
        simp only [List.length_cons, List.map_cons, List.prod_cons, hcoeff, c', a]
        ring
      simp_rw [hrew]
      have hlim : Tendsto (fun x => ‖e.eval a‖ * (‖sβ x‖ / thetaCuspFullSource x) +
          ‖a‖ * (‖u₁ x - c' * thetaSourceC x‖ / thetaCuspFullSource x)) (cocompact ℝ) (𝓝 0) := by
        simpa using ((tendsto_thetaListDivision_div β L).const_mul ‖e.eval a‖).add
          (hu₁lim.const_mul ‖a‖)
      refine squeeze_zero (fun x => div_nonneg (norm_nonneg _) (thetaCuspFullSource_pos x).le)
        (fun x => ?_) hlim
      rw [div_le_iff₀ (thetaCuspFullSource_pos x)]
      have hk := (thetaCuspFullSource_pos x).ne'
      calc ‖e.eval a * sβ x - a * (u₁ x - c' * thetaSourceC x)‖
          ≤ ‖e.eval a‖ * ‖sβ x‖ + ‖a‖ * ‖u₁ x - c' * thetaSourceC x‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
        _ = _ := by field_simp

/-- **Realization of divisor quotients**, existential form. -/
theorem exists_source_mul_listDivisor {L : List ℂ} (hL : ThetaDivisionList L)
    (e : Polynomial ℂ) (he : e.natDegree ≤ L.length) :
    ∃ u : ℝ → ℂ, ExpMomentSource u ∧ (∀ x, u (-x) = u x) ∧
      (∃ C, ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) ∧
      (∀ z, sourceTransform u z * listDivisor L z = XiC z * e.eval (z ^ 2)) ∧
      Tendsto (fun x => ‖u x - e.coeff L.length * (L.map fun β => -β ^ 2).prod * thetaSourceC x‖ /
        thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) :=
  ⟨_, listComb_spec hL e he⟩

/-! ## Smoothness of successive divisions -/

/-- The transform of `G_L` vanishes at the next admissible zero `β`. -/
theorem sourceTransform_thetaListDivision_eq_zero {β : ℂ} {L : List ℂ}
    (hL : ThetaDivisionList (β :: L)) : sourceTransform (thetaListDivision L) β = 0 := by
  have hL' := hL.tail
  have hβ : 0 < β.re := hL.1 β List.mem_cons_self
  have hGd : Differentiable ℂ (sourceTransform (thetaListDivision L)) :=
    (expMomentSource_thetaListDivision L).differentiable_sourceTransform
  have hord : analyticOrderAt XiC β =
      analyticOrderAt (sourceTransform (thetaListDivision L)) β + L.count β := by
    rw [← analyticOrderAt_listDivisor hβ L hL'.1, ← analyticOrderAt_mul (hGd.analyticAt β)
      ((differentiable_listDivisor L).analyticAt β)]
    congr 1
    funext w
    exact (sourceTransform_thetaListDivision_mul hL' w).symm
  have hcount := hL.2 β
  rw [List.count_cons_self, hord] at hcount
  by_contra hne
  rw [(hGd.analyticAt β).analyticOrderAt_eq_zero.2 hne, zero_add] at hcount
  have : ((L.count β + 1 : ℕ) : ℕ∞) ≤ (L.count β : ℕ∞) := by exact_mod_cast hcount
  norm_cast at this
  omega

/-- **Smooth reflection seam.**  Every admissible successive division of `k` is `C^∞` on `ℝ`: each
division step has its necessary zero at the join. -/
theorem contDiff_thetaListDivision {L : List ℂ} (hL : ThetaDivisionList L) :
    ContDiff ℝ (⊤ : ℕ∞) (thetaListDivision L) := by
  induction L with
  | nil => exact contDiff_thetaSourceC
  | cons β L ih =>
    exact (zeroDivision_smooth_green (expMomentSource_thetaListDivision L)
      (thetaListDivision_neg L) (ih hL.tail) (sourceTransform_thetaListDivision_eq_zero hL)).1

/-! ## Conjugation and real parts of sources -/

theorem sourceTransform_neg_eq_of_even {u : ℝ → ℂ} (heven : ∀ x, u (-x) = u x) (z : ℂ) :
    sourceTransform u (-z) = sourceTransform u z := by
  unfold sourceTransform
  rw [← integral_neg_eq_self (fun x : ℝ => Complex.exp (-I * z * x) * u x) volume]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [heven, Complex.ofReal_neg]
  ring_nf

theorem sourceTransform_conj_comp {u : ℝ → ℂ} (z : ℂ) :
    sourceTransform (fun x => (starRingEnd ℂ) (u x)) z =
      (starRingEnd ℂ) (sourceTransform u (-(starRingEnd ℂ) z)) := by
  unfold sourceTransform
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_conj]
  ring_nf

/-- **Real part of an even source.**  `Fourier(Re u)(z) = (û(z) + conj û(conj z)) / 2`. -/
theorem sourceTransform_ofReal_re {u : ℝ → ℂ} (hu : ExpMomentSource u)
    (heven : ∀ x, u (-x) = u x) (z : ℂ) :
    sourceTransform (fun x => ((u x).re : ℂ)) z =
      (sourceTransform u z + (starRingEnd ℂ) (sourceTransform u ((starRingEnd ℂ) z))) / 2 := by
  have hconj : ExpMomentSource fun x => (starRingEnd ℂ) (u x) :=
    ⟨Complex.continuous_conj.comp hu.continuous, fun c => (hu.moment c).congr
      (Eventually.of_forall fun x => by simp only [Complex.norm_conj])⟩
  have hsum := sourceTransform_add hu hconj z
  have hre : (fun x => ((u x).re : ℂ)) = fun x => (1 / 2 : ℂ) * (u x + (starRingEnd ℂ) (u x)) :=
    funext fun x => by rw [Complex.add_conj]; push_cast; ring
  rw [hre, sourceTransform_const_mul, hsum, sourceTransform_conj_comp,
    sourceTransform_neg_eq_of_even heven]
  ring

end

end RHTower
