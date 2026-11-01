import GaloisForLFunctions.LatticeSectionTheory.TheKunnethRiemannRoch
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# The rectangular lattice count and its Epstein function

The rectangular lattice `ℤ ⊕ yℤ ⊂ ℝ²` (`y > 0`) carries the positive definite form
`Q_y(m, n) = m² + y² n²`. Its Gaussian count is the product of two base counts,

    θ_y(t) = Σ_{(m,n) ∈ ℤ²} e^{−π t Q_y(m,n)} = θ(t) θ(y² t).

* **Two-dimensional Poisson summation** (`rectTheta_inv`): `θ_y(1/t) = (t/y) θ_{1/y}(t)`. The dual
  lattice of `ℤ ⊕ yℤ` is `ℤ ⊕ y⁻¹ℤ`, of covolume `1/y`. In degrees this is a Serre duality of a
  rank-two count.
* **The Epstein FE-pair** (`rectFEPair`). Positivity, the Poisson identity and the exponential
  decay `θ_y(t) − 1 = O(e^{−bt})` make `(θ_y, θ_{1/y})` a weak FE-pair of weight `1` and root number
  `1/y`. Mathlib's Mellin machinery then gives the **completed Epstein function**
  `Λ_y = (rectFEPair y).Λ`: meromorphic with simple poles at `0` and `1` only, and the functional
  equation `Λ_y(1 − s) = y⁻¹ Λ_{1/y}(s)`.
* **Dirichlet series** (`hasSum_epsteinLambda`). For `Re s > 1`,
  `Λ_y(s) = Γ(s) Σ'_{(m,n) ≠ 0} (π Q_y(m, n))^{−s}`: the completed Epstein zeta function of the
  rectangular lattice.

Every property here holds for every `y > 0`: they are the soft properties of a definite count.
-/

noncomputable section

open Real Complex Filter Topology Set Asymptotics

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticOrientationGeometry

/-! ### The count -/

/-- The Gaussian count of the rectangular lattice `ℤ ⊕ yℤ`: `θ_y(t) = θ(t) θ(y² t)`. -/
def rectTheta (y t : ℝ) : ℝ := thetaSum t * thetaSum (y ^ 2 * t)

theorem one_le_rectTheta {y t : ℝ} (hy : y ≠ 0) (ht : 0 < t) : 1 ≤ rectTheta y t := by
  have h1 := one_le_thetaSum ht
  have h2 := one_le_thetaSum (mul_pos (pow_pos (abs_pos.mpr hy) 2 |>.trans_eq (sq_abs y)) ht)
  unfold rectTheta; nlinarith

theorem thetaSum_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : thetaSum v ≤ thetaSum u := by
  rcases huv.lt_or_eq with h | h
  · exact (thetaSum_lt_thetaSum hu h).le
  · rw [h]

/-- **Two-dimensional Poisson summation**: `θ_y(1/t) = (t/y) θ_{1/y}(t)`. -/
theorem rectTheta_inv {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    rectTheta y (1 / t) = 1 / y * t * rectTheta (1 / y) t := by
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ t = r ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have hs : ∀ u : ℝ, 0 < u → thetaSum u = (Real.sqrt u)⁻¹ * thetaSum u⁻¹ := fun u hu => by
    rw [Real.sqrt_eq_rpow]; exact thetaSum_inv hu
  rw [rectTheta, rectTheta, hs (1 / r ^ 2) (by positivity), hs (y ^ 2 * (1 / r ^ 2)) (by positivity)]
  have e1 : (1 / r ^ 2)⁻¹ = r ^ 2 := by rw [one_div, inv_inv]
  have e2 : (y ^ 2 * (1 / r ^ 2))⁻¹ = (1 / y) ^ 2 * r ^ 2 := by
    field_simp
  have e3 : Real.sqrt (1 / r ^ 2) = r⁻¹ := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_sq hr.le]
  have e4 : Real.sqrt (y ^ 2 * (1 / r ^ 2)) = y * r⁻¹ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le, e3]
  rw [e1, e2, e3, e4, inv_inv, mul_inv, inv_inv]
  ring

/-! ### Decay and the FE-pair -/

theorem continuousOn_thetaSum : ContinuousOn thetaSum (Ioi 0) :=
  (HurwitzZeta.continuousOn_evenKernel 0).congr fun _ hu => thetaSum_eq_evenKernel hu

theorem continuousOn_rectTheta {y : ℝ} (hy : y ≠ 0) : ContinuousOn (rectTheta y) (Ioi 0) := by
  have hy2 : 0 < y ^ 2 := by positivity
  refine continuousOn_thetaSum.mul (continuousOn_thetaSum.comp
    ((continuous_const.mul continuous_id).continuousOn) fun t ht => ?_)
  exact mul_pos hy2 ht

/-- Exponential decay of the rectangular count: `0 ≤ θ_y(t) − 1 ≤ C e^{−bt}` for large `t`. -/
theorem rectTheta_sub_one_le {y : ℝ} (hy : y ≠ 0) :
    ∃ b C : ℝ, 0 < b ∧ ∀ t : ℝ, max 1 (1 / y ^ 2) ≤ t →
      0 ≤ rectTheta y t - 1 ∧ rectTheta y t - 1 ≤ C * Real.exp (-b * t) := by
  have hy2 : 0 < y ^ 2 := by positivity
  set c := min 1 (y ^ 2)
  have hc : 0 < c := lt_min one_pos hy2
  refine ⟨π * c, 4 * thetaSum 1 + 4, mul_pos Real.pi_pos hc, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hyt : 1 ≤ y ^ 2 * t := by
    have := (le_max_right _ _).trans ht
    rw [div_le_iff₀ hy2] at this; linarith
  have h0 : 0 < t := by linarith
  refine ⟨by linarith [one_le_rectTheta hy h0], ?_⟩
  have a1 := thetaSum_sub_one_le ht1
  have a2 := thetaSum_sub_one_le hyt
  have m1 := thetaSum_antitone one_pos hyt
  have b1 : Real.exp (-π * t) ≤ Real.exp (-(π * c) * t) := by
    rw [Real.exp_le_exp]
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le h0.le) (sub_nonneg.2 (min_le_left 1 (y ^ 2)))]
  have b2 : Real.exp (-π * (y ^ 2 * t)) ≤ Real.exp (-(π * c) * t) := by
    rw [Real.exp_le_exp]
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le h0.le) (sub_nonneg.2 (min_le_right 1 (y ^ 2)))]
  have p1 := one_le_thetaSum h0
  have p2 := one_le_thetaSum (show 0 < y ^ 2 * t by positivity)
  have e : rectTheta y t - 1 = (thetaSum t - 1) * thetaSum (y ^ 2 * t) + (thetaSum (y ^ 2 * t) - 1) := by
    unfold rectTheta; ring
  rw [e]
  have hθ1 : 0 < thetaSum 1 := thetaSum_pos one_pos
  have hE := Real.exp_pos (-(π * c) * t)
  calc (thetaSum t - 1) * thetaSum (y ^ 2 * t) + (thetaSum (y ^ 2 * t) - 1)
      ≤ 4 * Real.exp (-(π * c) * t) * thetaSum 1 + 4 * Real.exp (-(π * c) * t) := by
        have : (thetaSum t - 1) * thetaSum (y ^ 2 * t) ≤ 4 * Real.exp (-(π * c) * t) * thetaSum 1 :=
          mul_le_mul (a1.trans (by linarith)) m1 (by linarith) (by positivity)
        linarith
    _ = (4 * thetaSum 1 + 4) * Real.exp (-(π * c) * t) := by ring

theorem isBigO_rectTheta_sub_one {y : ℝ} (hy : y ≠ 0) (r : ℝ) :
    (fun t : ℝ => ((rectTheta y t : ℝ) : ℂ) - 1) =O[atTop] (· ^ r) := by
  obtain ⟨b, C, hb, hbound⟩ := rectTheta_sub_one_le hy
  have h1 : (fun t : ℝ => ((rectTheta y t : ℝ) : ℂ) - 1) =O[atTop] fun t => Real.exp (-b * t) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (max 1 (1 / y ^ 2))] with t ht
    obtain ⟨h0, hle⟩ := hbound t ht
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg h0,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hle
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hb r).isBigO

/-- **The Epstein FE-pair** of the rectangular lattice: `(θ_y, θ_{1/y})`, weight `1`, root number
`1/y`, constant terms `1`. -/
def rectFEPair (y : ℝ) (hy : 0 < y) : WeakFEPair ℂ where
  f t := (rectTheta y t : ℂ)
  g t := (rectTheta (1 / y) t : ℂ)
  k := 1
  ε := ((1 / y : ℝ) : ℂ)
  f₀ := 1
  g₀ := 1
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_rectTheta hy.ne')).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn
    (continuousOn_rectTheta (one_div_pos.mpr hy).ne')).locallyIntegrableOn measurableSet_Ioi
  hk := one_pos
  hε := by exact_mod_cast (one_div_pos.mpr hy).ne'
  h_feq x hx := by
    rw [rectTheta_inv hy hx, Real.rpow_one, smul_eq_mul]
    push_cast; ring
  hf_top r := isBigO_rectTheta_sub_one hy.ne' r
  hg_top r := isBigO_rectTheta_sub_one (one_div_pos.mpr hy).ne' r

/-- **The completed Epstein function** of the rectangular lattice `ℤ ⊕ yℤ`. -/
def epsteinLambda (y : ℝ) (hy : 0 < y) (s : ℂ) : ℂ := (rectFEPair y hy).Λ s

/-- The completed Epstein function is holomorphic away from `0` and `1`. -/
theorem differentiableAt_epsteinLambda {y : ℝ} (hy : 0 < y) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (epsteinLambda y hy) s :=
  (rectFEPair y hy).differentiableAt_Λ (Or.inl hs0) (Or.inl (by simpa [rectFEPair] using hs1))

/-- **Functional equation**: `Λ_y(1 − s) = y⁻¹ Λ_{1/y}(s)`. -/
theorem epsteinLambda_one_sub {y : ℝ} (hy : 0 < y) (s : ℂ) :
    epsteinLambda y hy (1 - s) = ((1 / y : ℝ) : ℂ) * epsteinLambda (1 / y) (one_div_pos.mpr hy) s := by
  have h := (rectFEPair y hy).functional_equation s
  have hsymm : (rectFEPair y hy).symm.Λ = epsteinLambda (1 / y) (one_div_pos.mpr hy) := by
    have : (rectFEPair y hy).symm = rectFEPair (1 / y) (one_div_pos.mpr hy) := by
      unfold rectFEPair WeakFEPair.symm
      congr 1 <;> simp
    rw [this]; rfl
  have hk : (((rectFEPair y hy).k : ℝ) : ℂ) = 1 := by simp [rectFEPair]
  rw [hsymm, hk] at h
  exact h

/-! ### The Dirichlet series -/

/-- The quadratic form of the rectangular lattice. -/
def rectForm (y : ℝ) (i : ℤ × ℤ) : ℝ := (i.1 : ℝ) ^ 2 + y ^ 2 * (i.2 : ℝ) ^ 2

theorem rectForm_pos {y : ℝ} (hy : y ≠ 0) {i : ℤ × ℤ} (hi : i ≠ 0) : 0 < rectForm y i := by
  unfold rectForm
  rcases i with ⟨m, n⟩
  by_cases hm : m = 0
  · have hn : n ≠ 0 := fun hn => hi (by simp [hm, hn])
    subst hm
    have : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have : (0 : ℝ) < y ^ 2 := by positivity
    simp only [Int.cast_zero]; nlinarith
  · have : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have : (0 : ℝ) ≤ y ^ 2 * (n : ℝ) ^ 2 := by positivity
    linarith

theorem rectForm_nonneg (y : ℝ) (i : ℤ × ℤ) : 0 ≤ rectForm y i := by
  unfold rectForm; positivity

/-- The rectangular form dominates `min(1, y²)` times the square of the sup norm. -/
theorem rectForm_ge {y : ℝ} (i : ℤ × ℤ) :
    min 1 (y ^ 2) * ‖(finTwoArrowEquiv ℤ).symm i‖ ^ 2 ≤ rectForm y i := by
  rcases i with ⟨m, n⟩
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
  unfold rectForm
  simp only
  have hm : (|(m : ℝ)|) ^ 2 = (m : ℝ) ^ 2 := sq_abs _
  have hn : (|(n : ℝ)|) ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  have hc1 := min_le_left 1 (y ^ 2)
  have hc2 := min_le_right 1 (y ^ 2)
  have hc0 : 0 ≤ min 1 (y ^ 2) := le_min zero_le_one (sq_nonneg y)
  rcases le_total |(m : ℝ)| |(n : ℝ)| with h | h
  · rw [max_eq_right h, hn]
    nlinarith [sq_nonneg (m : ℝ), sq_nonneg (n : ℝ)]
  · rw [max_eq_left h, hm]
    nlinarith [sq_nonneg (m : ℝ), sq_nonneg (n : ℝ), mul_nonneg (sq_nonneg y) (sq_nonneg (n : ℝ))]

/-- Summability of the Epstein series for exponent `σ > 1`. -/
theorem summable_rectForm_rpow {y : ℝ} (hy : y ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun i : ℤ × ℤ => (if i = 0 then (0 : ℝ) else 1) / (π * rectForm y i) ^ σ := by
  set c := min 1 (y ^ 2)
  have hc : 0 < c := lt_min one_pos (by positivity)
  have hs : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith)
  have hs' := (hs.comp_injective (finTwoArrowEquiv ℤ).symm.injective).mul_left ((π * c) ^ (-σ))
  refine hs'.of_nonneg_of_le (fun i => div_nonneg (by split_ifs <;> norm_num)
    (Real.rpow_nonneg (mul_nonneg Real.pi_pos.le (rectForm_nonneg y i)) σ)) fun i => ?_
  split_ifs with hi
  · simp only [zero_div, Function.comp_apply]
    exact mul_nonneg (Real.rpow_nonneg (mul_nonneg Real.pi_pos.le hc.le) _)
      (Real.rpow_nonneg (norm_nonneg _) _)
  · have hpos := rectForm_pos hy hi
    have hnorm : 0 < ‖(finTwoArrowEquiv ℤ).symm i‖ := by
      rw [norm_pos_iff]
      intro h
      apply hi
      rcases i with ⟨m, n⟩
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.zero_apply] at h0 h1
      simp [h0, h1]
    have hge := rectForm_ge (y := y) i
    simp only [Function.comp_apply, one_div]
    rw [← Real.rpow_neg (by positivity)]
    have hbase : π * c * ‖(finTwoArrowEquiv ℤ).symm i‖ ^ 2 ≤ π * rectForm y i := by
      have := mul_le_mul_of_nonneg_left hge Real.pi_pos.le; linarith
    calc (π * rectForm y i) ^ (-σ) ≤ (π * c * ‖(finTwoArrowEquiv ℤ).symm i‖ ^ 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
      _ = (π * c) ^ (-σ) * ‖(finTwoArrowEquiv ℤ).symm i‖ ^ (-(2 * σ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hnorm.le]
          norm_num

/-- The rectangular count as a sum over `ℤ²` without the zero vector. -/
theorem hasSum_rectTheta_sub_one {y t : ℝ} (hy : y ≠ 0) (ht : 0 < t) :
    HasSum (fun i : ℤ × ℤ => if i = 0 then (0 : ℝ) else Real.exp (-(π * rectForm y i) * t))
      (rectTheta y t - 1) := by
  classical
  have hpos : 0 < y ^ 2 * t := by positivity
  have h1 := hasSum_thetaSum ht
  have h2 := hasSum_thetaSum hpos
  have hprod := h1.mul h2 (h1.summable.mul_of_nonneg h2.summable (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le))
  have hu := hprod.update (0 : ℤ × ℤ) 0
  have e : rectTheta y t - 1 = 0 - Real.exp (-π * t * (((0 : ℤ × ℤ).1 : ℤ) : ℝ) ^ 2) *
      Real.exp (-π * (y ^ 2 * t) * (((0 : ℤ × ℤ).2 : ℤ) : ℝ) ^ 2) +
      HurwitzZeta.evenKernel 0 t * HurwitzZeta.evenKernel 0 (y ^ 2 * t) := by
    unfold rectTheta
    rw [thetaSum_eq_evenKernel ht, thetaSum_eq_evenKernel hpos]
    simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, Real.exp_zero, mul_one]
    ring
  have hu' : HasSum (Function.update (fun x : ℤ × ℤ => Real.exp (-π * t * (x.1 : ℝ) ^ 2) *
      Real.exp (-π * (y ^ 2 * t) * (x.2 : ℝ) ^ 2)) 0 0) (rectTheta y t - 1) := by
    rw [e]; exact hu
  refine hu'.congr_fun fun i => ?_
  by_cases hi : i = 0
  · simp [hi]
  · rw [Function.update_of_ne hi, if_neg hi, ← Real.exp_add]
    congr 1; unfold rectForm; ring

/-- **The Dirichlet series of the completed Epstein function.** For `Re s > 1`,
`Λ_y(s) = Σ'_{(m,n) ≠ 0} Γ(s) (π (m² + y² n²))^{−s}`. -/
theorem hasSum_epsteinLambda {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun i : ℤ × ℤ => Complex.Gamma s * (if i = 0 then (0 : ℂ) else 1) /
      ((π * rectForm y i : ℝ) : ℂ) ^ s) (epsteinLambda y hy s) := by
  have hM := (rectFEPair y hy).hasMellin (s := s) (by simpa [rectFEPair] using hs)
  have hval : mellin (fun t => (rectFEPair y hy).f t - (rectFEPair y hy).f₀) s =
      epsteinLambda y hy s := hM.2
  rw [← hval]
  refine hasSum_mellin (a := fun i => if i = 0 then (0 : ℂ) else 1)
    (p := fun i => π * rectForm y i) (fun i => ?_) (by linarith) (fun t ht => ?_) ?_
  · by_cases hi : i = 0
    · exact Or.inl (if_pos hi)
    · exact Or.inr (mul_pos Real.pi_pos (rectForm_pos hy.ne' hi))
  · have h := (hasSum_rectTheta_sub_one hy.ne' ht).mapL Complex.ofRealCLM
    simp only [rectFEPair]
    refine (h.congr_fun fun i => ?_).trans_eq ?_
    · by_cases hi : i = 0 <;> simp [hi]
    · simp
  · refine (summable_rectForm_rpow hy.ne' hs).congr fun i => ?_
    by_cases hi : i = 0 <;> simp [hi]

end GaloisForLFunctions.LatticeSectionTheory
