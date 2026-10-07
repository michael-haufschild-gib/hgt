import GaloisForLFunctions.HTGeometry.PolydiskRadialLogarithm
import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle

/-!
# Lee–Yang restrictions have linear zero counts

A **Lee–Yang datum** is a polynomial `P` in finitely many variables together with positive
frequencies `λⱼ`.  `P` has no zero on the open polydisk, and neither does its reflected polynomial
`P^♯(v) = Σ_α conj(c_α) v^{D−α}`, where `Dⱼ = deg_{vⱼ} P`.  Its restriction is

`f(t) = P(e^{−iλ₁t}, …, e^{−iλₙt})`.

* All zeros of `f` are real (`restr_im_eq_zero_of_eq_zero`).  Below the axis every field lies in the
  disk.  Above it, `P(u) = u^D · conj P^♯(1/ū)` with `1/ū` in the disk.
* **Linear count** (`abs_zeroCount_sub_le`).  For `a < b` with `f(a), f(b) ≠ 0`, the number of zeros
  in `[a,b]`, with multiplicity, differs from `(b − a)·D` by at most `2S`.  Here
  `D = (1/2π) Σⱼ Dⱼ λⱼ` and `S = Σⱼ Dⱼ`.

**Proof.**  Apply the argument principle on `[a,b] × [−η, η]`.
* Along the lower edge `f(x − iη) = P(w_x)` with `w_x` in the polydisk.  The radial logarithm of `P`
  is a continuous logarithm along the edge, so the argument variation is a difference of two radial
  values, each within `π · totalDegree P` of `arg P(0)`.
* Along the upper edge `f(x + iη) = u(x)^D · conj P^♯(w'_x)`.  This contributes `−(b − a) Σ Dⱼλⱼ`
  plus a radial difference for `P^♯`.
* The vertical edges vanish as `η → 0`.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.LeeYangCount

noncomputable section

variable {ι : Type*} [Fintype ι]

/-! ## The reflected polynomial -/

/-- The degree vector `Dⱼ = deg_{uⱼ} P`. -/
def degVec (P : MvPolynomial ι ℂ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => P.degreeOf j

theorem degVec_apply (P : MvPolynomial ι ℂ) (j : ι) : degVec P j = P.degreeOf j := rfl

/-- The reflected polynomial `P^♯(v) = Σ_α conj(c_α) v^{D−α}`. -/
def dualPoly (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ α ∈ P.support, MvPolynomial.monomial (degVec P - α) ((starRingEnd ℂ) (MvPolynomial.coeff α P))

/-- `S = Σⱼ Dⱼ`. -/
def degSum (P : MvPolynomial ι ℂ) : ℕ := ∑ j, P.degreeOf j

omit [Fintype ι] in
theorem le_degreeOf_of_mem_support {P : MvPolynomial ι ℂ} {α : ι →₀ ℕ} (hα : α ∈ P.support)
    (j : ι) : α j ≤ P.degreeOf j :=
  MvPolynomial.monomial_le_degreeOf j hα

theorem totalDegree_le_degSum (P : MvPolynomial ι ℂ) : P.totalDegree ≤ degSum P := by
  apply Finset.sup_le
  intro α hα
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact Finset.sum_le_sum fun j _ => le_degreeOf_of_mem_support hα j

theorem totalDegree_dualPoly_le (P : MvPolynomial ι ℂ) : (dualPoly P).totalDegree ≤ degSum P := by
  unfold dualPoly
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro α _
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact Finset.sum_le_sum fun j _ => by
    rw [Finsupp.tsub_apply, degVec_apply]
    exact Nat.sub_le _ _

theorem eval_dualPoly (P : MvPolynomial ι ℂ) (v : ι → ℂ) :
    MvPolynomial.eval v (dualPoly P) =
      ∑ α ∈ P.support, (starRingEnd ℂ) (MvPolynomial.coeff α P) *
        ∏ j, v j ^ (P.degreeOf j - α j) := by
  rw [dualPoly, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

/-- **The reflection identity.**  For `u` with nonzero coordinates,
`P(u) = (∏ uⱼ^{Dⱼ}) · conj P^♯(1/ū)`. -/
theorem eval_eq_prod_mul_conj_dual (P : MvPolynomial ι ℂ) {u : ι → ℂ} (hu : ∀ j, u j ≠ 0) :
    MvPolynomial.eval u P =
      (∏ j, u j ^ P.degreeOf j) *
        (starRingEnd ℂ) (MvPolynomial.eval (fun j => ((starRingEnd ℂ) (u j))⁻¹) (dualPoly P)) := by
  rw [eval_dualPoly, map_sum, Finset.mul_sum, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [map_mul, Complex.conj_conj, map_prod]
  have hterm : ∀ j, u j ^ P.degreeOf j *
      (starRingEnd ℂ) (((starRingEnd ℂ) (u j))⁻¹ ^ (P.degreeOf j - α j)) = u j ^ α j := by
    intro j
    rw [map_pow, map_inv₀, Complex.conj_conj]
    have hle := le_degreeOf_of_mem_support hα j
    have hsplit : u j ^ P.degreeOf j = u j ^ α j * u j ^ (P.degreeOf j - α j) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hsplit, mul_assoc, ← mul_pow, mul_inv_cancel₀ (hu j), one_pow, mul_one]
  calc MvPolynomial.coeff α P * ∏ j, u j ^ α j
      = MvPolynomial.coeff α P * ∏ j, (u j ^ P.degreeOf j *
          (starRingEnd ℂ) (((starRingEnd ℂ) (u j))⁻¹ ^ (P.degreeOf j - α j))) := by
        rw [Finset.prod_congr rfl fun j _ => hterm j]
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

/-! ## Lee–Yang data and their restrictions -/

/-- A Lee–Yang datum. -/
structure LeeYangDatum (ι : Type*) [Fintype ι] where
  P : MvPolynomial ι ℂ
  freq : ι → ℝ
  freq_pos : ∀ j, 0 < freq j
  disk : ∀ w : ι → ℂ, (∀ j, ‖w j‖ < 1) → MvPolynomial.eval w P ≠ 0
  dualDisk : ∀ w : ι → ℂ, (∀ j, ‖w j‖ < 1) → MvPolynomial.eval w (dualPoly P) ≠ 0

namespace LeeYangDatum

variable (L : LeeYangDatum ι)

/-- The field `uⱼ(t) = e^{−iλⱼt}`. -/
def field (j : ι) (t : ℂ) : ℂ := Complex.exp (-(I * (L.freq j : ℂ) * t))

/-- The restriction `f(t) = P(u(t))`. -/
def restr (t : ℂ) : ℂ := MvPolynomial.eval (fun j => L.field j t) L.P

/-- The mean density `D = (1/2π) Σⱼ Dⱼ λⱼ`. -/
def density : ℝ := (1 / (2 * Real.pi)) * ∑ j, (L.P.degreeOf j : ℝ) * L.freq j

theorem norm_field (j : ι) (t : ℂ) : ‖L.field j t‖ = Real.exp (L.freq j * t.im) := by
  rw [field, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem field_ne_zero (j : ι) (t : ℂ) : L.field j t ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_restr : Differentiable ℂ L.restr := by
  have h : L.restr = fun t => ∑ α ∈ L.P.support, MvPolynomial.coeff α L.P *
      ∏ j, L.field j t ^ α j := by
    funext t
    rw [restr, MvPolynomial.eval_eq']
  rw [h]
  unfold field
  fun_prop

theorem analyticOnNhd_restr : AnalyticOnNhd ℂ L.restr Set.univ :=
  fun z _ => L.differentiable_restr.analyticAt z

/-- **All zeros are real.** -/
theorem restr_ne_zero_of_im_ne_zero {t : ℂ} (ht : t.im ≠ 0) : L.restr t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · apply L.disk
    intro j
    rw [norm_field, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (L.freq_pos j) hlt
  · rw [restr, eval_eq_prod_mul_conj_dual L.P (fun j => L.field_ne_zero j t)]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (L.field_ne_zero j t))
      ((map_ne_zero _).mpr (L.dualDisk _ fun j => ?_))
    rw [norm_inv, Complex.norm_conj, norm_field]
    apply inv_lt_one_of_one_lt₀
    rw [Real.one_lt_exp_iff]
    exact mul_pos (L.freq_pos j) hgt

theorem restr_im_eq_zero_of_eq_zero {t : ℂ} (h : L.restr t = 0) : t.im = 0 := by
  by_contra ht
  exact L.restr_ne_zero_of_im_ne_zero ht h

/-! ## The horizontal edges -/

theorem hasDerivAt_restr_line (T x : ℝ) :
    HasDerivAt (fun y : ℝ => L.restr ((y : ℂ) + (T : ℂ) * I))
      (deriv L.restr ((x : ℂ) + (T : ℂ) * I)) x := by
  have h := ((L.differentiable_restr ((x : ℂ) + (T : ℂ) * I)).hasDerivAt).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).add_const ((T : ℂ) * I))
  simpa using h.comp_ofReal

theorem continuous_logDeriv_line {T : ℝ} (hT : T ≠ 0) :
    Continuous fun x : ℝ => logDeriv L.restr ((x : ℂ) + (T : ℂ) * I) := by
  have hd : Continuous (deriv L.restr) :=
    (L.differentiable_restr.contDiff (n := 1)).continuous_deriv le_rfl
  simp_rw [logDeriv_apply]
  refine (hd.comp (by fun_prop)).div (L.differentiable_restr.continuous.comp (by fun_prop)) ?_
  intro x
  apply L.restr_ne_zero_of_im_ne_zero
  simpa using hT

/-- Lower-edge points `u(x + iT)`, `T < 0`. -/
def lowerPoint (T x : ℝ) : ι → ℂ := fun j => L.field j ((x : ℂ) + (T : ℂ) * I)

theorem norm_lowerPoint_lt_one {T : ℝ} (hT : T < 0) (x : ℝ) (j : ι) :
    ‖L.lowerPoint T x j‖ < 1 := by
  rw [lowerPoint, norm_field, Real.exp_lt_one_iff]
  simpa using mul_neg_of_pos_of_neg (L.freq_pos j) hT

omit [Fintype ι] in
theorem radialFree_of_norm_lt_one {Q : MvPolynomial ι ℂ}
    (hQ : ∀ w : ι → ℂ, (∀ j, ‖w j‖ < 1) → MvPolynomial.eval w Q ≠ 0) {w : ι → ℂ}
    (hw : ∀ j, ‖w j‖ < 1) : RadialFree Q w := by
  intro s hs
  apply hQ
  intro j
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  calc s * ‖w j‖ ≤ 1 * ‖w j‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hw j

theorem continuous_lowerPoint (T : ℝ) : Continuous (L.lowerPoint T) := by
  apply continuous_pi
  intro j
  unfold lowerPoint field
  fun_prop

/-- **Lower edge.**  The argument variation is a difference of radial logarithms of `P`. -/
theorem integral_lower_edge {T : ℝ} (hT : T < 0) (a b : ℝ) :
    ∫ x in a..b, (logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)).im =
      (radialLog L.P (L.lowerPoint T b)).im - (radialLog L.P (L.lowerPoint T a)).im := by
  have hfree : ∀ x, RadialFree L.P (L.lowerPoint T x) :=
    fun x => radialFree_of_norm_lt_one L.disk (L.norm_lowerPoint_lt_one hT x)
  have hcont := continuous_radialLog_comp (L.continuous_lowerPoint T) hfree
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y => radialLog L.P (L.lowerPoint T y))
      (logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)) x := by
    intro x
    rw [logDeriv_apply]
    exact hasDerivAt_of_exp_eq (g := fun y : ℝ => L.restr ((y : ℂ) + (T : ℂ) * I))
      (L := fun y => radialLog L.P (L.lowerPoint T y)) (L.hasDerivAt_restr_line T x)
      (L.restr_ne_zero_of_im_ne_zero (by simpa using hT.ne)) hcont.continuousAt
      (Eventually.of_forall fun y => exp_radialLog (hfree y))
  have hint := (L.continuous_logDeriv_line hT.ne).intervalIntegrable (μ := volume) a b
  have him : ∫ x in a..b, (logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)).im =
      (∫ x in a..b, logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)).im :=
    Complex.imCLM.intervalIntegral_comp_comm hint
  rw [him, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint,
    Complex.sub_im]

/-- Upper-edge points `1/conj u(x + iT)`, `T > 0`. -/
def upperPoint (T x : ℝ) : ι → ℂ :=
  fun j => ((starRingEnd ℂ) (L.field j ((x : ℂ) + (T : ℂ) * I)))⁻¹

theorem norm_upperPoint_lt_one {T : ℝ} (hT : 0 < T) (x : ℝ) (j : ι) :
    ‖L.upperPoint T x j‖ < 1 := by
  rw [upperPoint, norm_inv, Complex.norm_conj, norm_field]
  apply inv_lt_one_of_one_lt₀
  rw [Real.one_lt_exp_iff]
  simpa using mul_pos (L.freq_pos j) hT

theorem continuous_upperPoint (T : ℝ) : Continuous (L.upperPoint T) := by
  apply continuous_pi
  intro j
  unfold upperPoint
  refine (Complex.continuous_conj.comp ?_).inv₀ fun x => ?_
  · unfold field; fun_prop
  · exact (map_ne_zero _).mpr (L.field_ne_zero j _)

/-- The upper-edge logarithm. -/
def upperLog (T x : ℝ) : ℂ :=
  (∑ j, (L.P.degreeOf j : ℂ) * (-(I * (L.freq j : ℂ) * ((x : ℂ) + (T : ℂ) * I)))) +
    (starRingEnd ℂ) (radialLog (dualPoly L.P) (L.upperPoint T x))

theorem exp_upperLog {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Complex.exp (L.upperLog T x) = L.restr ((x : ℂ) + (T : ℂ) * I) := by
  have hfree : RadialFree (dualPoly L.P) (L.upperPoint T x) :=
    radialFree_of_norm_lt_one L.dualDisk (L.norm_upperPoint_lt_one hT x)
  rw [upperLog, Complex.exp_add, Complex.exp_sum, Complex.exp_conj, exp_radialLog hfree,
    restr, eval_eq_prod_mul_conj_dual L.P (fun j => L.field_ne_zero j _)]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [field, ← Complex.exp_nat_mul]

/-- **Upper edge.**  The argument variation is `−(b−a)Σ Dⱼλⱼ` minus a radial difference of `P^♯`. -/
theorem integral_upper_edge {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    ∫ x in a..b, (logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)).im =
      -((b - a) * ∑ j, (L.P.degreeOf j : ℝ) * L.freq j) -
        ((radialLog (dualPoly L.P) (L.upperPoint T b)).im -
          (radialLog (dualPoly L.P) (L.upperPoint T a)).im) := by
  have hfree : ∀ x, RadialFree (dualPoly L.P) (L.upperPoint T x) :=
    fun x => radialFree_of_norm_lt_one L.dualDisk (L.norm_upperPoint_lt_one hT x)
  have hcont : Continuous (L.upperLog T) := by
    unfold upperLog
    refine Continuous.add (by fun_prop) (Complex.continuous_conj.comp
      (continuous_radialLog_comp (L.continuous_upperPoint T) hfree))
  have hderiv : ∀ x : ℝ, HasDerivAt (L.upperLog T)
      (logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)) x := by
    intro x
    rw [logDeriv_apply]
    exact hasDerivAt_of_exp_eq (g := fun y : ℝ => L.restr ((y : ℂ) + (T : ℂ) * I))
      (L := L.upperLog T) (L.hasDerivAt_restr_line T x)
      (L.restr_ne_zero_of_im_ne_zero (by simpa using hT.ne')) hcont.continuousAt
      (Eventually.of_forall fun y => L.exp_upperLog hT y)
  have hint := (L.continuous_logDeriv_line hT.ne').intervalIntegrable (μ := volume) a b
  have him : ∫ x in a..b, (logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)).im =
      (∫ x in a..b, logDeriv L.restr ((x : ℂ) + (T : ℂ) * I)).im :=
    Complex.imCLM.intervalIntegral_comp_comm hint
  rw [him, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
  simp only [Complex.sub_im, upperLog, Complex.add_im, Complex.conj_im, Complex.im_sum]
  have hlin : ∀ y : ℝ, ∑ j, ((L.P.degreeOf j : ℂ) *
      (-(I * (L.freq j : ℂ) * ((y : ℂ) + (T : ℂ) * I)))).im =
      -(y * ∑ j, (L.P.degreeOf j : ℝ) * L.freq j) := by
    intro y
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [hlin, hlin]
  ring

/-! ## The vertical edges and the count -/

/-- Short vertical edges through a non-zero carry arbitrarily small argument variation. -/
theorem exists_vertical_small {x₀ : ℝ} (h : L.restr x₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η₀ > 0, ∀ η, 0 < η → η ≤ η₀ →
      |∫ y in (-η)..η, (logDeriv L.restr ((x₀ : ℂ) + (y : ℂ) * I)).re| ≤ ε := by
  have hcont : ContinuousAt (logDeriv L.restr) (x₀ : ℂ) := by
    have hd : Continuous (deriv L.restr) :=
      (L.differentiable_restr.contDiff (n := 1)).continuous_deriv le_rfl
    have hfun : logDeriv L.restr = fun z => deriv L.restr z / L.restr z :=
      funext fun z => logDeriv_apply _ _
    rw [hfun]
    exact hd.continuousAt.div L.differentiable_restr.continuous.continuousAt h
  set M : ℝ := ‖logDeriv L.restr (x₀ : ℂ)‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  refine ⟨min (δ / 2) (ε / (2 * M)), by positivity, fun η hη hηle => ?_⟩
  have hbound : ∀ y ∈ Set.uIoc (-η) η, ‖(logDeriv L.restr ((x₀ : ℂ) + (y : ℂ) * I)).re‖ ≤ M := by
    intro y hy
    have hy' : |y| ≤ η := by
      rw [uIoc_of_le (by linarith)] at hy
      exact abs_le.mpr ⟨hy.1.le, hy.2⟩
    have hdist : dist ((x₀ : ℂ) + (y : ℂ) * I) (x₀ : ℂ) < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      have : η ≤ δ / 2 := hηle.trans (min_le_left _ _)
      linarith
    have hclose := hball hdist
    rw [dist_eq_norm] at hclose
    calc ‖(logDeriv L.restr ((x₀ : ℂ) + (y : ℂ) * I)).re‖
        ≤ ‖logDeriv L.restr ((x₀ : ℂ) + (y : ℂ) * I)‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ ≤ ‖logDeriv L.restr (x₀ : ℂ)‖ + ‖logDeriv L.restr ((x₀ : ℂ) + (y : ℂ) * I) -
            logDeriv L.restr (x₀ : ℂ)‖ := by
          have := norm_add_le (logDeriv L.restr (x₀ : ℂ))
            (logDeriv L.restr ((x₀ : ℂ) + (y : ℂ) * I) - logDeriv L.restr (x₀ : ℂ))
          rwa [add_sub_cancel] at this
      _ ≤ M := by rw [hM]; linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans ?_
  have h2 : |η - -η| = 2 * η := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
  rw [h2]
  have : η ≤ ε / (2 * M) := hηle.trans (min_le_right _ _)
  calc M * (2 * η) ≤ M * (2 * (ε / (2 * M))) := by gcongr
    _ = ε := by field_simp

/-- **Linear count.**  For `a < b` with `f(a), f(b) ≠ 0`, the zero count in `[a,b]` (with
multiplicity) is within `2 Σⱼ Dⱼ` of `(b − a)·D`. -/
theorem abs_zeroCount_sub_le {a b : ℝ} (hab : a < b) (ha : L.restr a ≠ 0) (hb : L.restr b ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ z, z ∈ Z ↔ z ∈ (uIcc a b ×ℂ uIcc (-1 : ℝ) 1) ∧ L.restr z = 0) :
    |(∑ w ∈ Z, ((analyticOrderAt L.restr w).toNat : ℝ)) - (b - a) * L.density| ≤
      2 * (degSum L.P : ℝ) := by
  set C : ℝ := ∑ w ∈ Z, ((analyticOrderAt L.restr w).toNat : ℝ) with hC
  set S : ℝ := (degSum L.P : ℝ) with hS
  have hπ := Real.pi_pos
  -- the bound up to an arbitrary vertical error
  have key : ∀ η, 0 < η → η ≤ 1 →
      |C - (b - a) * L.density| ≤ 2 * S +
        (|∫ y in (-η)..η, (logDeriv L.restr ((a : ℂ) + (y : ℂ) * I)).re| +
          |∫ y in (-η)..η, (logDeriv L.restr ((b : ℂ) + (y : ℂ) * I)).re|) / (2 * Real.pi) := by
    intro η hη hη1
    have hne : ∃ z : ℂ, L.restr z ≠ 0 := ⟨I, L.restr_ne_zero_of_im_ne_zero (by simp)⟩
    have hedge : ∀ {x : ℝ} {t : ℝ}, L.restr x ≠ 0 → L.restr ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro x t hx
      by_cases ht : t = 0
      · simpa [ht] using hx
      · exact L.restr_ne_zero_of_im_ne_zero (by simpa using ht)
    obtain ⟨Z', hZ', hident⟩ := RHTower.exists_entire_argument_variation_rectangle
      L.analyticOnNhd_restr hne hab (show -η < η by linarith)
      (fun x _ => L.restr_ne_zero_of_im_ne_zero (by simpa using hη.ne'))
      (fun x _ => L.restr_ne_zero_of_im_ne_zero (by simpa using hη.ne'))
      (fun t _ => hedge hb) (fun t _ => hedge ha)
    -- the two zero sets coincide: every zero is real
    have hZZ : Z' = Z := by
      ext z
      rw [hZ', hZ]
      simp only [Complex.mem_reProdIm]
      constructor
      · rintro ⟨⟨hre, _⟩, hz⟩
        have him := L.restr_im_eq_zero_of_eq_zero hz
        refine ⟨⟨hre, ?_⟩, hz⟩
        rw [him, uIcc_of_le (by norm_num)]
        exact ⟨by norm_num, by norm_num⟩
      · rintro ⟨⟨hre, _⟩, hz⟩
        have him := L.restr_im_eq_zero_of_eq_zero hz
        refine ⟨⟨hre, ?_⟩, hz⟩
        rw [him, uIcc_of_le (by linarith)]
        exact ⟨by linarith, by linarith⟩
    rw [hZZ] at hident
    have hlow := L.integral_lower_edge (show -η < 0 by linarith) a b
    have hup := L.integral_upper_edge hη a b
    have hlowB := abs_im_radialLog_sub_le (radialFree_of_norm_lt_one L.disk
      (L.norm_lowerPoint_lt_one (show -η < 0 by linarith) b))
    have hlowA := abs_im_radialLog_sub_le (radialFree_of_norm_lt_one L.disk
      (L.norm_lowerPoint_lt_one (show -η < 0 by linarith) a))
    have hupB := abs_im_radialLog_sub_le (radialFree_of_norm_lt_one L.dualDisk
      (L.norm_upperPoint_lt_one hη b))
    have hupA := abs_im_radialLog_sub_le (radialFree_of_norm_lt_one L.dualDisk
      (L.norm_upperPoint_lt_one hη a))
    have hdegP : (L.P.totalDegree : ℝ) ≤ S := by
      rw [hS]; exact_mod_cast totalDegree_le_degSum L.P
    have hdegD : ((dualPoly L.P).totalDegree : ℝ) ≤ S := by
      rw [hS]; exact_mod_cast totalDegree_dualPoly_le L.P
    have hdens : (b - a) * ∑ j, (L.P.degreeOf j : ℝ) * L.freq j =
        2 * Real.pi * ((b - a) * L.density) := by
      rw [density]; field_simp
    push_cast at hident hlow
    rw [hlow, hup, hdens] at hident
    set VA := ∫ y in (-η)..η, (logDeriv L.restr ((a : ℂ) + (y : ℂ) * I)).re with hVA
    set VB := ∫ y in (-η)..η, (logDeriv L.restr ((b : ℂ) + (y : ℂ) * I)).re with hVB
    set lB := (radialLog L.P (L.lowerPoint (-η) b)).im
    set lA := (radialLog L.P (L.lowerPoint (-η) a)).im
    set uB := (radialLog (dualPoly L.P) (L.upperPoint η b)).im
    set uA := (radialLog (dualPoly L.P) (L.upperPoint η a)).im
    set base := (Complex.log (MvPolynomial.eval 0 L.P)).im
    set baseD := (Complex.log (MvPolynomial.eval 0 (dualPoly L.P))).im
    have hmain : 2 * Real.pi * (C - (b - a) * L.density) = VB - VA + (lB - lA) + (uB - uA) := by
      linarith
    have hl : |lB - lA| ≤ 2 * Real.pi * S := by
      have e : lB - lA = (lB - base) - (lA - base) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      nlinarith [hlowB, hlowA]
    have hu : |uB - uA| ≤ 2 * Real.pi * S := by
      have e : uB - uA = (uB - baseD) - (uA - baseD) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      nlinarith [hupB, hupA]
    have h2π : 0 < 2 * Real.pi := by positivity
    have htot : |2 * Real.pi * (C - (b - a) * L.density)| ≤ |VA| + |VB| + 4 * Real.pi * S := by
      rw [hmain]
      calc |VB - VA + (lB - lA) + (uB - uA)| ≤ |VB - VA| + |lB - lA| + |uB - uA| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ (|VB| + |VA|) + 2 * Real.pi * S + 2 * Real.pi * S := by
            gcongr
            exact abs_sub _ _
        _ = |VA| + |VB| + 4 * Real.pi * S := by ring
    rw [abs_mul, abs_of_pos h2π] at htot
    rw [show 2 * S + (|VA| + |VB|) / (2 * Real.pi) = (|VA| + |VB| + 4 * Real.pi * S) / (2 * Real.pi)
      by field_simp; ring]
    rw [le_div_iff₀ h2π]
    linarith
  -- send the vertical edges to zero
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε' : 0 < ε * Real.pi := by positivity
  obtain ⟨ηa, hηa, hA⟩ := L.exists_vertical_small ha hε'
  obtain ⟨ηb, hηb, hB⟩ := L.exists_vertical_small hb hε'
  set η := min (min ηa ηb) 1 with hηdef
  have hη : 0 < η := lt_min (lt_min hηa hηb) one_pos
  have h1 := key η hη (min_le_right _ _)
  have hA' := hA η hη ((min_le_left _ _).trans (min_le_left _ _))
  have hB' := hB η hη ((min_le_left _ _).trans (min_le_right _ _))
  have hsum : (|∫ y in (-η)..η, (logDeriv L.restr ((a : ℂ) + (y : ℂ) * I)).re| +
      |∫ y in (-η)..η, (logDeriv L.restr ((b : ℂ) + (y : ℂ) * I)).re|) / (2 * Real.pi) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

end LeeYangDatum

end

end RHTower.LeeYangCount
