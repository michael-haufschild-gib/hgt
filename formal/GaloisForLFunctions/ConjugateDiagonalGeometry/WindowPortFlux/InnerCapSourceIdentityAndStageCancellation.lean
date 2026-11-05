import GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.CauchyCapCancellationAndPolynomialStage

/-!
# Inner-Cap Source Identity, Off-Line Exponential Residue Isolation, and Polynomial-Stage Cancellation

On every Burnol unit window `[burnolUnitLower m, burnolUnitUpper m]` (`m : ℕ`) and every prefix
`N ≥ capCancelSqrtPrefix m`, the outer horizontal cap `[burnolCapAbscissa m, 3 / 2]` cancels the
`e^t` right vertical-edge flux down to the vertical-line flux `vertFlux (burnolCapAbscissa m)`,
leaving the reduced right-port sum across the shifted vertical line and the inner caps
`[1 / 2, burnolCapAbscissa m]`:

1. **Exact outer-cap reduction to the inner caps `[1 / 2, burnolCapAbscissa m]`**
   (`rightHalfPort_eq_vertFlux_add_innerCapFlux`,
   `burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux`). Whenever `A_N` has no zeros on
   `[σ₁, 3 / 2] × [y₁, y₂]` (`1 / 2 ≤ σ₁ ≤ 3 / 2`), `rightHalfPort y₁ y₂ N t` equals
   `vertFlux σ₁ y₁ y₂ N t + horizCapFlux (1 / 2) σ₁ y₁ y₂ N t` identically for all `t : ℝ`. On
   every Burnol unit window (`N ≥ capCancelSqrtPrefix m`), this holds unconditionally at
   `σ₁ = burnolCapAbscissa m ∈ (3 / 4, 1)` with `‖vertFlux σ_m t‖ = O(exp((σ_m - 1/2) t))`.

2. **Exact inner-cap source identity and bounded-remainder decomposition**
   (`burnolInnerOffLineZeros_subset_strip`, `burnol_innerCap_source_identity`,
   `norm_burnolInnerBoundedSource_le_degree`). Splitting the window zeros of `A_N` into
   `burnolInnerOffLineZeros m N hN` (`1 / 2 < Re z`) and `burnolInnerNonposZeros m N hN`
   (`Re z ≤ 1 / 2`) confines every `z ∈ burnolInnerOffLineZeros m N hN` unconditionally to the
   inner-cap strip `1 / 2 < Re z < burnolCapAbscissa m`, and expresses the inner-cap flux sum
   `vertFlux σ_m + horizCapFlux (1 / 2) σ_m` identically for all `t : ℝ` as
   `burnolInnerOffLineSource m N hN t + burnolInnerBoundedSource m N hN t - leftHalfPort ... t`,
   where `burnolInnerBoundedSource` is bounded on `[0, ∞)` by the window degree and `leftHalfPort`
   is in unweighted `L²(0, ∞)`.

3. **Laplace equivalence at every positive exponent and polynomial-stage equivalences**
   (`integrableOn_innerCapFlux_iff_offLineSource`,
   `innerCap_allExponents_iff_offLineZeros_empty`,
   `innerCap_fixedDegree_polynomialStage_iff_invPoly_corridor`,
   `innerCap_allPolynomialStages_iff_riemannHypothesis`). Because `burnolInnerBoundedSource -
   leftHalfPort` is unconditionally square-integrable against `e^{-xt}` for every `x > 0`, Laplace
   square-integrability of `vertFlux σ_m + horizCapFlux (1 / 2) σ_m` at any stage threshold `x > 0`
   is unconditionally equivalent to Laplace square-integrability of `burnolInnerOffLineSource` at
   `x`. Across all `x > 0` on a single `(m, N)`, cancellation holds if and only if
   `burnolInnerOffLineZeros m N hN = ∅` (`burnolInnerOffLineSource = 0`); at fixed polynomial degree
   `k ≥ 1`, inner-cap cancellation at `fixedPolyDoorStage k c m` (`N ≥ polySqrtPrefix k m`) is
   equivalent to the degree-`k` inverse-polynomial zero-free corridor `|Re ρ - 1/2| ≤ C / |Im ρ|^k`;
   across all `(k, m)`, inner-cap cancellation at every polynomial stage is equivalent to
   `RiemannHypothesis`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux

open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ### 1. Exact outer-cap reduction of `rightHalfPort` to the inner caps `[1 / 2, σ₁]` -/

/-- Whenever `finiteThetaAmplitude N` is boundary-regular on `[-1/2, 3/2] × [y₁, y₂]` and zero-free
on `[σ₁, 3 / 2] × [y₁, y₂]` (`1 / 2 ≤ σ₁ ≤ 3 / 2`), the outer cap `[σ₁, 3 / 2]` cancels
`rightEdgeFlux` identically, reducing `rightHalfPort` to `vertFlux σ₁` plus the inner-cap flux
across `[1 / 2, σ₁]`. -/
theorem rightHalfPort_eq_vertFlux_add_innerCapFlux {σ₁ y₁ y₂ : ℝ}
    (hσ_lo : 1 / 2 ≤ σ₁) (hσ_hi : σ₁ ≤ 3 / 2) (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0)
    (hnz : ∀ z ∈ Icc σ₁ (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0)
    (t : ℝ) :
    rightHalfPort y₁ y₂ N t =
      vertFlux σ₁ y₁ y₂ N t + horizCapFlux (1 / 2) σ₁ y₁ y₂ N t := by
  have hnz₁ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0 := fun x hx =>
    edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
      ⟨by simp, by simpa using hy⟩ (Or.inr (Or.inr (Or.inl (by simp))))
  have hnz₂ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0 := fun x hx =>
    edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
      ⟨by simpa using hy, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
  unfold rightHalfPort
  rw [horizCapFlux_add_adjacent hσ_lo hσ_hi N hnz₁ hnz₂ t,
    show rightEdgeFlux y₁ y₂ N t +
        (horizCapFlux (1 / 2) σ₁ y₁ y₂ N t + horizCapFlux σ₁ (3 / 2) y₁ y₂ N t) =
      (rightEdgeFlux y₁ y₂ N t + horizCapFlux σ₁ (3 / 2) y₁ y₂ N t) +
        horizCapFlux (1 / 2) σ₁ y₁ y₂ N t by ring,
    rightEdgeFlux_add_horizCapFlux_eq_vertFlux hσ_hi hy N hnz t]

/-- **Unconditional reduction of `rightHalfPort` to the inner caps `[1 / 2, burnolCapAbscissa m]`**
on every Burnol unit window (`m : ℕ`, `N ≥ capCancelSqrtPrefix m`). -/
theorem burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux (m : ℕ) {N : ℕ}
    (hN : capCancelSqrtPrefix m ≤ N) :
    3 / 4 < burnolCapAbscissa m ∧ burnolCapAbscissa m < 1 ∧
      (∀ t : ℝ, rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t =
        vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
          horizCapFlux (1 / 2) (burnolCapAbscissa m)
            (burnolUnitLower m) (burnolUnitUpper m) N t) ∧
      (∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
        ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t‖ ≤
          M * Real.exp ((burnolCapAbscissa m - 1 / 2) * t)) := by
  obtain ⟨hlo, hhi, _, hnz, M, hM, hbd⟩ := exists_burnol_subHalfExp_cap_cancellation m hN
  have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_capCancelSqrtPrefix m).trans hN)
  have hy := burnolUnitLower_le_upper m
  have hσ_lo : 1 / 2 ≤ burnolCapAbscissa m := by linarith
  have hσ_hi : burnolCapAbscissa m ≤ 3 / 2 := by linarith
  refine ⟨hlo, hhi, fun t =>
    rightHalfPort_eq_vertFlux_add_innerCapFlux hσ_lo hσ_hi hy N hbdry hnz t, M, hM, fun t => ?_⟩
  rw [← rightEdgeFlux_add_horizCapFlux_eq_vertFlux hσ_hi hy N hnz t]
  exact hbd t

/-! ### 2. Inner-cap source identity and bounded-remainder isolation -/

/-- Boundary-regularity witness on Burnol unit window `m` for `N ≥ capCancelSqrtPrefix m`. -/
private lemma burnolCap_bdry_regular (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N) :
    ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft (burnolUnitLower m))
        (centeredWindowUpperRight (burnolUnitUpper m)) τ) ≠ 0 :=
  burnolUnit_bdry_regular m ((burnolPrefix_le_capCancelSqrtPrefix m).trans hN)

/-- The reflected window of `finiteThetaAmplitude N` on Burnol unit window `m` (`N ≥ capCancelSqrtPrefix m`). -/
def burnolReflectedWindow (m : ℕ) (N : ℕ) (hN : capCancelSqrtPrefix m ≤ N) : ReflectedWindow :=
  centeredThetaWindow (burnolUnitLower_le_upper m) N (burnolCap_bdry_regular m hN)

/-- Off-line right-half zeros (`1 / 2 < Re z`) of `finiteThetaAmplitude N` inside Burnol unit window `m`. -/
def burnolInnerOffLineZeros (m : ℕ) (N : ℕ) (hN : capCancelSqrtPrefix m ≤ N) : Finset ℂ :=
  (burnolReflectedWindow m N hN).Z.filter fun z => 1 / 2 < z.re

/-- Critical-line and left-half zeros (`Re z ≤ 1 / 2`) of `finiteThetaAmplitude N` inside Burnol unit window `m`. -/
def burnolInnerNonposZeros (m : ℕ) (N : ℕ) (hN : capCancelSqrtPrefix m ≤ N) : Finset ℂ :=
  (burnolReflectedWindow m N hN).Z.filter fun z => z.re ≤ 1 / 2

/-- Exponential residue source of right-half off-line zeros inside the inner-cap strip. -/
def burnolInnerOffLineSource (m : ℕ) (N : ℕ) (hN : capCancelSqrtPrefix m ≤ N) (t : ℝ) : ℂ :=
  ∑ z ∈ burnolInnerOffLineZeros m N hN,
    ((burnolReflectedWindow m N hN).mult z : ℂ) * cexp ((t : ℂ) * (z - 1 / 2))

/-- Uniformly bounded exponential source from critical-line and left-half window zeros (`Re z ≤ 1 / 2`). -/
def burnolInnerBoundedSource (m : ℕ) (N : ℕ) (hN : capCancelSqrtPrefix m ≤ N) (t : ℝ) : ℂ :=
  ∑ z ∈ burnolInnerNonposZeros m N hN,
    ((burnolReflectedWindow m N hN).mult z : ℂ) * cexp ((t : ℂ) * (z - 1 / 2))

/-- Every right-half window zero of `finiteThetaAmplitude N` (`N ≥ capCancelSqrtPrefix m`) lies
strictly inside the inner-cap strip `1 / 2 < Re z < burnolCapAbscissa m`. -/
theorem burnolInnerOffLineZeros_subset_strip (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N)
    {z : ℂ} (hz : z ∈ burnolInnerOffLineZeros m N hN) :
    1 / 2 < z.re ∧ z.re < burnolCapAbscissa m ∧
      burnolUnitLower m < z.im ∧ z.im < burnolUnitUpper m ∧
      _root_.RHTower.finiteThetaAmplitude N z = 0 := by
  obtain ⟨hzW, hgt⟩ := Finset.mem_filter.mp hz
  obtain ⟨⟨_, hx_hi, hy_lo, hy_hi⟩, hz0⟩ :=
    (mem_centeredThetaWindow_iff (burnolUnitLower_le_upper m) N
      (burnolCap_bdry_regular m hN) z).mp hzW
  obtain ⟨_, _, _, hnz, _⟩ := exists_burnol_subHalfExp_cap_cancellation m hN
  refine ⟨hgt, ?_, hy_lo, hy_hi, hz0⟩
  by_contra hge
  exact hnz z ⟨⟨not_lt.mp hge, hx_hi.le⟩, ⟨hy_lo.le, hy_hi.le⟩⟩ hz0

/-- Continuity of `burnolInnerOffLineSource`. -/
theorem continuous_burnolInnerOffLineSource (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N) :
    Continuous (burnolInnerOffLineSource m N hN) := by
  unfold burnolInnerOffLineSource
  fun_prop

/-- Continuity of `burnolInnerBoundedSource`. -/
theorem continuous_burnolInnerBoundedSource (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N) :
    Continuous (burnolInnerBoundedSource m N hN) := by
  unfold burnolInnerBoundedSource
  fun_prop

/-- On `[0, ∞)`, `burnolInnerBoundedSource` is uniformly bounded by the window degree. -/
theorem norm_burnolInnerBoundedSource_le_degree (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖burnolInnerBoundedSource m N hN t‖ ≤
      (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) := by
  unfold burnolInnerBoundedSource
  calc ‖∑ z ∈ burnolInnerNonposZeros m N hN,
          ((burnolReflectedWindow m N hN).mult z : ℂ) * cexp ((t : ℂ) * (z - 1 / 2))‖
      ≤ ∑ z ∈ burnolInnerNonposZeros m N hN,
          ‖((burnolReflectedWindow m N hN).mult z : ℂ) * cexp ((t : ℂ) * (z - 1 / 2))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ z ∈ burnolInnerNonposZeros m N hN, ((burnolReflectedWindow m N hN).mult z : ℝ) := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hle : z.re ≤ 1 / 2 := (Finset.mem_filter.mp hz).2
        rw [norm_mul, Complex.norm_natCast, Complex.norm_exp]
        have hexp : Real.exp (((t : ℂ) * (z - 1 / 2)).re) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have hre : ((t : ℂ) * (z - 1 / 2)).re = t * (z.re - 1 / 2) := by simp
          rw [hre]
          exact mul_nonpos_of_nonneg_of_nonpos ht (by linarith)
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) hexp
    _ ≤ ∑ z ∈ (burnolReflectedWindow m N hN).Z, ((burnolReflectedWindow m N hN).mult z : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
          Nat.cast_nonneg _
    _ = (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast centeredThetaWindow_degree (burnolUnitLower_le_upper m) N
          (burnolCap_bdry_regular m hN)

private lemma burnolReflectedWindow_expSum_eq_add (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N)
    (t : ℝ) :
    (burnolReflectedWindow m N hN).expSum t =
      burnolInnerOffLineSource m N hN t + burnolInnerBoundedSource m N hN t := by
  unfold ReflectedWindow.expSum burnolInnerOffLineSource burnolInnerBoundedSource
    burnolInnerOffLineZeros burnolInnerNonposZeros
  have hfilt :
      ((burnolReflectedWindow m N hN).Z.filter fun z => z.re ≤ 1 / 2) =
        ((burnolReflectedWindow m N hN).Z.filter fun z => ¬ 1 / 2 < z.re) :=
    Finset.filter_congr fun _ _ => not_lt.symm
  rw [hfilt]
  exact (Finset.sum_filter_add_sum_filter_not (burnolReflectedWindow m N hN).Z
    (fun z : ℂ => 1 / 2 < z.re) _).symm

/-- **Exact inner-cap source identity on every Burnol unit window.**
For every `m : ℕ`, `N ≥ capCancelSqrtPrefix m`, and `t : ℝ`, the reduced right-port sum across
`σ_m = burnolCapAbscissa m` and the inner caps `[1 / 2, σ_m]` equals the inner-strip off-line
exponential source plus `burnolInnerBoundedSource` minus `leftHalfPort`. -/
theorem burnol_innerCap_source_identity (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N) (t : ℝ) :
    vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
        horizCapFlux (1 / 2) (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t =
      burnolInnerOffLineSource m N hN t + burnolInnerBoundedSource m N hN t -
        leftHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t := by
  obtain ⟨_, _, hcap, _⟩ := burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux m hN
  have hbdry := burnolCap_bdry_regular m hN
  have hy := burnolUnitLower_le_upper m
  have hport := centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort hy N hbdry t
  have hexp : (burnolReflectedWindow m N hN).expSum t =
      centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t :=
    centeredThetaWindow_expSum hy N hbdry t
  calc vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
        horizCapFlux (1 / 2) (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t
      = rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t := (hcap t).symm
    _ = centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t -
          leftHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t :=
        eq_sub_of_add_eq hport.symm
    _ = (burnolReflectedWindow m N hN).expSum t -
          leftHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t := by rw [← hexp]
    _ = burnolInnerOffLineSource m N hN t + burnolInnerBoundedSource m N hN t -
          leftHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t := by
        rw [burnolReflectedWindow_expSum_eq_add m hN t]

/-! ### 3. Exact Laplace equivalence at every positive exponent and polynomial-stage corollaries -/

private lemma norm_add_sq_le_two_mul_add' (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h1 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2
  have h2 : 0 ≤ (‖u‖ - ‖v‖) ^ 2 := sq_nonneg _
  have hid : (‖u‖ + ‖v‖) ^ 2 + (‖u‖ - ‖v‖) ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by ring
  linarith only [h1, h2, hid]

/-- For every `x > 0`, `burnolInnerBoundedSource m N hN` is Laplace-square-integrable on `(0, ∞)`. -/
theorem integrableOn_burnolInnerBoundedSource_sq (m : ℕ) {N : ℕ} (hN : capCancelSqrtPrefix m ≤ N)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(x * t)) * ‖burnolInnerBoundedSource m N hN t‖ ^ 2)
      (Ioi (0 : ℝ)) := by
  set D : ℝ := (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) ^ 2 + 1
  have hdom : IntegrableOn (fun t : ℝ => D * Real.exp ((-x) * t)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hx) 0).const_mul D
  refine hdom.mono'
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      ((continuous_burnolInnerBoundedSource m hN).norm.pow 2)).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  have hbd := norm_burnolInnerBoundedSource_le_degree m hN ht0
  have hsq : ‖burnolInnerBoundedSource m N hN t‖ ^ 2 ≤ D := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hbd 2
    dsimp only [D]; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  calc Real.exp (-(x * t)) * ‖burnolInnerBoundedSource m N hN t‖ ^ 2
      ≤ Real.exp (-(x * t)) * D := mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = D * Real.exp ((-x) * t) := by rw [neg_mul, mul_comm]

/-- **Unconditional inner-cap Laplace equivalence at every positive exponent `x > 0`.**
On every Burnol unit window `m` and `N ≥ capCancelSqrtPrefix m`, Laplace square-integrability of the
reduced right-port sum `vertFlux σ_m + horizCapFlux (1 / 2) σ_m` against `e^{-xt}` is
unconditionally equivalent to Laplace square-integrability of `burnolInnerOffLineSource` against
`e^{-xt}` (and to that of `rightHalfPort` and `centeredThetaExpSum`). -/
theorem integrableOn_innerCapFlux_iff_offLineSource (m : ℕ) {N : ℕ}
    (hN : capCancelSqrtPrefix m ≤ N) {x : ℝ} (hx : 0 < x) :
    IntegrableOn
        (fun t : ℝ => Real.exp (-(x * t)) *
          ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
            horizCapFlux (1 / 2) (burnolCapAbscissa m)
              (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
        (Ioi (0 : ℝ)) ↔
      IntegrableOn
        (fun t : ℝ => Real.exp (-(x * t)) * ‖burnolInnerOffLineSource m N hN t‖ ^ 2)
        (Ioi (0 : ℝ)) := by
  obtain ⟨_, _, hcap, _⟩ := burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux m hN
  have hbdry := burnolCap_bdry_regular m hN
  have hy := burnolUnitLower_le_upper m
  have heq_port :
      (fun t : ℝ => Real.exp (-(x * t)) *
        ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
          horizCapFlux (1 / 2) (burnolCapAbscissa m)
            (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) =
      fun t : ℝ => Real.exp (-(x * t)) *
        ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
    funext fun t => by rw [hcap t]
  rw [heq_port, ← integrableOn_windowEnergy_iff_rightHalfPort hy N hbdry hx.le]
  have hcont_Z : Continuous (centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N) := by
    have heq : centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N =
        fun t => (burnolReflectedWindow m N hN).expSum t :=
      funext fun t => (centeredThetaWindow_expSum hy N hbdry t).symm
    rw [heq]; exact (burnolReflectedWindow m N hN).continuous_expSum
  have hsplit : ∀ t : ℝ,
      centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t =
        burnolInnerOffLineSource m N hN t + burnolInnerBoundedSource m N hN t := fun t => by
    have hexp : (burnolReflectedWindow m N hN).expSum t =
        centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t :=
      centeredThetaWindow_expSum hy N hbdry t
    rw [← hexp, burnolReflectedWindow_expSum_eq_add m hN t]
  have hB := integrableOn_burnolInnerBoundedSource_sq m hN hx
  constructor
  · intro hZ
    have hdom := (hZ.const_mul 2).add (hB.const_mul 2)
    refine hdom.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        ((continuous_burnolInnerOffLineSource m hN).norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_
    have hrw : burnolInnerOffLineSource m N hN t =
        centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t +
          (-burnolInnerBoundedSource m N hN t) := by
      linear_combination -(hsplit t)
    have hsq : ‖burnolInnerOffLineSource m N hN t‖ ^ 2 ≤
        2 * ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 +
          2 * ‖burnolInnerBoundedSource m N hN t‖ ^ 2 := by
      rw [hrw]
      simpa only [norm_neg] using norm_add_sq_le_two_mul_add' _ (-burnolInnerBoundedSource m N hN t)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-(x * t)) * ‖burnolInnerOffLineSource m N hN t‖ ^ 2
        ≤ Real.exp (-(x * t)) *
            (2 * ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 +
              2 * ‖burnolInnerBoundedSource m N hN t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = 2 * (Real.exp (-(x * t)) *
            ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) +
          2 * (Real.exp (-(x * t)) * ‖burnolInnerBoundedSource m N hN t‖ ^ 2) := by ring
  · intro hOff
    have hdom := (hOff.const_mul 2).add (hB.const_mul 2)
    refine hdom.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hcont_Z.norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_
    have hsq : ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 ≤
        2 * ‖burnolInnerOffLineSource m N hN t‖ ^ 2 +
          2 * ‖burnolInnerBoundedSource m N hN t‖ ^ 2 := by
      rw [hsplit t]
      exact norm_add_sq_le_two_mul_add' _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-(x * t)) * ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2
        ≤ Real.exp (-(x * t)) *
            (2 * ‖burnolInnerOffLineSource m N hN t‖ ^ 2 +
              2 * ‖burnolInnerBoundedSource m N hN t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = 2 * (Real.exp (-(x * t)) * ‖burnolInnerOffLineSource m N hN t‖ ^ 2) +
          2 * (Real.exp (-(x * t)) * ‖burnolInnerBoundedSource m N hN t‖ ^ 2) := by ring

/-- **All-exponent inner-cap cancellation characterization on a fixed Burnol window `(m, N)`.**
Laplace square-integrability of `vertFlux σ_m + horizCapFlux (1 / 2) σ_m` holds across all `x > 0`
if and only if `burnolInnerOffLineZeros m N hN = ∅` (equivalently `burnolInnerOffLineSource = 0`,
and equivalently every window zero of `A_N` lies on `Re z = 1 / 2`). -/
theorem innerCap_allExponents_iff_offLineZeros_empty (m : ℕ) {N : ℕ}
    (hN : capCancelSqrtPrefix m ≤ N) :
    ((∀ x : ℝ, 0 < x →
        IntegrableOn
          (fun t : ℝ => Real.exp (-(x * t)) *
            ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
              horizCapFlux (1 / 2) (burnolCapAbscissa m)
                (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ))) ↔
      burnolInnerOffLineZeros m N hN = ∅) ∧
    (burnolInnerOffLineZeros m N hN = ∅ ↔
      ∀ t : ℝ, burnolInnerOffLineSource m N hN t = 0) := by
  have hbdry := burnolCap_bdry_regular m hN
  have hy := burnolUnitLower_le_upper m
  have htfae := subexp_windowEnergy_tfae hy N hbdry
  have h24 : (∀ x : ℝ, 0 < x →
      IntegrableOn
        (fun t : ℝ => Real.exp (-(x * t)) *
          ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
        (Ioi (0 : ℝ))) ↔
      (∀ z : ℂ, -1 / 2 < z.re → z.re < 3 / 2 → burnolUnitLower m < z.im →
        z.im < burnolUnitUpper m → _root_.RHTower.finiteThetaAmplitude N z = 0 → z.re = 1 / 2) :=
    htfae.out 1 3
  obtain ⟨_, _, hcap, _⟩ := burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux m hN
  have hport_iff : (∀ x : ℝ, 0 < x →
      IntegrableOn
        (fun t : ℝ => Real.exp (-(x * t)) *
          ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
            horizCapFlux (1 / 2) (burnolCapAbscissa m)
              (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
        (Ioi (0 : ℝ))) ↔
      (∀ x : ℝ, 0 < x →
        IntegrableOn
          (fun t : ℝ => Real.exp (-(x * t)) *
            ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ))) := by
    refine forall_congr' fun x => imp_congr_right fun hx => ?_
    have heq :
        (fun t : ℝ => Real.exp (-(x * t)) *
          ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
            horizCapFlux (1 / 2) (burnolCapAbscissa m)
              (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) =
        fun t : ℝ => Real.exp (-(x * t)) *
          ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
      funext fun t => by rw [hcap t]
    rw [heq, ← integrableOn_windowEnergy_iff_rightHalfPort hy N hbdry hx.le]
  have hempty_iff :
      (∀ z : ℂ, -1 / 2 < z.re → z.re < 3 / 2 → burnolUnitLower m < z.im →
        z.im < burnolUnitUpper m → _root_.RHTower.finiteThetaAmplitude N z = 0 → z.re = 1 / 2) ↔
      burnolInnerOffLineZeros m N hN = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    constructor
    · intro hpure z hz
      obtain ⟨hzW, hgt⟩ := Finset.mem_filter.mp hz
      obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ :=
        (mem_centeredThetaWindow_iff hy N hbdry z).mp hzW
      have heq := hpure z hx1 hx2 hy1 hy2 hz0
      linarith
    · intro hempty z hx1 hx2 hy1 hy2 hz0
      have hzW : z ∈ (burnolReflectedWindow m N hN).Z :=
        (mem_centeredThetaWindow_iff hy N hbdry z).mpr ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩
      have hle1 : z.re ≤ 1 / 2 := by
        by_contra hgt
        exact hempty z (Finset.mem_filter.mpr ⟨hzW, not_le.mp hgt⟩)
      have hz'W : 1 - star z ∈ (burnolReflectedWindow m N hN).Z :=
        (burnolReflectedWindow m N hN).refl_mem z hzW
      have hle2 : (1 - star z).re ≤ 1 / 2 := by
        by_contra hgt
        exact hempty (1 - star z) (Finset.mem_filter.mpr ⟨hz'W, not_le.mp hgt⟩)
      have hre : (1 - star z).re = 1 - z.re := by simp
      linarith
  have hzero_iff : burnolInnerOffLineZeros m N hN = ∅ ↔
      ∀ t : ℝ, burnolInnerOffLineSource m N hN t = 0 := by
    constructor
    · intro hempty t
      unfold burnolInnerOffLineSource
      rw [hempty, Finset.sum_empty]
    · intro hzero
      rw [← hport_iff.trans (h24.trans hempty_iff)]
      intro x hx
      rw [integrableOn_innerCapFlux_iff_offLineSource m hN hx]
      have heq0 : (fun t : ℝ => Real.exp (-(x * t)) * ‖burnolInnerOffLineSource m N hN t‖ ^ 2) =
          fun _ => 0 := funext fun t => by simp [hzero t]
      rw [heq0]
      exact integrableOn_zero
  exact ⟨hport_iff.trans (h24.trans hempty_iff), hzero_iff⟩

/-- **Fixed-degree polynomial-stage inner-cap cancellation equivalence (`k ≥ 1`).**
At fixed polynomial degree `k ≥ 1`, a degree-`k` inverse-polynomial zero-free corridor
`|Re ρ - 1/2| ≤ C / |Im ρ|^k` for `ξ` is unconditionally equivalent to Laplace square-integrability
of the inner-cap reduced right-port flux `vertFlux σ_m + horizCapFlux (1 / 2) σ_m` — and
equivalently of `burnolInnerOffLineSource` — at the polynomial stage threshold
`1 / (2 * fixedPolyDoorStage k c m)` across `m ≥ m₀` and `N ≥ polySqrtPrefix k m`. -/
theorem innerCap_fixedDegree_polynomialStage_iff_invPoly_corridor {k : ℕ} (hk : 1 ≤ k) :
    ((∃ T₁ C : ℝ, 2 ≤ T₁ ∧ 0 < C ∧
        ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ C / |ρ.im| ^ k) ↔
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (N : ℕ), polySqrtPrefix k m ≤ N →
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
            ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
              horizCapFlux (1 / 2) (burnolCapAbscissa m)
                (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ))) ∧
    ((∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (N : ℕ), polySqrtPrefix k m ≤ N →
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
            ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
              horizCapFlux (1 / 2) (burnolCapAbscissa m)
                (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ))) ↔
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (N : ℕ) (hN : polySqrtPrefix k m ≤ N),
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
            ‖burnolInnerOffLineSource m N
              ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN) t‖ ^ 2)
          (Ioi (0 : ℝ))) := by
  have htfae := invPoly_corridor_iff_fixedDegree_polynomialStage hk
  have h12 := htfae.out 0 1
  constructor
  · refine h12.trans ?_
    refine exists_congr fun c => and_congr_right fun _ => and_congr_right fun _ =>
      exists_congr fun m₀ => forall_congr' fun m => imp_congr_right fun _ =>
        forall_congr' fun N => imp_congr_right fun hN => ?_
    have hNcap := (capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN
    obtain ⟨_, _, hcap, _⟩ := burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux m hNcap
    have hbdry := burnolCap_bdry_regular m hNcap
    have hy := burnolUnitLower_le_upper m
    set n := fixedPolyDoorStage k c m
    have hn6 : 6 ≤ n :=
      (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hx_pos : 0 < 1 / (2 * (n : ℝ)) := by positivity
    have heq :
        (fun t : ℝ => Real.exp (-((1 / (2 * (n : ℝ))) * t)) *
          ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
            horizCapFlux (1 / 2) (burnolCapAbscissa m)
              (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) =
        fun t : ℝ => Real.exp (-((1 / (2 * (n : ℝ))) * t)) *
          ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
      funext fun t => by rw [hcap t]
    rw [heq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(integrableOn_windowEnergy_iff_rightHalfPort hy N hbdry hx_pos.le).mpr h, h⟩
  · refine exists_congr fun c => and_congr_right fun _ => and_congr_right fun _ =>
      exists_congr fun m₀ => forall_congr' fun m => imp_congr_right fun _ =>
        forall_congr' fun N => ?_
    constructor
    · intro h hN
      set n := fixedPolyDoorStage k c m
      have hn6 : 6 ≤ n :=
        (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact (integrableOn_innerCapFlux_iff_offLineSource m
        ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN) (by positivity)).mp (h hN)
    · intro h hN
      set n := fixedPolyDoorStage k c m
      have hn6 : 6 ≤ n :=
        (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact (integrableOn_innerCapFlux_iff_offLineSource m
        ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN) (by positivity)).mpr (h hN)

/-- **Global polynomial-stage inner-cap cancellation equivalence across all Burnol windows.**
Across all polynomial degrees `k : ℕ`, Burnol unit windows `m : ℕ`, and `N ≥ polySqrtPrefix k m`,
inner-cap cancellation at the stage threshold `1 / (2 * doorUnitStage m ((m + 6)^k))` — equivalently
for `vertFlux σ_m + horizCapFlux (1 / 2) σ_m` and for `burnolInnerOffLineSource` — is
unconditionally equivalent to `RiemannHypothesis`. -/
theorem innerCap_allPolynomialStages_iff_riemannHypothesis :
    (RiemannHypothesis ↔
      ∀ k m : ℕ, ∀ N ≥ polySqrtPrefix k m,
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
            ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
              horizCapFlux (1 / 2) (burnolCapAbscissa m)
                (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ))) ∧
    ((∀ k m : ℕ, ∀ N ≥ polySqrtPrefix k m,
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
            ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
              horizCapFlux (1 / 2) (burnolCapAbscissa m)
                (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ))) ↔
      ∀ k m : ℕ, ∀ (N : ℕ) (hN : polySqrtPrefix k m ≤ N),
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
            ‖burnolInnerOffLineSource m N
              ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN) t‖ ^ 2)
          (Ioi (0 : ℝ))) := by
  have h14 := riemannHypothesis_polynomialStage_tfae.out 0 3
  constructor
  · refine h14.trans ?_
    refine forall_congr' fun k => forall_congr' fun m => forall_congr' fun N =>
      imp_congr_right fun hN => ?_
    have hNcap := (capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN
    obtain ⟨_, _, hcap, _⟩ := burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux m hNcap
    have heq :
        (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
          ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) =
        fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
          ‖vertFlux (burnolCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
            horizCapFlux (1 / 2) (burnolCapAbscissa m)
              (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
      funext fun t => by rw [hcap t]
    rw [heq]
  · refine forall_congr' fun k => forall_congr' fun m => forall_congr' fun N => ?_
    constructor
    · intro h hN
      set n := doorUnitStage m ((m + 6) ^ k)
      have hn6 : 6 ≤ n :=
        (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact (integrableOn_innerCapFlux_iff_offLineSource m
        ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN) (by positivity)).mp (h hN)
    · intro h hN
      set n := doorUnitStage m ((m + 6) ^ k)
      have hn6 : 6 ≤ n :=
        (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact (integrableOn_innerCapFlux_iff_offLineSource m
        ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN) (by positivity)).mpr (h hN)

#print axioms rightHalfPort_eq_vertFlux_add_innerCapFlux
#print axioms burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux
#print axioms burnolInnerOffLineZeros_subset_strip
#print axioms burnol_innerCap_source_identity
#print axioms integrableOn_innerCapFlux_iff_offLineSource
#print axioms innerCap_allExponents_iff_offLineZeros_empty
#print axioms innerCap_fixedDegree_polynomialStage_iff_invPoly_corridor
#print axioms innerCap_allPolynomialStages_iff_riemannHypothesis

end GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux

end
