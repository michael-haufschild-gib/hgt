import GaloisForLFunctions.BiScaleUncertainty.PrimePowerTowerDeletionInteraction

/-!
# The prime side on short windows: exact ceilings

On tests supported in an interval of length `L`, the prime side `Σ_n Λ(n) L_n` of the Weil
functional only sees the nodes `log n < L`. Write `w_n = Λ(n)/√n` for the prime atom. As a quadratic
form the prime side is the weighted adjacency operator of the graph `u ~ u ± log n` on the window,
and its top is the slack the archimedean part must pay at aperture `L/2`.

**Theorem** (`abs_primeSide_le_of_window`, `isGreatest_windowDeviations`). For `log 3 < L < log 4`
the exact ceiling of `(A − W)/‖c‖² = Σ_n Λ(n) L_n/‖c‖²` over nonnegative combinations of tests
supported in intervals of length `L` is

`λ₂₃ = (w₃ + √(w₃² + 4 w₂²))/2`,  `w₂ = log 2/√2`, `w₃ = log 3/√3`,

and the floor is `−λ₂₃`. On the first window `log 2 < L ≤ log 3` only the node `2` is visible and
the deletion law of `PrimePowerNodeDeletionPrice` bounds the prime side by the atom `w₂`.

**Mechanism.**
* (`two_mul_abs_re_weilTest_le`, weighted Schur bound) For every positive weight `φ`,
  `2|Re k(s)| ≤ ∫ |f|² (φ(t−s) + φ(t+s))/φ(t)` with the neighbours restricted to the window.
* The window graph for `L < log 4` is a disjoint union of four-vertex paths
  `u + log 2 — u — u + log 3 — u + log 3 − log 2` (weights `w₂, w₃, w₂`), single `w₂`-edges and
  isolated points: the square `u, u + log 2, u + log 3, u + log 6` needs `L > log 6`. The two-valued
  weight `φ = λ₂₃` on `[0, L − log 3) ∪ [log 3, L)` and `φ = w₂` elsewhere is a supersolution
  `Σ w φ(nbr)/φ ≤ λ₂₃` (`windowWeight_schur_le`): `λ₂₃` is the Perron root `λ² = w₃λ + w₂²`.
* The ceiling is attained by the narrow eigenvector test with weights `w₂, λ₂₃, λ₂₃, w₂` on the path.

Since `λ₂₃ < w₂ + w₃` (`lambdaTwoThree_lt_add`), the joint price of the nodes `2` and `3` on this
window is strictly below the sum of their single prices: the additive value needs the cross lag
`log 6 = log 2 + log 3` inside the window, although `Λ(6) = 0`.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. The weighted Schur bound for one shift -/

/-- `2|Re(z w̄)| ≤ (q/p)|z|² + (p/q)|w|²`. -/
theorem two_mul_abs_re_mul_conj_le (z w : ℂ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    2 * |(z * conj w).re| ≤ q / p * ‖z‖ ^ 2 + p / q * ‖w‖ ^ 2 := by
  have h1 : |(z * conj w).re| ≤ ‖z‖ * ‖w‖ := by
    calc |(z * conj w).re| ≤ ‖z * conj w‖ := Complex.abs_re_le_norm _
      _ = ‖z‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]
  have h2 : 2 * (‖z‖ * ‖w‖) ≤ q / p * ‖z‖ ^ 2 + p / q * ‖w‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div _ _ hp.ne' hq.ne',
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (q * ‖z‖ - p * ‖w‖), norm_nonneg z, norm_nonneg w]
  linarith

/-- **Weighted Schur bound.** For `f` supported in `(a, b)` and a weight `φ` with `m ≤ φ ≤ M`,
`2|Re k(s)| ≤ ∫ |f(t)|² (φ(t − s) + φ(t + s))/φ(t)`, neighbours outside `(a, b)` counted as `0`. -/
theorem two_mul_abs_re_weilTest_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {a b : ℝ} (hsupp : ∀ t, f t ≠ 0 → t ∈ Ioo a b) {φ : ℝ → ℝ} (hφm : Measurable φ) {m M : ℝ}
    (hm : 0 < m) (hlo : ∀ t, m ≤ φ t) (hhi : ∀ t, φ t ≤ M) (s : ℝ) :
    2 * |(EF.weilTest f f s).re| ≤
      ∫ t, ‖f t‖ ^ 2 * ((Ioo a b).indicator φ (t - s) / φ t + (Ioo a b).indicator φ (t + s) / φ t) := by
  have hφpos : ∀ t, 0 < φ t := fun t => hm.trans_le (hlo t)
  set ind : ℝ → ℝ := (Ioo a b).indicator φ with hind
  have hind0 : ∀ t, 0 ≤ ind t := fun t => by
    simp only [hind, Set.indicator]; split_ifs
    · exact (hφpos t).le
    · exact le_rfl
  have hindM : ∀ t, ind t ≤ M := fun t => by
    simp only [hind, Set.indicator]; split_ifs
    · exact hhi t
    · linarith [hhi t, hφpos t]
  have hindm : Measurable ind := hφm.indicator measurableSet_Ioo
  -- the pointwise Schur inequality
  have hpt : ∀ t, 2 * |(f t * conj (f (t - s))).re| ≤
      ‖f t‖ ^ 2 * (ind (t - s) / φ t) + ‖f (t - s)‖ ^ 2 * (ind t / φ (t - s)) := by
    intro t
    by_cases h1 : f t = 0
    · rw [h1, zero_mul, Complex.zero_re, abs_zero, mul_zero]
      exact add_nonneg (mul_nonneg (by positivity) (div_nonneg (hind0 _) (hφpos _).le))
        (mul_nonneg (by positivity) (div_nonneg (hind0 _) (hφpos _).le))
    by_cases h2 : f (t - s) = 0
    · rw [h2, map_zero, mul_zero, Complex.zero_re, abs_zero, mul_zero]
      exact add_nonneg (mul_nonneg (by positivity) (div_nonneg (hind0 _) (hφpos _).le))
        (mul_nonneg (by positivity) (div_nonneg (hind0 _) (hφpos _).le))
    have e1 : ind (t - s) = φ (t - s) := Set.indicator_of_mem (hsupp _ h2) φ
    have e2 : ind t = φ t := Set.indicator_of_mem (hsupp _ h1) φ
    rw [e1, e2]
    have := two_mul_abs_re_mul_conj_le (f t) (f (t - s)) (hφpos t) (hφpos (t - s))
    linarith
  -- integrability
  have hcs : HasCompactSupport (fun t => ‖f t‖ ^ 2) :=
    hfc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hnorm : Integrable (fun t => ‖f t‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hcs
  have hA : Integrable (fun t => ‖f t‖ ^ 2 * (ind (t - s) / φ t)) := by
    refine hnorm.mul_bdd (c := M / m) (((hindm.comp (measurable_id.sub_const s)).div hφm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hind0 _) (hφpos _).le)]
    exact div_le_div₀ ((hm.le.trans (hlo t)).trans (hhi t)) (hindM _) hm (hlo _)
  have hA' : Integrable (fun t => ‖f t‖ ^ 2 * (ind (t + s) / φ t)) := by
    refine hnorm.mul_bdd (c := M / m) (((hindm.comp (measurable_id.add_const s)).div hφm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hind0 _) (hφpos _).le)]
    exact div_le_div₀ ((hm.le.trans (hlo t)).trans (hhi t)) (hindM _) hm (hlo _)
  have hB : Integrable (fun t => ‖f (t - s)‖ ^ 2 * (ind t / φ (t - s))) := by
    have := hA'.comp_sub_right s
    simpa only [sub_add_cancel] using this
  have hk : Integrable (fun t => f t * conj (f (t - s))) :=
    (hf.mul (continuous_conj.comp (hf.comp (continuous_id.sub continuous_const)))).integrable_of_hasCompactSupport
      hfc.mul_right
  -- integrate
  have hre_eq : (∫ t, f t * conj (f (t - s))).re = ∫ t, (f t * conj (f (t - s))).re :=
    (integral_re hk).symm
  rw [WeilSpectral.weilTest_apply, hre_eq]
  have hre : Integrable (fun t => (f t * conj (f (t - s))).re) := hk.re
  calc 2 * |∫ t, (f t * conj (f (t - s))).re|
      ≤ ∫ t, 2 * |(f t * conj (f (t - s))).re| := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (by norm_num)
    _ ≤ ∫ t, (‖f t‖ ^ 2 * (ind (t - s) / φ t) + ‖f (t - s)‖ ^ 2 * (ind t / φ (t - s))) :=
        integral_mono (hre.abs.const_mul 2) (hA.add hB) hpt
    _ = (∫ t, ‖f t‖ ^ 2 * (ind (t - s) / φ t)) + ∫ t, ‖f t‖ ^ 2 * (ind (t + s) / φ t) := by
        have hBA : ∫ t, ‖f (t - s)‖ ^ 2 * (ind t / φ (t - s)) =
            ∫ t, ‖f t‖ ^ 2 * (ind (t + s) / φ t) := by
          have := integral_add_right_eq_self (μ := volume)
            (fun t => ‖f (t - s)‖ ^ 2 * (ind t / φ (t - s))) s
          simp only [add_sub_cancel_right] at this
          exact this.symm
        rw [integral_add hA hB, hBA]
    _ = ∫ t, (‖f t‖ ^ 2 * (ind (t - s) / φ t) + ‖f t‖ ^ 2 * (ind (t + s) / φ t)) :=
        (integral_add hA hA').symm
    _ = _ := by
        congr 1; funext t; ring

/-- The Schur integrand is integrable. -/
theorem integrable_schurIntegrand {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {I : Set ℝ} (hI : MeasurableSet I) {φ : ℝ → ℝ} (hφm : Measurable φ) {m M : ℝ}
    (hm : 0 < m) (hlo : ∀ t, m ≤ φ t) (hhi : ∀ t, φ t ≤ M) (s : ℝ) :
    Integrable (fun t => ‖f t‖ ^ 2 * (I.indicator φ (t - s) / φ t + I.indicator φ (t + s) / φ t)) := by
  have hφpos : ∀ t, 0 < φ t := fun t => hm.trans_le (hlo t)
  have hcs : HasCompactSupport (fun t => ‖f t‖ ^ 2) :=
    hfc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hnorm : Integrable (fun t => ‖f t‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hcs
  have hindm : Measurable (I.indicator φ) := hφm.indicator hI
  have hb : ∀ x, 0 ≤ I.indicator φ x ∧ I.indicator φ x ≤ M := fun x => by
    simp only [Set.indicator]; split_ifs
    · exact ⟨(hφpos x).le, hhi x⟩
    · exact ⟨le_rfl, (hφpos x).le.trans (hhi x)⟩
  refine hnorm.mul_bdd (c := 2 * (M / m))
    ((((hindm.comp (measurable_id.sub_const s)).div hφm).add
      ((hindm.comp (measurable_id.add_const s)).div hφm)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  have h1 : I.indicator φ (t - s) / φ t ≤ M / m :=
    div_le_div₀ ((hm.le.trans (hlo t)).trans (hhi t)) (hb _).2 hm (hlo _)
  have h2 : I.indicator φ (t + s) / φ t ≤ M / m :=
    div_le_div₀ ((hm.le.trans (hlo t)).trans (hhi t)) (hb _).2 hm (hlo _)
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (div_nonneg (hb _).1 (hφpos _).le)
    (div_nonneg (hb _).1 (hφpos _).le))]
  linarith

/-! ### 2. The second window -/

/-- The prime atom `w₂ = log 2/√2`. -/
def atomTwo : ℝ := Real.log 2 / Real.sqrt 2

/-- The prime atom `w₃ = log 3/√3`. -/
def atomThree : ℝ := Real.log 3 / Real.sqrt 3

/-- The Perron root `λ₂₃ = (w₃ + √(w₃² + 4w₂²))/2` of the path with weights `w₂, w₃, w₂`. -/
def lambdaTwoThree : ℝ := (atomThree + Real.sqrt (atomThree ^ 2 + 4 * atomTwo ^ 2)) / 2

theorem atomTwo_pos : 0 < atomTwo :=
  div_pos (Real.log_pos one_lt_two) (Real.sqrt_pos.mpr two_pos)

theorem atomThree_pos : 0 < atomThree :=
  div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

theorem sqrt_disc_sq : Real.sqrt (atomThree ^ 2 + 4 * atomTwo ^ 2) ^ 2 = atomThree ^ 2 + 4 * atomTwo ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem two_atomTwo_lt_sqrt_disc : 2 * atomTwo < Real.sqrt (atomThree ^ 2 + 4 * atomTwo ^ 2) := by
  rw [Real.lt_sqrt (by linarith [atomTwo_pos])]
  nlinarith [atomThree_pos]

/-- The Perron equation `λ² = w₃λ + w₂²`. -/
theorem lambdaTwoThree_sq : lambdaTwoThree ^ 2 = atomThree * lambdaTwoThree + atomTwo ^ 2 := by
  unfold lambdaTwoThree
  nlinarith [sqrt_disc_sq]

theorem atomTwo_lt_lambdaTwoThree : atomTwo < lambdaTwoThree := by
  unfold lambdaTwoThree
  linarith [two_atomTwo_lt_sqrt_disc, atomThree_pos]

theorem lambdaTwoThree_pos : 0 < lambdaTwoThree := atomTwo_pos.trans atomTwo_lt_lambdaTwoThree

/-- **Strict sub-additivity on the second window**: `λ₂₃ < w₂ + w₃`. -/
theorem lambdaTwoThree_lt_add : lambdaTwoThree < atomTwo + atomThree := by
  unfold lambdaTwoThree
  have h : Real.sqrt (atomThree ^ 2 + 4 * atomTwo ^ 2) < atomThree + 2 * atomTwo := by
    rw [Real.sqrt_lt' (by linarith [atomTwo_pos, atomThree_pos])]
    nlinarith [atomTwo_pos, atomThree_pos]
  linarith

/-- The two-valued supersolution: `λ₂₃` on `[0, L − log 3) ∪ [log 3, L)`, `w₂` elsewhere. -/
def windowWeight (a L t : ℝ) : ℝ :=
  if t - a < L - Real.log 3 ∨ Real.log 3 ≤ t - a then lambdaTwoThree else atomTwo

theorem measurable_windowWeight (a L : ℝ) : Measurable (windowWeight a L) := by
  unfold windowWeight
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt (measurable_id.sub_const a) measurable_const).union
    (measurableSet_le measurable_const (measurable_id.sub_const a))

theorem atomTwo_le_windowWeight (a L t : ℝ) : atomTwo ≤ windowWeight a L t := by
  unfold windowWeight; split_ifs
  · exact atomTwo_lt_lambdaTwoThree.le
  · exact le_rfl

theorem windowWeight_le (a L t : ℝ) : windowWeight a L t ≤ lambdaTwoThree := by
  unfold windowWeight; split_ifs
  · exact le_rfl
  · exact atomTwo_lt_lambdaTwoThree.le

/-- Numerical relations between `log 2`, `log 3`, `log 4`. -/
theorem log_relations :
    0 < Real.log 2 ∧ Real.log 2 < Real.log 3 ∧ Real.log 4 = 2 * Real.log 2 ∧
      3 * Real.log 2 < 2 * Real.log 3 := by
  refine ⟨Real.log_pos one_lt_two, Real.log_lt_log two_pos (by norm_num), ?_, ?_⟩
  · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  · have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 3) (by norm_num : (2 : ℝ) ^ 3 < 3 ^ 2)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith

/-- **The supersolution inequality.** On the window `(a, a + L)`, `L < log 4`, the weighted
neighbour sum `Σ_s w_s (φ(t − s) + φ(t + s))/φ(t)` over the shifts `log 2`, `log 3` is at most
`λ₂₃`. -/
theorem windowWeight_schur_le {a L t : ℝ} (hL : L < Real.log 4) (ht : t ∈ Ioo a (a + L)) :
    atomTwo * ((Ioo a (a + L)).indicator (windowWeight a L) (t - Real.log 2) / windowWeight a L t +
        (Ioo a (a + L)).indicator (windowWeight a L) (t + Real.log 2) / windowWeight a L t) +
      atomThree * ((Ioo a (a + L)).indicator (windowWeight a L) (t - Real.log 3) /
          windowWeight a L t +
        (Ioo a (a + L)).indicator (windowWeight a L) (t + Real.log 3) / windowWeight a L t) ≤
      lambdaTwoThree := by
  obtain ⟨h2, h23, h4, h98⟩ := log_relations
  rw [h4] at hL
  obtain ⟨hta, htb⟩ := ht
  set φ := windowWeight a L with hφ
  set I := Ioo a (a + L) with hI
  have hlam := lambdaTwoThree_pos
  have hw2 := atomTwo_pos
  have hw3 := atomThree_pos
  have hsq := lambdaTwoThree_sq
  have hind_le : ∀ x, I.indicator φ x ≤ lambdaTwoThree := fun x => by
    simp only [Set.indicator]; split_ifs
    · exact windowWeight_le a L x
    · exact hlam.le
  have hind_nn : ∀ x, 0 ≤ I.indicator φ x := fun x => by
    simp only [Set.indicator]; split_ifs
    · exact hw2.le.trans (atomTwo_le_windowWeight a L x)
    · exact le_rfl
  have out : ∀ x, x ∉ I → I.indicator φ x = 0 := fun x hx => Set.indicator_of_notMem hx φ
  have inn : ∀ x, x ∈ I → I.indicator φ x = φ x := fun x hx => Set.indicator_of_mem hx φ
  by_cases hA : t - a < L - Real.log 3
  · -- a path centre on the low side
    have hφt : φ t = lambdaTwoThree := by simp only [hφ, windowWeight]; rw [if_pos (Or.inl hA)]
    have e1 : I.indicator φ (t - Real.log 2) = 0 := out _ (fun h => by linarith [h.1])
    have e2 : I.indicator φ (t - Real.log 3) = 0 := out _ (fun h => by linarith [h.1])
    have e3 : I.indicator φ (t + Real.log 2) = atomTwo := by
      rw [inn _ ⟨by linarith, by linarith⟩]
      simp only [hφ, windowWeight]
      rw [if_neg (by push Not; constructor <;> linarith)]
    have e4 : I.indicator φ (t + Real.log 3) = lambdaTwoThree := by
      rw [inn _ ⟨by linarith, by linarith⟩]
      simp only [hφ, windowWeight]
      rw [if_pos (Or.inr (by linarith))]
    rw [hφt, e1, e2, e3, e4]
    field_simp
    nlinarith
  by_cases hC : Real.log 3 ≤ t - a
  · -- a path centre on the high side
    have hφt : φ t = lambdaTwoThree := by simp only [hφ, windowWeight]; rw [if_pos (Or.inr hC)]
    have e1 : I.indicator φ (t + Real.log 2) = 0 := out _ (fun h => by linarith [h.2])
    have e2 : I.indicator φ (t + Real.log 3) = 0 := out _ (fun h => by linarith [h.2])
    have e3 : I.indicator φ (t - Real.log 2) = atomTwo := by
      rw [inn _ ⟨by linarith, by linarith⟩]
      simp only [hφ, windowWeight]
      rw [if_neg (by push Not; constructor <;> linarith)]
    have e4 := hind_le (t - Real.log 3)
    rw [hφt, e1, e2, e3]
    have key : atomTwo * (atomTwo / lambdaTwoThree + 0 / lambdaTwoThree) +
        atomThree * (I.indicator φ (t - Real.log 3) / lambdaTwoThree + 0 / lambdaTwoThree) ≤
        atomTwo * (atomTwo / lambdaTwoThree) + atomThree * (lambdaTwoThree / lambdaTwoThree) := by
      simp only [zero_div, add_zero]
      gcongr
    refine key.trans (le_of_eq ?_)
    field_simp
    nlinarith
  · -- a leaf, a single edge or an isolated point: weight `w₂`, at most one neighbour
    have hφt : φ t = atomTwo := by
      simp only [hφ, windowWeight]; rw [if_neg (by push Not; exact ⟨by linarith, by linarith⟩)]
    have e1 : I.indicator φ (t - Real.log 3) = 0 := out _ (fun h => by push Not at hC; linarith [h.1])
    have e2 : I.indicator φ (t + Real.log 3) = 0 := out _ (fun h => by push Not at hA; linarith [h.2])
    have hone : I.indicator φ (t - Real.log 2) + I.indicator φ (t + Real.log 2) ≤ lambdaTwoThree := by
      by_cases hm : t - Real.log 2 ∈ I
      · have : t + Real.log 2 ∉ I := fun h => by linarith [hm.1, h.2]
        rw [out _ this, add_zero]; exact hind_le _
      · rw [out _ hm, zero_add]; exact hind_le _
    rw [hφt, e1, e2, zero_div, zero_add, mul_zero, add_zero, ← add_div, mul_div_assoc']
    rw [div_le_iff₀ hw2]
    nlinarith

/-! ### 3. The ceiling on the second window -/

/-- A correlation vanishes at every lag of size at least the window length. -/
theorem weilTest_eq_zero_of_window {f : ℝ → ℂ} {a L : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Ioo a (a + L)) {y : ℝ} (hy : L ≤ |y|) : EF.weilTest f f y = 0 := by
  rw [WeilSpectral.weilTest_apply]
  have : (fun u => f u * conj (f (u - y))) = fun _ => 0 := by
    funext u
    by_cases h1 : f u = 0
    · rw [h1, zero_mul]
    by_cases h2 : f (u - y) = 0
    · rw [h2, map_zero, mul_zero]
    exfalso
    have m1 := hsupp u h1
    have m2 := hsupp _ h2
    rcases le_abs'.mp hy with h | h <;> linarith [m1.1, m1.2, m2.1, m2.2]
  rw [this, integral_zero]

theorem logValue_eq_zero_of_window {f : ℝ → ℂ} {a L : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Ioo a (a + L)) {n : ℕ} (hn : 1 ≤ n) (hL : L ≤ Real.log n) :
    logValue f n = 0 := by
  have h0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [logValue, weilTest_eq_zero_of_window hsupp (by rwa [abs_of_nonneg h0]),
    weilTest_eq_zero_of_window hsupp (by rwa [abs_neg, abs_of_nonneg h0])]
  simp

/-- On a window shorter than `log 4` only the nodes `2` and `3` are visible. -/
theorem primeSide_eq_of_window {f : WeilTestFn} {a L : ℝ} (hL : L < Real.log 4)
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) :
    linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) =
      atomTwo * ((EF.weilTest f.1 f.1 (Real.log 2)).re + (EF.weilTest f.1 f.1 (-Real.log 2)).re) +
        atomThree * ((EF.weilTest f.1 f.1 (Real.log 3)).re +
          (EF.weilTest f.1 f.1 (-Real.log 3)).re) := by
  classical
  have hvec : logVector f = Finsupp.single (⟨2, le_rfl⟩ : LogIndex) (logValue f.1 2) +
      Finsupp.single (⟨3, by norm_num⟩ : LogIndex) (logValue f.1 3) := by
    ext j
    rw [logVector_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h2 : (j : ℕ) = 2
    · rw [if_pos (Subtype.ext h2.symm), if_neg (fun h => by
        have := congrArg Subtype.val h; simp at this; omega), add_zero, h2]
    by_cases h3 : (j : ℕ) = 3
    · rw [if_neg (fun h => h2 (congrArg Subtype.val h).symm), if_pos (Subtype.ext h3.symm),
        zero_add, h3]
    rw [if_neg (fun h => h2 (congrArg Subtype.val h).symm),
      if_neg (fun h => h3 (congrArg Subtype.val h).symm), add_zero]
    have hj4 : 4 ≤ (j : ℕ) := by have := j.2; omega
    exact logValue_eq_zero_of_window hsupp (by omega)
      (hL.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hj4)))
  rw [hvec, map_add, linearCombination_single, linearCombination_single, smul_eq_mul, smul_eq_mul]
  simp only [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three, logValue, Nat.cast_ofNat,
    atomTwo, atomThree, Complex.add_re]
  ring

/-- **The second-window ceiling for one test.** -/
theorem abs_primeSide_le_of_window {f : WeilTestFn} {a L : ℝ} (hL : L < Real.log 4)
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) :
    |linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f)| ≤ lambdaTwoThree * ∫ u, ‖f.1 u‖ ^ 2 := by
  rw [primeSide_eq_of_window hL hsupp]
  have hfc := f.2.1.continuous
  have hfs := f.2.2
  set φ := windowWeight a L with hφ
  have hφm := measurable_windowWeight a L
  have hlo := atomTwo_le_windowWeight a L
  have hhi := windowWeight_le a L
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ, F = fun s t => ‖f.1 t‖ ^ 2 *
      ((Ioo a (a + L)).indicator φ (t - s) / φ t + (Ioo a (a + L)).indicator φ (t + s) / φ t) :=
    ⟨_, rfl⟩
  have hS : ∀ s, 2 * |(EF.weilTest f.1 f.1 s).re| ≤ ∫ t, F s t := fun s => by
    rw [hF]; exact two_mul_abs_re_weilTest_le hfc hfs hsupp hφm atomTwo_pos hlo hhi s
  have hI : ∀ s, Integrable (F s) := fun s => by
    rw [hF]; exact integrable_schurIntegrand hfc hfs (measurableSet_Ioo (a := a) (b := a + L))
      hφm atomTwo_pos hlo hhi s
  have hneg : ∀ s, F (-s) = F s := fun s => by
    rw [hF]; funext t; simp only [sub_neg_eq_add, ← sub_eq_add_neg]; ring
  have hpair : ∀ s, |(EF.weilTest f.1 f.1 s).re| + |(EF.weilTest f.1 f.1 (-s)).re| ≤ ∫ t, F s t := by
    intro s
    have h1 := hS s
    have h2 := hS (-s)
    rw [hneg] at h2
    linarith
  have hw2 := atomTwo_pos
  have hw3 := atomThree_pos
  have hcs : HasCompactSupport (fun t => ‖f.1 t‖ ^ 2) :=
    hfs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hnorm : Integrable (fun t => ‖f.1 t‖ ^ 2) :=
    (hfc.norm.pow 2).integrable_of_hasCompactSupport hcs
  calc |atomTwo * ((EF.weilTest f.1 f.1 (Real.log 2)).re + (EF.weilTest f.1 f.1 (-Real.log 2)).re) +
        atomThree * ((EF.weilTest f.1 f.1 (Real.log 3)).re + (EF.weilTest f.1 f.1 (-Real.log 3)).re)|
      ≤ atomTwo * (∫ t, F (Real.log 2) t) + atomThree * ∫ t, F (Real.log 3) t := by
        have e2 := hpair (Real.log 2)
        have e3 := hpair (Real.log 3)
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hw2, abs_of_pos hw3]
        gcongr
        · exact (abs_add_le _ _).trans e2
        · exact (abs_add_le _ _).trans e3
    _ = ∫ t, (atomTwo * F (Real.log 2) t + atomThree * F (Real.log 3) t) := by
        rw [integral_add ((hI _).const_mul _) ((hI _).const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ ∫ t, lambdaTwoThree * ‖f.1 t‖ ^ 2 := by
        refine integral_mono (((hI _).const_mul _).add ((hI _).const_mul _))
          (hnorm.const_mul _) fun t => ?_
        rw [hF]
        by_cases h0 : f.1 t = 0
        · simp [h0]
        have hb := windowWeight_schur_le hL (hsupp t h0)
        simp only
        have : atomTwo * (‖f.1 t‖ ^ 2 * ((Ioo a (a + L)).indicator φ (t - Real.log 2) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 2) / φ t)) +
            atomThree * (‖f.1 t‖ ^ 2 * ((Ioo a (a + L)).indicator φ (t - Real.log 3) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 3) / φ t)) =
            ‖f.1 t‖ ^ 2 * (atomTwo * ((Ioo a (a + L)).indicator φ (t - Real.log 2) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 2) / φ t) +
            atomThree * ((Ioo a (a + L)).indicator φ (t - Real.log 3) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 3) / φ t)) := by ring
        rw [this, mul_comm lambdaTwoThree]
        exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = lambdaTwoThree * ∫ u, ‖f.1 u‖ ^ 2 := integral_const_mul _ _

/-- **The second-window ceiling.** For every nonnegative combination of tests, each supported in
an interval of length `L < log 4`: `|A − W| ≤ λ₂₃ ‖c‖²`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_window {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    {L : ℝ} (hL : L < Real.log 4)
    (hsupp : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) :
    |nodeArchEnergy c - weilEnergy c| ≤ lambdaTwoThree * massOf c := by
  rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_eq,
    linearCombination_apply ℝ (v := logVector), map_finsuppSum]
  have hX : ∀ f ∈ c.support,
      |linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (c f • logVector f)| ≤ c f * (lambdaTwoThree * ∫ u, ‖f.1 u‖ ^ 2) := by
    intro f hf
    obtain ⟨a, ha⟩ := hsupp f hf
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hc f)]
    exact mul_le_mul_of_nonneg_left (abs_primeSide_le_of_window hL ha) (hc f)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [WeilOneSided.massOf, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  have := hX f hf
  linarith

/-! ### 4. Attainment: the narrow Perron test on one path -/

/-- The Perron weights `λ₂₃, σw₂, σλ₂₃, w₂` on the path vertices `0, log 2, log 3, log 3 − log 2`. -/
def fourCoeff (σ : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then lambdaTwoThree else if m = 1 then σ * atomTwo else if m = 2 then σ * lambdaTwoThree
    else atomTwo

/-- The path vertices `0, log 2, log 3, log 3 − log 2`. -/
def fourShift (m : ℕ) : ℝ :=
  if m = 0 then 0 else if m = 1 then Real.log 2 else if m = 2 then Real.log 3
    else Real.log 3 - Real.log 2

/-- The narrow Perron test of one path component. -/
def fourBump (j : ℕ) (σ : ℝ) (u : ℝ) : ℂ :=
  ∑ m ∈ Finset.range 4, ((fourCoeff σ m : ℝ) : ℂ) * narrowBumpC j (u - fourShift m)

theorem contDiff_fourBump (j : ℕ) (σ : ℝ) : ContDiff ℝ 2 (fourBump j σ) := by
  unfold fourBump
  refine ContDiff.sum fun m _ => contDiff_const.mul ?_
  exact ((contDiff_narrowBumpC j).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const)

theorem fourShift_mem (m : ℕ) : 0 ≤ fourShift m ∧ fourShift m ≤ 2 := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  unfold fourShift
  split_ifs <;> constructor <;> linarith

theorem hasCompactSupport_fourBump (j : ℕ) (σ : ℝ) : HasCompactSupport (fourBump j σ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 3)) fun u hu => ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  unfold fourBump
  refine Finset.sum_eq_zero fun m _ => ?_
  obtain ⟨h0, h2⟩ := fourShift_mem m
  have hr : 1 / (4 * ((j : ℝ) + 1)) < |u - fourShift m| := by
    have : 1 / (4 * ((j : ℝ) + 1)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    rcases hu with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [narrowBumpC_eq_zero j hr, mul_zero]

/-- The narrow Perron test as a Weil test. -/
def fourBumpFn (j : ℕ) (σ : ℝ) : WeilTestFn :=
  ⟨fourBump j σ, contDiff_fourBump j σ, hasCompactSupport_fourBump j σ⟩

/-- The gaps between the path lags. -/
theorem path_gaps : 1 / 3 ≤ Real.log 3 - Real.log 2 ∧ 1 / 4 ≤ 2 * Real.log 2 - Real.log 3 ∧
    0.69 < Real.log 2 := by
  refine ⟨?_, ?_, by linarith [Real.log_two_gt_d9]⟩
  · rw [← Real.log_div (by norm_num) (by norm_num)]
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    norm_num at this ⊢; linarith
  · rw [show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
      ← Real.log_div (by norm_num) (by norm_num)]
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at this ⊢; linarith

theorem narrowCorr_eq_zero_of_quarter {j : ℕ} (hj : 2 ≤ j) {z : ℝ} (hz : 1 / 4 ≤ |z|) :
    EF.weilTest (narrowBumpC j) (narrowBumpC j) z = 0 := by
  refine weilTest_narrowBumpC_eq_zero j (lt_of_lt_of_le ?_ hz)
  have : (2 : ℝ) ≤ j := by exact_mod_cast hj
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The autocorrelation of the narrow Perron test, as sixteen lag terms. -/
theorem weilTest_fourBump (j : ℕ) (σ y : ℝ) :
    EF.weilTest (fourBump j σ) (fourBump j σ) y =
      ∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4,
        ((fourCoeff σ m * fourCoeff σ m' : ℝ) : ℂ) *
          EF.weilTest (narrowBumpC j) (narrowBumpC j) (y - fourShift m + fourShift m') := by
  unfold fourBump
  rw [weilTest_sum_translates (contDiff_narrowBumpC j).continuous (hasCompactSupport_narrowBumpC j)]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  rw [Complex.conj_ofReal]; push_cast; ring

/-- **Lag selection.** If every lag of the path either equals `y` or misses it by `1/4`, the
correlation at `y` is the selected coefficient mass times the seed correlation at `0`. -/
theorem weilTest_fourBump_select {j : ℕ} (hj : 2 ≤ j) (σ y : ℝ)
    (hsep : ∀ m < 4, ∀ m' < 4, fourShift m - fourShift m' ≠ y →
      1 / 4 ≤ |y - fourShift m + fourShift m'|) :
    EF.weilTest (fourBump j σ) (fourBump j σ) y =
      ((∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4,
          if fourShift m - fourShift m' = y then fourCoeff σ m * fourCoeff σ m' else 0 : ℝ) : ℂ) *
        ((∫ t, (narrowBump j t) ^ 2 : ℝ) : ℂ) := by
  rw [weilTest_fourBump, ← weilTest_narrowBumpC_zero, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [Finset.mem_range] at hm hm'
  by_cases h : fourShift m - fourShift m' = y
  · rw [if_pos h, show y - fourShift m + fourShift m' = 0 by linarith]
  · rw [if_neg h, narrowCorr_eq_zero_of_quarter hj (hsep m hm m' hm' h)]
    simp

theorem fourShift_zero : fourShift 0 = 0 := by simp [fourShift]
theorem fourShift_one : fourShift 1 = Real.log 2 := by simp [fourShift]
theorem fourShift_two : fourShift 2 = Real.log 3 := by simp [fourShift]
theorem fourShift_three : fourShift 3 = Real.log 3 - Real.log 2 := by simp [fourShift]

/-- The separation of the path lags at the five evaluation points. -/
theorem fourShift_sep (y : ℝ)
    (hy : y = 0 ∨ y = Real.log 2 ∨ y = -Real.log 2 ∨ y = Real.log 3 ∨ y = -Real.log 3) :
    ∀ m < 4, ∀ m' < 4, fourShift m - fourShift m' ≠ y →
      1 / 4 ≤ |y - fourShift m + fourShift m'| := by
  obtain ⟨g1, g2, g3⟩ := path_gaps
  intro m hm m' hm' h
  rcases hy with rfl | rfl | rfl | rfl | rfl <;>
  · interval_cases m <;> interval_cases m' <;>
    simp only [fourShift_zero, fourShift_one, fourShift_two, fourShift_three] at h ⊢ <;>
    first
      | (apply le_abs.mpr; first | (left; linarith) | (right; linarith))
      | exact absurd (by ring1) h

/-- Evaluating a selected sum through an explicit table. -/
theorem select_sum_eq (σ y : ℝ) (E : ℕ → ℕ → ℝ)
    (hE : ∀ m < 4, ∀ m' < 4,
      (if fourShift m - fourShift m' = y then fourCoeff σ m * fourCoeff σ m' else 0) = E m m') :
    (∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4,
      if fourShift m - fourShift m' = y then fourCoeff σ m * fourCoeff σ m' else 0) =
      ∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4, E m m' :=
  Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun m' hm' =>
    hE m (Finset.mem_range.mp hm) m' (Finset.mem_range.mp hm')


/-- The matching table of the origin. -/
def tableZero (σ : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => fourCoeff σ 0 * fourCoeff σ 0
  | 1, 1 => fourCoeff σ 1 * fourCoeff σ 1
  | 2, 2 => fourCoeff σ 2 * fourCoeff σ 2
  | 3, 3 => fourCoeff σ 3 * fourCoeff σ 3
  | _, _ => 0

/-- The matching table of `log 2`. -/
def tableTwo (σ : ℝ) : ℕ → ℕ → ℝ
  | 1, 0 => fourCoeff σ 1 * fourCoeff σ 0
  | 2, 3 => fourCoeff σ 2 * fourCoeff σ 3
  | _, _ => 0

/-- The matching table of `−log 2`. -/
def tableTwoNeg (σ : ℝ) : ℕ → ℕ → ℝ
  | 0, 1 => fourCoeff σ 0 * fourCoeff σ 1
  | 3, 2 => fourCoeff σ 3 * fourCoeff σ 2
  | _, _ => 0

/-- The matching table of `log 3`. -/
def tableThree (σ : ℝ) : ℕ → ℕ → ℝ
  | 2, 0 => fourCoeff σ 2 * fourCoeff σ 0
  | _, _ => 0

/-- The matching table of `−log 3`. -/
def tableThreeNeg (σ : ℝ) : ℕ → ℕ → ℝ
  | 0, 2 => fourCoeff σ 0 * fourCoeff σ 2
  | _, _ => 0

/-- The table tactic: decide each lag against the target from the gaps. -/
macro "path_table" : tactic => `(tactic| (
  intro m hm m' hm'
  obtain ⟨g1, g2, g3⟩ := path_gaps
  interval_cases m <;> interval_cases m' <;>
    simp only [fourShift_zero, fourShift_one, fourShift_two, fourShift_three, tableZero, tableTwo,
      tableTwoNeg, tableThree, tableThreeNeg] <;>
    split_ifs with h <;> first | rfl | (exfalso; exact h (by ring1)) | (exfalso; linarith)))

theorem sum_tableZero (σ : ℝ) :
    (∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4, tableZero σ m m') =
      lambdaTwoThree ^ 2 + (σ * atomTwo) ^ 2 + (σ * lambdaTwoThree) ^ 2 + atomTwo ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, tableZero, fourCoeff]
  norm_num; ring

theorem sum_tableTwo (σ : ℝ) :
    (∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4, tableTwo σ m m') =
      2 * σ * atomTwo * lambdaTwoThree := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, tableTwo, fourCoeff]
  norm_num; ring

theorem sum_tableTwoNeg (σ : ℝ) :
    (∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4, tableTwoNeg σ m m') =
      2 * σ * atomTwo * lambdaTwoThree := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, tableTwoNeg, fourCoeff]
  norm_num; ring

theorem sum_tableThree (σ : ℝ) :
    (∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4, tableThree σ m m') = σ * lambdaTwoThree ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, tableThree, fourCoeff]
  norm_num; ring

theorem sum_tableThreeNeg (σ : ℝ) :
    (∑ m ∈ Finset.range 4, ∑ m' ∈ Finset.range 4, tableThreeNeg σ m m') =
      σ * lambdaTwoThree ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, tableThreeNeg, fourCoeff]
  norm_num; ring

section PerronValues

variable {j : ℕ} (hj : 2 ≤ j) (σ : ℝ)

include hj in
theorem weilTest_fourBump_zero :
    EF.weilTest (fourBump j σ) (fourBump j σ) 0 =
      (((lambdaTwoThree ^ 2 + (σ * atomTwo) ^ 2 + (σ * lambdaTwoThree) ^ 2 + atomTwo ^ 2) *
        ∫ t, (narrowBump j t) ^ 2 : ℝ) : ℂ) := by
  rw [weilTest_fourBump_select hj σ 0 (fourShift_sep 0 (Or.inl rfl)),
    select_sum_eq σ 0 (tableZero σ) (by path_table)]
  rw [sum_tableZero σ]; push_cast; ring

include hj in
theorem weilTest_fourBump_log_two (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (fourBump j σ) (fourBump j σ) (s * Real.log 2) =
      ((2 * σ * atomTwo * lambdaTwoThree * ∫ t, (narrowBump j t) ^ 2 : ℝ) : ℂ) := by
  rcases hs with rfl | rfl
  · rw [one_mul, weilTest_fourBump_select hj σ _ (fourShift_sep _ (Or.inr (Or.inl rfl))),
      select_sum_eq σ _ (tableTwo σ) (by path_table)]
    rw [sum_tableTwo σ]; push_cast; ring
  · rw [neg_one_mul, weilTest_fourBump_select hj σ _ (fourShift_sep _ (Or.inr (Or.inr (Or.inl rfl)))),
      select_sum_eq σ _ (tableTwoNeg σ) (by path_table)]
    rw [sum_tableTwoNeg σ]; push_cast; ring

include hj in
theorem weilTest_fourBump_log_three (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (fourBump j σ) (fourBump j σ) (s * Real.log 3) =
      ((σ * lambdaTwoThree ^ 2 * ∫ t, (narrowBump j t) ^ 2 : ℝ) : ℂ) := by
  rcases hs with rfl | rfl
  · rw [one_mul, weilTest_fourBump_select hj σ _
      (fourShift_sep _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      select_sum_eq σ _ (tableThree σ) (by path_table)]
    rw [sum_tableThree σ]; push_cast; ring
  · rw [neg_one_mul, weilTest_fourBump_select hj σ _
      (fourShift_sep _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))),
      select_sum_eq σ _ (tableThreeNeg σ) (by path_table)]
    rw [sum_tableThreeNeg σ]; push_cast; ring

end PerronValues

/-! ### 5. The exact ceilings -/

/-- The normalized prime sides `(A − W)/‖c‖²` of nonnegative combinations of tests each supported
in an open interval of length `L`. -/
def windowDeviations (L : ℝ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
    (∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) ∧ 0 < massOf c ∧
      x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem abs_le_of_mem_windowDeviations {L x : ℝ} (hL : L < Real.log 4)
    (hx : x ∈ windowDeviations L) : |x| ≤ lambdaTwoThree := by
  obtain ⟨c, hc, hs, hpos, rfl⟩ := hx
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  exact abs_nodeArchEnergy_sub_weilEnergy_le_window hc hL hs

/-- The narrow Perron test lies in the window `(−r, −r + L)` once `log 3 + 1/(2(j+1)) < L`. -/
theorem fourBump_support {j : ℕ} {σ L : ℝ} (hjL : Real.log 3 + 1 / (2 * ((j : ℝ) + 1)) < L) :
    ∀ u, fourBump j σ u ≠ 0 →
      u ∈ Ioo (-(1 / (4 * ((j : ℝ) + 1)))) (-(1 / (4 * ((j : ℝ) + 1))) + L) := by
  intro u hu
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have hb : narrowBumpC j (u - fourShift m) ≠ 0 := fun h => hm (by rw [h, mul_zero])
  have hr : |u - fourShift m| < 1 / (4 * ((j : ℝ) + 1)) := by
    by_contra h
    push Not at h
    apply hb
    have := (narrowBump j).zero_of_le_dist (x := u - fourShift m)
      (by rw [Real.dist_eq, sub_zero]; exact h)
    simp only [narrowBumpC, this, Complex.ofReal_zero]
  obtain ⟨h0, -⟩ := fourShift_mem m
  have h3 : fourShift m ≤ Real.log 3 := by
    have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    unfold fourShift; split_ifs <;> linarith
  have e : 1 / (2 * ((j : ℝ) + 1)) = 2 * (1 / (4 * ((j : ℝ) + 1))) := by field_simp; ring
  rw [abs_lt] at hr
  constructor <;> linarith

/-- **The Perron test realizes `σλ₂₃`.** -/
theorem perron_mem_windowDeviations {L : ℝ} (h3 : Real.log 3 < L) (h4 : L < Real.log 4) {σ : ℝ}
    (hσ : σ ^ 2 = 1) : σ * lambdaTwoThree ∈ windowDeviations L := by
  classical
  -- a bump narrow enough for the window
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / (L - Real.log 3))
  have hj2 : 2 ≤ j + 2 := by omega
  set k := j + 2 with hk
  have hkL : Real.log 3 + 1 / (2 * ((k : ℝ) + 1)) < L := by
    have hpos : 0 < L - Real.log 3 := by linarith
    have : 1 / (2 * ((k : ℝ) + 1)) < L - Real.log 3 := by
      rw [div_lt_iff₀ (by positivity)]
      have : (2 / (L - Real.log 3)) < (k : ℝ) + 1 := by
        rw [hk]; push_cast; linarith
      rw [div_lt_iff₀ hpos] at this
      nlinarith
    linarith
  have hsupp := fourBump_support (σ := σ) hkL
  have hI := integral_narrowBump_sq_pos k
  have hlam := lambdaTwoThree_pos
  have hw2 := atomTwo_pos
  set f := fourBumpFn k σ with hf
  have hmass : massOf (Finsupp.single f 1) =
      (lambdaTwoThree ^ 2 + (σ * atomTwo) ^ 2 + (σ * lambdaTwoThree) ^ 2 + atomTwo ^ 2) *
        ∫ t, (narrowBump k t) ^ 2 := by
    have h0 := weilTest_fourBump_zero hj2 σ
    rw [RHTower.weilTest_zero_eq_integral_norm_sq] at h0
    rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
    exact_mod_cast h0
  have hpos : 0 < massOf (Finsupp.single f 1) := by rw [hmass]; positivity
  refine ⟨Finsupp.single f 1, fun g => ?_, fun g hg => ?_, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hg
    split_ifs at hg with hfg
    · rw [← hfg]; exact ⟨_, hsupp⟩
    · exact absurd rfl hg
  · rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_single_test,
      primeSide_eq_of_window h4 hsupp, hmass]
    have e2 := weilTest_fourBump_log_two hj2 σ 1 (Or.inl rfl)
    have e2' := weilTest_fourBump_log_two hj2 σ (-1) (Or.inr rfl)
    have e3 := weilTest_fourBump_log_three hj2 σ 1 (Or.inl rfl)
    have e3' := weilTest_fourBump_log_three hj2 σ (-1) (Or.inr rfl)
    rw [one_mul] at e2 e3
    rw [neg_one_mul] at e2' e3'
    change σ * lambdaTwoThree = (atomTwo * ((EF.weilTest (fourBump k σ) (fourBump k σ)
      (Real.log 2)).re + (EF.weilTest (fourBump k σ) (fourBump k σ) (-Real.log 2)).re) +
      atomThree * ((EF.weilTest (fourBump k σ) (fourBump k σ) (Real.log 3)).re +
        (EF.weilTest (fourBump k σ) (fourBump k σ) (-Real.log 3)).re)) / _
    rw [e2, e2', e3, e3']
    simp only [Complex.ofReal_re]
    have hsq := lambdaTwoThree_sq
    rw [eq_div_iff (by positivity)]
    linear_combination (σ * (∫ t, (narrowBump k t) ^ 2) * lambdaTwoThree *
      (atomTwo ^ 2 + lambdaTwoThree ^ 2)) * hσ +
      (2 * σ * (∫ t, (narrowBump k t) ^ 2) * lambdaTwoThree) * hsq

/-- **The second-window ceiling is `λ₂₃`.** -/
theorem isGreatest_windowDeviations {L : ℝ} (h3 : Real.log 3 < L) (h4 : L < Real.log 4) :
    IsGreatest (windowDeviations L) lambdaTwoThree := by
  refine ⟨by simpa using perron_mem_windowDeviations h3 h4 (σ := 1) (by norm_num), fun x hx => ?_⟩
  exact (le_abs_self x).trans (abs_le_of_mem_windowDeviations h4 hx)

/-- **The second-window floor is `−λ₂₃`.** -/
theorem isLeast_windowDeviations {L : ℝ} (h3 : Real.log 3 < L) (h4 : L < Real.log 4) :
    IsLeast (windowDeviations L) (-lambdaTwoThree) := by
  refine ⟨by simpa using perron_mem_windowDeviations h3 h4 (σ := -1) (by norm_num), fun x hx => ?_⟩
  have := abs_le_of_mem_windowDeviations h4 hx
  linarith [neg_abs_le x]

end

end GaloisForLFunctions.BiScaleUncertainty
