import GaloisForLFunctions.RHTower.PolynomialWeilTests
import GaloisForLFunctions.RHTower.LowHeightHodgeExclusion
import GaloisForLFunctions.HTGeometry.LagrangeRectangleContour
import Zeta23.WeilEF.VerticalLine
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Interpolation tests for the sub-Nyquist Hodge exclusion

Fix a finite set `K` of points to be killed and a finite set `S` of interpolation nodes, closed
under conjugation and off the real axis.  Let `Ŵ` be the transform of the unit weight
`(1 - u²)₊^{5/2}`, `P = Π_{r ∈ K} (x - r)(x - r̄)`, `ω = Π_{s ∈ S} (x - s)`, and let `p` be the
Lagrange interpolant of `±i / (P Ŵ^N)` at the nodes (`+` below the real axis).  Then
`Φ = Ŵ^N · P · p` satisfies:

* `Φ = ±i` at the nodes and `Φ = 0` at the killed points (`interpProfile_node`,
  `interpProfile_killed`);
* `P·p` has real coefficients (`interpQ_real`) and degree `< 2|K| + |S|`
  (`natDegree_interpQ_lt`);
* **contour bound** (`norm_interpProfile_le`): let the nodes lie in `|Re s| < X`,
  `y₀ < |Im s| < 1` and every killed point in `|Re r| > X`, `|Im r| < y₀` or `|Im r| > 1`.  If
  `|P ω| ≥ λ` on the sides of the rectangles `[-X, X] × ±[y₀, 1]` and `|P(x) ω(x)| ≤ M`, then
  for `|Re x| ≥ X + 1`, `|Φ(x)| ≤ 2 (M/λ) (|Ŵ(x)|/(cos 1 · w₁))^N`, `w₁ = (3/4)^{5/2}`.

The bound does not see how the nodes cluster: the part of the barycentric formula carried by the
nodes inside a rectangle is the contour integral of the holomorphic function `±i/(P Ŵ^N)`
against `1/((x - t) ω(t))` over its border
(`HTGeometry.sum_nodalWeight_inside_eq_rectangleIntegral`), so only `|P ω|` on the border enters.
The lower bound `|Re Ŵ(t)| ≥ cos 1 · w₁` for `|Re t| ≤ 1` holds at every height
(`re_unitHat_ge`).
-/

open Complex MeasureTheory Real Set Filter Topology Polynomial Lagrange
open scoped ComplexConjugate Interval

noncomputable section
namespace RHTower

open Zeta23 HTGeometry

/-- The transform of the unit weight `(1 - u²)₊^{5/2}`. -/
def unitHat (z : ℂ) : ℂ := paperFT (fun u => (sinhTestWeight 1 u : ℂ)) z

theorem differentiable_unitHat : Differentiable ℂ unitHat := by
  have hc : Continuous (fun u => (sinhTestWeight 1 u : ℂ)) :=
    Complex.continuous_ofReal.comp (sinhTestWeight_contDiff 1).continuous
  have hcs : HasCompactSupport (fun u => (sinhTestWeight 1 u : ℂ)) :=
    hasCompactSupport_ofReal_of_abs (sinhTestWeight_supp zero_le_one)
  exact Zeta23.WeilEF.differentiable_paperFT hc hcs

theorem conj_unitHat_conj (z : ℂ) : conj (unitHat (conj z)) = unitHat z :=
  conj_paperFT_conj_of_even (sinhTestWeight_even 1) z

/-- `Re Ŵ(t) ≥ cos θ · (3/4)^{5/2}` for `|Re t| ≤ θ ≤ π/2`. -/
theorem re_unitHat_ge {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 2) {t : ℂ} (ht : |t.re| ≤ θ) :
    Real.cos θ * unitWeightFloor ≤ (unitHat t).re := by
  set w := sinhTestWeight 1
  have hwc : Continuous w := (sinhTestWeight_contDiff 1).continuous
  have hws : HasCompactSupport w := hasCompactSupport_of_support_subset_abs
    (sinhTestWeight_supp zero_le_one)
  have hint : Integrable (fun u : ℝ => (w u : ℂ) * cexp (I * t * u)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hasCompactSupport_ofReal_of_abs (sinhTestWeight_supp zero_le_one)).mul_right
  have hre : (unitHat t).re = ∫ u, w u * (Real.exp (-(t.im * u)) * Real.cos (t.re * u)) := by
    unfold unitHat
    rw [paperFT_def]
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [Complex.re_ofReal_mul, Complex.exp_re]
    congr 2
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
  -- the cosine factor is at least `cos θ` on the support
  have hcos : ∀ u, w u * (Real.exp (-(t.im * u)) * Real.cos θ) ≤
      w u * (Real.exp (-(t.im * u)) * Real.cos (t.re * u)) := by
    intro u
    by_cases hu : |u| ≤ 1
    · have hw0 := sinhTestWeight_nonneg 1 u
      have hc : Real.cos θ ≤ Real.cos (t.re * u) := by
        rw [← Real.cos_abs (t.re * u)]
        apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
        rw [abs_mul]
        calc |t.re| * |u| ≤ θ * 1 := mul_le_mul ht hu (abs_nonneg _) hθ0
          _ = θ := mul_one θ
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) hw0
    · have : w u = 0 := sinhTestWeight_eq_zero zero_le_one (lt_of_not_ge hu)
      simp [this]
  have hi1 : Integrable (fun u => w u * (Real.exp (-(t.im * u)) * Real.cos θ)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hws.mul_right
  have hi2 : Integrable (fun u => w u * (Real.exp (-(t.im * u)) * Real.cos (t.re * u))) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hws.mul_right
  have hmono := integral_mono hi1 hi2 hcos
  -- `∫ w e^{-yu} = Re Ŵ(iy) = ∫ w cosh(yu) ≥ (3/4)^{5/2}`
  have hint' : Integrable (fun u : ℝ => (w u : ℂ) * cexp (I * (I * t.im) * u)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hasCompactSupport_ofReal_of_abs (sinhTestWeight_supp zero_le_one)).mul_right
  have hre2 : (unitHat (I * t.im)).re = ∫ u, w u * Real.exp (-(t.im * u)) := by
    unfold unitHat
    rw [paperFT_def]
    have h := integral_re hint'
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [Complex.re_ofReal_mul, Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im]
  have hval : unitHat (I * t.im) = ((∫ u, sinhTestWeight 1 u * Real.cosh (-t.im * u) : ℝ) : ℂ) := by
    have h := paperFT_unitWeight_neg_I_mul (-t.im)
    rw [show -(I * ((-t.im : ℝ) : ℂ)) = I * t.im by push_cast; ring] at h
    exact h
  have hfloor : unitWeightFloor ≤ ∫ u, w u * Real.exp (-(t.im * u)) := by
    rw [← hre2, hval, Complex.ofReal_re]
    exact unitWeightFloor_le (-t.im)
  have hθc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) hθ
  have hpull : ∫ u, w u * (Real.exp (-(t.im * u)) * Real.cos θ) =
      Real.cos θ * ∫ u, w u * Real.exp (-(t.im * u)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    ring
  rw [hre]
  calc Real.cos θ * unitWeightFloor ≤ Real.cos θ * ∫ u, w u * Real.exp (-(t.im * u)) :=
        mul_le_mul_of_nonneg_left hfloor hθc
    _ = ∫ u, w u * (Real.exp (-(t.im * u)) * Real.cos θ) := hpull.symm
    _ ≤ _ := hmono

/-- `cos 1 · (3/4)^{5/2}`, the floor of `|Ŵ|` on `|Re t| ≤ 1`. -/
def unitHatFloor : ℝ := Real.cos 1 * unitWeightFloor

theorem unitHatFloor_pos : 0 < unitHatFloor := by
  unfold unitHatFloor
  refine mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three],
    by linarith [Real.pi_gt_three]⟩) unitWeightFloor_pos

theorem unitHatFloor_le_norm {t : ℂ} (ht : |t.re| ≤ 1) : unitHatFloor ≤ ‖unitHat t‖ :=
  (re_unitHat_ge zero_le_one (by linarith [Real.pi_gt_three]) ht).trans
    ((le_abs_self _).trans (Complex.abs_re_le_norm _))

theorem unitHat_ne_zero {t : ℂ} (ht : |t.re| ≤ 11 / 10) : unitHat t ≠ 0 := by
  have h := re_unitHat_ge (θ := 11 / 10) (by norm_num) (by linarith [Real.pi_gt_three]) ht
  have hc : 0 < Real.cos (11 / 10) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  intro h0
  rw [h0, Complex.zero_re] at h
  nlinarith [unitWeightFloor_pos]

/-! ### The killed-root polynomial and the interpolant -/

/-- `Π_{r ∈ K} (X - r)(X - r̄)`. -/
def killPoly (K : Finset ℂ) : ℂ[X] := ∏ r ∈ K, (X - C r) * (X - C (conj r))

theorem eval_killPoly (K : Finset ℂ) (x : ℂ) :
    (killPoly K).eval x = ∏ r ∈ K, (x - r) * (x - conj r) := by
  simp [killPoly, eval_prod]

theorem killPoly_ne_zero (K : Finset ℂ) : killPoly K ≠ 0 := by
  unfold killPoly
  rw [Finset.prod_ne_zero_iff]
  exact fun r _ => mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero _)

theorem natDegree_killPoly (K : Finset ℂ) : (killPoly K).natDegree = 2 * K.card := by
  unfold killPoly
  rw [natDegree_prod _ _ fun r _ => mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero _)]
  simp only [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C]
  simp [Finset.sum_const]
  ring

theorem map_conj_killPoly (K : Finset ℂ) : (killPoly K).map (starRingEnd ℂ) = killPoly K := by
  unfold killPoly
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, Complex.conj_conj]
  refine Finset.prod_congr rfl fun r _ => ?_
  ring

theorem coeff_real_of_map_conj {Q : ℂ[X]} (h : Q.map (starRingEnd ℂ) = Q) :
    ∀ n, conj (Q.coeff n) = Q.coeff n := by
  intro n
  have := congrArg (fun q : ℂ[X] => q.coeff n) h
  simpa [coeff_map] using this

/-- `p̄(s) = conj (p (s̄))`. -/
theorem eval_map_starRingEnd (p : ℂ[X]) (s : ℂ) :
    (p.map (starRingEnd ℂ)).eval s = conj (p.eval (conj s)) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, map_sum, natDegree_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_map, map_mul, map_pow, Complex.conj_conj]

/-- The interpolation data `±i / (P(t) Ŵ(t)^N)`, `+` below the real axis. -/
def interpData (K : Finset ℂ) (N : ℕ) (t : ℂ) : ℂ :=
  (if t.im < 0 then I else -I) / ((killPoly K).eval t * unitHat t ^ N)

/-- The Lagrange interpolant of the data at the nodes `S`. -/
def interpPoly (K S : Finset ℂ) (N : ℕ) : ℂ[X] := interpolate S id (interpData K N)

/-- `Q = P · p`. -/
def interpQ (K S : Finset ℂ) (N : ℕ) : ℂ[X] := killPoly K * interpPoly K S N

/-- The profile `Φ = Ŵ^N · Q`. -/
def interpProfile (K S : Finset ℂ) (N : ℕ) (x : ℂ) : ℂ :=
  unitHat x ^ N * (interpQ K S N).eval x

theorem interpProfile_killed (K S : Finset ℂ) (N : ℕ) {r : ℂ} (hr : r ∈ K) :
    interpProfile K S N r = 0 ∧ interpProfile K S N (conj r) = 0 := by
  unfold interpProfile interpQ
  rw [eval_mul, eval_mul, eval_killPoly, eval_killPoly]
  constructor
  · rw [Finset.prod_eq_zero hr (by ring)]; ring
  · rw [Finset.prod_eq_zero hr (by rw [sub_self, mul_zero])]; ring

/-- At a node, `Φ = ±i`. -/
theorem interpProfile_node {K S : Finset ℂ} {N : ℕ} {s : ℂ} (hs : s ∈ S)
    (hP : (killPoly K).eval s ≠ 0) (hW : unitHat s ≠ 0) :
    interpProfile K S N s = if s.im < 0 then I else -I := by
  unfold interpProfile interpQ interpPoly
  have h := eval_interpolate_at_node (interpData K N) (Set.injOn_id _) hs
  simp only [id] at h
  rw [eval_mul, h]
  simp only [interpData]
  field_simp

theorem natDegree_interpQ_lt (K S : Finset ℂ) (N : ℕ) (hS : S.Nonempty) :
    (interpQ K S N).natDegree < 2 * K.card + S.card := by
  unfold interpQ
  have hdeg := degree_interpolate_lt (s := S) (v := id) (interpData K N) (Set.injOn_id _)
  by_cases hp : interpPoly K S N = 0
  · rw [hp, mul_zero, natDegree_zero]
    have := hS.card_pos
    omega
  · rw [natDegree_mul (killPoly_ne_zero K) hp, natDegree_killPoly]
    have : (interpPoly K S N).natDegree < S.card := by
      have h := (natDegree_lt_iff_degree_lt hp).mpr hdeg
      exact h
    omega

/-- **Real coefficients.**  With nodes closed under conjugation and off the real axis, the
interpolant, hence `Q`, has real coefficients. -/
theorem interpQ_real {K S : Finset ℂ} {N : ℕ} (hSc : ∀ s ∈ S, conj s ∈ S)
    (hSim : ∀ s ∈ S, s.im ≠ 0) :
    ∀ n, conj ((interpQ K S N).coeff n) = (interpQ K S N).coeff n := by
  set p := interpPoly K S N
  have hdata : ∀ s ∈ S, conj (interpData K N (conj s)) = interpData K N s := by
    intro s hs
    unfold interpData
    rw [map_div₀, map_mul, map_pow, conj_unitHat_conj, Complex.conj_im]
    have hPc : conj ((killPoly K).eval (conj s)) = (killPoly K).eval s := by
      rw [eval_killPoly, eval_killPoly, map_prod]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [map_mul, map_sub, map_sub, Complex.conj_conj, Complex.conj_conj]
      ring
    rw [hPc]
    congr 1
    rcases lt_or_gt_of_ne (hSim s hs) with h | h
    · rw [if_neg (by linarith), if_pos h, map_neg, Complex.conj_I, neg_neg]
    · rw [if_pos (by linarith), if_neg (by linarith), Complex.conj_I]
  have hmap : p.map (starRingEnd ℂ) = p := by
    have hdeg : (p.map (starRingEnd ℂ)).degree < S.card := by
      rw [degree_map]
      exact degree_interpolate_lt _ (Set.injOn_id _)
    have heval : ∀ s ∈ S, (p.map (starRingEnd ℂ)).eval (id s) = interpData K N s := by
      intro s hs
      rw [id, eval_map_starRingEnd]
      have := eval_interpolate_at_node (interpData K N) (Set.injOn_id _)
        (hSc s hs)
      simp only [id] at this
      simp only [p, interpPoly]
      rw [this, hdata s hs]
    exact eq_interpolate_of_eval_eq _ (Set.injOn_id _) hdeg heval
  refine coeff_real_of_map_conj ?_
  unfold interpQ
  rw [Polynomial.map_mul, map_conj_killPoly, hmap]


/-! ### The contour bound -/

theorem norm_eval_nodal (S : Finset ℂ) (y : ℂ) :
    ‖eval y (nodal S id)‖ = ∏ s ∈ S, ‖y - s‖ := by
  rw [eval_nodal, norm_prod]
  rfl

theorem norm_eval_killPoly (K : Finset ℂ) (y : ℂ) :
    ‖(killPoly K).eval y‖ = ∏ r ∈ K, (‖y - r‖ * ‖y - conj r‖) := by
  rw [eval_killPoly, norm_prod]
  exact Finset.prod_congr rfl fun r _ => norm_mul _ _

theorem killPoly_eval_ne_zero {K : Finset ℂ} {t : ℂ} (h : ∀ r ∈ K, t ≠ r ∧ t ≠ conj r) :
    (killPoly K).eval t ≠ 0 := by
  rw [eval_killPoly]
  exact Finset.prod_ne_zero_iff.mpr fun r hr =>
    mul_ne_zero (sub_ne_zero.mpr (h r hr).1) (sub_ne_zero.mpr (h r hr).2)

open scoped Classical in
/-- **One rectangle.**  Let the killed points and their conjugates lie outside a rectangle `R`
in `|Re t| ≤ 1`, and the nodes off `∂R`.  If `|P ω| ≥ λ`, `|Ŵ| ≥ c` and `|x - t| ≥ 1` on `∂R`,
and `|P(x) ω(x)| ≤ M`, then the part of `Ŵ(x)^N P(x) p(x)` carried by the nodes inside `R`, on
which the data are `σ/(P Ŵ^N)` with `|σ| = 1`, is at most `(M/λ)(|Ŵ(x)|/c)^N`.  It is the
contour integral of `σ/(P Ŵ^N)` against `1/((x - t) ω(t))` over `∂R`. -/
theorem norm_rect_part_le {K S : Finset ℂ} {N : ℕ} {z w x σ : ℂ} {lam M c : ℝ} (hσ : ‖σ‖ = 1)
    (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im)
    (hper : 2 * (|w.re - z.re| + |w.im - z.im|) ≤ 2 * Real.pi)
    (hRe : ∀ t ∈ Rectangle z w, |t.re| ≤ 1)
    (hK : ∀ r ∈ K, r ∉ Rectangle z w ∧ conj r ∉ Rectangle z w)
    (hnode : ∀ s ∈ S, Rectangle z w ∈ 𝓝 s ∨ s ∉ Rectangle z w) (hSne : S.Nonempty)
    (hx : x ∉ Rectangle z w) (hc : 0 < c) (hlam : 0 < lam)
    (hborder : ∀ t ∈ RectangleBorder z w,
      lam ≤ ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖ ∧ c ≤ ‖unitHat t‖ ∧ 1 ≤ ‖x - t‖)
    (hM : ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ ≤ M) :
    ‖unitHat x ^ N * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rectangle z w),
          nodalWeight S id s * (x - s)⁻¹ * (σ / ((killPoly K).eval s * unitHat s ^ N))‖
      ≤ M / lam * (‖unitHat x‖ / c) ^ N := by
  set U : Set ℂ := {t : ℂ | |t.re| < 11 / 10} ∩ {t : ℂ | (killPoly K).eval t ≠ 0} with hU
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_ne_fun (Polynomial.continuous _) continuous_const)
  have hRU : Rectangle z w ⊆ U := by
    intro t ht
    refine ⟨show |t.re| < 11 / 10 by linarith [hRe t ht],
      killPoly_eval_ne_zero fun r hr => ⟨?_, ?_⟩⟩
    · intro h; rw [h] at ht; exact (hK r hr).1 ht
    · intro h; rw [h] at ht; exact (hK r hr).2 ht
  have hPU : ∀ t ∈ U, (killPoly K).eval t ≠ 0 := fun t ht => ht.2
  have hWU : ∀ t ∈ U, unitHat t ≠ 0 := fun t ht => unitHat_ne_zero (le_of_lt (by
    have h1 : |t.re| < 11 / 10 := ht.1
    exact h1))
  set G : ℂ → ℂ := fun t => σ / ((killPoly K).eval t * unitHat t ^ N) with hG
  have hGd : DifferentiableOn ℂ G U := by
    refine (differentiableOn_const σ).div ?_ fun t ht => mul_ne_zero (hPU t ht)
      (pow_ne_zero _ (hWU t ht))
    exact ((Polynomial.differentiable _).mul (differentiable_unitHat.pow N)).differentiableOn
  have hcont := sum_nodalWeight_inside_eq_rectangleIntegral (s := S) (v := id)
    (Set.injOn_id _) hSne hUo hRU hGd hzw hzw' (fun s hs => hnode s hs) hx
  simp only [id] at hcont
  have hsum : ∑ s ∈ S.filter (fun s => s ∈ Rectangle z w),
      nodalWeight S id s * (x - s)⁻¹ * (σ / ((killPoly K).eval s * unitHat s ^ N)) =
      RectangleIntegral' (fun t => G t / ((x - t) * eval t (nodal S id))) z w := by
    rw [← hcont]
  rw [hsum]
  set A := unitHat x ^ N * (killPoly K).eval x * eval x (nodal S id) with hA
  set Rb := M / lam * (‖unitHat x‖ / c) ^ N with hRb
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have hRb0 : 0 ≤ Rb := by rw [hRb]; positivity
  have hpt : ∀ t ∈ RectangleBorder z w, ‖A * (G t / ((x - t) * eval t (nodal S id)))‖ ≤ Rb := by
    intro t ht
    obtain ⟨hlt, hWt, hxt1⟩ := hborder t ht
    have hPω : 0 < ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖ := lt_of_lt_of_le hlam hlt
    have hPt : 0 < ‖(killPoly K).eval t‖ := by
      rcases (norm_nonneg ((killPoly K).eval t)).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hPω; exact absurd hPω (lt_irrefl _)
    have hωt : 0 < ‖eval t (nodal S id)‖ := by
      rcases (norm_nonneg (eval t (nodal S id))).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hPω; exact absurd hPω (lt_irrefl _)
    have hWt0 : 0 < ‖unitHat t‖ := lt_of_lt_of_le hc hWt
    have hWr : ‖unitHat x‖ ^ N ≤ (‖unitHat x‖ / c) ^ N * ‖unitHat t‖ ^ N := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ N
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left hWt (norm_nonneg _)
    have hnorm : ‖A * (G t / ((x - t) * eval t (nodal S id)))‖ =
        ‖unitHat x‖ ^ N * ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ /
          (‖(killPoly K).eval t‖ * ‖unitHat t‖ ^ N * ‖x - t‖ * ‖eval t (nodal S id)‖) := by
      simp only [hA, hG, norm_mul, norm_div, norm_pow, hσ]
      field_simp
    rw [hnorm, div_le_iff₀ (by positivity)]
    have hML : 0 ≤ M / lam := div_nonneg hM0 hlam.le
    calc ‖unitHat x‖ ^ N * ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖
        ≤ ‖unitHat x‖ ^ N * M := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hM (by positivity)
      _ = M / lam * ‖unitHat x‖ ^ N * lam * 1 := by field_simp
      _ ≤ M / lam * ((‖unitHat x‖ / c) ^ N * ‖unitHat t‖ ^ N) *
            (‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖) * ‖x - t‖ := by
          gcongr
      _ = Rb * (‖(killPoly K).eval t‖ * ‖unitHat t‖ ^ N * ‖x - t‖ * ‖eval t (nodal S id)‖) := by
          rw [hRb]; ring
  have hRI : RectangleIntegral' (fun t => A * (G t / ((x - t) * eval t (nodal S id)))) z w =
      A * RectangleIntegral' (fun t => G t / ((x - t) * eval t (nodal S id))) z w := by
    rw [RectangleIntegral', RectangleIntegral', rectangleIntegral_const_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [← hRI, RectangleIntegral', norm_smul]
  have hbd := norm_rectangleIntegral_le hpt
  have h2pi : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2pi]
  calc 1 / (2 * Real.pi) * ‖RectangleIntegral (fun t => A * (G t / ((x - t) *
        eval t (nodal S id)))) z w‖
      ≤ 1 / (2 * Real.pi) * (2 * (|w.re - z.re| + |w.im - z.im|) * Rb) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ ≤ 1 / (2 * Real.pi) * (2 * Real.pi * Rb) := by gcongr
    _ = Rb := by field_simp

open scoped Classical in
/-- **One horizontal band.**  The rectangle `[-X, X] × [a, b]`, lying in `y₀ ≤ |Im t| ≤ 1` with
its horizontal sides on `|Im t| ∈ {y₀, 1}`, carries at most `(M/λ)(|Ŵ(x)|/(cos 1 · w₁))^N` of
`Φ(x)` for `|Re x| ≥ X + 1`, whenever `|P ω| ≥ λ` on the sides `|Re t| = X`, `y₀ ≤ |Im t| ≤ 1`
and `|Im t| ∈ {y₀, 1}`, `|Re t| ≤ X`. -/
theorem norm_band_part_le {K S : Finset ℂ} {N : ℕ} {x σ : ℂ} {X a b y₀ lam M : ℝ}
    (hσ : ‖σ‖ = 1) (hX0 : 0 < X) (hX : X ≤ 3 / 4) (hab : a ≤ b) (hba : b - a ≤ 1)
    (hband : ∀ y : ℝ, a ≤ y → y ≤ b → y₀ ≤ |y| ∧ |y| ≤ 1)
    (ha : |a| = y₀ ∨ |a| = 1) (hb : |b| = y₀ ∨ |b| = 1) (hSne : S.Nonempty)
    (hS : ∀ s ∈ S, |s.re| < X ∧ ((a < s.im ∧ s.im < b) ∨ s.im < a ∨ b < s.im))
    (hK : ∀ r ∈ K, X < |r.re| ∨ r.im < a ∨ b < r.im)
    (hKc : ∀ r ∈ K, X < |(conj r).re| ∨ (conj r).im < a ∨ b < (conj r).im)
    (hx : X + 1 ≤ |x.re|) (hlam : 0 < lam)
    (hborder : ∀ t : ℂ, (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1)) →
      lam ≤ ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖)
    (hM : ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ ≤ M) :
    ‖unitHat x ^ N * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rectangle ⟨-X, a⟩ ⟨X, b⟩),
          nodalWeight S id s * (x - s)⁻¹ * (σ / ((killPoly K).eval s * unitHat s ^ N))‖
      ≤ M / lam * (‖unitHat x‖ / unitHatFloor) ^ N := by
  set z : ℂ := ⟨-X, a⟩ with hz
  set w : ℂ := ⟨X, b⟩ with hw
  have hmemR : ∀ t : ℂ, t ∈ Rectangle z w ↔ (-X ≤ t.re ∧ t.re ≤ X) ∧ (a ≤ t.im ∧ t.im ≤ b) := by
    intro t
    rw [Rectangle, Complex.mem_reProdIm, hz, hw]
    simp only [Set.uIcc_of_le (show -X ≤ X by linarith), Set.uIcc_of_le hab, Set.mem_Icc]
  have hout : ∀ q : ℂ, (X < |q.re| ∨ q.im < a ∨ b < q.im) → q ∉ Rectangle z w := by
    intro q hq hqR
    rw [hmemR] at hqR
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hqR
    have := abs_le.mpr ⟨h1, h2⟩
    rcases hq with hq | hq | hq <;> linarith
  have hRe : ∀ t ∈ Rectangle z w, |t.re| ≤ 1 := by
    intro t ht
    rw [hmemR] at ht
    exact (abs_le.mpr ⟨ht.1.1, ht.1.2⟩).trans (by linarith)
  have hnode : ∀ s ∈ S, Rectangle z w ∈ 𝓝 s ∨ s ∉ Rectangle z w := by
    intro s hs
    obtain ⟨hre, hband' | hlow | hhigh⟩ := hS s hs
    · left
      rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hz, hw]
      simp only [Set.uIoo_of_le (show -X ≤ X by linarith), Set.uIoo_of_le hab, Set.mem_Ioo]
      have := abs_lt.mp hre
      exact ⟨⟨this.1, this.2⟩, hband'.1, hband'.2⟩
    · right; exact hout s (Or.inr (Or.inl hlow))
    · right; exact hout s (Or.inr (Or.inr hhigh))
  have hxR : x ∉ Rectangle z w := hout x (Or.inl (by linarith))
  have hper : 2 * (|w.re - z.re| + |w.im - z.im|) ≤ 2 * Real.pi := by
    have h1 : w.re - z.re = 2 * X := by rw [hz, hw]; ring
    have h2 : w.im - z.im = b - a := rfl
    rw [h1, h2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith [Real.pi_gt_three]
  refine norm_rect_part_le hσ (show z.re ≤ w.re by show -X ≤ X; linarith) hab hper hRe
    (fun r hr => ⟨hout r (hK r hr), hout _ (hKc r hr)⟩) hnode hSne hxR unitHatFloor_pos hlam
    (fun t ht => ?_) hM
  have htR := (hmemR t).mp (rectangleBorder_subset_rectangle z w ht)
  obtain ⟨⟨htr1, htr2⟩, hti1, hti2⟩ := htR
  have htabs : |t.re| ≤ X := abs_le.mpr ⟨htr1, htr2⟩
  refine ⟨hborder t ?_, unitHatFloor_le_norm (by linarith), ?_⟩
  · rcases ht with ((h | h) | h) | h
    · right
      refine ⟨htabs, ?_⟩
      have : t.im = a := (Complex.mem_reProdIm.mp h).2
      rw [this]; exact ha
    · left
      have : t.re = -X := (Complex.mem_reProdIm.mp h).1
      rw [this, abs_neg, abs_of_pos hX0]
      exact ⟨rfl, hband t.im hti1 hti2⟩
    · right
      refine ⟨htabs, ?_⟩
      have : t.im = b := (Complex.mem_reProdIm.mp h).2
      rw [this]; exact hb
    · left
      have : t.re = X := (Complex.mem_reProdIm.mp h).1
      rw [this, abs_of_pos hX0]
      exact ⟨rfl, hband t.im hti1 hti2⟩
  · have hn := Complex.abs_re_le_norm (x - t)
    rw [Complex.sub_re] at hn
    have := abs_sub_abs_le_abs_sub x.re t.re
    linarith

/-- **The tail bound.**  Let the nodes lie in `|Re s| < X`, `y₀ < |Im s| < 1`, and every killed
point satisfy `|Re r| > X`, `|Im r| < y₀` or `|Im r| > 1`.  If `|P ω| ≥ λ` on the borders of the
rectangles `[-X, X] × ±[y₀, 1]` and `|P(x) ω(x)| ≤ M`, then for `|Re x| ≥ X + 1`,
`|Φ(x)| ≤ 2 (M/λ)(|Ŵ(x)|/(cos 1 · w₁))^N`. -/
theorem norm_interpProfile_le {K S : Finset ℂ} {N : ℕ} {X y₀ lam M : ℝ} {x : ℂ}
    (hX0 : 0 < X) (hX : X ≤ 3 / 4) (hy0 : 0 < y₀) (hy : y₀ ≤ 1 / 2)
    (hS : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| < 1)
    (hK : ∀ r ∈ K, X < |r.re| ∨ |r.im| < y₀ ∨ 1 < |r.im|)
    (hx : X + 1 ≤ |x.re|) (hlam : 0 < lam)
    (hborder : ∀ t : ℂ, (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1)) →
      lam ≤ ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖)
    (hM : ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ ≤ M) :
    ‖interpProfile K S N x‖ ≤ 2 * (M / lam * (‖unitHat x‖ / unitHatFloor) ^ N) := by
  classical
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    rw [interpProfile, interpQ, interpPoly, interpolate_empty, mul_zero, eval_zero, mul_zero,
      norm_zero]
    have hc0 := unitHatFloor_pos
    positivity
  have hxS : ∀ s ∈ S, x ≠ id s := by
    intro s hs h
    have := (hS s hs).1
    rw [h] at hx
    simp only [id] at hx
    linarith
  set Rp : Set ℂ := Rectangle ⟨-X, y₀⟩ ⟨X, 1⟩ with hRp
  set Rm : Set ℂ := Rectangle ⟨-X, -1⟩ ⟨X, -y₀⟩ with hRm
  have hmemRp : ∀ s ∈ S, s ∈ Rp ↔ 0 < s.im := by
    intro s hs
    obtain ⟨hre, him, him'⟩ := hS s hs
    rw [hRp, Rectangle, Complex.mem_reProdIm]
    simp only [Set.uIcc_of_le (show -X ≤ X by linarith),
      Set.uIcc_of_le (show y₀ ≤ 1 by linarith), Set.mem_Icc]
    have hre' := abs_le.mp hre.le
    have hi := abs_lt.mp him'
    constructor
    · rintro ⟨-, h, -⟩; linarith
    · intro h
      rw [abs_of_pos h] at him
      exact ⟨hre', by linarith, by linarith⟩
  have hmemRm : ∀ s ∈ S, s ∈ Rm ↔ s.im < 0 := by
    intro s hs
    obtain ⟨hre, him, him'⟩ := hS s hs
    rw [hRm, Rectangle, Complex.mem_reProdIm]
    simp only [Set.uIcc_of_le (show -X ≤ X by linarith),
      Set.uIcc_of_le (show (-1 : ℝ) ≤ -y₀ by linarith), Set.mem_Icc]
    have hre' := abs_le.mp hre.le
    have hi := abs_lt.mp him'
    constructor
    · rintro ⟨-, -, h⟩; linarith
    · intro h
      rw [abs_of_neg h] at him
      exact ⟨hre', by linarith, by linarith⟩
  have hsplit : eval x (interpPoly K S N) = eval x (nodal S id) *
      ((∑ s ∈ S.filter (fun s => s ∈ Rp),
          nodalWeight S id s * (x - s)⁻¹ * (-I / ((killPoly K).eval s * unitHat s ^ N))) +
        ∑ s ∈ S.filter (fun s => s ∈ Rm),
          nodalWeight S id s * (x - s)⁻¹ * (I / ((killPoly K).eval s * unitHat s ^ N))) := by
    rw [interpPoly, eval_interpolate_not_at_node _ hxS]
    congr 1
    simp only [id]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun s => s ∈ Rp)]
    congr 1
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_filter] at hs
      have h := (hmemRp s hs.1).mp hs.2
      rw [interpData, if_neg (by linarith)]
    · have hf : S.filter (fun s => s ∉ Rp) = S.filter (fun s => s ∈ Rm) := by
        refine Finset.filter_congr fun s hs => ?_
        rw [hmemRp s hs, hmemRm s hs]
        have := (hS s hs).2.1
        constructor
        · intro h
          rcases lt_trichotomy s.im 0 with h' | h' | h'
          · exact h'
          · rw [h', abs_zero] at this; linarith
          · exact absurd h' h
        · intro h h'; linarith
      rw [hf]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_filter] at hs
      have h := (hmemRm s hs.1).mp hs.2
      rw [interpData, if_pos h]
  have hΦ : interpProfile K S N x =
      unitHat x ^ N * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rp),
          nodalWeight S id s * (x - s)⁻¹ * (-I / ((killPoly K).eval s * unitHat s ^ N)) +
      unitHat x ^ N * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rm),
          nodalWeight S id s * (x - s)⁻¹ * (I / ((killPoly K).eval s * unitHat s ^ N)) := by
    rw [interpProfile, interpQ, eval_mul, hsplit]
    ring
  have hKc : ∀ r ∈ K, X < |(conj r).re| ∨ |(conj r).im| < y₀ ∨ 1 < |(conj r).im| := by
    intro r hr
    rw [Complex.conj_im, Complex.conj_re, abs_neg]
    exact hK r hr
  have hp := norm_band_part_le (K := K) (S := S) (N := N) (x := x) (σ := -I) (X := X) (a := y₀)
    (b := 1) (y₀ := y₀) (by rw [norm_neg, Complex.norm_I]) hX0 hX (by linarith) (by linarith)
    (fun y h1 h2 => by rw [abs_of_pos (by linarith)]; exact ⟨h1, h2⟩)
    (Or.inl (abs_of_pos hy0)) (Or.inr abs_one) hSne
    (fun s hs => by
      obtain ⟨hre, him, him'⟩ := hS s hs
      refine ⟨hre, ?_⟩
      have hi := abs_lt.mp him'
      rcases lt_or_ge 0 s.im with h | h
      · rw [abs_of_pos h] at him
        exact Or.inl ⟨him, by linarith⟩
      · rw [abs_of_nonpos h] at him
        exact Or.inr (Or.inl (by linarith)))
    (fun r hr => by
      rcases hK r hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by linarith [le_abs_self r.im]))
      · rcases lt_or_ge 0 r.im with h' | h'
        · rw [abs_of_pos h'] at h; exact Or.inr (Or.inr h)
        · rw [abs_of_nonpos h'] at h; exact Or.inr (Or.inl (by linarith)))
    (fun r hr => by
      rcases hKc r hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by linarith [le_abs_self (conj r).im]))
      · rcases lt_or_ge 0 (conj r).im with h' | h'
        · rw [abs_of_pos h'] at h; exact Or.inr (Or.inr h)
        · rw [abs_of_nonpos h'] at h; exact Or.inr (Or.inl (by linarith)))
    hx hlam hborder hM
  have hm := norm_band_part_le (K := K) (S := S) (N := N) (x := x) (σ := I) (X := X) (a := -1)
    (b := -y₀) (y₀ := y₀) Complex.norm_I hX0 hX (by linarith) (by linarith)
    (fun y h1 h2 => by rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩)
    (Or.inr (by rw [abs_neg, abs_one])) (Or.inl (by rw [abs_neg, abs_of_pos hy0])) hSne
    (fun s hs => by
      obtain ⟨hre, him, him'⟩ := hS s hs
      refine ⟨hre, ?_⟩
      have hi := abs_lt.mp him'
      rcases lt_or_ge s.im 0 with h | h
      · rw [abs_of_neg h] at him
        exact Or.inl ⟨by linarith, by linarith⟩
      · rw [abs_of_nonneg h] at him
        exact Or.inr (Or.inr (by linarith)))
    (fun r hr => by
      rcases hK r hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (by linarith [neg_abs_le r.im]))
      · rcases lt_or_ge 0 r.im with h' | h'
        · rw [abs_of_pos h'] at h; exact Or.inr (Or.inr (by linarith))
        · rw [abs_of_nonpos h'] at h; exact Or.inr (Or.inl (by linarith)))
    (fun r hr => by
      rcases hKc r hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (by linarith [neg_abs_le (conj r).im]))
      · rcases lt_or_ge 0 (conj r).im with h' | h'
        · rw [abs_of_pos h'] at h; exact Or.inr (Or.inr (by linarith))
        · rw [abs_of_nonpos h'] at h; exact Or.inr (Or.inl (by linarith)))
    hx hlam hborder hM
  rw [hΦ]
  refine (norm_add_le _ _).trans ?_
  linarith

end RHTower
