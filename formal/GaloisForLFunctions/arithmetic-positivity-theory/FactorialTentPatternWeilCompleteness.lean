import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTranslatedTentApproximation
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion

/-!
# Completeness of the factorial tent family for the Weil criterion

On the grid `a + j d_n`, with `d_n` the half-width of the factorial tent of scale `n`, every tent
carries the same global factor `e^{3x/2}`. The hat `causalTent d (y)/d` is a difference of two
unit ramps, so Abel summation shows that a single-scale grid tent pattern is exactly
`e^{3x/2}` times the piecewise-linear interpolant of its nodal data. Consecutive ramps add up
to one long ramp, hence the interpolant keeps the Lipschitz constant of the data and
approximates it within `2Ld`. The quantitative full-form stability estimate then gives
`Q(f_n) → Q(g)` for every compact source `g` with Lipschitz `e^{-3x/2}g`, in all channels.
Together with mollification of tent patterns, the Riemann hypothesis is equivalent to
nonnegativity of the complete Weil energy on finite translated factorial tent patterns.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology CompactlySupported

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The unit ramp `clamp(u, 0, 1)`. -/
def unitRamp (u : ℝ) : ℝ := max 0 (min u 1)

theorem unitRamp_mono {u v : ℝ} (h : u ≤ v) : unitRamp u ≤ unitRamp v :=
  max_le_max le_rfl (min_le_min_right 1 h)

theorem unitRamp_of_le_zero {u : ℝ} (h : u ≤ 0) : unitRamp u = 0 := by
  unfold unitRamp; rw [max_eq_left]; exact (min_le_left _ _).trans h

theorem unitRamp_of_one_le {u : ℝ} (h : 1 ≤ u) : unitRamp u = 1 := by
  unfold unitRamp; rw [min_eq_right h]; norm_num

/-- Consecutive unit ramps add up to one long ramp: `Σ_{j<M} r(u - j) = clamp(u, 0, M)`. -/
theorem sum_unitRamp (M : ℕ) (u : ℝ) :
    ∑ j ∈ Finset.range M, unitRamp (u - j) = max 0 (min u M) := by
  induction M with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]; rw [max_eq_left (min_le_right _ _)]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    unfold unitRamp
    push_cast
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rcases le_total u 0 with h0 | h0
    · rw [max_eq_left (min_le_left _ _ |>.trans h0), max_eq_left ((min_le_left _ _).trans (by linarith)),
        max_eq_left ((min_le_left _ _).trans h0)]; ring
    rcases le_total u M with h1 | h1
    · rw [min_eq_left h1, max_eq_right h0, max_eq_left ((min_le_left _ _).trans (by linarith)),
        min_eq_left (by linarith : u ≤ (M : ℝ) + 1), max_eq_right h0]; ring
    rcases le_total u (M + 1) with h2 | h2
    · rw [min_eq_right h1, max_eq_right hM, min_eq_left (by linarith : u - M ≤ 1),
        max_eq_right (by linarith : (0 : ℝ) ≤ u - M), min_eq_left h2, max_eq_right h0]; ring
    · rw [min_eq_right h1, max_eq_right hM, min_eq_right (by linarith : 1 ≤ u - M), max_eq_right zero_le_one,
        min_eq_right h2, max_eq_right (by linarith)]

/-- Piecewise-linear interpolant of `G` on the grid `a + jd`, `0 ≤ j ≤ M`, in Abel form. -/
def gridInterpolant (G : ℝ → ℝ) (a d : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, (G (a + (j + 1) * d) - G (a + j * d)) * unitRamp ((x - a) / d - j)

/-- The interpolant inherits the Lipschitz constant of its data: consecutive ramps never overlap. -/
theorem gridInterpolant_lipschitz {G : ℝ → ℝ} {L : ℝ} (hG : ∀ x y, |G x - G y| ≤ L * |x - y|)
    {a d : ℝ} (hd : 0 < d) (M : ℕ) (x y : ℝ) :
    |gridInterpolant G a d M x - gridInterpolant G a d M y| ≤ L * |x - y| := by
  have hL : 0 ≤ L := by
    have := hG 1 0; norm_num at this; linarith [abs_nonneg (G 1 - G 0)]
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]; exact this y x (le_of_not_ge hxy)
  have hstep (j : ℕ) : |G (a + (j + 1) * d) - G (a + j * d)| ≤ L * d := by
    refine (hG _ _).trans (le_of_eq ?_)
    rw [show a + (j + 1) * d - (a + j * d) = d by ring, abs_of_pos hd]
  have hmono (j : ℕ) : unitRamp ((y - a) / d - j) ≤ unitRamp ((x - a) / d - j) :=
    unitRamp_mono (by have := div_le_div_of_nonneg_right (sub_le_sub_right hxy a) hd.le; linarith)
  unfold gridInterpolant
  rw [← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range M, ((G (a + (j + 1) * d) - G (a + j * d)) * unitRamp ((x - a) / d - j) -
        (G (a + (j + 1) * d) - G (a + j * d)) * unitRamp ((y - a) / d - j))| ≤
      ∑ j ∈ Finset.range M, L * d * (unitRamp ((x - a) / d - j) - unitRamp ((y - a) / d - j)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hmono j))]
        exact mul_le_mul_of_nonneg_right (hstep j) (sub_nonneg.mpr (hmono j))
    _ = L * d * (max 0 (min ((x - a) / d) M) - max 0 (min ((y - a) / d) M)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_unitRamp, sum_unitRamp]
    _ ≤ L * d * ((x - a) / d - (y - a) / d) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL hd.le)
        have h1 := abs_max_sub_max_le_abs (min ((x - a) / d) M) (min ((y - a) / d) M) 0
        have h2 := abs_min_sub_min_le_max ((x - a) / d) (M : ℝ) ((y - a) / d) M
        rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h2
        rw [max_comm 0, max_comm 0]
        have h3 := le_abs_self (max (min ((x - a) / d) ↑M) 0 - max (min ((y - a) / d) ↑M) 0)
        have h4 : (y - a) / d ≤ (x - a) / d :=
          div_le_div_of_nonneg_right (sub_le_sub_right hxy a) hd.le
        rw [abs_of_nonneg (sub_nonneg.mpr h4)] at h2
        linarith
    _ = L * |x - y| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hxy)]; field_simp; ring

/-- At the node `a + kd` the interpolant equals `G(a + kd) - G(a)`. -/
theorem gridInterpolant_node (G : ℝ → ℝ) (a : ℝ) {d : ℝ} (hd : 0 < d) {M k : ℕ} (hk : k ≤ M) :
    gridInterpolant G a d M (a + k * d) = G (a + k * d) - G a := by
  unfold gridInterpolant
  have hr (j : ℕ) : unitRamp ((a + k * d - a) / d - j) = if j < k then 1 else 0 := by
    rw [show (a + k * d - a) / d - j = (k : ℝ) - j by field_simp; ring]
    split_ifs with h
    · exact unitRamp_of_one_le (by linarith [(by exact_mod_cast h : (j : ℝ) + 1 ≤ k)])
    · exact unitRamp_of_le_zero (by linarith [(by exact_mod_cast (not_lt.mp h) : (k : ℝ) ≤ j)])
  simp_rw [hr, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    show Finset.filter (fun j => j < k) (Finset.range M) = Finset.range k by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  have := Finset.sum_range_sub (fun j : ℕ => G (a + j * d)) k
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] at this
  exact this

theorem gridInterpolant_of_le (G : ℝ → ℝ) (a : ℝ) {d : ℝ} (hd : 0 < d) (M : ℕ) {x : ℝ} (hx : x ≤ a) :
    gridInterpolant G a d M x = 0 := by
  unfold gridInterpolant
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [unitRamp_of_le_zero, mul_zero]
  have : (x - a) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem gridInterpolant_of_ge (G : ℝ → ℝ) (a : ℝ) {d : ℝ} (hd : 0 < d) (M : ℕ) {x : ℝ}
    (hx : a + M * d ≤ x) : gridInterpolant G a d M x = G (a + M * d) - G a := by
  rw [← gridInterpolant_node G a hd le_rfl]
  unfold gridInterpolant
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjM : (j : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.mp hj
  rw [unitRamp_of_one_le, unitRamp_of_one_le]
  · rw [show (a + M * d - a) / d - j = (M : ℝ) - j by field_simp; ring]; linarith
  · have : (M : ℝ) ≤ (x - a) / d := by rw [le_div_iff₀ hd]; linarith
    linarith

/-- A Lipschitz profile vanishing off the grid window is approximated within `2Ld`. -/
theorem abs_gridInterpolant_sub_le {G : ℝ → ℝ} {L : ℝ} (hG : ∀ x y, |G x - G y| ≤ L * |x - y|)
    {a d : ℝ} (hd : 0 < d) {M : ℕ} (ha : G a = 0)
    (hout : ∀ x, x ≤ a ∨ a + M * d ≤ x → G x = 0) (x : ℝ) :
    |gridInterpolant G a d M x - G x| ≤ 2 * L * d := by
  have hL : 0 ≤ L := by
    have := hG 1 0; norm_num at this; linarith [abs_nonneg (G 1 - G 0)]
  rcases le_or_gt x a with hxa | hxa
  · rw [gridInterpolant_of_le G a hd M hxa, hout x (Or.inl hxa)]; simp; positivity
  rcases le_or_gt (a + M * d) x with hxb | hxb
  · rw [gridInterpolant_of_ge G a hd M hxb, hout x (Or.inr hxb), hout _ (Or.inr le_rfl), ha]
    simp; positivity
  set r := (x - a) / d with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hd.le
  have hrM : r < M := by rw [hr, div_lt_iff₀ hd]; linarith
  set k := ⌊r⌋₊ with hk
  have hkM : k ≤ M := Nat.floor_le_of_le hrM.le
  have hk1 : (k : ℝ) ≤ r := Nat.floor_le hr0
  have hk2 : r < k + 1 := Nat.lt_floor_add_one r
  have hlo : a + k * d ≤ x := by
    have := mul_le_mul_of_nonneg_right hk1 hd.le
    rw [hr, div_mul_cancel₀ _ hd.ne'] at this; linarith
  have hhi : x - (a + k * d) ≤ d := by
    have := mul_lt_mul_of_pos_right hk2 hd
    rw [hr, div_mul_cancel₀ _ hd.ne'] at this; linarith
  have hnode := gridInterpolant_node G a hd hkM
  rw [ha, sub_zero] at hnode
  have h1 := gridInterpolant_lipschitz (a := a) hG hd M x (a + k * d)
  have h2 := hG (a + k * d) x
  rw [abs_of_nonneg (by linarith : 0 ≤ x - (a + k * d))] at h1
  rw [abs_of_nonpos (by linarith : a + k * d - x ≤ 0)] at h2
  calc |gridInterpolant G a d M x - G x| ≤
      |gridInterpolant G a d M x - gridInterpolant G a d M (a + k * d)| +
        |G (a + k * d) - G x| := by
        rw [hnode]; exact abs_sub_le _ _ _
    _ ≤ L * (x - (a + k * d)) + L * (-(a + k * d - x)) := add_le_add h1 h2
    _ ≤ 2 * L * d := by nlinarith

/-- A factorial hat is a difference of two unit ramps. -/
theorem causalTent_div_eq {d : ℝ} (hd : 0 < d) (y : ℝ) :
    BiScaleUncertainty.SignedPrimePolar.causalTent d y / d = unitRamp (y / d) - unitRamp (y / d - 1) := by
  unfold BiScaleUncertainty.SignedPrimePolar.causalTent unitRamp
  rcases le_total y 0 with h0 | h0
  · have : y / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 hd.le
    rw [max_eq_left (by simp only [min_le_iff]; left; exact h0), max_eq_left
      ((min_le_left _ _).trans this), max_eq_left ((min_le_left _ _).trans (by linarith))]
    simp
  rcases le_total y d with h1 | h1
  · have hy1 : y / d ≤ 1 := by rw [div_le_one hd]; exact h1
    rw [min_eq_left (by linarith : y ≤ 2 * d - y), max_eq_right h0, min_eq_left hy1,
      max_eq_right (div_nonneg h0 hd.le), max_eq_left ((min_le_left _ _).trans (by linarith))]
    simp
  rcases le_total y (2 * d) with h2 | h2
  · have hy1 : 1 ≤ y / d := by rw [le_div_iff₀ hd]; linarith
    have hy2 : y / d - 1 ≤ 1 := by
      have : y / d ≤ 2 := by rw [div_le_iff₀ hd]; linarith
      linarith
    rw [min_eq_right (by linarith : 2 * d - y ≤ y), max_eq_right (by linarith : (0 : ℝ) ≤ 2 * d - y),
      min_eq_right hy1, max_eq_right zero_le_one, min_eq_left hy2,
      max_eq_right (by linarith : (0 : ℝ) ≤ y / d - 1)]
    field_simp; ring
  · have hy1 : 1 ≤ y / d := by rw [le_div_iff₀ hd]; linarith
    have hy2 : 1 ≤ y / d - 1 := by
      have : 2 ≤ y / d := by rw [le_div_iff₀ hd]; linarith
      linarith
    rw [max_eq_left ((min_le_right _ _).trans (by linarith)), min_eq_right hy1,
      max_eq_right zero_le_one, min_eq_right hy2, max_eq_right zero_le_one]
    simp

/-- Abel summation turns the hat expansion into the ramp form of the interpolant. -/
theorem sum_hat_eq_gridInterpolant (G : ℝ → ℝ) (a d : ℝ) (M : ℕ) (u : ℝ) :
    ∑ i ∈ Finset.range (M + 1), G (a + i * d) * (unitRamp (u - i + 1) - unitRamp (u - i)) =
      G a * unitRamp (u + 1) +
        (∑ j ∈ Finset.range M, (G (a + (j + 1) * d) - G (a + j * d)) * unitRamp (u - j)) -
          G (a + M * d) * unitRamp (u - M) := by
  induction M with
  | zero => simp; ring
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    rw [show u - ((M : ℝ) + 1) + 1 = u - M by ring]
    ring

open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar in
/-- The tent pattern of a single scale `n` on the grid `a + j d_n`, whose coefficients carry the
nodal values of `G`; `d_n` is the factorial tent half-width. -/
def gridTentPattern (G : ℝ → ℝ) (n : ℕ) (a : ℝ) (M : ℕ) : C_c(ℝ, ℝ) :=
  factorialTentPattern (Finset.range (M + 1)) (fun _ => n)
    (fun i => G (a + i * sourceFactorialWidth (n + 1)) *
      (Real.exp (sourceFactorialWidth (n + 1)) - 1) ^ 2 *
      Real.exp (-(3 * (sourceFactorialWidth (n + 1) - (a + i * sourceFactorialWidth (n + 1))) / 2)) /
      sourceFactorialWidth (n + 1))
    (fun i => sourceFactorialWidth (n + 1) - (a + i * sourceFactorialWidth (n + 1)))

open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar in
/-- **Exact grid representation.** A single-scale grid tent pattern is `e^{3x/2}` times the
piecewise-linear interpolant of its nodal data. -/
theorem gridTentPattern_apply {G : ℝ → ℝ} (n : ℕ) {a : ℝ} {M : ℕ} (hGa : G a = 0)
    (hGM : G (a + M * sourceFactorialWidth (n + 1)) = 0) (x : ℝ) :
    gridTentPattern G n a M x =
      Real.exp (3 * x / 2) * gridInterpolant G a (sourceFactorialWidth (n + 1)) M x := by
  set d := sourceFactorialWidth (n + 1) with hddef
  have hd : 0 < d := sourceFactorialWidth_pos (by omega)
  have hc1 : Real.exp d - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hd)).ne'
  have hterm (i : ℕ) : G (a + i * d) * (Real.exp d - 1) ^ 2 *
      Real.exp (-(3 * (d - (a + i * d)) / 2)) / d * factorialSourceRight n (x + (d - (a + i * d))) =
      Real.exp (3 * x / 2) * (G (a + i * d) *
        (unitRamp ((x - a) / d - i + 1) - unitRamp ((x - a) / d - i))) := by
    have key : unitRamp ((x - a) / d - i + 1) - unitRamp ((x - a) / d - i) =
        causalTent d (x + (d - (a + i * d))) / d := by
      rw [causalTent_div_eq hd, show (x + (d - (a + i * d))) / d = (x - a) / d - i + 1 by
        field_simp; ring]
      ring_nf
    change _ * exponentialTentSource d _ = _
    rw [exponentialTentSource_eq, key]
    rw [show Real.exp (3 * x / 2) = Real.exp (-(3 * (d - (a + i * d)) / 2)) *
      Real.exp (3 * (x + (d - (a + i * d))) / 2) by rw [← Real.exp_add]; ring_nf]
    field_simp
  unfold gridTentPattern
  rw [factorialTentPattern_apply]
  simp_rw [← hddef]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, sum_hat_eq_gridInterpolant,
    hGa, hGM]
  simp [gridInterpolant]

private theorem abs_exp_sub_exp_le {p q s : ℝ} (hp : p ≤ s) (hq : q ≤ s) :
    |Real.exp p - Real.exp q| ≤ Real.exp s * |p - q| := by
  wlog hqp : q ≤ p generalizing p q
  · rw [abs_sub_comm, abs_sub_comm p q]; exact this hq hp (le_of_not_ge hqp)
  have h1 : Real.exp p - Real.exp q = Real.exp p * (1 - Real.exp (q - p)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  have h2 : 1 - Real.exp (q - p) ≤ p - q := by linarith [Real.add_one_le_exp (q - p)]
  have h3 : 0 ≤ 1 - Real.exp (q - p) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  rw [h1, abs_of_nonneg (mul_nonneg (Real.exp_pos p).le h3), abs_of_nonneg (by linarith : 0 ≤ p - q)]
  exact mul_le_mul (Real.exp_le_exp.mpr hp) h2 h3 (Real.exp_pos s).le

/-- The weight `e^{3x/2}` preserves Lipschitz control on a fixed window. -/
theorem expWeight_mul_lipschitz {F : ℝ → ℝ} {L MF B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (hM : ∀ x, |F x| ≤ MF)
    (hout : ∀ x, B < |x| → F x = 0) (x y : ℝ) :
    |Real.exp (3 * x / 2) * F x - Real.exp (3 * y / 2) * F y| ≤
      Real.exp (3 * B / 2) * (L + 3 / 2 * MF) * |x - y| := by
  have hL : 0 ≤ L := by
    have := hF 1 0; norm_num at this; linarith [abs_nonneg (F 1 - F 0)]
  set c : ℝ → ℝ := fun z => max (min z B) (-B) with hcdef
  have hcle (z : ℝ) : c z ≤ B := max_le (min_le_right _ _) (by linarith)
  have hclip (z : ℝ) : Real.exp (3 * z / 2) * F z = Real.exp (3 * c z / 2) * F z := by
    by_cases hz : |z| ≤ B
    · have h := abs_le.mp hz
      simp only [c, min_eq_left h.2, max_eq_left h.1]
    · rw [hout z (lt_of_not_ge hz), mul_zero, mul_zero]
  have hcl (u v : ℝ) : |c u - c v| ≤ |u - v| := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have := abs_min_sub_min_le_max u B v B
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at this
    exact this
  have hMF : 0 ≤ MF := (abs_nonneg _).trans (hM 0)
  rw [hclip x, hclip y]
  have he1 : Real.exp (3 * c x / 2) ≤ Real.exp (3 * B / 2) :=
    Real.exp_le_exp.mpr (by linarith [hcle x])
  have he2 := abs_exp_sub_exp_le (s := 3 * B / 2) (by linarith [hcle x] : 3 * c x / 2 ≤ 3 * B / 2)
    (by linarith [hcle y] : 3 * c y / 2 ≤ 3 * B / 2)
  rw [show 3 * c x / 2 - 3 * c y / 2 = 3 / 2 * (c x - c y) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at he2
  calc |Real.exp (3 * c x / 2) * F x - Real.exp (3 * c y / 2) * F y|
      = |Real.exp (3 * c x / 2) * (F x - F y) + F y * (Real.exp (3 * c x / 2) - Real.exp (3 * c y / 2))| := by
        ring_nf
    _ ≤ Real.exp (3 * c x / 2) * |F x - F y| + |F y| * |Real.exp (3 * c x / 2) - Real.exp (3 * c y / 2)| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (3 * B / 2) * (L * |x - y|) + MF * (Real.exp (3 * B / 2) * (3 / 2 * |x - y|)) := by
        gcongr
        · exact hF x y
        · exact hM y
        · exact he2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcl x y) (by norm_num))
            (Real.exp_pos _).le)
    _ = _ := by ring

private theorem primeCutoff_large (R : ℝ) :
    2 * (R + 1) < BiScaleUncertainty.SignedPrimePolar.cutoff (compactFullWeilPrimeCutoff R) := by
  have he : Real.exp (2 * (R + 1) + 1) ≤ (compactFullWeilPrimeCutoff R : ℝ) := Nat.le_ceil _
  have he' : Real.exp (2 * (R + 1) + 1) ≤ ((compactFullWeilPrimeCutoff R + 2 : ℕ) : ℝ) := by
    push_cast; linarith
  have h := Real.log_le_log (Real.exp_pos _) he'
  rw [Real.log_exp] at h
  exact lt_of_lt_of_le (by linarith) h

open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar in
/-- **Grid tent patterns converge in the complete Weil form.** For a compact source `g` with
`G = e^{-3x/2} g` Lipschitz, the single-scale grid tent patterns interpolating `G` satisfy
`Q(f_n) → Q(g)`, with every prime, Gamma and polar channel retained. -/
theorem tendsto_compactFullWeilEnergy_gridTentPattern (g : C_c(ℝ, ℝ)) {R Mg Kg L : ℝ} (hR : 0 ≤ R)
    (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg) (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|) :
    Tendsto (fun n : ℕ => compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
      n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) atTop
      (𝓝 (compactFullWeilEnergy g)) := by
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x with hGdef
  set B := R + 2 with hBdef
  have hB : 0 ≤ B := by linarith
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hKg0 : 0 ≤ Kg := by have := (abs_nonneg _).trans (hKg 1 0); norm_num at this; exact this
  have hL0 : 0 ≤ L := by have := (abs_nonneg _).trans (hGL 1 0); norm_num at this; exact this
  set MG := Real.exp (3 * B / 2) * Mg
  have hMG (x : ℝ) : |G x| ≤ MG := by
    by_cases hx : R < |x|
    · simp only [G, hgR x hx, mul_zero, abs_zero]; positivity
    · have hx' := abs_le.mp (le_of_not_gt hx)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hMg x) (abs_nonneg _) (Real.exp_pos _).le
  set Mf := Real.exp (3 * B / 2) * (MG + 2 * L)
  set Kf := Real.exp (3 * B / 2) * (L + 3 / 2 * (MG + 2 * L))
  set N := compactFullWeilPrimeCutoff B
  set Const := (Mf + Mg) * (|EF.gammaBracket 0| + 2 * mass N) + (Kf + Kg) * archWeightFirstMoment
  have hConst : 0 ≤ Const := add_nonneg (mul_nonneg (by positivity)
    (add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (mass_nonneg N))))
    (mul_nonneg (by positivity) archWeightFirstMoment_nonneg)
  have hcut := primeCutoff_large B
  have hkey (n : ℕ) : |compactFullWeilEnergy (gridTentPattern G n (-(R + 1))
      ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) - compactFullWeilEnergy g| ≤
      (2 * B * (Real.exp (3 * B / 2) * (2 * L)) * Const) * sourceFactorialWidth (n + 1) := by
    set d := sourceFactorialWidth (n + 1) with hddef
    have hd : 0 < d := sourceFactorialWidth_pos (by omega)
    have hd1 : d ≤ 1 := sourceFactorialWidth_le_one (by omega)
    set M := ⌈2 * (R + 1) / d⌉₊ with hMdef
    have hM1 : 2 * (R + 1) ≤ M * d := by
      have := Nat.le_ceil (2 * (R + 1) / d)
      rw [div_le_iff₀ hd] at this; exact this
    have hM2 : M * d ≤ 2 * (R + 1) + d := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * (R + 1) / d by positivity)
      have h2 := mul_lt_mul_of_pos_right this hd
      rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at h2
      exact h2.le
    set a := -(R + 1)
    have hgz {x : ℝ} (hx : R < |x|) : G x = 0 := by simp only [G, hgR x hx, mul_zero]
    have hGa : G a = 0 := hgz (by rw [abs_of_neg (by linarith : a < 0)]; simp only [a]; linarith)
    have hGM : G (a + M * d) = 0 := hgz (by rw [abs_of_pos (by simp only [a]; linarith)]; simp only [a]; linarith)
    have hout : ∀ x, x ≤ a ∨ a + M * d ≤ x → G x = 0 := by
      intro x hx
      rcases hx with hx | hx
      · exact hgz (by rw [abs_of_neg (by simp only [a] at hx; linarith)]; simp only [a] at hx; linarith)
      · exact hgz (by rw [abs_of_pos (by simp only [a] at hx; linarith)]; simp only [a] at hx; linarith)
    set F := gridInterpolant G a d M
    have hrep (x : ℝ) : gridTentPattern G n a M x = Real.exp (3 * x / 2) * F x :=
      gridTentPattern_apply n hGa hGM x
    have hFG (x : ℝ) : |F x - G x| ≤ 2 * L * d := abs_gridInterpolant_sub_le hGL hd hGa hout x
    have hFL : ∀ x y, |F x - F y| ≤ L * |x - y| := gridInterpolant_lipschitz hGL hd M
    have hF0 : ∀ x, B < |x| → F x = 0 := by
      intro x hx
      rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hx; linarith) with hneg | hpos
      · rw [abs_of_neg hneg] at hx
        exact gridInterpolant_of_le G a hd M (by simp only [a]; linarith)
      · rw [abs_of_pos hpos] at hx
        show gridInterpolant G a d M x = 0
        rw [gridInterpolant_of_ge G a hd M (by simp only [a]; linarith), hGM, hGa, sub_zero]
    have hFM (x : ℝ) : |F x| ≤ MG + 2 * L := by
      have h1 := hFG x
      have h2 := hMG x
      have h3 : 2 * L * d ≤ 2 * L := by nlinarith
      calc |F x| ≤ |F x - G x| + |G x| := by
            have := abs_sub_abs_le_abs_sub (F x) (G x); linarith
        _ ≤ _ := by linarith
    have hfM (x : ℝ) : |gridTentPattern G n a M x| ≤ Mf := by
      rw [hrep]
      by_cases hx : B < |x|
      · rw [hF0 x hx, mul_zero, abs_zero]; positivity
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have hx' := abs_le.mp (le_of_not_gt hx)
        exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hFM x) (abs_nonneg _) (Real.exp_pos _).le
    have hfL : ∀ x y, |gridTentPattern G n a M x - gridTentPattern G n a M y| ≤ Kf * |x - y| := by
      intro x y; rw [hrep, hrep]; exact expWeight_mul_lipschitz hB hFL hFM hF0 x y
    have hf0 : ∀ x, B < |x| → gridTentPattern G n a M x = 0 := by
      intro x hx; rw [hrep, hF0 x hx, mul_zero]
    have hg0 : ∀ x, B < |x| → g x = 0 := fun x hx => hgR x (by linarith)
    have hft : ∀ x, cutoff N ≤ x → autocorr (gridTentPattern G n a M) x = 0 := by
      intro x hx
      exact autocorr_eq_zero_of_far hf0 (by rw [abs_of_pos (by linarith)]; linarith)
    have hgt : ∀ x, cutoff N ≤ x → autocorr g x = 0 := by
      intro x hx
      exact autocorr_eq_zero_of_far hg0 (by rw [abs_of_pos (by linarith)]; linarith)
    have hQ := compactFullWeilEnergy_sub_le_L1 (gridTentPattern G n a M) g hfM hMg hfL hKg N hft hgt
    have hgap : compactSourceL1Gap (gridTentPattern G n a M) g ≤ 2 * B * (Real.exp (3 * B / 2) * (2 * L)) * d := by
      have hpt (x : ℝ) : |gridTentPattern G n a M x - g x| ≤
          (Icc (-B) B).indicator (fun _ => Real.exp (3 * B / 2) * (2 * L * d)) x := by
        by_cases hx : B < |x|
        · rw [hf0 x hx, hg0 x hx, sub_zero, abs_zero]
          exact Set.indicator_nonneg (fun _ _ => by positivity) x
        · have hx' := abs_le.mp (le_of_not_gt hx)
          rw [Set.indicator_of_mem (by exact ⟨hx'.1, hx'.2⟩), hrep]
          have hgG : g x = Real.exp (3 * x / 2) * G x := by
            simp only [G, ← mul_assoc, ← Real.exp_add]; ring_nf; simp
          rw [hgG, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hFG x) (abs_nonneg _) (Real.exp_pos _).le
      have hint : Integrable fun x => |gridTentPattern G n a M x - g x| :=
        ((gridTentPattern G n a M - g).continuous.integrable_of_hasCompactSupport
          (gridTentPattern G n a M - g).hasCompactSupport).abs
      unfold compactSourceL1Gap
      calc (∫ x, |gridTentPattern G n a M x - g x|) ≤
          ∫ x, (Icc (-B) B).indicator (fun _ => Real.exp (3 * B / 2) * (2 * L * d)) x :=
            integral_mono hint ((integrable_indicator_iff measurableSet_Icc).mpr
              (integrableOn_const measure_Icc_lt_top.ne)) hpt
        _ = 2 * B * (Real.exp (3 * B / 2) * (2 * L)) * d := by
            rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
              smul_eq_mul]
            ring
    calc _ ≤ compactSourceL1Gap (gridTentPattern G n a M) g * Const := hQ
      _ ≤ 2 * B * (Real.exp (3 * B / 2) * (2 * L)) * d * Const := mul_le_mul_of_nonneg_right hgap hConst
      _ = _ := by ring
  have hdn : Tendsto (fun n : ℕ => sourceFactorialWidth (n + 1)) atTop (𝓝 0) := by
    have hub : Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 12 : ℝ)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    refine squeeze_zero (fun n => (sourceFactorialWidth_pos (by omega)).le) (fun n => ?_) hub
    have := (sourceFactorialWidth_bounds (N := n + 1) (by omega)).2
    push_cast at this; exact this
  have hlim := hdn.const_mul (2 * B * (Real.exp (3 * B / 2) * (2 * L)) * Const)
  rw [mul_zero] at hlim
  have := squeeze_zero (fun n => abs_nonneg _) hkey hlim
  exact tendsto_sub_nhds_zero_iff.mp (tendsto_zero_iff_abs_tendsto_zero _ |>.mpr this)

open _root_.RHTower.CHMDDoobGraph in
/-- **The factorial tent family is a complete Weil test family.** The Riemann hypothesis holds
iff the complete Weil energy (Gamma, prime and polar channels) is nonnegative on every finite
pattern of translated factorial tents. -/
theorem riemannHypothesis_iff_factorialTentPattern_nonneg :
    RiemannHypothesis ↔ ∀ (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ),
      0 ≤ compactFullWeilEnergy (factorialTentPattern S n b t) := by
  rw [_root_.RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive]
  constructor
  · intro hRH S n b t
    set f := factorialTentPattern S n b t
    set C := compactFullWeilApproximationCost (factorialTentPatternRadius S t)
      (factorialTentPatternValueBound S n b) (factorialTentPatternSlopeBound S n b)
    have hsm (k : ℕ) : 0 ≤ compactFullWeilEnergy (smoothCompactSource f k) :=
      hRH _ (smooth_contDiff (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport) k)
        (smooth_compact f.hasCompactSupport k)
    have hlow (k : ℕ) : -(C / ((k : ℝ) + 1)) ≤ compactFullWeilEnergy f := by
      have h := factorialTentPattern_fullWeil_smoothing_error S n b t k
      have := (abs_le.mp h).2
      linarith [hsm k]
    have hlim : Tendsto (fun k : ℕ => -(C / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C).neg
      simpa [div_eq_mul_inv] using this
    exact le_of_tendsto' hlim hlow
  · intro h g hg hgc
    set gc : C_c(ℝ, ℝ) := ⟨⟨g, hg.continuous⟩, hgc⟩
    obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    set R := max R₀ 0
    have hgR : ∀ x, R < |x| → gc x = 0 := by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR₀ hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_max_left R₀ 0]
    obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
    obtain ⟨Kg, hKg⟩ := hg.lipschitzWith_of_hasCompactSupport hgc (by norm_num)
    have hGc : ContDiff ℝ 2 fun x => Real.exp (-(3 * x / 2)) * g x := by fun_prop
    obtain ⟨L, hL⟩ := hGc.lipschitzWith_of_hasCompactSupport (hgc.mul_left) (by norm_num)
    have hlim := tendsto_compactFullWeilEnergy_gridTentPattern gc (le_max_right R₀ 0) hgR
      (fun x => by rw [← Real.norm_eq_abs]; exact hMg x)
      (fun x y => by
        have := hKg.dist_le_mul x y
        rwa [Real.dist_eq, Real.dist_eq] at this)
      (fun x y => by
        have := hL.dist_le_mul x y
        rwa [Real.dist_eq, Real.dist_eq] at this)
    exact ge_of_tendsto' hlim fun n => h _ _ _ _

end GaloisForLFunctions.ArithmeticPositivityTheory
