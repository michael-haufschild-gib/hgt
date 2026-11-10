import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDegreePointsCarryWeilsArchimedeanDiagonal

/-!
# The comb of the powers of a base

The degree points `qⁿ` of the toric surface of a base `q` form the comb `e^{hℤ}`, `h = log q`.
It is invariant under the subgroup `q^ℤ` of the torus, each point has the mass `h`, and the total
jump rate out of a point is the same at every point:

  `U(h) = Σ_{k ≥ 1} 2h·ω(kh)`,   `ω(x) = e^{−x/2}/(1 − e^{−2x})`.

* **The split** (`two_mul_archLevyDensity`): `2ω(y) = 1/(2 sinh(y/2)) + 1/(2 cosh(y/2))`.
* **The `cosh` part** (`le_tsum_coshTerm`, `tsum_coshTerm_le`): a Riemann sum of a decreasing
  function with primitive `2 arctan e^{y/2}`; it lies in `[π − 2 arctan e^{h/2}, π/2]`.
* **The `sinh` part is a Lambert series** (`tsum_sinhTerm_eq`):
  `Σ_k h/(2 sinh(kh/2)) = Σ_{i ≥ 0} h/(e^{(i+½)h} − 1)`, and
  `h/(e^y − 1) = 1/(i + ½) − h·ρ(y)` at `y = (i + ½)h`, `ρ(y) = 1/y − 1/(e^y − 1)`. The first terms
  sum to `2H_{2I} − H_I`; `ρ` decreases and has the primitive `log y − log(1 − e^{−y})`. Hence
  the sum lies between `γ + 2 log 2 − log h + R(h/2) − h` and `γ + 2 log 2 − log h + R(h/2)`
  (`le_tsum_lambertTerm`, `tsum_lambertTerm_le`).
* **The counterterm of an invariant comb** (`tendsto_baseCombRate_add_log`):
  `U(h) − log(1/(2πh)) → −A(0)` as `h → 0⁺`.

So a comb invariant under a cyclic subgroup of the torus has a constant diagonal, and its
counterterm is `log(1/(2πh))`, the logarithm of its density divided by `2π`. It diverges as the
subgroup becomes dense: no finite part is invariant under two commensurable subgroups. In the
limit `q → 1` the constant is Weil's `−A(0) = γ + π/2 + log 8π`; `γ` and the logarithms come from
the Lambert series, `π/2` from the `cosh` part.
-/

open Finset Filter Topology
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The comb and the split of the Lévy density -/

/-- The total jump rate out of a point of the comb `e^{hℤ}`, each point with the mass `h`. -/
def baseCombRate (h : ℝ) : ℝ :=
  ∑' k : ℕ, 2 * h * _root_.RHTower.archLevyDensity (((k : ℝ) + 1) * h)

/-- `1/(2 sinh(y/2))`. -/
def sinhDensity (y : ℝ) : ℝ := 1 / (Real.exp (y / 2) - Real.exp (-(y / 2)))

/-- `1/(2 cosh(y/2))`. -/
def coshDensity (y : ℝ) : ℝ := 1 / (Real.exp (y / 2) + Real.exp (-(y / 2)))

/-- **The split of the Lévy density**: `2ω(y) = 1/(2 sinh(y/2)) + 1/(2 cosh(y/2))`. -/
theorem two_mul_archLevyDensity {y : ℝ} (hy : 0 < y) :
    2 * _root_.RHTower.archLevyDensity y = sinhDensity y + coshDensity y := by
  have he : 1 < Real.exp (y / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  have h1 : Real.exp (-y / 2) = (Real.exp (y / 2))⁻¹ := by rw [neg_div, Real.exp_neg]
  have h2 : Real.exp (-2 * y) = (Real.exp (y / 2))⁻¹ ^ 4 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold _root_.RHTower.archLevyDensity sinhDensity coshDensity
  rw [h1, h2, Real.exp_neg]
  generalize Real.exp (y / 2) = e at he
  have he0 : 0 < e := by linarith
  have e1 : e - e⁻¹ = (e ^ 2 - 1) / e := by field_simp
  have e2 : e + e⁻¹ = (e ^ 2 + 1) / e := by field_simp
  have e3 : 1 - e⁻¹ ^ 4 = (e ^ 2 - 1) * (e ^ 2 + 1) / e ^ 4 := by
    field_simp
    ring
  have hne : e ^ 2 - 1 ≠ 0 := by nlinarith
  rw [e1, e2, e3]
  field_simp
  ring

/-! ### The `cosh` part -/

/-- A primitive of `coshDensity`: `2 arctan e^{y/2}`. -/
def coshPrimitive (y : ℝ) : ℝ := 2 * Real.arctan (Real.exp (y / 2))

theorem hasDerivAt_coshPrimitive (y : ℝ) : HasDerivAt coshPrimitive (coshDensity y) y := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (y / 2) * (1 / 2)) y :=
    ((hasDerivAt_id' y).div_const 2).exp
  refine (h1.arctan.const_mul 2).congr_deriv ?_
  unfold coshDensity
  rw [Real.exp_neg]
  have he : 0 < Real.exp (y / 2) := Real.exp_pos _
  generalize Real.exp (y / 2) = e at he
  field_simp
  ring

theorem coshDensity_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    coshDensity y ≤ coshDensity x := by
  have hc : ∀ t : ℝ, Real.exp (t / 2) + Real.exp (-(t / 2)) = 2 * Real.cosh (t / 2) := fun t => by
    rw [Real.cosh_eq]
    ring
  have hcosh : Real.cosh (x / 2) ≤ Real.cosh (y / 2) := Real.cosh_le_cosh.mpr (by
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith)
  unfold coshDensity
  rw [hc, hc]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

theorem coshPrimitive_zero : coshPrimitive 0 = Real.pi / 2 := by
  unfold coshPrimitive
  rw [zero_div, Real.exp_zero, Real.arctan_one]
  ring

theorem coshPrimitive_lt (y : ℝ) : coshPrimitive y < Real.pi := by
  unfold coshPrimitive
  linarith [Real.arctan_lt_pi_div_two (Real.exp (y / 2))]

theorem continuous_coshPrimitive : Continuous coshPrimitive := by
  unfold coshPrimitive
  fun_prop

theorem tendsto_coshPrimitive_atTop : Tendsto coshPrimitive atTop (𝓝 Real.pi) := by
  have h1 : Tendsto (fun y : ℝ => Real.exp (y / 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  have h2 := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1).const_mul 2
  have hv : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [hv] at h2
  exact h2

/-- The `cosh` term of the rate at the `k`-th neighbour. -/
def coshTerm (h : ℝ) (k : ℕ) : ℝ := h * coshDensity (((k : ℝ) + 1) * h)

theorem coshTerm_nonneg {h : ℝ} (hh : 0 < h) (k : ℕ) : 0 ≤ coshTerm h k := by
  unfold coshTerm coshDensity
  positivity

theorem sum_coshTerm_eq (h : ℝ) (K : ℕ) :
    ∑ k ∈ range K, coshTerm h k =
      ∑ k ∈ range K, coshDensity ((0 + (k : ℝ) + 1) / h⁻¹) / h⁻¹ :=
  Finset.sum_congr rfl fun k _ => by
    rw [zero_add, div_inv_eq_mul, div_inv_eq_mul, coshTerm, mul_comm]

theorem sum_coshTerm_le {h : ℝ} (hh : 0 < h) (K : ℕ) :
    ∑ k ∈ range K, coshTerm h k ≤ Real.pi - Real.pi / 2 := by
  have h1 := sum_div_le_primitive continuous_coshPrimitive.continuousOn
    (fun x _ => hasDerivAt_coshPrimitive x) (fun x y hx hxy => coshDensity_anti hx hxy)
    (inv_pos.mpr hh) le_rfl K
  rw [zero_div, coshPrimitive_zero, ← sum_coshTerm_eq] at h1
  exact h1.trans (sub_le_sub_right (coshPrimitive_lt _).le _)

theorem summable_coshTerm {h : ℝ} (hh : 0 < h) : Summable (coshTerm h) :=
  summable_of_sum_range_le (coshTerm_nonneg hh) (sum_coshTerm_le hh)

theorem tsum_coshTerm_le {h : ℝ} (hh : 0 < h) :
    ∑' k : ℕ, coshTerm h k ≤ Real.pi - Real.pi / 2 :=
  Real.tsum_le_of_sum_range_le (coshTerm_nonneg hh) (sum_coshTerm_le hh)

theorem le_tsum_coshTerm {h : ℝ} (hh : 0 < h) :
    Real.pi - coshPrimitive h ≤ ∑' k : ℕ, coshTerm h k := by
  have hJ : Tendsto (fun K : ℕ => (0 + (K : ℝ) + 1) / h⁻¹) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ (0 : ℝ) tendsto_natCast_atTop_atTop)).atTop_div_const
      (inv_pos.mpr hh)
  have e : ((0 : ℝ) + 1) / h⁻¹ = h := by rw [zero_add, div_inv_eq_mul, one_mul]
  have hlim := (tendsto_coshPrimitive_atTop.comp hJ).sub_const (coshPrimitive h)
  refine le_of_tendsto' hlim fun K => ?_
  have h1 := primitive_le_sum_div continuous_coshPrimitive.continuousOn
    (fun x _ => hasDerivAt_coshPrimitive x) (fun x y hx hxy => coshDensity_anti hx hxy)
    (inv_pos.mpr hh) le_rfl K
  rw [e, ← sum_coshTerm_eq] at h1
  exact h1.trans ((summable_coshTerm hh).sum_le_tsum _ fun k _ => coshTerm_nonneg hh k)

/-! ### The Lambert series -/

section Lambert

variable {σ : ℝ}

theorem hasSum_lambert_inner (hσ0 : 0 < σ) (hσ1 : σ < 1) (k : ℕ) :
    HasSum (fun i : ℕ => σ ^ ((k + 1) * (2 * i + 1)))
      (σ ^ (k + 1) / (1 - (σ ^ (k + 1)) ^ 2)) := by
  have hs0 : 0 < σ ^ (k + 1) := pow_pos hσ0 _
  have hs1 : σ ^ (k + 1) < 1 := pow_lt_one₀ hσ0.le hσ1 (Nat.succ_ne_zero k)
  have hsq : (σ ^ (k + 1)) ^ 2 < 1 := by nlinarith
  have h := (hasSum_geometric_of_lt_one (sq_nonneg (σ ^ (k + 1))) hsq).mul_left (σ ^ (k + 1))
  rw [← div_eq_mul_inv] at h
  have hf : (fun i : ℕ => σ ^ ((k + 1) * (2 * i + 1))) =
      fun i => σ ^ (k + 1) * ((σ ^ (k + 1)) ^ 2) ^ i := by
    funext i
    ring
  rw [hf]
  exact h

theorem hasSum_lambert_outer (hσ0 : 0 < σ) (hσ1 : σ < 1) (i : ℕ) :
    HasSum (fun k : ℕ => σ ^ ((k + 1) * (2 * i + 1)))
      (σ ^ (2 * i + 1) / (1 - σ ^ (2 * i + 1))) := by
  have hr0 : 0 < σ ^ (2 * i + 1) := pow_pos hσ0 _
  have hr1 : σ ^ (2 * i + 1) < 1 := pow_lt_one₀ hσ0.le hσ1 (Nat.succ_ne_zero _)
  have h := (hasSum_geometric_of_lt_one hr0.le hr1).mul_left (σ ^ (2 * i + 1))
  rw [← div_eq_mul_inv] at h
  have hf : (fun k : ℕ => σ ^ ((k + 1) * (2 * i + 1))) =
      fun k => σ ^ (2 * i + 1) * (σ ^ (2 * i + 1)) ^ k := by
    funext k
    ring
  rw [hf]
  exact h

theorem summable_lambert_left (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Summable fun k : ℕ => σ ^ (k + 1) / (1 - (σ ^ (k + 1)) ^ 2) := by
  have hσ2 : 0 < 1 - σ ^ 2 := by nlinarith
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_geometric_of_lt_one hσ0.le hσ1).mul_right (σ / (1 - σ ^ 2)))
  · have hs0 : 0 < σ ^ (k + 1) := pow_pos hσ0 _
    have hs1 : σ ^ (k + 1) < 1 := pow_lt_one₀ hσ0.le hσ1 (Nat.succ_ne_zero k)
    exact div_nonneg hs0.le (by nlinarith)
  · have hs0 : 0 < σ ^ (k + 1) := pow_pos hσ0 _
    have hsσ : σ ^ (k + 1) ≤ σ := by
      calc σ ^ (k + 1) = σ ^ k * σ := pow_succ σ k
        _ ≤ 1 * σ := by gcongr; exact pow_le_one₀ hσ0.le hσ1.le
        _ = σ := one_mul σ
    have hden : 1 - σ ^ 2 ≤ 1 - (σ ^ (k + 1)) ^ 2 := by nlinarith
    calc σ ^ (k + 1) / (1 - (σ ^ (k + 1)) ^ 2) ≤ σ ^ (k + 1) / (1 - σ ^ 2) :=
          div_le_div_of_nonneg_left hs0.le hσ2 hden
      _ = σ ^ k * (σ / (1 - σ ^ 2)) := by rw [pow_succ]; ring

theorem summable_lambert_right (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Summable fun i : ℕ => σ ^ (2 * i + 1) / (1 - σ ^ (2 * i + 1)) := by
  have hσ2 : 0 < 1 - σ := by linarith
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    ((summable_geometric_of_lt_one hσ0.le hσ1).mul_right (σ / (1 - σ)))
  · have hr0 : 0 < σ ^ (2 * i + 1) := pow_pos hσ0 _
    have hr1 : σ ^ (2 * i + 1) < 1 := pow_lt_one₀ hσ0.le hσ1 (Nat.succ_ne_zero _)
    exact div_nonneg hr0.le (by linarith)
  · have hr0 : 0 < σ ^ (2 * i + 1) := pow_pos hσ0 _
    have hrσ : σ ^ (2 * i + 1) ≤ σ ^ i * σ := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hσ0.le hσ1.le (show i ≤ 2 * i by omega)) hσ0.le
    have hrσ' : σ ^ (2 * i + 1) ≤ σ := hrσ.trans (by
      calc σ ^ i * σ ≤ 1 * σ := by gcongr; exact pow_le_one₀ hσ0.le hσ1.le
        _ = σ := one_mul σ)
    have hden : 1 - σ ≤ 1 - σ ^ (2 * i + 1) := by linarith
    calc σ ^ (2 * i + 1) / (1 - σ ^ (2 * i + 1)) ≤ σ ^ (2 * i + 1) / (1 - σ) :=
          div_le_div_of_nonneg_left hr0.le hσ2 hden
      _ ≤ σ ^ i * σ / (1 - σ) := by gcongr
      _ = σ ^ i * (σ / (1 - σ)) := by ring

theorem summable_lambert_uncurry (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Summable (Function.uncurry fun k i : ℕ => σ ^ ((k + 1) * (2 * i + 1))) := by
  rw [summable_prod_of_nonneg fun p => by
    simp only [Function.uncurry]
    positivity]
  refine ⟨fun k => (hasSum_lambert_inner hσ0 hσ1 k).summable, ?_⟩
  have hf : (fun k : ℕ =>
      ∑' i : ℕ, Function.uncurry (fun k i : ℕ => σ ^ ((k + 1) * (2 * i + 1))) (k, i)) =
      fun k => σ ^ (k + 1) / (1 - (σ ^ (k + 1)) ^ 2) :=
    funext fun k => (hasSum_lambert_inner hσ0 hσ1 k).tsum_eq
  rw [hf]
  exact summable_lambert_left hσ0 hσ1

/-- **The Lambert swap**: `Σ_k σ^k/(1 − σ^{2k}) = Σ_{i ≥ 0} σ^{2i+1}/(1 − σ^{2i+1})`. -/
theorem tsum_lambert_swap (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∑' k : ℕ, σ ^ (k + 1) / (1 - (σ ^ (k + 1)) ^ 2) =
      ∑' i : ℕ, σ ^ (2 * i + 1) / (1 - σ ^ (2 * i + 1)) := by
  have h := (summable_lambert_uncurry hσ0 hσ1).tsum_comm
  simp only [fun k => (hasSum_lambert_inner hσ0 hσ1 k).tsum_eq,
    fun i => (hasSum_lambert_outer hσ0 hσ1 i).tsum_eq] at h
  exact h.symm

end Lambert

/-! ### The Bernoulli density and its primitive -/

/-- `ρ(y) = 1/y − 1/(e^y − 1)`. -/
def bernoulliDensity (y : ℝ) : ℝ := y⁻¹ - (Real.exp y - 1)⁻¹

/-- A primitive of `ρ`: `log y − log(1 − e^{−y})`. -/
def bernoulliPrimitive (y : ℝ) : ℝ := Real.log y - Real.log (1 - Real.exp (-y))

theorem hasDerivAt_bernoulliPrimitive {y : ℝ} (hy : 0 < y) :
    HasDerivAt bernoulliPrimitive (bernoulliDensity y) y := by
  have he : Real.exp (-y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 := Real.hasDerivAt_log hy.ne'
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-y) * -1) y :=
    (hasDerivAt_id' y).neg.exp
  have h3 := (h2.const_sub 1).log (sub_pos.mpr he).ne'
  refine (h1.sub h3).congr_deriv ?_
  unfold bernoulliDensity
  rw [Real.exp_neg]
  have hE : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  generalize Real.exp y = E at hE
  have hE0 : 0 < E := by linarith
  have hE1 : E - 1 ≠ 0 := (sub_pos.mpr hE).ne'
  have e1 : 1 - E⁻¹ = (E - 1) / E := by field_simp
  rw [e1]
  field_simp

theorem hasDerivAt_bernoulliDensity {y : ℝ} (hy : 0 < y) :
    HasDerivAt bernoulliDensity
      (-(y ^ 2)⁻¹ - -Real.exp y / (Real.exp y - 1) ^ 2) y := by
  have hE : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  exact (hasDerivAt_inv hy.ne').sub
    (((Real.hasDerivAt_exp y).sub_const 1).inv (sub_pos.mpr hE).ne')

/-- `ρ` decreases on `(0, ∞)`: `y ≤ 2 sinh(y/2)`. -/
theorem bernoulliDensity_antitoneOn : AntitoneOn bernoulliDensity (Set.Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun x hx => (hasDerivAt_bernoulliDensity hx).continuousAt.continuousWithinAt)
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_bernoulliDensity hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    rw [(hasDerivAt_bernoulliDensity hx0).deriv]
    -- `x·e^{x/2} ≤ e^x − 1`
    have hG : 0 < Real.exp (x / 2) := Real.exp_pos _
    have hGG : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsinh : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_eq, Real.exp_neg] at hsinh
    have hE : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx0
    have hmul : x * Real.exp (x / 2) ≤ Real.exp x - 1 := by
      have hinv : (Real.exp (x / 2))⁻¹ * Real.exp (x / 2) = 1 := inv_mul_cancel₀ hG.ne'
      have h1 : x ≤ Real.exp (x / 2) - (Real.exp (x / 2))⁻¹ := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hG.le
      rw [sub_mul, hGG, hinv] at h2
      exact h2
    have hsq : x ^ 2 * Real.exp x ≤ (Real.exp x - 1) ^ 2 := by
      have h3 : (x * Real.exp (x / 2)) ^ 2 ≤ (Real.exp x - 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hmul 2
      calc x ^ 2 * Real.exp x = (x * Real.exp (x / 2)) ^ 2 := by rw [mul_pow, pow_two (Real.exp _), hGG]
        _ ≤ (Real.exp x - 1) ^ 2 := h3
    have hpos : 0 < (Real.exp x - 1) ^ 2 := by
      have : 0 < Real.exp x - 1 := by linarith
      positivity
    have hx2 : 0 < x ^ 2 := by positivity
    have hle : Real.exp x / (Real.exp x - 1) ^ 2 ≤ (x ^ 2)⁻¹ := by
      rw [div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ hx2]
      linarith
    have hneg : -Real.exp x / (Real.exp x - 1) ^ 2 = -(Real.exp x / (Real.exp x - 1) ^ 2) := by
      rw [neg_div]
    rw [hneg]
    linarith

theorem bernoulliDensity_le_one {y : ℝ} (hy : 0 < y) : bernoulliDensity y ≤ 1 := by
  have hE : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  have h1 := Real.add_one_le_exp (-y)
  rw [Real.exp_neg] at h1
  have hE0 : 0 < Real.exp y := Real.exp_pos y
  -- `(1 − y)·e^y ≤ 1`
  have h2 : (1 - y) * Real.exp y ≤ 1 := by
    have h3 := mul_le_mul_of_nonneg_right h1 hE0.le
    rw [inv_mul_cancel₀ hE0.ne'] at h3
    linarith
  have key : (1 - y) * (Real.exp y - 1) ≤ y := by nlinarith
  unfold bernoulliDensity
  have hE1 : 0 < Real.exp y - 1 := by linarith
  have hsub : 1 - (y⁻¹ - (Real.exp y - 1)⁻¹) =
      (y - (1 - y) * (Real.exp y - 1)) / (y * (Real.exp y - 1)) := by
    field_simp
    ring
  have hnn : 0 ≤ 1 - (y⁻¹ - (Real.exp y - 1)⁻¹) := by
    rw [hsub]
    exact div_nonneg (by linarith) (by positivity)
  linarith

/-- `log y ≤ R(y) ≤ log y + 1/y` and `0 ≤ R(y) ≤ y`. -/
theorem bernoulliPrimitive_bounds {y : ℝ} (hy : 0 < y) :
    (Real.log y ≤ bernoulliPrimitive y ∧ bernoulliPrimitive y ≤ Real.log y + y⁻¹) ∧
      (0 ≤ bernoulliPrimitive y ∧ bernoulliPrimitive y ≤ y) := by
  have he0 : 0 < Real.exp (-y) := Real.exp_pos _
  have he1 : Real.exp (-y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht0 : 0 < 1 - Real.exp (-y) := by linarith
  have h1 := Real.add_one_le_exp (-y)
  have h2 := Real.add_one_le_exp y
  have hE0 : 0 < Real.exp y := Real.exp_pos y
  have hinv : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  -- `log(1 − e^{−y}) ≤ 0`, `≤ log y`, `≥ log y − y`, `≥ −1/y`
  have hl0 : Real.log (1 - Real.exp (-y)) ≤ 0 := Real.log_nonpos ht0.le (by linarith)
  have hl1 : Real.log (1 - Real.exp (-y)) ≤ Real.log y := Real.log_le_log ht0 (by linarith)
  have hl2 : Real.log y - y ≤ Real.log (1 - Real.exp (-y)) := by
    have hprod : y * Real.exp (-y) ≤ 1 - Real.exp (-y) := by nlinarith
    have hlog := Real.log_le_log (by positivity) hprod
    rw [Real.log_mul hy.ne' he0.ne', Real.log_exp] at hlog
    linarith
  have hl3 : -y⁻¹ ≤ Real.log (1 - Real.exp (-y)) := by
    have h3 := Real.one_sub_inv_le_log_of_pos ht0
    have h4 : y * Real.exp (-y) ≤ 1 - Real.exp (-y) := by nlinarith
    have h5 : (1 - Real.exp (-y))⁻¹ ≤ 1 + y⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ ht0]
      have h6 : (1 + y⁻¹) * (1 - Real.exp (-y)) =
          1 - Real.exp (-y) + y⁻¹ * (1 - Real.exp (-y)) := by ring
      have h7 : Real.exp (-y) ≤ y⁻¹ * (1 - Real.exp (-y)) := by
        rw [inv_mul_eq_div, le_div_iff₀ hy]
        linarith
      linarith
    linarith
  unfold bernoulliPrimitive
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Left step: `R(y + h) − R(y) ≤ ρ(y)·h`. -/
theorem bernoulliPrimitive_step_le {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    bernoulliPrimitive (y + h) - bernoulliPrimitive y ≤ bernoulliDensity y * h := by
  have hab : y < y + h := by linarith
  have h1 := sub_le_mul_of_hasDerivAt hab
    (fun x hx => (hasDerivAt_bernoulliPrimitive (hy.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_bernoulliPrimitive (hy.trans hx.1))
    (fun x hx => bernoulliDensity_antitoneOn hy (hy.trans hx.1) hx.1.le)
  rwa [add_sub_cancel_left] at h1

/-- Right step: `ρ(y + h)·h ≤ R(y + h) − R(y)`. -/
theorem le_bernoulliPrimitive_step {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    bernoulliDensity (y + h) * h ≤ bernoulliPrimitive (y + h) - bernoulliPrimitive y := by
  have hab : y < y + h := by linarith
  have h1 := mul_le_sub_of_hasDerivAt hab
    (fun x hx => (hasDerivAt_bernoulliPrimitive (hy.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_bernoulliPrimitive (hy.trans hx.1))
    (fun x hx => bernoulliDensity_antitoneOn (hy.trans hx.1) (hy.trans hab) hx.2.le)
  rwa [add_sub_cancel_left] at h1

theorem le_sum_bernoulliDensity {h : ℝ} (hh : 0 < h) (I : ℕ) :
    bernoulliPrimitive (((I : ℝ) + 1 / 2) * h) - bernoulliPrimitive (1 / 2 * h) ≤
      ∑ i ∈ range I, bernoulliDensity (((i : ℝ) + 1 / 2) * h) * h := by
  have hsum := Finset.sum_range_sub (fun i : ℕ => bernoulliPrimitive (((i : ℝ) + 1 / 2) * h)) I
  simp only [Nat.cast_zero, zero_add] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hy : 0 < ((i : ℝ) + 1 / 2) * h := by positivity
  have e : (((i + 1 : ℕ) : ℝ) + 1 / 2) * h = ((i : ℝ) + 1 / 2) * h + h := by push_cast; ring
  rw [e]
  exact bernoulliPrimitive_step_le hy hh

theorem sum_bernoulliDensity_le {h : ℝ} (hh : 0 < h) (J : ℕ) :
    ∑ i ∈ range (J + 1), bernoulliDensity (((i : ℝ) + 1 / 2) * h) * h ≤
      bernoulliPrimitive (((J : ℝ) + 1 / 2) * h) - bernoulliPrimitive (1 / 2 * h) + h := by
  have hsum := Finset.sum_range_sub (fun i : ℕ => bernoulliPrimitive (((i : ℝ) + 1 / 2) * h)) J
  simp only [Nat.cast_zero, zero_add] at hsum
  rw [Finset.sum_range_succ', ← hsum]
  have h0 : bernoulliDensity ((((0 : ℕ) : ℝ) + 1 / 2) * h) * h ≤ h := by
    have hy : 0 < (((0 : ℕ) : ℝ) + 1 / 2) * h := by positivity
    calc bernoulliDensity ((((0 : ℕ) : ℝ) + 1 / 2) * h) * h ≤ 1 * h :=
          mul_le_mul_of_nonneg_right (bernoulliDensity_le_one hy) hh.le
      _ = h := one_mul h
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) h0
  have hy : 0 < ((i : ℝ) + 1 / 2) * h := by positivity
  have e : (((i + 1 : ℕ) : ℝ) + 1 / 2) * h = ((i : ℝ) + 1 / 2) * h + h := by push_cast; ring
  rw [e]
  exact le_bernoulliPrimitive_step hy hh

/-! ### The partial sums of the Lambert series -/

/-- `Σ_{i < I} 1/(i + ½) = 2H_{2I} − H_I`. -/
theorem sum_range_inv_add_half (I : ℕ) :
    ∑ i ∈ range I, ((i : ℝ) + 1 / 2)⁻¹ = 2 * harm (2 * I) - harm I := by
  induction I with
  | zero => simp [harm_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, harm_succ, harm_succ,
      harm_succ]
    push_cast
    field_simp
    ring

/-- The Lambert term `h/(e^{(i+½)h} − 1)`. -/
def lambertTerm (h : ℝ) (i : ℕ) : ℝ := h * (Real.exp (((i : ℝ) + 1 / 2) * h) - 1)⁻¹

theorem lambertTerm_eq {h : ℝ} (hh : 0 < h) (i : ℕ) :
    lambertTerm h i =
      ((i : ℝ) + 1 / 2)⁻¹ - bernoulliDensity (((i : ℝ) + 1 / 2) * h) * h := by
  have hi : (0 : ℝ) < (i : ℝ) + 1 / 2 := by positivity
  unfold lambertTerm bernoulliDensity
  generalize (Real.exp (((i : ℝ) + 1 / 2) * h) - 1)⁻¹ = c
  field_simp
  ring

theorem sum_lambertTerm {h : ℝ} (hh : 0 < h) (I : ℕ) :
    ∑ i ∈ range I, lambertTerm h i =
      2 * harm (2 * I) - harm I - ∑ i ∈ range I, bernoulliDensity (((i : ℝ) + 1 / 2) * h) * h := by
  rw [← sum_range_inv_add_half, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => lambertTerm_eq hh i

/-- The harmonic part of the partial sums: `2H_{2(J+1)} − H_{J+1} − log(J + 1) → γ + 2 log 2`. -/
theorem tendsto_harm_double_sub :
    Tendsto (fun J : ℕ => 2 * harm (2 * (J + 1)) - harm (J + 1) - Real.log ((J : ℝ) + 1)) atTop
      (𝓝 (Real.eulerMascheroniConstant + 2 * Real.log 2)) := by
  have hsucc : Tendsto (fun J : ℕ => J + 1) atTop atTop := tendsto_add_atTop_nat 1
  have h2 : Tendsto (fun J : ℕ => 2 * (J + 1)) atTop atTop :=
    tendsto_atTop_mono (fun J => by
      show J ≤ 2 * (J + 1)
      omega) tendsto_id
  have f1 := tendsto_harm_sub_log.comp h2
  have f2 := tendsto_harm_sub_log.comp hsucc
  have h := ((f1.const_mul 2).sub f2).add_const (2 * Real.log 2)
  have hv : 2 * Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + 2 * Real.log 2 =
      Real.eulerMascheroniConstant + 2 * Real.log 2 := by ring
  rw [hv] at h
  refine h.congr fun J => ?_
  have hJ : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  simp only [Function.comp_apply]
  rw [show ((2 * (J + 1) : ℕ) : ℝ) = 2 * ((J : ℝ) + 1) by push_cast; ring,
    show ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 by push_cast; ring,
    Real.log_mul (x := 2) (y := (J : ℝ) + 1) (by norm_num) hJ.ne']
  ring

theorem sum_lambertTerm_le {h : ℝ} (hh : 0 < h) (J : ℕ) :
    ∑ i ∈ range (J + 1), lambertTerm h i ≤
      2 * harm (2 * (J + 1)) - harm (J + 1) - Real.log ((J : ℝ) + 1) - Real.log h +
        bernoulliPrimitive (1 / 2 * h) := by
  have hJ : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hy : 0 < (((J + 1 : ℕ) : ℝ) + 1 / 2) * h := by positivity
  have hlow := le_sum_bernoulliDensity hh (J + 1)
  have hR := (bernoulliPrimitive_bounds hy).1.1
  have hlog : Real.log ((J : ℝ) + 1) + Real.log h ≤ Real.log ((((J + 1 : ℕ) : ℝ) + 1 / 2) * h) := by
    rw [← Real.log_mul hJ.ne' hh.ne']
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith
  rw [sum_lambertTerm hh]
  linarith

theorem le_sum_lambertTerm {h : ℝ} (hh : 0 < h) (J : ℕ) :
    2 * harm (2 * (J + 1)) - harm (J + 1) - Real.log ((J : ℝ) + 1) - Real.log h +
        bernoulliPrimitive (1 / 2 * h) - h - (((J : ℝ) + 1 / 2) * h)⁻¹ ≤
      ∑ i ∈ range (J + 1), lambertTerm h i := by
  have hJ : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hJ2 : (0 : ℝ) < (J : ℝ) + 1 / 2 := by positivity
  have hy : 0 < ((J : ℝ) + 1 / 2) * h := by positivity
  have hupp := sum_bernoulliDensity_le hh J
  have hR := (bernoulliPrimitive_bounds hy).1.2
  have hlog : Real.log (((J : ℝ) + 1 / 2) * h) ≤ Real.log ((J : ℝ) + 1) + Real.log h := by
    rw [← Real.log_mul hJ.ne' hh.ne']
    apply Real.log_le_log hy
    nlinarith
  rw [sum_lambertTerm hh]
  linarith

/-! ### The `sinh` part is the Lambert series -/

/-- The `sinh` term of the rate at the `k`-th neighbour. -/
def sinhTerm (h : ℝ) (k : ℕ) : ℝ := h * sinhDensity (((k : ℝ) + 1) * h)

theorem sinhDensity_eq {h : ℝ} (hh : 0 < h) (k : ℕ) :
    sinhDensity (((k : ℝ) + 1) * h) =
      Real.exp (-(h / 2)) ^ (k + 1) / (1 - (Real.exp (-(h / 2)) ^ (k + 1)) ^ 2) := by
  have hσ0 : 0 < Real.exp (-(h / 2)) := Real.exp_pos _
  have hσ1 : Real.exp (-(h / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Real.exp (-(((k : ℝ) + 1) * h / 2)) = Real.exp (-(h / 2)) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hs' : Real.exp (((k : ℝ) + 1) * h / 2) = (Real.exp (-(h / 2)) ^ (k + 1))⁻¹ := by
    rw [← hs, Real.exp_neg, inv_inv]
  have hs0 : 0 < Real.exp (-(h / 2)) ^ (k + 1) := pow_pos hσ0 _
  have hs1 : Real.exp (-(h / 2)) ^ (k + 1) < 1 := pow_lt_one₀ hσ0.le hσ1 (Nat.succ_ne_zero k)
  unfold sinhDensity
  rw [hs, hs']
  generalize Real.exp (-(h / 2)) ^ (k + 1) = s at hs0 hs1
  have hne : 1 - s ^ 2 ≠ 0 := by nlinarith
  have e1 : s⁻¹ - s = (1 - s ^ 2) / s := by field_simp
  rw [e1]
  field_simp

theorem lambertTerm_eq_pow {h : ℝ} (hh : 0 < h) (i : ℕ) :
    lambertTerm h i =
      h * (Real.exp (-(h / 2)) ^ (2 * i + 1) / (1 - Real.exp (-(h / 2)) ^ (2 * i + 1))) := by
  have hσ0 : 0 < Real.exp (-(h / 2)) := Real.exp_pos _
  have hσ1 : Real.exp (-(h / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr : Real.exp (-(((i : ℝ) + 1 / 2) * h)) = Real.exp (-(h / 2)) ^ (2 * i + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hr' : Real.exp (((i : ℝ) + 1 / 2) * h) = (Real.exp (-(h / 2)) ^ (2 * i + 1))⁻¹ := by
    rw [← hr, Real.exp_neg, inv_inv]
  have hr0 : 0 < Real.exp (-(h / 2)) ^ (2 * i + 1) := pow_pos hσ0 _
  have hr1 : Real.exp (-(h / 2)) ^ (2 * i + 1) < 1 :=
    pow_lt_one₀ hσ0.le hσ1 (Nat.succ_ne_zero _)
  unfold lambertTerm
  rw [hr']
  generalize Real.exp (-(h / 2)) ^ (2 * i + 1) = r at hr0 hr1
  have hne : 1 - r ≠ 0 := by linarith
  have e1 : r⁻¹ - 1 = (1 - r) / r := by field_simp
  rw [e1, inv_div]

theorem summable_sinhTerm {h : ℝ} (hh : 0 < h) : Summable (sinhTerm h) := by
  have hσ0 : 0 < Real.exp (-(h / 2)) := Real.exp_pos _
  have hσ1 : Real.exp (-(h / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hf : sinhTerm h = fun k : ℕ =>
      h * (Real.exp (-(h / 2)) ^ (k + 1) / (1 - (Real.exp (-(h / 2)) ^ (k + 1)) ^ 2)) :=
    funext fun k => by rw [sinhTerm, sinhDensity_eq hh]
  rw [hf]
  exact (summable_lambert_left hσ0 hσ1).mul_left h

theorem summable_lambertTerm {h : ℝ} (hh : 0 < h) : Summable (lambertTerm h) := by
  have hσ0 : 0 < Real.exp (-(h / 2)) := Real.exp_pos _
  have hσ1 : Real.exp (-(h / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hf : lambertTerm h = fun i : ℕ =>
      h * (Real.exp (-(h / 2)) ^ (2 * i + 1) / (1 - Real.exp (-(h / 2)) ^ (2 * i + 1))) :=
    funext fun i => lambertTerm_eq_pow hh i
  rw [hf]
  exact (summable_lambert_right hσ0 hσ1).mul_left h

/-- **The `sinh` part is a Lambert series.** -/
theorem tsum_sinhTerm_eq {h : ℝ} (hh : 0 < h) :
    ∑' k : ℕ, sinhTerm h k = ∑' i : ℕ, lambertTerm h i := by
  have hσ0 : 0 < Real.exp (-(h / 2)) := Real.exp_pos _
  have hσ1 : Real.exp (-(h / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 : ∑' k : ℕ, sinhTerm h k = h * ∑' k : ℕ,
      Real.exp (-(h / 2)) ^ (k + 1) / (1 - (Real.exp (-(h / 2)) ^ (k + 1)) ^ 2) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [sinhTerm, sinhDensity_eq hh]
  have h2 : ∑' i : ℕ, lambertTerm h i = h * ∑' i : ℕ,
      Real.exp (-(h / 2)) ^ (2 * i + 1) / (1 - Real.exp (-(h / 2)) ^ (2 * i + 1)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun i => lambertTerm_eq_pow hh i
  rw [h1, h2, tsum_lambert_swap hσ0 hσ1]

/-- The Lambert series from above. -/
theorem tsum_lambertTerm_le {h : ℝ} (hh : 0 < h) :
    ∑' i : ℕ, lambertTerm h i ≤
      Real.eulerMascheroniConstant + 2 * Real.log 2 - Real.log h +
        bernoulliPrimitive (1 / 2 * h) := by
  have hP := (summable_lambertTerm hh).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hU := (tendsto_harm_double_sub.sub_const (Real.log h)).add_const
    (bernoulliPrimitive (1 / 2 * h))
  exact le_of_tendsto_of_tendsto' hP hU fun J => sum_lambertTerm_le hh J

/-- The Lambert series from below. -/
theorem le_tsum_lambertTerm {h : ℝ} (hh : 0 < h) :
    Real.eulerMascheroniConstant + 2 * Real.log 2 - Real.log h +
        bernoulliPrimitive (1 / 2 * h) - h ≤ ∑' i : ℕ, lambertTerm h i := by
  have hP := (summable_lambertTerm hh).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun J : ℕ => (((J : ℝ) + 1 / 2) * h)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_atTop_add_const_right _ (1 / 2) tendsto_natCast_atTop_atTop).atTop_mul_const hh)
  have hL := ((((tendsto_harm_double_sub.sub_const (Real.log h)).add_const
    (bernoulliPrimitive (1 / 2 * h))).sub_const h).sub hinv)
  rw [sub_zero] at hL
  exact le_of_tendsto_of_tendsto' hL hP fun J => le_sum_lambertTerm hh J

/-! ### The counterterm of the invariant comb -/

theorem baseCombRate_eq {h : ℝ} (hh : 0 < h) :
    baseCombRate h = ∑' i : ℕ, lambertTerm h i + ∑' k : ℕ, coshTerm h k := by
  have hterm : ∀ k : ℕ, 2 * h * _root_.RHTower.archLevyDensity (((k : ℝ) + 1) * h) =
      sinhTerm h k + coshTerm h k := by
    intro k
    have hy : 0 < ((k : ℝ) + 1) * h := by positivity
    rw [sinhTerm, coshTerm, ← mul_add, ← two_mul_archLevyDensity hy]
    ring
  rw [baseCombRate, tsum_congr hterm, (summable_sinhTerm hh).tsum_add (summable_coshTerm hh),
    tsum_sinhTerm_eq hh]

/-- **The counterterm of a comb invariant under a subgroup of the torus**: the total jump rate of
the comb `e^{hℤ}` minus `log(1/(2πh))` tends to `−A(0)` as `h → 0⁺`. -/
theorem tendsto_baseCombRate_add_log :
    Tendsto (fun h : ℝ => baseCombRate h + Real.log (2 * Real.pi * h)) (𝓝[>] 0)
      (𝓝 (-EF.gammaBracket 0)) := by
  rw [_root_.RHTower.ArchimedeanAnomaly.gammaBracket_zero_eq, neg_neg]
  have h8 : Real.log (8 * Real.pi) = 2 * Real.log 2 + Real.log (2 * Real.pi) := by
    rw [show (8 : ℝ) * Real.pi = 2 ^ 2 * (2 * Real.pi) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  -- the two bounds
  have hlow : Tendsto (fun h : ℝ => Real.eulerMascheroniConstant + 2 * Real.log 2 - h +
      (Real.pi - coshPrimitive h) + Real.log (2 * Real.pi)) (𝓝[>] 0)
      (𝓝 (Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi))) := by
    have hc : Continuous fun h : ℝ => Real.eulerMascheroniConstant + 2 * Real.log 2 - h +
        (Real.pi - coshPrimitive h) + Real.log (2 * Real.pi) := by
      have := continuous_coshPrimitive
      fun_prop
    have h0 := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ)) (hc.tendsto 0)
    have hv : Real.eulerMascheroniConstant + 2 * Real.log 2 - 0 + (Real.pi - coshPrimitive 0) +
        Real.log (2 * Real.pi) =
        Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi) := by
      rw [coshPrimitive_zero, h8]
      ring
    rw [hv] at h0
    exact h0
  have hupp : Tendsto (fun h : ℝ => Real.eulerMascheroniConstant + 2 * Real.log 2 + h / 2 +
      (Real.pi - Real.pi / 2) + Real.log (2 * Real.pi)) (𝓝[>] 0)
      (𝓝 (Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi))) := by
    have hc : Continuous fun h : ℝ => Real.eulerMascheroniConstant + 2 * Real.log 2 + h / 2 +
        (Real.pi - Real.pi / 2) + Real.log (2 * Real.pi) := by fun_prop
    have h0 := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ)) (hc.tendsto 0)
    have hv : Real.eulerMascheroniConstant + 2 * Real.log 2 + 0 / 2 + (Real.pi - Real.pi / 2) +
        Real.log (2 * Real.pi) =
        Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi) := by
      rw [h8]
      ring
    rw [hv] at h0
    exact h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : (0 : ℝ) < h := hh
    have hy : (0 : ℝ) < 1 / 2 * h := by positivity
    have hR := (bernoulliPrimitive_bounds hy).2.1
    have h1 := le_tsum_lambertTerm hh0
    have h2 := le_tsum_coshTerm hh0
    rw [baseCombRate_eq hh0, Real.log_mul (by positivity) hh0.ne']
    linarith
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : (0 : ℝ) < h := hh
    have hy : (0 : ℝ) < 1 / 2 * h := by positivity
    have hR := (bernoulliPrimitive_bounds hy).2.2
    have h1 := tsum_lambertTerm_le hh0
    have h2 := tsum_coshTerm_le hh0
    rw [baseCombRate_eq hh0, Real.log_mul (by positivity) hh0.ne']
    linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
