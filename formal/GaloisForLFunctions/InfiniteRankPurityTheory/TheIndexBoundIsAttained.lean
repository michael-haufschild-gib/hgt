import GaloisForLFunctions.InfiniteRankPurityTheory.TheEisensteinConstantTermIsPureByParity
import GaloisForLFunctions.InfiniteRankWeilTheory.TheFunctionalEquationAdmitsEveryFiniteLayer
import GaloisForLFunctions.RHTower.XiGlobalKummerSquareClasses

/-!
# The index bound is attained

The index-one theorem leaves room for one real exceptional point on each side of the line, and for
nothing else. Both halves are sharp.

* **The exceptional parameter exists.** For every `x₁ ∈ (½, 1)` and all large `Y` the cleared
  constant term `(s − 1) ξ(2s) Y^s + s ξ(2s − 1) Y^{1−s}` has exactly one zero right of the line; it is
  real and lies in `(x₁, 1)` (`exists_unique_exceptionalParameter`). On the real axis the function is
  `½` at `s = 1` and negative at `x₁` once `Y^{2x₁−1}` is large, since `ξ > 0` on the real axis; the
  intermediate value theorem gives the zero and the index bound its uniqueness. This is an exceptional
  spectral parameter, `s(1 − s) < ¼`, of an object built from `ζ`: purity by parity is `c`-purity and
  cannot be improved to purity.
* **It is born once.** An exceptional parameter is real and lies in `(½, 1)`
  (`exceptionalParameter_mem`); once it exists at a height it exists at every larger height and moves
  to the right (`exceptionalParameter_mono`).
* **Index two admits a non-real pair.** The `cosh` model of one quartet is a Hermite–Biehler sum
  `P E + P♯ E'` with `E ≠ 0` and `‖E'‖ ≤ ‖E‖` right of the line and a real defect `P = (s − q)(s − q̄)`
  of degree two, and it vanishes at the non-real pair `q, q̄` (`indexTwo_admits_nonreal_pair`). The
  parity argument needs the index to be smaller than the orbit of complex conjugation.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower _root_.RHTower.XiGlobalKummer GaloisForLFunctions.InfiniteRankWeilTheory

noncomputable section

/-! ### The exceptional parameter of the constant term -/

/-- `ξ` on the real axis, as a real function. -/
def xiReal (t : ℝ) : ℝ := (xi (t : ℂ)).re

theorem xiReal_pos (t : ℝ) : 0 < xiReal t := xi_real_pos t

theorem xi_ofReal (t : ℝ) : xi (t : ℂ) = (xiReal t : ℂ) := (xi_real_cast t).symm

theorem continuous_xiReal : Continuous xiReal :=
  Complex.continuous_re.comp (xi_differentiable.continuous.comp Complex.continuous_ofReal)

/-- The cleared constant term on the real axis. -/
def constantTermReal (Y x : ℝ) : ℝ :=
  (x - 1) * xiReal (2 * x) * Y ^ x + x * xiReal (2 * x - 1) * Y ^ (1 - x)

theorem constantTerm_ofReal {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    constantTerm Y (x : ℂ) = (constantTermReal Y x : ℂ) := by
  have e1 : (2 : ℂ) * (x : ℂ) = ((2 * x : ℝ) : ℂ) := by push_cast; ring
  have e2 : (2 : ℂ) * (x : ℂ) - 1 = ((2 * x - 1 : ℝ) : ℂ) := by push_cast; ring
  have e3 : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
  rw [constantTerm, constantTermHalf, constantTermDual, constantTermReal, e2, e1, e3, xi_ofReal,
    xi_ofReal, ← Complex.ofReal_cpow hY.le, ← Complex.ofReal_cpow hY.le]
  push_cast
  ring

theorem continuous_constantTermReal {Y : ℝ} (hY : 0 < Y) : Continuous (constantTermReal Y) := by
  have hp1 : Continuous fun x : ℝ => Y ^ x :=
    continuous_const.rpow continuous_id (fun _ => Or.inl hY.ne')
  have hp2 : Continuous fun x : ℝ => Y ^ (1 - x) :=
    continuous_const.rpow (continuous_const.sub continuous_id) (fun _ => Or.inl hY.ne')
  have hx1 : Continuous fun x : ℝ => xiReal (2 * x) := continuous_xiReal.comp (by fun_prop)
  have hx2 : Continuous fun x : ℝ => xiReal (2 * x - 1) := continuous_xiReal.comp (by fun_prop)
  unfold constantTermReal
  exact (((continuous_id.sub continuous_const).mul hx1).mul hp1).add ((continuous_id.mul hx2).mul hp2)

theorem constantTermReal_one {Y : ℝ} (hY : 0 < Y) : constantTermReal Y 1 = 1 / 2 := by
  have h := constantTerm_ofReal hY 1
  rw [Complex.ofReal_one, constantTerm_one hY] at h
  have h2 : ((1 / 2 : ℝ) : ℂ) = (constantTermReal Y 1 : ℂ) := by rw [← h]; norm_num
  exact (Complex.ofReal_injective h2).symm

/-- At a point `x₁ ∈ (½, 1)` the cleared constant term is negative once `Y^{2x₁−1}` exceeds
`x₁ ξ(2x₁−1) / ((1−x₁) ξ(2x₁))`. -/
theorem constantTermReal_neg {Y x₁ : ℝ} (hY : 0 < Y)
    (hlarge : x₁ * xiReal (2 * x₁ - 1) < (1 - x₁) * xiReal (2 * x₁) * Y ^ (2 * x₁ - 1)) :
    constantTermReal Y x₁ < 0 := by
  have hsplit : Y ^ x₁ = Y ^ (2 * x₁ - 1) * Y ^ (1 - x₁) := by
    rw [← Real.rpow_add hY]
    congr 1
    ring
  have hpos : 0 < Y ^ (1 - x₁) := Real.rpow_pos_of_pos hY _
  have hfac : constantTermReal Y x₁ =
      (x₁ * xiReal (2 * x₁ - 1) - (1 - x₁) * xiReal (2 * x₁) * Y ^ (2 * x₁ - 1)) *
        Y ^ (1 - x₁) := by
    rw [constantTermReal, hsplit]
    ring
  rw [hfac]
  exact mul_neg_of_neg_of_pos (by linarith) hpos

/-- A real zero in `(x₁, 1)` under the size condition. -/
theorem exists_zero_constantTermReal {Y x₁ : ℝ} (hY : 0 < Y) (h2 : x₁ < 1)
    (hlarge : x₁ * xiReal (2 * x₁ - 1) < (1 - x₁) * xiReal (2 * x₁) * Y ^ (2 * x₁ - 1)) :
    ∃ x : ℝ, x₁ < x ∧ x < 1 ∧ constantTermReal Y x = 0 := by
  have hneg := constantTermReal_neg hY hlarge
  have hone := constantTermReal_one hY
  have hmem : (0 : ℝ) ∈ Ioo (constantTermReal Y x₁) (constantTermReal Y 1) := by
    rw [hone]
    exact ⟨hneg, by norm_num⟩
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := intermediate_value_Ioo h2.le
    (continuous_constantTermReal hY).continuousOn hmem
  exact ⟨x, hx1, hx2, hx⟩

/-- **The exceptional parameter.** For every `x₁ ∈ (½, 1)` and all large `Y` the cleared constant
term has exactly one zero right of the line; it is real and lies in `(x₁, 1)`. -/
theorem exists_unique_exceptionalParameter {x₁ : ℝ} (h1 : 1 / 2 < x₁) (h2 : x₁ < 1) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, 1 ≤ Y ∧ ∃ x : ℝ, x₁ < x ∧ x < 1 ∧ constantTerm Y (x : ℂ) = 0 ∧
      ∀ s ∈ rightHalf, constantTerm Y s = 0 → s = (x : ℂ) := by
  have hden : 0 < (1 - x₁) * xiReal (2 * x₁) := mul_pos (by linarith) (xiReal_pos _)
  set K : ℝ := x₁ * xiReal (2 * x₁ - 1) / ((1 - x₁) * xiReal (2 * x₁)) with hK
  have hp : 0 < 2 * x₁ - 1 := by linarith
  have hev : ∀ᶠ Y : ℝ in atTop, K < Y ^ (2 * x₁ - 1) ∧ 1 ≤ Y :=
    ((tendsto_rpow_atTop hp).eventually_gt_atTop K).and (eventually_ge_atTop 1)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hev
  refine ⟨Y₀, fun Y hYge => ?_⟩
  obtain ⟨hKlt, hY1⟩ := hY₀ Y hYge
  have hY0 : 0 < Y := by linarith
  have hlarge : x₁ * xiReal (2 * x₁ - 1) < (1 - x₁) * xiReal (2 * x₁) * Y ^ (2 * x₁ - 1) := by
    have := (div_lt_iff₀ hden).mp hKlt
    linarith
  obtain ⟨x, hx1, hx2, hx⟩ := exists_zero_constantTermReal hY0 h2 hlarge
  have hzero : constantTerm Y (x : ℂ) = 0 := by rw [constantTerm_ofReal hY0, hx, Complex.ofReal_zero]
  have hmem : (x : ℂ) ∈ rightHalf := by
    show (1 : ℝ) / 2 < (x : ℂ).re
    rw [Complex.ofReal_re]
    linarith
  refine ⟨hY1, x, hx1, hx2, hzero, fun s hs hsz => ?_⟩
  exact constantTerm_zero_subsingleton hY1 ⟨hs, hsz⟩ ⟨hmem, hzero⟩

/-- The cleared constant term is positive on the real axis from `1` on. -/
theorem constantTermReal_pos_of_one_le {Y x : ℝ} (hY : 0 < Y) (hx : 1 ≤ x) :
    0 < constantTermReal Y x := by
  have h1 : 0 ≤ (x - 1) * xiReal (2 * x) * Y ^ x :=
    mul_nonneg (mul_nonneg (by linarith) (xiReal_pos _).le) (Real.rpow_pos_of_pos hY _).le
  have h2 : 0 < x * xiReal (2 * x - 1) * Y ^ (1 - x) :=
    mul_pos (mul_pos (by linarith) (xiReal_pos _)) (Real.rpow_pos_of_pos hY _)
  unfold constantTermReal
  linarith

/-- **An exceptional parameter is real and lies in `(½, 1)`.** -/
theorem exceptionalParameter_mem {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hs : s ∈ rightHalf)
    (h : constantTerm Y s = 0) : ∃ x : ℝ, s = (x : ℂ) ∧ 1 / 2 < x ∧ x < 1 := by
  have hY0 : 0 < Y := by linarith
  have him := (constantTerm_indexOne hY).2 s hs h
  have hsx : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨s.re, hsx, hs, ?_⟩
  by_contra hge
  have hpos := constantTermReal_pos_of_one_le hY0 (not_lt.mp hge)
  rw [hsx, constantTerm_ofReal hY0] at h
  have : constantTermReal Y s.re = 0 := by exact_mod_cast h
  linarith

/-- **The exceptional parameter persists and moves to the right.** If the cleared constant term at
height `Y₁ ≥ 1` has a real zero `x₁ > ½`, then at every height `Y₂ > Y₁` it has a zero in
`(x₁, 1)`. So the heights with an exceptional parameter form an up-set, and the parameter increases
with the height. -/
theorem exceptionalParameter_mono {Y₁ Y₂ x₁ : ℝ} (hY₁ : 1 ≤ Y₁) (h12 : Y₁ < Y₂) (hx : 1 / 2 < x₁)
    (hz : constantTerm Y₁ (x₁ : ℂ) = 0) :
    ∃ x₂ : ℝ, x₁ < x₂ ∧ x₂ < 1 ∧ constantTerm Y₂ (x₂ : ℂ) = 0 := by
  have hY₁0 : 0 < Y₁ := by linarith
  have hY₂0 : 0 < Y₂ := by linarith
  have hreal : constantTermReal Y₁ x₁ = 0 := by
    rw [constantTerm_ofReal hY₁0] at hz
    exact_mod_cast hz
  have hx1 : x₁ < 1 := by
    by_contra hge
    have := constantTermReal_pos_of_one_le hY₁0 (not_lt.mp hge)
    linarith
  -- at `Y₁` the two terms balance
  have hsplit : Y₁ ^ x₁ = Y₁ ^ (2 * x₁ - 1) * Y₁ ^ (1 - x₁) := by
    rw [← Real.rpow_add hY₁0]
    congr 1
    ring
  have hpos : 0 < Y₁ ^ (1 - x₁) := Real.rpow_pos_of_pos hY₁0 _
  have hbal : x₁ * xiReal (2 * x₁ - 1) = (1 - x₁) * xiReal (2 * x₁) * Y₁ ^ (2 * x₁ - 1) := by
    have hfac : constantTermReal Y₁ x₁ =
        (x₁ * xiReal (2 * x₁ - 1) - (1 - x₁) * xiReal (2 * x₁) * Y₁ ^ (2 * x₁ - 1)) *
          Y₁ ^ (1 - x₁) := by
      rw [constantTermReal, hsplit]
      ring
    rw [hfac] at hreal
    have := (mul_eq_zero.mp hreal).resolve_right hpos.ne'
    linarith
  have hgrow : Y₁ ^ (2 * x₁ - 1) < Y₂ ^ (2 * x₁ - 1) :=
    Real.rpow_lt_rpow hY₁0.le h12 (by linarith)
  have hcoef : 0 < (1 - x₁) * xiReal (2 * x₁) := mul_pos (by linarith) (xiReal_pos _)
  have hlarge : x₁ * xiReal (2 * x₁ - 1) < (1 - x₁) * xiReal (2 * x₁) * Y₂ ^ (2 * x₁ - 1) := by
    rw [hbal]
    exact mul_lt_mul_of_pos_left hgrow hcoef
  obtain ⟨x₂, h1, h2, h0⟩ := exists_zero_constantTermReal hY₂0 hx1 hlarge
  exact ⟨x₂, h1, h2, by rw [constantTerm_ofReal hY₂0, h0, Complex.ofReal_zero]⟩

/-! ### Index two: the `cosh` model of one quartet -/

/-- The defect of a quartet: `(s − q)(s − q̄)`, a real polynomial with both roots right of the
line. -/
def pairFactor (q s : ℂ) : ℂ := (s - q) * (s - starRingEnd ℂ q)

/-- The reflected defect `(s − (1 − q))(s − (1 − q̄))`. -/
def pairFactorDual (q s : ℂ) : ℂ := (s - (1 - q)) * (s - (1 - starRingEnd ℂ q))

/-- The `cosh` model of one quartet as a Hermite–Biehler sum with a defect of degree two. -/
theorem coshModel_singleton_eq (q s : ℂ) :
    coshModel {q} s =
      pairFactor q s * (Complex.exp (s - 1 / 2) / 2 * pairFactorDual q s) +
        pairFactorDual q s * (Complex.exp (1 / 2 - s) / 2 * pairFactor q s) := by
  rw [coshModel, Finset.prod_singleton, quartet, pairFactor, pairFactorDual, Complex.cosh,
    show -(s - 1 / 2) = 1 / 2 - s by ring]
  ring

theorem norm_sub_le_norm_sub_reflect {w s : ℂ} (hw : w ∈ rightHalf) (hs : s ∈ rightHalf) :
    ‖s - w‖ ≤ ‖s - (1 - (starRingEnd ℂ) w)‖ := by
  have hid := normSq_defect_identity w s
  have h1 : (1 : ℝ) / 2 < w.re := hw
  have h2 : (1 : ℝ) / 2 < s.re := hs
  have hpos : 0 ≤ (2 * w.re - 1) * (2 * s.re - 1) := by nlinarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hid
  nlinarith [norm_nonneg (s - w), norm_nonneg (s - (1 - (starRingEnd ℂ) w))]

/-- **Index two admits a non-real pair.** For a non-real `q` right of the line, the `cosh` model of
the quartet of `q` is `P E + P♯ E'` with `P = (s − q)(s − q̄)`, where `E`, `E'` are entire and real,
`E ≠ 0` and `‖E'‖ ≤ ‖E‖` right of the line; it vanishes at the two distinct points `q`, `q̄` right
of the line. -/
theorem indexTwo_admits_nonreal_pair {q : ℂ} (hq : q ∈ rightHalf) (him : q.im ≠ 0) :
    ∃ E E' : ℂ → ℂ, Differentiable ℂ E ∧ Differentiable ℂ E' ∧
      (∀ s ∈ rightHalf, E s ≠ 0) ∧ (∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖) ∧
      (∀ s, E ((starRingEnd ℂ) s) = (starRingEnd ℂ) (E s)) ∧
      (∀ s, E' ((starRingEnd ℂ) s) = (starRingEnd ℂ) (E' s)) ∧
      (∀ s, coshModel {q} s = pairFactor q s * E s + pairFactorDual q s * E' s) ∧
      coshModel {q} q = 0 ∧ coshModel {q} ((starRingEnd ℂ) q) = 0 ∧
      q ≠ (starRingEnd ℂ) q ∧ (starRingEnd ℂ) q ∈ rightHalf := by
  have hqc : (starRingEnd ℂ) q ∈ rightHalf := conj_mem_rightHalf hq
  have h12 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  refine ⟨fun s => Complex.exp (s - 1 / 2) / 2 * pairFactorDual q s,
    fun s => Complex.exp (1 / 2 - s) / 2 * pairFactor q s, ?_, ?_, ?_, ?_, ?_, ?_,
    coshModel_singleton_eq q, ?_, ?_, ?_, hqc⟩
  · unfold pairFactorDual
    fun_prop
  · unfold pairFactor
    fun_prop
  · intro s hs
    have d1 : s - (1 - q) ≠ 0 := by
      have := defect_denom_ne_zero hqc hs
      rwa [Complex.conj_conj] at this
    have d2 : s - (1 - (starRingEnd ℂ) q) ≠ 0 := defect_denom_ne_zero hq hs
    exact mul_ne_zero (div_ne_zero (Complex.exp_ne_zero _) two_ne_zero) (mul_ne_zero d1 d2)
  · intro s hs
    have hs' : (1 : ℝ) / 2 < s.re := hs
    have n1 : ‖s - q‖ ≤ ‖s - (1 - (starRingEnd ℂ) q)‖ := norm_sub_le_norm_sub_reflect hq hs
    have n2 : ‖s - (starRingEnd ℂ) q‖ ≤ ‖s - (1 - q)‖ := by
      have := norm_sub_le_norm_sub_reflect hqc hs
      rwa [Complex.conj_conj] at this
    have hexp : ‖Complex.exp (1 / 2 - s) / 2‖ ≤ ‖Complex.exp (s - 1 / 2) / 2‖ := by
      rw [norm_div, norm_div, Complex.norm_exp, Complex.norm_exp]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simp only [sub_re, one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
      linarith
    simp only [pairFactor, pairFactorDual, norm_mul]
    have hprod : ‖s - q‖ * ‖s - (starRingEnd ℂ) q‖ ≤
        ‖s - (1 - q)‖ * ‖s - (1 - (starRingEnd ℂ) q)‖ := by
      rw [mul_comm ‖s - (1 - q)‖]
      exact mul_le_mul n1 n2 (norm_nonneg _) (norm_nonneg _)
    exact mul_le_mul hexp hprod (by positivity) (norm_nonneg _)
  · intro s
    simp only [pairFactorDual, map_mul, map_div₀, map_sub, map_one, Complex.conj_conj, h12, h2,
      ← Complex.exp_conj]
    ring
  · intro s
    simp only [pairFactor, map_mul, map_div₀, map_sub, Complex.conj_conj, h12, h2,
      ← Complex.exp_conj]
    ring
  · rw [coshModel_singleton_eq]
    simp [pairFactor]
  · rw [coshModel_singleton_eq]
    simp [pairFactor]
  · intro h
    exact him (Complex.conj_eq_iff_im.mp h.symm)

end

end GaloisForLFunctions.InfiniteRankPurityTheory
