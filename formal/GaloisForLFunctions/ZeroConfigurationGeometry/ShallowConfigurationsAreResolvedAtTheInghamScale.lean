import GaloisForLFunctions.ZeroConfigurationGeometry.ResolutionIsUniformInDepth

/-!
# Shallow configurations are resolved at the Ingham scale

`ResolutionIsUniformInDepth` resolves configurations of depth `≤ s` at height separation
`g ≥ 90/V` through a block inequality for the two profiles of a pair. Here the separation is
pushed to the Ingham scale `π/V`, which on-line lattices attain, for every configuration that is
shallow enough.

* **A pair is its centre plus a depth remainder** (`pair_eq_centre_add_rem`):
  `p e^{δv} + q e^{−δv} = (p + q) + p(e^{δv} − 1) + q(e^{−δv} − 1)`. The centres form a scalar
  exponential sum, bounded below by Ingham's inequality at the sharp threshold `g > π/V`
  (`ingham_lower`, the tilted inequality at tilt `0`). The remainders have size `O(e^{2sV} − 1)`
  and derivatives `O(s)`, so their sum has mean square at most `K(V, g, s) Σ (|p_k| + |q_k|)²`
  with `K → 0` as `s → 0` (`remainder_upper`; the weight `cos(πv/(4V))` on `[−2V, 2V]` is
  `≥ 1/2` on `[−V, V]`).
* **Vanishing pair sums** (`inghamConst_mul_normSq_le`). If a summable pair sum vanishes on
  `[−V, V]`, every centre satisfies `θ |p_k + q_k|² ≤ 2K Σ (|p_j| + |q_j|)²`, `θ` the Ingham
  constant: truncate, compare, and let the tail go to zero.
* **The maximal site** (`eq_of_weil_eq_of_shallow`). Localize the camera at the site where the
  multiplicity weighted by `1 + |ρ − ½|²` is largest. There both pair coefficients equal
  `m κ̂_w(−iδ)²` with `κ̂_w(−iδ)` real, so the centre is at least `|m| r²`,
  `r = 4w e^{−ws} ∫κ`; elsewhere the multiplicities are at most `2(1 + s²)(1 + x²)` times the
  maximal one, `x` the height offset, and the bump transform decays like `(1 + |x|)^{−4}`. The
  whole sum is therefore at most `T(w, g, s) |m|²`, and `2KT < θ r⁴` forces `m = 0`.

**The Ingham scale** (`exists_depth_resolving_at_ingham_scale`). For every aperture `a` and every
separation `g > π/(2a)` there is a depth `s₀ > 0` such that tempered configurations of depth
`≤ s₀`, whose union has `g`-separated heights apart from FE partners, are determined by their
Weil forms on `C²` tests supported in `[−a, a]`. On-line lattices of union separation `π/(2a)`
hide at aperture `a`, so the constant `π` is optimal: the resolution scale of shallow
configurations is the Ingham scale.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open SquareRootThreshold Zeta23

/-! ### The depth remainder of a pair -/

/-- The tilt `±δ` of the two frequencies of a pair. -/
def pairTilt (δ : ℝ) (b : Bool) : ℝ := if b then δ else -δ

theorem abs_pairTilt (δ : ℝ) (b : Bool) : |pairTilt δ b| = |δ| := by
  cases b <;> simp [pairTilt]

/-- The depth remainder `e^{±δv} − 1` of a pair. -/
def remProfile (δ : ℝ) (b : Bool) (v : ℝ) : ℝ := Real.exp (pairTilt δ b * v) - 1

def remProfile1 (δ : ℝ) (b : Bool) (v : ℝ) : ℝ := pairTilt δ b * Real.exp (pairTilt δ b * v)

def remProfile2 (δ : ℝ) (b : Bool) (v : ℝ) : ℝ := pairTilt δ b ^ 2 * Real.exp (pairTilt δ b * v)

theorem hasDerivAt_remProfile (δ : ℝ) (b : Bool) (v : ℝ) :
    HasDerivAt (remProfile δ b) (remProfile1 δ b v) v :=
  ((((hasDerivAt_id' v).const_mul (pairTilt δ b)).exp).sub_const 1).congr_deriv
    (by simp only [remProfile1]; ring)

theorem hasDerivAt_remProfile1 (δ : ℝ) (b : Bool) (v : ℝ) :
    HasDerivAt (remProfile1 δ b) (remProfile2 δ b v) v :=
  ((((hasDerivAt_id' v).const_mul (pairTilt δ b)).exp).const_mul (pairTilt δ b)).congr_deriv
    (by simp only [remProfile2]; ring)

theorem continuous_remProfile (δ : ℝ) (b : Bool) : Continuous (remProfile δ b) := by
  unfold remProfile; fun_prop

theorem continuous_remProfile2 (δ : ℝ) (b : Bool) : Continuous (remProfile2 δ b) := by
  unfold remProfile2; fun_prop

/-- The bounds `e^{2sV} − 1`, `s e^{2sV}`, `s² e^{2sV}` of a remainder and its derivatives on
`[−2V, 2V]`. -/
def remBound0 (V s : ℝ) : ℝ := Real.exp (s * (2 * V)) - 1

def remBound1 (V s : ℝ) : ℝ := s * Real.exp (s * (2 * V))

def remBound2 (V s : ℝ) : ℝ := s ^ 2 * Real.exp (s * (2 * V))

theorem remProfile_bounds {δ s V v : ℝ} (hδ : |δ| ≤ s) (hv : v ∈ Icc (-(2 * V)) (2 * V))
    (b : Bool) :
    |remProfile δ b v| ≤ remBound0 V s ∧ |remProfile1 δ b v| ≤ remBound1 V s ∧
      |remProfile2 δ b v| ≤ remBound2 V s := by
  have hσ := abs_pairTilt δ b
  have hvV : |v| ≤ 2 * V := abs_le.mpr hv
  have hs : 0 ≤ s := (abs_nonneg _).trans hδ
  have hexp : Real.exp |pairTilt δ b * v| ≤ Real.exp (s * (2 * V)) := Real.exp_le_exp.mpr (by
    rw [abs_mul, hσ]; exact mul_le_mul hδ hvV (abs_nonneg _) hs)
  have hexp' : Real.exp (pairTilt δ b * v) ≤ Real.exp (s * (2 * V)) :=
    (Real.exp_le_exp.mpr (le_abs_self _)).trans hexp
  refine ⟨(abs_exp_sub_one_le _).trans (by unfold remBound0; linarith), ?_, ?_⟩
  · rw [remProfile1, abs_mul, abs_of_pos (Real.exp_pos _), hσ]
    exact mul_le_mul hδ hexp' (Real.exp_pos _).le hs
  · rw [remProfile2, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, hσ]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hδ 2) hexp' (Real.exp_pos _).le
      (by positivity)

/-- **A pair is its centre plus the depth remainder.** -/
theorem pair_eq_centre_add_rem (p q : ℂ) (δ v : ℝ) :
    p * cexp ((δ : ℂ) * v) + q * cexp (-(δ : ℂ) * v) =
      (p + q) + (p * (remProfile δ true v : ℂ) + q * (remProfile δ false v : ℂ)) := by
  simp only [remProfile, pairTilt, if_true, Bool.false_eq_true, if_false]
  push_cast
  ring

/-! ### The remainder is small -/

/-- The remainder constant `K(V, g, s) = 2(4V E₀² + π²B/(3g²))`, with `B` the off-diagonal
constant of the remainder profiles on `[−2V, 2V]`. -/
def remConst (V g s : ℝ) : ℝ :=
  2 * (4 * V * remBound0 V s ^ 2 + π ^ 2 / 3 *
    offDiagConst (inghamA (2 * V)) (2 * V) (remBound0 V s) (remBound1 V s) (remBound2 V s) /
      g ^ 2)

theorem remBound0_nonneg {V s : ℝ} (hV : 0 ≤ V) (hs : 0 ≤ s) : 0 ≤ remBound0 V s := by
  unfold remBound0
  linarith [Real.one_le_exp (by positivity : 0 ≤ s * (2 * V))]

theorem remConst_nonneg {V g s : ℝ} (hV : 0 < V) (hs : 0 ≤ s) : 0 ≤ remConst V g s := by
  have h0 := remBound0_nonneg hV.le hs
  have ha : 0 < inghamA (2 * V) := by unfold inghamA; positivity
  unfold remConst offDiagConst remBound1 remBound2
  positivity

theorem remConst_zero (V g : ℝ) : remConst V g 0 = 0 := by
  simp [remConst, remBound0, remBound1, remBound2, offDiagConst]

theorem continuous_remConst (V g : ℝ) : Continuous fun s => remConst V g s := by
  unfold remConst offDiagConst remBound0 remBound1 remBound2
  fun_prop

/-- Row sums of `1/x²` over `g`-separated heights. -/
theorem sum_inv_sq_sep_le {ι : Type*} [Fintype ι] [DecidableEq ι] (γ : ι → ℝ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (j : ι) :
    ∑ l ∈ Finset.univ.filter (· ≠ j), 1 / |γ j - γ l| ^ 2 ≤ π ^ 2 / 3 / g ^ 2 := by
  have hbasel := _root_.RHTower.hasSum_inv_add_one_sq
  have hψn : ∀ n : ℕ, 1 / (((n : ℝ) + 1) * g) ^ 2 = 1 / g ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    intro n
    rw [mul_pow]
    field_simp
  have hψs : Summable fun n : ℕ => 1 / (((n : ℝ) + 1) * g) ^ 2 := by
    rw [show (fun n : ℕ => 1 / (((n : ℝ) + 1) * g) ^ 2) =
      fun n : ℕ => 1 / g ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ from funext hψn]
    exact hbasel.summable.mul_left _
  have h := sum_offDiag_le_two_tsum γ hg hsep (ψ := fun x => 1 / x ^ 2)
    (fun x hx => by positivity)
    (fun x y hx hxy => div_le_div_of_nonneg_left zero_le_one (pow_pos (by linarith) 2)
      (pow_le_pow_left₀ (by linarith) hxy 2)) hψs j
  refine h.trans (le_of_eq ?_)
  rw [tsum_congr hψn, tsum_mul_left, hbasel.tsum_eq]
  ring

/-- **The remainder is small.** For `g`-separated heights and depths `≤ s`,
`∫_{−V}^{V} |Σ_k e^{iγ_k v}(p_k(e^{δ_k v} − 1) + q_k(e^{−δ_k v} − 1))|² ≤ K(V, g, s) Σ_k (|p_k| + |q_k|)²`. -/
theorem remainder_upper {ι : Type*} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ) (p q : ι → ℂ)
    {g V s : ℝ} (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s) (hδ : ∀ k, |δ k| ≤ s)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) :
    ∫ v in -V..V, ‖∑ k, cexp (I * γ k * v) *
        (p k * (remProfile (δ k) true v : ℂ) + q k * (remProfile (δ k) false v : ℂ))‖ ^ 2 ≤
      remConst V g s * ∑ k, (‖p k‖ + ‖q k‖) ^ 2 := by
  classical
  have hV2 : 0 < 2 * V := by positivity
  set a := inghamA (2 * V) with ha_def
  have ha : 0 < a := by rw [ha_def]; unfold inghamA; positivity
  have haV : a * (2 * V) = π / 2 := inghamA_mul hV2
  have hE0 := remBound0_nonneg hV.le hs
  have hE1 : 0 ≤ remBound1 V s := by unfold remBound1; positivity
  have hE2 : 0 ≤ remBound2 V s := by unfold remBound2; positivity
  set B := offDiagConst a (2 * V) (remBound0 V s) (remBound1 V s) (remBound2 V s) with hB
  have hB0 : 0 ≤ B := by rw [hB]; unfold offDiagConst; positivity
  set Rr := π ^ 2 / 3 * B / g ^ 2 with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  -- the two remainders of each site
  set c' : ι × Bool → ℂ := fun x => if x.2 then p x.1 else q x.1 with hc'
  set γ' : ι × Bool → ℝ := fun x => γ x.1 with hγ'
  set u : ι × Bool → ℝ → ℝ := fun x => remProfile (δ x.1) x.2 with hu
  have huc : ∀ x, Continuous (u x) := fun x => continuous_remProfile _ _
  set f : ℝ → ℂ := fun v => ∑ x, c' x * (cexp (I * γ' x * v) * (u x v : ℂ)) with hf
  have hF : ∀ v : ℝ, (∑ k, cexp (I * γ k * v) *
      (p k * (remProfile (δ k) true v : ℂ) + q k * (remProfile (δ k) false v : ℂ))) = f v := by
    intro v
    rw [hf, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
    simp only [hc', hγ', hu, if_true, Bool.false_eq_true, if_false]
    ring
  have hfc : Continuous fun v => ‖f v‖ ^ 2 := by
    rw [hf]
    have := huc
    fun_prop
  have hcosc : Continuous fun v : ℝ => Real.cos (a * v) * ‖f v‖ ^ 2 :=
    (by fun_prop : Continuous fun v : ℝ => Real.cos (a * v)).mul hfc
  -- `cos(av) ≥ 1/2` on `[−V, V]`
  have hcos : ∀ v ∈ Icc (-V) V, (1 : ℝ) / 2 ≤ Real.cos (a * v) := by
    intro v hv
    have h1 := Real.one_sub_sq_div_two_le_cos (x := a * v)
    have haV' : a * V = π / 4 := by linear_combination haV / 2
    have hav : |a * v| ≤ π / 4 := by
      rw [abs_mul, abs_of_pos ha, ← haV']
      exact mul_le_mul_of_nonneg_left (abs_le.mpr hv) ha.le
    have hpi : π / 4 ≤ 1 := by linarith [Real.pi_le_four]
    have : (a * v) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (a * v)]
    linarith
  have hstep1 : ∫ v in -V..V, ‖f v‖ ^ 2 ≤ 2 * ∫ v in -V..V, Real.cos (a * v) * ‖f v‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) (hfc.intervalIntegrable _ _)
      ((hcosc.const_mul 2).intervalIntegrable _ _) fun v hv => ?_
    have := hcos v hv
    nlinarith [mul_nonneg (sub_nonneg.mpr this) (sq_nonneg ‖f v‖)]
  have hstep2 : ∫ v in -V..V, Real.cos (a * v) * ‖f v‖ ^ 2 ≤
      ∫ v in -(2 * V)..(2 * V), Real.cos (a * v) * ‖f v‖ ^ 2 := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith) ?_
      (hcosc.intervalIntegrable _ _)
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun v hv => ?_
    rw [Set.uIoc_of_le (by linarith)] at hv
    exact mul_nonneg (cos_mul_nonneg ha.le haV ⟨hv.1.le, hv.2⟩) (by positivity)
  have hQ : ∫ v in -(2 * V)..(2 * V), Real.cos (a * v) * ‖f v‖ ^ 2 =
      (∑ x, ∑ y, c' x * conj (c' y) *
        ∫ v in -(2 * V)..(2 * V), ((Real.cos (a * v) * (u x v * u y v) : ℝ) : ℂ) *
          cexp (I * ((γ' x - γ' y : ℝ) : ℂ) * v)).re :=
    integral_cos_mul_normSq_profileSum γ' u huc c' a (2 * V)
  set J : ι × Bool → ι × Bool → ℂ := fun x y =>
    ∫ v in -(2 * V)..(2 * V), ((Real.cos (a * v) * (u x v * u y v) : ℝ) : ℂ) *
      cexp (I * ((γ' x - γ' y : ℝ) : ℂ) * v) with hJ
  set blk : ι → ι → ℂ := fun k l => ∑ b : Bool, ∑ b' : Bool,
    c' (k, b) * conj (c' (l, b')) * J (k, b) (l, b') with hblk
  have hsplit : (∑ x, ∑ y, c' x * conj (c' y) * J x y) = ∑ k, ∑ l, blk k l := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fintype.sum_prod_type, hblk]
    rw [Finset.sum_comm]
  set w : ι → ℝ := fun k => ‖p k‖ + ‖q k‖ with hw
  have hcw : ∀ k l, ∑ b : Bool, ∑ b' : Bool, ‖c' (k, b)‖ * ‖c' (l, b')‖ = w k * w l := by
    intro k l
    simp only [Fintype.sum_bool, hc', if_true, Bool.false_eq_true, if_false, hw]
    ring
  have hblk_le : ∀ k l (X : ℝ), (∀ b b' : Bool, ‖J (k, b) (l, b')‖ ≤ X) →
      ‖blk k l‖ ≤ w k * w l * X := by
    intro k l X hX
    calc ‖blk k l‖ ≤ ∑ b : Bool, ∑ b' : Bool, ‖c' (k, b)‖ * ‖c' (l, b')‖ * X := by
          simp only [hblk]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (hX b b') (by positivity)
      _ = w k * w l * X := by rw [← hcw, Finset.sum_mul]; simp only [Finset.sum_mul]
  -- the diagonal blocks
  have hdiag : ∀ k, ‖blk k k‖ ≤ w k * w k * (4 * V * remBound0 V s ^ 2) := by
    intro k
    refine hblk_le k k _ fun b b' => ?_
    simp only [hJ, hγ', sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      mul_one]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_).trans
      (le_of_eq ?_)
    · rw [Set.uIoc_of_le (by linarith)] at hv
      have hv' : v ∈ Icc (-(2 * V)) (2 * V) := ⟨hv.1.le, hv.2⟩
      have h1 := (remProfile_bounds (hδ k) hv' b).1
      have h2 := (remProfile_bounds (hδ k) hv' b').1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
      have hc := Real.abs_cos_le_one (a * v)
      calc |Real.cos (a * v)| * (|u (k, b) v| * |u (k, b') v|) ≤
          1 * (remBound0 V s * remBound0 V s) := by
            gcongr
            · exact h1
            · exact h2
        _ = remBound0 V s ^ 2 := by ring
    · rw [show 2 * V - -(2 * V) = 4 * V by ring, abs_of_pos (by linarith)]
      ring
  -- the off-diagonal blocks
  have hoff : ∀ k l, k ≠ l → ‖blk k l‖ ≤ w k * w l * (B / |γ k - γ l| ^ 2) := by
    intro k l hkl
    have hx : γ k - γ l ≠ 0 := by
      intro h0
      have := hsep k l hkl
      rw [h0, abs_zero] at this
      linarith
    refine hblk_le k l _ fun b b' => ?_
    rw [sq_abs]
    simp only [hJ, hu, hγ']
    exact norm_integral_cos_mul_mul_cexp_le hV2.le ha.le haV hx
      (hasDerivAt_remProfile _ _) (hasDerivAt_remProfile1 _ _) (continuous_remProfile2 _ _)
      (hasDerivAt_remProfile _ _) (hasDerivAt_remProfile1 _ _) (continuous_remProfile2 _ _)
      (fun v hv => remProfile_bounds (hδ k) hv b) (fun v hv => remProfile_bounds (hδ l) hv b')
  have hrow : ∀ k, ∑ l ∈ Finset.univ.filter (· ≠ k), B / |γ k - γ l| ^ 2 ≤ Rr := by
    intro k
    have h := sum_inv_sq_sep_le γ hg hsep k
    calc ∑ l ∈ Finset.univ.filter (· ≠ k), B / |γ k - γ l| ^ 2 =
        B * ∑ l ∈ Finset.univ.filter (· ≠ k), 1 / |γ k - γ l| ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ B * (π ^ 2 / 3 / g ^ 2) := mul_le_mul_of_nonneg_left h hB0
      _ = Rr := by rw [hRr]; ring
  have hrowk : ∀ k, (∑ l, blk k l).re ≤ w k * w k * (4 * V * remBound0 V s ^ 2) +
      ∑ l ∈ Finset.univ.filter (· ≠ k), w k * w l * (B / |γ k - γ l| ^ 2) := by
    intro k
    rw [Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ k), Complex.add_re,
      Complex.re_sum]
    refine add_le_add ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (hdiag k)))
      (Finset.sum_le_sum fun l hl => (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
        (hoff k l (Finset.ne_of_mem_erase hl).symm)))
  have hschur := schur_offDiag_le w (fun k l => B / |γ k - γ l| ^ 2)
    (fun k l _ => by positivity) (fun k l => by simp only [abs_sub_comm]) hrow
  have htotal : (∑ k, ∑ l, blk k l).re ≤ (4 * V * remBound0 V s ^ 2 + Rr) * ∑ k, w k ^ 2 := by
    rw [Complex.re_sum]
    refine (Finset.sum_le_sum fun k _ => hrowk k).trans ?_
    rw [Finset.sum_add_distrib]
    have e : ∑ k, w k * w k * (4 * V * remBound0 V s ^ 2) =
        4 * V * remBound0 V s ^ 2 * ∑ k, w k ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, add_mul]
    exact add_le_add le_rfl hschur
  have hint : (∫ v in -V..V, ‖∑ k, cexp (I * γ k * v) *
      (p k * (remProfile (δ k) true v : ℂ) + q k * (remProfile (δ k) false v : ℂ))‖ ^ 2) =
        ∫ v in -V..V, ‖f v‖ ^ 2 := by
    congr 1 with v
    rw [hF v]
  rw [hint]
  calc ∫ v in -V..V, ‖f v‖ ^ 2 ≤ 2 * ∫ v in -(2 * V)..(2 * V), Real.cos (a * v) * ‖f v‖ ^ 2 :=
        hstep1.trans (by linarith)
    _ = 2 * (∑ k, ∑ l, blk k l).re := by
        rw [hQ, show (∑ x, ∑ y, c' x * conj (c' y) *
          ∫ v in -(2 * V)..(2 * V), ((Real.cos (a * v) * (u x v * u y v) : ℝ) : ℂ) *
            cexp (I * ((γ' x - γ' y : ℝ) : ℂ) * v)) = ∑ x, ∑ y, c' x * conj (c' y) * J x y from rfl,
          hsplit]
    _ ≤ 2 * ((4 * V * remBound0 V s ^ 2 + Rr) * ∑ k, w k ^ 2) := by linarith
    _ = remConst V g s * ∑ k, (‖p k‖ + ‖q k‖) ^ 2 := by
        rw [remConst, ← ha_def, ← hB, hRr]
        ring

/-! ### Ingham at the sharp threshold -/

/-- **Ingham's inequality at the sharp threshold.** For `g`-separated real frequencies and
`g > π/V`, `θ Σ|c_j|² ≤ ∫_{−V}^{V} |Σ_j c_j e^{iγ_j v}|²`, `θ` the tilted constant at tilt `0`. -/
theorem ingham_lower {ι : Type*} [Fintype ι] (γ : ι → ℝ) (c : ι → ℂ) {g V : ℝ} (hg : 0 < g)
    (hV : 0 < V) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (hgap : π / V < g) :
    tiltedInghamConst V g 0 * ∑ j, ‖c j‖ ^ 2 ≤
      ∫ v in -V..V, ‖∑ j, c j * cexp (I * γ j * v)‖ ^ 2 := by
  have hgap' : 2 * Real.sqrt ((π / (2 * V)) ^ 2 + 4 * (0 : ℝ) ^ 2) < g := by
    rw [show (π / (2 * V)) ^ 2 + 4 * (0 : ℝ) ^ 2 = (π / (2 * V)) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    calc 2 * (π / (2 * V)) = π / V := by field_simp
      _ < g := hgap
  have h := tilted_ingham_inequality γ (fun _ => 0) c hg hV le_rfl (fun _ => by simp) hsep hgap'
  simpa using h

theorem inghamConst_pos {V g : ℝ} (hV : 0 < V) (hgap : π / V < g) :
    0 < tiltedInghamConst V g 0 := by
  apply tiltedInghamConst_pos hV
  have ha : 0 < π / (2 * V) := by positivity
  rw [show (π / (2 * V)) ^ 2 + 4 * (0 : ℝ) ^ 2 = (π / (2 * V)) ^ 2 by ring, Real.sqrt_sq ha.le,
    mul_zero, zero_mul, Real.cosh_zero, one_mul]
  refine (tsum_two_div_sq_sub_one_lt_one ?_).2
  rw [lt_div_iff₀ ha]
  calc 2 * (π / (2 * V)) = π / V := by field_simp
    _ < g := hgap

/-! ### Vanishing pair sums -/

/-- **Centres of a vanishing pair sum are small.** If a summable pair sum vanishes on `[−V, V]`,
with `g`-separated heights, depths `≤ s` and `g > π/V`, every centre satisfies
`θ |p_k + q_k|² ≤ 2K(V, g, s) Σ_j (|p_j| + |q_j|)²`. -/
theorem inghamConst_mul_normSq_le {κ : Type*} (γ δ : κ → ℝ) (p q : κ → ℂ) {g V s : ℝ}
    (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s) (hδ : ∀ k, |δ k| ≤ s)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (hgap : π / V < g)
    (hsum : Summable fun k => ‖p k‖ + ‖q k‖)
    (hzero : ∀ v ∈ Icc (-V) V, ∑' k, cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)) = 0) (k₀ : κ) :
    tiltedInghamConst V g 0 * ‖p k₀ + q k₀‖ ^ 2 ≤
      2 * remConst V g s * ∑' k, (‖p k‖ + ‖q k‖) ^ 2 := by
  classical
  set w : κ → ℝ := fun k => ‖p k‖ + ‖q k‖ with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by positivity
  have hw2 : Summable fun k => w k ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (hsum.mul_left (∑' j, w j))
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hsum.le_tsum k fun j _ => hw0 j) (hw0 k)
  have hθ0 := (inghamConst_pos hV hgap).le
  have hK0 := remConst_nonneg (g := g) hV hs
  set E := Real.exp (s * V) with hE
  -- the term of a site and its bound
  set T : κ → ℝ → ℂ := fun k v => cexp (I * γ k * v) *
    (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)) with hT
  have hTb : ∀ k, ∀ v ∈ Icc (-V) V, ‖T k v‖ ≤ E * w k := by
    intro k v hv
    have hvV : |v| ≤ V := abs_le.mpr hv
    have hδv : ∀ σ : ℝ, |σ| ≤ s → ‖cexp ((σ : ℂ) * v)‖ ≤ E := fun σ hσ => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul hσ hvV (abs_nonneg _) hs))
    have h1 : ‖cexp (I * γ k * v)‖ = 1 := by
      rw [show I * (γ k : ℂ) * v = ((γ k * v : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hneg : -(δ k : ℂ) * v = ((-δ k : ℝ) : ℂ) * v := by push_cast; ring
    simp only [hT]
    rw [norm_mul, h1, one_mul, hneg]
    calc ‖p k * cexp ((δ k : ℂ) * v) + q k * cexp (((-δ k : ℝ) : ℂ) * v)‖ ≤
        ‖p k‖ * E + ‖q k‖ * E := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul_of_nonneg_left (hδv _ (hδ k)) (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hδv _ (by rw [abs_neg]; exact hδ k)) (norm_nonneg _)
      _ = E * w k := by rw [hw]; ring
  -- the tail of the sum
  set τ : Finset κ → ℝ := fun S => ∑' k : {k // k ∉ S}, w k with hτ
  have hτlim : Tendsto τ atTop (𝓝 0) := tendsto_tsum_compl_atTop_zero w
  have hfin : ∀ S : Finset κ, k₀ ∈ S → tiltedInghamConst V g 0 * ‖p k₀ + q k₀‖ ^ 2 ≤
      2 * remConst V g s * ∑' k, w k ^ 2 + 2 * (2 * V * (E * τ S) ^ 2) := by
    intro S hk₀
    -- the three finite sums
    set M : ℝ → ℂ := fun v => ∑ k : S, (p k + q k) * cexp (I * γ k * v) with hM
    set R : ℝ → ℂ := fun v => ∑ k : S, cexp (I * γ k * v) *
      (p k * (remProfile (δ k) true v : ℂ) + q k * (remProfile (δ k) false v : ℂ)) with hR
    set F : ℝ → ℂ := fun v => ∑ k : S, T k v with hF
    have hMRF : ∀ v, M v = F v - R v := by
      intro v
      simp only [hM, hR, hF, hT]
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pair_eq_centre_add_rem]
      ring
    have hMc : Continuous M := by rw [hM]; fun_prop
    have hRc : Continuous R := by
      rw [hR]
      have : ∀ k : S, ∀ b, Continuous (remProfile (δ k) b) := fun k b => continuous_remProfile _ _
      fun_prop
    have hFc : Continuous F := by rw [hF, hT]; fun_prop
    -- Ingham for the centres
    have hsepS : ∀ j l : S, j ≠ l → g ≤ |γ j - γ l| := fun j l hjl =>
      hsep j l fun h => hjl (Subtype.ext h)
    have hlow := ingham_lower (fun k : S => γ k) (fun k : S => p k + q k) hg hV hsepS hgap
    have hδS : ∀ k : S, |δ k| ≤ s := fun k => hδ k
    have hup := remainder_upper (fun k : S => γ k) (fun k : S => δ k) (fun k : S => p k)
      (fun k : S => q k) hg hV hs hδS hsepS
    -- the truncated pair sum is the negative tail
    have hFb : ∀ v ∈ Icc (-V) V, ‖F v‖ ≤ E * τ S := by
      intro v hv
      have hTs : Summable fun k => T k v :=
        Summable.of_norm_bounded (hsum.mul_left E) fun k => hTb k v hv
      have hsplit := hTs.sum_add_tsum_subtype_compl S
      rw [hzero v hv] at hsplit
      have hFeq : F v = -∑' k : {k // k ∉ S}, T k v := by
        rw [hF, Finset.sum_coe_sort S (fun k => T k v)]
        linear_combination hsplit
      rw [hFeq, norm_neg]
      have hws : Summable fun k : {k // k ∉ S} => w k := hsum.subtype _
      refine (norm_tsum_le_tsum_norm ((hws.mul_left E).of_norm_bounded fun k => ?_)).trans ?_
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hTb k v hv
      · rw [hτ, ← tsum_mul_left]
        exact (Summable.of_norm_bounded (hws.mul_left E) fun k => hTb k v hv).norm.tsum_le_tsum
          (fun k => hTb k v hv) (hws.mul_left E)
    have hFint : ∫ v in -V..V, ‖F v‖ ^ 2 ≤ 2 * V * (E * τ S) ^ 2 := by
      have hτ0 : 0 ≤ τ S := tsum_nonneg fun k => hw0 k
      calc ∫ v in -V..V, ‖F v‖ ^ 2 ≤ ∫ v in -V..V, (E * τ S) ^ 2 :=
            intervalIntegral.integral_mono_on (by linarith)
              ((hFc.norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const fun v hv =>
                pow_le_pow_left₀ (norm_nonneg _) (hFb v hv) 2
        _ = 2 * V * (E * τ S) ^ 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hpt : ∀ v, ‖M v‖ ^ 2 ≤ 2 * ‖R v‖ ^ 2 + 2 * ‖F v‖ ^ 2 := by
      intro v
      rw [hMRF v]
      have h := norm_sub_le (F v) (R v)
      nlinarith [norm_nonneg (F v - R v), norm_nonneg (F v), norm_nonneg (R v),
        sq_nonneg (‖F v‖ - ‖R v‖)]
    have hMint : ∫ v in -V..V, ‖M v‖ ^ 2 ≤
        2 * ∫ v in -V..V, ‖R v‖ ^ 2 + 2 * ∫ v in -V..V, ‖F v‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (((hRc.norm.pow 2).const_mul 2).intervalIntegrable _ _)
          (((hFc.norm.pow 2).const_mul 2).intervalIntegrable _ _)]
      exact intervalIntegral.integral_mono_on (by linarith)
        ((hMc.norm.pow 2).intervalIntegrable _ _)
        ((((hRc.norm.pow 2).const_mul 2).add ((hFc.norm.pow 2).const_mul 2)).intervalIntegrable
          _ _) fun v _ => hpt v
    have hsumS : ∑ k : S, (‖p k‖ + ‖q k‖) ^ 2 ≤ ∑' k, w k ^ 2 := by
      rw [Finset.sum_coe_sort S (fun k => (‖p k‖ + ‖q k‖) ^ 2)]
      exact hw2.sum_le_tsum S fun k _ => sq_nonneg _
    have hk : ‖p k₀ + q k₀‖ ^ 2 ≤ ∑ k : S, ‖p k + q k‖ ^ 2 := by
      rw [Finset.sum_coe_sort S (fun k => ‖p k + q k‖ ^ 2)]
      exact Finset.single_le_sum (f := fun k => ‖p k + q k‖ ^ 2) (fun _ _ => by positivity) hk₀
    calc tiltedInghamConst V g 0 * ‖p k₀ + q k₀‖ ^ 2 ≤
        tiltedInghamConst V g 0 * ∑ k : S, ‖p k + q k‖ ^ 2 := mul_le_mul_of_nonneg_left hk hθ0
      _ ≤ ∫ v in -V..V, ‖M v‖ ^ 2 := hlow
      _ ≤ 2 * ∫ v in -V..V, ‖R v‖ ^ 2 + 2 * ∫ v in -V..V, ‖F v‖ ^ 2 := hMint
      _ ≤ 2 * (remConst V g s * ∑' k, w k ^ 2) + 2 * (2 * V * (E * τ S) ^ 2) := by
          gcongr
          exact hup.trans (mul_le_mul_of_nonneg_left hsumS hK0)
      _ = 2 * remConst V g s * ∑' k, w k ^ 2 + 2 * (2 * V * (E * τ S) ^ 2) := by ring
  have hlim : Tendsto (fun S => 2 * remConst V g s * ∑' k, w k ^ 2 +
      2 * (2 * V * (E * τ S) ^ 2)) atTop (𝓝 (2 * remConst V g s * ∑' k, w k ^ 2)) := by
    have h := ((((hτlim.const_mul E).pow 2).const_mul (2 * V)).const_mul 2).const_add
      (2 * remConst V g s * ∑' k, w k ^ 2)
    simpa using h
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨{k₀}, fun S hS =>
    hfin S (hS (Finset.mem_singleton_self k₀))⟩)

end GaloisForLFunctions.ZeroConfigurationGeometry
