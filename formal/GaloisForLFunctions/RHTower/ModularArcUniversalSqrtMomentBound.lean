import GaloisForLFunctions.RHTower.ModularArcArbitraryOrderInversionDuality

/-!
# Universal scale-invariant square-root frequency bounds and `1 / (2 cosh(log m))` sublattice cancellation

In `ModularArcAtomicSubharmonicAsymptotics`, we proved the dilation-invariant Basset–Whittaker bound
`|e^{−w/2} ∫ arcLineDeriv ν t · sin(c e^w t) dt| ≤ 2 √(π/2) · ν.real univ · √c` for all `c > 0` and
`w ∈ ℝ`.

In this module we prove that this **universal `O(√c)` frequency scaling law is preserved across the
entire hyperbolic dilation-filter tower** with constants **completely independent of the dilation
scale `k` (or `m`)**, and that when `hyperbolicFilterDeriv m` is applied to an `N`-sublattice-blind
function, the `m` prefactor in the backward term and the `1/m = √(1/m²)` factor from the `O(√c)`
frequency bound **cancel identically**, leaving a `1 / (2 cosh(log m)) ≤ 1/m` suppression factor
along the entire `N`-sublattice:

1. **Universal `L¹` weight bound (`atomMass_le_four`) and scale-independent `O(√c)` atomic bound
   (`abs_integral_arcLineAtomicDeriv_mul_sin_le_sqrt`):**
   For every `b ∈ ℝ`, `atomMass b ≤ 4`, and for every `c > 0`,
   `|∫ arcLineAtomicDeriv b ν x · sin(c x) dx| ≤ 8 √(π/2) · ν.real univ · √c`
   (completely independent of `b`).
2. **Scale-invariant `O(√c)` preservation under `hyperbolicFilterDeriv m`
   (`abs_integral_hyperbolicFilterDeriv_mul_sin_le_sqrt`):**
   If `|∫ f'(t) sin(ω t) dt| ≤ K √ω` for all `ω > 0`, then for every integer `m ≥ 1` and every
   `c > 0`, the forward scale `m⁻¹ √(c m²) = √c` and backward scale `m √(c / m²) = √c` both match
   `√c` identically, so
   `|∫ hyperbolicFilterDeriv m f' x · sin(c x) dx| ≤ (2 K) √c` (independent of `m`).
3. **Scale-independent `O(√c)` bound at arbitrary tower depth `d`
   (`abs_integral_arcLineTowerDeriv_mul_sin_le_sqrt`):**
   For every `k ≥ 1`, `d ∈ ℕ`, and `c > 0`,
   `|∫ arcLineTowerDeriv k d ν x · sin(c x) dx| ≤ 2^d · (8 √(π/2) · ν.real univ) · √c`.
4. **Exact `N`-sublattice isolation and `1 / (2 cosh(log m))` cancellation
   (`integral_hyperbolicFilterDeriv_mul_sin_of_sublattice_blind`,
   `abs_integral_hyperbolicFilterDeriv_mul_sin_of_sublattice_blind_le`):**
   If `f'` is blind on the `N`-sublattice and `|∫ f'(t) sin(ω t) dt| ≤ K √ω`, then for every
   integer `m ≥ 1` and every `j ∈ ℕ`, along `c = arcFreq (N(j+1) − 1)` both the central and
   forward terms of `hyperbolicFilterDeriv m f'` vanish, and the `m` in `m / (2 cosh(log m))`
   cancels the `1/m` in `√(c / m²) = √c / m`, yielding
   `|∫ hyperbolicFilterDeriv m f' x · sin(arcFreq (N(j+1) − 1) x) dx|`
   `≤ K √(arcFreq (N(j+1) − 1)) / (2 cosh(log m))`,
   which vanishes at rate `O(1/m)` as `m → ∞`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Universal `atomMass b ≤ 4` bound and scale-independent `O(√c)` atomic sine moment bound -/

/-- For every `b ∈ ℝ`, the total `L¹` weight `atomMass b = Σ_{j=0}^4 |atomWeight b j|` is at most `4`. -/
theorem atomMass_le_four (b : ℝ) : atomMass b ≤ 4 := by
  have hC1 : 1 ≤ Real.cosh (b / 2) := Real.one_le_cosh (b / 2)
  have hCpos : 0 < Real.cosh (b / 2) := Real.cosh_pos (b / 2)
  have hCsq : 1 ≤ Real.cosh (b / 2) ^ 2 := by nlinarith
  have hw0_pos : 0 ≤ atomW0 b := by unfold atomW0; positivity
  have hw0_le : atomW0 b ≤ 3 / 2 := by
    unfold atomW0
    have : 1 / (2 * Real.cosh (b / 2) ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) zero_lt_two]
      linarith
    linarith
  have hw1_abs : |atomW1 b| ≤ 1 := by
    unfold atomW1
    rw [abs_neg, abs_of_pos (by positivity)]
    exact div_le_one_of_le₀ hC1 hCpos.le
  have hw2_pos : 0 ≤ atomW2 b := by unfold atomW2; positivity
  have hw2_le : atomW2 b ≤ 1 / 4 := by
    unfold atomW2
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    linarith
  unfold atomMass
  simp only [Fin.sum_univ_five, atomWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  rw [abs_of_nonneg hw0_pos, abs_of_nonneg hw2_pos]
  linarith

/-- **Scale-independent `O(√c)` bound for `arcLineAtomicDeriv b ν` at all real frequencies `c > 0`.** -/
theorem abs_integral_arcLineAtomicDeriv_mul_sin_le_sqrt (b : ℝ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    |∫ x, arcLineAtomicDeriv b ν x * Real.sin (c * x)| ≤
      8 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c := by
  rw [integral_arcLineAtomicDeriv_mul_sin]
  set B := 2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c
  have hB0 : 0 ≤ B := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  have hsum : |∑ j, atomWeight b j * (Real.exp (-(atomShift b j / 2)) *
      ∫ t, arcLineDeriv ν t * Real.sin (c * Real.exp (atomShift b j) * t))| ≤
      atomMass b * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [atomMass, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_exp_mul_integral_arcLineDeriv_mul_sin_le ν hc (atomShift b j)) (abs_nonneg _)
  calc |∑ j, atomWeight b j * (Real.exp (-(atomShift b j / 2)) *
        ∫ t, arcLineDeriv ν t * Real.sin (c * Real.exp (atomShift b j) * t))|
      ≤ atomMass b * B := hsum
    _ ≤ 4 * B := mul_le_mul_of_nonneg_right (atomMass_le_four b) hB0
    _ = 8 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c := by dsimp [B]; ring

/-! ### General sine moment formula and `O(√c)` preservation for `hyperbolicFilterDeriv` -/

/-- **General sine moment decomposition for `hyperbolicFilterDeriv m f'` at any frequency `c ∈ ℝ`.** -/
theorem integral_hyperbolicFilterDeriv_mul_sin {m : ℕ} (hm : 1 ≤ m) {f' : ℝ → ℝ}
    (hf' : Integrable f') (c : ℝ) :
    ∫ x, hyperbolicFilterDeriv m f' x * Real.sin (c * x) =
      (∫ x, f' x * Real.sin (c * x)) -
        (1 / (2 * Real.cosh (Real.log m))) *
          ((m : ℝ)⁻¹ * (∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)) +
            (m : ℝ) * (∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t))) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have h0_int : Integrable fun x => f' x * Real.sin (c * x) :=
    hf'.mul_bdd (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h1_int : Integrable fun x =>
      ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x) :=
    ((hf'.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hmne))).const_mul (((m : ℝ) ^ 3)⁻¹)).mul_bdd
      (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h2_int : Integrable fun x =>
      (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x) :=
    ((hf'.comp_mul_left' (pow_ne_zero 2 hmne)).const_mul ((m : ℝ) ^ 3)).mul_bdd
      (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h01_int : Integrable fun x =>
      f' x * Real.sin (c * x) -
        (1 / (2 * Real.cosh (Real.log m))) *
          (((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) :=
    h0_int.sub (h1_int.const_mul _)
  have h1_eq : ∫ x, ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x) =
      (m : ℝ)⁻¹ * (∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)) := by
    have e : (fun x => ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) =
        fun x => ((m : ℝ) ^ 3)⁻¹ * (f' (x * ((m : ℝ) ^ 2)⁻¹) *
          Real.sin ((c * (m : ℝ) ^ 2) * (x * ((m : ℝ) ^ 2)⁻¹))) := by
      funext x
      have hx : (c * (m : ℝ) ^ 2) * (x * ((m : ℝ) ^ 2)⁻¹) = c * x := by field_simp
      rw [hx]; ring
    rw [e, integral_const_mul, Measure.integral_comp_mul_right
      (fun t => f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)) (((m : ℝ) ^ 2)⁻¹),
      smul_eq_mul, abs_of_pos (by positivity)]
    field_simp
  have h2_eq : ∫ x, (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x) =
      (m : ℝ) * (∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t)) := by
    have e : (fun x => (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x)) =
        fun x => (m : ℝ) ^ 3 * (f' ((m : ℝ) ^ 2 * x) *
          Real.sin ((c / (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 * x))) := by
      funext x
      have hx : (c / (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 * x) = c * x := by field_simp
      rw [hx]; ring
    rw [e, integral_const_mul, Measure.integral_comp_mul_left
      (fun t => f' t * Real.sin ((c / (m : ℝ) ^ 2) * t)) ((m : ℝ) ^ 2),
      smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hmpos 2))]
    field_simp
  have e : (fun x => hyperbolicFilterDeriv m f' x * Real.sin (c * x)) = fun x =>
      f' x * Real.sin (c * x) -
        (1 / (2 * Real.cosh (Real.log m))) *
          (((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) -
        (1 / (2 * Real.cosh (Real.log m))) *
          ((m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x)) := by
    funext x; unfold hyperbolicFilterDeriv; ring
  rw [e, integral_sub h01_int (h2_int.const_mul _),
    integral_sub h0_int (h1_int.const_mul _),
    integral_const_mul, integral_const_mul, h1_eq, h2_eq]
  ring

/-- **Scale-invariant `O(√c)` preservation under `hyperbolicFilterDeriv m`:**
if `|∫ f'(t) sin(ω t) dt| ≤ K √ω` for all `ω > 0`, then for every integer `m ≥ 1` and `c > 0`,
`|∫ hyperbolicFilterDeriv m f' x · sin(c x) dx| ≤ (2 K) √c` (with constant independent of `m`). -/
theorem abs_integral_hyperbolicFilterDeriv_mul_sin_le_sqrt
    {m : ℕ} (hm : 1 ≤ m) {f' : ℝ → ℝ} (hf' : Integrable f')
    {K : ℝ}
    (hbound : ∀ ω : ℝ, 0 < ω → |∫ t, f' t * Real.sin (ω * t)| ≤ K * Real.sqrt ω)
    {c : ℝ} (hc : 0 < c) :
    |∫ x, hyperbolicFilterDeriv m f' x * Real.sin (c * x)| ≤ (2 * K) * Real.sqrt c := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  rw [integral_hyperbolicFilterDeriv_mul_sin hm hf' c]
  have h0 := hbound c hc
  have h1 : |(m : ℝ)⁻¹ * (∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t))| ≤ K * Real.sqrt c := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hmpos)]
    have hb1 := hbound (c * (m : ℝ) ^ 2) (by positivity)
    have hsqrt1 : Real.sqrt (c * (m : ℝ) ^ 2) = Real.sqrt c * (m : ℝ) := by
      rw [Real.sqrt_mul hc.le, Real.sqrt_sq hmpos.le]
    rw [hsqrt1] at hb1
    calc (m : ℝ)⁻¹ * |∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)|
        ≤ (m : ℝ)⁻¹ * (K * (Real.sqrt c * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hb1 (inv_nonneg.mpr hmpos.le)
      _ = K * Real.sqrt c := by field_simp
  have h2 : |(m : ℝ) * (∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t))| ≤ K * Real.sqrt c := by
    rw [abs_mul, abs_of_pos hmpos]
    have hb2 := hbound (c / (m : ℝ) ^ 2) (by positivity)
    have hsqrt2 : Real.sqrt (c / (m : ℝ) ^ 2) = Real.sqrt c / (m : ℝ) := by
      rw [Real.sqrt_div hc.le, Real.sqrt_sq hmpos.le]
    rw [hsqrt2] at hb2
    calc (m : ℝ) * |∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t)|
        ≤ (m : ℝ) * (K * (Real.sqrt c / (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hb2 hmpos.le
      _ = K * Real.sqrt c := by field_simp
  have hcosh : 1 / (2 * Real.cosh (Real.log m)) ≤ 1 / 2 := by
    have := Real.one_le_cosh (Real.log m)
    rw [div_le_div_iff₀ (by positivity) zero_lt_two]
    linarith
  have hsum : |(1 / (2 * Real.cosh (Real.log m))) *
      ((m : ℝ)⁻¹ * (∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)) +
        (m : ℝ) * (∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t)))| ≤ K * Real.sqrt c := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have habs := (abs_add_le
      ((m : ℝ)⁻¹ * (∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)))
      ((m : ℝ) * (∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t)))).trans (add_le_add h1 h2)
    calc 1 / (2 * Real.cosh (Real.log m)) *
          |(m : ℝ)⁻¹ * (∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)) +
            (m : ℝ) * (∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t))|
        ≤ (1 / 2) * (K * Real.sqrt c + K * Real.sqrt c) :=
          mul_le_mul hcosh habs (abs_nonneg _) (by positivity)
      _ = K * Real.sqrt c := by ring
  linarith [abs_sub (∫ x, f' x * Real.sin (c * x))
    ((1 / (2 * Real.cosh (Real.log m))) *
      ((m : ℝ)⁻¹ * (∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t)) +
        (m : ℝ) * (∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t))))]

/-- **Scale-independent `O(√c)` frequency bound at arbitrary tower depth `d ∈ ℕ`.**
For every `k ≥ 1`, `d ∈ ℕ`, and `c > 0`, `|∫ arcLineTowerDeriv k d ν x · sin(c x) dx|` is bounded
by `2^d · (8 √(π/2) · ν.real univ) · √c`, completely independent of `k`. -/
theorem abs_integral_arcLineTowerDeriv_mul_sin_le_sqrt
    {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    ∀ {c : ℝ}, 0 < c →
      |∫ x, arcLineTowerDeriv k d ν x * Real.sin (c * x)| ≤
        2 ^ d * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt c := by
  induction d with
  | zero =>
    intro c hc
    simpa [arcLineTowerDeriv] using
      abs_integral_arcLineAtomicDeriv_mul_sin_le_sqrt (Real.log k) ν hc
  | succ d ih =>
    intro c hc
    have hstep := abs_integral_hyperbolicFilterDeriv_mul_sin_le_sqrt hk
      (integrable_arcLineTowerDeriv hk d ν) (fun _ hω => ih hω) hc
    calc |∫ x, arcLineTowerDeriv k (d + 1) ν x * Real.sin (c * x)|
        ≤ (2 * (2 ^ d * (8 * Real.sqrt (Real.pi / 2) * ν.real univ))) * Real.sqrt c := hstep
      _ = 2 ^ (d + 1) * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt c := by
          rw [pow_succ']; ring

/-! ### Exact `N`-sublattice isolation and `1 / (2 cosh(log m))` cancellation law -/

/-- **Exact `N`-sublattice backward isolation for `hyperbolicFilterDeriv m` at ANY integer scale `m ≥ 1`:**
If `f'` is blind on the `N`-sublattice (`arcFreq (N(j+1) − 1)`), then for **every** integer `m ≥ 1`
(without any divisibility condition between `m` and `N`), both the central term `f'(x)` and the
forward-dilated term `m⁻³ f'(x / m²)` vanish identically along the `N`-sublattice, isolating the
backward-dilated term `−(m / (2 cosh(log m))) ∫ f'(t) sin((arcFreq (N(j+1) − 1) / m²) t) dt`. -/
theorem integral_hyperbolicFilterDeriv_mul_sin_of_sublattice_blind
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) {f' : ℝ → ℝ} (hf' : Integrable f')
    (hblind : ∀ j : ℕ, ∫ x, f' x * Real.sin (arcFreq (N * (j + 1) - 1) * x) = 0)
    (j : ℕ) :
    ∫ x, hyperbolicFilterDeriv m f' x *
        Real.sin (arcFreq (N * (j + 1) - 1) * x) =
      -((m : ℝ) / (2 * Real.cosh (Real.log m))) *
        ∫ t, f' t * Real.sin ((arcFreq (N * (j + 1) - 1) / (m : ℝ) ^ 2) * t) := by
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m hm
  set c := arcFreq (N * (j + 1) - 1)
  rw [integral_hyperbolicFilterDeriv_mul_sin hm hf' c, hblind j]
  have hf_zero : ∫ t, f' t * Real.sin ((c * (m : ℝ) ^ 2) * t) = 0 := by
    have h1 : 1 ≤ m ^ 2 * (j + 1) := Nat.mul_pos hm2 (Nat.succ_pos j)
    have h2 : 1 ≤ N * (j + 1) := Nat.mul_pos hN (Nat.succ_pos j)
    have heq : (N * (j + 1) - 1 + 1) * m ^ 2 - 1 =
        N * ((m ^ 2 * (j + 1) - 1) + 1) - 1 := by
      rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
      ring_nf
    have hfreq : c * (m : ℝ) ^ 2 = arcFreq (N * ((m ^ 2 * (j + 1) - 1) + 1) - 1) := by
      change arcFreq (N * (j + 1) - 1) * (m : ℝ) ^ 2 = _
      rw [← heq, ← arcFreq_mul_nat hm2 (N * (j + 1) - 1)]
      push_cast; ring
    rw [hfreq]
    exact hblind (m ^ 2 * (j + 1) - 1)
  rw [hf_zero, mul_zero, zero_add]
  ring

/-- **The `1 / (2 cosh(log m))` Cancellation Law on the `N`-sublattice:**
If `f'` is blind on the `N`-sublattice and satisfies the universal square-root bound
`|∫ f'(t) sin(ω t) dt| ≤ K √ω`, then for every integer `m ≥ 1` and every `j ∈ ℕ`, the `m` in
`m / (2 cosh(log m))` and the `1/m = √(1/m²)` in `√(arcFreq (N(j+1) − 1) / m²)` cancel
identically, yielding the `O(1/m)` decay bound
`|∫ hyperbolicFilterDeriv m f' x · sin(arcFreq (N(j+1) − 1) x) dx|`
`≤ K √(arcFreq (N(j+1) − 1)) / (2 cosh(log m))`. -/
theorem abs_integral_hyperbolicFilterDeriv_mul_sin_of_sublattice_blind_le
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) {f' : ℝ → ℝ} (hf' : Integrable f')
    (hblind : ∀ j : ℕ, ∫ x, f' x * Real.sin (arcFreq (N * (j + 1) - 1) * x) = 0)
    {K : ℝ}
    (hbound : ∀ ω : ℝ, 0 < ω → |∫ t, f' t * Real.sin (ω * t)| ≤ K * Real.sqrt ω)
    (j : ℕ) :
    |∫ x, hyperbolicFilterDeriv m f' x *
        Real.sin (arcFreq (N * (j + 1) - 1) * x)| ≤
      K * Real.sqrt (arcFreq (N * (j + 1) - 1)) / (2 * Real.cosh (Real.log m)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  set c := arcFreq (N * (j + 1) - 1)
  have hc : 0 < c := arcFreq_pos _
  rw [integral_hyperbolicFilterDeriv_mul_sin_of_sublattice_blind hm hN hf' hblind j,
    abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hb := hbound (c / (m : ℝ) ^ 2) (by positivity)
  have hsqrt : Real.sqrt (c / (m : ℝ) ^ 2) = Real.sqrt c / (m : ℝ) := by
    rw [Real.sqrt_div hc.le, Real.sqrt_sq hmpos.le]
  rw [hsqrt] at hb
  calc (m : ℝ) / (2 * Real.cosh (Real.log m)) *
        |∫ t, f' t * Real.sin ((c / (m : ℝ) ^ 2) * t)|
      ≤ (m : ℝ) / (2 * Real.cosh (Real.log m)) * (K * (Real.sqrt c / (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = K * Real.sqrt c / (2 * Real.cosh (Real.log m)) := by field_simp

/-- **Application to `arcLineTowerDeriv k d ν`:**
Applying `hyperbolicFilterDeriv m` (`m ≥ 1`) to level `d` of the tower suppresses all moments
on the `k^{2(d+1)}`-sublattice by `1 / (2 cosh(log m)) ≤ 1/m` while annihilating the
`(m² k^{2(d+1)})`-sublattice identically. -/
theorem abs_integral_hyperbolicFilterDeriv_arcLineTowerDeriv_mul_sin_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (d j : ℕ) :
    |∫ x, hyperbolicFilterDeriv m (arcLineTowerDeriv k d ν) x *
        Real.sin (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1) * x)| ≤
      2 ^ d * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) *
        Real.sqrt (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1)) /
        (2 * Real.cosh (Real.log m)) :=
  abs_integral_hyperbolicFilterDeriv_mul_sin_of_sublattice_blind_le
    hm (Nat.one_le_pow (2 * (d + 1)) k hk)
    (integrable_arcLineTowerDeriv hk d ν)
    (integral_arcLineTowerDeriv_mul_sin_sublattice_eq_zero hblind hk d)
    (fun _ hω => abs_integral_arcLineTowerDeriv_mul_sin_le_sqrt hk d ν hω) j

/-- **Asymptotic `O(1/m)` vanishing as `m → ∞` along the `k^{2(d+1)}`-sublattice.** -/
theorem tendsto_integral_hyperbolicFilterDeriv_arcLineTowerDeriv_mul_sin_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d j : ℕ) :
    Tendsto (fun m : ℕ =>
      ∫ x, hyperbolicFilterDeriv m (arcLineTowerDeriv k d ν) x *
        Real.sin (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1) * x))
      atTop (𝓝 0) := by
  set C := 2 ^ d * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) *
    Real.sqrt (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1)) / 2
  have hbound : Tendsto (fun m : ℕ => C * (1 / Real.cosh (Real.log m))) atTop (𝓝 0) := by
    simpa using tendsto_inv_cosh_log_atTop.const_mul C
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs]
  have h := abs_integral_hyperbolicFilterDeriv_arcLineTowerDeriv_mul_sin_le hblind hk hm d j
  calc |∫ x, hyperbolicFilterDeriv m (arcLineTowerDeriv k d ν) x *
        Real.sin (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1) * x)|
      ≤ 2 ^ d * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) *
          Real.sqrt (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1)) /
          (2 * Real.cosh (Real.log m)) := h
    _ = C * (1 / Real.cosh (Real.log m)) := by dsimp [C]; ring

end

end RHTower
