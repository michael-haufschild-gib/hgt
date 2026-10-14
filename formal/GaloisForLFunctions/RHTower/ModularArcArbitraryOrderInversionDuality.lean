import GaloisForLFunctions.RHTower.ModularArcTowerCascadeAsymptotics

/-!
# Arbitrary-order Mellin inversion duality, forward-backward spectral isolation, and `k^{4(d+1)}`-sublattice blindness

In `ModularArcArbitraryOrderAllIntegerBlindTower`, we constructed the forward `D_{2(d+1) log k}`-dilated
modular arc tower `arcLineForwardTowerVector k d ν`, which is simultaneously blind at **every**
positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`) while vanishing to arbitrary order
`O((1/2 − l)^{d+1})` at the critical strip edge `l → (1/2)⁻`.

In this module we construct its **Mellin-inversion dual** (`arcLineBackwardTowerVector k d ν`) and
their **self-reciprocal symmetrization** (`arcLineSymTowerVector k d ν`) at every tower depth
`d ∈ ℕ`, establishing:

1. **Exact Mellin inversion duality at depth `d` (`arcLineForwardTowerVector_inv_eq_backward`,
   `arcLineBackwardTowerVector_inv_eq_forward`):**
   For every `x ≠ 0`, `arcLineForwardTowerVector k d ν (1/x) = |x| · arcLineBackwardTowerVector k d ν x`
   and vice versa, so `arcLineSymTowerVector k d ν` is strictly self-reciprocal
   (`S(1/x) = |x| S(x)`, `arcLineSymTowerVector_inv`).
2. **Exact Forward-Backward Spectral Isolation Law at all positive integers
   (`integral_arcLineSymTowerDeriv_mul_sin_eq_half_backward`):**
   Because the forward component `arcLineForwardTowerDeriv k d ν` vanishes identically at **every**
   positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`), the sine moment of the
   self-reciprocal witness `arcLineSymTowerDeriv k d ν` at every `arcFreq n` isolates purely the
   backward sub-harmonic component `(k^{d+1} / 2) ∫ arcLineTowerDeriv k d ν t · sin((arcFreq n / k^{2(d+1)}) t)`.
3. **Exact `k^{4(d+1)}`-sublattice blindness (`integral_arcLineSymTowerDeriv_mul_sin_double_sublattice_eq_zero`):**
   Along `arcFreq (k^{4(d+1)}(m+1) − 1)`, rescaling by `k^{−2(d+1)}` lands on the `k^{2(d+1)}`-blind
   sublattice of `arcLineTowerDeriv k d ν`, so both `arcLineBackwardTowerDeriv k d ν` and
   `arcLineSymTowerDeriv k d ν` vanish identically.
4. **Arbitrary-order `O((1/2 − l)^{d+1})` strip-edge vanishing for `arcLineSymTowerProfile`
   (`abs_integral_exp_mul_arcLineSymTowerProfile_le`,
   `tendsto_div_pow_integral_exp_mul_arcLineSymTowerProfile_nhdsWithin`):**
   The strip Laplace/Mellin transform of `arcLineSymTowerProfile k d ν` factors as
   `cosh(2(d+1) l log k) · ∫ e^{lv} arcLineTowerProfile k d ν v`, preserving order-`(d+1)`
   strip-edge vanishing across `l ∈ [0, 1/2)`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### The backward `2(d+1) log k`-dilated tower `arcLineBackwardTowerVector` -/

/-- Level `d` of the backward `2(d+1) log k`-dilated modular arc tower:
`B_{k,d,ν}(x) = k^{d+1} · arcLineTowerVector k d ν (k^{2(d+1)} x)`. -/
def arcLineBackwardTowerVector (k d : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (k : ℝ) ^ (d + 1) * arcLineTowerVector k d ν ((k : ℝ) ^ (2 * (d + 1)) * x)

/-- Its derivative `B_{k,d,ν}'(x) = k^{3(d+1)} · arcLineTowerDeriv k d ν (k^{2(d+1)} x)`. -/
def arcLineBackwardTowerDeriv (k d : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (k : ℝ) ^ (3 * (d + 1)) * arcLineTowerDeriv k d ν ((k : ℝ) ^ (2 * (d + 1)) * x)

/-- Its log-scale profile `arcLineTowerProfile k d ν (v + 2(d+1) log k)`. -/
def arcLineBackwardTowerProfile (k d : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  arcLineTowerProfile k d ν (v + ((2 * (d + 1) : ℕ) : ℝ) * Real.log k)

theorem hasDerivAt_arcLineBackwardTowerVector (k d : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineBackwardTowerVector k d ν) (arcLineBackwardTowerDeriv k d ν x) x := by
  have hc : HasDerivAt (fun x' : ℝ => (k : ℝ) ^ (2 * (d + 1)) * x')
      ((k : ℝ) ^ (2 * (d + 1))) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) ^ (2 * (d + 1)))
  have h := ((hasDerivAt_arcLineTowerVector k d ν
    ((k : ℝ) ^ (2 * (d + 1)) * x)).comp x hc).const_mul ((k : ℝ) ^ (d + 1))
  refine h.congr_deriv ?_
  unfold arcLineBackwardTowerDeriv
  have hpow : (k : ℝ) ^ (3 * (d + 1)) = (k : ℝ) ^ (d + 1) * (k : ℝ) ^ (2 * (d + 1)) := by
    rw [show 3 * (d + 1) = (d + 1) + 2 * (d + 1) by ring, pow_add]
  rw [hpow]
  ring

theorem arcLineBackwardTowerVector_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineBackwardTowerVector k d ν (-x) = arcLineBackwardTowerVector k d ν x := by
  unfold arcLineBackwardTowerVector
  rw [mul_neg, arcLineTowerVector_neg_of_map_arcNeg k d hν]

theorem arcLineBackwardTowerDeriv_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineBackwardTowerDeriv k d ν (-x) = -arcLineBackwardTowerDeriv k d ν x := by
  unfold arcLineBackwardTowerDeriv
  rw [mul_neg, arcLineTowerDeriv_neg_of_map_arcNeg k d hν, mul_neg]

/-! ### Exact Mellin inversion duality between forward and backward towers -/

/-- **Forward-to-backward Mellin inversion duality at depth `d`:**
for `x ≠ 0`, `arcLineForwardTowerVector k d ν (1/x) = |x| · arcLineBackwardTowerVector k d ν x`. -/
theorem arcLineForwardTowerVector_inv_eq_backward {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcLineForwardTowerVector k d ν (1 / x) =
      |x| * arcLineBackwardTowerVector k d ν x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hy : (k : ℝ) ^ (2 * (d + 1)) * x ≠ 0 :=
    mul_ne_zero (pow_ne_zero (2 * (d + 1)) hkne) hx
  unfold arcLineForwardTowerVector arcLineBackwardTowerVector
  have e : 1 / x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹ = 1 / ((k : ℝ) ^ (2 * (d + 1)) * x) := by
    field_simp
  have hpow : (k : ℝ) ^ (2 * (d + 1)) = (k : ℝ) ^ (d + 1) * (k : ℝ) ^ (d + 1) := by
    rw [show 2 * (d + 1) = (d + 1) + (d + 1) by ring, pow_add]
  rw [e, arcLineTowerVector_inv hk d ν _ hy, abs_mul,
    abs_of_pos (pow_pos hkpos (2 * (d + 1))), hpow]
  field_simp

/-- **Backward-to-forward Mellin inversion duality at depth `d`:**
for `x ≠ 0`, `arcLineBackwardTowerVector k d ν (1/x) = |x| · arcLineForwardTowerVector k d ν x`. -/
theorem arcLineBackwardTowerVector_inv_eq_forward {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcLineBackwardTowerVector k d ν (1 / x) =
      |x| * arcLineForwardTowerVector k d ν x := by
  have h := arcLineForwardTowerVector_inv_eq_backward hk d ν (one_div_ne_zero hx)
  rw [one_div_one_div, abs_one_div] at h
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  calc arcLineBackwardTowerVector k d ν (1 / x)
      = |x| * (|x|⁻¹ * arcLineBackwardTowerVector k d ν (1 / x)) := by
        rw [← mul_assoc, mul_inv_cancel₀ habs, one_mul]
    _ = |x| * arcLineForwardTowerVector k d ν x := by
        rw [← one_div, ← h]

theorem exp_half_mul_arcLineBackwardTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineBackwardTowerVector k d ν (Real.exp v) =
      arcLineBackwardTowerProfile k d ν v := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  unfold arcLineBackwardTowerVector arcLineBackwardTowerProfile
  have he2 : (k : ℝ) ^ (2 * (d + 1)) =
      Real.exp (((2 * (d + 1) : ℕ) : ℝ) * Real.log k) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
  have he1 : (k : ℝ) ^ (d + 1) =
      Real.exp (((d + 1 : ℕ) : ℝ) * Real.log k) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
  have e1 : (k : ℝ) ^ (2 * (d + 1)) * Real.exp v =
      Real.exp (v + ((2 * (d + 1) : ℕ) : ℝ) * Real.log k) := by
    rw [he2, ← Real.exp_add, add_comm]
  have e2 : Real.exp (v / 2) * (k : ℝ) ^ (d + 1) =
      Real.exp ((v + ((2 * (d + 1) : ℕ) : ℝ) * Real.log k) / 2) := by
    rw [he1, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [e1, ← mul_assoc, e2, exp_half_mul_arcLineTowerVector hk d ν]

theorem abs_arcLineBackwardTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineBackwardTowerProfile k d ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d *
        (k : ℝ) ^ (3 * (d + 1)) * Real.exp (-(3 * |v| / 2)) := by
  have e : arcLineBackwardTowerProfile k d ν v = arcLineForwardTowerProfile k d ν (-v) := by
    unfold arcLineBackwardTowerProfile arcLineForwardTowerProfile
    rw [← arcLineTowerProfile_neg k d ν]
    congr 1
    ring
  rw [e]
  simpa [abs_neg] using abs_arcLineForwardTowerProfile_le hk d hν (-v)

theorem integrable_arcLineBackwardTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineBackwardTowerVector k d ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineTowerVector hk d hν).comp_mul_left'
    (pow_ne_zero (2 * (d + 1)) hkpos.ne')).const_mul ((k : ℝ) ^ (d + 1))

theorem integrable_arcLineBackwardTowerDeriv {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineBackwardTowerDeriv k d ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineTowerDeriv hk d ν).comp_mul_left'
    (pow_ne_zero (2 * (d + 1)) hkpos.ne')).const_mul ((k : ℝ) ^ (3 * (d + 1)))

theorem integral_arcLineBackwardTowerVector_eq_zero {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineBackwardTowerVector k d ν x = 0 := by
  unfold arcLineBackwardTowerVector
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (arcLineTowerVector k d ν) ((k : ℝ) ^ (2 * (d + 1))),
    integral_arcLineTowerVector_eq_zero hk d hν, smul_zero, mul_zero]

/-! ### Sine moments and `k^{4(d+1)}`-sublattice blindness of `arcLineBackwardTowerDeriv` -/

theorem integral_arcLineBackwardTowerDeriv_mul_sin {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (c : ℝ) :
    ∫ x, arcLineBackwardTowerDeriv k d ν x * Real.sin (c * x) =
      (k : ℝ) ^ (d + 1) * ∫ t, arcLineTowerDeriv k d ν t *
        Real.sin ((c / (k : ℝ) ^ (2 * (d + 1))) * t) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have e : (fun x => arcLineBackwardTowerDeriv k d ν x * Real.sin (c * x)) = fun x =>
      (k : ℝ) ^ (3 * (d + 1)) * (arcLineTowerDeriv k d ν ((k : ℝ) ^ (2 * (d + 1)) * x) *
        Real.sin ((c / (k : ℝ) ^ (2 * (d + 1))) * ((k : ℝ) ^ (2 * (d + 1)) * x))) := by
    funext x
    unfold arcLineBackwardTowerDeriv
    have hx : c / (k : ℝ) ^ (2 * (d + 1)) * ((k : ℝ) ^ (2 * (d + 1)) * x) = c * x := by
      field_simp
    rw [hx]; ring
  have hpow : (k : ℝ) ^ (3 * (d + 1)) = (k : ℝ) ^ (d + 1) * (k : ℝ) ^ (2 * (d + 1)) := by
    rw [show 3 * (d + 1) = (d + 1) + 2 * (d + 1) by ring, pow_add]
  rw [e, integral_const_mul, Measure.integral_comp_mul_left
    (fun t => arcLineTowerDeriv k d ν t *
      Real.sin ((c / (k : ℝ) ^ (2 * (d + 1))) * t)) ((k : ℝ) ^ (2 * (d + 1))),
    smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hkpos (2 * (d + 1)))), hpow]
  field_simp

/-- On the `k^{2(d+1)}`-sublattice `arcFreq (k^{2(d+1)}(m+1) − 1)`, rescaling maps the frequency
to `arcFreq m`. -/
theorem integral_arcLineBackwardTowerDeriv_mul_sin_sublattice {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (m : ℕ) :
    ∫ x, arcLineBackwardTowerDeriv k d ν x *
        Real.sin (arcFreq (k ^ (2 * (d + 1)) * (m + 1) - 1) * x) =
      (k : ℝ) ^ (d + 1) * ∫ t, arcLineTowerDeriv k d ν t * Real.sin (arcFreq m * t) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  set N := k ^ (2 * (d + 1))
  have hN : 1 ≤ N := Nat.one_le_pow (2 * (d + 1)) k hk
  have hfreq : arcFreq (N * (m + 1) - 1) / (k : ℝ) ^ (2 * (d + 1)) = arcFreq m := by
    have hmul : arcFreq (N * (m + 1) - 1) = arcFreq m * (N : ℝ) := by
      rw [Nat.mul_comm N (m + 1), ← arcFreq_mul_nat hN m]
    have hNcast : (N : ℝ) = (k : ℝ) ^ (2 * (d + 1)) := by dsimp [N]; push_cast; rfl
    rw [hmul, hNcast]
    field_simp
  rw [integral_arcLineBackwardTowerDeriv_mul_sin hk d ν, hfreq]

/-- **Exact `k^{4(d+1)}`-sublattice blindness of `arcLineBackwardTowerDeriv k d ν`.** -/
theorem integral_arcLineBackwardTowerDeriv_mul_sin_double_sublattice_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d m : ℕ) :
    ∫ x, arcLineBackwardTowerDeriv k d ν x *
        Real.sin (arcFreq (k ^ (4 * (d + 1)) * (m + 1) - 1) * x) = 0 := by
  have hN : 1 ≤ k ^ (2 * (d + 1)) := Nat.one_le_pow (2 * (d + 1)) k hk
  have h1 : 1 ≤ k ^ (2 * (d + 1)) * (m + 1) := Nat.mul_pos hN (Nat.succ_pos m)
  have hidx : k ^ (4 * (d + 1)) * (m + 1) - 1 =
      k ^ (2 * (d + 1)) * ((k ^ (2 * (d + 1)) * (m + 1) - 1) + 1) - 1 := by
    have hpow : k ^ (4 * (d + 1)) = k ^ (2 * (d + 1)) * k ^ (2 * (d + 1)) := by
      rw [show 4 * (d + 1) = 2 * (d + 1) + 2 * (d + 1) by ring, pow_add]
    rw [Nat.sub_add_cancel h1, hpow]
    ring_nf
  rw [hidx, integral_arcLineBackwardTowerDeriv_mul_sin_sublattice hk d ν,
    integral_arcLineTowerDeriv_mul_sin_sublattice_eq_zero hblind hk d m, mul_zero]

/-! ### The self-reciprocal symmetrization `arcLineSymTowerVector` at depth `d` -/

/-- Level `d` of the self-reciprocal symmetrized forward-backward tower:
`S_{k,d,ν}(x) = ½ (arcLineForwardTowerVector k d ν x + arcLineBackwardTowerVector k d ν x)`. -/
def arcLineSymTowerVector (k d : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (arcLineForwardTowerVector k d ν x + arcLineBackwardTowerVector k d ν x)

/-- Its derivative `S_{k,d,ν}'(x) = ½ (F_{k,d,ν}'(x) + B_{k,d,ν}'(x))`. -/
def arcLineSymTowerDeriv (k d : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (arcLineForwardTowerDeriv k d ν x + arcLineBackwardTowerDeriv k d ν x)

/-- Its log-scale profile `½ (F_{k,d,ν}^{prof}(v) + B_{k,d,ν}^{prof}(v))`. -/
def arcLineSymTowerProfile (k d : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (arcLineForwardTowerProfile k d ν v + arcLineBackwardTowerProfile k d ν v)

theorem hasDerivAt_arcLineSymTowerVector (k d : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineSymTowerVector k d ν) (arcLineSymTowerDeriv k d ν x) x :=
  ((hasDerivAt_arcLineForwardTowerVector k d ν x).add
    (hasDerivAt_arcLineBackwardTowerVector k d ν x)).const_mul (1 / 2 : ℝ)

theorem arcLineSymTowerVector_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineSymTowerVector k d ν (-x) = arcLineSymTowerVector k d ν x := by
  unfold arcLineSymTowerVector
  rw [arcLineForwardTowerVector_neg_of_map_arcNeg k d hν,
    arcLineBackwardTowerVector_neg_of_map_arcNeg k d hν]

theorem arcLineSymTowerDeriv_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineSymTowerDeriv k d ν (-x) = -arcLineSymTowerDeriv k d ν x := by
  unfold arcLineSymTowerDeriv
  rw [arcLineForwardTowerDeriv_neg_of_map_arcNeg k d hν,
    arcLineBackwardTowerDeriv_neg_of_map_arcNeg k d hν]
  ring

/-- **Exact `x ↦ 1/x` self-reciprocity at every tower depth `d ∈ ℕ`:**
`arcLineSymTowerVector k d ν (1/x) = |x| · arcLineSymTowerVector k d ν x` for all `x ≠ 0`. -/
theorem arcLineSymTowerVector_inv {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (ν : Measure ArcParam)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineSymTowerVector k d ν (1 / x) = |x| * arcLineSymTowerVector k d ν x := by
  unfold arcLineSymTowerVector
  rw [arcLineForwardTowerVector_inv_eq_backward hk d ν hx,
    arcLineBackwardTowerVector_inv_eq_forward hk d ν hx]
  ring

theorem exp_half_mul_arcLineSymTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineSymTowerVector k d ν (Real.exp v) =
      arcLineSymTowerProfile k d ν v := by
  unfold arcLineSymTowerVector arcLineSymTowerProfile
  rw [← mul_left_comm, mul_add, exp_half_mul_arcLineForwardTowerVector hk d ν,
    exp_half_mul_arcLineBackwardTowerVector hk d ν]

theorem integrable_arcLineSymTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineSymTowerVector k d ν) :=
  ((integrable_arcLineForwardTowerVector hk d hν).add
    (integrable_arcLineBackwardTowerVector hk d hν)).const_mul (1 / 2 : ℝ)

theorem integrable_arcLineSymTowerDeriv {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineSymTowerDeriv k d ν) :=
  ((integrable_arcLineForwardTowerDeriv hk d ν).add
    (integrable_arcLineBackwardTowerDeriv hk d ν)).const_mul (1 / 2 : ℝ)

theorem integral_arcLineSymTowerVector_eq_zero {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineSymTowerVector k d ν x = 0 := by
  unfold arcLineSymTowerVector
  rw [integral_const_mul, integral_add (integrable_arcLineForwardTowerVector hk d hν)
    (integrable_arcLineBackwardTowerVector hk d hν),
    integral_arcLineForwardTowerVector_eq_zero hk d hν,
    integral_arcLineBackwardTowerVector_eq_zero hk d hν, add_zero, mul_zero]

/-! ### Exact Forward-Backward Spectral Isolation Law and `k^{4(d+1)}`-blindness -/

/-- **Exact Forward-Backward Spectral Isolation Law at arbitrary depth `d ∈ ℕ`:**
At every positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`), the forward component
`arcLineForwardTowerDeriv k d ν` vanishes identically, so the sine moment of the self-reciprocal
witness `arcLineSymTowerDeriv k d ν` equals `½` the backward moment. -/
theorem integral_arcLineSymTowerDeriv_mul_sin_eq_half_backward
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d n : ℕ) :
    ∫ x, arcLineSymTowerDeriv k d ν x * Real.sin (arcFreq n * x) =
      (1 / 2 : ℝ) * ∫ x, arcLineBackwardTowerDeriv k d ν x * Real.sin (arcFreq n * x) := by
  have hF : Integrable fun x => arcLineForwardTowerDeriv k d ν x * Real.sin (arcFreq n * x) :=
    (integrable_arcLineForwardTowerDeriv hk d ν).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hB : Integrable fun x => arcLineBackwardTowerDeriv k d ν x * Real.sin (arcFreq n * x) :=
    (integrable_arcLineBackwardTowerDeriv hk d ν).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : (fun x => arcLineSymTowerDeriv k d ν x * Real.sin (arcFreq n * x)) = fun x =>
      (1 / 2 : ℝ) * (arcLineForwardTowerDeriv k d ν x * Real.sin (arcFreq n * x) +
        arcLineBackwardTowerDeriv k d ν x * Real.sin (arcFreq n * x)) := by
    funext x; unfold arcLineSymTowerDeriv; ring
  rw [e, integral_const_mul, integral_add hF hB,
    integral_arcLineForwardTowerDeriv_mul_sin_eq_zero hblind hk d n, zero_add]

/-- **Exact `k^{4(d+1)}`-sublattice blindness of the self-reciprocal witness `arcLineSymTowerDeriv`.** -/
theorem integral_arcLineSymTowerDeriv_mul_sin_double_sublattice_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d m : ℕ) :
    ∫ x, arcLineSymTowerDeriv k d ν x *
        Real.sin (arcFreq (k ^ (4 * (d + 1)) * (m + 1) - 1) * x) = 0 := by
  rw [integral_arcLineSymTowerDeriv_mul_sin_eq_half_backward hblind hk d,
    integral_arcLineBackwardTowerDeriv_mul_sin_double_sublattice_eq_zero hblind hk d m, mul_zero]

/-! ### Strip Laplace/Mellin factorization and `O((1/2 − l)^{d+1})` strip-edge vanishing -/

theorem integral_exp_mul_arcLineBackwardTowerProfile (k d : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    ∫ v, Real.exp (l * v) * arcLineBackwardTowerProfile k d ν v =
      Real.exp (-(l * (((2 * (d + 1) : ℕ) : ℝ) * Real.log k))) *
        ∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v := by
  unfold arcLineBackwardTowerProfile
  set w := ((2 * (d + 1) : ℕ) : ℝ) * Real.log k
  rw [← integral_sub_right_eq_self (μ := volume)
    (fun v => Real.exp (l * v) * arcLineTowerProfile k d ν (v + w)) w, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [sub_add_cancel, show l * (v - w) = -(l * w) + l * v by ring, Real.exp_add]
  ring

theorem integral_exp_mul_arcLineSymTowerProfile (k d : ℕ) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * arcLineSymTowerProfile k d ν v =
      Real.cosh (l * (((2 * (d + 1) : ℕ) : ℝ) * Real.log k)) *
        ∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v := by
  have hk0 : Integrable fun v => Real.exp (l * v) * arcLineTowerProfile k d ν v := by
    induction d with
    | zero => exact integrable_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl
    | succ d ih => exact integrable_exp_mul_hyperbolicFilterProfile k ih
  set w := ((2 * (d + 1) : ℕ) : ℝ) * Real.log k
  have hF : Integrable fun v => Real.exp (l * v) * arcLineForwardTowerProfile k d ν v := by
    have h := (hk0.comp_sub_right w).const_mul (Real.exp (l * w))
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [arcLineForwardTowerProfile]
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have hB : Integrable fun v => Real.exp (l * v) * arcLineBackwardTowerProfile k d ν v := by
    have h := (hk0.comp_add_right w).const_mul (Real.exp (-(l * w)))
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [arcLineBackwardTowerProfile]
    rw [show l * v = -(l * w) + l * (v + w) by ring, Real.exp_add]; ring
  have e : (fun v => Real.exp (l * v) * arcLineSymTowerProfile k d ν v) = fun v =>
      (1 / 2 : ℝ) * (Real.exp (l * v) * arcLineForwardTowerProfile k d ν v +
        Real.exp (l * v) * arcLineBackwardTowerProfile k d ν v) := by
    funext v; unfold arcLineSymTowerProfile; ring
  rw [e, integral_const_mul, integral_add hF hB,
    integral_exp_mul_arcLineForwardTowerProfile,
    integral_exp_mul_arcLineBackwardTowerProfile,
    Real.cosh_eq (l * (((2 * (d + 1) : ℕ) : ℝ) * Real.log k))]
  ring

/-- **Arbitrary-order `O((1/2 − l)^{d+1})` strip-edge vanishing for `arcLineSymTowerProfile`.** -/
theorem abs_integral_exp_mul_arcLineSymTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineSymTowerProfile k d ν v| ≤
      10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
        (1 / 2 - l) ^ (d + 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hexp : Real.exp (((d + 1 : ℕ) : ℝ) * Real.log k) = (k : ℝ) ^ (d + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
  set w := ((2 * (d + 1) : ℕ) : ℝ) * Real.log k
  have hcosh_le : Real.cosh (l * w) ≤ (k : ℝ) ^ (d + 1) := by
    have hw : l * w ≤ ((d + 1 : ℕ) : ℝ) * Real.log k := by
      have h2 : w = 2 * (((d + 1 : ℕ) : ℝ) * Real.log k) := by dsimp [w]; push_cast; ring
      have hd0 : 0 ≤ ((d + 1 : ℕ) : ℝ) * Real.log k := by positivity
      nlinarith
    have h1 : Real.exp (l * w) ≤ (k : ℝ) ^ (d + 1) := by
      rw [← hexp]; exact Real.exp_le_exp.mpr hw
    have h2 : Real.exp (-(l * w)) ≤ (k : ℝ) ^ (d + 1) := by
      rw [← hexp]; refine Real.exp_le_exp.mpr ?_
      have hlw0 : 0 ≤ l * w := by positivity
      have hd0 : 0 ≤ ((d + 1 : ℕ) : ℝ) * Real.log k := by positivity
      linarith
    rw [Real.cosh_eq]
    linarith
  rw [integral_exp_mul_arcLineSymTowerProfile k d hν hl0 hl, abs_mul,
    abs_of_pos (Real.cosh_pos _)]
  have hT := abs_integral_exp_mul_arcLineTowerProfile_le hk d hν hl0 hl
  calc Real.cosh (l * w) * |∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v|
      ≤ (k : ℝ) ^ (d + 1) * (10 * ν.real univ * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
          (1 / 2 - l) ^ (d + 1)) :=
        mul_le_mul hcosh_le hT (abs_nonneg _) (by positivity)
    _ = 10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
          (1 / 2 - l) ^ (d + 1) := by ring

/-- **`d`-th divided-difference vanishing as `l → (1/2)⁻` for `arcLineSymTowerProfile`.** -/
theorem tendsto_div_pow_integral_exp_mul_arcLineSymTowerProfile_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ v, Real.exp (l * v) * arcLineSymTowerProfile k d ν v) / (1 / 2 - l) ^ d)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := 10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  have hκ : 0 < 1 / 2 - l := by linarith [hl.2]
  have hpow : 0 < (1 / 2 - l) ^ d := pow_pos hκ d
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  calc |∫ v, Real.exp (l * v) * arcLineSymTowerProfile k d ν v|
      ≤ D * (1 / 2 - l) ^ (d + 1) :=
        abs_integral_exp_mul_arcLineSymTowerProfile_le hk d hν hl.1.le hl.2
    _ = D * (1 / 2 - l) * (1 / 2 - l) ^ d := by rw [pow_succ']; ring

/-! ### Master unconditional arbitrary-order Mellin-inversion duality & spectral isolation theorem -/

/-- **Master unconditional theorem for arbitrary-order Mellin-inversion duality and spectral isolation.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2` and every prescribed order `d ∈ ℕ`:
1. `arcLineForwardTowerVector k d ν` and `arcLineBackwardTowerVector k d ν` are exact Mellin-inversion
   duals (`F(1/x) = |x| B(x)` and `B(1/x) = |x| F(x)`);
2. Their symmetrization `arcLineSymTowerVector k d ν` is even, strictly self-reciprocal
   (`S(1/x) = |x| S(x)`), and has zero mean;
3. At **every** positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`), `F'` vanishes
   identically and `∫ S'(x) sin(arcFreq n · x) dx = ½ ∫ B'(x) sin(arcFreq n · x) dx`;
4. Along the `k^{4(d+1)}`-sublattice `arcFreq (k^{4(d+1)}(m+1) − 1)`, both `B'` and `S'` vanish
   identically;
5. The strip Laplace/Mellin transform of `arcLineSymTowerProfile k d ν` vanishes to arbitrary
   prescribed order `O((1/2 − l)^{d+1})` as `l → (1/2)⁻`, with vanishing `d`-th divided difference
   on `𝓝[<] (1/2)`. -/
theorem exists_arbitraryOrder_inversionDual_isolation_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k → ∀ d : ℕ,
        (∀ x, x ≠ 0 → arcLineForwardTowerVector k d ν (1 / x) =
          |x| * arcLineBackwardTowerVector k d ν x) ∧
        (∀ x, x ≠ 0 → arcLineBackwardTowerVector k d ν (1 / x) =
          |x| * arcLineForwardTowerVector k d ν x) ∧
        (∀ x, arcLineSymTowerVector k d ν (-x) = arcLineSymTowerVector k d ν x) ∧
        (∀ x, x ≠ 0 → arcLineSymTowerVector k d ν (1 / x) =
          |x| * arcLineSymTowerVector k d ν x) ∧
        ∫ x, arcLineSymTowerVector k d ν x = 0 ∧
        (∀ n : ℕ, ∫ x, arcLineSymTowerDeriv k d ν x * Real.sin (arcFreq n * x) =
          (1 / 2 : ℝ) * ∫ x, arcLineBackwardTowerDeriv k d ν x * Real.sin (arcFreq n * x)) ∧
        (∀ m : ℕ, ∫ x, arcLineSymTowerDeriv k d ν x *
          Real.sin (arcFreq (k ^ (4 * (d + 1)) * (m + 1) - 1) * x) = 0) ∧
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |∫ v, Real.exp (l * v) * arcLineSymTowerProfile k d ν v| ≤
            10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
              (1 / 2 - l) ^ (d + 1)) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineSymTowerProfile k d ν v) / (1 / 2 - l) ^ d)
          (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, _⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk d => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨fun x hx => arcLineForwardTowerVector_inv_eq_backward hk1 d ν hx,
    fun x hx => arcLineBackwardTowerVector_inv_eq_forward hk1 d ν hx,
    arcLineSymTowerVector_neg_of_map_arcNeg k d hsym,
    fun x hx => arcLineSymTowerVector_inv hk1 d ν hx,
    integral_arcLineSymTowerVector_eq_zero hk1 d hsym,
    integral_arcLineSymTowerDeriv_mul_sin_eq_half_backward hblind hk1 d,
    integral_arcLineSymTowerDeriv_mul_sin_double_sublattice_eq_zero hblind hk1 d,
    fun l hl0 hl => abs_integral_exp_mul_arcLineSymTowerProfile_le hk1 d hsym hl0 hl,
    tendsto_div_pow_integral_exp_mul_arcLineSymTowerProfile_nhdsWithin hk1 d hsym⟩

end

end RHTower
