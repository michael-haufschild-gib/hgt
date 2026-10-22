import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOneSidedConnection

/-!
# The prime-deletion / modular-inversion commutator of the Jacobi theta function

Let `Θ(y) = Σ_{n ∈ ℤ} e^{-π n² y}`, `(S f)(y) = y^{-1/2} f(1/y)` and `(D_q f)(y) = f(y) - f(qy)`.
Jacobi inversion is `S Θ = Θ`; for `q = p²` the operator `D_q` deletes exactly the theta atoms
whose label is divisible by `p`.  The commutator
`C_q(y) = (D_q - S D_q) Θ(y) = q^{-1/2} Θ(y/q) - Θ(qy) = y^{-1/2} Θ(q/y) - Θ(qy)`
satisfies `S C_q = -C_q` and, for `q > 1`, has the single seam crossing
`C_q > 0` on `(0, 1)`, `C_q(1) = 0`, `C_q < 0` on `(1, ∞)`.
The profile `F(q, y) = -C_q(y)` has `∂_q F = 2π Σ_{n≥1} n² [y^{-3/2} e^{-πn²q/y} - y e^{-πn²qy}] > 0`
for `q ≥ 1 < y` (from `y^{5/2} < e^{π(y - 1/y)}`), the exchange symmetry `F(q, y) = F(y, q)`,
bounds `0 < F < 1 - y^{-1/2}` and the limit `1 - y^{-1/2}`.

In logarithmic coordinates `P(t) = e^{t/4} Θ(e^t)` is even and
`e^{(a+b)/4} F(e^a, e^b) = K(a, b) = P(a + b) - P(a - b)`; with `R(t) = e^{t/4}(Θ(e^t) - 1)`
positive and strictly decreasing on `t ≥ 0`, `K = [V(a+b) - V(|a-b|)] - [R(|a-b|) - R(a+b)]`
(`V(t) = e^{t/4}`), both brackets positive, and the vacuum has the Gram form
`V(a+b) - V(|a-b|) = ½ ∫₀^{min(a,b)} e^{(a-s)/4} e^{(b-s)/4} ds`.

For a continuous even `P` of exponential type `ω` and `u, v > ω`, a triangle exchange gives the
two-scale Laplace pairing
`∫₀^∞∫₀^∞ e^{-ua-vb}[P(a+b) - P(a-b)] = (L(v) - L(u))/(u - v) - (L(u) + L(v))/(u + v)
  = 2[G(v) - G(u)]/(u² - v²)`, `G(u) = u L(u)`, with diagonal value `-G'(u)/u`.
For the theta profile it is positive, so `G` decreases strictly on `(1/4, ∞)`.  Finally
`L(u) = 1/(u - 1/4) + M_{2iu}` with the Ward Mellin integral `M_z`, the one-sided connection is
`H(2is) = (s² - 1/16) L(s) - s Θ(1)`, and `Ξ(2is) = (s² - 1/16) [L(s) + L(-s)]`.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta

noncomputable section

namespace RHTower

/-! ## The real Jacobi theta function -/

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-- Jacobi inversion `Θ(1/y) = √y Θ(y)`. -/
theorem evenKernel_zero_one_div {y : ℝ} (hy : 0 < y) : Θ (1 / y) = Real.sqrt y * Θ y := by
  have h := evenKernel_functional_equation (0 : UnitAddCircle) y
  rw [← evenKernel_eq_cosKernel_of_zero, ← Real.sqrt_eq_rpow] at h
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [h]
  field_simp

/-- Two-scale form of inversion: `y^{-1/2} Θ(q/y) = q^{-1/2} Θ(y/q)`. -/
theorem evenKernel_zero_div_inversion {q y : ℝ} (hq : 0 < q) (hy : 0 < y) :
    (Real.sqrt y)⁻¹ * Θ (q / y) = (Real.sqrt q)⁻¹ * Θ (y / q) := by
  have h := evenKernel_zero_one_div (div_pos hy hq)
  rw [one_div_div, Real.sqrt_div' _ hq.le] at h
  rw [h]
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hq' : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  field_simp

/-- `Θ(y) - 1 = 2 Σ_{n ≥ 1} e^{-π n² y}`. -/
theorem hasSum_evenKernel_zero_sub_one {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 2 * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * y))) (Θ y - 1) := by
  have h := hasSum_nat_cosKernel₀ 0 hy
  simp only [QuotientAddGroup.mk_zero, ← evenKernel_eq_cosKernel_of_zero] at h
  simpa [neg_mul] using h

theorem evenKernel_zero_eq_int_tsum {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y))) (Θ y) := by
  have h := hasSum_int_evenKernel 0 hy
  simpa [neg_mul] using h

theorem one_lt_evenKernel_zero {y : ℝ} (hy : 0 < y) : 1 < Θ y := by
  have h := hasSum_evenKernel_zero_sub_one hy
  have hpos : 0 < Θ y - 1 := h.tsum_eq ▸ h.summable.tsum_pos (fun n => by positivity) 0
    (by positivity)
  linarith

/-- The theta moment series `Σ_{n ≥ 1} n^{2k} e^{-π n² y}`. -/
def thetaMoment (k : ℕ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * k) * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * y))

theorem summable_thetaMoment_terms (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * k) *
      Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * y))) := by
  have h := GaloisForLFunctions.summable_pow_mul_exp_neg_nat_sq (2 * k)
    (mul_pos Real.pi_pos hy)
  have h1 := (summable_nat_add_iff 1).mpr h
  refine h1.congr fun n => ?_
  push_cast
  ring_nf

theorem thetaMoment_pos (k : ℕ) {y : ℝ} (hy : 0 < y) : 0 < thetaMoment k y :=
  (summable_thetaMoment_terms k hy).tsum_pos (fun n => by positivity) 0 (by positivity)

theorem hasDerivAt_thetaMoment (k : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (thetaMoment k) (-(Real.pi * thetaMoment (k + 1) y)) y := by
  have hy2 : y / 2 ∈ Ioi (y / 4) := by simp only [mem_Ioi]; linarith
  have hyI : y ∈ Ioi (y / 4) := by simp only [mem_Ioi]; linarith
  have hu := (summable_thetaMoment_terms (k + 1) (show 0 < y / 4 by positivity)).mul_left Real.pi
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun (n : ℕ) (w : ℝ) =>
      ((n : ℝ) + 1) ^ (2 * k) * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * w)))
    (g' := fun (n : ℕ) (w : ℝ) =>
      -(Real.pi * (((n : ℝ) + 1) ^ (2 * (k + 1)) *
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * w))))) hu isOpen_Ioi
    isPreconnected_Ioi
    (fun n w _ => by
      have h0 : HasDerivAt (fun x : ℝ => -(Real.pi * ((n : ℝ) + 1) ^ 2 * x))
          (-(Real.pi * ((n : ℝ) + 1) ^ 2 * 1)) w :=
        ((hasDerivAt_id w).const_mul (Real.pi * ((n : ℝ) + 1) ^ 2)).neg
      refine (h0.exp.const_mul (((n : ℝ) + 1) ^ (2 * k))).congr_deriv ?_
      ring)
    (fun n w hw => by
      have hw' : y / 4 < w := hw
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
        Real.pi_pos.le
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ Real.pi * ((n : ℝ) + 1) ^ 2 := by positivity
      nlinarith)
    hy2 (summable_thetaMoment_terms k (by linarith [hy2.out] : (0 : ℝ) < y / 2)) hyI
  have hsum : (∑' n : ℕ, -(Real.pi * (((n : ℝ) + 1) ^ (2 * (k + 1)) *
      Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * y))))) = -(Real.pi * thetaMoment (k + 1) y) := by
    rw [tsum_neg, tsum_mul_left]; rfl
  rw [hsum] at key
  exact key

theorem evenKernel_zero_eq_thetaMoment {y : ℝ} (hy : 0 < y) : Θ y = 1 + 2 * thetaMoment 0 y := by
  have h := (hasSum_evenKernel_zero_sub_one hy).tsum_eq
  rw [tsum_mul_left] at h
  unfold thetaMoment
  simp only [mul_zero, pow_zero, one_mul]
  linarith

/-- `Θ'(y) = -2π Σ_{n ≥ 1} n² e^{-π n² y}`. -/
theorem hasDerivAt_evenKernel_zero {y : ℝ} (hy : 0 < y) :
    HasDerivAt Θ (-(2 * Real.pi * thetaMoment 1 y)) y := by
  have h := ((hasDerivAt_thetaMoment 0 hy).const_mul 2).const_add 1
  have heq : (fun w => 1 + 2 * thetaMoment 0 w) =ᶠ[𝓝 y] Θ := by
    filter_upwards [isOpen_Ioi.mem_nhds (show y ∈ Ioi 0 from hy)] with w hw
    exact (evenKernel_zero_eq_thetaMoment hw).symm
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  ring

theorem tendsto_evenKernel_zero_atTop : Tendsto Θ atTop (𝓝 1) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  simp only [if_true] at hO
  have h0 : Tendsto (fun x : ℝ => Real.exp (-p * x)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
    refine this.congr fun x => ?_
    simp [neg_mul]
  have := hO.trans_tendsto h0
  have h2 := this.add_const 1
  simpa using h2

/-! ## The deletion–inversion commutator -/

/-- Modular inversion `(S f)(y) = y^{-1/2} f(1/y)`. -/
def thetaInversion (f : ℝ → ℝ) (y : ℝ) : ℝ := (Real.sqrt y)⁻¹ * f (1 / y)

/-- Scale deletion `(D_q f)(y) = f(y) - f(qy)`. -/
def scaleDeletion (q : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := f y - f (q * y)

/-- The deletion–inversion commutator `C_q = (D_q - S D_q) Θ`. -/
def deletionInversionCommutator (q y : ℝ) : ℝ :=
  scaleDeletion q Θ y - thetaInversion (scaleDeletion q Θ) y

/-- The profile `F(q, y) = -C_q(y) = Θ(qy) - y^{-1/2} Θ(q/y)`. -/
def commutatorProfile (q y : ℝ) : ℝ := Θ (q * y) - (Real.sqrt y)⁻¹ * Θ (q / y)

/-- Jacobi inversion `S Θ = Θ`. -/
theorem thetaInversion_evenKernel {y : ℝ} (hy : 0 < y) : thetaInversion Θ y = Θ y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [thetaInversion, evenKernel_zero_one_div hy]
  field_simp

/-- `S² = 1` on positive arguments. -/
theorem thetaInversion_thetaInversion (f : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    thetaInversion (thetaInversion f) y = f y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [thetaInversion, thetaInversion, one_div_one_div, Real.sqrt_div' _ hy.le, Real.sqrt_one]
  field_simp

/-- `C_q(y) = y^{-1/2} Θ(q/y) - Θ(qy)`. -/
theorem deletionInversionCommutator_eq {q y : ℝ} (hy : 0 < y) :
    deletionInversionCommutator q y = (Real.sqrt y)⁻¹ * Θ (q / y) - Θ (q * y) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [deletionInversionCommutator, scaleDeletion, thetaInversion, scaleDeletion,
    evenKernel_zero_one_div hy, mul_one_div]
  field_simp
  ring

/-- `C_q(y) = q^{-1/2} Θ(y/q) - Θ(qy)`. -/
theorem deletionInversionCommutator_eq' {q y : ℝ} (hq : 0 < q) (hy : 0 < y) :
    deletionInversionCommutator q y = (Real.sqrt q)⁻¹ * Θ (y / q) - Θ (q * y) := by
  rw [deletionInversionCommutator_eq hy, evenKernel_zero_div_inversion hq hy]

/-- For `q = p²`, `D_q Θ` deletes exactly the theta atoms whose label is divisible by `p`. -/
theorem hasSum_scaleDeletion_prime_sq {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => if (p : ℤ) ∣ n then 0 else Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y)))
      (scaleDeletion ((p : ℝ) ^ 2) Θ y) := by
  set f : ℤ → ℝ := fun n => Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hall : HasSum f (Θ y) := evenKernel_zero_eq_int_tsum hy
  have hmul : HasSum (fun n : ℤ => if (p : ℤ) ∣ n then f n else 0) (Θ ((p : ℝ) ^ 2 * y)) := by
    have hinj : Function.Injective (fun m : ℤ => (p : ℤ) * m) :=
      fun a b h => mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) h
    rw [← hinj.hasSum_iff]
    · have h2 := evenKernel_zero_eq_int_tsum (show 0 < (p : ℝ) ^ 2 * y by positivity)
      refine h2.congr_fun fun m => ?_
      simp only [Function.comp, dvd_mul_right, if_true, f]
      push_cast
      ring_nf
    · intro n hn
      have : ¬ (p : ℤ) ∣ n := by
        rintro ⟨m, rfl⟩
        exact hn ⟨m, rfl⟩
      simp [this]
  have := hall.sub hmul
  refine this.congr_fun fun n => ?_
  by_cases h : (p : ℤ) ∣ n <;> simp [h, f]

theorem neg_deletionInversionCommutator {q y : ℝ} (hy : 0 < y) :
    -deletionInversionCommutator q y = commutatorProfile q y := by
  rw [deletionInversionCommutator_eq hy, commutatorProfile]
  ring

/-- `C_q(y) = y^{-1/2} F(q, 1/y)`. -/
theorem deletionInversionCommutator_eq_profile_inv {q y : ℝ} (hy : 0 < y) :
    deletionInversionCommutator q y = (Real.sqrt y)⁻¹ * commutatorProfile q (1 / y) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [deletionInversionCommutator_eq hy, commutatorProfile, Real.sqrt_div' _ hy.le,
    Real.sqrt_one, div_div_eq_mul_div, div_one, mul_one_div]
  field_simp

/-- `S C_q = -C_q`. -/
theorem thetaInversion_deletionInversionCommutator {q y : ℝ} (hy : 0 < y) :
    thetaInversion (deletionInversionCommutator q) y = -deletionInversionCommutator q y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [thetaInversion, deletionInversionCommutator_eq (one_div_pos.2 hy),
    deletionInversionCommutator_eq hy, Real.sqrt_div' _ hy.le, Real.sqrt_one,
    div_div_eq_mul_div, div_one, mul_one_div]
  field_simp
  ring

/-- **Exchange symmetry** `F(q, y) = F(y, q)`. -/
theorem commutatorProfile_symm {q y : ℝ} (hq : 0 < q) (hy : 0 < y) :
    commutatorProfile q y = commutatorProfile y q := by
  rw [commutatorProfile, commutatorProfile, mul_comm, evenKernel_zero_div_inversion hq hy]

theorem commutatorProfile_one_left {y : ℝ} (hy : 0 < y) : commutatorProfile 1 y = 0 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  rw [commutatorProfile, one_mul, evenKernel_zero_one_div hy]
  field_simp
  ring

theorem commutatorProfile_one_right (q : ℝ) : commutatorProfile q 1 = 0 := by
  rw [commutatorProfile, mul_one, div_one, Real.sqrt_one, inv_one, one_mul, sub_self]

/-- The `q`-derivative of the profile, `2π Σ_{n ≥ 1} n² [y^{-3/2} e^{-πn²q/y} - y e^{-πn²qy}]`. -/
def commutatorProfileDeriv (q y : ℝ) : ℝ :=
  2 * Real.pi * ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 *
    (((Real.sqrt y) ^ 3)⁻¹ * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q / y))) -
      y * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q * y))))

theorem hasDerivAt_commutatorProfile {q y : ℝ} (hq : 0 < q) (hy : 0 < y) :
    HasDerivAt (fun q => commutatorProfile q y) (commutatorProfileDeriv q y) q := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h1 : HasDerivAt (fun q => Θ (q * y)) (-(2 * Real.pi * thetaMoment 1 (q * y)) * y) q :=
    (hasDerivAt_evenKernel_zero (mul_pos hq hy)).comp q ((hasDerivAt_id q).mul_const y |>.congr_deriv
      (one_mul y))
  have h2 : HasDerivAt (fun q => Θ (q / y)) (-(2 * Real.pi * thetaMoment 1 (q / y)) * (1 / y)) q :=
    (hasDerivAt_evenKernel_zero (div_pos hq hy)).comp q
      ((hasDerivAt_id q).div_const y |>.congr_deriv (by simp [one_div]))
  have h := h1.sub (h2.const_mul (Real.sqrt y)⁻¹)
  refine h.congr_deriv ?_
  have hA := summable_thetaMoment_terms 1 (mul_pos hq hy)
  have hB := summable_thetaMoment_terms 1 (div_pos hq hy)
  have hD : commutatorProfileDeriv q y = 2 * Real.pi *
      (((Real.sqrt y) ^ 3)⁻¹ * thetaMoment 1 (q / y) - y * thetaMoment 1 (q * y)) := by
    rw [commutatorProfileDeriv]
    congr 1
    have hs := (hB.hasSum.mul_left ((Real.sqrt y) ^ 3)⁻¹).sub (hA.hasSum.mul_left y)
    rw [thetaMoment, thetaMoment]
    refine (hs.congr_fun fun n => ?_).tsum_eq
    ring
  have hy3 : (Real.sqrt y) ^ 3 = Real.sqrt y * y := by
    rw [pow_succ, sq, Real.mul_self_sqrt hy.le]; ring
  rw [hD, hy3]
  field_simp
  ring

/-- `y^{5/2} < e^{π(y - 1/y)}` for `y > 1`. -/
theorem sqrt_pow_five_lt_exp {y : ℝ} (hy : 1 < y) :
    y * (Real.sqrt y) ^ 3 < Real.exp (Real.pi * (y - 1 / y)) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hsq : Real.sqrt y = Real.exp (Real.log y / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy0]; ring_nf
  have hlhs : y * (Real.sqrt y) ^ 3 = Real.exp (5 / 2 * Real.log y) := by
    rw [hsq, ← Real.exp_nat_mul]
    calc y * Real.exp (((3 : ℕ) : ℝ) * (Real.log y / 2)) =
        Real.exp (Real.log y) * Real.exp (((3 : ℕ) : ℝ) * (Real.log y / 2)) := by
          rw [Real.exp_log hy0]
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [hlhs, Real.exp_lt_exp]
  have h1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  have h2 : y - 1 ≤ y - 1 / y := by
    have : 1 / y ≤ 1 := by rw [div_le_one hy0]; linarith
    linarith
  nlinarith [Real.pi_gt_three]

theorem commutatorProfileDeriv_pos {q y : ℝ} (hq : 1 ≤ q) (hy : 1 < y) :
    0 < commutatorProfileDeriv q y := by
  have hy0 : 0 < y := by linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hq0 : 0 < q := by linarith
  have hterm : ∀ n : ℕ, y * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q * y))) <
      ((Real.sqrt y) ^ 3)⁻¹ * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q / y))) := by
    intro n
    have hkey := sqrt_pow_five_lt_exp hy
    have ha : Real.pi ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * q := by
      have : 1 ≤ ((n : ℝ) + 1) ^ 2 * q := by
        have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        nlinarith
      nlinarith [Real.pi_pos]
    have hgap : 0 < y - 1 / y := by
      have : 1 / y < 1 := by rw [div_lt_one hy0]; exact hy
      linarith
    have hexp : Real.exp (Real.pi * (y - 1 / y)) ≤
        Real.exp (Real.pi * ((n : ℝ) + 1) ^ 2 * q * (y - 1 / y)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hgap.le)
    have hsplit : Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q / y))) =
        Real.exp (Real.pi * ((n : ℝ) + 1) ^ 2 * q * (y - 1 / y)) *
          Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q * y))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [hsplit]
    have hlt : y < ((Real.sqrt y) ^ 3)⁻¹ *
        Real.exp (Real.pi * ((n : ℝ) + 1) ^ 2 * q * (y - 1 / y)) := by
      rw [lt_inv_mul_iff₀ (by positivity)]
      nlinarith [hkey, hexp]
    exact lt_of_lt_of_eq (mul_lt_mul_of_pos_right hlt (Real.exp_pos _)) (by ring)
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
      (((Real.sqrt y) ^ 3)⁻¹ * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q / y))) -
        y * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * (q * y))))) := by
    have hA := summable_thetaMoment_terms 1 (mul_pos hq0 hy0)
    have hB := summable_thetaMoment_terms 1 (div_pos hq0 hy0)
    refine ((hB.mul_left ((Real.sqrt y) ^ 3)⁻¹).sub (hA.mul_left y)).congr fun n => ?_
    ring
  refine mul_pos (by positivity) (hsum.tsum_pos (fun n => ?_) 0 ?_)
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr (hterm n).le)
  · exact mul_pos (by positivity) (sub_pos.mpr (hterm 0))

theorem continuous_evenKernel_zero_on : ContinuousOn Θ (Ioi 0) := fun _ hy =>
  (hasDerivAt_evenKernel_zero hy).continuousAt.continuousWithinAt

/-- **Scale order.** For `y > 1`, `q ↦ F(q, y)` is strictly increasing on `[1, ∞)`. -/
theorem strictMonoOn_commutatorProfile {y : ℝ} (hy : 1 < y) :
    StrictMonoOn (fun q => commutatorProfile q y) (Ici 1) := by
  have hy0 : 0 < y := by linarith
  refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
  · intro q hq
    exact (hasDerivAt_commutatorProfile (by linarith [hq.out] : (0 : ℝ) < q) hy0).continuousAt
      |>.continuousWithinAt
  · intro q hq
    rw [interior_Ici] at hq
    rw [(hasDerivAt_commutatorProfile (by linarith [hq.out] : (0 : ℝ) < q) hy0).deriv]
    exact commutatorProfileDeriv_pos (le_of_lt hq) hy

theorem tendsto_commutatorProfile_atTop {y : ℝ} (hy : 0 < y) :
    Tendsto (fun q => commutatorProfile q y) atTop (𝓝 (1 - (Real.sqrt y)⁻¹)) := by
  have h1 := tendsto_evenKernel_zero_atTop.comp (tendsto_id.atTop_mul_const hy)
  have h2 := tendsto_evenKernel_zero_atTop.comp (tendsto_id.atTop_div_const hy)
  have := h1.sub (h2.const_mul (Real.sqrt y)⁻¹)
  simpa [commutatorProfile, mul_one] using this

theorem commutatorProfile_pos {q y : ℝ} (hq : 1 < q) (hy : 1 < y) : 0 < commutatorProfile q y := by
  have h : commutatorProfile 1 y < commutatorProfile q y :=
    strictMonoOn_commutatorProfile hy self_mem_Ici (le_of_lt hq : (1 : ℝ) ≤ q) hq
  rwa [commutatorProfile_one_left (by linarith)] at h

theorem commutatorProfile_lt {q y : ℝ} (hq : 1 ≤ q) (hy : 1 < y) :
    commutatorProfile q y < 1 - (Real.sqrt y)⁻¹ := by
  have hmono := strictMonoOn_commutatorProfile hy
  have hlt : commutatorProfile q y < commutatorProfile (q + 1) y :=
    hmono (show (1 : ℝ) ≤ q from hq) (show (1 : ℝ) ≤ q + 1 by linarith) (by linarith)
  refine lt_of_lt_of_le hlt (ge_of_tendsto (tendsto_commutatorProfile_atTop (by linarith)) ?_)
  filter_upwards [eventually_ge_atTop (q + 1)] with r hr
  exact hmono.monotoneOn (show (1 : ℝ) ≤ q + 1 by linarith) (show (1 : ℝ) ≤ r by linarith) hr

/-- **Sign pattern (2).** For `q > 1`, `C_q > 0` on `(0, 1)`, `C_q(1) = 0`, `C_q < 0` on `(1, ∞)`. -/
theorem deletionInversionCommutator_neg {q y : ℝ} (hq : 1 < q) (hy : 1 < y) :
    deletionInversionCommutator q y < 0 := by
  have h := commutatorProfile_pos hq hy
  rw [← neg_deletionInversionCommutator (by linarith)] at h
  linarith

theorem deletionInversionCommutator_one (q : ℝ) : deletionInversionCommutator q 1 = 0 := by
  have h := neg_deletionInversionCommutator (q := q) one_pos
  rw [commutatorProfile_one_right] at h
  linarith

theorem deletionInversionCommutator_pos {q y : ℝ} (hq : 1 < q) (hy0 : 0 < y) (hy : y < 1) :
    0 < deletionInversionCommutator q y := by
  rw [deletionInversionCommutator_eq_profile_inv hy0]
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  exact mul_pos (inv_pos.2 hs) (commutatorProfile_pos hq (by rw [lt_div_iff₀ hy0]; linarith))

/-- On `(1, ∞)` the family `-C_q(y)` increases strictly in `q ≥ 1` with derivative
`2π Σ n² [y^{-3/2} e^{-πn²q/y} - y e^{-πn²qy}] > 0`. -/
theorem hasDerivAt_neg_deletionInversionCommutator {q y : ℝ} (hq : 1 ≤ q) (hy : 1 < y) :
    HasDerivAt (fun q => -deletionInversionCommutator q y) (commutatorProfileDeriv q y) q ∧
      0 < commutatorProfileDeriv q y := by
  have hy0 : 0 < y := by linarith
  refine ⟨?_, commutatorProfileDeriv_pos hq hy⟩
  have h := hasDerivAt_commutatorProfile (by linarith : (0 : ℝ) < q) hy0
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
  exact neg_deletionInversionCommutator hy0

theorem neg_deletionInversionCommutator_bounds {q y : ℝ} (hq : 1 < q) (hy : 1 < y) :
    0 < -deletionInversionCommutator q y ∧ -deletionInversionCommutator q y < 1 - (Real.sqrt y)⁻¹ := by
  rw [neg_deletionInversionCommutator (by linarith)]
  exact ⟨commutatorProfile_pos hq hy, commutatorProfile_lt hq.le hy⟩

theorem tendsto_deletionInversionCommutator_atTop {y : ℝ} (hy : 0 < y) :
    Tendsto (fun q => deletionInversionCommutator q y) atTop (𝓝 ((Real.sqrt y)⁻¹ - 1)) := by
  have h := (tendsto_commutatorProfile_atTop hy).neg
  refine (h.congr fun q => ?_).trans (by rw [neg_sub])
  rw [← neg_deletionInversionCommutator hy, neg_neg]

/-- Below the seam, `q ↦ C_q(y)` increases strictly on `[1, ∞)` from `0` towards `y^{-1/2} - 1`. -/
theorem strictMonoOn_deletionInversionCommutator {y : ℝ} (hy0 : 0 < y) (hy : y < 1) :
    StrictMonoOn (fun q => deletionInversionCommutator q y) (Ici 1) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have h := strictMonoOn_commutatorProfile (show 1 < 1 / y by rw [lt_div_iff₀ hy0]; linarith)
  intro a ha b hb hab
  simp only [deletionInversionCommutator_eq_profile_inv hy0]
  exact mul_lt_mul_of_pos_left (h ha hb hab) (inv_pos.2 hs)

theorem deletionInversionCommutator_lt {q y : ℝ} (hq : 1 < q) (hy0 : 0 < y) (hy : y < 1) :
    deletionInversionCommutator q y < (Real.sqrt y)⁻¹ - 1 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  rw [deletionInversionCommutator_eq_profile_inv hy0]
  have h := commutatorProfile_lt hq.le (show 1 < 1 / y by rw [lt_div_iff₀ hy0]; linarith)
  rw [Real.sqrt_div' _ hy0.le, Real.sqrt_one] at h
  have := mul_lt_mul_of_pos_left h (inv_pos.2 hs)
  calc (Real.sqrt y)⁻¹ * commutatorProfile q (1 / y) < (Real.sqrt y)⁻¹ * (1 - (1 / Real.sqrt y)⁻¹) :=
        this
    _ = (Real.sqrt y)⁻¹ * (1 - Real.sqrt y) := by rw [one_div, inv_inv]
    _ = (Real.sqrt y)⁻¹ - 1 := by field_simp

/-- By exchange symmetry, `F` increases strictly in `y ≥ 1` for fixed `q > 1`. -/
theorem strictMonoOn_commutatorProfile_right {q : ℝ} (hq : 1 < q) :
    StrictMonoOn (fun y => commutatorProfile q y) (Ici 1) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) < a := by linarith [ha.out]
  have hb0 : (0 : ℝ) < b := by linarith [hb.out]
  simp only
  rw [commutatorProfile_symm (by linarith) ha0, commutatorProfile_symm (by linarith) hb0]
  exact strictMonoOn_commutatorProfile hq ha hb hab

theorem tendsto_commutatorProfile_atTop_right {q : ℝ} (hq : 0 < q) :
    Tendsto (fun y => commutatorProfile q y) atTop (𝓝 (1 - (Real.sqrt q)⁻¹)) := by
  refine (tendsto_commutatorProfile_atTop hq).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  exact commutatorProfile_symm hy hq

/-! ## Logarithmic coordinates and the vacuum/arithmetic split -/

/-- `P(t) = e^{t/4} Θ(e^t)`. -/
def thetaLogProfile (t : ℝ) : ℝ := Real.exp (t / 4) * Θ (Real.exp t)

/-- The arithmetic tail `R(t) = e^{t/4} (Θ(e^t) - 1)`. -/
def thetaLogTail (t : ℝ) : ℝ := Real.exp (t / 4) * (Θ (Real.exp t) - 1)

/-- The two-scale kernel `K(a, b) = P(a + b) - P(a - b)`. -/
def deletionInversionKernel (a b : ℝ) : ℝ := thetaLogProfile (a + b) - thetaLogProfile (a - b)

private theorem sqrt_exp_eq (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf

/-- Jacobi inversion makes `P` even. -/
theorem thetaLogProfile_neg (t : ℝ) : thetaLogProfile (-t) = thetaLogProfile t := by
  rw [thetaLogProfile, thetaLogProfile, Real.exp_neg, ← one_div,
    evenKernel_zero_one_div (Real.exp_pos t), sqrt_exp_eq, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Difference-of-scales form (5).** `e^{(a+b)/4} F(e^a, e^b) = P(a + b) - P(a - b)`. -/
theorem exp_mul_commutatorProfile_exp (a b : ℝ) :
    Real.exp ((a + b) / 4) * commutatorProfile (Real.exp a) (Real.exp b) =
      deletionInversionKernel a b := by
  rw [commutatorProfile, deletionInversionKernel, thetaLogProfile, thetaLogProfile,
    ← Real.exp_add, ← Real.exp_sub, sqrt_exp_eq, ← Real.exp_neg, mul_sub, ← mul_assoc,
    ← Real.exp_add]
  congr 2
  ring_nf

theorem thetaLogProfile_eq_add (t : ℝ) : thetaLogProfile t = Real.exp (t / 4) + thetaLogTail t := by
  rw [thetaLogProfile, thetaLogTail]; ring

/-- `R(t) = 2 Σ_{n ≥ 1} e^{t/4 - π n² e^t}`. -/
theorem hasSum_thetaLogTail (t : ℝ) :
    HasSum (fun n : ℕ => 2 * Real.exp (t / 4 - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp t))
      (thetaLogTail t) := by
  have h := (hasSum_evenKernel_zero_sub_one (Real.exp_pos t)).mul_left (Real.exp (t / 4))
  refine h.congr_fun fun n => ?_
  rw [mul_left_comm, ← Real.exp_add]
  congr 2

theorem thetaLogTail_pos (t : ℝ) : 0 < thetaLogTail t :=
  (hasSum_thetaLogTail t).tsum_eq ▸
    (hasSum_thetaLogTail t).summable.tsum_pos (fun n => by positivity) 0 (by positivity)

/-- Every summand of `R` has logarithmic derivative `1/4 - π n² e^t < 0`, so `R` decreases
strictly on `t ≥ 0`. -/
theorem strictAntiOn_thetaLogTail : StrictAntiOn thetaLogTail (Ici 0) := by
  intro s hs t ht hst
  have hs0 : (0 : ℝ) ≤ s := hs
  have hterm : ∀ n : ℕ, t / 4 - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp t <
      s / 4 - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp s := by
    intro n
    have h1 : t - s ≤ Real.exp t - Real.exp s := by
      have h2 : Real.exp t = Real.exp s * Real.exp (t - s) := by rw [← Real.exp_add]; ring_nf
      have h3 := Real.add_one_le_exp (t - s)
      have h4 : 1 ≤ Real.exp s := Real.one_le_exp hs0
      nlinarith
    have hc : Real.pi ≤ Real.pi * ((n : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      nlinarith [Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  refine hasSum_lt (f := fun n : ℕ => 2 * Real.exp (t / 4 - Real.pi * ((n : ℝ) + 1) ^ 2 *
    Real.exp t)) (i := 0) (fun n => ?_) ?_ (hasSum_thetaLogTail t) (hasSum_thetaLogTail s)
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hterm n).le) (by norm_num)
  · exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (hterm 0)) (by norm_num)

/-- **Vacuum versus arithmetic tail (5a).** For `a, b > 0`,
`K(a, b) = [V(a + b) - V(|a - b|)] - [R(|a - b|) - R(a + b)]` with `V(t) = e^{t/4}`. -/
theorem deletionInversionKernel_eq_vacuum_sub_arith (a b : ℝ) :
    deletionInversionKernel a b =
      (Real.exp ((a + b) / 4) - Real.exp (|a - b| / 4)) -
        (thetaLogTail |a - b| - thetaLogTail (a + b)) := by
  have hP : thetaLogProfile (a - b) = thetaLogProfile |a - b| := by
    rcases abs_cases (a - b) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, thetaLogProfile_neg]
  rw [deletionInversionKernel, hP, thetaLogProfile_eq_add, thetaLogProfile_eq_add]
  ring

theorem vacuumKernel_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < Real.exp ((a + b) / 4) - Real.exp (|a - b| / 4) := by
  have : |a - b| < a + b := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have := Real.exp_lt_exp.mpr (show |a - b| / 4 < (a + b) / 4 by linarith)
  linarith

theorem arithKernel_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < thetaLogTail |a - b| - thetaLogTail (a + b) := by
  have : |a - b| < a + b := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have := strictAntiOn_thetaLogTail (show (0 : ℝ) ≤ |a - b| from abs_nonneg _)
    (show (0 : ℝ) ≤ a + b by linarith) this
  linarith

/-- The kernel is positive on `(0, ∞)²`: the vacuum dominates the arithmetic tail entrywise. -/
theorem deletionInversionKernel_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < deletionInversionKernel a b := by
  rw [← exp_mul_commutatorProfile_exp]
  exact mul_pos (Real.exp_pos _) (commutatorProfile_pos (Real.one_lt_exp_iff.2 ha)
    (Real.one_lt_exp_iff.2 hb))

theorem arithKernel_lt_vacuumKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    thetaLogTail |a - b| - thetaLogTail (a + b) <
      Real.exp ((a + b) / 4) - Real.exp (|a - b| / 4) := by
  have h := deletionInversionKernel_pos ha hb
  rw [deletionInversionKernel_eq_vacuum_sub_arith] at h
  linarith

/-- **Gram form of the vacuum (5b).**
`V(a + b) - V(|a - b|) = ½ ∫₀^{min(a,b)} e^{(a-s)/4} e^{(b-s)/4} ds`. -/
theorem vacuumKernel_eq_integral (a b : ℝ) :
    Real.exp ((a + b) / 4) - Real.exp (|a - b| / 4) =
      (1 / 2) * ∫ s in (0 : ℝ)..min a b, Real.exp ((a - s) / 4) * Real.exp ((b - s) / 4) := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) (min a b),
      HasDerivAt (fun s => -2 * Real.exp ((a + b) / 4 - s / 2))
        (Real.exp ((a - s) / 4) * Real.exp ((b - s) / 4)) s := by
    intro s _
    have h := (((hasDerivAt_id s).div_const 2).const_sub ((a + b) / 4)).exp.const_mul (-2)
    refine h.congr_deriv ?_
    rw [← Real.exp_add]
    simp only [id]
    ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun s : ℝ =>
      Real.exp ((a - s) / 4) * Real.exp ((b - s) / 4)).intervalIntegrable _ _)]
  have hmin : (a + b) / 4 - min a b / 2 = |a - b| / 4 := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  rw [hmin]
  simp only [zero_div, sub_zero]
  ring

/-! ## One-sided Laplace transforms and the triangle exchange -/

/-- The one-sided Laplace transform `∫₀^∞ e^{-u t} f(t) dt`. -/
def halfLineLaplace (f : ℝ → ℝ) (u : ℝ) : ℝ := ∫ t in Ioi 0, Real.exp (-(u * t)) * f t

theorem setIntegral_Ioi_zero_comp_add (g : ℝ → ℝ) (b : ℝ) :
    ∫ x in Ioi 0, g (x + b) = ∫ y in Ioi b, g y := by
  have h := (measurePreserving_add_right volume b).setIntegral_preimage_emb
    (measurableEmbedding_addRight b) g (Ioi b)
  have hpre : (fun x : ℝ => x + b) ⁻¹' Ioi b = Ioi 0 := by ext x; simp
  rwa [hpre] at h

/-- `y e^{-δ y} ≤ (2/δ) e^{-δy/2}`. -/
theorem mul_exp_neg_le_two_div {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    y * Real.exp (-(δ * y)) ≤ 2 / δ * Real.exp (-(δ / 2 * y)) := by
  have h := Real.add_one_le_exp (δ / 2 * y)
  have hsplit : Real.exp (-(δ / 2 * y)) = Real.exp (δ / 2 * y) * Real.exp (-(δ * y)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have he := Real.exp_pos (-(δ * y))
  have : y ≤ 2 / δ * Real.exp (δ / 2 * y) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith
  nlinarith

theorem integrableOn_of_le_mul_exp {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0)) {D δ : ℝ}
    (hδ : 0 < δ) (hle : ∀ y, 0 < y → |F y| ≤ D * (y * Real.exp (-(δ * y)))) :
    IntegrableOn F (Ioi 0) := by
  have hdom : IntegrableOn (fun y => |D| * (2 / δ) * Real.exp ((-(δ / 2)) * y)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hdom.mono' (hF.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
  have hy0 : (0 : ℝ) < y := hy
  rw [Real.norm_eq_abs]
  calc |F y| ≤ D * (y * Real.exp (-(δ * y))) := hle y hy0
    _ ≤ |D| * (y * Real.exp (-(δ * y))) :=
        mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity)
    _ ≤ |D| * (2 / δ * Real.exp (-(δ / 2 * y))) :=
        mul_le_mul_of_nonneg_left (mul_exp_neg_le_two_div hδ y) (abs_nonneg D)
    _ = |D| * (2 / δ) * Real.exp ((-(δ / 2)) * y) := by ring_nf

/-- Integrability of the triangle kernel `1_{x < y} g(x) f(y)` on `(0, ∞)²`. -/
theorem integrable_triangle {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hF : IntegrableOn (fun y => |f y| * ∫ x in (0 : ℝ)..y, |g x|) (Ioi 0)) :
    Integrable (fun p : ℝ × ℝ => if p.1 < p.2 then g p.1 * f p.2 else 0)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  classical
  have hmeas : Measurable (fun p : ℝ × ℝ => if p.1 < p.2 then g p.1 * f p.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      ((by fun_prop : Continuous fun p : ℝ × ℝ => g p.1 * f p.2).measurable) measurable_const
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  have hind : ∀ y : ℝ, (fun x => if x < y then g x * f y else 0) =
      (Iio y).indicator (fun x => g x * f y) := fun y => by
    funext x; simp only [Set.indicator, mem_Iio]
  refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
  · simp only
    rw [hind y, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iio]
    refine ((by fun_prop : Continuous fun x => g x * f y).integrableOn_Icc (a := 0) (b := y)).mono_set
      ?_
    intro x hx
    exact ⟨le_of_lt hx.2, le_of_lt hx.1⟩
  · refine hF.congr_fun_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    simp only
    have hn : (fun x => ‖if x < y then g x * f y else 0‖) =
        (Iio y).indicator (fun x => |g x| * |f y|) := by
      funext x; simp only [Set.indicator, mem_Iio]
      split_ifs <;> simp
    rw [hn, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      intervalIntegral.integral_of_le hy0.le, integral_Ioc_eq_integral_Ioo, integral_mul_const,
      mul_comm]

/-- **Triangle exchange.** `∫₀^∞ g(x) ∫_x^∞ f = ∫₀^∞ f(y) ∫₀^y g`, with both sides integrable. -/
theorem integral_triangle_swap {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hF : IntegrableOn (fun y => |f y| * ∫ x in (0 : ℝ)..y, |g x|) (Ioi 0)) :
    IntegrableOn (fun x => g x * ∫ y in Ioi x, f y) (Ioi 0) ∧
      IntegrableOn (fun y => f y * ∫ x in (0 : ℝ)..y, g x) (Ioi 0) ∧
      (∫ x in Ioi 0, g x * ∫ y in Ioi x, f y) = ∫ y in Ioi 0, f y * ∫ x in (0 : ℝ)..y, g x := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let K : ℝ → ℝ → ℝ := fun x y => if x < y then g x * f y else 0
  have hK : Integrable (Function.uncurry K) (μ.prod μ) := integrable_triangle hf hg hF
  have hL : ∀ x ∈ Ioi (0 : ℝ), g x * (∫ y in Ioi x, f y) = ∫ y in Ioi 0, K x y := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hind : (fun y => K x y) = (Ioi x).indicator (fun y => g x * f y) := by
      funext y; simp only [K, Set.indicator, mem_Ioi]
    rw [hind, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr hx0.le,
      integral_const_mul]
  have hR : ∀ y ∈ Ioi (0 : ℝ), f y * (∫ x in (0 : ℝ)..y, g x) = ∫ x in Ioi 0, K x y := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hind : (fun x => K x y) = (Iio y).indicator (fun x => g x * f y) := by
      funext x; simp only [K, Set.indicator, mem_Iio]
    rw [hind, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      intervalIntegral.integral_of_le hy0.le, integral_Ioc_eq_integral_Ioo, integral_mul_const,
      mul_comm]
  have hint1 : Integrable (fun x => ∫ y, K x y ∂μ) μ := hK.integral_prod_left
  have hint2 : Integrable (fun y => ∫ x, K x y ∂μ) μ := hK.integral_prod_right
  refine ⟨?_, ?_, ?_⟩
  · exact hint1.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => (hL x hx).symm))
  · exact hint2.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun y hy => (hR y hy).symm))
  · calc (∫ x in Ioi 0, g x * ∫ y in Ioi x, f y) = ∫ x, ∫ y, K x y ∂μ ∂μ :=
          setIntegral_congr_fun measurableSet_Ioi hL
      _ = ∫ y, ∫ x, K x y ∂μ ∂μ := integral_integral_swap hK
      _ = ∫ y in Ioi 0, f y * ∫ x in (0 : ℝ)..y, g x :=
          (setIntegral_congr_fun measurableSet_Ioi hR).symm

section Pairing

variable {P : ℝ → ℝ} {C ω : ℝ}

theorem integrableOn_exp_mul_of_abs_le (hP : Continuous P)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) {u : ℝ} (hu : ω < u) (c : ℝ) :
    IntegrableOn (fun t => Real.exp (-(u * t)) * P t) (Ioi c) := by
  have h0 : IntegrableOn (fun t => Real.exp (-(u * t)) * P t) (Ioi 0) := by
    have hdom : IntegrableOn (fun t => C * Real.exp ((ω - u) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul C
    refine hdom.mono' ((by fun_prop : Continuous fun t =>
      Real.exp (-(u * t)) * P t).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(u * t)) * |P t| ≤ Real.exp (-(u * t)) * (C * Real.exp (ω * |t|)) :=
          mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le
      _ = C * Real.exp ((ω - u) * t) := by
          rw [abs_of_pos ht0, mul_left_comm, ← Real.exp_add]; ring_nf
  have hc : IntegrableOn (fun t => Real.exp (-(u * t)) * P t) (Icc (min c 0) 0) :=
    (by fun_prop : Continuous fun t => Real.exp (-(u * t)) * P t).integrableOn_Icc
  refine (hc.union h0).mono_set ?_
  intro t ht
  by_cases h : t ≤ 0
  · left; exact ⟨le_trans (min_le_left _ _) (le_of_lt ht), h⟩
  · right; exact lt_of_not_ge h

theorem integral_exp_mul_shift_add (u b : ℝ) :
    ∫ a in Ioi 0, Real.exp (-(u * a)) * P (a + b) =
      Real.exp (u * b) * ∫ s in Ioi b, Real.exp (-(u * s)) * P s := by
  have h := setIntegral_Ioi_zero_comp_add (fun s => Real.exp (-(u * s)) * P s) b
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integral_exp_mul_shift_sub (hP : Continuous P) (heven : ∀ t, P (-t) = P t)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) {u : ℝ} (hu : ω < u) {b : ℝ} (hb0 : 0 ≤ b) :
    ∫ a in Ioi 0, Real.exp (-(u * a)) * P (a - b) =
      Real.exp (-(u * b)) *
        ((∫ s in (0 : ℝ)..b, Real.exp (u * s) * P s) + halfLineLaplace P u) := by
  have h := setIntegral_Ioi_zero_comp_add (fun s => Real.exp (-(u * s)) * P s) (-b)
  have hL : (∫ a in Ioi 0, Real.exp (-(u * a)) * P (a - b)) =
      Real.exp (-(u * b)) * ∫ a in Ioi 0, Real.exp (-(u * (a + -b))) * P (a + -b) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
    rw [← mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]
    congr 2
    ring
  rw [hL, h]
  congr 1
  have hint := integrableOn_exp_mul_of_abs_le hP hb hu (-b)
  rw [← Ioc_union_Ioi_eq_Ioi (neg_nonpos.2 hb0), setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self)
    (hint.mono_set (Ioi_subset_Ioi (neg_nonpos.2 hb0)))]
  congr 1
  rw [← intervalIntegral.integral_of_le (neg_nonpos.2 hb0)]
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := b)
    (fun s => Real.exp (-(u * s)) * P s)
  simp only [neg_zero] at hneg
  rw [← hneg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [heven, mul_neg, neg_neg]

theorem integrableOn_exp_mul_comp_add (hP : Continuous P)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) (hω : 0 ≤ ω) {u : ℝ} (hu : ω < u) (b : ℝ) :
    IntegrableOn (fun a => Real.exp (-(u * a)) * P (a + b)) (Ioi 0) := by
  have hC : 0 ≤ C := by
    have := hb 0
    have h2 := abs_nonneg (P 0)
    have h3 := Real.exp_pos (ω * |(0 : ℝ)|)
    nlinarith
  have hbd : ∀ a, |P (a + b)| ≤ (C * Real.exp (ω * |b|)) * Real.exp (ω * |a|) := by
    intro a
    refine (hb (a + b)).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    nlinarith [abs_add_le a b]
  exact integrableOn_exp_mul_of_abs_le (P := fun a => P (a + b)) (by fun_prop) hbd hu 0

theorem integrableOn_pairing_inner (hP : Continuous P)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) (hω : 0 ≤ ω) {u : ℝ} (hu : ω < u) (v b : ℝ) :
    IntegrableOn (fun a => Real.exp (-(u * a) - v * b) * (P (a + b) - P (a - b))) (Ioi 0) := by
  have h1 := integrableOn_exp_mul_comp_add hP hb hω hu b
  have h2 := integrableOn_exp_mul_comp_add hP hb hω hu (-b)
  refine IntegrableOn.congr_fun ((h1.sub h2).const_mul (Real.exp (-(v * b)))) (fun a _ => ?_)
    measurableSet_Ioi
  simp only [Pi.sub_apply, ← sub_eq_add_neg]
  rw [sub_eq_add_neg (-(u * a)), Real.exp_add]
  ring

/-- **Two-scale Laplace pairing.** For a continuous even `P` with `|P(t)| ≤ C e^{ω|t|}` and
`u, v > ω ≥ 0`,
`∫₀^∞∫₀^∞ e^{-ua-vb} [P(a+b) - P(a-b)] da db
  = ∫₀^∞ e^{-us} P(s) (∫₀^s e^{(u-v)x} dx) ds - (L(u) + L(v))/(u + v)`. -/
theorem laplacePairing (hP : Continuous P) (heven : ∀ t, P (-t) = P t)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) (hω : 0 ≤ ω) {u v : ℝ} (hu : ω < u) (hv : ω < v) :
    IntegrableOn (fun b => ∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * (P (a + b) - P (a - b)))
      (Ioi 0) ∧
    (∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * (P (a + b) - P (a - b))) =
      (∫ s in Ioi 0, Real.exp (-(u * s)) * P s * ∫ x in (0 : ℝ)..s, Real.exp ((u - v) * x)) -
        (halfLineLaplace P u + halfLineLaplace P v) / (u + v) := by
  have hC : 0 ≤ C := by
    have := hb 0
    have h2 := abs_nonneg (P 0)
    have h3 := Real.exp_pos (ω * |(0 : ℝ)|)
    nlinarith
  have huv : 0 < u + v := by linarith
  -- shifted profiles are integrable against `e^{-ua}`
  have hshift : ∀ b : ℝ, IntegrableOn (fun a => Real.exp (-(u * a)) * P (a + b)) (Ioi 0) ∧
      IntegrableOn (fun a => Real.exp (-(u * a)) * P (a - b)) (Ioi 0) := by
    intro b
    refine ⟨integrableOn_exp_mul_comp_add hP hb hω hu b, ?_⟩
    simpa only [← sub_eq_add_neg] using integrableOn_exp_mul_comp_add hP hb hω hu (-b)
  -- the inner integral in closed form
  have hinner : ∀ b ∈ Ioi (0 : ℝ),
      (∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * (P (a + b) - P (a - b))) =
        Real.exp ((u - v) * b) * (∫ s in Ioi b, Real.exp (-(u * s)) * P s) -
          Real.exp (-((u + v) * b)) * (∫ s in (0 : ℝ)..b, Real.exp (u * s) * P s) -
            Real.exp (-((u + v) * b)) * halfLineLaplace P u := by
    intro b hb0
    have hb0' : (0 : ℝ) ≤ b := le_of_lt hb0
    have hsplit : (fun a => Real.exp (-(u * a) - v * b) * (P (a + b) - P (a - b))) =
        fun a => Real.exp (-(v * b)) * (Real.exp (-(u * a)) * P (a + b)) -
          Real.exp (-(v * b)) * (Real.exp (-(u * a)) * P (a - b)) := by
      funext a
      rw [sub_eq_add_neg (-(u * a)), Real.exp_add]
      ring
    rw [hsplit, integral_sub ((hshift b).1.const_mul _) ((hshift b).2.const_mul _),
      integral_const_mul, integral_const_mul, integral_exp_mul_shift_add,
      integral_exp_mul_shift_sub hP heven hb hu hb0']
    have e1 : Real.exp (-(v * b)) * Real.exp (u * b) = Real.exp ((u - v) * b) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(v * b)) * Real.exp (-(u * b)) = Real.exp (-((u + v) * b)) := by
      rw [← Real.exp_add]; ring_nf
    rw [← mul_assoc, e1, ← mul_assoc, e2]
    ring
  -- the two triangle exchanges
  have hδ1 : 0 < min u v - ω := by
    rcases le_total u v with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hF1 : IntegrableOn (fun y => |Real.exp (-(u * y)) * P y| *
      ∫ x in (0 : ℝ)..y, |Real.exp ((u - v) * x)|) (Ioi 0) := by
    refine integrableOn_of_le_mul_exp (D := C) (δ := min u v - ω) ?_ hδ1 ?_
    · refine Continuous.continuousOn ?_
      have := intervalIntegral.continuous_primitive (μ := volume)
        (f := fun x => |Real.exp ((u - v) * x)|)
        (fun a b => (by fun_prop : Continuous fun x => |Real.exp ((u - v) * x)|).intervalIntegrable
          a b) 0
      fun_prop
    · intro y hy
      have hprim : (∫ x in (0 : ℝ)..y, |Real.exp ((u - v) * x)|) ≤
          Real.exp (max (u - v) 0 * y) * y := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y)
          (C := Real.exp (max (u - v) 0 * y)) (f := fun x => |Real.exp ((u - v) * x)|)
          (fun x hx => by
            rw [uIoc_of_le hy.le] at hx
            rw [Real.norm_eq_abs, abs_abs, abs_of_pos (Real.exp_pos _)]
            refine Real.exp_le_exp.mpr ?_
            have h1 : (u - v) * x ≤ max (u - v) 0 * x :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hx.1.le
            have h2 : max (u - v) 0 * x ≤ max (u - v) 0 * y :=
              mul_le_mul_of_nonneg_left hx.2 (le_max_right _ _)
            linarith)
        rw [sub_zero, abs_of_pos hy] at h
        exact (Real.le_norm_self _).trans h
      rw [abs_mul, abs_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hP' := hb y
      rw [abs_of_pos hy] at hP'
      have hnn : 0 ≤ ∫ x in (0 : ℝ)..y, |Real.exp ((u - v) * x)| :=
        intervalIntegral.integral_nonneg hy.le fun x _ => abs_nonneg _
      rw [abs_of_nonneg hnn]
      calc Real.exp (-(u * y)) * |P y| * ∫ x in (0 : ℝ)..y, |Real.exp ((u - v) * x)|
          ≤ Real.exp (-(u * y)) * (C * Real.exp (ω * y)) * (Real.exp (max (u - v) 0 * y) * y) := by
            gcongr
        _ = C * (y * Real.exp ((max (u - v) 0 - u + ω) * y)) := by
            rw [show (max (u - v) 0 - u + ω) * y = -(u * y) + ω * y + max (u - v) 0 * y by ring,
              Real.exp_add, Real.exp_add]
            ring
        _ ≤ C * (y * Real.exp (-((min u v - ω) * y))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr ?_) hy.le) hC
            have : max (u - v) 0 - u = -min u v := by
              rcases le_total u v with h | h
              · rw [min_eq_left h, max_eq_right (by linarith)]; ring
              · rw [min_eq_right h, max_eq_left (by linarith)]; ring
            nlinarith
  have hF2 : IntegrableOn (fun y => |Real.exp (-((u + v) * y))| *
      ∫ x in (0 : ℝ)..y, |Real.exp (u * x) * P x|) (Ioi 0) := by
    refine integrableOn_of_le_mul_exp (D := C) (δ := v - ω) ?_ (by linarith) ?_
    · refine Continuous.continuousOn ?_
      have := intervalIntegral.continuous_primitive (μ := volume)
        (f := fun x => |Real.exp (u * x) * P x|)
        (fun a b => (by fun_prop : Continuous fun x => |Real.exp (u * x) * P x|).intervalIntegrable
          a b) 0
      fun_prop
    · intro y hy
      have hprim : (∫ x in (0 : ℝ)..y, |Real.exp (u * x) * P x|) ≤
          C * Real.exp ((u + ω) * y) * y := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y)
          (C := C * Real.exp ((u + ω) * y)) (f := fun x => |Real.exp (u * x) * P x|)
          (fun x hx => by
            rw [uIoc_of_le hy.le] at hx
            rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            have hPx := hb x
            rw [abs_of_pos hx.1] at hPx
            calc Real.exp (u * x) * |P x| ≤ Real.exp (u * x) * (C * Real.exp (ω * x)) :=
                  mul_le_mul_of_nonneg_left hPx (Real.exp_pos _).le
              _ = C * Real.exp ((u + ω) * x) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf
              _ ≤ C * Real.exp ((u + ω) * y) := by
                  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
                  exact mul_le_mul_of_nonneg_left hx.2 (by linarith))
        rw [sub_zero, abs_of_pos hy] at h
        exact (Real.le_norm_self _).trans h
      have hnn : 0 ≤ ∫ x in (0 : ℝ)..y, |Real.exp (u * x) * P x| :=
        intervalIntegral.integral_nonneg hy.le fun x _ => abs_nonneg _
      rw [abs_mul, abs_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hnn]
      calc Real.exp (-((u + v) * y)) * ∫ x in (0 : ℝ)..y, |Real.exp (u * x) * P x|
          ≤ Real.exp (-((u + v) * y)) * (C * Real.exp ((u + ω) * y) * y) :=
            mul_le_mul_of_nonneg_left hprim (Real.exp_pos _).le
        _ = C * (y * Real.exp (-((v - ω) * y))) := by
            rw [show -((v - ω) * y) = -((u + v) * y) + (u + ω) * y by ring, Real.exp_add]
            ring
  obtain ⟨hI1, -, hE1⟩ := integral_triangle_swap (g := fun x => Real.exp ((u - v) * x))
    (f := fun y => Real.exp (-(u * y)) * P y) (by fun_prop) (by fun_prop) hF1
  obtain ⟨-, hI2, hE2⟩ := integral_triangle_swap (g := fun x => Real.exp (u * x) * P x)
    (f := fun y => Real.exp (-((u + v) * y))) (by fun_prop) (by fun_prop) hF2
  have hI3 : IntegrableOn (fun b => Real.exp (-((u + v) * b)) * halfLineLaplace P u) (Ioi 0) := by
    have := (integrableOn_exp_mul_Ioi (show -(u + v) < 0 by linarith) 0).mul_const
      (halfLineLaplace P u)
    refine IntegrableOn.congr_fun this (fun b _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have hI12 : IntegrableOn (fun b => Real.exp ((u - v) * b) *
      (∫ s in Ioi b, Real.exp (-(u * s)) * P s) -
        Real.exp (-((u + v) * b)) * (∫ s in (0 : ℝ)..b, Real.exp (u * s) * P s)) (Ioi 0) :=
    hI1.sub hI2
  refine ⟨(hI12.sub hI3).congr_fun (fun b hb => (hinner b hb).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_sub hI12 hI3,
    integral_sub hI1 hI2, hE1]
  -- evaluate the second triangle and the constant term
  have hE2' : (∫ y in Ioi 0, Real.exp (-((u + v) * y)) *
      ∫ x in (0 : ℝ)..y, Real.exp (u * x) * P x) = halfLineLaplace P v / (u + v) := by
    rw [← hE2, halfLineLaplace, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have hexp := integral_exp_mul_Ioi (show -(u + v) < 0 by linarith) x
    rw [show (∫ y in Ioi x, Real.exp (-((u + v) * y))) =
      ∫ y in Ioi x, Real.exp (-(u + v) * y) from by simp only [neg_mul], hexp]
    rw [show Real.exp (u * x) * P x * (-Real.exp (-(u + v) * x) / -(u + v)) =
      Real.exp (u * x) * Real.exp (-(u + v) * x) * P x / (u + v) by
        field_simp, ← Real.exp_add]
    congr 3
    ring
  have hE3 : (∫ b in Ioi 0, Real.exp (-((u + v) * b)) * halfLineLaplace P u) =
      halfLineLaplace P u / (u + v) := by
    rw [integral_mul_const]
    have hexp := integral_exp_mul_Ioi (show -(u + v) < 0 by linarith) 0
    simp only [mul_zero, Real.exp_zero] at hexp
    rw [show (∫ b in Ioi (0 : ℝ), Real.exp (-((u + v) * b))) =
      ∫ b in Ioi (0 : ℝ), Real.exp (-(u + v) * b) from by simp only [neg_mul], hexp]
    field_simp
  rw [hE2', hE3]
  ring

theorem integral_exp_mul_zero_to {κ : ℝ} (hκ : κ ≠ 0) (s : ℝ) :
    ∫ x in (0 : ℝ)..s, Real.exp (κ * x) = (Real.exp (κ * s) - 1) / κ := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun x => Real.exp (κ * x) / κ) (Real.exp (κ * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul κ).exp).div_const κ
    refine h.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun x => Real.exp (κ * x)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  ring

theorem setIntegral_Ioi_pos {f : ℝ → ℝ} (hint : IntegrableOn f (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < f x) : 0 < ∫ x in Ioi 0, f x := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => (hpos x hx).le)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsupp : Function.support f ∩ Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
    exact fun hx => (hpos x hx).ne'
  rw [hsupp, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- Off the diagonal the pairing is the divided difference
`(L(v) - L(u))/(u - v) - (L(u) + L(v))/(u + v)`. -/
theorem laplacePairing_of_ne (hP : Continuous P) (heven : ∀ t, P (-t) = P t)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) (hω : 0 ≤ ω) {u v : ℝ} (hu : ω < u) (hv : ω < v)
    (huv : u ≠ v) :
    (∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * (P (a + b) - P (a - b))) =
      (halfLineLaplace P v - halfLineLaplace P u) / (u - v) -
        (halfLineLaplace P u + halfLineLaplace P v) / (u + v) := by
  rw [(laplacePairing hP heven hb hω hu hv).2]
  congr 1
  have hne : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hIu := integrableOn_exp_mul_of_abs_le hP hb hu 0
  have hIv := integrableOn_exp_mul_of_abs_le hP hb hv 0
  rw [halfLineLaplace, halfLineLaplace, ← integral_sub hIv hIu, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [integral_exp_mul_zero_to hne]
  have : Real.exp (-(u * s)) * Real.exp ((u - v) * s) = Real.exp (-(v * s)) := by
    rw [← Real.exp_add]; ring_nf
  rw [← this]
  ring

theorem divided_difference_eq (Lu Lv : ℝ) {u v : ℝ} (huv : u ≠ v) (hpos : 0 < u + v) :
    (Lv - Lu) / (u - v) - (Lu + Lv) / (u + v) = 2 * (v * Lv - u * Lu) / (u ^ 2 - v ^ 2) := by
  have h1 : u - v ≠ 0 := sub_ne_zero.mpr huv
  have h2 : u + v ≠ 0 := hpos.ne'
  have h3 : u ^ 2 - v ^ 2 ≠ 0 := by
    rw [show u ^ 2 - v ^ 2 = (u - v) * (u + v) by ring]; exact mul_ne_zero h1 h2
  field_simp
  ring

/-- On the diagonal, `∫∫ e^{-u(a+b)} [P(a+b) - P(a-b)] = ∫₀^∞ s e^{-us} P(s) ds - L(u)/u`. -/
theorem laplacePairing_diag (hP : Continuous P) (heven : ∀ t, P (-t) = P t)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) (hω : 0 ≤ ω) {u : ℝ} (hu : ω < u) :
    (∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - u * b) * (P (a + b) - P (a - b))) =
      (∫ s in Ioi 0, s * (Real.exp (-(u * s)) * P s)) - halfLineLaplace P u / u := by
  rw [(laplacePairing hP heven hb hω hu hu).2]
  have hu0 : 0 < u := lt_of_le_of_lt hω hu
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [sub_self, zero_mul, Real.exp_zero, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, mul_one]
    ring
  · field_simp

theorem laplacePairing_pos (hP : Continuous P) (heven : ∀ t, P (-t) = P t)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) (hω : 0 ≤ ω) {u v : ℝ} (hu : ω < u) (hv : ω < v)
    (hK : ∀ a b, 0 < a → 0 < b → 0 < P (a + b) - P (a - b)) :
    0 < ∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * (P (a + b) - P (a - b)) := by
  refine setIntegral_Ioi_pos (laplacePairing hP heven hb hω hu hv).1 fun b hb0 => ?_
  exact setIntegral_Ioi_pos (integrableOn_pairing_inner hP hb hω hu v b) fun a ha =>
    mul_pos (Real.exp_pos _) (hK a b ha hb0)

/-- Differentiation of the Laplace transform under the integral sign. -/
theorem hasDerivAt_halfLineLaplace (hP : Continuous P) (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|))
    {u : ℝ} (hu : ω < u) :
    HasDerivAt (halfLineLaplace P) (-∫ t in Ioi 0, t * (Real.exp (-(u * t)) * P t)) u := by
  have hC : 0 ≤ C := by
    have := hb 0
    have h2 := abs_nonneg (P 0)
    have h3 := Real.exp_pos (ω * |(0 : ℝ)|)
    nlinarith
  set ε := (u - ω) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hbound : IntegrableOn (fun t => C * (t * Real.exp (-((u - ε - ω) * t)))) (Ioi 0) := by
    refine integrableOn_of_le_mul_exp (D := C) (δ := u - ε - ω)
      (by fun_prop : Continuous fun t => C * (t * Real.exp (-((u - ε - ω) * t)))).continuousOn
      (by rw [hε]; linarith) fun t ht => ?_
    rw [abs_of_nonneg (by positivity)]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (w t : ℝ) => Real.exp (-(w * t)) * P t)
    (F' := fun (w t : ℝ) => -(t * (Real.exp (-(w * t)) * P t)))
    (bound := fun t => C * (t * Real.exp (-((u - ε - ω) * t))))
    (Metric.ball_mem_nhds u hε0)
    (Eventually.of_forall fun w =>
      (by fun_prop : Continuous fun t => Real.exp (-(w * t)) * P t).aestronglyMeasurable)
    (integrableOn_exp_mul_of_abs_le hP hb hu 0)
    ((by fun_prop : Continuous fun t => -(t * (Real.exp (-(u * t)) * P t))).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht w hw => ?_))
    hbound
    (Eventually.of_forall fun t w _ => ?_)
  · rw [integral_neg] at key
    exact key.2
  · have ht0 : (0 : ℝ) < t := ht
    have hw' : u - ε < w := by
      have := (Metric.mem_ball.mp hw)
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (w - u)]
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_pos ht0, abs_of_pos (Real.exp_pos _)]
    have hPt := hb t
    rw [abs_of_pos ht0] at hPt
    calc t * (Real.exp (-(w * t)) * |P t|) ≤ t * (Real.exp (-(w * t)) * (C * Real.exp (ω * t))) := by
          gcongr
      _ = C * (t * Real.exp (-((w - ω) * t))) := by
          rw [show -((w - ω) * t) = -(w * t) + ω * t by ring, Real.exp_add]; ring
      _ ≤ C * (t * Real.exp (-((u - ε - ω) * t))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr ?_) ht0.le) hC
          nlinarith
  · have h := ((hasDerivAt_id w).mul_const t).neg.exp.mul_const (P t)
    refine h.congr_deriv ?_
    simp only [id, Pi.neg_apply]
    ring

/-- **Diagonal value.** At `u = v` the pairing equals the continuous derivative value
`-G'(u)/u` of the divided difference, `G(u) = u L(u)`. -/
theorem laplacePairing_diag_eq_deriv (hP : Continuous P) (heven : ∀ t, P (-t) = P t)
    (hb : ∀ t, |P t| ≤ C * Real.exp (ω * |t|)) (hω : 0 ≤ ω) {u : ℝ} (hu : ω < u) :
    (∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - u * b) * (P (a + b) - P (a - b))) =
      -deriv (fun w => w * halfLineLaplace P w) u / u := by
  have hu0 : 0 < u := lt_of_le_of_lt hω hu
  have hG : HasDerivAt (fun w => w * halfLineLaplace P w)
      (1 * halfLineLaplace P u + u * -∫ t in Ioi 0, t * (Real.exp (-(u * t)) * P t)) u :=
    (hasDerivAt_id' u).mul (hasDerivAt_halfLineLaplace hP hb hu)
  rw [laplacePairing_diag hP heven hb hω hu, hG.deriv]
  field_simp
  ring_nf

end Pairing

/-! ## The theta profile: Laplace pairing and the one-sided connection -/

theorem continuous_thetaLogProfile : Continuous thetaLogProfile := by
  have h : Continuous fun t => Θ (Real.exp t) :=
    continuous_evenKernel_zero_on.comp_continuous Real.continuous_exp fun t => Real.exp_pos t
  unfold thetaLogProfile
  fun_prop

theorem continuous_thetaLogTail : Continuous thetaLogTail := by
  have h : Continuous fun t => Θ (Real.exp t) :=
    continuous_evenKernel_zero_on.comp_continuous Real.continuous_exp fun t => Real.exp_pos t
  unfold thetaLogTail
  fun_prop

theorem thetaLogProfile_pos (t : ℝ) : 0 < thetaLogProfile t := by
  rw [thetaLogProfile_eq_add]
  exact add_pos (Real.exp_pos _) (thetaLogTail_pos t)

theorem thetaLogProfile_abs_eq (t : ℝ) : thetaLogProfile |t| = thetaLogProfile t := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, thetaLogProfile_neg]

/-- `|P(t)| ≤ (1 + R(0)) e^{|t|/4}`. -/
theorem abs_thetaLogProfile_le (t : ℝ) :
    |thetaLogProfile t| ≤ (1 + thetaLogTail 0) * Real.exp (1 / 4 * |t|) := by
  rw [abs_of_pos (thetaLogProfile_pos t), ← thetaLogProfile_abs_eq, thetaLogProfile_eq_add]
  have hR : thetaLogTail |t| ≤ thetaLogTail 0 :=
    strictAntiOn_thetaLogTail.antitoneOn (self_mem_Ici)
      (show |t| ∈ Ici (0 : ℝ) from abs_nonneg t) (abs_nonneg t)
  have h1 : 1 ≤ Real.exp (1 / 4 * |t|) := Real.one_le_exp (by positivity)
  have h0 := (thetaLogTail_pos 0).le
  rw [show |t| / 4 = 1 / 4 * |t| by ring]
  nlinarith

theorem abs_thetaLogTail_le (t : ℝ) :
    |thetaLogTail t| ≤ (2 + thetaLogTail 0) * Real.exp (1 / 4 * |t|) := by
  have h := abs_thetaLogProfile_le t
  have hR : thetaLogTail t = thetaLogProfile t - Real.exp (t / 4) := by
    rw [thetaLogProfile_eq_add]; ring
  have h1 : Real.exp (t / 4) ≤ Real.exp (1 / 4 * |t|) :=
    Real.exp_le_exp.mpr (by nlinarith [le_abs_self t])
  rw [hR]
  calc |thetaLogProfile t - Real.exp (t / 4)| ≤ |thetaLogProfile t| + |Real.exp (t / 4)| :=
        abs_sub _ _
    _ ≤ (1 + thetaLogTail 0) * Real.exp (1 / 4 * |t|) + Real.exp (1 / 4 * |t|) := by
        rw [abs_of_pos (Real.exp_pos _)]; linarith
    _ = (2 + thetaLogTail 0) * Real.exp (1 / 4 * |t|) := by ring

/-- **Two-scale Laplace pairing (7).** For distinct `u, v > 1/4`,
`∫₀^∞∫₀^∞ e^{-ua-vb} K(a,b) da db = (L(v)-L(u))/(u-v) - (L(u)+L(v))/(u+v)
  = 2 [G(v) - G(u)]/(u² - v²)`, `G(u) = u L(u)`. -/
theorem thetaLaplacePairing {u v : ℝ} (hu : 1 / 4 < u) (hv : 1 / 4 < v) (huv : u ≠ v) :
    (∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * deletionInversionKernel a b) =
      (halfLineLaplace thetaLogProfile v - halfLineLaplace thetaLogProfile u) / (u - v) -
        (halfLineLaplace thetaLogProfile u + halfLineLaplace thetaLogProfile v) / (u + v) :=
  laplacePairing_of_ne continuous_thetaLogProfile thetaLogProfile_neg abs_thetaLogProfile_le
    (by norm_num) hu hv huv

theorem thetaLaplacePairing_eq_G {u v : ℝ} (hu : 1 / 4 < u) (hv : 1 / 4 < v) (huv : u ≠ v) :
    (∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * deletionInversionKernel a b) =
      2 * (v * halfLineLaplace thetaLogProfile v - u * halfLineLaplace thetaLogProfile u) /
        (u ^ 2 - v ^ 2) := by
  rw [thetaLaplacePairing hu hv huv, divided_difference_eq _ _ huv (by linarith)]

/-- The pairing is strictly positive for all `u, v > 1/4`. -/
theorem thetaLaplacePairing_pos {u v : ℝ} (hu : 1 / 4 < u) (hv : 1 / 4 < v) :
    0 < ∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - v * b) * deletionInversionKernel a b :=
  laplacePairing_pos continuous_thetaLogProfile thetaLogProfile_neg abs_thetaLogProfile_le
    (by norm_num) hu hv fun a b ha hb => deletionInversionKernel_pos ha hb

/-- At `u = v` the pairing takes the continuous derivative value `-G'(u)/u`. -/
theorem thetaLaplacePairing_diag {u : ℝ} (hu : 1 / 4 < u) :
    (∫ b in Ioi 0, ∫ a in Ioi 0, Real.exp (-(u * a) - u * b) * deletionInversionKernel a b) =
      -deriv (fun w => w * halfLineLaplace thetaLogProfile w) u / u :=
  laplacePairing_diag_eq_deriv continuous_thetaLogProfile thetaLogProfile_neg
    abs_thetaLogProfile_le (by norm_num) hu

/-- `G(u) = u L(u)` decreases strictly on `(1/4, ∞)`. -/
theorem strictAntiOn_thetaLogLaplace_mul :
    StrictAntiOn (fun u => u * halfLineLaplace thetaLogProfile u) (Ioi (1 / 4)) := by
  intro u hu v hv huv
  have hu' : (1 : ℝ) / 4 < u := hu
  have hv' : (1 : ℝ) / 4 < v := hv
  have hpos := thetaLaplacePairing_pos hu' hv'
  rw [thetaLaplacePairing_eq_G hu' hv' huv.ne] at hpos
  have hden : u ^ 2 - v ^ 2 < 0 := by nlinarith
  have := (div_pos_iff.mp hpos)
  rcases this with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · simp only
    linarith

/-- The meromorphic continuation `L(s) = 1/(s - 1/4) + M_{2is}` of the Laplace transform. -/
def thetaLogLaplaceC (s : ℂ) : ℂ := 1 / (s - 1 / 4) + wardMellin (2 * I * s)

theorem wardExponent_two_I_mul (u : ℝ) : wardExponent (2 * I * u) = ((-u - 3 / 4 : ℝ) : ℂ) := by
  rw [wardExponent]
  push_cast
  linear_combination (u : ℂ) * I_sq

/-- `∫₀^∞ e^{-ut} R(t) dt = M_{2iu}` for real `u`. -/
theorem integral_exp_mul_thetaLogTail (u : ℝ) :
    (((∫ t in Ioi 0, Real.exp (-(u * t)) * thetaLogTail t : ℝ)) : ℂ) = wardMellin (2 * I * u) := by
  rw [wardMellin, ← integral_Ioi_exp_smul_comp, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [wardExponent_two_I_mul, ← Complex.ofReal_cpow (Real.exp_pos t).le,
    jacobiThetaSum_ofReal_eq_evenKernel, Complex.real_smul, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [thetaLogTail, ← Real.exp_mul, ← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- **Laplace–Mellin identity (8).** For `u > 1/4`, `L(u) = 1/(u - 1/4) + M_{2iu}`. -/
theorem thetaLogLaplace_eq {u : ℝ} (hu : 1 / 4 < u) :
    ((halfLineLaplace thetaLogProfile u : ℝ) : ℂ) = thetaLogLaplaceC u := by
  have hI1 : IntegrableOn (fun t => Real.exp ((1 / 4 - u) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hI2 := integrableOn_exp_mul_of_abs_le continuous_thetaLogTail abs_thetaLogTail_le hu 0
  have hsplit : halfLineLaplace thetaLogProfile u =
      (∫ t in Ioi 0, Real.exp ((1 / 4 - u) * t)) +
        ∫ t in Ioi 0, Real.exp (-(u * t)) * thetaLogTail t := by
    rw [halfLineLaplace, ← integral_add hI1 hI2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [thetaLogProfile_eq_add, mul_add, ← Real.exp_add]
    congr 2
    ring
  have hexp := integral_exp_mul_Ioi (show 1 / 4 - u < 0 by linarith) 0
  simp only [mul_zero, Real.exp_zero] at hexp
  have hval : (-1 / (1 / 4 - u) : ℝ) = 1 / (u - 1 / 4) := by
    have h1 : (1 / 4 - u : ℝ) ≠ 0 := by linarith
    have h2 : (u - 1 / 4 : ℝ) ≠ 0 := by linarith
    rw [div_eq_div_iff h1 h2]
    ring
  rw [hsplit, hexp, hval, Complex.ofReal_add, integral_exp_mul_thetaLogTail, thetaLogLaplaceC]
  push_cast
  ring

/-- The one-sided connection at `z = 2is` without the pole:
`H(2is) = (s + 1/4) + (s² - 1/16) M_{2is} - s Θ(1)`. -/
theorem thetaOneSidedConnection_two_I_mul (s : ℂ) :
    thetaOneSidedConnection (2 * I * s) =
      (s + 1 / 4) + (s ^ 2 - 1 / 16) * wardMellin (2 * I * s) - s * jacobiThetaSum 1 := by
  rw [thetaOneSidedConnection_eq_ward]
  linear_combination (s * (jacobiThetaSum 1 - 1) - s ^ 2 * wardMellin (2 * I * s)) * I_sq

/-- **Ward form of the connection (9).** `H(2is) = (s² - 1/16) L(s) - s Θ(1)` for `s ≠ 1/4`. -/
theorem thetaOneSidedConnection_eq_laplace {s : ℂ} (hs : s ≠ 1 / 4) :
    thetaOneSidedConnection (2 * I * s) =
      (s ^ 2 - 1 / 16) * thetaLogLaplaceC s - s * jacobiThetaSum 1 := by
  have hne : s - 1 / 4 ≠ 0 := sub_ne_zero.mpr hs
  have key : (s ^ 2 - 1 / 16) * (1 / (s - 1 / 4)) = s + 1 / 4 := by
    rw [mul_one_div, div_eq_iff hne]; ring
  rw [thetaOneSidedConnection_two_I_mul, thetaLogLaplaceC, mul_add, key]

/-- **Two-ended connection formula (10).** `Ξ(2is) = (s² - 1/16) [L(s) + L(-s)]`, `s ≠ ±1/4`. -/
theorem XiC_two_I_mul_eq_laplace {s : ℂ} (h1 : s ≠ 1 / 4) (h2 : s ≠ -(1 / 4)) :
    XiC (2 * I * s) = (s ^ 2 - 1 / 16) * (thetaLogLaplaceC s + thetaLogLaplaceC (-s)) := by
  have h2' : -s ≠ 1 / 4 := fun h => h2 (by rw [← h, neg_neg])
  rw [XiC_eq_thetaOneSidedConnection_add, show -(2 * I * s) = 2 * I * (-s) by ring,
    thetaOneSidedConnection_eq_laplace h1, thetaOneSidedConnection_eq_laplace h2']
  ring

end RHTower
