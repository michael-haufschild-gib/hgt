import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPositivePrimitives

/-!
# Reciprocal primitive, matched dilations and the quarter-age gap kernel

With `M_m` the repeated Borel primitives, `T` the smoothed profile and `G = M_1/2 - rT` the
positive primitive gap:

* `g(r) = rT(r) = M_2(r)/r = ∫₀¹ M_1(ur) du`, with `T(0) = 1/2`, `g(0) = 0`, `g'(0) = 1/2`,
  `g, g' ≥ 0` and `rg' ≥ g` on `r ≥ 0`.
* For every dilation `u > 0`, `∫₀ᵗ P(us)M_1(u(t-s)) ds = (tuM_1(ut) - 2M_2(ut))/u ≥ ν₁u³t⁴/24`;
  its average over `u ∈ [0,1]` is `A_dil(t) = ∑_{j≥1} 2j b_j t^{2j+2}/((2j+1)(2j+2)²) ≥ ν₁t⁴/96`.
* `P⋆g = A_dil + C_dil`, the mismatch `C_dil` being an explicit signed same-history integral; and
  `P⋆g = C₂(t)/t + (1/t)∫₀ᵗ D(s)(s²g'(t-s) - 2sg(t-s)) ds`, whose kernel is nonnegative for
  `s ≥ 2t/3`.
* `G(0) = G'(0) = 0`, `3G ≤ rG'` (strict for `r > 0`), the gap kernel
  `H_G(t,s) = sG'(t-s) - G(t-s) = ∑ b_j j (t-s)^{2j}((2j+1)s - (t-s))/((2j+1)(2j+2))` is
  positive on `[t/4, t)`, zero at `s = t`, negative at `s = 0`, and the quarter is sharp:
  `H_G(t,ct)/t³ → (ν₁/48)(1-c)²(4c-1) < 0` as `t ↓ 0` for every `c ∈ [0,1/4)`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped Interval
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "P" => liEvenCrossActualClockPrimitive
local notation "D" => liEvenCrossActualClockLogHistory
local notation "Dens" => liEvenCrossActualClockLogHistoryDensity
local notation "nu" => thetaCuspNormalizedEvenMoment
local notation "bc" => liEvenCrossActualClockBorelCoefficient
local notation "M" => liEvenCrossActualClockBorelPrimitive
local notation "G" => liEvenCrossActualClockPrimitiveScoreGap
local notation "Tc" => liClockThetaSmoothedBorelProfile

/-- The reciprocal primitive `g(r) = rT(r)`. -/
def liEvenCrossActualClockReciprocalPrimitive (r : ℝ) : ℝ := r*(Tc (r:ℂ)).re

/-- The matched-dilation history `A_dil(t) = ∫₀¹∫₀ᵗ P(us)M_1(u(t-s)) ds du`. -/
def liEvenCrossActualClockMatchedDilationHistory (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, ∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s))

/-- The dilation mismatch `C_dil(t) = ∫₀¹∫₀ᵗ (P(s) - P(us))M_1(u(t-s)) ds du`. -/
def liEvenCrossActualClockDilationHistoryMismatch (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, ∫ s in (0:ℝ)..t, (P s-P (u*s))*M 1 (u*(t-s))

/-- The gap-history kernel `H_G(t,s) = sG'(t-s) - G(t-s)`. -/
def liEvenCrossActualClockPrimitiveGapHistoryKernel (t s : ℝ) : ℝ :=
  s*deriv G (t-s) - G (t-s)

local notation "g" => liEvenCrossActualClockReciprocalPrimitive
local notation "Adil" => liEvenCrossActualClockMatchedDilationHistory
local notation "Cdil" => liEvenCrossActualClockDilationHistoryMismatch
local notation "HG" => liEvenCrossActualClockPrimitiveGapHistoryKernel

/-! ### Termwise differentiation of factorial-type power series -/

private theorem fg_pow_bound (k j : ℕ) : ((2*j+k : ℕ) : ℝ) ≤ (k+1)*3^j := by
  have h1 : (1:ℝ) + j*2 ≤ (1+2)^j := one_add_mul_le_pow (by norm_num) j
  have h2 : ((k:ℝ)+1)*(1+j*2) ≤ ((k:ℝ)+1)*3^j := by
    norm_num at h1 ⊢; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) j]

private theorem fg_series {k : ℕ} {c : ℕ → ℝ} {C κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ j, |c j| ≤ C*κ^j/(j.factorial:ℝ)) (r : ℝ) :
    HasDerivAt (fun x => ∑' j, c j*x^(2*j+k)) (∑' j, c j*((2*j+k:ℕ):ℝ)*r^(2*j+k-1)) r ∧
      Summable (fun j => c j*((2*j+k:ℕ):ℝ)*r^(2*j+k-1)) := by
  have hS1 : (1:ℝ) ≤ |r| + 2 := by linarith [abs_nonneg r]
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (by simpa using hc 0)
  have husum : Summable (fun j : ℕ => C*(k+1)*(|r|+2)^k*((3*κ*(|r|+2)^2)^j/(j.factorial:ℝ))) :=
    (Real.summable_pow_div_factorial _).mul_left _
  have hball : ∀ x ∈ Metric.ball (0:ℝ) (|r|+1), |x| ≤ |r| + 2 := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx; linarith
  have hbound : ∀ j : ℕ, ∀ y ∈ Metric.ball (0:ℝ) (|r|+1),
      ‖c j*((2*j+k:ℕ):ℝ)*y^(2*j+k-1)‖ ≤ C*(k+1)*(|r|+2)^k*((3*κ*(|r|+2)^2)^j/(j.factorial:ℝ)) := by
    intro j y hy
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast, norm_pow,
      Real.norm_eq_abs]
    have h3 : |y|^(2*j+k-1) ≤ (|r|+2)^(2*j+k) :=
      (pow_le_pow_left₀ (abs_nonneg y) (hball y hy) _).trans (pow_le_pow_right₀ hS1 (Nat.sub_le _ _))
    have hcj : 0 ≤ C*κ^j/(j.factorial:ℝ) := div_nonneg (mul_nonneg hC (pow_nonneg hκ _)) (by positivity)
    have e : C*(k+1)*(|r|+2)^k*((3*κ*(|r|+2)^2)^j/(j.factorial:ℝ)) =
        (C*κ^j/(j.factorial:ℝ))*(((k:ℝ)+1)*3^j)*(|r|+2)^(2*j+k) := by
      rw [mul_pow, mul_pow, ← pow_mul, pow_add]; ring
    rw [e]
    exact mul_le_mul (mul_le_mul (hc j) (fg_pow_bound k j) (Nat.cast_nonneg _) hcj) h3
      (pow_nonneg (abs_nonneg _) _) (mul_nonneg hcj (by positivity))
  have hr : r ∈ Metric.ball (0:ℝ) (|r|+1) := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith
  refine ⟨hasDerivAt_tsum_of_isPreconnected husum Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun j y _ => ?_) (fun j y hy => hbound j y hy)
    (Metric.mem_ball_self (by positivity)) ?_ hr, ?_⟩
  · have h := (hasDerivAt_pow (2*j+k) y).const_mul (c j)
    exact h.congr_deriv (by push_cast; ring)
  · refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial κ).mul_left C) fun j => ?_
    rw [norm_mul, Real.norm_eq_abs, norm_pow, norm_zero]
    calc |c j| *0^(2*j+k) ≤ |c j| *1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ le_rfl zero_le_one) (abs_nonneg _)
      _ ≤ C*(κ^j/(j.factorial:ℝ)) := by rw [mul_one, ← mul_div_assoc]; exact hc j
  · exact Summable.of_norm_bounded husum fun j => hbound j r hr

/-! ### Coefficients of `g` and `G` -/

private def gcoef (j : ℕ) : ℝ := nu j/(((2*j+2).factorial:ℝ)*((2*j).factorial:ℝ))
private def acoef (j : ℕ) : ℝ := bc j*(j:ℝ)/((2*(j:ℝ)+1)*(2*(j:ℝ)+2))

private theorem gcoef_nonneg (j : ℕ) : 0 ≤ gcoef j :=
  div_nonneg (thetaCuspNormalizedEvenMoment_pos j).le (by positivity)
private theorem acoef_nonneg (j : ℕ) : 0 ≤ acoef j :=
  div_nonneg (mul_nonneg (liEvenCrossActualClockBorelCoefficient_pos j).le (Nat.cast_nonneg j))
    (by positivity)
private theorem acoef_zero : acoef 0 = 0 := by simp [acoef]
private theorem acoef_one : acoef 1 = nu 1/48 := by
  simp only [acoef, liEvenCrossActualClockBorelCoefficient]; norm_num [Nat.factorial]; ring
private theorem acoef_two_pos : 0 < acoef 2 :=
  div_pos (mul_pos (liEvenCrossActualClockBorelCoefficient_pos 2) (by norm_num)) (by positivity)

private theorem gcoef_le (j : ℕ) : |gcoef j| ≤ 1*(32/303:ℝ)^j/(j.factorial:ℝ) := by
  rw [abs_of_nonneg (gcoef_nonneg j), one_mul]
  refine le_trans ?_ (liEvenCrossActualClockBorelCoefficient_le j)
  unfold gcoef liEvenCrossActualClockBorelCoefficient
  apply div_le_div_of_nonneg_left (thetaCuspNormalizedEvenMoment_pos j).le (by positivity)
  rw [sq]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le (by omega)) (by positivity)

private theorem acoef_le (j : ℕ) : |acoef j| ≤ 1*(32/303:ℝ)^j/(j.factorial:ℝ) := by
  rw [abs_of_nonneg (acoef_nonneg j), one_mul]
  refine le_trans ?_ (liEvenCrossActualClockBorelCoefficient_le j)
  unfold acoef
  have hb := (liEvenCrossActualClockBorelCoefficient_pos j).le
  rw [div_le_iff₀ (by positivity)]
  have hj : (j:ℝ) ≤ (2*(j:ℝ)+1)*(2*(j:ℝ)+2) := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  nlinarith

private theorem g_hasSum (r : ℝ) : HasSum (fun j => gcoef j*r^(2*j+1)) (g r) := by
  have h := (hasSum_liClockThetaSmoothedBorelProfile_re r).mul_left r
  refine h.congr_fun fun j => ?_
  unfold gcoef; rw [pow_succ]; ring

private theorem G_hasSum (r : ℝ) : HasSum (fun j => acoef j*r^(2*j+1)) (G r) := by
  refine (hasSum_liEvenCrossActualClockPrimitiveScoreGap r).congr_fun fun j => ?_
  unfold acoef; ring

private theorem g_eq : g = fun x => ∑' j, gcoef j*x^(2*j+1) :=
  funext fun x => (g_hasSum x).tsum_eq.symm
private theorem G_eq : G = fun x => ∑' j, acoef j*x^(2*j+1) :=
  funext fun x => (G_hasSum x).tsum_eq.symm

private theorem g_deriv (r : ℝ) :
    HasDerivAt g (∑' j, gcoef j*((2*j+1:ℕ):ℝ)*r^(2*j)) r ∧
      HasSum (fun j => gcoef j*((2*j+1:ℕ):ℝ)*r^(2*j)) (deriv g r) := by
  obtain ⟨h, hs⟩ := fg_series (k := 1) (by norm_num) gcoef_le r
  simp only [Nat.add_sub_cancel] at h hs
  rw [g_eq]
  exact ⟨h, h.deriv ▸ hs.hasSum⟩

private theorem G_deriv (r : ℝ) :
    HasDerivAt G (∑' j, acoef j*((2*j+1:ℕ):ℝ)*r^(2*j)) r ∧
      HasSum (fun j => acoef j*((2*j+1:ℕ):ℝ)*r^(2*j)) (deriv G r) := by
  obtain ⟨h, hs⟩ := fg_series (k := 1) (by norm_num) acoef_le r
  simp only [Nat.add_sub_cancel] at h hs
  rw [G_eq]
  exact ⟨h, h.deriv ▸ hs.hasSum⟩

/-! ### The reciprocal primitive -/

/-- **(F3)**  `g(r) = ∫₀¹ M_1(ur) du`, `M_2(r) = r g(r)`, and `g(r) = M_2(r)/r` for `r ≠ 0`. -/
theorem liEvenCrossActualClockReciprocalPrimitive_source (r : ℝ) :
    g r = (∫ u in (0:ℝ)..1, M 1 (u*r)) ∧ M 2 r = r*g r ∧ (r ≠ 0 → g r = M 2 r/r) := by
  have hM2 : M 2 r = r*g r := by
    have h1 := hasSum_liEvenCrossActualClockBorelPrimitive 2 r
    refine h1.unique (((g_hasSum r).mul_left r).congr_fun fun j => ?_)
    unfold gcoef; ring
  refine ⟨?_, hM2, fun hr => by rw [hM2]; field_simp⟩
  rcases eq_or_ne r 0 with rfl | hr
  · simp [liEvenCrossActualClockReciprocalPrimitive, liEvenCrossActualClockBorelPrimitive_origin]
  · rw [intervalIntegral.integral_comp_mul_right (M 1) hr, zero_mul, one_mul, smul_eq_mul]
    change g r = r⁻¹*M 2 r
    rw [hM2]; field_simp

/-- **(F3)**  `T(0) = 1/2`, `g(0) = 0`, `g'(0) = 1/2`, and on `r ≥ 0`: `g, g' ≥ 0`, `g ≤ rg'`. -/
theorem liEvenCrossActualClockReciprocalPrimitive_origin_nonneg :
    (Tc ((0:ℝ):ℂ)).re = 1/2 ∧ g 0 = 0 ∧ deriv g 0 = 1/2 ∧
      ∀ r : ℝ, 0 ≤ r → 0 ≤ g r ∧ 0 ≤ deriv g r ∧ g r ≤ r*deriv g r := by
  refine ⟨liClockThetaSmoothedBorelProfile_re_zero, by simp [liEvenCrossActualClockReciprocalPrimitive],
    ?_, fun r hr => ⟨(g_hasSum r).nonneg fun j => mul_nonneg (gcoef_nonneg j) (pow_nonneg hr _),
      (g_deriv r).2.nonneg fun j => mul_nonneg (mul_nonneg (gcoef_nonneg j) (Nat.cast_nonneg _))
        (pow_nonneg hr _), ?_⟩⟩
  · have h1 : HasSum (fun j => gcoef j*((2*j+1:ℕ):ℝ)*(0:ℝ)^(2*j))
        (gcoef 0*((2*0+1:ℕ):ℝ)*(0:ℝ)^(2*0)) :=
      hasSum_single 0 fun j hj => by simp [hj]
    rw [(g_deriv 0).2.unique h1]
    simp [gcoef, Nat.factorial]
  · have h := ((g_deriv r).2.mul_left r).sub (g_hasSum r)
    have hnn := h.nonneg fun j => by
      have e : r*(gcoef j*((2*j+1:ℕ):ℝ)*r^(2*j)) - gcoef j*r^(2*j+1) =
          gcoef j*(2*(j:ℝ))*r^(2*j+1) := by push_cast; ring
      rw [e]; exact mul_nonneg (mul_nonneg (gcoef_nonneg j) (by positivity)) (pow_nonneg hr _)
    linarith

/-! ### The gap degree law and the gap-history kernel -/

/-- **(F7b)**  `G'(0) = 0`; for `r ≥ 0`, `G' ≥ 0` and `3G ≤ rG'`, strictly for `r > 0`. -/
theorem liEvenCrossActualClockPrimitiveScoreGap_degree :
    deriv G 0 = 0 ∧ ∀ r : ℝ, 0 ≤ r →
      0 ≤ deriv G r ∧ 3*G r ≤ r*deriv G r ∧ (0 < r → 3*G r < r*deriv G r) := by
  refine ⟨?_, fun r hr => ?_⟩
  · have h1 : HasSum (fun j => acoef j*((2*j+1:ℕ):ℝ)*(0:ℝ)^(2*j))
        (acoef 0*((2*0+1:ℕ):ℝ)*(0:ℝ)^(2*0)) :=
      hasSum_single 0 fun j hj => by simp [hj]
    rw [(G_deriv 0).2.unique h1, acoef_zero]
    simp
  have h := ((G_deriv r).2.mul_left r).sub ((G_hasSum r).mul_left 3)
  have e : ∀ j : ℕ, r*(acoef j*((2*j+1:ℕ):ℝ)*r^(2*j)) - 3*(acoef j*r^(2*j+1)) =
      acoef j*(2*(j:ℝ)-2)*r^(2*j+1) := fun j => by push_cast; ring
  have hnn : ∀ j : ℕ, 0 ≤ acoef j*(2*(j:ℝ)-2)*r^(2*j+1) := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [acoef_zero]
    · have : (1:ℝ) ≤ j := by exact_mod_cast hj
      exact mul_nonneg (mul_nonneg (acoef_nonneg j) (by linarith)) (pow_nonneg hr _)
  simp only [e] at h
  refine ⟨(G_deriv r).2.nonneg fun j => mul_nonneg (mul_nonneg (acoef_nonneg j) (Nat.cast_nonneg _))
    (pow_nonneg hr _), by linarith [h.nonneg hnn], fun hr0 => ?_⟩
  have h2 := le_hasSum h 2 fun j _ => hnn j
  have hpos : 0 < acoef 2*(2*((2:ℕ):ℝ)-2)*r^(2*2+1) :=
    mul_pos (mul_pos acoef_two_pos (by norm_num)) (pow_pos hr0 _)
  linarith

/-- **(F8b)**  Complete row expansion
`H_G(t,s) = ∑ b_j j (t-s)^{2j}((2j+1)s - (t-s))/((2j+1)(2j+2))`. -/
theorem hasSum_liEvenCrossActualClockPrimitiveGapHistoryKernel (t s : ℝ) :
    HasSum (fun j : ℕ => bc j*(j:ℝ)*(t-s)^(2*j)*(((2*j+1:ℕ):ℝ)*s-(t-s))/
      (((2*j+1:ℕ):ℝ)*((2*j+2:ℕ):ℝ))) (HG t s) := by
  have h := ((G_deriv (t-s)).2.mul_left s).sub (G_hasSum (t-s))
  unfold liEvenCrossActualClockPrimitiveGapHistoryKernel
  refine h.congr_fun fun j => ?_
  unfold acoef
  push_cast
  field_simp
  ring

/-- **(F8a)**  `H_G(t,t) = 0`, `H_G(t,0) = -G(t) < 0`, and `H_G(t,s) > 0` for `t/4 ≤ s < t`. -/
theorem liEvenCrossActualClockPrimitiveGapHistoryKernel_sign {t : ℝ} (ht : 0 < t) :
    HG t t = 0 ∧ HG t 0 < 0 ∧ ∀ s : ℝ, t/4 ≤ s → s < t → 0 < HG t s := by
  obtain ⟨hG0', hdeg⟩ := liEvenCrossActualClockPrimitiveScoreGap_degree
  refine ⟨?_, ?_, fun s hs hst => ?_⟩
  · simp [liEvenCrossActualClockPrimitiveGapHistoryKernel, hG0',
      liEvenCrossActualClockPrimitiveScoreGap_zero]
  · simp only [liEvenCrossActualClockPrimitiveGapHistoryKernel, zero_mul, zero_sub, sub_zero,
      neg_lt_zero]
    exact liEvenCrossActualClockPrimitiveScoreGap_pos ht
  · unfold liEvenCrossActualClockPrimitiveGapHistoryKernel
    have hr : 0 < t - s := by linarith
    obtain ⟨hG', -, hstrict⟩ := hdeg (t-s) hr.le
    have h3 := hstrict hr
    have h4 : (t-s)*deriv G (t-s) ≤ (3*s)*deriv G (t-s) :=
      mul_le_mul_of_nonneg_right (by linarith) hG'
    linarith

private theorem acoef_summable : Summable acoef :=
  Summable.of_nonneg_of_le acoef_nonneg (fun j => by simpa [abs_of_nonneg (acoef_nonneg j)] using acoef_le j)
    (Real.summable_pow_div_factorial _)

private theorem acoef_deriv_summable : Summable (fun j => acoef j*((2*j+1:ℕ):ℝ)) := by
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (acoef_nonneg j) (Nat.cast_nonneg _))
    (fun j => ?_) (Real.summable_pow_div_factorial (32/303:ℝ))
  refine le_trans ?_ (liEvenCrossActualClockBorelCoefficient_le j)
  have hb := (liEvenCrossActualClockBorelCoefficient_pos j).le
  unfold acoef
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) j, mul_nonneg hb (Nat.cast_nonneg (α := ℝ) j)]

private theorem G_cubic_remainder {r : ℝ} (hr : |r| ≤ 1) :
    |G r - nu 1/48*r^3| ≤ (∑' j, acoef (j+2))*|r|^5 := by
  have hs2 := (hasSum_nat_add_iff' 2).mpr (G_hasSum r)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, acoef_zero, zero_mul,
    acoef_one] at hs2
  have hb : HasSum (fun j => acoef (j+2)*|r|^5) ((∑' j, acoef (j+2))*|r|^5) :=
    ((summable_nat_add_iff (f := acoef) 2).mpr acoef_summable).hasSum.mul_right _
  have h := hs2.norm_le_of_bounded hb fun j => by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (acoef_nonneg _), norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg r) hr (by omega))
      (acoef_nonneg _)
  rw [Real.norm_eq_abs] at h
  convert h using 2

private theorem G_deriv_remainder {r : ℝ} (hr : |r| ≤ 1) :
    |deriv G r - 3*(nu 1/48)*r^2| ≤ (∑' j, acoef (j+2)*((2*(j+2)+1:ℕ):ℝ))*|r|^4 := by
  have hs2 := (hasSum_nat_add_iff' 2).mpr (G_deriv r).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, acoef_zero, zero_mul,
    acoef_one] at hs2
  have hb : HasSum (fun j => acoef (j+2)*((2*(j+2)+1:ℕ):ℝ)*|r|^4)
      ((∑' j, acoef (j+2)*((2*(j+2)+1:ℕ):ℝ))*|r|^4) :=
    ((summable_nat_add_iff (f := fun j => acoef j*((2*j+1:ℕ):ℝ)) 2).mpr
      acoef_deriv_summable).hasSum.mul_right _
  have h := hs2.norm_le_of_bounded hb fun j => by
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (acoef_nonneg _), Real.norm_eq_abs,
      Nat.abs_cast, norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg r) hr (by omega))
      (mul_nonneg (acoef_nonneg _) (Nat.cast_nonneg _))
  rw [Real.norm_eq_abs] at h
  convert h using 2
  push_cast
  ring

/-- **(F8c)**  The quarter is sharp over all positive clocks: for `c ∈ [0, 1/4)`,
`H_G(t,ct)/t³ → (ν₁/48)(1-c)²(4c-1) < 0` as `t ↓ 0`. -/
theorem liEvenCrossActualClockPrimitiveGapHistoryKernel_quarter_sharp {c : ℝ} (hc : 0 ≤ c)
    (hcq : c < 1/4) :
    Tendsto (fun t : ℝ => HG t (c*t)/t^3) (𝓝[>] 0) (𝓝 ((nu 1/48)*(1-c)^2*(4*c-1))) ∧
      (nu 1/48)*(1-c)^2*(4*c-1) < 0 := by
  have hnu := thetaCuspNormalizedEvenMoment_pos 1
  refine ⟨?_, mul_neg_of_pos_of_neg (mul_pos (by positivity) (by nlinarith)) (by linarith)⟩
  set K1 := ∑' j, acoef (j+2)
  set K2 := ∑' j, acoef (j+2)*((2*(j+2)+1:ℕ):ℝ)
  have hK1 : 0 ≤ K1 := tsum_nonneg fun j => acoef_nonneg _
  have hK2 : 0 ≤ K2 := tsum_nonneg fun j => mul_nonneg (acoef_nonneg _) (Nat.cast_nonneg _)
  rw [← tendsto_sub_nhds_zero_iff]
  have hO : (fun t : ℝ => HG t (c*t)/t^3 - (nu 1/48)*(1-c)^2*(4*c-1)) =O[𝓝[>] 0]
      (fun t : ℝ => t^2) := by
    refine IsBigO.of_bound (c*K2+K1) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    have hr0 : 0 ≤ (1-c)*t := mul_nonneg (by linarith) ht.1.le
    have hr1 : |(1-c)*t| ≤ 1 := by
      rw [abs_of_nonneg hr0]; nlinarith [ht.2, ht.1]
    have hrt : (1-c)*t ≤ t := by nlinarith [ht.1]
    have e1 := G_cubic_remainder hr1
    have e2 := G_deriv_remainder hr1
    rw [abs_of_nonneg hr0] at e1 e2
    set E1 := G ((1-c)*t) - nu 1/48*((1-c)*t)^3
    set E2 := deriv G ((1-c)*t) - 3*(nu 1/48)*((1-c)*t)^2
    have hHG : HG t (c*t) = c*t*(3*(nu 1/48)*((1-c)*t)^2 + E2) - (nu 1/48*((1-c)*t)^3 + E1) := by
      simp only [liEvenCrossActualClockPrimitiveGapHistoryKernel, E1, E2,
        show t - c*t = (1-c)*t by ring]
      ring
    have ht3 : 0 < t^3 := pow_pos ht.1 3
    have ht0 : t ≠ 0 := ht.1.ne'
    have hdiff : HG t (c*t)/t^3 - (nu 1/48)*(1-c)^2*(4*c-1) = (c*t*E2 - E1)/t^3 := by
      rw [hHG]; field_simp; ring
    rw [hdiff, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos ht3,
      abs_of_nonneg (sq_nonneg t), div_le_iff₀ ht3]
    have hr4 : ((1-c)*t)^4 ≤ t^4 := pow_le_pow_left₀ hr0 hrt 4
    have hr5 : ((1-c)*t)^5 ≤ t^5 := pow_le_pow_left₀ hr0 hrt 5
    calc |c*t*E2 - E1| ≤ c*t*|E2| + |E1| := by
          calc |c*t*E2 - E1| ≤ |c*t*E2| + |E1| := abs_sub _ _
            _ = c*t*|E2| + |E1| := by rw [abs_mul, abs_of_nonneg (mul_nonneg hc ht.1.le)]
      _ ≤ c*t*(K2*t^4) + K1*t^5 :=
          add_le_add (mul_le_mul_of_nonneg_left (e2.trans (mul_le_mul_of_nonneg_left hr4 hK2))
            (mul_nonneg hc ht.1.le)) (e1.trans (mul_le_mul_of_nonneg_left hr5 hK1))
      _ = (c*K2+K1)*t^2*t^3 := by ring
  refine hO.trans_tendsto ?_
  have h : Tendsto (fun t : ℝ => t^2) (𝓝 0) (𝓝 (0^2)) := (continuous_pow 2).tendsto 0
  rw [zero_pow two_ne_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### Matched dilations and the reciprocal commutator -/

private theorem fg_P_cont : Continuous P := contDiff_liEvenCrossActualClockPrimitive.continuous
private theorem fg_D_cont : Continuous D :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_liEvenCrossActualClockLogHistory s).continuousAt
private theorem fg_M_cont (m : ℕ) : Continuous (M m) :=
  (contDiff_liEvenCrossActualClockBorelPrimitive m).continuous
private theorem fg_mul_density (s : ℝ) : s*Dens s = P s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [liEvenCrossActualClockPrimitive_origin_even.1]
  · rw [liEvenCrossActualClockLogHistoryDensity]; field_simp
/-- The reciprocal primitive is smooth. -/
theorem contDiff_liEvenCrossActualClockReciprocalPrimitive : ContDiff ℝ (⊤:ℕ∞) g := by
  have hd : Differentiable ℂ Tc := fun z => (liClockThetaScoreProfiles_analyticAt z).2.2.1.differentiableAt
  exact contDiff_id.mul hd.contDiff.real_of_complex
private theorem fg_g_deriv_cont : Continuous (deriv g) :=
  contDiff_liEvenCrossActualClockReciprocalPrimitive.continuous_deriv (by exact_mod_cast le_top)
private theorem fg_rect {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (a b c d : ℝ) :
    IntegrableOn (Function.uncurry F) (uIoc a b ×ˢ uIoc c d) :=
  (hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

/-- **(F4a)**  For every dilation `u > 0` and `t ≥ 0`,
`∫₀ᵗ P(us)M_1(u(t-s)) ds = (utM_1(ut) - 2M_2(ut))/u = tM_1(ut) - 2M_2(ut)/u ≥ ν₁u³t⁴/24`. -/
theorem liEvenCrossActualClockMatchedDilationHistory_scaled {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s))) = ((u*t)*M 1 (u*t) - 2*M 2 (u*t))/u ∧
      (∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s))) = t*M 1 (u*t) - 2*M 2 (u*t)/u ∧
      nu 1*u^3*t^4/24 ≤ ∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s)) := by
  have hut : 0 ≤ u*t := mul_nonneg hu.le ht
  have hconv := liEvenCrossActualClockPrimitive_convolution_primitive 1 hut
  have hlow := liEvenCrossActualClockPrimitive_convolution_primitive_lower 1 hut
  norm_num at hconv hlow
  have hsub : (∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s))) =
      u⁻¹*∫ v in (0:ℝ)..u*t, P v*M 1 (u*t - v) := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := t)
      (fun v => P v*M 1 (u*t - v)) hu.ne'
    rw [mul_zero, smul_eq_mul] at h
    rw [← h]
    congr 1; funext s; rw [mul_sub]
  have he : (∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s))) = ((u*t)*M 1 (u*t) - 2*M 2 (u*t))/u := by
    rw [hsub, hconv]; field_simp
  refine ⟨he, by rw [he]; field_simp, ?_⟩
  rw [hsub]
  have : nu 1*u^3*t^4/24 = u⁻¹*(nu 1*(u*t)^4/24) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by simpa using hlow) (inv_nonneg.2 hu.le)

private theorem fg_fact2 (m : ℕ) : ((m+2).factorial:ℝ) = (m+2)*(m+1)*(m.factorial:ℝ) := by
  rw [show m+2 = (m+1)+1 by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring

/-- **(F4b)**  `A_dil(t) = ∑_{j≥1} 2j b_j t^{2j+2}/((2j+1)(2j+2)²)` for `t ≥ 0`. -/
theorem hasSum_liEvenCrossActualClockMatchedDilationHistory {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun j : ℕ => (2:ℝ)*((j+1:ℕ):ℝ)*bc (j+1)*t^(2*(j+1)+2)/
      (((2*(j+1)+1:ℕ):ℝ)*((2*(j+1)+2:ℕ):ℝ)^2)) (Adil t) := by
  set F : ℕ → ℝ → ℝ := fun j u => (2*(j+1):ℝ)*nu (j+1)*u^(2*(j+1)+1)*t^(2*(j+1)+1+1)/
    (((2*(j+1)).factorial:ℝ)*((2*(j+1)+1+1).factorial:ℝ)) with hF
  have hser : ∀ u : ℝ, 0 < u → HasSum (fun j => F j u) (∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s))) := by
    intro u hu
    have h := (hasSum_liEvenCrossActualClockPrimitive_convolution_primitive 1
      (mul_nonneg hu.le ht)).mul_left u⁻¹
    rw [liEvenCrossActualClockPrimitive_convolution_primitive 1 (mul_nonneg hu.le ht)] at h
    have hval : u⁻¹*(u*t*M 1 (u*t) - (((1:ℕ):ℝ)+1)*M (1+1) (u*t)) =
        ∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s)) := by
      rw [(liEvenCrossActualClockMatchedDilationHistory_scaled hu ht).1]
      norm_num
      field_simp
    rw [hval] at h
    refine h.congr_fun fun j => ?_
    simp only [hF]
    rw [mul_pow, pow_succ u (2*(j+1)+1)]
    field_simp
  have hF1 : HasSum (fun j => F j 1) (∫ s in (0:ℝ)..t, P (1*s)*M 1 (1*(t-s))) := hser 1 one_pos
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := 1)
    (μ := volume) (F := F) (f := fun u => ∫ s in (0:ℝ)..t, P (u*s)*M 1 (u*(t-s)))
    (fun j _ => F j 1)
    (fun j => (by simp only [hF]; fun_prop : Continuous (F j)).aestronglyMeasurable)
    (fun j => Eventually.of_forall fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      simp only [hF, Real.norm_eq_abs]
      have hnum : 0 ≤ (2*(j+1):ℝ)*nu (j+1) :=
        mul_nonneg (by positivity) (thetaCuspNormalizedEvenMoment_pos _).le
      rw [abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg hnum (pow_nonneg hu.1.le _))
        (pow_nonneg ht _)) (by positivity))]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [one_pow, mul_one]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hnum
        (pow_le_one₀ hu.1.le hu.2)) (pow_nonneg ht _))
    (Eventually.of_forall fun _ _ => hF1.summable)
    intervalIntegrable_const
    (Eventually.of_forall fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact hser u hu.1)
  refine hint.congr_fun fun j => ?_
  simp only [hF]
  have e : ∀ u : ℝ, (2*(j+1):ℝ)*nu (j+1)*u^(2*(j+1)+1)*t^(2*(j+1)+1+1)/
      (((2*(j+1)).factorial:ℝ)*((2*(j+1)+1+1).factorial:ℝ)) =
      ((2*(j+1):ℝ)*nu (j+1)*t^(2*(j+1)+1+1)/
      (((2*(j+1)).factorial:ℝ)*((2*(j+1)+1+1).factorial:ℝ)))*u^(2*(j+1)+1) := fun u => by ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, integral_pow, fg_fact2 (2*(j+1))]
  unfold liEvenCrossActualClockBorelCoefficient
  push_cast
  field_simp
  ring

/-- **(F4b)**  `A_dil(t) ≥ ν₁t⁴/96` for `t ≥ 0`, and `A_dil(t) > 0` for `t > 0`. -/
theorem liEvenCrossActualClockMatchedDilationHistory_lower {t : ℝ} (ht : 0 ≤ t) :
    nu 1*t^4/96 ≤ Adil t ∧ (0 < t → 0 < Adil t) := by
  have hs := hasSum_liEvenCrossActualClockMatchedDilationHistory ht
  have hnn : ∀ j : ℕ, 0 ≤ (2:ℝ)*((j+1:ℕ):ℝ)*bc (j+1)*t^(2*(j+1)+2)/
      (((2*(j+1)+1:ℕ):ℝ)*((2*(j+1)+2:ℕ):ℝ)^2) := fun j =>
    div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (liEvenCrossActualClockBorelCoefficient_pos _).le) (pow_nonneg ht _)) (by positivity)
  have hle := le_hasSum hs 0 fun j _ => hnn j
  have e : (2:ℝ)*((0+1:ℕ):ℝ)*bc (0+1)*t^(2*(0+1)+2)/
      (((2*(0+1)+1:ℕ):ℝ)*((2*(0+1)+2:ℕ):ℝ)^2) = nu 1*t^4/96 := by
    simp only [liEvenCrossActualClockBorelCoefficient]; norm_num [Nat.factorial]; ring
  rw [e] at hle
  refine ⟨hle, fun ht0 => lt_of_lt_of_le ?_ hle⟩
  have := thetaCuspNormalizedEvenMoment_pos 1
  positivity

/-- **(F5)**  `P⋆g = A_dil + C_dil`, and the mismatch is the signed same-history integral
`C_dil(t) = ∫₀¹∫₀ᵗ (D(s) - D(us))(suB(u(t-s)) - M_1(u(t-s))) ds du`. -/
theorem liEvenCrossActualClockDilationHistoryMismatch_identity (t : ℝ) :
    (∫ s in (0:ℝ)..t, P s*g (t-s)) = Adil t + Cdil t ∧
      Cdil t = ∫ u in (0:ℝ)..1, ∫ s in (0:ℝ)..t,
        (D s - D (u*s))*(s*u*B (u*(t-s)) - M 1 (u*(t-s))) := by
  have hM1 : ∀ x, HasDerivAt (M 1) (B x) x := fun x =>
    hasDerivAt_liEvenCrossActualClockBorelPrimitive 0 x
  have hFc : Continuous (Function.uncurry fun s u : ℝ => P s*M 1 (u*(t-s))) :=
    (fg_P_cont.comp continuous_fst).mul ((fg_M_cont 1).comp (continuous_snd.mul
      (continuous_const.sub continuous_fst)))
  have hA : Continuous (Function.uncurry fun u s : ℝ => P (u*s)*M 1 (u*(t-s))) :=
    (fg_P_cont.comp (continuous_fst.mul continuous_snd)).mul ((fg_M_cont 1).comp
      (continuous_fst.mul (continuous_const.sub continuous_snd)))
  have hC : Continuous (Function.uncurry fun u s : ℝ => (P s - P (u*s))*M 1 (u*(t-s))) :=
    ((fg_P_cont.comp continuous_snd).sub (fg_P_cont.comp (continuous_fst.mul continuous_snd))).mul
      ((fg_M_cont 1).comp (continuous_fst.mul (continuous_const.sub continuous_snd)))
  have h1 : (∫ s in (0:ℝ)..t, P s*g (t-s)) =
      ∫ u in (0:ℝ)..1, ∫ s in (0:ℝ)..t, P s*M 1 (u*(t-s)) := by
    rw [← intervalIntegral_intervalIntegral_swap (fg_rect hFc 0 t 0 1)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [(liEvenCrossActualClockReciprocalPrimitive_source (t-s)).1,
      ← intervalIntegral.integral_const_mul]
  have h2 : Adil t + Cdil t = ∫ u in (0:ℝ)..1, ∫ s in (0:ℝ)..t, P s*M 1 (u*(t-s)) := by
    unfold liEvenCrossActualClockMatchedDilationHistory liEvenCrossActualClockDilationHistoryMismatch
    rw [← intervalIntegral.integral_add
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hA 0 t).intervalIntegrable _ _)
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hC 0 t).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [← intervalIntegral.integral_add
      (by exact ((fg_P_cont.comp (continuous_const.mul continuous_id)).mul ((fg_M_cont 1).comp
          (continuous_const.mul (continuous_const.sub continuous_id)))).intervalIntegrable _ _ :
        IntervalIntegrable (fun s => P (u*s)*M 1 (u*(t-s))) volume 0 t)
      (by exact ((fg_P_cont.sub (fg_P_cont.comp (continuous_const.mul continuous_id))).mul
          ((fg_M_cont 1).comp (continuous_const.mul (continuous_const.sub continuous_id)))).intervalIntegrable _ _ :
        IntervalIntegrable (fun s => (P s - P (u*s))*M 1 (u*(t-s))) volume 0 t)]
    congr 1; funext s; ring
  refine ⟨by rw [h1, h2], ?_⟩
  unfold liEvenCrossActualClockDilationHistoryMismatch
  refine intervalIntegral.integral_congr fun u _ => ?_
  have hE : ∀ s, HasDerivAt (fun s => s*(D s - D (u*s))) ((D s - D (u*s)) + (P s - P (u*s))) s := by
    intro s
    have hd1 := hasDerivAt_liEvenCrossActualClockLogHistory s
    have hd2 := (hasDerivAt_liEvenCrossActualClockLogHistory (u*s)).comp s
      ((hasDerivAt_id s).const_mul u)
    have h := (hasDerivAt_id' s).mul (hd1.sub hd2)
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply, Function.comp_apply, mul_one, one_mul]
    rw [← fg_mul_density s, ← fg_mul_density (u*s)]
    ring
  have hV : ∀ s, HasDerivAt (fun s => M 1 (u*(t-s))) (-(u*B (u*(t-s)))) s := by
    intro s
    have hl : HasDerivAt (fun s => u*(t-s)) (-u) s := by
      simpa using ((hasDerivAt_id s).const_sub t).const_mul u
    have h := (hM1 (u*(t-s))).comp s hl
    exact h.congr_deriv (by ring)
  have hEc : Continuous (fun s => D s - D (u*s)) :=
    fg_D_cont.sub (fg_D_cont.comp (continuous_const.mul continuous_id))
  have hPc : Continuous (fun s => P s - P (u*s)) :=
    fg_P_cont.sub (fg_P_cont.comp (continuous_const.mul continuous_id))
  have hVc : Continuous (fun s => M 1 (u*(t-s))) :=
    (fg_M_cont 1).comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hBc : Continuous (fun s => u*B (u*(t-s))) :=
    continuous_const.mul (continuous_liEvenCrossActualClockBorelKernel.comp
      (continuous_const.mul (continuous_const.sub continuous_id)))
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := t) (u := fun s => s*(D s - D (u*s))) (v := fun s => M 1 (u*(t-s)))
    (u' := fun s => (D s - D (u*s)) + (P s - P (u*s))) (v' := fun s => -(u*B (u*(t-s))))
    ((continuous_id.mul hEc).continuousOn) hVc.continuousOn (fun s _ => hE s) (fun s _ => hV s)
    ((hEc.add hPc).intervalIntegrable _ _) (hBc.neg.intervalIntegrable _ _)
  beta_reduce at hIBP
  simp only [sub_self, mul_zero, liEvenCrossActualClockBorelPrimitive_origin, one_ne_zero,
    if_false, zero_mul, sub_zero] at hIBP
  have i1 : IntervalIntegrable (fun s => (D s - D (u*s))*M 1 (u*(t-s))) volume 0 t :=
    (hEc.mul hVc).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => (P s - P (u*s))*M 1 (u*(t-s))) volume 0 t :=
    (hPc.mul hVc).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun s => (D s - D (u*s))*(s*u*B (u*(t-s)))) volume 0 t :=
    (hEc.mul ((continuous_id.mul continuous_const).mul (continuous_liEvenCrossActualClockBorelKernel.comp
      (continuous_const.mul (continuous_const.sub continuous_id))))).intervalIntegrable _ _
  have e1 : (∫ s in (0:ℝ)..t, ((D s - D (u*s)) + (P s - P (u*s)))*M 1 (u*(t-s))) =
      (∫ s in (0:ℝ)..t, (D s - D (u*s))*M 1 (u*(t-s))) +
        ∫ s in (0:ℝ)..t, (P s - P (u*s))*M 1 (u*(t-s)) := by
    rw [← intervalIntegral.integral_add i1 i2]; congr 1; funext s; ring
  have e2 : (∫ s in (0:ℝ)..t, s*(D s - D (u*s))*-(u*B (u*(t-s)))) =
      -∫ s in (0:ℝ)..t, (D s - D (u*s))*(s*u*B (u*(t-s))) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext s; ring
  have e3 : (∫ s in (0:ℝ)..t, (D s - D (u*s))*(s*u*B (u*(t-s)) - M 1 (u*(t-s)))) =
      (∫ s in (0:ℝ)..t, (D s - D (u*s))*(s*u*B (u*(t-s)))) -
        ∫ s in (0:ℝ)..t, (D s - D (u*s))*M 1 (u*(t-s)) := by
    rw [← intervalIntegral.integral_sub i3 i1]; congr 1; funext s; ring
  rw [e1, e2] at hIBP
  rw [e3]
  linarith

/-- **(F6)**  For `t > 0`, `P⋆g = C₂(t)/t + (1/t)∫₀ᵗ sP(s)g(t-s) ds` with `C₂ = tM_2 - 3M_3`,
`∫₀ᵗ sP(s)g(t-s) ds = ∫₀ᵗ D(s)(s²g'(t-s) - 2sg(t-s)) ds`, and the kernel is `≥ 0` on
`[2t/3, t]`. -/
theorem liEvenCrossActualClockReciprocalPrimitive_commutator {t : ℝ} (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, P s*g (t-s)) = (t*M 2 t - 3*M 3 t)/t +
        (1/t)*(∫ s in (0:ℝ)..t, s*P s*g (t-s)) ∧
      (∫ s in (0:ℝ)..t, s*P s*g (t-s)) =
        (∫ s in (0:ℝ)..t, D s*(s^2*deriv g (t-s) - 2*s*g (t-s))) ∧
      ∀ s ∈ Icc (2*t/3) t, 0 ≤ s^2*deriv g (t-s) - 2*s*g (t-s) := by
  have hgc : Continuous g := contDiff_liEvenCrossActualClockReciprocalPrimitive.continuous
  have hg1 : Continuous (fun s => g (t-s)) := hgc.comp (continuous_const.sub continuous_id)
  have hg2 : Continuous (fun s => deriv g (t-s)) :=
    fg_g_deriv_cont.comp (continuous_const.sub continuous_id)
  refine ⟨?_, ?_, fun s hs => ?_⟩
  · have hconv := liEvenCrossActualClockPrimitive_convolution_primitive 2 ht.le
    norm_num at hconv
    have hsplit : t*(∫ s in (0:ℝ)..t, P s*g (t-s)) =
        (∫ s in (0:ℝ)..t, P s*M 2 (t-s)) + ∫ s in (0:ℝ)..t, s*P s*g (t-s) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (by exact (fg_P_cont.mul ((fg_M_cont 2).comp (continuous_const.sub continuous_id))).intervalIntegrable _ _ :
          IntervalIntegrable (fun s => P s*M 2 (t-s)) volume 0 t)
        (by exact ((continuous_id.mul fg_P_cont).mul hg1).intervalIntegrable _ _ :
          IntervalIntegrable (fun s => s*P s*g (t-s)) volume 0 t)]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [(liEvenCrossActualClockReciprocalPrimitive_source (t-s)).2.1]
      ring
    rw [hconv] at hsplit
    field_simp
    linarith
  · have hu : ∀ s, HasDerivAt (fun s => s^2*D s) (2*s*D s + s*P s) s := by
      intro s
      have h := (hasDerivAt_pow 2 s).mul (hasDerivAt_liEvenCrossActualClockLogHistory s)
      refine h.congr_deriv ?_
      rw [← fg_mul_density s]; push_cast; ring
    have hv : ∀ s, HasDerivAt (fun s => g (t-s)) (-deriv g (t-s)) s := fun s =>
      ((contDiff_liEvenCrossActualClockReciprocalPrimitive.differentiable (by simp) (t-s)).hasDerivAt).comp_const_sub t s
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := 0) (b := t) (u := fun s => s^2*D s) (v := fun s => g (t-s))
      (u' := fun s => 2*s*D s + s*P s) (v' := fun s => -deriv g (t-s))
      (((continuous_pow 2).mul fg_D_cont).continuousOn) hg1.continuousOn
      (fun s _ => hu s) (fun s _ => hv s)
      ((((continuous_const.mul continuous_id).mul fg_D_cont).add
        (continuous_id.mul fg_P_cont)).intervalIntegrable _ _)
      (hg2.neg.intervalIntegrable _ _)
    beta_reduce at hIBP
    have hg0 : g 0 = 0 := by simp [liEvenCrossActualClockReciprocalPrimitive]
    simp only [sub_self, hg0, mul_zero, zero_pow two_ne_zero, zero_mul, sub_zero] at hIBP
    have i1 : IntervalIntegrable (fun s => 2*s*D s*g (t-s)) volume 0 t :=
      (((continuous_const.mul continuous_id).mul fg_D_cont).mul hg1).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun s => s*P s*g (t-s)) volume 0 t :=
      ((continuous_id.mul fg_P_cont).mul hg1).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun s => D s*(s^2*deriv g (t-s))) volume 0 t :=
      (fg_D_cont.mul ((continuous_pow 2).mul hg2)).intervalIntegrable _ _
    have e1 : (∫ s in (0:ℝ)..t, (2*s*D s + s*P s)*g (t-s)) =
        (∫ s in (0:ℝ)..t, 2*s*D s*g (t-s)) + ∫ s in (0:ℝ)..t, s*P s*g (t-s) := by
      rw [← intervalIntegral.integral_add i1 i2]; congr 1; funext s; ring
    have e2 : (∫ s in (0:ℝ)..t, s^2*D s*-deriv g (t-s)) =
        -∫ s in (0:ℝ)..t, D s*(s^2*deriv g (t-s)) := by
      rw [← intervalIntegral.integral_neg]; congr 1; funext s; ring
    have e3 : (∫ s in (0:ℝ)..t, D s*(s^2*deriv g (t-s) - 2*s*g (t-s))) =
        (∫ s in (0:ℝ)..t, D s*(s^2*deriv g (t-s))) - ∫ s in (0:ℝ)..t, 2*s*D s*g (t-s) := by
      rw [← intervalIntegral.integral_sub i3 i1]; congr 1; funext s; ring
    rw [e1, e2] at hIBP
    rw [e3]
    linarith
  · obtain ⟨-, -, -, hg⟩ := liEvenCrossActualClockReciprocalPrimitive_origin_nonneg
    have hr : 0 ≤ t - s := by linarith [hs.2]
    obtain ⟨-, hg', hrg⟩ := hg (t-s) hr
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have h2r : 2*(t-s) ≤ s := by linarith [hs.1]
    have h1 : 2*((t-s)*deriv g (t-s)) ≤ s*deriv g (t-s) := by nlinarith
    nlinarith

end
end RHTower
