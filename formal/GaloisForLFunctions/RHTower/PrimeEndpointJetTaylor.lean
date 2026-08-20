import GaloisForLFunctions.RHTower.PrimeEndpointJetExpansion
import Mathlib

/-!
# Taylor data for the endpoint jet

The endpoint-jet expansion needs a test function split into its Taylor polynomial at the collapsed
endpoint plus a remainder vanishing to one higher order.  This module supplies that split for any
derivative tower:

* `abs_le_of_hasDerivAt_bound` — a function vanishing at `0` whose derivative is `≤ B u^j` is
  itself `≤ B u^{j+1}/(j+1)`;
* `tower_bound` — iterating that bound along a derivative tower;
* `jetTaylor` and `abs_sub_jetTaylor_le` — the Taylor polynomial of a tower and the remainder
  bound `A u^{M+1}/(M+1)!`;
* `exists_abs_primeBoundaryDefect_taylor_jet_le` — the card's endpoint-jet theorem for a smooth
  boundary test function vanishing at the endpoint.
-/

set_option maxHeartbeats 1600000

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## Iterated integration of a vanishing jet -/

theorem abs_le_of_hasDerivAt_bound {g g' : ℝ → ℝ} {B : ℝ} {j : ℕ} (_hB : 0 ≤ B)
    (hg0 : g 0 = 0)
    (hderiv : ∀ u : ℝ, HasDerivAt g (g' u) u)
    (hcont : Continuous g')
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |g' u| ≤ B * u ^ j) :
    ∀ u ∈ Icc (0 : ℝ) 1, |g u| ≤ B * u ^ (j + 1) / ((j : ℝ) + 1) := by
  intro u hu
  have hu0 : (0 : ℝ) ≤ u := hu.1
  have hftc : (∫ s in (0 : ℝ)..u, g' s) = g u - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hcont.intervalIntegrable _ _)
  rw [hg0, sub_zero] at hftc
  rw [← hftc]
  have hI1 : IntervalIntegrable (fun s : ℝ => |g' s|) volume 0 u :=
    (hcont.abs).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun s : ℝ => B * s ^ j) volume 0 u :=
    ((continuous_pow j).const_mul B).intervalIntegrable _ _
  calc |∫ s in (0 : ℝ)..u, g' s| ≤ ∫ s in (0 : ℝ)..u, |g' s| :=
        intervalIntegral.abs_integral_le_integral_abs hu0
    _ ≤ ∫ s in (0 : ℝ)..u, B * s ^ j := by
        refine intervalIntegral.integral_mono_on hu0 hI1 hI2 ?_
        intro s hs
        exact hbound s ⟨hs.1, le_trans hs.2 hu.2⟩
    _ = B * u ^ (j + 1) / ((j : ℝ) + 1) := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        rw [zero_pow (by omega)]
        ring

/-- **Iterated jet bound.**  A derivative tower of length `k` vanishing at the origin, whose top
derivative is bounded by `A` on `[0,1]`, has base bounded by `A u^k / k!`. -/
theorem tower_bound {A : ℝ} (hA : 0 ≤ A) :
    ∀ (k : ℕ) (g : ℕ → ℝ → ℝ),
      (∀ j < k, ∀ u : ℝ, HasDerivAt (g j) (g (j + 1) u) u) →
      (∀ j ≤ k, Continuous (g j)) →
      (∀ j < k, g j 0 = 0) →
      (∀ u ∈ Icc (0 : ℝ) 1, |g k u| ≤ A) →
      ∀ u ∈ Icc (0 : ℝ) 1, |g 0 u| ≤ A * u ^ k / ((k.factorial : ℕ) : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro g _ _ _ hbound u hu
      simpa using hbound u hu
  | succ n ih =>
      intro g hderiv hcont hzero hbound u hu
      have hshift := ih (fun j => g (j + 1))
        (fun j hj v => hderiv (j + 1) (by omega) v)
        (fun j hj => hcont (j + 1) (by omega))
        (fun j hj => hzero (j + 1) (by omega))
        (fun v hv => hbound v hv)
      have hfacpos : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos n
      have hstep := abs_le_of_hasDerivAt_bound (g := g 0) (g' := g 1)
        (B := A / ((n.factorial : ℕ) : ℝ)) (j := n)
        (by positivity) (hzero 0 (by omega)) (fun v => hderiv 0 (by omega) v)
        (hcont 1 (by omega))
        (fun v hv => by
          have h := hshift v hv
          calc |g 1 v| ≤ A * v ^ n / ((n.factorial : ℕ) : ℝ) := h
            _ = A / ((n.factorial : ℕ) : ℝ) * v ^ n := by ring)
      have h := hstep u hu
      refine h.trans_eq ?_
      have hfac : ((n + 1).factorial : ℕ) = (n + 1) * n.factorial := Nat.factorial_succ n
      rw [hfac]
      push_cast
      field_simp

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-! ## The Taylor polynomial of a derivative tower -/

/-- The order-`M` Taylor polynomial at the origin of a derivative tower. -/
def jetTaylor (f : ℕ → ℝ → ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (M + 1), f k 0 * u ^ k / ((k.factorial : ℕ) : ℝ)

theorem jetTaylor_zero_eq (f : ℕ → ℝ → ℝ) (M : ℕ) : jetTaylor f M 0 = f 0 0 := by
  simp only [jetTaylor]
  rw [Finset.sum_range_succ']
  have hzero : ∀ k ∈ Finset.range M,
      f (k + 1) 0 * (0 : ℝ) ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ) = 0 := by
    intro k _
    rw [zero_pow (by omega)]
    ring
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add]
  norm_num

theorem continuous_jetTaylor (f : ℕ → ℝ → ℝ) (M : ℕ) : Continuous (jetTaylor f M) := by
  have hfun : jetTaylor f M
      = fun u : ℝ => ∑ k ∈ Finset.range (M + 1), f k 0 * u ^ k / ((k.factorial : ℕ) : ℝ) := rfl
  rw [hfun]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_const.mul (continuous_pow k)).div_const _

theorem hasDerivAt_jetTaylor (f : ℕ → ℝ → ℝ) (M : ℕ) (u : ℝ) :
    HasDerivAt (jetTaylor f (M + 1)) (jetTaylor (fun j => f (j + 1)) M u) u := by
  have hterm : ∀ k ∈ Finset.range (M + 2),
      HasDerivAt (fun v : ℝ => f k 0 * v ^ k / ((k.factorial : ℕ) : ℝ))
        (f k 0 * ((k : ℝ) * u ^ (k - 1)) / ((k.factorial : ℕ) : ℝ)) u := by
    intro k _
    have hp : HasDerivAt (fun v : ℝ => v ^ k) ((k : ℝ) * u ^ (k - 1)) u := hasDerivAt_pow k u
    exact (hp.const_mul (f k 0)).div_const _
  have hsum0 := HasDerivAt.sum hterm
  have hfun : (∑ i ∈ Finset.range (M + 2), fun v : ℝ => f i 0 * v ^ i / ((i.factorial : ℕ) : ℝ))
      = jetTaylor f (M + 1) := by
    funext v
    simp only [Finset.sum_apply]
    rfl
  rw [hfun] at hsum0
  refine hsum0.congr_deriv ?_
  have hgoalfun : jetTaylor (fun j => f (j + 1)) M u
      = ∑ k ∈ Finset.range (M + 1), f (k + 1) 0 * u ^ k / ((k.factorial : ℕ) : ℝ) := rfl
  rw [hgoalfun, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfac : (((k + 1).factorial : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have hk1 : (k + 1 : ℕ) - 1 = k := by omega
  rw [hk1]
  have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-- **The Taylor remainder bound for a derivative tower.**  If the `(M+1)`-st derivative is
bounded by `A` on `[0,1]`, the remainder after the order-`M` Taylor polynomial is at most
`A u^{M+1}/(M+1)!`. -/
theorem abs_sub_jetTaylor_le {A : ℝ} (hA : 0 ≤ A) :
    ∀ (M : ℕ) (f : ℕ → ℝ → ℝ),
      (∀ j ≤ M, ∀ u : ℝ, HasDerivAt (f j) (f (j + 1) u) u) →
      (∀ j ≤ M + 1, Continuous (f j)) →
      (∀ u ∈ Icc (0 : ℝ) 1, |f (M + 1) u| ≤ A) →
      ∀ u ∈ Icc (0 : ℝ) 1,
        |f 0 u - jetTaylor f M u| ≤ A * u ^ (M + 1) / (((M + 1).factorial : ℕ) : ℝ) := by
  intro M
  induction M with
  | zero =>
      intro f hderiv hcont hbound u hu
      have hjt : ∀ v : ℝ, jetTaylor f 0 v = f 0 0 := by
        intro v
        have : jetTaylor f 0 v
            = ∑ k ∈ Finset.range 1, f k 0 * v ^ k / ((k.factorial : ℕ) : ℝ) := rfl
        rw [this, Finset.sum_range_one]
        norm_num
      have hderivg : ∀ v : ℝ,
          HasDerivAt (fun w : ℝ => f 0 w - jetTaylor f 0 w) (f 1 v) v := by
        intro v
        have hconst : (fun w : ℝ => f 0 w - jetTaylor f 0 w) = fun w : ℝ => f 0 w - f 0 0 := by
          funext w
          rw [hjt w]
        rw [hconst]
        exact (hderiv 0 (by omega) v).sub_const (f 0 0)
      have hg0 : (fun w : ℝ => f 0 w - jetTaylor f 0 w) 0 = 0 := by
        simp only
        rw [hjt 0]
        ring
      have hbnd : ∀ v ∈ Icc (0 : ℝ) 1, |f 1 v| ≤ A * v ^ 0 := by
        intro v hv
        simpa using hbound v hv
      have h := abs_le_of_hasDerivAt_bound (g := fun w : ℝ => f 0 w - jetTaylor f 0 w)
        (g' := f 1) (B := A) (j := 0) hA hg0 hderivg (hcont 1 (by omega)) hbnd u hu
      simpa using h
  | succ N ih =>
      intro f hderiv hcont hbound u hu
      have hshift := ih (fun j => f (j + 1))
        (fun j hj v => hderiv (j + 1) (by omega) v)
        (fun j hj => hcont (j + 1) (by omega))
        (fun v hv => hbound v hv)
      have hderivg : ∀ v : ℝ,
          HasDerivAt (fun w : ℝ => f 0 w - jetTaylor f (N + 1) w)
            ((fun w : ℝ => f 1 w - jetTaylor (fun j => f (j + 1)) N w) v) v := by
        intro v
        exact (hderiv 0 (by omega) v).sub (hasDerivAt_jetTaylor f N v)
      have hg0 : (fun w : ℝ => f 0 w - jetTaylor f (N + 1) w) 0 = 0 := by
        simp only
        rw [jetTaylor_zero_eq]
        ring
      have hfacpos : (0 : ℝ) < (((N + 1).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (N + 1)
      have hbnd : ∀ v ∈ Icc (0 : ℝ) 1,
          |(fun w : ℝ => f 1 w - jetTaylor (fun j => f (j + 1)) N w) v|
            ≤ A / (((N + 1).factorial : ℕ) : ℝ) * v ^ (N + 1) := by
        intro v hv
        have h := hshift v hv
        calc |(fun w : ℝ => f 1 w - jetTaylor (fun j => f (j + 1)) N w) v|
            ≤ A * v ^ (N + 1) / (((N + 1).factorial : ℕ) : ℝ) := h
          _ = A / (((N + 1).factorial : ℕ) : ℝ) * v ^ (N + 1) := by ring
      have hcontg : Continuous (fun w : ℝ => f 1 w - jetTaylor (fun j => f (j + 1)) N w) :=
        (hcont 1 (by omega)).sub (continuous_jetTaylor _ _)
      have h := abs_le_of_hasDerivAt_bound (g := fun w : ℝ => f 0 w - jetTaylor f (N + 1) w)
        (g' := fun w : ℝ => f 1 w - jetTaylor (fun j => f (j + 1)) N w)
        (B := A / (((N + 1).factorial : ℕ) : ℝ)) (j := N + 1)
        (by positivity) hg0 hderivg hcontg hbnd u hu
      refine h.trans_eq ?_
      have hfac : (((N + 1 + 1).factorial : ℕ) : ℝ)
          = ((N + 2 : ℕ) : ℝ) * (((N + 1).factorial : ℕ) : ℝ) := by
        rw [show N + 1 + 1 = (N + 1) + 1 from rfl, Nat.factorial_succ]
        push_cast
        ring
      rw [hfac]
      push_cast
      field_simp
      ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-- **`(6)`: the endpoint jet of a smooth boundary test function.**  For a test function with a
derivative tower of length `N+2` vanishing at the collapsed endpoint, the prime-harmonic boundary
defect is the jet `∑_{k ≤ N} (h^{(k+1)}(0)/(k+1)!) C_{k+1} / (log x)^{k+1}` up to
`O((log x)^{-N-2})`. -/
theorem exists_abs_primeBoundaryDefect_taylor_jet_le (N : ℕ) (f : ℕ → ℝ → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hderiv : ∀ j ≤ N + 1, ∀ u : ℝ, HasDerivAt (f j) (f (j + 1) u) u)
    (hcont : ∀ j ≤ N + 2, Continuous (f j))
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |f (N + 2) u| ≤ A)
    (hzero : f 0 0 = 0) :
    ∃ B X₀ : ℝ, 0 ≤ B ∧ 4 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      |primeBoundaryDefect (f 0) x
          - ∑ k ∈ Finset.range (N + 1),
              (f (k + 1) 0 / (((k + 1).factorial : ℕ) : ℝ))
                * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1)|
        ≤ B / (Real.log x) ^ (N + 2) := by
  classical
  set b : ℕ → ℝ := fun k => f (k + 1) 0 / (((k + 1).factorial : ℕ) : ℝ) with hb
  set r : ℝ → ℝ := fun u => f 0 u - jetTaylor f (N + 1) u with hr
  set r' : ℝ → ℝ := fun u => f 1 u - jetTaylor (fun j => f (j + 1)) N u with hr'
  have hfacpos : (0 : ℝ) < (((N + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (N + 1)
  have hfacpos2 : (0 : ℝ) < (((N + 2).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (N + 2)
  set A' : ℝ := A / (((N + 1).factorial : ℕ) : ℝ) with hA'
  have hA'nn : 0 ≤ A' := by positivity
  -- the Taylor polynomial is the jet polynomial
  have hpoly : ∀ u : ℝ, jetTaylor f (N + 1) u = ∑ k ∈ Finset.range (N + 1), b k * u ^ (k + 1) := by
    intro u
    have hval : jetTaylor f (N + 1) u
        = ∑ k ∈ Finset.range (N + 2), f k 0 * u ^ k / ((k.factorial : ℕ) : ℝ) := rfl
    rw [hval, Finset.sum_range_succ']
    have hfirst : f 0 0 * u ^ 0 / (((0 : ℕ).factorial : ℕ) : ℝ) = 0 := by
      rw [hzero]
      norm_num
    rw [hfirst, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb]
    ring
  -- remainder bounds
  have hrb : ∀ u ∈ Ioc (0 : ℝ) 1, |r u| ≤ A' * u ^ (N + 1 + 1) := by
    intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hu.1, hu.2⟩
    have h := abs_sub_jetTaylor_le hA (N + 1) f
      (fun j hj v => hderiv j hj v) (fun j hj => hcont j hj) hbound u huIcc
    have hle : A * u ^ (N + 2) / (((N + 2).factorial : ℕ) : ℝ) ≤ A' * u ^ (N + 1 + 1) := by
      rw [hA']
      have hfacle : (((N + 1).factorial : ℕ) : ℝ) ≤ (((N + 2).factorial : ℕ) : ℝ) := by
        have : (N + 1).factorial ≤ (N + 2).factorial :=
          Nat.factorial_le (by omega)
        exact_mod_cast this
      have hupow : (0 : ℝ) ≤ u ^ (N + 2) := pow_nonneg (le_of_lt hu.1) _
      rw [show N + 1 + 1 = N + 2 from rfl, div_mul_eq_mul_div, mul_comm A (u ^ (N + 2))]
      exact div_le_div_of_nonneg_left (mul_nonneg hupow hA) hfacpos hfacle
    exact h.trans hle
  have hrb' : ∀ u ∈ Ioc (0 : ℝ) 1, |r' u| ≤ A' * u ^ (N + 1) := by
    intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hu.1, hu.2⟩
    have h := abs_sub_jetTaylor_le hA N (fun j => f (j + 1))
      (fun j hj v => hderiv (j + 1) (by omega) v) (fun j hj => hcont (j + 1) (by omega))
      hbound u huIcc
    refine h.trans_eq ?_
    rw [hA']
    ring
  have hrderiv : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivAt r (r' u) u := by
    intro u _
    rw [hr, hr']
    exact (hderiv 0 (by omega) u).sub (hasDerivAt_jetTaylor f N u)
  have hrcont : ContinuousOn r' (Ioc (0 : ℝ) 1) := by
    refine Continuous.continuousOn ?_
    rw [hr']
    exact (hcont 1 (by omega)).sub (continuous_jetTaylor _ _)
  obtain ⟨B, X₀, hB, hX₀, hmain⟩ := exists_abs_primeBoundaryDefect_jet_le (N + 1) b A' hA'nn
  refine ⟨B, X₀, hB, hX₀, ?_⟩
  intro x hx
  have hfun : (fun u : ℝ => (∑ k ∈ Finset.range (N + 1), b k * u ^ (k + 1)) + r u) = f 0 := by
    funext u
    rw [hr, ← hpoly]
    ring
  have h := hmain r r' hrderiv hrcont hrb hrb' x hx
  rw [hfun] at h
  exact h

end

end RHTower
