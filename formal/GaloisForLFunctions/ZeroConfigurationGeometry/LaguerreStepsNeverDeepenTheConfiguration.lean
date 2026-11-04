import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Laguerre steps never deepen the configuration

A finite configuration in the coordinate `z = γ − iδ` is the zero set of a complex polynomial; its
depth is `max |Im z|`. The heat flow `e^{−tD²}` is the limit of the steps `1 − (t/n)D²`, and each
step factors as `(1 − cD)(1 + cD)`.

* **First-order steps keep the strip** (`rootsInStrip_add_smul_derivative`). If every root of `p`
  satisfies `|Im z| ≤ b`, so does every root of `p + c p'` (`c` real). At a new root `z` outside the
  strip, `p'/p(z) = Σ_k 1/(z − z_k)` would have imaginary part of one strict sign, while
  `p'/p(z) = −1/c` is real.
* **Heat steps keep the strip** (`rootsInStrip_heatStep`). `p − c² p'' = (1 − cD)(1 + cD)p` has all
  roots in the strip of `p`.

So no step of the discrete heat flow can push a point deeper than the deepest point of the
configuration: the maximal depth is pointwise non-increasing. The statement is sharp for single
steps (`heatStep_keeps_triple_edge_root`): a triple root on the edge of the strip survives a step. Together with the spread law of
`HeatTimeSpreadsTheConfiguration` (the total squared gap grows at a fixed rate) and the pair model
(`w² ↦ w² + 2t`), this is the repulsion picture of the de Bruijn–Newman flow in finite dimension.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- All roots of `p` lie in the horizontal strip `|Im z| ≤ b`. -/
def RootsInStrip (b : ℝ) (p : ℂ[X]) : Prop := ∀ z ∈ p.roots, |z.im| ≤ b

theorem im_one_div_sub_neg {x z : ℂ} (h : z.im < x.im) : (1 / (x - z)).im < 0 := by
  have hw : 0 < (x - z).im := by rw [Complex.sub_im]; linarith
  have hne : x - z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  rw [one_div, Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hw) (Complex.normSq_pos.mpr hne)

theorem im_one_div_sub_pos {x z : ℂ} (h : x.im < z.im) : 0 < (1 / (x - z)).im := by
  have hw : (x - z).im < 0 := by rw [Complex.sub_im]; linarith
  have hne : x - z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  rw [one_div, Complex.inv_im]
  exact div_pos (neg_pos.mpr hw) (Complex.normSq_pos.mpr hne)

theorem im_multiset_sum (s : Multiset ℂ) : s.sum.im = (s.map Complex.im).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

theorem multiset_sum_neg {s : Multiset ℝ} (hs : s ≠ 0) (h : ∀ x ∈ s, x < 0) : s.sum < 0 := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    rw [Multiset.sum_cons]
    by_cases h0 : s = 0
    · rw [h0, Multiset.sum_zero, add_zero]; exact h a (Multiset.mem_cons_self a s)
    · have := ih h0 fun x hx => h x (Multiset.mem_cons_of_mem hx)
      linarith [h a (Multiset.mem_cons_self a s)]

theorem multiset_sum_pos {s : Multiset ℝ} (hs : s ≠ 0) (h : ∀ x ∈ s, 0 < x) : 0 < s.sum := by
  have := multiset_sum_neg (s := s.map Neg.neg) (by simpa using hs)
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact neg_lt_zero.mpr (h y hy))
  rw [Multiset.sum_map_neg, Multiset.map_id'] at this
  linarith

/-- **First-order steps keep the strip.** -/
theorem rootsInStrip_add_smul_derivative {p : ℂ[X]} {b : ℝ} (hp : RootsInStrip b p) (c : ℝ)
    (hq : p + C (c : ℂ) * derivative p ≠ 0) : RootsInStrip b (p + C (c : ℂ) * derivative p) := by
  intro z hz
  have hroot : (p + C (c : ℂ) * derivative p).eval z = 0 := ((mem_roots hq).mp hz)
  rw [eval_add, eval_mul, eval_C] at hroot
  have hp0 : p ≠ 0 := fun h => hq (by rw [h, derivative_zero, mul_zero, add_zero])
  by_cases hpz : p.eval z = 0
  · exact hp z ((mem_roots hp0).mpr hpz)
  · -- logarithmic derivative over the roots
    set S := (p.roots.map fun w => 1 / (z - w)).sum with hS
    have hld := (IsAlgClosed.splits p).eval_derivative_eq_eval_mul_sum hpz
    rw [hld] at hroot
    have hcS : 1 + (c : ℂ) * S = 0 := by
      have : p.eval z * (1 + (c : ℂ) * S) = 0 := by rw [← hroot]; ring
      exact (mul_eq_zero.mp this).resolve_left hpz
    have hroots : p.roots ≠ 0 := fun h0 => by
      rw [hS, h0, Multiset.map_zero, Multiset.sum_zero, mul_zero, add_zero] at hcS
      exact one_ne_zero hcS
    have hc : (c : ℂ) ≠ 0 := fun h0 => by rw [h0, zero_mul, add_zero] at hcS; exact one_ne_zero hcS
    have hImS : S.im = 0 := by
      have h1 := congrArg Complex.im hcS
      simp only [Complex.add_im, Complex.one_im, zero_add, Complex.zero_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast (Complex.ofReal_ne_zero.mp hc))
    rw [abs_le]
    constructor
    · by_contra hlt
      push Not at hlt
      have hpos : 0 < S.im := by
        rw [hS, im_multiset_sum, Multiset.map_map]
        refine multiset_sum_pos (by simpa using hroots) fun x hx => ?_
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
        have := (abs_le.mp (hp w hw)).1
        exact im_one_div_sub_pos (by linarith)
      linarith
    · by_contra hlt
      push Not at hlt
      have hneg : S.im < 0 := by
        rw [hS, im_multiset_sum, Multiset.map_map]
        refine multiset_sum_neg (by simpa using hroots) fun x hx => ?_
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
        have := (abs_le.mp (hp w hw)).2
        exact im_one_div_sub_neg (by linarith)
      linarith

/-- A first-order step keeps a nonzero polynomial nonzero. -/
theorem add_smul_derivative_ne_zero {p : ℂ[X]} (hp : p ≠ 0) (c : ℂ) :
    p + C c * derivative p ≠ 0 := by
  intro h
  have hc := congrArg (fun q : ℂ[X] => q.coeff p.natDegree) h
  simp only [coeff_add, coeff_C_mul, coeff_derivative, coeff_zero] at hc
  rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul, mul_zero, add_zero] at hc
  exact hp (leadingCoeff_eq_zero.mp hc)

/-- **Heat steps keep the strip.** `p − c² p''` has all roots in the strip of `p`. -/
theorem rootsInStrip_heatStep {p : ℂ[X]} {b : ℝ} (hp : RootsInStrip b p) (hp0 : p ≠ 0) (c : ℝ) :
    RootsInStrip b (p - C ((c : ℂ) ^ 2) * derivative (derivative p)) := by
  have h1 := rootsInStrip_add_smul_derivative hp c (add_smul_derivative_ne_zero hp0 _)
  have hq0 := add_smul_derivative_ne_zero hp0 (c : ℂ)
  have h2 := rootsInStrip_add_smul_derivative h1 (-c)
    (by
      have := add_smul_derivative_ne_zero hq0 ((-c : ℝ) : ℂ)
      exact this)
  have heq : p + C (c : ℂ) * derivative p + C ((-c : ℝ) : ℂ) * derivative (p + C (c : ℂ) * derivative p) =
      p - C ((c : ℂ) ^ 2) * derivative (derivative p) := by
    simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, Complex.ofReal_neg,
      map_neg, map_pow]
    ring
  rwa [heq] at h2

/-- **Non-deepening is sharp for single steps.** A triple root on the edge of the strip survives every
heat step: for `p = (x − ib)³(x + ib)³`, the polynomial `p − c² p''` still vanishes at `ib`. A strict
contraction of the maximal depth therefore needs the continuum flow, where multiple roots split. -/
theorem heatStep_keeps_triple_edge_root (b c : ℝ) :
    ((((X - C (Complex.I * b)) ^ 3 * (X - C (-(Complex.I * b))) ^ 3 : ℂ[X]) -
      C ((c : ℂ) ^ 2) * derivative (derivative
        ((X - C (Complex.I * b)) ^ 3 * (X - C (-(Complex.I * b))) ^ 3))).IsRoot
        (Complex.I * b)) := by
  set p : ℂ[X] := (X - C (Complex.I * b)) ^ 3 * (X - C (-(Complex.I * b))) ^ 3
  have hdvd : (X - C (Complex.I * b)) ^ 3 ∣ p := dvd_mul_right _ _
  have h2 : (X - C (Complex.I * b)) ^ (3 - 2) ∣ derivative^[2] p :=
    pow_sub_dvd_iterate_derivative_of_pow_dvd 2 hdvd
  have hroot2 : (derivative (derivative p)).IsRoot (Complex.I * b) := by
    have h : (X - C (Complex.I * b)) ∣ derivative (derivative p) := by simpa using h2
    exact dvd_iff_isRoot.mp h
  have hroot : p.IsRoot (Complex.I * b) := by simp [p]
  simp only [IsRoot, eval_sub, eval_mul, eval_C] at hroot hroot2 ⊢
  rw [hroot, hroot2]; ring

end GaloisForLFunctions.ZeroConfigurationGeometry
