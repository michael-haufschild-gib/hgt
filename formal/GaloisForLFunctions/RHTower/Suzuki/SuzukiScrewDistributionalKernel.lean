import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewDisjointCrossCoupling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The regular screw kernel is the distributional `-g''` on atom-free intervals

The restricted Weil kernel of Suzuki's screw function is `K = -g''` in the distributional sense.
Off the prime-power atoms `g` is genuinely twice differentiable with `g'' = -K`, and on an atom-free
interval the arithmetic hinge sum is not merely locally affine but **globally** affine, because every
atom then lies outside the interval.  Consequently `g` differs from a smooth function by one affine
function there, and two integrations by parts turn the distributional pairing into the ordinary
integral against the regular kernel:

```text
-∫ g φ'' = ∫ K φ
```

for every twice differentiable `φ` whose value and derivative vanish at both endpoints of a compact
subinterval.  This is the identity that licenses treating the restricted Weil form as the ordinary
double integral `∫∫ K (x - y) f y h x` whenever the support difference avoids `0` and every atom.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory intervalIntegral

/-! ## Global affineness of the hinge sum on an atom-free interval -/

/-- **On an atom-free open interval the prime-power hinge sum is a single affine function.**  Every
atom `log n` lies outside the interval, so the index set `{n : log n ≤ s}` does not vary. -/
theorem exists_affine_screwPrimeSum_Ioo {α β : ℝ}
    (hfree : ∀ s ∈ Ioo α β, ∀ n : ℕ, 2 ≤ n → s ≠ Real.log n) :
    ∃ A B : ℝ, ∀ s ∈ Ioo α β, screwPrimeSum s = A * s - B := by
  classical
  set N : ℕ := ⌊Real.exp β⌋₊ with hN
  set S : Finset ℕ := (Finset.Icc 2 N).filter (fun n => Real.log n ≤ α) with hS
  refine ⟨∑ n ∈ S, screwPrimeWeight n, ∑ n ∈ S, screwPrimeWeight n * Real.log n, ?_⟩
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hsN : ⌊Real.exp s⌋₊ ≤ N := Nat.floor_mono (Real.exp_le_exp.mpr hs2.le)
  have hSsub : S ⊆ Finset.Icc 2 N := Finset.filter_subset _ _
  have hin : ∀ n ∈ S, screwPrimeWeight n * max 0 (s - Real.log n)
      = screwPrimeWeight n * (s - Real.log n) := by
    intro n hn
    have hle : Real.log n ≤ α := (Finset.mem_filter.mp hn).2
    rw [max_eq_right (by linarith)]
  have hout : ∀ n ∈ Finset.Icc 2 N, n ∉ S → screwPrimeWeight n * max 0 (s - Real.log n) = 0 := by
    intro n hn hnot
    have hgt : α < Real.log n := by
      by_contra hle
      exact hnot (Finset.mem_filter.mpr ⟨hn, not_lt.mp hle⟩)
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hβ : β ≤ Real.log n := by
      by_contra hlt
      exact hfree (Real.log n) ⟨hgt, not_le.mp hlt⟩ n hn2 rfl
    rw [max_eq_left (by linarith), mul_zero]
  calc screwPrimeSum s
      = ∑ n ∈ Finset.Icc 2 N, screwPrimeWeight n * max 0 (s - Real.log n) :=
        screwPrimeSum_eq_sum_max hsN
    _ = ∑ n ∈ S, screwPrimeWeight n * max 0 (s - Real.log n) := (Finset.sum_subset hSsub hout).symm
    _ = ∑ n ∈ S, screwPrimeWeight n * (s - Real.log n) := Finset.sum_congr rfl hin
    _ = (∑ n ∈ S, screwPrimeWeight n) * s - ∑ n ∈ S, screwPrimeWeight n * Real.log n := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun n _ => by ring

/-! ## The first derivative as an explicit function -/

/-- The first derivative of Suzuki's screw function on an atom-free interval whose hinge slope
is `A`. -/
def screwFnDeriv (c₁ A : ℝ) (t : ℝ) : ℝ :=
  -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)) + A - c₁ / 2 + screwLerchTail₁ t

theorem hasDerivAt_screwFn_Ioo (c₁ c₀ A B : ℝ) {α β : ℝ} (hα : 0 < α)
    (haff : ∀ r ∈ Ioo α β, screwPrimeSum r = A * r - B) {s : ℝ} (hs : s ∈ Ioo α β) :
    HasDerivAt (screwFn c₁ c₀) (screwFnDeriv c₁ A s) s := by
  have hspos : 0 < s := lt_trans hα hs.1
  have hIoo : Ioo α β ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs
  have hhinge : HasDerivAt screwPrimeSum A s := by
    have haffs : HasDerivAt (fun r : ℝ => A * r - B) A s := by
      simpa using ((hasDerivAt_id s).const_mul A).sub_const B
    exact haffs.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hIoo fun r hr => haff r hr)
  have hlin : HasDerivAt (fun r : ℝ => c₁ / 2 * r) (c₁ / 2) s := by
    simpa using (hasDerivAt_id s).const_mul (c₁ / 2)
  have htail : HasDerivAt screwLerchTail (screwLerchTail₁ s) s := hasDerivAt_screwLerchTail hspos
  exact ((((hasDerivAt_screwExpBlock s).fun_add hhinge).fun_sub hlin).sub_const c₀).fun_add htail

/-- **The second derivative in explicit-function form**: the derivative of `screwFnDeriv` is
`-K` everywhere on `(0, ∞)`, with no atom condition, because `screwFnDeriv` is smooth. -/
theorem hasDerivAt_screwFnDeriv (c₁ A : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (screwFnDeriv c₁ A) (-screwRegularKernel t) t := by
  have h := (((((hasDerivAt_exp_half t).const_mul (-2 : ℝ)).fun_add
    ((hasDerivAt_exp_neg_half t).const_mul (2 : ℝ))).add_const A).sub_const
    (c₁ / 2)).fun_add (hasDerivAt_screwLerchTail₁ ht)
  have hval : (-2 : ℝ) * (Real.exp (t / 2) * (1 / 2))
        + 2 * (Real.exp (-(t / 2)) * (-(1 / 2))) + screwLerchTail₂ t
      = -screwRegularKernel t := by
    rw [screwRegularKernel_eq_tailForm ht, screwLerchTail₂_eq ht]
    ring
  rw [hval] at h
  exact h

theorem continuousOn_screwFnDeriv (c₁ A : ℝ) : ContinuousOn (screwFnDeriv c₁ A) (Ioi 0) :=
  fun t ht => ((hasDerivAt_screwFnDeriv c₁ A (ht : 0 < t)).continuousAt).continuousWithinAt

/-! ## The distributional identity -/

/-- **`K = -g''` in the distributional sense on an atom-free interval.**  For every compact
subinterval `[a,b]` of an atom-free `(α, β) ⊆ (0, ∞)` and every twice differentiable test function
whose value and derivative vanish at `a` and `b`,

```text
-∫ g φ'' = ∫ K φ.
```
-/
theorem neg_integral_screwFn_mul_secondDeriv (c₁ c₀ : ℝ) {α β a b : ℝ}
    (hα : 0 < α) (hab : a ≤ b) (haα : α < a) (hbβ : b < β)
    (hfree : ∀ s ∈ Ioo α β, ∀ n : ℕ, 2 ≤ n → s ≠ Real.log n)
    (φ φ' φ'' : ℝ → ℝ)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Icc a b, HasDerivAt φ' (φ'' x) x)
    (hφ''int : IntervalIntegrable φ'' volume a b)
    (hφa : φ a = 0) (hφb : φ b = 0) (hφ'a : φ' a = 0) (hφ'b : φ' b = 0) :
    -∫ x in a..b, screwFn c₁ c₀ x * φ'' x = ∫ x in a..b, screwRegularKernel x * φ x := by
  obtain ⟨A, B, haff⟩ := exists_affine_screwPrimeSum_Ioo hfree
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hsub : Icc a b ⊆ Ioo α β := fun x hx =>
    ⟨lt_of_lt_of_le haα hx.1, lt_of_le_of_lt hx.2 hbβ⟩
  have hxpos : ∀ x ∈ Icc a b, 0 < x := fun x hx => lt_trans hα (hsub hx).1
  have hg : ∀ x ∈ uIcc a b, HasDerivAt (screwFn c₁ c₀) (screwFnDeriv c₁ A x) x := by
    rw [huIcc]
    exact fun x hx => hasDerivAt_screwFn_Ioo c₁ c₀ A B hα haff (hsub hx)
  have hg' : ∀ x ∈ uIcc a b, HasDerivAt (screwFnDeriv c₁ A) (-screwRegularKernel x) x := by
    rw [huIcc]
    exact fun x hx => hasDerivAt_screwFnDeriv c₁ A (hxpos x hx)
  have hφIcc : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x := by rw [huIcc]; exact hφ
  have hφ'Icc : ∀ x ∈ uIcc a b, HasDerivAt φ' (φ'' x) x := by rw [huIcc]; exact hφ'
  have hg'int : IntervalIntegrable (screwFnDeriv c₁ A) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact fun x hx =>
      ((hasDerivAt_screwFnDeriv c₁ A (hxpos x hx)).continuousAt).continuousWithinAt
  have hKint : IntervalIntegrable (fun x => -screwRegularKernel x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact (continuousOn_screwRegularKernel.mono fun x hx => hxpos x hx).neg
  have hφ'int : IntervalIntegrable φ' volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact fun x hx => ((hφ' x hx).continuousAt).continuousWithinAt
  have hIBP1 := integral_mul_deriv_eq_deriv_mul hg hφ'Icc hg'int hφ''int
  have hIBP2 := integral_mul_deriv_eq_deriv_mul hg' hφIcc hKint hφ'int
  have hneg : (∫ x in a..b, -screwRegularKernel x * φ x)
      = -∫ x in a..b, screwRegularKernel x * φ x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [hφ'a, hφ'b] at hIBP1
  rw [hφa, hφb, hneg] at hIBP2
  simp only [mul_zero, sub_zero, zero_sub, sub_neg_eq_add, zero_add] at hIBP1 hIBP2
  linarith [hIBP1, hIBP2]

end GaloisForLFunctions.RHTower

end
