import GaloisForLFunctions.RHTower.Sieve.FibreKernelUniform

/-!
# The fibre kernel is exactly an interval count

`fibre_kernel_subset_Icc` gives one inclusion; with the dyadic constraint `√x ≤ a ≤ 2√x` of
`outerBlock` folded into the endpoints the inclusion becomes an equality:

```text
{ a ∈ outerBlock : m, n ∈ innerFibre a } = Icc ⌈max (x/n) √x⌉ ⌊min ((x + h√x)/m) (2√x)⌋
```

whenever `1 ≤ n ≤ m ≤ ⌊x + h√x⌋`.  The remaining constraints of `outerBlock` and `innerFibre` are
implied: `a ≥ √x ≥ 2 ≥ 1` and `a ≤ 2√x ≤ x`, while `x ≤ an ≤ am` and `an ≤ am ≤ x + h√x` follow
from `n ≤ m`.

The kernel is therefore a *count of integers in an interval whose endpoints move smoothly with the
inner variable*, which is what makes the smooth/error split of `KernelSmoothSplit` available.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The lower endpoint of the admissible outer indices. -/
def fibreLow (x : ℝ) (n : ℕ) : ℝ := max (x / (n : ℝ)) (Real.sqrt x)

/-- The upper endpoint of the admissible outer indices. -/
def fibreHigh (x h : ℝ) (m : ℕ) : ℝ :=
  min ((x + h * Real.sqrt x) / (m : ℝ)) (2 * Real.sqrt x)

theorem two_le_sqrt {x : ℝ} (hx : 4 ≤ x) : (2 : ℝ) ≤ Real.sqrt x := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [← h4]
  exact Real.sqrt_le_sqrt hx

theorem two_sqrt_le_self {x : ℝ} (hx : 4 ≤ x) : 2 * Real.sqrt x ≤ x := by
  have hs := two_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  nlinarith [hs, hsq]

theorem fibreHigh_nonneg {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) (m : ℕ) :
    0 ≤ fibreHigh x h m := by
  have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  rw [fibreHigh]
  refine le_min ?_ (by linarith)
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  positivity

/-- **The fibre kernel is the count of integers in an explicit interval.** -/
theorem fibre_kernel_eq_Icc {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {m n : ℕ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hmM : m ≤ ⌊x + h * Real.sqrt x⌋₊) :
    (outerBlock x h).filter (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)
      = Finset.Icc ⌈fibreLow x n⌉₊ ⌊fibreHigh x h m⌋₊ := by
  classical
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := two_le_sqrt hx
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm1 : 1 ≤ m := le_trans hn hnm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  ext a
  simp only [Finset.mem_filter, mem_outerBlock, mem_innerFibre, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨-, -⟩, hsa, ha2⟩, ⟨-, -, hmx2⟩, -, hnx1, -⟩
    have hmR : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
    have hnR : ((a * n : ℕ) : ℝ) = (a : ℝ) * (n : ℝ) := by push_cast; ring
    rw [hmR] at hmx2
    rw [hnR] at hnx1
    constructor
    · rw [Nat.ceil_le, fibreLow]
      refine max_le ?_ hsa
      rw [div_le_iff₀ hn0]
      exact hnx1
    · refine Nat.le_floor ?_
      rw [fibreHigh]
      refine le_min ?_ ha2
      rw [le_div_iff₀ hm0]
      exact hmx2
  · rintro ⟨hlo, hhi⟩
    have hlo' : fibreLow x n ≤ (a : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hlo)
    have hhi' : (a : ℝ) ≤ fibreHigh x h m := by
      refine le_trans ?_ (Nat.floor_le (fibreHigh_nonneg hx hh m))
      exact_mod_cast hhi
    rw [fibreLow] at hlo'
    rw [fibreHigh] at hhi'
    have hsa : Real.sqrt x ≤ (a : ℝ) := le_trans (le_max_right _ _) hlo'
    have ha2 : (a : ℝ) ≤ 2 * Real.sqrt x := le_trans hhi' (min_le_right _ _)
    have hlown : x / (n : ℝ) ≤ (a : ℝ) := le_trans (le_max_left _ _) hlo'
    have hhim : (a : ℝ) ≤ (x + h * Real.sqrt x) / (m : ℝ) := le_trans hhi' (min_le_left _ _)
    have hxn : x ≤ (a : ℝ) * (n : ℝ) := by rwa [div_le_iff₀ hn0] at hlown
    have ham : (a : ℝ) * (m : ℝ) ≤ x + h * Real.sqrt x := by rwa [le_div_iff₀ hm0] at hhim
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have hxm : x ≤ (a : ℝ) * (m : ℝ) := by nlinarith [hxn, hnmR, ha0]
    have han : (a : ℝ) * (n : ℝ) ≤ x + h * Real.sqrt x := by nlinarith [ham, hnmR, ha0]
    have ha1 : 1 ≤ a := by
      have : (1 : ℝ) ≤ (a : ℝ) := by linarith
      exact_mod_cast this
    have haM : a ≤ ⌊x + h * Real.sqrt x⌋₊ := by
      refine Nat.le_floor ?_
      have := two_sqrt_le_self hx
      have hhs : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
      linarith
    have hnM : n ≤ ⌊x + h * Real.sqrt x⌋₊ := le_trans hnm hmM
    have hmR : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
    have hnR : ((a * n : ℕ) : ℝ) = (a : ℝ) * (n : ℝ) := by push_cast; ring
    exact ⟨⟨⟨ha1, haM⟩, hsa, ha2⟩, ⟨⟨hm1, hmM⟩, by rw [hmR]; exact hxm, by rw [hmR]; exact ham⟩,
      ⟨hn, hnM⟩, by rw [hnR]; exact hxn, by rw [hnR]; exact han⟩

end RHTower.Sieve

end
