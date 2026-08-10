import GaloisForLFunctions.RHTower.Sieve.FibreKernelSize

/-!
# The diagonal, and where the kernel lives

Two facts that fix the size of the bilinear form.

On the diagonal the kernel is the number of `a` with `m` in the fibre, and the interval bound
collapses:

```text
K(m,m) ≤ h√x/m + 1 .
```

And the kernel vanishes unless `m` lies in the range the block can reach: `a ∈ outerBlock` means
`√x ≤ a ≤ 2√x`, so `x ≤ am ≤ x + h√x` forces

```text
√x/2 ≤ m ≤ √x + h .
```

Together these give the diagonal contribution `≍ ∑_{m ≍ √x} (h√x/m + 1) ≍ h√x + √x`, which is the
*trivial* size of the whole mean square.  The content of the theorem is entirely in the
off-diagonal cancellation; no bound on individual terms can produce it.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **On the diagonal the kernel is at most `h√x/m + 1`.** -/
theorem fibre_kernel_diag_le {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {m : ℕ} (hm : 1 ≤ m) :
    ((((outerBlock x h).filter
        (fun a => m ∈ innerFibre x h a ∧ m ∈ innerFibre x h a)).card : ℕ) : ℝ)
      ≤ h * Real.sqrt x / m + 1 := by
  have hbase := fibre_kernel_card_le hx hh hm hm
  have hmax : max m m = m := max_self m
  have hmin : min m m = m := min_self m
  rw [hmax, hmin] at hbase
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hval : (x + h * Real.sqrt x) / (m : ℝ) - x / (m : ℝ) + 1
      = h * Real.sqrt x / (m : ℝ) + 1 := by
    field_simp
    ring
  rw [hval] at hbase
  have hnn : (0 : ℝ) ≤ h * Real.sqrt x / (m : ℝ) + 1 := by
    have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    positivity
  rw [max_eq_left hnn] at hbase
  exact hbase

/-- **The kernel lives on `[√x/2, √x + h]`.** -/
theorem fibre_kernel_support {x h : ℝ} (hx : 0 < x) {m a : ℕ}
    (ha : a ∈ outerBlock x h) (hma : m ∈ innerFibre x h a) :
    Real.sqrt x / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ Real.sqrt x + h := by
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  rw [mem_outerBlock] at ha
  obtain ⟨⟨ha1, -⟩, hal, hau⟩ := ha
  rw [mem_innerFibre] at hma
  obtain ⟨-, hm1, hm2⟩ := hma
  have hcast : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
  rw [hcast] at hm1 hm2
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hs0 hal
  constructor
  · -- `m ≥ x/a ≥ x/(2√x) = √x/2`
    nlinarith [hm1, hau, hsq, hs0, ha0]
  · -- `m ≤ (x + h√x)/a ≤ (x + h√x)/√x = √x + h`
    nlinarith [hm2, hal, hsq, hs0, ha0]

end RHTower.Sieve

end
