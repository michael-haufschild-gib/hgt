import GaloisForLFunctions.RHTower.Sieve.FibreFixedWidth

/-!
# The fibre, characterised in the logarithmic variable

The containment of `FibreFixedWidth` is an equivalence: for `b ≥ 1`,

```text
b ∈ innerFibre x h a  ↔  log(x/a) ≤ log b ≤ log(x/a) + fibreWidth x h .
```

So the fibres of the Matomäki–Radziwiłł reduction are exactly the logarithmic windows of the single
width `log(1 + h/√x)`, at the `√x` starting points `log(x/a)`.

The corpus's `logWindow δ n = [log n − δ, log n)` is half-open, while the fibre is closed at both
ends; the two therefore differ by at most the two endpoint terms, which for a unit-bounded weight
cost `O(1)` per fibre and `O(√x)` in total — negligible against the target `o(h²√x)` once `h → ∞`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The converse inclusion. -/
theorem mem_innerFibre_of_log {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) {b : ℕ} (hb : 1 ≤ b)
    (h1 : Real.log (x / a) ≤ Real.log b)
    (h2 : Real.log b ≤ Real.log (x / a) + fibreWidth x h) :
    b ∈ innerFibre x h a := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have ha1 : 1 ≤ a := by
    rw [mem_outerBlock] at ha
    exact ha.1.1
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hxa0 : (0 : ℝ) < x / (a : ℝ) := by positivity
  have hone : (0 : ℝ) < 1 + h / Real.sqrt x := by positivity
  -- undo the logarithms
  have hlow : x / (a : ℝ) ≤ (b : ℝ) := by
    by_contra hc
    exact absurd (Real.log_lt_log hb0 (by linarith : (b : ℝ) < x / (a : ℝ))) (by linarith)
  have hfac : (x + h * Real.sqrt x) / (a : ℝ) = (x / (a : ℝ)) * (1 + h / Real.sqrt x) := by
    field_simp
    nlinarith [hsq, hs0]
  have hhigh : (b : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) := by
    rw [hfac]
    by_contra hc
    have hlt : (x / (a : ℝ)) * (1 + h / Real.sqrt x) < (b : ℝ) := by linarith
    have := Real.log_lt_log (by positivity) hlt
    rw [Real.log_mul (ne_of_gt hxa0) (ne_of_gt hone)] at this
    rw [fibreWidth] at h2
    linarith
  rw [innerFibre_eq hx hh ha, Finset.mem_Icc]
  constructor
  · exact Nat.ceil_le.2 hlow
  · exact Nat.le_floor hhigh

/-- **The fibre is a logarithmic window of the common width.** -/
theorem mem_innerFibre_iff_log {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) {b : ℕ} (hb : 1 ≤ b) :
    b ∈ innerFibre x h a
      ↔ Real.log (x / a) ≤ Real.log b
        ∧ Real.log b ≤ Real.log (x / a) + fibreWidth x h :=
  ⟨fun hmem => innerFibre_log_bounds hx hh ha hb hmem,
    fun ⟨h1, h2⟩ => mem_innerFibre_of_log hx hh ha hb h1 h2⟩

end RHTower.Sieve

end
