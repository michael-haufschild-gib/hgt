import GaloisForLFunctions.RHTower.Sieve.GoodStartFibreWindow

/-!
# The fibre window sits below the window top
-/

namespace RHTower.Sieve

open Finset

/-- **The top of the fibre is below the top of the whole window.** -/
theorem fibre_top_le_floor {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) :
    fibreStartIdx x a + fibreLen x h a ≤ ⌊x + h * Real.sqrt x⌋₊ := by
  rw [mem_outerBlock] at ha
  obtain ⟨⟨hone, -⟩, hlow, hhigh⟩ := ha
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hone
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have htop0 : (0 : ℝ) ≤ x + h * Real.sqrt x := by positivity
  have hP : ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ ≤ ⌊x + h * Real.sqrt x⌋₊ := by
    refine Nat.floor_mono ?_
    rw [div_le_iff₀ ha0]
    nlinarith [htop0, ha1]
  have hQ : ⌈x / (a : ℝ)⌉₊ - 1 ≤ ⌊x + h * Real.sqrt x⌋₊ := by
    have h1 : ⌈x / (a : ℝ)⌉₊ ≤ ⌈x⌉₊ := by
      refine Nat.ceil_mono ?_
      rw [div_le_iff₀ ha0]
      nlinarith [hx0, ha1]
    have h2 : ⌈x⌉₊ ≤ ⌊x⌋₊ + 1 := by
      refine Nat.ceil_le.2 ?_
      have := Nat.lt_floor_add_one x
      push_cast
      linarith
    have h3 : ⌊x⌋₊ ≤ ⌊x + h * Real.sqrt x⌋₊ := by
      refine Nat.floor_mono ?_
      nlinarith [hs0, hh]
    omega
  rw [fibreLen, fibreStartIdx]
  omega

/-- **The fibre top is below the square of the ceiling square root of the window top.** -/
theorem fibre_top_lt_sq {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) :
    fibreStartIdx x a + fibreLen x h a
      < (⌈Real.sqrt (x + h * Real.sqrt x)⌉₊ + 1) ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have htop0 : (0 : ℝ) ≤ x + h * Real.sqrt x := by positivity
  have hle := fibre_top_le_floor hx hh ha
  have hfl : ((⌊x + h * Real.sqrt x⌋₊ : ℕ) : ℝ) ≤ x + h * Real.sqrt x := Nat.floor_le htop0
  have hsq : Real.sqrt (x + h * Real.sqrt x)
      ≤ ((⌈Real.sqrt (x + h * Real.sqrt x)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (x + h * Real.sqrt x) := Real.sqrt_nonneg _
  have hTsq : x + h * Real.sqrt x
      = Real.sqrt (x + h * Real.sqrt x) * Real.sqrt (x + h * Real.sqrt x) :=
    (Real.mul_self_sqrt htop0).symm
  have hTle : x + h * Real.sqrt x
      ≤ ((⌈Real.sqrt (x + h * Real.sqrt x)⌉₊ : ℕ) : ℝ)
        * ((⌈Real.sqrt (x + h * Real.sqrt x)⌉₊ : ℕ) : ℝ) := by
    have hmul := mul_self_le_mul_self hsq0 hsq
    linarith [hTsq, hmul]
  have hlt : ((⌊x + h * Real.sqrt x⌋₊ : ℕ) : ℝ)
      < (((⌈Real.sqrt (x + h * Real.sqrt x)⌉₊ + 1 : ℕ)) : ℝ) ^ 2 := by
    push_cast
    nlinarith [hfl, hTle, Nat.cast_nonneg (α := ℝ) ⌈Real.sqrt (x + h * Real.sqrt x)⌉₊]
  have hnat : ⌊x + h * Real.sqrt x⌋₊
      < (⌈Real.sqrt (x + h * Real.sqrt x)⌉₊ + 1) ^ 2 := by exact_mod_cast hlt
  omega

end RHTower.Sieve
