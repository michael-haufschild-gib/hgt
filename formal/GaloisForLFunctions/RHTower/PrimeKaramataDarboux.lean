import GaloisForLFunctions.RHTower.PrimeKaramataShell

/-!
# Darboux bounds for the profile power on a uniform partition

The Riemann sums of the decreasing profile `v ↦ v^{−α}` on `[v₀, 1]` bracket its integral.  After
the affine substitution `v = v₀ + h u` this is mathlib's unit-step statement for an antitone
function, so no new analysis is needed.
-/

open MeasureTheory Filter Topology intervalIntegral

namespace RHTower

noncomputable section

/-- Shells chain. -/
theorem primeLogSum_chain (f : ℝ → ℝ) (x : ℕ → ℝ)
    (hmono : ∀ k, ⌊x k⌋₊ ≤ ⌊x (k + 1)⌋₊) (n : ℕ) :
    ∑ k ∈ Finset.range n, primeLogSum f (x k) (x (k + 1)) = primeLogSum f (x 0) (x n) := by
  have hmono0 : ∀ m : ℕ, ⌊x 0⌋₊ ≤ ⌊x m⌋₊ := by
    intro m
    induction m with
    | zero => exact le_rfl
    | succ k ihk => exact le_trans ihk (hmono k)
  induction n with
  | zero => simp [primeLogSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact primeLogSum_add (hmono0 n) (hmono n)

/-- The value of the profile integral. -/
theorem integral_rpow_neg_unit {α v₀ : ℝ} (hα1 : α < 1) (hv₀ : 0 < v₀) :
    (∫ v in v₀..(1 : ℝ), v ^ (-α)) = (1 - v₀ ^ (1 - α)) / (1 - α) := by
  rw [integral_rpow (Or.inl (by linarith))]
  have h1 : -α + 1 = 1 - α := by ring
  rw [h1, Real.one_rpow]

/-- **The Darboux bracket.** -/
theorem rpow_darboux {α v₀ : ℝ} (hα0 : 0 ≤ α) (hv₀ : 0 < v₀) (hv₀1 : v₀ < 1) {N : ℕ}
    (hN : 0 < N) :
    (∑ j ∈ Finset.range N, (v₀ + ((j : ℝ) + 1) * ((1 - v₀) / N)) ^ (-α)) * ((1 - v₀) / N)
        ≤ ∫ v in v₀..(1 : ℝ), v ^ (-α)
      ∧ (∫ v in v₀..(1 : ℝ), v ^ (-α))
        ≤ (∑ j ∈ Finset.range N, (v₀ + (j : ℝ) * ((1 - v₀) / N)) ^ (-α)) * ((1 - v₀) / N) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set h : ℝ := (1 - v₀) / N with hh
  have hh0 : 0 < h := by rw [hh]; have : (0:ℝ) < 1 - v₀ := by linarith
                         positivity
  have hhN : h * (N : ℝ) = 1 - v₀ := by rw [hh]; field_simp
  -- the substituted profile
  set G : ℝ → ℝ := fun u : ℝ => (h * u + v₀) ^ (-α) with hG
  have hGanti : AntitoneOn G (Set.Icc (0 : ℝ) (0 + (N : ℝ))) := by
    intro u hu v hv huv
    have hu0 : (0 : ℝ) ≤ u := by simpa using hu.1
    have hv0 : (0 : ℝ) ≤ v := by simpa using hv.1
    have h1 : (0 : ℝ) < h * u + v₀ := by nlinarith [hh0, hv₀]
    exact Real.rpow_le_rpow_of_nonpos h1 (by nlinarith [hh0]) (by linarith)
  have hsub : (∫ u in (0 : ℝ)..(N : ℝ), G u) = h⁻¹ * ∫ v in v₀..(1 : ℝ), v ^ (-α) := by
    have := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := (N : ℝ))
      (fun v : ℝ => v ^ (-α)) hh0.ne' v₀
    rw [hG]
    rw [this]
    have hend : h * (N : ℝ) + v₀ = 1 := by rw [hhN]; ring
    rw [mul_zero, zero_add, hend, smul_eq_mul]
  have hupper := hGanti.integral_le_sum
  have hlower := hGanti.sum_le_integral
  rw [zero_add] at hupper hlower
  rw [hsub] at hupper hlower
  constructor
  · have hL : ∑ i ∈ Finset.range N, G ((0 : ℝ) + ((i + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.range N, (v₀ + ((j : ℝ) + 1) * h) ^ (-α) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hG]
      push_cast
      ring_nf
    rw [hL] at hlower
    have hmul := mul_le_mul_of_nonneg_right hlower hh0.le
    have hid : h⁻¹ * (∫ v in v₀..(1 : ℝ), v ^ (-α)) * h = ∫ v in v₀..(1 : ℝ), v ^ (-α) := by
      field_simp
    rw [hid] at hmul
    calc (∑ j ∈ Finset.range N, (v₀ + ((j : ℝ) + 1) * h) ^ (-α)) * h
        = (∑ j ∈ Finset.range N, (v₀ + ((j : ℝ) + 1) * h) ^ (-α)) * h := rfl
      _ ≤ ∫ v in v₀..(1 : ℝ), v ^ (-α) := hmul
  · have hU : ∑ i ∈ Finset.range N, G ((0 : ℝ) + (i : ℝ))
        = ∑ j ∈ Finset.range N, (v₀ + (j : ℝ) * h) ^ (-α) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hG]
      push_cast
      ring_nf
    rw [hU] at hupper
    have hmul := mul_le_mul_of_nonneg_right hupper hh0.le
    have hid : h⁻¹ * (∫ v in v₀..(1 : ℝ), v ^ (-α)) * h = ∫ v in v₀..(1 : ℝ), v ^ (-α) := by
      field_simp
    rw [hid] at hmul
    exact hmul

end

end RHTower
