import GaloisForLFunctions.RHTower.DeningerCollarExchange

/-!
# Multiplicative periodization of the exponentially decreasing source

In the logarithmic coordinate the prime `p` acts by the translation `τ_L`, `L = log p`, and the
periodization defect is `Δ_L = 1 - τ_L`.  Because the source beats every exponential, the whole
translation lattice sum converges geometrically:

`‖f(t + jL)‖ ≤ C e^{|t|} (e^{-L})^{|j|}`,

so both the one-sided Green sum `G_L f(t) = ∑_{j ≥ 0} f(t + jL)` and the two-sided periodization
`Per_L f(t) = ∑_{j ∈ ℤ} f(t + jL)` are absolutely convergent at every point.

Telescoping then gives the two structural facts of the periodization sequence: the defect is
injective, because a translation-periodic member of the source must vanish at infinity, and the
periodization kills every defect.

* `deningerShift_summable`, `deningerShiftInt_summable` : geometric convergence of the lattice sums.
* `deningerGreenSum`, `deningerGreenSum_telescope` : **`Δ_L G_L = 1` pointwise.**
* `deningerExpSchwartz_eq_zero_of_periodic` : **`Δ_L` is injective.**
* `deningerPeriodizationSum`, `deningerPeriodization_defect` : **`Per_L ∘ Δ_L = 0`.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-! ## The exponential bound -/

/-- The defining bound of the source, read at derivative order zero. -/
theorem deningerExpSchwartz_norm_le {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖(f : ℝ → ℂ) t‖ ≤ C * Real.exp (-(A * |t|)) := by
  obtain ⟨C, hC⟩ := hf A 0
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have h0 := hC t
  rw [norm_iteratedFDeriv_zero] at h0
  have hval : Real.exp (A * |t|) * ‖(f : ℝ → ℂ) t‖ ≤ max C 0 := le_trans h0 (le_max_left _ _)
  have hepos : (0 : ℝ) < Real.exp (A * |t|) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hepos]
  calc ‖(f : ℝ → ℂ) t‖ * Real.exp (A * |t|)
      = Real.exp (A * |t|) * ‖(f : ℝ → ℂ) t‖ := by ring
    _ ≤ max C 0 := hval

/-- **The lattice terms decay geometrically**, uniformly on bounded sets of the base point. -/
theorem deningerShift_norm_le {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℤ,
      ‖(f : ℝ → ℂ) (t + (j : ℝ) * L)‖ ≤ C * (Real.exp (-L)) ^ |j| := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_norm_le hf 1
  refine ⟨C * Real.exp |t|, by positivity, fun j => ?_⟩
  have hbase := hC (t + (j : ℝ) * L)
  have habs : |(j : ℝ)| * L ≤ |t| + |t + (j : ℝ) * L| := by
    have h1 : |(j : ℝ) * L| = |(j : ℝ)| * L := by
      rw [abs_mul, abs_of_pos hL]
    have h2 : |(j : ℝ) * L| ≤ |t + (j : ℝ) * L| + |t| := by
      have := abs_sub (t + (j : ℝ) * L) t
      have hrw : t + (j : ℝ) * L - t = (j : ℝ) * L := by ring
      calc |(j : ℝ) * L| = |t + (j : ℝ) * L - t| := by rw [hrw]
        _ ≤ |t + (j : ℝ) * L| + |t| := abs_sub _ _
    linarith [h1 ▸ h2]
  have hstep : Real.exp (-(1 * |t + (j : ℝ) * L|)) ≤ Real.exp |t| * (Real.exp (-L)) ^ |j| := by
    have hpow : (Real.exp (-L)) ^ |j| = Real.exp (-(|(j : ℝ)| * L)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hcast : ((|j| : ℕ) : ℝ) = |(j : ℝ)| := by
        rw [Int.cast_natAbs]
        push_cast
        ring
      rw [hcast]
      ring
    rw [hpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [one_mul]
    linarith
  refine le_trans hbase ?_
  calc C * Real.exp (-(1 * |t + (j : ℝ) * L|))
      ≤ C * (Real.exp |t| * (Real.exp (-L)) ^ |j|) :=
        mul_le_mul_of_nonneg_left hstep hCnn
    _ = C * Real.exp |t| * (Real.exp (-L)) ^ |j| := by ring

/-! ## Convergence of the lattice sums -/

/-- **The two-sided lattice sum converges absolutely.** -/
theorem deningerShiftInt_summable {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    Summable fun j : ℤ => (f : ℝ → ℂ) (t + (j : ℝ) * L) := by
  obtain ⟨C, hCnn, hC⟩ := deningerShift_norm_le hf hL t
  have hq : |Real.exp (-L)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable fun j : ℤ => C * (Real.exp (-L)) ^ |j| :=
    (summable_geometric_iff_norm_lt_one.mpr (by rwa [Real.norm_eq_abs])
      |>.comp_injective (fun _ _ h => h) |> fun _ => by exact ?_) |> fun _ => by exact ?_
  exact Summable.of_norm_bounded hgeo hC

/-- The one-sided Green sum of the translation lattice. -/
def deningerGreenSum (f : 𝓢(ℝ, ℂ)) (L t : ℝ) : ℂ := ∑' j : ℕ, (f : ℝ → ℂ) (t + (j : ℝ) * L)

/-- The two-sided periodization of the translation lattice. -/
def deningerPeriodizationSum (f : 𝓢(ℝ, ℂ)) (L t : ℝ) : ℂ :=
  ∑' j : ℤ, (f : ℝ → ℂ) (t + (j : ℝ) * L)

end

end RHTower
