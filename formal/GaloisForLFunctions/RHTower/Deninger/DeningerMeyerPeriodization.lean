import GaloisForLFunctions.RHTower.Deninger.DeningerCollarExchange

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

* `deningerShift_norm_le` : geometric decay of the lattice terms.
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

/-- **The lattice terms decay geometrically** in the lattice index. -/
theorem deningerShift_norm_le {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℤ,
      ‖(f : ℝ → ℂ) (t + (j : ℝ) * L)‖ ≤ C * (Real.exp (-L)) ^ j.natAbs := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_norm_le hf 1
  refine ⟨C * Real.exp |t|, by positivity, fun j => ?_⟩
  have hbase := hC (t + (j : ℝ) * L)
  have hcast : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have habs : |(j : ℝ)| * L ≤ |t| + |t + (j : ℝ) * L| := by
    have h1 : |(j : ℝ) * L| = |(j : ℝ)| * L := by
      rw [abs_mul, abs_of_pos hL]
    have hrw : t + (j : ℝ) * L - t = (j : ℝ) * L := by ring
    have h2 : |(j : ℝ) * L| ≤ |t + (j : ℝ) * L| + |t| := by
      calc |(j : ℝ) * L| = |t + (j : ℝ) * L - t| := by rw [hrw]
        _ ≤ |t + (j : ℝ) * L| + |t| := abs_sub _ _
    rw [h1] at h2
    linarith
  have hpow : (Real.exp (-L)) ^ j.natAbs = Real.exp (-(|(j : ℝ)| * L)) := by
    rw [← Real.exp_nat_mul, hcast]
    congr 1
    ring
  have hstep : Real.exp (-(1 * |t + (j : ℝ) * L|))
      ≤ Real.exp |t| * (Real.exp (-L)) ^ j.natAbs := by
    rw [hpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [one_mul]
    linarith
  refine le_trans hbase ?_
  calc C * Real.exp (-(1 * |t + (j : ℝ) * L|))
      ≤ C * (Real.exp |t| * (Real.exp (-L)) ^ j.natAbs) :=
        mul_le_mul_of_nonneg_left hstep hCnn
    _ = C * Real.exp |t| * (Real.exp (-L)) ^ j.natAbs := by ring

/-! ## Convergence of the lattice sums -/

/-- The geometric majorant of the lattice sum is summable over `ℤ`. -/
theorem deningerGeometricInt_summable {C : ℝ} {L : ℝ} (hL : 0 < L) :
    Summable fun j : ℤ => C * (Real.exp (-L)) ^ j.natAbs := by
  have hq : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hqnn : (0 : ℝ) ≤ Real.exp (-L) := (Real.exp_pos _).le
  have hnat : Summable fun n : ℕ => C * (Real.exp (-L)) ^ n :=
    (summable_geometric_of_lt_one hqnn hq).mul_left C
  refine Summable.of_nat_of_neg_add_one (by simpa using hnat) ?_
  have hshift : Summable fun n : ℕ => C * (Real.exp (-L)) ^ (n + 1) :=
    hnat.comp_injective (add_left_injective 1)
  refine hshift.congr fun n => ?_
  congr 2

/-- **The two-sided lattice sum converges absolutely.** -/
theorem deningerShiftInt_summable {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    Summable fun j : ℤ => (f : ℝ → ℂ) (t + (j : ℝ) * L) := by
  obtain ⟨C, hCnn, hC⟩ := deningerShift_norm_le hf hL t
  exact Summable.of_norm_bounded (deningerGeometricInt_summable (C := C) hL) hC

/-- **The one-sided lattice sum converges absolutely.** -/
theorem deningerShiftNat_summable {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    Summable fun j : ℕ => (f : ℝ → ℂ) (t + (j : ℝ) * L) := by
  obtain ⟨C, hCnn, hC⟩ := deningerShift_norm_le hf hL t
  have hq : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnat : Summable fun n : ℕ => C * (Real.exp (-L)) ^ n :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left C
  refine Summable.of_norm_bounded hnat fun n => ?_
  have h := hC (n : ℤ)
  simpa using h

/-! ## The Green sum and the periodization -/

/-- The one-sided Green sum of the translation lattice. -/
def deningerGreenSum (f : 𝓢(ℝ, ℂ)) (L t : ℝ) : ℂ := ∑' j : ℕ, (f : ℝ → ℂ) (t + (j : ℝ) * L)

/-- The two-sided periodization of the translation lattice. -/
def deningerPeriodizationSum (f : 𝓢(ℝ, ℂ)) (L t : ℝ) : ℂ :=
  ∑' j : ℤ, (f : ℝ → ℂ) (t + (j : ℝ) * L)

/-- **The Green sum inverts the periodization defect pointwise.** -/
theorem deningerGreenSum_telescope {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    deningerGreenSum f L t - deningerGreenSum f L (t + L) = (f : ℝ → ℂ) t := by
  have hsum := deningerShiftNat_summable hf hL t
  rw [deningerGreenSum, deningerGreenSum, hsum.tsum_eq_zero_add]
  have hshift : ∀ j : ℕ, (f : ℝ → ℂ) (t + ((j + 1 : ℕ) : ℝ) * L)
      = (f : ℝ → ℂ) (t + L + (j : ℝ) * L) := by
    intro j
    congr 1
    push_cast
    ring
  rw [tsum_congr hshift]
  have hzero : (f : ℝ → ℂ) (t + ((0 : ℕ) : ℝ) * L) = (f : ℝ → ℂ) t := by
    norm_num
  rw [hzero]
  ring

/-- **A translation-periodic member of the source vanishes.**  Iterating the period pushes the
value out to infinity, where the source decays. -/
theorem deningerExpSchwartz_eq_zero_of_periodic {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz)
    {L : ℝ} (hL : 0 < L) (hper : ∀ t : ℝ, (f : ℝ → ℂ) t = (f : ℝ → ℂ) (t + L)) : f = 0 := by
  refine SchwartzMap.ext fun t => ?_
  obtain ⟨C, hCnn, hC⟩ := deningerShift_norm_le hf hL t
  have hiter : ∀ n : ℕ, (f : ℝ → ℂ) t = (f : ℝ → ℂ) (t + (n : ℝ) * L) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [ih, hper (t + (n : ℝ) * L)]
      congr 1
      push_cast
      ring
  have hbound : ∀ n : ℕ, ‖(f : ℝ → ℂ) t‖ ≤ C * (Real.exp (-L)) ^ n := by
    intro n
    rw [hiter n]
    have h := hC (n : ℤ)
    simpa using h
  have hq : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlim : Filter.Tendsto (fun n : ℕ => C * (Real.exp (-L)) ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-L)).le hq
    simpa using this.const_mul C
  have hle : ‖(f : ℝ → ℂ) t‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have : (f : ℝ → ℂ) t = 0 := by
    have := norm_nonneg ((f : ℝ → ℂ) t)
    have heq : ‖(f : ℝ → ℂ) t‖ = 0 := le_antisymm hle this
    exact norm_eq_zero.mp heq
  simpa using this

/-- **The periodization kills every periodization defect.**  Reindexing the lattice by one step is
a bijection, so the telescoping sum vanishes. -/
theorem deningerPeriodization_defect (f : 𝓢(ℝ, ℂ)) (L t : ℝ) :
    (deningerPeriodizationSum f L t - deningerPeriodizationSum (deningerExpShift L f) L t)
      = 0 := by
  have hcoe : ∀ j : ℤ, ((deningerExpShift L f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (t + (j : ℝ) * L)
      = (f : ℝ → ℂ) (t + ((j + 1 : ℤ) : ℝ) * L) := by
    intro j
    rw [deningerExpShift_apply]
    congr 1
    push_cast
    ring
  have hreindex := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun j : ℤ => (f : ℝ → ℂ) (t + (j : ℝ) * L))
  simp only [Equiv.coe_addRight] at hreindex
  rw [deningerPeriodizationSum, deningerPeriodizationSum]
  rw [tsum_congr hcoe, hreindex, sub_self]

end

end RHTower
