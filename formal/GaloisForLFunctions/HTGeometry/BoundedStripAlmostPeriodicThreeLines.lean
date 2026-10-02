import GaloisForLFunctions.HTGeometry.DirichletStripAlmostPeriodic
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Bohr's theorem in almost-periodicity form

**Theorem** (`isStripAlmostPeriodicOn_of_bounded_of_line`).  Let `F` be holomorphic and bounded by
`M` on the half-plane `Re z > x`, and almost periodic on one vertical line `Re z = u`: for every
`ε > 0` the shifts `τ` with `sup_{Re z = u} |F(z + iτ) − F(z)| ≤ ε` are relatively dense.  Then `F`
is almost periodic on every closed strip `l' ≤ Re z ≤ u` with `x < l'`.

**Proof.**  For a shift `τ`, the difference `g(z) = F(z + iτ) − F(z)` is holomorphic on
`Re z > x`, bounded by `2M`, and bounded by `ε` on `Re z = u`.  Hadamard's three-lines theorem on
`l ≤ Re z ≤ u`, `l = (x + l')/2`, gives `|g(z)| ≤ (2M)^{1−θ} ε^{θ}` with
`θ = (Re z − l)/(u − l) ≥ θ₀ = (l' − l)/(u − l) > 0`, uniformly small on `Re z ≥ l'`.  So every
`ε`-almost period on the line is an `η`-almost period on the strip, with `η → 0` as `ε → 0`.

For an ordinary Dirichlet series the line hypothesis holds on every line of absolute convergence
(`isStripAlmostPeriodic_LSeries`).  So a Dirichlet series with a bounded holomorphic continuation to
`Re z > x` is almost periodic on every closed substrip of `Re z > x`.  This is the
almost-periodicity half of Bohr's theorem `σ_u = σ_b`, and it suffices for recurrence arguments.
-/

open Complex Set Filter Topology Metric

noncomputable section

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Almost periodicity moves left through a region of boundedness.** -/
theorem isStripAlmostPeriodicOn_of_bounded_of_line {F : ℂ → ℂ} {x u l' M : ℝ}
    (hxl' : x < l') (hl'u : l' ≤ u)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re})
    (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hline : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, ∃ τ ∈ Icc a (a + L),
      ∀ z : ℂ, z.re = u → ‖F (z + (τ : ℂ) * I) - F z‖ ≤ ε) :
    IsStripAlmostPeriodicOn F ((l' + u) / 2) ((u - l') / 2) := by
  intro η hη
  set l : ℝ := (x + l') / 2 with hl
  have hxl : x < l := by rw [hl]; linarith
  have hll' : l < l' := by rw [hl]; linarith
  have hlu : l < u := lt_of_lt_of_le hll' hl'u
  set θ₀ : ℝ := (l' - l) / (u - l) with hθ₀
  have hθ₀pos : 0 < θ₀ := div_pos (by linarith) (by linarith)
  set A : ℝ := max (2 * M) 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA0 : 0 < A := by linarith
  have hηA : 0 < η / A := div_pos hη hA0
  set b : ℝ := min 1 ((η / A) ^ (1 / θ₀)) with hb
  have hbpos : 0 < b := lt_min one_pos (Real.rpow_pos_of_pos hηA _)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbθ : b ^ θ₀ ≤ η / A := by
    calc b ^ θ₀ ≤ ((η / A) ^ (1 / θ₀)) ^ θ₀ :=
          Real.rpow_le_rpow hbpos.le (min_le_right _ _) hθ₀pos.le
      _ = η / A := by
          rw [← Real.rpow_mul hηA.le, one_div_mul_cancel hθ₀pos.ne', Real.rpow_one]
  obtain ⟨L, hL, hτ⟩ := hline b hbpos
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτu⟩ := hτ a
  refine ⟨τ, hτmem, fun z hz => ?_⟩
  have hz' : l' ≤ z.re ∧ z.re ≤ u := by
    have := abs_le.mp hz
    constructor <;> linarith [this.1, this.2]
  have hshift : ∀ w : ℂ, (w + (τ : ℂ) * I).re = w.re := fun w => by simp
  have hopen : IsOpen {w : ℂ | x < w.re} := isOpen_lt continuous_const continuous_re
  set g : ℂ → ℂ := fun w => F (w + (τ : ℂ) * I) - F w with hg
  have hgd : DifferentiableOn ℂ g {w : ℂ | x < w.re} := by
    intro w hw
    have hw' : x < (w + (τ : ℂ) * I).re := by rw [hshift]; exact hw
    have h1 : DifferentiableAt ℂ F (w + (τ : ℂ) * I) :=
      (hF _ hw').differentiableAt (hopen.mem_nhds hw')
    exact ((h1.comp w (differentiableAt_id.add_const _)).differentiableWithinAt).sub (hF w hw)
  have hgM : ∀ w : ℂ, x < w.re → ‖g w‖ ≤ A := by
    intro w hw
    have hw' : x < (w + (τ : ℂ) * I).re := by rw [hshift]; exact hw
    calc ‖g w‖ ≤ ‖F (w + (τ : ℂ) * I)‖ + ‖F w‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM _ hw') (hM w hw)
      _ ≤ A := by rw [hA]; linarith [le_max_left (2 * M) 1]
  have hclosed : IsClosed {w : ℂ | l ≤ w.re} := isClosed_le continuous_const continuous_re
  have hcl : closure (HadamardThreeLines.verticalStrip l u) ⊆ {w : ℂ | x < w.re} := by
    refine (closure_minimal (fun w hw => ?_) hclosed).trans fun w hw => ?_
    · exact (show l < w.re ∧ w.re < u from hw).1.le
    · exact lt_of_lt_of_le hxl hw
  have hdc : DiffContOnCl ℂ g (HadamardThreeLines.verticalStrip l u) :=
    (hgd.mono hcl).diffContOnCl
  have hbdd : BddAbove (norm ∘ g '' HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hgM w (lt_of_lt_of_le hxl (show l ≤ w.re ∧ w.re ≤ u from hw).1)
  have hzmem : z ∈ HadamardThreeLines.verticalClosedStrip l u :=
    show l ≤ z.re ∧ z.re ≤ u from ⟨by linarith, hz'.2⟩
  have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' (a := A) (b := b)
    hlu hzmem hdc hbdd
    (fun w hw => hgM w (by
      have : w.re = l := hw
      rw [this]; exact hxl))
    (fun w hw => hτu w hw)
  set θ : ℝ := (z.re - l) / (u - l) with hθ
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
  have hθθ₀ : θ₀ ≤ θ := by
    rw [hθ₀, hθ]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hAθ : A ^ (1 - θ) ≤ A := by
    calc A ^ (1 - θ) ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
      _ = A := Real.rpow_one A
  have hbθ' : b ^ θ ≤ b ^ θ₀ := Real.rpow_le_rpow_of_exponent_ge hbpos hb1 hθθ₀
  calc ‖F (z + (τ : ℂ) * I) - F z‖ = ‖g z‖ := rfl
    _ ≤ A ^ (1 - θ) * b ^ θ := h3
    _ ≤ A * (η / A) := mul_le_mul hAθ (hbθ'.trans hbθ) (by positivity) hA0.le
    _ = η := by field_simp

/-- **Line almost periodicity of an absolutely convergent Dirichlet series.**  If `Σ f(n) n^{−s}`
converges absolutely on `Re s = u − R` with `R > 0`, it is almost periodic on the strip
`|Re s − u| < R`. -/
theorem isStripAlmostPeriodic_LSeries {f : ℕ → ℂ} {u R : ℝ}
    (hf : LSeriesSummable f ((u - R : ℝ) : ℂ)) :
    IsStripAlmostPeriodic (LSeries f) u R := by
  refine isStripAlmostPeriodic_dirichlet (fun k => f (k + 1)) (fun k => Real.log (k + 1))
    (LSeries f) fun r hr ε hε => ?_
  set w : ℂ := ((u - R : ℝ) : ℂ) with hw
  set g : ℕ → ℝ := fun n => ‖LSeries.term f w (n + 1)‖ with hgdef
  have hgs : Summable g := (summable_nat_add_iff 1).mpr hf.norm
  obtain ⟨N, hN⟩ := ((tendsto_sum_nat_add g).eventually (ge_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨N, fun z hz => ?_⟩
  have hzre : w.re ≤ z.re := by
    have := abs_le.mp (show |z.re - u| ≤ r from hz)
    rw [hw, ofReal_re]
    linarith [this.1]
  have hterm : ∀ k : ℕ, LSeries.term f z (k + 1) =
      f (k + 1) * Complex.exp (-((Real.log (k + 1) : ℝ) : ℂ) * z) := by
    intro k
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), div_eq_mul_inv, ← Complex.cpow_neg]
    congr 1
    have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hk : ((k + 1 : ℕ) : ℂ) = ((((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [hk, Complex.cpow_def_of_ne_zero (by exact_mod_cast hk0), ← Complex.ofReal_log (by positivity)]
    congr 1
    ring
  have hzs : LSeriesSummable f z := hf.of_re_le_re hzre
  have hz1 : Summable fun n : ℕ => LSeries.term f z (n + 1) := (summable_nat_add_iff 1).mpr hzs
  have hsplit : LSeries f z = (∑ k ∈ Finset.range N, LSeries.term f z (k + 1)) +
      ∑' k : ℕ, LSeries.term f z (k + N + 1) := by
    rw [LSeries, hzs.tsum_eq_zero_add, LSeries.term_zero, zero_add,
      ← hz1.sum_add_tsum_nat_add N]
  have htail : ‖∑' k : ℕ, LSeries.term f z (k + N + 1)‖ ≤ ∑' k : ℕ, g (k + N) := by
    have hzt : Summable fun k : ℕ => ‖LSeries.term f z (k + N + 1)‖ :=
      (summable_nat_add_iff (f := fun n : ℕ => ‖LSeries.term f z (n + 1)‖) N).mpr hz1.norm
    have hgt : Summable fun k : ℕ => g (k + N) := (summable_nat_add_iff (f := g) N).mpr hgs
    refine (norm_tsum_le_tsum_norm hzt).trans (Summable.tsum_le_tsum (fun k => ?_) hzt hgt)
    exact LSeries.norm_term_le_of_re_le_re f hzre _
  have key : ∑ k ∈ Finset.range N, f (k + 1) * Complex.exp (-((Real.log ((k : ℝ) + 1) : ℝ) : ℂ) * z)
      = ∑ k ∈ Finset.range N, LSeries.term f z (k + 1) :=
    Finset.sum_congr rfl fun k _ => (hterm k).symm
  rw [key, hsplit, add_sub_cancel_left]
  exact htail.trans (hN N le_rfl)

/-- **Bohr's theorem, almost-periodicity form, for Dirichlet series.**  If `Σ f(n) n^{−s}` converges
absolutely on `Re s = u₀` and agrees on `Re s > u₀` with a function `F` that is holomorphic and
bounded on `Re s > x`, then `F` is almost periodic on every closed strip `l' ≤ Re s ≤ u` with
`x < l'` and `u₀ < u`. -/
theorem isStripAlmostPeriodicOn_of_bounded_LSeries {f : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ u l' M : ℝ}
    (hxl' : x < l') (hl'u : l' ≤ u) (hu : u₀ < u) (hsum : LSeriesSummable f (u₀ : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries f z) :
    IsStripAlmostPeriodicOn F ((l' + u) / 2) ((u - l') / 2) := by
  refine isStripAlmostPeriodicOn_of_bounded_of_line hxl' hl'u hF hM fun ε hε => ?_
  have hap := isStripAlmostPeriodic_LSeries (f := f) (u := u) (R := u - u₀)
    (by rw [show u - (u - u₀) = u₀ by ring]; exact hsum) 0 (by linarith) ε hε
  obtain ⟨L, hL, hτ⟩ := hap
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτz⟩ := hτ a
  refine ⟨τ, hτmem, fun z hz => ?_⟩
  have hz0 : |z.re - u| ≤ 0 := by rw [hz, sub_self, abs_zero]
  have hzτ : (z + (τ : ℂ) * I).re = u := by simp [hz]
  rw [hFL _ (by rw [hzτ]; exact hu), hFL _ (by rw [hz]; exact hu)]
  exact hτz z hz0

end GaloisForLFunctions

end
