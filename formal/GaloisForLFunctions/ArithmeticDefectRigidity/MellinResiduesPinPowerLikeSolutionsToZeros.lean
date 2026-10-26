import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-!
# Mellin residues pin power-like solutions to the translated zeros

Let `0 < ε < 1/2`, `α = 1 − ε`, and `S_ε v(n) = Σ_{j≤n} j^{-ε} v(⌊n/j⌋)`. Suppose a complex row is a finite
power sum plus a row of bounded pronic energy, `v = Σ_{s∈F} c_s n^s + r`, with `1/2 < Re s ≤ 1`,
`s ≠ α`, and satisfies the renormalized inversion law `S_ε v = c' n^α + r'` with `r'` of bounded
energy. Then `ζ(s + ε) = 0` for every `s` with `c_s ≠ 0`
(`riemannZeta_add_eq_zero_of_powerLike_solution`).

The finite-horizon symbol calculus cannot see this: `S_ε` is unbounded on rows of bounded energy,
and nothing excludes `S_ε r` cancelling the power terms at every horizon. The Mellin transform does.
With `𝓜v(w) = Σ v(n)(n^{-w} − (n+1)^{-w})`:

* `𝓜(S_ε v)(w) = ζ(w + ε) 𝓜v(w)` for `Re w > 2` (`rowMellin_cTotalCofactorSum`);
* `𝓜(n^s)(w) = s ζ(w − s + 1) + E_s(w)` with `E_s` holomorphic on `Re w > Re s − 1`
  (`rowMellin_cpow_eq`, `differentiableOn_powerCorrection`);
* `𝓜r` is holomorphic on `Re w > 1/2` for `r` of bounded energy (`differentiableOn_rowMellin`).

So `ζ(w+ε)(Σ c_s(sζ(w−s+1) + E_s) + 𝓜r) − c'(αζ(w−α+1) + E_α) − 𝓜r'` is meromorphic on
`Re w > 1/2` and vanishes on `Re w > 2`, hence near every point; its residue at `s` is
`c_s s ζ(s + ε)`.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinCell complexMellinPairing
  norm_complexMellinCell_le summable_abs_mul_rpow_of_energy differentiableOn_complexMellinPairing)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The complex Mellin transform of a complex row. -/
def rowMellin (v : ℕ → ℂ) (w : ℂ) : ℂ := ∑' n : ℕ, v n * complexMellinCell w n

/-- Bounded pronic energy of a complex row. -/
def EnergyBounded (v : ℕ → ℂ) : Prop :=
  ∃ E : ℝ, ∀ T : ℕ, ∑ n ∈ Icc 1 T, ‖v n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E

/-! ### Rows of bounded energy -/

/-- A row of bounded energy grows at most linearly: `‖r(n)‖ ≤ √E (n + 1)`. -/
theorem norm_le_of_energyBounded {r : ℕ → ℂ} {E : ℝ}
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, ‖r n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) {n : ℕ} (hn : 1 ≤ n) :
    ‖r n‖ ≤ Real.sqrt E * ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ‖r n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := by
    refine le_trans ?_ (hE n)
    exact single_le_sum (f := fun k => ‖r k‖ ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)))
      (fun k _ => by positivity) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have hsq : ‖r n‖ ^ 2 ≤ E * ((n : ℝ) + 1) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hterm
    nlinarith [sq_nonneg ‖r n‖]
  have hE0 : 0 ≤ E := le_trans (by positivity) hterm
  calc ‖r n‖ = Real.sqrt (‖r n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (E * ((n : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt E * ((n : ℝ) + 1) := by
        rw [Real.sqrt_mul hE0, Real.sqrt_sq (by positivity)]

/-- **The Mellin transform of a row of bounded energy is holomorphic on `Re w > 1/2`.** -/
theorem differentiableOn_rowMellin {r : ℕ → ℂ} (hr0 : r 0 = 0) {E : ℝ}
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, ‖r n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) :
    DifferentiableOn ℂ (rowMellin r) {w : ℂ | 1 / 2 < w.re} := by
  have hEre : ∀ T : ℕ, ∑ n ∈ Icc 1 T, (r n).re ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := fun T =>
    le_trans (sum_le_sum fun n _ => div_le_div_of_nonneg_right
      (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2)
      (by positivity)) (hE T)
  have hEim : ∀ T : ℕ, ∑ n ∈ Icc 1 T, (r n).im ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := fun T =>
    le_trans (sum_le_sum fun n _ => div_le_div_of_nonneg_right
      (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2)
      (by positivity)) (hE T)
  have hre0 : (fun n => (r n).re) 0 = 0 := by simp [hr0]
  have him0 : (fun n => (r n).im) 0 = 0 := by simp [hr0]
  have hD := (differentiableOn_complexMellinPairing hre0 hEre).add
    ((differentiableOn_complexMellinPairing him0 hEim).const_mul I)
  refine hD.congr fun w hw => ?_
  have hw' : (1 : ℝ) / 2 < w.re := hw
  -- summability of the real and imaginary parts
  have hsumm : ∀ f : ℕ → ℝ, f 0 = 0 →
      (∀ T : ℕ, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) →
      Summable fun n => (f n : ℂ) * complexMellinCell w n := by
    intro f hf0 hfE
    refine Summable.of_norm_bounded ((summable_abs_mul_rpow_of_energy hw' hf0 hfE).mul_left ‖w‖)
      fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf0]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |f n| * ‖complexMellinCell w n‖ ≤ |f n| * (‖w‖ * (n : ℝ) ^ (-w.re - 1)) :=
          mul_le_mul_of_nonneg_left (norm_complexMellinCell_le (by linarith) hn) (abs_nonneg _)
      _ = ‖w‖ * (|f n| * (n : ℝ) ^ (-w.re - 1)) := by ring
  have h1 := hsumm _ hre0 hEre
  have h2 := hsumm _ him0 hEim
  simp only [Pi.add_apply, rowMellin, complexMellinPairing]
  rw [← tsum_mul_left, ← h1.tsum_add (h2.mul_left I)]
  refine tsum_congr fun n => ?_
  conv_lhs => rw [← Complex.re_add_im (r n)]
  ring

/-! ### The Mellin transform of a power row -/

theorem hasDerivAt_ofReal_cpow_const (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ s) (s * ((x : ℝ) : ℂ) ^ (s - 1)) x := by
  have h := (hasDerivAt_id' (x := (x : ℂ))).cpow_const (c := s)
    (Complex.ofReal_mem_slitPlane.mpr hx)
  simpa using h.comp_ofReal

/-- Mean value bound `‖b^z − u^z‖ ≤ ‖z‖ a^{Re z − 1} (b − u)` for `0 < a ≤ u ≤ b`, `Re z ≤ 1`. -/
theorem norm_ofReal_cpow_sub_le' {z : ℂ} (hz : z.re ≤ 1) {a u b : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hub : u ≤ b) :
    ‖((b : ℝ) : ℂ) ^ z - ((u : ℝ) : ℂ) ^ z‖ ≤ ‖z‖ * a ^ (z.re - 1) * (b - u) := by
  have hu0 : 0 < u := lt_of_lt_of_le ha hau
  refine norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => ((y : ℝ) : ℂ) ^ z) (f' := fun y => z * ((y : ℝ) : ℂ) ^ (z - 1))
    (fun y hy => (hasDerivAt_ofReal_cpow_const z (lt_of_lt_of_le hu0 hy.1)).hasDerivWithinAt)
    (fun y hy => ?_) b ⟨hub, le_rfl⟩
  have hy0 : 0 < y := lt_of_lt_of_le hu0 hy.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (z - 1).re = z.re - 1 := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos ha (hau.trans hy.1) (by linarith)

/-- The second-order defect `e_s(k) = (k+1)^s − k^s − s (k+1)^{s−1}`. -/
def powerDefect (s : ℂ) (k : ℕ) : ℂ :=
  (((k : ℝ) + 1 : ℝ) : ℂ) ^ s - ((k : ℝ) : ℂ) ^ s - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1)

/-- `‖e_s(k)‖ ≤ ‖s‖ ‖s − 1‖ k^{Re s − 2}` for `k ≥ 1` and `Re s ≤ 2`. -/
theorem norm_powerDefect_le {s : ℂ} (hs : s.re ≤ 2) {k : ℕ} (hk : 1 ≤ k) :
    ‖powerDefect s k‖ ≤ ‖s‖ * ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set g : ℝ → ℂ := fun x => ((x : ℝ) : ℂ) ^ s - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) * (x : ℂ)
    with hg
  have hderiv : ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), HasDerivWithinAt g
      (s * ((x : ℝ) : ℂ) ^ (s - 1) - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1))
        (Set.Icc (k : ℝ) ((k : ℝ) + 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hk0 hx.1
    have h1 := hasDerivAt_ofReal_cpow_const s hx0
    have h2 : HasDerivAt (fun y : ℝ => s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) * (y : ℂ))
        (s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) * 1) x :=
      (Complex.ofRealCLM.hasDerivAt.const_mul _)
    simpa using (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1),
      ‖s * ((x : ℝ) : ℂ) ^ (s - 1) - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1)‖ ≤
        ‖s‖ * ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) := by
    intro x hx
    have hmv := norm_ofReal_cpow_sub_le' (z := s - 1) (by simp; linarith) hk0 hx.1 hx.2.le
    rw [← mul_sub, norm_mul, norm_sub_rev, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (s - 1).re - 1 = s.re - 2 := by simp; ring
    rw [hre] at hmv
    calc _ ≤ ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) * ((k : ℝ) + 1 - x) := hmv
      _ ≤ ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) * 1 := by
          refine mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by positivity)
      _ = _ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound ((k : ℝ) + 1)
    ⟨by linarith, le_rfl⟩
  rw [show (k : ℝ) + 1 - k = 1 by ring, mul_one] at h
  have hid : g ((k : ℝ) + 1) - g k = powerDefect s k := by
    simp only [hg, powerDefect]
    push_cast
    ring
  rw [← hid]
  exact h

end GaloisForLFunctions.ArithmeticDefectRigidity
