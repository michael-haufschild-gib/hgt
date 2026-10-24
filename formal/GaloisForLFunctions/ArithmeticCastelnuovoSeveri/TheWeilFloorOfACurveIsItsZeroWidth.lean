import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFirstNegativeLagOfACurve
import GaloisForLFunctions.SquareRootThreshold.WeilGroundStateLawOnLagLattices

/-!
# The Weil floor of a curve is its zero width

For `ζ` the degree-defect floor rate of Weil's form equals twice the zero width
(`RiemannRochForZAndTheReflectedPrimePolarLedger`, Square-Root Threshold mechanism 31). This file
proves the exact `𝔽_q` form on the scaling surface of a curve datum. Let `L = log q`, `N = 2g` the
number of eigenvalues, `R ≥ 1` a bound for their moduli, and `δ = log R / L` (the zero width when
`R = max |β_i|`).

* **Floor** (`re_W_curveConfig_ge_floor`). Every `C²` test supported in `[−a, a]` has
  `Re W(f, f) ≥ −2N L n e^{2δa} ‖f‖²`, `n = ⌈2a/L⌉`. The ground-state law of lag lattices
  (`SquareRootThreshold.weil_floor_iff_toeplitz_floor`) reduces the floor to the Toeplitz window,
  and Gershgorin bounds the window by `|t_m| ≤ N R^{|m|}`.
* **Sharpness** (`exists_lagTest_le`). If an eigenvalue has modulus `R > 1`, then in every window
  `[M + 1, M + N]` some lag `ν` and sign carry a two-bump test with
  `Re W(f, f) ≤ L (N − R^ν/C_M) ‖f‖²`, `C_M = 2e N (6(N + 1)(M + 2N + 2))^N` polynomial in `M`
  (Turán, `HTGeometry.exists_norm_powerSum_ge_scaled`).

So at aperture `a ≈ νL/2` the floor lies between `−C a e^{2δa}` and `−c e^{2δa}/poly(a)`: the
exponential rate of the Weil floor of a curve is exactly twice its zero width, and is `0` iff the
curve is pure. The `ζ` law is the arithmetic form of this calibration.
-/

open Complex MeasureTheory Finset
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (toeplitzForm re_toeplitzForm_ge
  weil_floor_iff_toeplitz_floor)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- Each trace is bounded by the eigenvalue moduli: `|t_m| ≤ N R^m`. -/
theorem abs_trace_le {R : ℝ} (hR : ∀ i, ‖D.β i‖ ≤ R) (m : ℕ) :
    |D.trace m| ≤ Fintype.card ι * R ^ m := by
  rw [D.abs_trace_eq_norm_powerSum]
  calc ‖∑ i, D.β i ^ m‖ ≤ ∑ i, ‖D.β i ^ m‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, R ^ m := Finset.sum_le_sum fun i _ => by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hR i) m
    _ = Fintype.card ι * R ^ m := by simp

/-- **The Weil floor of a curve.** Every `C²` test supported in `[−a, a]` satisfies
`Re W(f, f) ≥ −2N log q · n · e^{2δa} ‖f‖²` with `n = ⌈2a/log q⌉` and `δ = log R / log q`. -/
theorem re_W_curveConfig_ge_floor {R : ℝ} (hR1 : 1 ≤ R) (hR : ∀ i, ‖D.β i‖ ≤ R) {a : ℝ}
    (ha : 0 < a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Set.Icc (-a) a) :
    -(2 * Fintype.card ι * Real.log D.q * ⌈2 * a / Real.log D.q⌉₊ *
        Real.exp (2 * (Real.log R / Real.log D.q) * a)) * ∫ u, ‖f u‖ ^ 2 ≤
      ((D.curveConfig hD).W f f).re := by
  have hL := D.log_q_pos
  set n : ℕ := ⌈2 * a / Real.log D.q⌉₊ with hn
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  -- `R^{n−1} ≤ e^{2δa}`
  have hRn : R ^ (n - 1) ≤ Real.exp (2 * (Real.log R / Real.log D.q) * a) := by
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
    have hn1 : ((n - 1 : ℕ) : ℝ) ≤ 2 * a / Real.log D.q := by
      have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * a / Real.log D.q by positivity)
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0]; simp; positivity
      · rw [Nat.cast_sub hpos, Nat.cast_one]; rw [← hn] at hlt; linarith
    calc Real.log R * ((n - 1 : ℕ) : ℝ) ≤ Real.log R * (2 * a / Real.log D.q) :=
          mul_le_mul_of_nonneg_left hn1 hlogR
      _ = 2 * (Real.log R / Real.log D.q) * a := by ring
  -- the Gershgorin floor of the window
  set μ : ℝ := -(2 * N * n * R ^ (n - 1)) with hμ
  have hwin : ∀ c : Fin n → ℂ, μ * ∑ j, ‖c j‖ ^ 2 ≤
      (toeplitzForm (fun m : ℤ => (D.trace m.natAbs : ℂ)) n c).re := by
    intro c
    refine le_trans ?_ (re_toeplitzForm_ge _ c)
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity)
    have hterm : ∀ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0,
        ‖((D.trace m.natAbs : ℝ) : ℂ)‖ ≤ N * R ^ (n - 1) := by
      intro m hm
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine (D.abs_trace_le hR _).trans ?_
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 ?_) hN0
      have := Finset.mem_Ioo.mp (Finset.mem_of_mem_erase hm)
      omega
    have hcard : ((Finset.Ioo (-(n : ℤ)) n).erase 0).card ≤ 2 * n := by
      refine (Finset.card_erase_le).trans ?_
      rw [Int.card_Ioo]
      omega
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul] at hsum
    have h0 : (((D.trace (0 : ℤ).natAbs : ℝ) : ℂ)).re = N := by
      simp [hN, D.trace_zero]
    simp only [h0]
    have hcard' : (((Finset.Ioo (-(n : ℤ)) n).erase 0).card : ℝ) ≤ 2 * n := by
      exact_mod_cast hcard
    have hpos : 0 ≤ N * R ^ (n - 1) := mul_nonneg hN0 (pow_nonneg (by linarith) _)
    nlinarith
  have hW := (weil_floor_iff_toeplitz_floor (D.curveConfig hD) hL _
    (fun f hf hfc => D.W_curveConfig_lagFormula hD hf hfc) ha μ).mpr hwin f hf hfs
  refine le_trans ?_ hW
  have hI : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hpow : 0 ≤ R ^ (n - 1) := pow_nonneg (by linarith) _
  rw [hμ]
  have : Real.log D.q * (2 * N * n * R ^ (n - 1)) ≤
      2 * N * Real.log D.q * n * Real.exp (2 * (Real.log R / Real.log D.q) * a) := by
    have hc : 0 ≤ 2 * N * Real.log D.q * n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hRn hc]
  nlinarith

/-- The two copies of a narrow bump in a lag test do not overlap: `‖g + s g(· − v)‖² = 2‖g‖²`
for `|s| = 1` and `v` beyond the width. -/
theorem integral_norm_sq_lagTest {g : ℝ → ℂ} {w : ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) {s : ℝ} (hs : s = 1 ∨ s = -1) {v : ℝ}
    (hv : w < v) :
    ∫ u, ‖lagTest g s v u‖ ^ 2 = 2 * ∫ u, ‖g u‖ ^ 2 := by
  have hgz : ∀ u, g u ≠ 0 → |u| ≤ w / 2 := fun u hu => abs_le.mpr (hgs (subset_tsupport _ hu))
  have hpt : ∀ u, ‖lagTest g s v u‖ ^ 2 = ‖g u‖ ^ 2 + ‖g (u - v)‖ ^ 2 := by
    intro u
    simp only [lagTest]
    by_cases h1 : g u = 0
    · rw [h1, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rcases hs with rfl | rfl <;> simp
    · have h2 : g (u - v) = 0 := by
        by_contra h2
        have h3 := abs_le.mp (hgz u h1)
        have h4 := abs_le.mp (hgz (u - v) h2)
        linarith [h3.2, h4.1]
      rw [h2, mul_zero, add_zero, norm_zero]
      ring
  have hgc : HasCompactSupport g := RHTower.hasCompactSupport_of_tsupport_subset_Icc hgs
  have hgi : Integrable fun u => ‖g u‖ ^ 2 := by
    have h : Integrable fun u => ‖g u‖ * ‖g u‖ :=
      (hg.norm.mul hg.norm).integrable_of_hasCompactSupport hgc.norm.mul_right
    simpa only [← pow_two] using h
  rw [show (fun u => ‖lagTest g s v u‖ ^ 2) = fun u => ‖g u‖ ^ 2 + ‖g (u - v)‖ ^ 2 from
    funext hpt, integral_add hgi (hgi.comp_sub_right v), integral_sub_right_eq_self
    (fun u => ‖g u‖ ^ 2) v]
  ring

/-- **Sharpness of the floor.** If an eigenvalue has modulus `R > 1`, then for every `M` some lag
`ν ∈ [M + 1, M + N]` and sign `s = ±1` give a two-bump test with
`Re W(f, f) ≤ log q · (N − R^ν / C_M) · ‖f‖²`. -/
theorem exists_lagTest_le {i₀ : ι} (hR : 1 < ‖D.β i₀‖) (M : ℕ) {g : ℝ → ℂ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2))
    (hwL : w < Real.log D.q) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + Fintype.card ι ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ((D.curveConfig hD).W (lagTest g s (ν * Real.log D.q))
        (lagTest g s (ν * Real.log D.q))).re ≤
        Real.log D.q * (Fintype.card ι - ‖D.β i₀‖ ^ ν /
          (2 * (Real.exp 1 * Fintype.card ι * (6 * (Fintype.card ι + 1) *
            ((M : ℝ) + 2 * Fintype.card ι + 2)) ^ Fintype.card ι))) *
        ∫ u, ‖lagTest g s (ν * Real.log D.q) u‖ ^ 2 := by
  set R := ‖D.β i₀‖ with hRdef
  set N : ℕ := Fintype.card ι with hN
  have hR0 : 0 < R := by linarith
  obtain ⟨ν, hν1, hν2, hνT⟩ := exists_norm_powerSum_ge_scaled Finset.univ (fun i => D.β i) hR0
    ⟨i₀, Finset.mem_univ _, le_rfl⟩ M
  simp only [Finset.card_univ] at hν2 hνT
  refine ⟨ν, hν1, hν2, ?_⟩
  have hL := D.log_q_pos
  have hνpos : 1 ≤ ν := by omega
  have hvw : w < ν * Real.log D.q := by
    have : (1 : ℝ) ≤ ν := by exact_mod_cast hνpos
    nlinarith
  have hbig : R ^ ν / (2 * (Real.exp 1 * N * (6 * (N + 1) * ((M : ℝ) + 2 * N + 2)) ^ N)) ≤
      |D.trace ν| := by
    rw [D.abs_trace_eq_norm_powerSum]; exact hνT
  have hI : 0 ≤ ∫ u, ‖g u‖ ^ 2 := integral_nonneg fun _ => by positivity
  rcases le_or_gt 0 (D.trace ν) with hpos | hneg
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [D.re_W_curveConfig_lagTest hD hg hgs hwL, integral_norm_sq_lagTest hg.continuous hgs
      (Or.inr rfl) hvw, D.trace_zero, ← hN]
    rw [abs_of_nonneg hpos] at hbig
    nlinarith [mul_le_mul_of_nonneg_left hbig (mul_nonneg hL.le hI)]
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [D.re_W_curveConfig_lagTest hD hg hgs hwL, integral_norm_sq_lagTest hg.continuous hgs
      (Or.inl rfl) hvw, D.trace_zero, ← hN]
    rw [abs_of_neg hneg] at hbig
    nlinarith [mul_le_mul_of_nonneg_left hbig (mul_nonneg hL.le hI)]

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
