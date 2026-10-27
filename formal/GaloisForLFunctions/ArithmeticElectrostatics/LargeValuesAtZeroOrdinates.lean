import GaloisForLFunctions.RHTower.LargeValues
import GaloisForLFunctions.RHTower.Sieve.DirichletMVT
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Large values of Dirichlet polynomials at zero ordinates

The zero ordinates `γ` are points of the prime torus through the phases `γ log n`; a Dirichlet
polynomial `F(t) = Σ_{n ≤ N} a_n n^{it}` is a function on that torus, and its large values mark the
aligned phases. Both zero-side detectors of the frontier — the odd detector and the outward reserve
— ask how often zero ordinates are aligned with short prime polynomials. This file bounds that
frequency by a second moment.

* **Cell Sobolev bound** (`normSq_dirPoly_le_cell`): at a point `t ∈ [c, c + 1]`,
  `|F(t)|² ≤ 2∫_c^{c+1}|F|² + ∫_c^{c+1}|F′|²`.
* **Window mean value** (`integral_window_normSq_dirPoly_le`): `∫_A^{A+R} |F|² ≤ (R + 8N(1 + log N)) Σ|a_n|²`.
* **The discrete mean value over zeros** (`exists_sum_zeroOrdinates_normSq_le`): for zero copies with
  ordinates in `(A, A + R]`, `A ≥ T₀`,
  `Σ_γ |F(γ)|² ≤ K log(A + R + 1) (R + 8N(1 + log N)) (2 + log² N) Σ|a_n|²`.
  Each unit cell holds `O(log)` zero copies (the local zero ceiling), and each copy is controlled by
  its cell's mean square.
* **Large values** (`exists_card_largeValues_le`): the number of zero copies in the window at which
  `|F(γ)| ≥ V` is at most the same bound divided by `V²`.
* **The prime polynomial** (`coeffMass_primeCoeff_le`, `exists_card_aligned_le`): for
  `a_n = w_n Λ(n)/√n`, `|w_n| ≤ 1`, the mass is at most `log N (log N + log 4 + 4)` (Mertens), which
  gives the explicit alignment law.

For the detector polynomial with `a_n = Λ(n)/√n`, `n ≤ X`, the coefficient mass is `O(log² X)`, so the
zero ordinates in `(T, 2T]` at which the polynomial reaches `(1 − η) log T` number
`O(T log⁴ X / log T)`: a vanishing proportion of the `≍ T log T` zeros as long as
`log X = o(√log T)`, which covers every aperture up to the forcing threshold. Excluding isolated deep
zeros needs a power saving; applied to powers `F^k` (again Dirichlet polynomials, of length `N^k`)
the same law gives the higher moments.
-/

noncomputable section

open Finset MeasureTheory intervalIntegral RHTower RHTower.Sieve

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- The **coefficient mass** `Σ ‖a_n‖²`. -/
def coeffMass {N : ℕ} (a : Fin N → ℂ) : ℝ := ∑ m, ‖a m‖ ^ 2

theorem coeffMass_nonneg {N : ℕ} (a : Fin N → ℂ) : 0 ≤ coeffMass a :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- Differentiation multiplies the mass by at most `log² N`. -/
theorem coeffMass_dirDerivCoeff_le {N : ℕ} (a : Fin N → ℂ) :
    coeffMass (dirDerivCoeff N a) ≤ Real.log N ^ 2 * coeffMass a := by
  rw [coeffMass, coeffMass, mul_sum]
  refine sum_le_sum fun m _ => ?_
  rw [dirDerivCoeff, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have h1 : (1 : ℝ) ≤ (m : ℕ) + 1 := by linarith [(Nat.cast_nonneg (m : ℕ) : (0 : ℝ) ≤ (m : ℕ))]
  have h2 : ((m : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast m.2
  have hl0 : 0 ≤ Real.log (((m : ℕ) : ℝ) + 1) := Real.log_nonneg h1
  exact pow_le_pow_left₀ hl0 (Real.log_le_log (by linarith) h2) 2

/-- **Cell Sobolev bound**: `|F(t)|² ≤ 2∫_c^{c+1}|F|² + ∫_c^{c+1}|F′|²` for `t ∈ [c, c + 1]`. -/
theorem normSq_dirPoly_le_cell {N : ℕ} (a : Fin N → ℂ) {c t : ℝ} (ht : t ∈ Set.Icc c (c + 1)) :
    ‖dirPoly N a t‖ ^ 2 ≤ 2 * (∫ u in c..c + 1, ‖dirPoly N a u‖ ^ 2) +
      ∫ u in c..c + 1, ‖dirPoly N (dirDerivCoeff N a) u‖ ^ 2 := by
  have hF := continuous_dirPoly N a
  have hF' := continuous_dirPoly N (dirDerivCoeff N a)
  have hsob := sobolev_pointwise (f := dirPoly N a) (f' := dirPoly N (dirDerivCoeff N a))
    (c := c) (δ := 1) one_pos (fun y _ => hasDerivAt_dirPoly N a y)
    ((continuous_const.mul (hF.inner hF')).intervalIntegrable _ _)
    ((hF.norm.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (hF.norm.mul hF'.norm)).intervalIntegrable _ _) ht
  have hcross : (∫ u in c..c + 1, 2 * (‖dirPoly N a u‖ * ‖dirPoly N (dirDerivCoeff N a) u‖)) ≤
      ∫ u in c..c + 1, (‖dirPoly N a u‖ ^ 2 + ‖dirPoly N (dirDerivCoeff N a) u‖ ^ 2) :=
    integral_mono_on (by linarith)
      ((continuous_const.mul (hF.norm.mul hF'.norm)).intervalIntegrable _ _)
      (((hF.norm.pow 2).add (hF'.norm.pow 2)).intervalIntegrable _ _)
      fun u _ => by nlinarith [sq_nonneg (‖dirPoly N a u‖ - ‖dirPoly N (dirDerivCoeff N a) u‖)]
  have hadd : (∫ u in c..c + 1, (‖dirPoly N a u‖ ^ 2 + ‖dirPoly N (dirDerivCoeff N a) u‖ ^ 2)) =
      (∫ u in c..c + 1, ‖dirPoly N a u‖ ^ 2) +
        ∫ u in c..c + 1, ‖dirPoly N (dirDerivCoeff N a) u‖ ^ 2 :=
    intervalIntegral.integral_add ((hF.norm.pow 2).intervalIntegrable _ _)
      ((hF'.norm.pow 2).intervalIntegrable _ _)
  simp only [div_one, one_mul] at hsob
  linarith

/-- **Window mean value**: `∫_A^{A+R} |F|² ≤ (R + 8N(1 + log N)) Σ|a_n|²`. -/
theorem integral_window_normSq_dirPoly_le {N : ℕ} (a : Fin N → ℂ) (A R : ℝ) :
    ∫ u in A..A + R, ‖dirPoly N a u‖ ^ 2 ≤ (R + 8 * N * (1 + Real.log N)) * coeffMass a := by
  have hF := continuous_dirPoly N a
  have hsplit : ∫ u in A..A + R, ‖dirPoly N a u‖ ^ 2 =
      (∫ u in (0 : ℝ)..A + R, ‖dirPoly N a u‖ ^ 2) - ∫ u in (0 : ℝ)..A, ‖dirPoly N a u‖ ^ 2 :=
    (intervalIntegral.integral_interval_sub_left ((hF.norm.pow 2).intervalIntegrable _ _)
      ((hF.norm.pow 2).intervalIntegrable _ _)).symm
  have h1 := abs_le.mp (dirichlet_meanValue_theorem N a (A + R))
  have h2 := abs_le.mp (dirichlet_meanValue_theorem N a A)
  rw [hsplit, coeffMass]
  nlinarith [h1.2, h2.1]

/-- Cells of unit length: an ordinate in `(A, A + R]` lies in the cell `(A + k, A + k + 1]` with
`k = ⌈γ − A⌉ − 1 < R`. -/
theorem cell_spec {A x : ℝ} {R : ℕ} (h1 : A < x) (h2 : x ≤ A + R) :
    ⌈x - A⌉₊ - 1 < R ∧ A + ((⌈x - A⌉₊ - 1 : ℕ) : ℝ) < x ∧ x ≤ A + ((⌈x - A⌉₊ - 1 : ℕ) : ℝ) + 1 := by
  have hpos : 0 < x - A := by linarith
  have hc1 : 1 ≤ ⌈x - A⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hpos).ne'
  have hle : x - A ≤ ⌈x - A⌉₊ := Nat.le_ceil _
  have hlt : (⌈x - A⌉₊ : ℝ) < x - A + 1 := Nat.ceil_lt_add_one hpos.le
  have hcR : ⌈x - A⌉₊ ≤ R := Nat.ceil_le.mpr (by linarith)
  have hcast : ((⌈x - A⌉₊ - 1 : ℕ) : ℝ) = (⌈x - A⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hc1, Nat.cast_one]
  refine ⟨by omega, ?_, ?_⟩ <;> rw [hcast] <;> linarith

/-- **The discrete mean value over zero ordinates.** -/
theorem exists_sum_zeroOrdinates_normSq_le :
    ∃ K T₀ : ℝ, 0 < K ∧ 4 ≤ T₀ ∧ ∀ A : ℝ, T₀ ≤ A → ∀ R : ℕ, ∀ G : Finset XiZeroCopy,
      (∀ q ∈ G, A < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ A + R) → ∀ (N : ℕ) (a : Fin N → ℂ),
      ∑ q ∈ G, ‖dirPoly N a (q.1 : ℂ).im‖ ^ 2 ≤
        K * Real.log (A + R + 1) * ((R + 8 * N * (1 + Real.log N)) *
          ((2 + Real.log N ^ 2) * coeffMass a)) := by
  obtain ⟨C, hC, T₀, hT₀, hcount⟩ := exists_card_window_le
  refine ⟨1 / (2 * Real.pi) + 2 * C, T₀, by positivity, hT₀, fun A hA R G hG N a => ?_⟩
  set K := 1 / (2 * Real.pi) + 2 * C
  set F := dirPoly N a
  set F' := dirPoly N (dirDerivCoeff N a)
  set cell : XiZeroCopy → ℕ := fun q => ⌈(q.1 : ℂ).im - A⌉₊ - 1
  set g : ℕ → ℝ := fun k => 2 * (∫ u in A + k..A + k + 1, ‖F u‖ ^ 2) +
    ∫ u in A + k..A + k + 1, ‖F' u‖ ^ 2
  have hg0 : ∀ k : ℕ, 0 ≤ g k := fun k => by
    have h1 : 0 ≤ ∫ u in A + k..A + k + 1, ‖F u‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun u _ => sq_nonneg _
    have h2 : 0 ≤ ∫ u in A + k..A + k + 1, ‖F' u‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun u _ => sq_nonneg _
    simp only [g]; linarith
  have hmaps : ∀ q ∈ G, cell q ∈ range R := fun q hq =>
    mem_range.mpr (cell_spec (hG q hq).1 (hG q hq).2).1
  have hlogpos : 0 ≤ Real.log (A + R + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith)
  -- each cell holds at most `K log(A + R + 1)` zero copies
  have hcard : ∀ k ∈ range R, ((G.filter fun q => cell q = k).card : ℝ) ≤
      K * Real.log (A + R + 1) := by
    intro k hk
    have hkR : (k : ℝ) + 1 ≤ R := by exact_mod_cast mem_range.mp hk
    have h := hcount (A + k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) 1 zero_le_one
      (G.filter fun q => cell q = k) fun q hq => by
        obtain ⟨hqG, hqk⟩ := mem_filter.mp hq
        have hs := cell_spec (hG q hqG).1 (hG q hqG).2
        have hqk' : ⌈(q.1 : ℂ).im - A⌉₊ - 1 = k := hqk
        rw [hqk'] at hs
        exact ⟨hs.2.1, by linarith [hs.2.2]⟩
    have hlog : Real.log (A + k + 1) ≤ Real.log (A + R + 1) :=
      Real.log_le_log (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by linarith)
    calc ((G.filter fun q => cell q = k).card : ℝ)
        ≤ 1 / (2 * Real.pi) * Real.log (A + k + 1) + 2 * C * Real.log (A + k + 1) := h
      _ = K * Real.log (A + k + 1) := by simp only [K]; ring
      _ ≤ K * Real.log (A + R + 1) := mul_le_mul_of_nonneg_left hlog (by positivity)
  -- each copy is controlled by its cell
  have hcellBound : ∀ k ∈ range R, ∑ q ∈ G.filter (fun q => cell q = k), ‖F (q.1 : ℂ).im‖ ^ 2 ≤
      K * Real.log (A + R + 1) * g k := by
    intro k hk
    calc ∑ q ∈ G.filter (fun q => cell q = k), ‖F (q.1 : ℂ).im‖ ^ 2
        ≤ ∑ _q ∈ G.filter (fun q => cell q = k), g k := by
          refine sum_le_sum fun q hq => ?_
          obtain ⟨hqG, hqk⟩ := mem_filter.mp hq
          have hs := cell_spec (hG q hqG).1 (hG q hqG).2
          have hqk' : ⌈(q.1 : ℂ).im - A⌉₊ - 1 = k := hqk
          rw [hqk'] at hs
          exact normSq_dirPoly_le_cell a ⟨hs.2.1.le, hs.2.2⟩
      _ = ((G.filter fun q => cell q = k).card : ℝ) * g k := by rw [sum_const, nsmul_eq_mul]
      _ ≤ K * Real.log (A + R + 1) * g k := mul_le_mul_of_nonneg_right (hcard k hk) (hg0 k)
  -- the cells tile the window
  have htile : ∑ k ∈ range R, g k = 2 * (∫ u in A..A + R, ‖F u‖ ^ 2) +
      ∫ u in A..A + R, ‖F' u‖ ^ 2 := by
    have hF := continuous_dirPoly N a
    have hF' := continuous_dirPoly N (dirDerivCoeff N a)
    have e : ∀ h : ℝ → ℝ, Continuous h →
        ∑ k ∈ range R, ∫ u in A + k..A + k + 1, h u = ∫ u in A..A + R, h u := by
      intro h hh
      have := sum_integral_adjacent_intervals (μ := volume) (a := fun k : ℕ => A + k) (n := R)
        (fun k _ => hh.intervalIntegrable _ _)
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at this
      rw [← this]
      exact sum_congr rfl fun k _ => by rw [add_assoc]
    have e1 : ∑ k ∈ range R, ∫ u in A + k..A + k + 1, ‖F u‖ ^ 2 = ∫ u in A..A + R, ‖F u‖ ^ 2 :=
      e _ (hF.norm.pow 2)
    have e2 : ∑ k ∈ range R, ∫ u in A + k..A + k + 1, ‖F' u‖ ^ 2 = ∫ u in A..A + R, ‖F' u‖ ^ 2 :=
      e _ (hF'.norm.pow 2)
    simp only [g, sum_add_distrib, ← mul_sum]
    rw [e1, e2]
  have hmv := integral_window_normSq_dirPoly_le a A R
  have hmv' := integral_window_normSq_dirPoly_le (dirDerivCoeff N a) A R
  have hmass' := coeffMass_dirDerivCoeff_le a
  have hRpos : 0 ≤ (R : ℝ) + 8 * N * (1 + Real.log N) := by
    have := Real.log_natCast_nonneg N
    positivity
  calc ∑ q ∈ G, ‖F (q.1 : ℂ).im‖ ^ 2
      = ∑ k ∈ range R, ∑ q ∈ G.filter (fun q => cell q = k), ‖F (q.1 : ℂ).im‖ ^ 2 :=
        (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ range R, K * Real.log (A + R + 1) * g k := sum_le_sum hcellBound
    _ = K * Real.log (A + R + 1) * (2 * (∫ u in A..A + R, ‖F u‖ ^ 2) +
          ∫ u in A..A + R, ‖F' u‖ ^ 2) := by rw [← mul_sum, htile]
    _ ≤ K * Real.log (A + R + 1) * ((R + 8 * N * (1 + Real.log N)) *
          ((2 + Real.log N ^ 2) * coeffMass a)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h3 : (R + 8 * N * (1 + Real.log N)) * coeffMass (dirDerivCoeff N a) ≤
            (R + 8 * N * (1 + Real.log N)) * (Real.log N ^ 2 * coeffMass a) :=
          mul_le_mul_of_nonneg_left hmass' hRpos
        nlinarith

/-- **Large values at zero ordinates**: zero copies in the window at which `|F(γ)| ≥ V` number at
most the discrete mean square divided by `V²`. -/
theorem exists_card_largeValues_le :
    ∃ K T₀ : ℝ, 0 < K ∧ 4 ≤ T₀ ∧ ∀ A : ℝ, T₀ ≤ A → ∀ R : ℕ, ∀ G : Finset XiZeroCopy,
      (∀ q ∈ G, A < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ A + R) → ∀ (N : ℕ) (a : Fin N → ℂ) (V : ℝ),
      0 ≤ V →
      ((G.filter fun q => V ≤ ‖dirPoly N a (q.1 : ℂ).im‖).card : ℝ) * V ^ 2 ≤
        K * Real.log (A + R + 1) * ((R + 8 * N * (1 + Real.log N)) *
          ((2 + Real.log N ^ 2) * coeffMass a)) := by
  obtain ⟨K, T₀, hK, hT₀, h⟩ := exists_sum_zeroOrdinates_normSq_le
  refine ⟨K, T₀, hK, hT₀, fun A hA R G hG N a V hV => ?_⟩
  refine le_trans ?_ (h A hA R (G.filter fun q => V ≤ ‖dirPoly N a (q.1 : ℂ).im‖)
    (fun q hq => hG q (mem_filter.mp hq).1) N a)
  calc ((G.filter fun q => V ≤ ‖dirPoly N a (q.1 : ℂ).im‖).card : ℝ) * V ^ 2
      = ∑ _q ∈ G.filter (fun q => V ≤ ‖dirPoly N a (q.1 : ℂ).im‖), V ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ q ∈ G.filter (fun q => V ≤ ‖dirPoly N a (q.1 : ℂ).im‖), ‖dirPoly N a (q.1 : ℂ).im‖ ^ 2 :=
        sum_le_sum fun q hq => pow_le_pow_left₀ hV (mem_filter.mp hq).2 2

/-! ### The prime polynomial -/

/-- The coefficients `w_n Λ(n)/√n`, indexed by `n − 1`. -/
def primeCoeff {N : ℕ} (w : Fin N → ℂ) : Fin N → ℂ := fun m =>
  w m * ((ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) / Real.sqrt (((m : ℕ) : ℝ) + 1) : ℝ) : ℂ)

/-- **The mass of the prime polynomial**: `Σ |w_n Λ(n)/√n|² ≤ log N (log N + log 4 + 4)`. -/
theorem coeffMass_primeCoeff_le {N : ℕ} (hN : 1 ≤ N) (w : Fin N → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) :
    coeffMass (primeCoeff w) ≤ Real.log N * (Real.log N + (Real.log 4 + 4)) := by
  have hterm : ∀ m : Fin N, ‖primeCoeff w m‖ ^ 2 ≤
      Real.log N * (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) / (((m : ℕ) + 1 : ℕ) : ℝ)) := by
    intro m
    have hn : (0 : ℝ) < ((m : ℕ) : ℝ) + 1 := by positivity
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := (m : ℕ) + 1)
    have hΛle : ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) ≤ Real.log N := by
      have h1 := ArithmeticFunction.vonMangoldt_le_log (n := (m : ℕ) + 1)
      have h2 : Real.log (((m : ℕ) + 1 : ℕ) : ℝ) ≤ Real.log N :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_of_lt m.2)
      linarith
    rw [primeCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow,
      Real.sq_sqrt hn.le]
    have hw2 : ‖w m‖ ^ 2 ≤ 1 := by
      have := hw m; nlinarith [norm_nonneg (w m)]
    push_cast
    calc ‖w m‖ ^ 2 * (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) ^ 2 / (((m : ℕ) : ℝ) + 1))
        ≤ 1 * (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) ^ 2 / (((m : ℕ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hw2 (by positivity)
      _ ≤ Real.log N * (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) / (((m : ℕ) : ℝ) + 1)) := by
          rw [one_mul, sq, mul_div_assoc, mul_comm]
          rw [mul_comm (Real.log N)]
          exact mul_le_mul_of_nonneg_left hΛle (div_nonneg hΛ hn.le)
  have hsum : ∑ m : Fin N, ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) / (((m : ℕ) + 1 : ℕ) : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / d := by
    rw [Fin.sum_univ_eq_sum_range (fun m => ArithmeticFunction.vonMangoldt (m + 1) /
      ((m + 1 : ℕ) : ℝ)) N, Finset.range_eq_Ico]
    rw [Finset.sum_Ico_add' (fun d => ArithmeticFunction.vonMangoldt d / (d : ℝ)) 0 N 1]
    rfl
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first N hN)).2
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc coeffMass (primeCoeff w) ≤ ∑ m : Fin N, Real.log N *
        (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) / (((m : ℕ) + 1 : ℕ) : ℝ)) :=
        sum_le_sum fun m _ => hterm m
    _ = Real.log N * ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / d := by
        rw [← mul_sum, hsum]
    _ ≤ Real.log N * (Real.log N + (Real.log 4 + 4)) :=
        mul_le_mul_of_nonneg_left (by linarith) hlogN

/-- **The alignment law at zero ordinates**: the zero copies in `(A, A + R]` at which the prime
polynomial `Σ_{n ≤ N} w_n Λ(n) n^{−1/2 + iγ}` (`|w_n| ≤ 1`) has modulus at least `V` number at most
`K log(A + R + 1)(R + 8N(1 + log N))(2 + log² N) log N (log N + log 4 + 4)/V²`. -/
theorem exists_card_aligned_le :
    ∃ K T₀ : ℝ, 0 < K ∧ 4 ≤ T₀ ∧ ∀ A : ℝ, T₀ ≤ A → ∀ R : ℕ, ∀ G : Finset XiZeroCopy,
      (∀ q ∈ G, A < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ A + R) → ∀ (N : ℕ), 1 ≤ N →
      ∀ (w : Fin N → ℂ), (∀ m, ‖w m‖ ≤ 1) → ∀ V : ℝ, 0 ≤ V →
      ((G.filter fun q => V ≤ ‖dirPoly N (primeCoeff w) (q.1 : ℂ).im‖).card : ℝ) * V ^ 2 ≤
        K * Real.log (A + R + 1) * ((R + 8 * N * (1 + Real.log N)) *
          ((2 + Real.log N ^ 2) * (Real.log N * (Real.log N + (Real.log 4 + 4))))) := by
  obtain ⟨K, T₀, hK, hT₀, h⟩ := exists_card_largeValues_le
  refine ⟨K, T₀, hK, hT₀, fun A hA R G hG N hN w hw V hV => ?_⟩
  refine (h A hA R G hG N (primeCoeff w) V hV).trans ?_
  have hlog : 0 ≤ Real.log (A + R + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith)
  have hR : 0 ≤ (R : ℝ) + 8 * N * (1 + Real.log N) := by
    have := Real.log_natCast_nonneg N
    positivity
  have h2 : 0 ≤ 2 + Real.log N ^ 2 := by positivity
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (coeffMass_primeCoeff_le hN w hw) h2) hR) (by positivity)

end GaloisForLFunctions.ArithmeticElectrostatics
