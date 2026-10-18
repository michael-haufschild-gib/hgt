import GaloisForLFunctions.«arithmetic-positivity-theory».RankOnePoleReadoutAndZeroNullspace

/-! Smoothed compact-ramp Weil lower and upper bounds, relative zero-sampling margin,
smoothing-limit transfer, translation-increment contraction, and two-dimensional
ramp–tent Gram/Schur coercivity (`APT-ROOT-RAMP-MARGIN` and `APT-ROOT-RAMP-LIMIT`).

Using the exact readout splitting `r_{n,k} = H_{n,k} - U_{n,k}` established in
`RankOnePoleReadoutAndZeroNullspace`, the corrected-source square-sampling bound
`Z(H_{n,k}) ≤ C_H / (n + 1)`, the tail square-sampling bound
`Z(U_{n,k}) ≤ C_U (1 + log(n + 1)) / (n + 1)`, and the eventual tail Weil diagonal
growth `Re W(U_{n,k}, U_{n,k}) ≥ log(n + 1) / (2048 (n + 1))`, we prove:
1. Eventually in `n` and then eventually in `k`, the smoothed compact ramp satisfies
   `Re W(r_{n,k}, r_{n,k}) ≥ log(n + 1) / (4096 (n + 1))`.
2. Uniformly for all `n, k`, `‖W(r_{n,k}, r_{n,k})‖ ≤ C (1 + log(n + 1)) / (n + 1)`
   with `C = 2 (C_H + C_U)`.
3. Consequently, the smoothed compact ramp carries a uniform relative positive margin
   `Re W(r_{n,k}, r_{n,k}) ≥ δ Z(r_{n,k})` eventually in `n` and `k`.
4. Passing to the `k → ∞` limit transfers both logarithmic bounds to any limiting
   unsmoothed ramp diagonal energy `A_n`, and coupling with a tent block `D_n ≥ n + 1`
   with vanishing mixed bound `|M_n| ≤ B_n → 0` yields the two-dimensional Gram margin
   `Q_n(c, d) ≥ (log(n + 1) / (8192 (n + 1))) c^2 + ((n + 1) / 2) d^2`. -/

open MeasureTheory Set Filter Complex
open scoped Topology Convolution BigOperators
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.CHMDDoobGraph
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

theorem weil_diag_norm_le_square_mass (f : ℝ → ℂ)
    (hf : Summable (zetaZeroSquareSummand f)) :
    ‖zetaZeroConfig.W f f‖ ≤ zetaZeroSquareMass f := by
  have h := weil_mixed_norm_le_scaled f f hf hf one_pos
  linarith

/-- Pointwise lower bound on the smoothed compact-ramp Weil diagonal from the tail
diagonal and the corrected/tail zero-square sampling masses. -/
theorem factorialMuntzSmoothedRamp_re_W_ge (n k : ℕ) :
    (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
    zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) -
    2 * Real.sqrt
      (zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) *
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ))) ≤
    (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re := by
  set H : ℝ → ℂ := fun x => (factorialMuntzSmoothed n k x : ℂ)
  set U : ℝ → ℂ := fun x => (factorialMuntzSmoothedTail n k x : ℂ)
  have hH := factorialCorrected_zeroSquare_summable n k
  have hU := factorialSmoothedTail_zeroSquare_summable n k
  have hHH : -zetaZeroSquareMass H ≤ (zetaZeroConfig.W H H).re := by
    have h1 := (Complex.abs_re_le_norm (zetaZeroConfig.W H H)).trans
      (weil_diag_norm_le_square_mass H hH)
    linarith [(abs_le.mp h1).1]
  have hHU : (zetaZeroConfig.W H U).re ≤
      Real.sqrt (zetaZeroSquareMass H * zetaZeroSquareMass U) :=
    (Complex.re_le_norm _).trans (weil_mixed_norm_le_sqrt_square_mass H U hH hU)
  have hUH : (zetaZeroConfig.W U H).re ≤
      Real.sqrt (zetaZeroSquareMass H * zetaZeroSquareMass U) := by
    have h1 := (Complex.re_le_norm _).trans (weil_mixed_norm_le_sqrt_square_mass U H hU hH)
    rwa [mul_comm (zetaZeroSquareMass U) (zetaZeroSquareMass H)] at h1
  rw [factorialMuntzSmoothedRamp_re_W_eq n k]
  linarith

/-- Uniform zero-square sampling upper bound for the smoothed compact ramp across all
arithmetic scales `n` and smoothing indices `k`. -/
theorem exists_factorialMuntzSmoothedRamp_zeroSquare_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ,
      zetaZeroSquareMass (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ≤
        C * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) := by
  obtain ⟨CU, hCU_pos, hCU⟩ := exists_factorialTail_raw_and_smoothed_zeroSquare_bound
  let CH := factorialCorrectedSamplingConstant
  have hCH_pos : 0 < CH := factorialCorrectedSamplingConstant_pos
  refine ⟨2 * (CH + CU), by positivity, fun n k => ?_⟩
  have hle := factorialMuntzSmoothedRamp_zeroSquare_le n k
  have hH := factorialCorrected_zeroSquare_le n k
  have hraw : 0 ≤ zetaZeroSquareMass (fun x => (factorialMuntzCorrectedTail n x : ℂ)) :=
    tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hU : zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ≤
      CU * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) :=
    (le_add_of_nonneg_left hraw).trans (hCU n k)
  have hlog_nonneg : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by linarith [ Nat.cast_nonneg (α := ℝ) n ])
  have hH' : zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) ≤
      CH * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) := by
    have h1 : CH / ((n + 1 : ℕ) : ℝ) ≤ CH * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) := by
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    exact hH.trans h1
  calc
    zetaZeroSquareMass (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ≤
        2 * (CH * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ)) +
          2 * (CU * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ)) := by
      linarith
    _ = 2 * (CH + CU) * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) := by ring

/-- Uniform upper bound on the smoothed compact-ramp Weil diagonal norm across all `n, k`. -/
theorem exists_factorialMuntzSmoothedRamp_weil_norm_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ,
      ‖zetaZeroConfig.W
        (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
        (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))‖ ≤
        C * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) := by
  obtain ⟨C, hC_pos, hC⟩ := exists_factorialMuntzSmoothedRamp_zeroSquare_bound
  refine ⟨C, hC_pos, fun n k => ?_⟩
  exact (weil_diag_norm_le_square_mass _
    (factorialMuntzSmoothedRamp_zeroSquare_summable n k)).trans (hC n k)

/-- **Eventual Logarithmic Lower Bound for the Smoothed Compact Ramp (`APT-ROOT-RAMP-MARGIN`).**
Eventually in the arithmetic scale `n` and then eventually in the smoothing index `k`,
the smoothed compact ramp has strictly positive Weil diagonal of order `log(n + 1) / (n + 1)`. -/
theorem factorialMuntzSmoothedRamp_weil_log_lower :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
      Real.log ((n + 1 : ℕ) : ℝ) / (4096 * ((n + 1 : ℕ) : ℝ)) ≤
        (zetaZeroConfig.W
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re := by
  obtain ⟨CU, hCU_pos, hCU⟩ := exists_factorialTail_raw_and_smoothed_zeroSquare_bound
  let CH := factorialCorrectedSamplingConstant
  have hCH_pos : 0 < CH := factorialCorrectedSamplingConstant_pos
  have ht : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  let M : ℝ := max 1 (max (8192 * CH) (8 * 8192 ^ 2 * CH * CU))
  filter_upwards [factorialMuntzSmoothedTail_weil_log_rate,
    ht.eventually (eventually_ge_atTop M)] with n hn hlogM
  filter_upwards [hn] with k hk
  set N : ℝ := ((n + 1 : ℕ) : ℝ)
  set L : ℝ := Real.log N
  have hN_pos : 0 < N := by positivity
  have hL_ge_one : 1 ≤ L := le_trans (le_max_left _ _) hlogM
  have hL_ge_CH : 8192 * CH ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogM
  have hL_ge_prod : 8 * 8192 ^ 2 * CH * CU ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlogM
  have hH_le : zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) ≤ CH / N :=
    factorialCorrected_zeroSquare_le n k
  have hraw : 0 ≤ zetaZeroSquareMass (fun x => (factorialMuntzCorrectedTail n x : ℂ)) :=
    tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hU_le : zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ≤
      CU * (1 + L) / N := by
    have h1 := (le_add_of_nonneg_left hraw).trans (hCU n k)
    simpa [N, L] using h1
  have hprod_le :
      zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) *
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ≤
        (L / (16384 * N)) ^ 2 := by
    have h1 :
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) *
          zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ≤
          (CH / N) * (CU * (1 + L) / N) :=
      mul_le_mul hH_le hU_le
        (tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (by positivity)
    have h2 : (CH / N) * (CU * (1 + L) / N) ≤ (L / (16384 * N)) ^ 2 := by
      have h1L : 1 + L ≤ 2 * L := by linarith
      have hCHCU : 0 ≤ CH * CU := mul_nonneg hCH_pos.le hCU_pos.le
      have hnum : CH * (CU * (1 + L)) ≤ L ^ 2 / 16384 ^ 2 := by
        have h3 : CH * (CU * (1 + L)) ≤ CH * CU * (2 * L) := by
          have := mul_le_mul_of_nonneg_left h1L hCHCU
          linarith
        have h4 : CH * CU * (2 * L) ≤ L ^ 2 / 16384 ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        exact h3.trans h4
      calc
        (CH / N) * (CU * (1 + L) / N) = (CH * (CU * (1 + L))) / N ^ 2 := by ring
        _ ≤ (L ^ 2 / 16384 ^ 2) / N ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
        _ = (L / (16384 * N)) ^ 2 := by ring
    exact h1.trans h2
  have hsqrt_le :
      2 * Real.sqrt
        (zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) *
          zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ))) ≤
        L / (8192 * N) := by
    have h1 := Real.sqrt_le_sqrt hprod_le
    rw [Real.sqrt_sq (by positivity)] at h1
    have h2 : 2 * (L / (16384 * N)) = L / (8192 * N) := by ring
    linarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)]
  have hCH_div : CH / N ≤ L / (8192 * N) := by
    rw [div_le_div_iff₀ hN_pos (by positivity)]
    nlinarith
  have hlo := factorialMuntzSmoothedRamp_re_W_ge n k
  have hsplit : L / (2048 * N) - L / (8192 * N) - L / (8192 * N) = L / (4096 * N) := by ring
  linarith [hH_le.trans hCH_div]

/-- **Relative Positive Margin for the Smoothed Compact Ramp.**
There is an absolute constant `δ > 0` such that eventually in `n` and then eventually in `k`,
the smoothed compact-ramp Weil energy dominates `δ` times its zero-square sampling mass. -/
theorem exists_factorialMuntzSmoothedRamp_relative_positive_margin :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
      δ * zetaZeroSquareMass (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ≤
        (zetaZeroConfig.W
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re := by
  obtain ⟨C, hC_pos, hC⟩ := exists_factorialMuntzSmoothedRamp_zeroSquare_bound
  let δ : ℝ := 1 / (8192 * C)
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, ?_⟩
  have ht : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  filter_upwards [factorialMuntzSmoothedRamp_weil_log_lower,
    ht.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hlog
  filter_upwards [hn] with k hk
  have hZ := hC n k
  have hL : 1 ≤ Real.log (n + 1 : ℝ) := by exact_mod_cast hlog
  have hscale : δ * (C * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ)) ≤
      Real.log ((n + 1 : ℕ) : ℝ) / (4096 * ((n + 1 : ℕ) : ℝ)) := by
    calc
      δ * (C * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ)) =
          (1 + Real.log (n + 1 : ℝ)) / (8192 * (n + 1 : ℝ)) := by
        dsimp [δ]
        field_simp
      _ ≤ (2 * Real.log (n + 1 : ℝ)) / (8192 * (n + 1 : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = Real.log ((n + 1 : ℕ) : ℝ) / (4096 * ((n + 1 : ℕ) : ℝ)) := by
        have hN : (n : ℝ) + 1 ≠ 0 := by positivity
        push_cast
        field_simp
        ring
  exact ((mul_le_mul_of_nonneg_left hZ hδ.le).trans hscale).trans hk

/-- **Translation-Increment $L^2$ Contraction under Smoothing (`APT-ROOT-RAMP-LIMIT`).**
For every arithmetic scale `n`, smoothing index `k`, and shift `t`, convolving the
compact factorial ramp with the normalized nonnegative mollifier contracts its
squared translation $L^2$ increment. -/
theorem factorialRamp_smooth_difference_L2_le (n k : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x : ℝ, |sourceFactorialRamp (n + 1) x| ≤ M) (t : ℝ) :
    (∫ x : ℝ,
      (CHMDDoobGraph.smooth (sourceFactorialRamp (n + 1)) k x -
        CHMDDoobGraph.smooth (sourceFactorialRamp (n + 1)) k (x + t)) ^ 2) ≤
    ∫ x : ℝ, (sourceFactorialRamp (n + 1) x - sourceFactorialRamp (n + 1) (x + t)) ^ 2 :=
  smooth_difference_L2_le
    (continuous_sourceFactorialRamp (n + 1)).measurable
    (hasCompactSupport_sourceFactorialRamp (N := n + 1) (by omega))
    hM hb k t

/-- **Smoothing-Limit Transfer Theorem (`APT-ROOT-RAMP-LIMIT` → `APT-ROOT-RAMP-MARGIN`).**
For any sequence `A : ℕ → ℝ` of unsmoothed compact-ramp Weil energies obtained as the
`k → ∞` limit of the smoothed ramp energies `Re W(r_{n,k}, r_{n,k})`, both the eventual
`log(n + 1) / (4096 (n + 1))` lower bound and the `(1 + log(n + 1)) / (n + 1)` upper bound
transfer unconditionally to `A n`. -/
theorem factorialRamp_weil_limit_bounds_of_tendsto (A : ℕ → ℝ)
    (hlim : ∀ n : ℕ, Tendsto
      (fun k : ℕ => (zetaZeroConfig.W
        (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
        (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re)
      atTop (𝓝 (A n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Real.log ((n + 1 : ℕ) : ℝ) / (4096 * ((n + 1 : ℕ) : ℝ)) ≤ A n ∧
      A n ≤ C * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) := by
  obtain ⟨C, hC_pos, hC⟩ := exists_factorialMuntzSmoothedRamp_weil_norm_upper
  refine ⟨C, hC_pos, ?_⟩
  filter_upwards [factorialMuntzSmoothedRamp_weil_log_lower] with n hn
  refine ⟨ge_of_tendsto (hlim n) hn, ?_⟩
  apply le_of_tendsto (hlim n)
  exact Eventually.of_forall fun k =>
    (Complex.re_le_norm _).trans (hC n k)

/-- Two-dimensional quadratic Gram form `Q(c, d) = A c^2 + M c d + D d^2` on the
ramp–tent coefficient plane. -/
def binaryGramForm (A M D c d : ℝ) : ℝ :=
  A * c ^ 2 + M * c * d + D * d ^ 2

/-- The Schur Gram coupling error `B^2 / (2 N)` for a tent block of scale at least `N`
and mixed pairing bounded by `B`. -/
def binaryGramError (N B : ℝ) : ℝ :=
  B ^ 2 / (2 * N)

/-- The optimal tent-corrected ramp energy `Q(1, -M / (2 D)) = A - M^2 / (4 D)`. -/
def binaryGramMinRamp (A M D : ℝ) : ℝ :=
  binaryGramForm A M D 1 (-M / (2 * D))

/-- Exact completion of the square for the two-dimensional ramp–tent Gram form. -/
theorem binaryGramForm_complete_square (A M D c d : ℝ) (hD : D ≠ 0) :
    binaryGramForm A M D c d =
      D * (d + c * M / (2 * D)) ^ 2 + c ^ 2 * binaryGramMinRamp A M D := by
  unfold binaryGramMinRamp
  unfold binaryGramForm
  field_simp [hD]
  ring

/-- Uniform diagonal decoupling lower bound for the two-dimensional Gram form whenever
`D ≥ N > 0` and `|M| ≤ B`. -/
theorem binaryGramForm_lower_of_scale (A : ℝ) {M D N B : ℝ}
    (hN : 0 < N) (hD : N ≤ D) (hM : |M| ≤ B) (c d : ℝ) :
    c ^ 2 * (A - binaryGramError N B) + (D / 2) * d ^ 2 ≤
      binaryGramForm A M D c d := by
  have hB0 : 0 ≤ B := (abs_nonneg M).trans hM
  have hMsq : M ^ 2 ≤ B ^ 2 := by
    have h1 := mul_nonneg (sub_nonneg.mpr hM) (add_nonneg hB0 (abs_nonneg M))
    nlinarith [sq_abs M]
  have hs := sq_nonneg (N * d + c * M)
  have he := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hMsq)
  have hd := mul_nonneg (mul_nonneg hN.le (sub_nonneg.mpr hD)) (sq_nonneg d)
  unfold binaryGramForm binaryGramError
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 2 * N by positivity)).1
  field_simp [hN.ne']
  nlinarith

/-- **Complete Two-Dimensional Ramp–Tent Gram Coercivity (`APT-ROOT-RAMP-MARGIN`).**
Whenever the pure-ramp diagonal `A_n` is obtained as the smoothing limit of
`Re W(r_{n,k}, r_{n,k})`, the tent diagonal satisfies `D_n ≥ n + 1` eventually, and the
mixed pairing satisfies `|M_n| ≤ B_n` with `B_n → 0`, the two-dimensional form satisfies
`Q_n(c, d) ≥ (log(n + 1) / (8192 (n + 1))) c^2 + ((n + 1) / 2) d^2` eventually in `n`
for all `c, d ∈ ℝ`, and the Schur-minimized ramp energy satisfies
`binaryGramMinRamp (A n) (M n) (D n) ≥ log(n + 1) / (8192 (n + 1))`. -/
theorem factorialRampTent_gram_margin_of_tendsto (A M D B : ℕ → ℝ)
    (hlim : ∀ n : ℕ, Tendsto
      (fun k : ℕ => (zetaZeroConfig.W
        (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
        (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re)
      atTop (𝓝 (A n)))
    (hD : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) ≤ D n)
    (hM : ∀ n : ℕ, |M n| ≤ B n)
    (hB : Tendsto B atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (∀ c d : ℝ,
        Real.log ((n + 1 : ℕ) : ℝ) / (8192 * ((n + 1 : ℕ) : ℝ)) * c ^ 2 +
          (((n + 1 : ℕ) : ℝ) / 2) * d ^ 2 ≤
          binaryGramForm (A n) (M n) (D n) c d) ∧
      Real.log ((n + 1 : ℕ) : ℝ) / (8192 * ((n + 1 : ℕ) : ℝ)) ≤
        binaryGramMinRamp (A n) (M n) (D n) := by
  obtain ⟨_, _, hA⟩ := factorialRamp_weil_limit_bounds_of_tendsto A hlim
  have ht : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hB1 : ∀ᶠ n : ℕ in atTop, |B n| < 1 := by
    have h := (Metric.tendsto_nhds.mp hB) 1 zero_lt_one
    filter_upwards [h] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [hA, hD, hB1, ht.eventually (eventually_ge_atTop (4096 : ℝ))] with
    n hAn hDn hBn hlog
  set N : ℝ := ((n + 1 : ℕ) : ℝ)
  set L : ℝ := Real.log N
  have hN : 0 < N := by positivity
  have hB_sq : (B n) ^ 2 ≤ 1 := by
    have habs : |B n| ≤ 1 := le_of_lt hBn
    nlinarith [sq_abs (B n), abs_nonneg (B n)]
  have herr : binaryGramError N (B n) ≤ L / (8192 * N) := by
    unfold binaryGramError
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hAn.1]
  have hmargin : L / (8192 * N) ≤ A n - binaryGramError N (B n) := by
    have hsplit : L / (4096 * N) - L / (8192 * N) = L / (8192 * N) := by ring
    linarith [hAn.1]
  refine ⟨fun c d => ?_, ?_⟩
  · have hlo := binaryGramForm_lower_of_scale (A n) hN hDn (hM n) c d
    have hc : L / (8192 * N) * c ^ 2 ≤ c ^ 2 * (A n - binaryGramError N (B n)) := by
      nlinarith [sq_nonneg c]
    have hd : (N / 2) * d ^ 2 ≤ (D n / 2) * d ^ 2 := by
      nlinarith [sq_nonneg d]
    linarith
  · have hlo := binaryGramForm_lower_of_scale (A n) hN hDn (hM n) 1 (-M n / (2 * D n))
    have hd0 : 0 ≤ (D n / 2) * (-M n / (2 * D n)) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    unfold binaryGramMinRamp
    linarith

end

end GaloisForLFunctions.ArithmeticPositivityTheory
