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

/-! ## Multi-Scale Rank-1 Corrected-Source Factorization & Uniform Eventual Positivity -/

/-- Exact evaluation of the canonical boundary coefficient at scale `n = 0`: `c(0) = 1 / 2`. -/
theorem factorialMuntzBoundaryCoefficient_zero :
    factorialMuntzBoundaryCoefficient 0 = 1 / 2 := by
  unfold factorialMuntzBoundaryCoefficient
  norm_num

/-- **Multi-Scale Rank-1 Zero Readout Proportional to `H_{0,k}`:**
At every nontrivial zeta zero `ρ`, the Mellin–Fourier readout of any finite combination
`H_{S,a,k} = ∑_{n ∈ S} a_n H_{n,k}` is exactly `2 Λ_pole(S, a)` times the readout of the
base-scale corrected source `H_{0,k}`. -/
theorem paperFT_factorialSmoothedCombo_eq_two_mul_pole_mul_zero
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    paperFT (factorialSmoothedCombo S a k) (gammaOf ρ) =
      2 * factorialPoleFunctional S a *
        paperFT (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) (gammaOf ρ) := by
  rw [paperFT_factorialSmoothedCombo_gamma, factorialMuntzSmoothed_paperFT_gamma,
    factorialMuntzBoundaryCoefficient_zero]
  push_cast
  ring

/-- **Pointwise Multi-Scale Zero-Square Summand Factorization:**
For every nontrivial zero `ρ`, the square-sampling summand of `H_{S,a,k}` is
`4 ‖Λ_pole(S, a)‖^2` times the square-sampling summand of `H_{0,k}`. -/
theorem zetaZeroSquareSummand_factorialSmoothedCombo
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroSquareSummand (factorialSmoothedCombo S a k) ρ =
      4 * ‖factorialPoleFunctional S a‖ ^ 2 *
        zetaZeroSquareSummand (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) ρ := by
  unfold zetaZeroSquareSummand
  rw [paperFT_factorialSmoothedCombo_eq_two_mul_pole_mul_zero, norm_mul, norm_mul,
    Complex.norm_ofNat]
  ring

/-- **Absolute Zero-Square Summability of Arbitrary Multi-Scale Corrected Combinations:**
Every finite combination `H_{S,a,k}` has an absolutely summable zero-square series. -/
theorem factorialSmoothedCombo_zeroSquare_summable
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) :
    Summable (zetaZeroSquareSummand (factorialSmoothedCombo S a k)) := by
  have h := (factorialCorrected_zeroSquare_summable 0 k).mul_left
    (4 * ‖factorialPoleFunctional S a‖ ^ 2)
  refine h.congr fun ρ => ?_
  exact (zetaZeroSquareSummand_factorialSmoothedCombo S a k ρ).symm

/-- **Exact Multi-Scale Rank-1 Zero-Square Mass Identity:**
The total zero-square sampling mass of `H_{S,a,k}` factors identically as
`4 ‖Λ_pole(S, a)‖^2` times the base-scale mass `Z(H_{0,k})`. -/
theorem zetaZeroSquareMass_factorialSmoothedCombo_eq
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) :
    zetaZeroSquareMass (factorialSmoothedCombo S a k) =
      4 * ‖factorialPoleFunctional S a‖ ^ 2 *
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) := by
  unfold zetaZeroSquareMass
  simp_rw [zetaZeroSquareSummand_factorialSmoothedCombo]
  exact tsum_mul_left

/-- **Rank-1 Multi-Scale Zero-Square Mass Bound (No `|S|` Cauchy–Schwarz Penalty):**
For every finite scale set `S`, coefficient vector `a`, and smoothing index `k`,
`Z(H_{S,a,k}) ≤ 4 C_H ‖Λ_pole(S, a)‖^2`. -/
theorem zetaZeroSquareMass_factorialSmoothedCombo_le
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) :
    zetaZeroSquareMass (factorialSmoothedCombo S a k) ≤
      4 * factorialCorrectedSamplingConstant * ‖factorialPoleFunctional S a‖ ^ 2 := by
  rw [zetaZeroSquareMass_factorialSmoothedCombo_eq]
  have h0 := factorialCorrected_zeroSquare_le 0 k
  simp only [Nat.zero_add, Nat.cast_one, div_one] at h0
  calc
    4 * ‖factorialPoleFunctional S a‖ ^ 2 *
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) ≤
      4 * ‖factorialPoleFunctional S a‖ ^ 2 * factorialCorrectedSamplingConstant :=
        mul_le_mul_of_nonneg_left h0 (by positivity)
    _ = 4 * factorialCorrectedSamplingConstant * ‖factorialPoleFunctional S a‖ ^ 2 := by ring

/-- **Pointwise Multi-Scale Weil Zero-Side Summand Factorization:**
For every nontrivial zero `ρ`, the bilinear Weil zero-side summand of `H_{S,a,k}` equals
`4 ‖Λ_pole(S, a)‖^2` times the Weil zero-side summand of `H_{0,k}`. -/
theorem weil_Wsummand_factorialSmoothedCombo_eq
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (factorialSmoothedCombo S a k) (factorialSmoothedCombo S a k) ρ =
      ((4 * ‖factorialPoleFunctional S a‖ ^ 2 : ℝ) : ℂ) *
        zetaZeroConfig.Wsummand
          (fun x => (factorialMuntzSmoothed 0 k x : ℂ))
          (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) ρ := by
  let σ : zetaZeroConfig.carrier := ⟨reflect ρ, zetaZeroConfig.reflect_mem _ ρ.2⟩
  have hγ : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (σ : ℂ) :=
    (Tail.gammaOf_reflect _).symm
  unfold ZeroConfig.Wsummand
  rw [hγ,
    paperFT_factorialSmoothedCombo_eq_two_mul_pole_mul_zero S a k ρ,
    paperFT_factorialSmoothedCombo_eq_two_mul_pole_mul_zero S a k σ,
    map_mul, map_mul, map_ofNat]
  have hnorm : factorialPoleFunctional S a * (starRingEnd ℂ) (factorialPoleFunctional S a) =
      ((‖factorialPoleFunctional S a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc
    (zetaZeroConfig.mult ρ : ℂ) *
        (2 * factorialPoleFunctional S a *
          paperFT (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) (gammaOf ρ)) *
        (2 * (starRingEnd ℂ) (factorialPoleFunctional S a) *
          (starRingEnd ℂ)
            (paperFT (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) (gammaOf σ))) =
      4 * (factorialPoleFunctional S a * (starRingEnd ℂ) (factorialPoleFunctional S a)) *
        ((zetaZeroConfig.mult ρ : ℂ) *
          paperFT (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) (gammaOf ρ) *
          (starRingEnd ℂ)
            (paperFT (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) (gammaOf σ))) := by ring
    _ = ((4 * ‖factorialPoleFunctional S a‖ ^ 2 : ℝ) : ℂ) *
        ((zetaZeroConfig.mult ρ : ℂ) *
          paperFT (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) (gammaOf ρ) *
          (starRingEnd ℂ)
            (paperFT (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) (gammaOf σ))) := by
      rw [hnorm]
      push_cast
      ring

/-- **Exact Multi-Scale Rank-1 Weil Zero-Side Factorization:**
For every finite scale set `S`, complex coefficient vector `a`, and smoothing index `k`,
`W(H_{S,a,k}, H_{S,a,k}) = 4 ‖Λ_pole(S, a)‖^2 W(H_{0,k}, H_{0,k})`. -/
theorem weil_factorialSmoothedCombo_eq
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) :
    zetaZeroConfig.W (factorialSmoothedCombo S a k) (factorialSmoothedCombo S a k) =
      ((4 * ‖factorialPoleFunctional S a‖ ^ 2 : ℝ) : ℂ) *
        zetaZeroConfig.W
          (fun x => (factorialMuntzSmoothed 0 k x : ℂ))
          (fun x => (factorialMuntzSmoothed 0 k x : ℂ)) := by
  unfold ZeroConfig.W
  simp_rw [weil_Wsummand_factorialSmoothedCombo_eq]
  exact tsum_mul_left

/-- **Real-Part Multi-Scale Rank-1 Weil Factorization:** -/
theorem re_weil_factorialSmoothedCombo_eq
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) :
    (zetaZeroConfig.W (factorialSmoothedCombo S a k) (factorialSmoothedCombo S a k)).re =
      4 * ‖factorialPoleFunctional S a‖ ^ 2 *
        (zetaZeroConfig.W
          (fun x => (factorialMuntzSmoothed 0 k x : ℂ))
          (fun x => (factorialMuntzSmoothed 0 k x : ℂ))).re := by
  rw [weil_factorialSmoothedCombo_eq, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- **Uniform Eventual Multi-Scale Corrected-Source Weil Positivity (Single Threshold `k₀`):**
There is a single smoothing threshold in `k` (independent of both the finite scale set `S`
and the complex coefficient vector `a`) above which every multi-scale corrected-source
combination `H_{S,a,k}` has nonnegative Weil zero-side energy, with strict positivity if and
only if it lies outside the pole-free hyperplane `Λ_pole(S, a) = 0`. -/
theorem eventually_re_weil_factorialSmoothedCombo_nonneg_and_pos_iff :
    ∀ᶠ k : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℂ),
      0 ≤ (zetaZeroConfig.W (factorialSmoothedCombo S a k) (factorialSmoothedCombo S a k)).re ∧
      (0 < (zetaZeroConfig.W (factorialSmoothedCombo S a k) (factorialSmoothedCombo S a k)).re ↔
        factorialPoleFunctional S a ≠ 0) := by
  filter_upwards [factorialMuntzSmoothed_weil_difference_eventually_pos 0] with k hk S a
  have h0_pos : 0 < (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothed 0 k x : ℂ))
      (fun x => (factorialMuntzSmoothed 0 k x : ℂ))).re := by
    have hid := factorialMuntzSmoothed_weil_identity 0 k
    linarith
  rw [re_weil_factorialSmoothedCombo_eq]
  refine ⟨mul_nonneg (by positivity) h0_pos.le, ?_⟩
  rw [mul_pos_iff_of_pos_right h0_pos]
  constructor
  · intro hp hzero
    simp [hzero] at hp
  · intro hne
    have hnorm : 0 < ‖factorialPoleFunctional S a‖ := norm_pos_iff.mpr hne
    positivity

/-- At every nontrivial zero `ρ`, the readout of `R_{S,a,k}` is the difference between the
readout of `H_{S,a,k}` and the readout of `U_{S,a,k}`. -/
theorem paperFT_factorialSmoothedRampCombo_gamma_eq_sub
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    paperFT (factorialSmoothedRampCombo S a k) (gammaOf ρ) =
      paperFT (factorialSmoothedCombo S a k) (gammaOf ρ) -
        paperFT (factorialSmoothedTailCombo S a k) (gammaOf ρ) := by
  have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
  rw [paperFT_factorialSmoothedRampCombo_gamma,
    paperFT_factorialSmoothedTailCombo_gamma S a k (s := (ρ : ℂ)) (by linarith [hρ.1]),
    paperFT_factorialSmoothedCombo_gamma,
    ← sum_factorialMuntzSmoothed_paperFT_gamma_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [factorialMuntzSmoothedRamp_paperFT_eq_sub n k (s := (ρ : ℂ)) (by linarith [hρ.1]), mul_sub]

/-- Pointwise sesquilinear expansion of the Weil summand of `R_{S,a,k}` at every nontrivial zero `ρ`. -/
theorem factorialSmoothedRampCombo_Wsummand_eq
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand
      (factorialSmoothedRampCombo S a k) (factorialSmoothedRampCombo S a k) ρ =
    zetaZeroConfig.Wsummand
      (factorialSmoothedCombo S a k) (factorialSmoothedCombo S a k) ρ +
    zetaZeroConfig.Wsummand
      (factorialSmoothedTailCombo S a k) (factorialSmoothedTailCombo S a k) ρ -
    zetaZeroConfig.Wsummand
      (factorialSmoothedCombo S a k) (factorialSmoothedTailCombo S a k) ρ -
    zetaZeroConfig.Wsummand
      (factorialSmoothedTailCombo S a k) (factorialSmoothedCombo S a k) ρ := by
  let σ : zetaZeroConfig.carrier := ⟨reflect ρ, zetaZeroConfig.reflect_mem _ ρ.2⟩
  have hγ : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (σ : ℂ) :=
    (Tail.gammaOf_reflect _).symm
  unfold ZeroConfig.Wsummand
  rw [hγ,
    paperFT_factorialSmoothedRampCombo_gamma_eq_sub S a k ρ,
    paperFT_factorialSmoothedRampCombo_gamma_eq_sub S a k σ,
    map_sub]
  ring

/-- Exact zero-side sesquilinear expansion of `Re W(R_{S,a,k}, R_{S,a,k})`. -/
theorem factorialSmoothedRampCombo_re_W_eq
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ)
    (hU : Summable (zetaZeroSquareSummand (factorialSmoothedTailCombo S a k))) :
    (zetaZeroConfig.W (factorialSmoothedRampCombo S a k)
      (factorialSmoothedRampCombo S a k)).re =
    (zetaZeroConfig.W (factorialSmoothedCombo S a k)
      (factorialSmoothedCombo S a k)).re +
    (zetaZeroConfig.W (factorialSmoothedTailCombo S a k)
      (factorialSmoothedTailCombo S a k)).re -
    (zetaZeroConfig.W (factorialSmoothedCombo S a k)
      (factorialSmoothedTailCombo S a k)).re -
    (zetaZeroConfig.W (factorialSmoothedTailCombo S a k)
      (factorialSmoothedCombo S a k)).re := by
  set H := factorialSmoothedCombo S a k
  set U := factorialSmoothedTailCombo S a k
  have hH := factorialSmoothedCombo_zeroSquare_summable S a k
  have hHH := summable_Wsummand H H hH hH
  have hUU := summable_Wsummand U U hU hU
  have hHU := summable_Wsummand H U hH hU
  have hUH := summable_Wsummand U H hU hH
  have hW : zetaZeroConfig.W (factorialSmoothedRampCombo S a k)
      (factorialSmoothedRampCombo S a k) =
      zetaZeroConfig.W H H + zetaZeroConfig.W U U -
        zetaZeroConfig.W H U - zetaZeroConfig.W U H := by
    unfold ZeroConfig.W
    simp_rw [factorialSmoothedRampCombo_Wsummand_eq S a k]
    rw [((hHH.add hUU).sub hHU).tsum_sub hUH, (hHH.add hUU).tsum_sub hHU, hHH.tsum_add hUU]
  rw [hW]
  simp only [Complex.sub_re, Complex.add_re]

/-- **Multi-Scale Smoothed Compact-Ramp vs. Tail Weil Lower Bound (Uniform in `(S, a)`):**
Once `k` is above the single base-scale smoothing threshold, the diagonal corrected-source
term `Re W(H_{S,a,k}, H_{S,a,k})` is nonnegative for every `(S, a)`, so the smoothed
compact-ramp combination `R_{S,a,k} = H_{S,a,k} - U_{S,a,k}` satisfies
`Re W(R_{S,a,k}, R_{S,a,k}) ≥ Re W(U_{S,a,k}, U_{S,a,k}) - 4 ‖Λ_pole(S, a)‖ √(C_H Z(U_{S,a,k}))`
with zero `|S|` Cauchy–Schwarz overhead and exact equality on the pole-free hyperplane. -/
theorem eventually_re_weil_factorialSmoothedRampCombo_ge_tailCombo_sub_rankOne :
    ∀ᶠ k : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℂ),
      Summable (zetaZeroSquareSummand (factorialSmoothedTailCombo S a k)) →
      (zetaZeroConfig.W (factorialSmoothedTailCombo S a k)
        (factorialSmoothedTailCombo S a k)).re -
      4 * ‖factorialPoleFunctional S a‖ *
        Real.sqrt (factorialCorrectedSamplingConstant *
          zetaZeroSquareMass (factorialSmoothedTailCombo S a k)) ≤
      (zetaZeroConfig.W (factorialSmoothedRampCombo S a k)
        (factorialSmoothedRampCombo S a k)).re := by
  filter_upwards [eventually_re_weil_factorialSmoothedCombo_nonneg_and_pos_iff] with k hk S a hU
  set H := factorialSmoothedCombo S a k
  set U := factorialSmoothedTailCombo S a k
  set R := factorialSmoothedRampCombo S a k
  have hH : Summable (zetaZeroSquareSummand H) :=
    factorialSmoothedCombo_zeroSquare_summable S a k
  have hdecomp := factorialSmoothedRampCombo_re_W_eq S a k hU
  have hHH_nonneg : 0 ≤ (zetaZeroConfig.W H H).re := (hk S a).1
  have hZU_nonneg : 0 ≤ zetaZeroSquareMass U :=
    tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hZH_le : zetaZeroSquareMass H ≤
      4 * factorialCorrectedSamplingConstant * ‖factorialPoleFunctional S a‖ ^ 2 :=
    zetaZeroSquareMass_factorialSmoothedCombo_le S a k
  have hprod_sqrt :
      Real.sqrt (zetaZeroSquareMass H * zetaZeroSquareMass U) ≤
        2 * ‖factorialPoleFunctional S a‖ *
          Real.sqrt (factorialCorrectedSamplingConstant * zetaZeroSquareMass U) := by
    have h1 : zetaZeroSquareMass H * zetaZeroSquareMass U ≤
        (2 * ‖factorialPoleFunctional S a‖) ^ 2 *
          (factorialCorrectedSamplingConstant * zetaZeroSquareMass U) := by
      calc
        zetaZeroSquareMass H * zetaZeroSquareMass U ≤
            (4 * factorialCorrectedSamplingConstant * ‖factorialPoleFunctional S a‖ ^ 2) *
              zetaZeroSquareMass U :=
          mul_le_mul_of_nonneg_right hZH_le hZU_nonneg
        _ = (2 * ‖factorialPoleFunctional S a‖) ^ 2 *
            (factorialCorrectedSamplingConstant * zetaZeroSquareMass U) := by ring
    calc
      Real.sqrt (zetaZeroSquareMass H * zetaZeroSquareMass U) ≤
          Real.sqrt ((2 * ‖factorialPoleFunctional S a‖) ^ 2 *
            (factorialCorrectedSamplingConstant * zetaZeroSquareMass U)) :=
        Real.sqrt_le_sqrt h1
      _ = 2 * ‖factorialPoleFunctional S a‖ *
          Real.sqrt (factorialCorrectedSamplingConstant * zetaZeroSquareMass U) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hHU : (zetaZeroConfig.W H U).re ≤
      2 * ‖factorialPoleFunctional S a‖ *
        Real.sqrt (factorialCorrectedSamplingConstant * zetaZeroSquareMass U) :=
    ((Complex.re_le_norm _).trans (weil_mixed_norm_le_sqrt_square_mass H U hH hU)).trans hprod_sqrt
  have hUH : (zetaZeroConfig.W U H).re ≤
      2 * ‖factorialPoleFunctional S a‖ *
        Real.sqrt (factorialCorrectedSamplingConstant * zetaZeroSquareMass U) := by
    have h1 := (Complex.re_le_norm _).trans (weil_mixed_norm_le_sqrt_square_mass U H hU hH)
    rw [mul_comm (zetaZeroSquareMass U) (zetaZeroSquareMass H)] at h1
    exact h1.trans hprod_sqrt
  linarith

end

end GaloisForLFunctions.ArithmeticPositivityTheory
