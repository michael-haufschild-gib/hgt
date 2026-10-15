import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.RHTower.Sieve.ChebyshevPNT

/-!
# Far-out nonnegative half-line tests have positive odd Markov form

Let `f ≥ 0` be a real `C²` test supported in `[x₀ − 1, x₀ + 1]` and bounded below by `h > 0` there.
By the odd-sector decomposition,
`M(f − f̃) = 2[M(f) + Σ_k f̃(−2k)² + Π(f)]`, with
* `M(f) = A(f) − P(f)` where the archimedean form satisfies `A(f) ≥ 2θ′(0)‖f‖²` (Lévy form) and the
  ratio prime sum `P(f)` only involves lags `log n ≤ 2`, i.e. `n ≤ 7`, so `P(f) ≤ C_R ‖f‖²`;
* the trivial-zero squares are nonnegative;
* the product pairing `Π(f) = Σ_n Λ(n) n^{−1/2} (f⋆f)(log n)` is at least
  `h² e^{−(x₀+1/4)} Σ_{e^{2x₀−1/2} < n ≤ e^{2x₀+1/2}} Λ(n)`, since `(f⋆f)(y) ≥ h²` for
  `|y − 2x₀| ≤ 1/2`; the prime number theorem in Chebyshev form gives
  `Σ_{X < n ≤ eX} Λ(n) ≥ (e−1)X/2` for large `X`, hence `Π(f) ≥ (e−1)/2 · h² e^{x₀ − 3/4}`.

So the product pairing grows exponentially in the position `x₀` while the archimedean mass and the
ratio pairing are bounded by `‖f‖²`: for every `h > 0` and `B` there is `X₀` such that every such
test with `‖f‖² ≤ B` and `x₀ ≥ X₀` has `M(f − f̃) > 0`. This is unconditional: the mechanism is the
Chebyshev growth of the product-prime pairing, not the location of the zeros. It also shows that the
nonnegative half-line class cannot witness a failure of the Riemann hypothesis through `M` far from
the origin: such witnesses need a vanishing `sinh`-moment.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ} {x₀ h : ℝ}

/-! ## The ratio pairing of a test of support length two -/

/-- The ratio-pairing constant `2 Σ_{n < 8} Λ(n) n^{−1/2}`. -/
def ratioConst : ℝ := 2 * ∑ n ∈ Finset.range 8, vonMangoldtAtom n

theorem vonMangoldtAtom_nonneg' (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

theorem ratioConst_nonneg : 0 ≤ ratioConst := by
  unfold ratioConst
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun n _ => vonMangoldtAtom_nonneg' n)

theorem two_lt_log_eight : (2 : ℝ) < Real.log 8 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1]

/-- The two shifted self-pairings of a support-length-two test vanish for `n ≥ 8`. -/
theorem shifted_pairings_eq_zero (hsupp : ∀ x, x ∉ Icc (x₀ - 1) (x₀ + 1) → f x = 0) {n : ℕ}
    (hn : 8 ≤ n) :
    (∫ t, f t * f (t - Real.log n)) + ∫ t, f t * f (t + Real.log n) = 0 := by
  have hlog : 2 < Real.log n :=
    lt_of_lt_of_le two_lt_log_eight (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have h1 : ∀ t, f t * f (t - Real.log n) = 0 := by
    intro t
    by_cases ht : t ∈ Icc (x₀ - 1) (x₀ + 1)
    · rw [hsupp (t - Real.log n) (by
        intro hm; rw [mem_Icc] at hm ht; linarith [hm.1, ht.1]), mul_zero]
    · rw [hsupp t ht, zero_mul]
  have h2 : ∀ t, f t * f (t + Real.log n) = 0 := by
    intro t
    by_cases ht : t ∈ Icc (x₀ - 1) (x₀ + 1)
    · rw [hsupp (t + Real.log n) (by
        intro hm; rw [mem_Icc] at hm ht; linarith [hm.2, ht.2]), mul_zero]
    · rw [hsupp t ht, zero_mul]
  simp only [h1, h2, integral_zero, add_zero]

/-- A shifted self-pairing is at most the `L²` norm. -/
theorem integral_mul_sub_shift_le (hf : Continuous f) (hfc : HasCompactSupport f) (ℓ : ℝ) :
    ∫ t, f t * f (t - ℓ) ≤ ∫ t, f t ^ 2 := by
  have h1 : Integrable fun t => f t ^ 2 := by
    have h0 : Integrable (fun t => f t * f t) :=
      (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
    simpa [pow_two] using h0
  have h2 : Integrable fun t => f (t - ℓ) ^ 2 := h1.comp_sub_right ℓ
  have h3 : Integrable fun t => f t * f (t - ℓ) := integrable_mul_comp_sub hf hfc f hf ℓ
  have hpt : (fun t => f t * f (t - ℓ)) ≤ fun t => (f t ^ 2 + f (t - ℓ) ^ 2) / 2 := by
    intro t
    have := two_mul_le_add_sq (f t) (f (t - ℓ))
    simp only
    linarith
  calc ∫ t, f t * f (t - ℓ) ≤ ∫ t, (f t ^ 2 + f (t - ℓ) ^ 2) / 2 :=
        integral_mono h3 ((h1.add h2).div_const 2) hpt
    _ = ((∫ t, f t ^ 2) + ∫ t, f (t - ℓ) ^ 2) / 2 := by rw [integral_div, integral_add h1 h2]
    _ = ∫ t, f t ^ 2 := by
        rw [integral_sub_right_eq_self (fun t => f t ^ 2) ℓ]; ring

theorem integral_mul_add_shift_le (hf : Continuous f) (hfc : HasCompactSupport f) (ℓ : ℝ) :
    ∫ t, f t * f (t + ℓ) ≤ ∫ t, f t ^ 2 := by
  have := integral_mul_sub_shift_le hf hfc (-ℓ)
  simpa [sub_neg_eq_add] using this

/-- **The ratio pairing of a support-length-two test is bounded by `C_R ‖f‖²`.** -/
theorem primeSum_le_of_support (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ x, x ∉ Icc (x₀ - 1) (x₀ + 1) → f x = 0) :
    primeSum f ≤ ratioConst * ∫ t, f t ^ 2 := by
  unfold primeSum
  have h0 : ∀ n ∉ Finset.range 8, vonMangoldtAtom n *
      ((∫ t, f t * f (t - Real.log n)) + ∫ t, f t * f (t + Real.log n)) = 0 := by
    intro n hn
    have h8 : 8 ≤ n := by simpa using hn
    rw [shifted_pairings_eq_zero hsupp h8, mul_zero]
  rw [tsum_eq_sum h0]
  calc (∑ n ∈ Finset.range 8, vonMangoldtAtom n *
        ((∫ t, f t * f (t - Real.log n)) + ∫ t, f t * f (t + Real.log n)))
      ≤ ∑ n ∈ Finset.range 8, vonMangoldtAtom n * (2 * ∫ t, f t ^ 2) := by
        refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg' n)
        linarith [integral_mul_sub_shift_le hf.continuous hfc (Real.log n),
          integral_mul_add_shift_le hf.continuous hfc (Real.log n)]
    _ = ratioConst * ∫ t, f t ^ 2 := by
        unfold ratioConst
        rw [← Finset.sum_mul]; ring

/-! ## The archimedean lower bound -/

theorem levyEnergy_nonneg (g : ℝ → ℝ) : 0 ≤ levyEnergy g := by
  unfold levyEnergy
  exact integral_nonneg_of_ae (levyIntegrand_nonneg g)

theorem archForm_ge {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    2 * gammaHardyPhaseRate 0 * ∫ u, g u ^ 2 ≤ archForm g := by
  rw [archForm_eq_levyEnergy hg hgc]
  linarith [levyEnergy_nonneg g]

/-! ## The convolution square of a fat nonnegative test -/

/-- `(f⋆f)(y) ≥ h²` for `|y − 2x₀| ≤ 1/2` when `f ≥ h` on `[x₀ − 1, x₀ + 1]`. -/
theorem sq_le_convSquare (hf : Continuous f) (hfc : HasCompactSupport f) (hpos : ∀ x, 0 ≤ f x)
    (hh : 0 ≤ h) (hlow : ∀ x ∈ Icc (x₀ - 1) (x₀ + 1), h ≤ f x) {y : ℝ}
    (hy : |y - 2 * x₀| ≤ 1 / 2) : h ^ 2 ≤ convSquare f y := by
  unfold convSquare
  have hint : Integrable fun t => f t * f (y - t) :=
    (hf.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hnn : 0 ≤ᵐ[volume] fun t => f t * f (y - t) :=
    Eventually.of_forall fun t => mul_nonneg (hpos t) (hpos _)
  have hset := setIntegral_le_integral (s := Icc (x₀ - 1 / 2) (x₀ + 1 / 2)) hint hnn
  have hab := abs_le.mp hy
  have hlow' : ∀ t ∈ Icc (x₀ - 1 / 2) (x₀ + 1 / 2), h ^ 2 ≤ f t * f (y - t) := by
    intro t ht
    rw [mem_Icc] at ht
    have h1 : h ≤ f t := hlow t ⟨by linarith, by linarith⟩
    have h2 : h ≤ f (y - t) := hlow (y - t) ⟨by linarith, by linarith⟩
    nlinarith [mul_le_mul h1 h2 hh (hpos t)]
  have hvol : volume.real (Icc (x₀ - 1 / 2) (x₀ + 1 / 2)) = 1 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  have hge := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hlow' hint.integrableOn
  rw [hvol, smul_eq_mul, one_mul] at hge
  exact hge.trans hset

/-! ## The prime number theorem window -/

/-- Chebyshev's function `ψ(x) = Σ_{n ≤ x} Λ(n)`. -/
def psiSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)

theorem one_lt_exp_one : (1 : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9; linarith

/-- **A Chebyshev window.** For large `X`, `Σ_{X < n ≤ eX} Λ(n) ≥ (e − 1) X / 2`. -/
theorem exists_psiSum_window : ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ X : ℝ, Y₀ ≤ X →
    (Real.exp 1 - 1) / 2 * X ≤ psiSum (Real.exp 1 * X) - psiSum X := by
  have he := one_lt_exp_one
  set ε : ℝ := (Real.exp 1 - 1) / (2 * (Real.exp 1 + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp Sieve.tendsto_sum_vonMangoldt_div ε hεpos
  refine ⟨max N 1, le_max_right _ _, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by linarith
  have heX : N ≤ Real.exp 1 * X := by nlinarith
  have heXpos : 0 < Real.exp 1 * X := by positivity
  have h1 := hN X hXN
  have h2 := hN (Real.exp 1 * X) heX
  simp only [Real.dist_eq] at h1 h2
  have hA : psiSum X ≤ (1 + ε) * X := by
    have := (abs_lt.mp h1).2
    unfold psiSum
    rw [div_sub_one hXpos.ne', div_lt_iff₀ hXpos] at this
    linarith
  have hB : (1 - ε) * (Real.exp 1 * X) ≤ psiSum (Real.exp 1 * X) := by
    have := (abs_lt.mp h2).1
    unfold psiSum
    rw [div_sub_one heXpos.ne', lt_div_iff₀ heXpos] at this
    linarith
  have hε' : ε * (Real.exp 1 + 1) = (Real.exp 1 - 1) / 2 := by
    rw [hε]; field_simp
  nlinarith [hA, hB, hε']

/-- The window sum as a difference of `ψ`. -/
theorem sum_Ico_vonMangoldt_eq_psiSum_sub {X Y : ℝ} (hXY : X ≤ Y) :
    (∑ n ∈ Finset.Ico (⌊X⌋₊ + 1) (⌊Y⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) =
      psiSum Y - psiSum X := by
  unfold psiSum
  exact Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ (Nat.floor_mono hXY))

/-! ## The product pairing lower bound -/

/-- **The product pairing of a far-out fat nonnegative test.** -/
theorem productPrimePairing_ge (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hx₀ : 1 < x₀)
    (hsupp : ∀ x, x ∉ Icc (x₀ - 1) (x₀ + 1) → f x = 0) (hpos : ∀ x, 0 ≤ f x) (hh : 0 ≤ h)
    (hlow : ∀ x ∈ Icc (x₀ - 1) (x₀ + 1), h ≤ f x) :
    Real.exp (-(x₀ + 1 / 4)) * h ^ 2 *
        (psiSum (Real.exp 1 * Real.exp (2 * x₀ - 1 / 2)) - psiSum (Real.exp (2 * x₀ - 1 / 2))) ≤
      productPrimePairing f := by
  set X : ℝ := Real.exp (2 * x₀ - 1 / 2) with hX
  have hXpos : 0 < X := Real.exp_pos _
  have he := one_lt_exp_one
  have heX : Real.exp 1 * X = Real.exp (2 * x₀ + 1 / 2) := by
    rw [hX, ← Real.exp_add]; congr 1; ring
  have hε : 0 < x₀ - 1 := by linarith
  have hsupp' : ∀ x, x < x₀ - 1 → f x = 0 := fun x hx =>
    hsupp x (by rw [mem_Icc]; intro hm; linarith [hm.1])
  have hsumm := summable_productPrimePairing_terms (f := f) (ε := x₀ - 1) hfc hε hsupp'
  set S : Finset ℕ := Finset.Ico (⌊X⌋₊ + 1) (⌊Real.exp 1 * X⌋₊ + 1) with hS
  -- every term of the product pairing is nonnegative
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ vonMangoldtAtom n * convSquare f (Real.log n) := fun n =>
    mul_nonneg (vonMangoldtAtom_nonneg' n)
      (integral_nonneg fun t => mul_nonneg (hpos t) (hpos _))
  -- lower bound of each window term
  have hwin : ∀ n ∈ S, Real.exp (-(x₀ + 1 / 4)) * h ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) ≤
      vonMangoldtAtom n * convSquare f (Real.log n) := by
    intro n hn
    rw [hS, Finset.mem_Ico] at hn
    have hnX : X < n := by
      have := Nat.lt_floor_add_one X
      exact lt_of_lt_of_le this (by exact_mod_cast hn.1)
    have hneX : (n : ℝ) ≤ Real.exp 1 * X := by
      have := Nat.floor_le (le_of_lt (by positivity : (0 : ℝ) < Real.exp 1 * X))
      exact le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hn.2) this
    have hnpos : (0 : ℝ) < n := lt_trans hXpos hnX
    have hn2 : 2 ≤ n := by
      have h3 : Real.exp (3 / 2) ≤ X := by
        rw [hX]; exact Real.exp_le_exp.mpr (by linarith)
      have h4 : (2 : ℝ) < Real.exp (3 / 2) := by linarith [Real.add_one_le_exp (3 / 2 : ℝ)]
      have : (2 : ℝ) < n := by linarith
      exact_mod_cast this.le
    -- the logarithm lies in the half-width window
    have hlog_lo : 2 * x₀ - 1 / 2 < Real.log n := by
      have := Real.log_lt_log hXpos hnX
      rwa [hX, Real.log_exp] at this
    have hlog_hi : Real.log n ≤ 2 * x₀ + 1 / 2 := by
      have := Real.log_le_log hnpos hneX
      rwa [heX, Real.log_exp] at this
    have hcs : h ^ 2 ≤ convSquare f (Real.log n) :=
      sq_le_convSquare hf.continuous hfc hpos hh hlow (abs_le.mpr ⟨by linarith, by linarith⟩)
    -- the atom weight `Λ(n)/√n ≥ Λ(n) e^{−(x₀+1/4)}`
    have hatom : Real.exp (-(x₀ + 1 / 4)) * (ArithmeticFunction.vonMangoldt n : ℝ) ≤
        vonMangoldtAtom n := by
      unfold vonMangoldtAtom
      rw [if_pos hn2]
      have hsq : Real.sqrt n ≤ Real.exp (x₀ + 1 / 4) := by
        have : (n : ℝ) ≤ Real.exp (x₀ + 1 / 4) ^ 2 := by
          rw [← Real.exp_nat_mul]
          calc (n : ℝ) ≤ Real.exp 1 * X := hneX
            _ = Real.exp (2 * x₀ + 1 / 2) := heX
            _ = Real.exp (↑(2 : ℕ) * (x₀ + 1 / 4)) := by congr 1; push_cast; ring
        calc Real.sqrt n ≤ Real.sqrt (Real.exp (x₀ + 1 / 4) ^ 2) := Real.sqrt_le_sqrt this
          _ = Real.exp (x₀ + 1 / 4) := Real.sqrt_sq (Real.exp_pos _).le
      have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
      have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      rw [le_div_iff₀ hsqpos]
      calc Real.exp (-(x₀ + 1 / 4)) * (ArithmeticFunction.vonMangoldt n : ℝ) * Real.sqrt n
          ≤ Real.exp (-(x₀ + 1 / 4)) * (ArithmeticFunction.vonMangoldt n : ℝ) *
              Real.exp (x₀ + 1 / 4) := by
            gcongr
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) := by
            rw [mul_comm, ← mul_assoc, ← Real.exp_add]; simp
    calc Real.exp (-(x₀ + 1 / 4)) * h ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ)
        = (Real.exp (-(x₀ + 1 / 4)) * (ArithmeticFunction.vonMangoldt n : ℝ)) * h ^ 2 := by ring
      _ ≤ vonMangoldtAtom n * convSquare f (Real.log n) :=
          mul_le_mul hatom hcs (sq_nonneg h) (vonMangoldtAtom_nonneg' n)
  -- sum over the window and compare with the full series
  have hsum : (∑ n ∈ S, Real.exp (-(x₀ + 1 / 4)) * h ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ)) ≤
      ∑ n ∈ S, vonMangoldtAtom n * convSquare f (Real.log n) :=
    Finset.sum_le_sum hwin
  have htsum : (∑ n ∈ S, vonMangoldtAtom n * convSquare f (Real.log n)) ≤ productPrimePairing f := by
    unfold productPrimePairing
    exact hsumm.sum_le_tsum S (fun n _ => hterm_nonneg n)
  have hwindow : (∑ n ∈ S, Real.exp (-(x₀ + 1 / 4)) * h ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ))
      = Real.exp (-(x₀ + 1 / 4)) * h ^ 2 * (psiSum (Real.exp 1 * X) - psiSum X) := by
    rw [← Finset.mul_sum, hS, sum_Ico_vonMangoldt_eq_psiSum_sub (by nlinarith)]
  rw [← hwindow]
  exact hsum.trans htsum

/-! ## Assembly -/

/-- **Far-out fat nonnegative half-line tests have positive odd Markov form (unconditional).**
For every lower bound `h > 0` and `L²` bound `B` there is `X₀` such that every real `C²` test
`f ≥ 0` supported in `[x₀ − 1, x₀ + 1]`, bounded below by `h` there, with `∫ f² ≤ B` and
`x₀ ≥ X₀`, satisfies `M(f − f̃) > 0`. The product-prime pairing grows like `e^{x₀}` by the prime
number theorem and beats the archimedean mass and the ratio pairing, which are `O(‖f‖²)`. -/
theorem exists_farOut_nonneg_oddExt_markovEnergy_pos (h B : ℝ) (hh : 0 < h) :
    ∃ X₀ : ℝ, ∀ (f : ℝ → ℝ) (x₀ : ℝ), X₀ ≤ x₀ → ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ x, x ∉ Icc (x₀ - 1) (x₀ + 1) → f x = 0) → (∀ x, 0 ≤ f x) →
      (∀ x ∈ Icc (x₀ - 1) (x₀ + 1), h ≤ f x) → (∫ x, f x ^ 2) ≤ B →
      0 < markovEnergy (fun x => ((f x - f (-x) : ℝ) : ℂ)) := by
  obtain ⟨Y₀, hY₀1, hY₀⟩ := exists_psiSum_window
  have he := one_lt_exp_one
  set K : ℝ := ratioConst + 2 * |gammaHardyPhaseRate 0| with hK
  have hK0 : 0 ≤ K := by rw [hK]; have := ratioConst_nonneg; positivity
  -- the target growth: `(e−1)/2 · h² · e^{x₀ − 3/4} ≥ K B + 1`
  set T : ℝ := 2 * (K * B + 1) / ((Real.exp 1 - 1) * h ^ 2) with hT
  refine ⟨max (max 2 ((Real.log Y₀ + 1 / 2) / 2)) (3 / 4 + Real.log (max T 1)), ?_⟩
  intro f x₀ hx₀ hf hfc hsupp hpos hlow hB
  have hx₀2 : 2 ≤ x₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx₀
  have hx₀1 : 1 < x₀ := by linarith
  have hε : 0 < x₀ - 1 := by linarith
  have hsupp' : ∀ x, x < x₀ - 1 → f x = 0 := fun x hx =>
    hsupp x (by rw [mem_Icc]; intro hm; linarith [hm.1])
  -- the decomposition
  rw [markovEnergy_oddExtension_eq hf hfc hε hsupp',
    markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc]
  -- archimedean minus ratio
  have hA := archForm_ge hf hfc
  have hP := primeSum_le_of_support hf hfc hsupp
  have hf2 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hM : -(K * B) ≤ archForm f - primeSum f := by
    have h1 : -(2 * |gammaHardyPhaseRate 0|) * ∫ x, f x ^ 2 ≤ 2 * gammaHardyPhaseRate 0 * ∫ x, f x ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hf2
      linarith [neg_abs_le (gammaHardyPhaseRate 0)]
    have h2 : K * ∫ x, f x ^ 2 ≤ K * B := mul_le_mul_of_nonneg_left hB hK0
    rw [hK] at h2 ⊢
    nlinarith [ratioConst_nonneg]
  -- trivial-zero squares
  have hsq : 0 ≤ ∑' k : ℕ, trivialZeroMoment f k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  -- product pairing
  have hXwin : Y₀ ≤ Real.exp (2 * x₀ - 1 / 2) := by
    have : (Real.log Y₀ + 1 / 2) / 2 ≤ x₀ :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx₀
    have hY₀pos : 0 < Y₀ := by linarith
    calc Y₀ = Real.exp (Real.log Y₀) := (Real.exp_log hY₀pos).symm
      _ ≤ Real.exp (2 * x₀ - 1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hwin := hY₀ _ hXwin
  have hProd := productPrimePairing_ge hf hfc hx₀1 hsupp hpos hh.le hlow
  have hgrow : K * B + 1 ≤ Real.exp (-(x₀ + 1 / 4)) * h ^ 2 *
      ((Real.exp 1 - 1) / 2 * Real.exp (2 * x₀ - 1 / 2)) := by
    have hpos' : 0 < (Real.exp 1 - 1) * h ^ 2 := by positivity
    have hexp : Real.exp (-(x₀ + 1 / 4)) * Real.exp (2 * x₀ - 1 / 2) = Real.exp (x₀ - 3 / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    have hx₀3 : 3 / 4 + Real.log (max T 1) ≤ x₀ := le_trans (le_max_right _ _) hx₀
    have hT1 : T ≤ Real.exp (x₀ - 3 / 4) := by
      calc T ≤ max T 1 := le_max_left _ _
        _ = Real.exp (Real.log (max T 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (x₀ - 3 / 4) := Real.exp_le_exp.mpr (by linarith)
    have hTeq : T * ((Real.exp 1 - 1) * h ^ 2) = 2 * (K * B + 1) := by
      have hne : Real.exp 1 - 1 ≠ 0 := (sub_pos.mpr he).ne'
      have hh2 : h ^ 2 ≠ 0 := by positivity
      rw [hT]; field_simp
    calc K * B + 1 = T * ((Real.exp 1 - 1) * h ^ 2) / 2 := by rw [hTeq]; ring
      _ ≤ Real.exp (x₀ - 3 / 4) * ((Real.exp 1 - 1) * h ^ 2) / 2 := by gcongr
      _ = Real.exp (-(x₀ + 1 / 4)) * h ^ 2 *
          ((Real.exp 1 - 1) / 2 * Real.exp (2 * x₀ - 1 / 2)) := by
          rw [← hexp]; ring
  have hProd' : K * B + 1 ≤ productPrimePairing f := by
    refine le_trans hgrow (le_trans ?_ hProd)
    have h0 : 0 ≤ Real.exp (-(x₀ + 1 / 4)) * h ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hwin h0
  linarith

end

end RHTower
