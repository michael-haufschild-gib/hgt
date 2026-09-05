import GaloisForLFunctions.RHTower.HighBlockDirectMeanSquare
import GaloisForLFunctions.RHTower.HighBlockChiModulus

/-!
# High-block law, brick B5: the dual×dual mean value with the frozen weight

With the dual weight frozen at a height `T`, the reflected head
`H_T(τ) = Σ_{n<L} (n+1)^{s−1} W_{d,T}((n+1)x)` is a Dirichlet polynomial at frequency `+τ`;
its modulus equals that of the conjugate polynomial at frequency `−τ`, so `H_T·Ψ` has the modulus
of one `dirPoly` of length `LN` at frequency `−τ`. The `χ` factor contributes the exact weight
`(τ/2π)^{2d} e^{e(τ)}` (`HighBlockChiModulus`), and the corpus's weighted transfer
(`abs_integral_weighted_meanSquare_sub_le`) turns the mean-value theorem into

`∫_{T₁}^{T₂} ‖χ H_T Ψ‖² ≤ e^{ε} [ E_dual · ∫_{T₁}^{T₂} (τ/2π)^{2d} dτ + 16 LN (1+log LN) E_dual (T₂/2π)^{2d} ]`,

`ε = 2d(π/T₁ + 5/T₁²)`, `E_dual` the frozen dual coefficient energy.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- Frozen reflected coefficient `(n+1)^{−½−d} W_{d,T}((n+1)x)`. -/
def highBlockDualCoeffFrozen (d x T : ℝ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ (displacedLinePt d 0 - 1) * smoothAFEZetaDisplacedDualWeight d T ((n + 1 : ℝ) * x)

/-- Frozen reflected head at height `τ`, weight frozen at `T`. -/
def highBlockDualHeadFrozen (d x T τ : ℝ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.range L,
    (n + 1 : ℂ) ^ (displacedLinePt d τ - 1) * smoothAFEZetaDisplacedDualWeight d T ((n + 1 : ℝ) * x)

theorem highBlockDualHeadFrozen_eq_dirPoly (d x T τ : ℝ) (L : ℕ) :
    highBlockDualHeadFrozen d x T τ L =
      Sieve.dirPoly L (fun n => highBlockDualCoeffFrozen d x T n) τ := by
  rw [highBlockDualHeadFrozen, sieveDirPoly_nat_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [highBlockDualCoeffFrozen, natSucc_cpow_displacedLinePt_sub_one_eq_phase]
  ring

/-- The modulus of the frozen head is that of the conjugate polynomial at frequency `−τ`. -/
theorem norm_highBlockDualHeadFrozen_eq (d x T τ : ℝ) (L : ℕ) :
    ‖highBlockDualHeadFrozen d x T τ L‖ =
      ‖Sieve.dirPoly L (fun n => (starRingEnd ℂ) (highBlockDualCoeffFrozen d x T n)) (-τ)‖ := by
  rw [highBlockDualHeadFrozen_eq_dirPoly, Sieve.dirPoly_conj_neg, neg_neg, Complex.norm_conj]

/-- Frozen dual coefficient energy against a Fin-indexed mollifier `a`. -/
def highBlockDualEnergy (d x T : ℝ) (L N : ℕ) (a : Fin N → ℂ) : ℝ :=
  ∑ r : Fin (L * N),
    ‖Sieve.dirConv L N (fun n => (starRingEnd ℂ) (highBlockDualCoeffFrozen d x T n)) a r‖ ^ 2

/-- Pointwise: `‖χ H_T Ψ‖² = ‖χ‖² ‖P(−τ)‖²` with `P` the conjugate convolution polynomial. -/
theorem normSq_chi_mul_highBlockDualHeadFrozen_mul_eq (d x T τ : ℝ) (L N : ℕ) (a : Fin N → ℂ) :
    ‖zetaChi (displacedLinePt d τ) * highBlockDualHeadFrozen d x T τ L *
        Sieve.dirPoly N a (-τ)‖ ^ 2 =
      ‖zetaChi (displacedLinePt d τ)‖ ^ 2 *
        ‖Sieve.dirPoly (L * N)
          (Sieve.dirConv L N (fun n => (starRingEnd ℂ) (highBlockDualCoeffFrozen d x T n)) a)
          (-τ)‖ ^ 2 := by
  rw [norm_mul, norm_mul, norm_highBlockDualHeadFrozen_eq, mul_assoc, ← norm_mul,
    Sieve.dirPoly_mul_eq_dirPoly, mul_pow]

/-- Continuity of `χ` along the displaced line. -/
theorem continuous_zetaChi_displacedLinePt {d : ℝ} (hd0 : 0 ≤ d) :
    Continuous (fun τ : ℝ => zetaChi (displacedLinePt d τ)) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have hz : Gammaℝ (1 - displacedLinePt d τ) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp [displacedLinePt]
    linarith
  have hmap : ContinuousAt (fun τ : ℝ => displacedLinePt d τ) τ := by
    unfold displacedLinePt
    fun_prop
  exact ContinuousAt.comp (f := fun τ : ℝ => displacedLinePt d τ)
    (zetaChi_analyticAt hz).continuousAt hmap

/-- **B5.** The frozen dual×dual mean square on `[T₁, T₂]`, `0 < T₁ ≤ T₂`. -/
theorem integral_normSq_chi_mul_highBlockDualFrozen_le {d T₁ T₂ : ℝ} (hd0 : 0 ≤ d)
    (hd4 : d ≤ 1 / 4) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) (x T : ℝ) (L N : ℕ) (a : Fin N → ℂ) :
    (∫ τ in T₁..T₂, ‖zetaChi (displacedLinePt d τ) * highBlockDualHeadFrozen d x T τ L *
        Sieve.dirPoly N a (-τ)‖ ^ 2) ≤
      Real.exp (2 * d * (Real.pi / T₁ + 5 / T₁ ^ 2)) *
        (highBlockDualEnergy d x T L N a * (∫ τ in T₁..T₂, chiModulusWeight (2 * d) τ) +
          8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) *
            highBlockDualEnergy d x T L N a * (2 * chiModulusWeight (2 * d) T₂)) := by
  set c : Fin (L * N) → ℂ :=
    Sieve.dirConv L N (fun n => (starRingEnd ℂ) (highBlockDualCoeffFrozen d x T n)) a with hc
  set P : ℝ → ℂ := fun τ => Sieve.dirPoly (L * N) c (-τ) with hP
  set M : ℝ := highBlockDualEnergy d x T L N a with hM
  set E : ℝ := 8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * M with hE
  set ε : ℝ := 2 * d * (Real.pi / T₁ + 5 / T₁ ^ 2) with hε
  set w : ℝ → ℝ := chiModulusWeight (2 * d) with hw
  have hPc : Continuous P := (Sieve.continuous_dirPoly _ _).comp continuous_neg
  have hχc := continuous_zetaChi_displacedLinePt hd0
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => by positivity
  -- pointwise rewrite
  have hpoint : ∀ τ : ℝ,
      ‖zetaChi (displacedLinePt d τ) * highBlockDualHeadFrozen d x T τ L *
          Sieve.dirPoly N a (-τ)‖ ^ 2 =
        ‖zetaChi (displacedLinePt d τ)‖ ^ 2 * ‖P τ‖ ^ 2 := fun τ =>
    normSq_chi_mul_highBlockDualHeadFrozen_mul_eq d x T τ L N a
  rw [intervalIntegral.integral_congr (fun τ _ => hpoint τ)]
  -- the χ-weight bound on the window
  have hchi : ∀ τ ∈ Set.Icc T₁ T₂,
      ‖zetaChi (displacedLinePt d τ)‖ ^ 2 * ‖P τ‖ ^ 2 ≤ Real.exp ε * (w τ * ‖P τ‖ ^ 2) := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le hT₁ hτ.1
    obtain ⟨e, he, heq⟩ := exists_normSq_zetaChi_displacedLinePt_eq_weight_mul_exp hd0 hd4 hτ0
    have hee : e ≤ ε := by
      refine (le_abs_self e).trans (he.trans ?_)
      rw [hε]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : Real.pi / τ ≤ Real.pi / T₁ :=
        div_le_div_of_nonneg_left Real.pi_pos.le hT₁ hτ.1
      have h2 : 5 / τ ^ 2 ≤ 5 / T₁ ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ hT₁.le hτ.1 2
      linarith
    rw [heq]
    have hwpos : 0 < w τ := chiModulusWeight_pos hτ0
    calc w τ * Real.exp e * ‖P τ‖ ^ 2 ≤ w τ * Real.exp ε * ‖P τ‖ ^ 2 := by
          gcongr
      _ = Real.exp ε * (w τ * ‖P τ‖ ^ 2) := by ring
  have hwOn : ContinuousOn w (Set.uIcc T₁ T₂) := by
    intro τ hτ
    rw [Set.uIcc_of_le hT] at hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le hT₁ hτ.1
    exact (hasDerivAt_chiModulusWeight (α := 2 * d) hτ0).continuousAt.continuousWithinAt
  have hint1 : IntervalIntegrable
      (fun τ => ‖zetaChi (displacedLinePt d τ)‖ ^ 2 * ‖P τ‖ ^ 2) volume T₁ T₂ :=
    ((hχc.norm.pow 2).mul (hPc.norm.pow 2)).intervalIntegrable T₁ T₂
  have hint2 : IntervalIntegrable (fun τ => Real.exp ε * (w τ * ‖P τ‖ ^ 2)) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (hwOn.mul (hPc.norm.pow 2).continuousOn)
  have hstep1 := intervalIntegral.integral_mono_on hT hint1 hint2 hchi
  rw [intervalIntegral.integral_const_mul] at hstep1
  have hmvt : ∀ u ∈ Set.Icc T₁ T₂, |(∫ τ in T₁..u, ‖P τ‖ ^ 2) - (u - T₁) * M| ≤ E := by
    intro u _
    exact Sieve.dirichlet_meanValue_window_neg (L * N) c T₁ u
  have htransfer := abs_integral_weighted_meanSquare_sub_le (a := T₁) (b := T₂) (M := M) (E := E)
    hT (w := w) (w' := fun τ => (2 * d) / τ * chiModulusWeight (2 * d) τ) (D := P) hPc
    (fun τ hτ => by
      rw [Set.uIcc_of_le hT] at hτ
      exact hasDerivAt_chiModulusWeight (lt_of_lt_of_le hT₁ hτ.1))
    (continuousOn_deriv_chiModulusWeight hT₁ hT)
    (fun τ hτ => by
      have hτ0 : 0 < τ := lt_of_lt_of_le hT₁ hτ.1
      have := chiModulusWeight_pos (α := 2 * d) hτ0
      positivity)
    (chiModulusWeight_pos hT₁).le
    hmvt
  have hwa : 0 ≤ w T₁ := (chiModulusWeight_pos hT₁).le
  have hlog : 0 ≤ Real.log ((L * N : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hE0 : 0 ≤ E := by
    rw [hE]
    positivity
  have hup : (∫ τ in T₁..T₂, w τ * ‖P τ‖ ^ 2) ≤ M * (∫ τ in T₁..T₂, w τ) + E * (2 * w T₂) := by
    have h := (abs_le.mp htransfer).2
    nlinarith [h, mul_nonneg hE0 hwa]
  calc (∫ τ in T₁..T₂, ‖zetaChi (displacedLinePt d τ)‖ ^ 2 * ‖P τ‖ ^ 2)
      ≤ Real.exp ε * ∫ τ in T₁..T₂, w τ * ‖P τ‖ ^ 2 := hstep1
    _ ≤ Real.exp ε * (M * (∫ τ in T₁..T₂, w τ) + E * (2 * w T₂)) :=
        mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le

end

end RHTower
