import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum
import GaloisForLFunctions.RHTower.LagExplicitFormula
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.SeamStripRamification
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain
import GaloisForLFunctions.RHTower.XiZeroCountingFunction
import GaloisForLFunctions.RHTower.WeilDeletionTwoBump
import Zeta23.WeilEF.Main
import Zeta23.Statement.SeamClosed

/-!
# Zero-side inputs for the single-prime deletion argument

Zeta23's explicit formula sums over the nontrivial zeros `ρ` of `ζ` with multiplicity
`zeroMult ρ = (analyticOrderAt ζ ρ).toNat`, evaluated at `γ_ρ = (ρ − ½)/i`.  This module
transports three facts of the corpus's `ξ`-divisor to that zero configuration:

* every nontrivial zero is a support point of the divisor of `ξ`, with the same multiplicity;
* every nontrivial zero has `|Im ρ|² > 41/2`, hence `‖γ_ρ‖² > 41/2`;
* `Σ_ρ m_ρ/‖γ_ρ‖² ≤ (11/10)·(2 + γ − log 4π) < 33/100`, from the certified genus zero-sum
  `Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π` and the termwise comparison
  `1/‖γ_ρ‖² ≤ (11/10)·Re(1/(ρ(1−ρ)))`.

The comparison lemma `carrier_tsum_le` bounds any multiplicity-weighted sum over Zeta23's zeros
by the corresponding sum over the corpus's zero copies.
-/

open Complex

namespace RHTower.WeilDeletion

noncomputable section

/-! ## Nontrivial zeros are support points of the divisor of `ξ` -/

theorem xi_analyticOrderAt_ne_zero_of_xi_eq_zero {ρ : ℂ} (hxi : xi ρ = 0) :
    analyticOrderAt xi ρ ≠ 0 := by
  intro h0
  rcases analyticOrderAt_eq_zero.mp h0 with hna | hne
  · exact hna (xi_differentiable.analyticAt ρ)
  · exact hne hxi

theorem mem_xiDivisorSupport_of_nontrivialZero {ρ : ℂ} (h : Zeta23.IsNontrivialZero ρ) :
    ρ ∈ (MeromorphicOn.divisor xi Set.univ).support := by
  obtain ⟨hζ, hre0, hre1⟩ := h
  have hxi : xi ρ = 0 := (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).mpr hζ
  have hord := xi_analyticOrderAt_ne_zero_of_xi_eq_zero hxi
  rw [Function.mem_support, xi_divisor_apply_of_mem (Set.mem_univ ρ)]
  intro hz
  apply hord
  have hz' : (analyticOrderAt xi ρ).toNat = 0 := by exact_mod_cast hz
  rw [← ENat.coe_toNat (xi_orderAt_ne_top ρ), hz']
  rfl

/-- The support point of a nontrivial zero. -/
def toSupport (ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ}) : XiDivisorSupport :=
  ⟨ρ.1, mem_xiDivisorSupport_of_nontrivialZero ρ.2⟩

theorem toSupport_coe (ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ}) :
    ((toSupport ρ : XiDivisorSupport) : ℂ) = ρ.1 := rfl

theorem toSupport_injective : Function.Injective toSupport := by
  intro a b h
  apply Subtype.ext
  have := congrArg (fun x : XiDivisorSupport => (x : ℂ)) h
  exact this

theorem zeroMult_eq_xiSupportMultiplicity (ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ}) :
    Zeta23.zeroMult ρ.1 = xiSupportMultiplicity (toSupport ρ) := by
  rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat, toSupport_coe]
  unfold Zeta23.zeroMult
  rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨ρ.2.2.1, ρ.2.2.2⟩]

/-- A zero copy above a nontrivial zero. -/
def toCopy (ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ}) : XiZeroCopy :=
  ⟨toSupport ρ, ⟨0, xiSupportMultiplicity_pos (toSupport ρ)⟩⟩

theorem toCopy_fst_coe (ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ}) :
    (((toCopy ρ).1 : XiDivisorSupport) : ℂ) = ρ.1 := rfl

/-! ## Ordinates -/

theorem fortyOne_div_two_lt_im_sq_of_nontrivialZero {ρ : ℂ} (h : Zeta23.IsNontrivialZero ρ) :
    (41 / 2 : ℝ) < ρ.im ^ 2 :=
  xiZeroCopy_fortyOne_div_two_lt_im_sq (toCopy ⟨ρ, h⟩)

theorem fortyOne_div_two_lt_normSq_gammaOf_of_nontrivialZero {ρ : ℂ}
    (h : Zeta23.IsNontrivialZero ρ) : (41 / 2 : ℝ) < ‖Zeta23.gammaOf ρ‖ ^ 2 := by
  have h1 := fortyOne_div_two_lt_im_sq_of_nontrivialZero h
  have h2 := Zeta23.WeilEF.abs_im_le_norm_gammaOf ρ
  have h3 : ρ.im ^ 2 ≤ ‖Zeta23.gammaOf ρ‖ ^ 2 := by
    rw [← sq_abs ρ.im]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  linarith

theorem gammaOf_ne_zero_of_nontrivialZero {ρ : ℂ} (h : Zeta23.IsNontrivialZero ρ) :
    Zeta23.gammaOf ρ ≠ 0 := by
  intro h0
  have := fortyOne_div_two_lt_normSq_gammaOf_of_nontrivialZero h
  rw [h0, norm_zero] at this
  norm_num at this

theorem abs_im_gammaOf_le_half_of_nontrivialZero {ρ : ℂ} (h : Zeta23.IsNontrivialZero ρ) :
    |(Zeta23.gammaOf ρ).im| ≤ 1 / 2 :=
  (Zeta23.WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le

/-- The spectral point of a copy is `γ_ρ`. -/
theorem gammaOf_eq_xiSpectralPoint (q : XiZeroCopy) :
    Zeta23.gammaOf (q.1 : ℂ) = xiSpectralPoint q := by
  unfold Zeta23.gammaOf
  rw [xiZeroCopy_eq_half_add q]
  field_simp
  ring

/-! ## The inverse-square sum over the zeros -/

theorem key_ineq {x y : ℝ} (hx : 41 / 2 < x ^ 2) (hy : y ^ 2 < 1 / 4) :
    (x * x + y * y)⁻¹ ≤ (11 / 10) * ((1 / 4 + x ^ 2 - y ^ 2) /
      ((1 / 4 + x ^ 2 - y ^ 2) * (1 / 4 + x ^ 2 - y ^ 2) + (2 * x * y) * (2 * x * y))) := by
  set A := 1 / 4 + x ^ 2 - y ^ 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; nlinarith
  have hS : 0 < x * x + y * y := by nlinarith
  have hD : 0 < A * A + (2 * x * y) * (2 * x * y) :=
    add_pos_of_pos_of_nonneg (mul_pos hApos hApos) (mul_self_nonneg _)
  have hrw : (11 / 10 : ℝ) * (A / (A * A + 2 * x * y * (2 * x * y))) =
      (11 * A) / (10 * (A * A + 2 * x * y * (2 * x * y))) := by
    field_simp
  rw [inv_eq_one_div, hrw, div_le_div_iff₀ hS (by positivity)]
  have h0 : 0 ≤ x ^ 2 * (1 - 4 * y ^ 2) := mul_nonneg (sq_nonneg x) (by linarith)
  have h1 : A * A + 2 * x * y * (2 * x * y) ≤ A * A + x ^ 2 := by nlinarith [h0]
  have h2 : x ^ 2 ≤ A := by rw [hAdef]; linarith
  have h3 : A + 1 ≤ 11 / 10 * (x * x + y * y) := by rw [hAdef]; nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 hApos.le
  nlinarith [h1, h2, h4]

theorem inv_normSq_spectralPoint_le (q : XiZeroCopy) :
    1 / ‖xiSpectralPoint q‖ ^ 2 ≤
      (11 / 10) * ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  have hρ := xiZeroCopy_eq_half_add q
  have hx : (xiSpectralPoint q).re = (q.1 : ℂ).im := by rw [hρ]; simp
  have hy : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by rw [hρ]; simp
  have hx2 : (41 / 2 : ℝ) < (xiSpectralPoint q).re ^ 2 := by
    rw [hx]; exact xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hre0 := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  have hy2 : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by rw [hy]; nlinarith
  have hprod : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = 1 / 4 + xiSpectralPoint q ^ 2 := by
    rw [hρ]
    linear_combination (-(xiSpectralPoint q ^ 2)) * Complex.I_mul_I
  rw [hprod, one_div, one_div, Complex.inv_re, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  have hA : (1 / 4 + xiSpectralPoint q ^ 2).re =
      1 / 4 + (xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2 := by
    simp [sq, Complex.add_re, Complex.mul_re]
    ring
  have hB : (1 / 4 + xiSpectralPoint q ^ 2).im =
      2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
    simp [sq, Complex.add_im, Complex.mul_im]
    ring
  rw [hA, hB]
  exact key_ineq hx2 hy2

/-- `Σ_ρ 1/‖γ_ρ‖² ≤ (11/10)·(2 + γ − log 4π)` over all zero copies. -/
theorem tsum_inv_normSq_spectralPoint_le :
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 ≤ (11 / 10) * poleSharpConstant := by
  have hsum := summable_inv_mul_one_sub
  have hre : Summable (fun q : XiZeroCopy => ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re) :=
    hsum.mapL Complex.reCLM
  calc ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
      ≤ ∑' q : XiZeroCopy, (11 / 10) * ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
        (xiSpectralPoint_inv_sq_summable).tsum_le_tsum (fun q => inv_normSq_spectralPoint_le q)
          (hre.mul_left _)
    _ = (11 / 10) * ∑' q : XiZeroCopy, ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
        tsum_mul_left
    _ = (11 / 10) * poleSharpConstant := by
        rw [← Complex.re_tsum hsum, tsum_inv_zero_mul_one_sub_zero_re]

theorem poleSharpConstant_lt : poleSharpConstant < 3 / 10 := by
  unfold poleSharpConstant
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have h12 : (12 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  have hlog12 : Real.log 12 ≤ Real.log (4 * Real.pi) := Real.log_le_log (by norm_num) h12
  have h12' : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have hlog2 := Real.log_two_gt_d9
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  linarith

theorem tsum_inv_normSq_spectralPoint_lt :
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 < 33 / 100 := by
  have := tsum_inv_normSq_spectralPoint_le
  have := poleSharpConstant_lt
  linarith

/-! ## Comparison of a multiplicity-weighted sum with the sum over copies -/

/-- The sum over the copies above a finite set of supports. -/
theorem sum_copies (W : Finset XiDivisorSupport) (g : ℂ → ℝ) :
    ∑ q ∈ W.sigma (fun ρ => (Finset.univ :
        Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)))))),
      g ((q.1 : XiDivisorSupport) : ℂ) =
      ∑ ρ ∈ W, (xiSupportMultiplicity ρ : ℝ) * g (ρ : ℂ) := by
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hconst : ∀ i ∈ (Finset.univ : Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ)
      (ρ : ℂ))))), g (((⟨ρ, i⟩ : XiZeroCopy).1 : XiDivisorSupport) : ℂ) = g (ρ : ℂ) :=
    fun _ _ => rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rfl

/-- A sum over Zeta23's nontrivial zeros, weighted by multiplicity and dominated termwise by
`m_ρ · g(ρ)`, is at most the sum of `g` over the corpus's zero copies. -/
theorem carrier_tsum_le (hs : Zeta23.ZetaSeam) (g : ℂ → ℝ)
    (hg : ∀ q : XiZeroCopy, 0 ≤ g (q.1 : ℂ))
    (hsum : Summable (fun q : XiZeroCopy => g (q.1 : ℂ)))
    (h : (Zeta23.zetaZeros hs).carrier → ℝ)
    (hh : ∀ ρ, h ρ ≤ ((Zeta23.zetaZeros hs).mult ρ : ℝ) * g (ρ : ℂ)) :
    ∑' ρ : (Zeta23.zetaZeros hs).carrier, h ρ ≤ ∑' q : XiZeroCopy, g (q.1 : ℂ) := by
  classical
  refine tsum_le_of_sum_le' (tsum_nonneg hg) fun F => ?_
  -- the carrier is the set of nontrivial zeros
  have hcar : ∀ ρ : (Zeta23.zetaZeros hs).carrier, Zeta23.IsNontrivialZero (ρ : ℂ) := fun ρ => ρ.2
  let e : (Zeta23.zetaZeros hs).carrier → {ρ : ℂ // Zeta23.IsNontrivialZero ρ} :=
    fun ρ => ⟨ρ.1, hcar ρ⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact this
  have hinj : Set.InjOn (toSupport ∘ e) (F : Set _) := (toSupport_injective.comp he).injOn
  calc ∑ ρ ∈ F, h ρ
      ≤ ∑ ρ ∈ F, ((Zeta23.zetaZeros hs).mult ρ : ℝ) * g (ρ : ℂ) :=
        Finset.sum_le_sum fun ρ _ => hh ρ
    _ = ∑ ρ' ∈ F.image (toSupport ∘ e), (xiSupportMultiplicity ρ' : ℝ) * g (ρ' : ℂ) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        simp only [Function.comp]
        rw [← zeroMult_eq_xiSupportMultiplicity, toSupport_coe]
        rfl
    _ = ∑ q ∈ (F.image (toSupport ∘ e)).sigma (fun ρ => (Finset.univ :
          Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)))))),
          g ((q.1 : XiDivisorSupport) : ℂ) := (sum_copies _ g).symm
    _ ≤ ∑' q : XiZeroCopy, g (q.1 : ℂ) := hsum.sum_le_tsum _ (fun q _ => hg q)

end

end RHTower.WeilDeletion
