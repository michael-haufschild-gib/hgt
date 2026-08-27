import GaloisForLFunctions.RHTower.SuzukiScrewWeilIdentity
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import GaloisForLFunctions.RHTower.LiCriterion

noncomputable section

/-!
# Suzuki's Corollary 4.6

`g_n(x) = e^{-x/2} Σ_{j=1}^n C(n,j)(-x)^{j-1}/(j-1)!` on `x > 0` is the Bombieri--Lagarias test
family.  Its Fourier transform in Suzuki's normalisation is computed here in closed form,

`ĝ_n(z) = 1 - (1 - 1/s)ⁿ`,  `s = 1/2 - iz`,

from the complex-rate half-line Laplace transform of a monomial
(`HTGeometry.integral_Ioi_pow_mul_cexp`) and the binomial theorem.

At a spectral point `γ` with `ρ = 1/2 + iγ` this gives `ĝ_n(-γ) = 1 - w_ρⁿ` and
`(ĝ_n)^♯(-γ) = 1 - w_ρ⁻ⁿ`, whose product is exactly the paired Li summand `2 - w_ρⁿ - w_ρ⁻ⁿ`
(the conjugate point is `1 - ρ`, and `w_{1-ρ} = w_ρ⁻¹`).  Hence

`⟨g_n, g_n⟩_W = 2 λ_n`,

and Li's criterion (`LiCriterion`) turns nonnegativity of `⟨g_n,g_n⟩_W` — which Suzuki's equality
`‖g_n‖₀² = ⟨g_n,g_n⟩_W` supplies, `‖·‖₀²` being a nonnegative real — into the Riemann hypothesis.
That is [BoLa99, §4], and with it Corollary 4.6.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Bombieri--Lagarias's test function
`g_n(x) = e^{-x/2} Σ_{j=1}^n C(n,j)(-x)^{j-1}/(j-1)!` on `x > 0`, `n/2` at `0`, `0` on `x < 0`,
written with the shifted index `k = j - 1`. -/
def suzukiLiTestFun (n : ℕ) (x : ℝ) : ℂ :=
  if 0 < x then
    Complex.exp (-((x : ℂ) / 2)) *
      ∑ k ∈ Finset.range n,
        ((n.choose (k + 1) : ℂ) * (-1) ^ k / ((k.factorial : ℕ) : ℂ)) * (x : ℂ) ^ k
  else if x = 0 then (n : ℂ) / 2 else 0

theorem sum_choose_succ_pow (t : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (n.choose (k + 1) : ℂ) * t ^ (k + 1) = (t + 1) ^ n - 1 := by
  have h := add_pow t (1 : ℂ) n
  simp only [one_pow, mul_one] at h
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one] at h
  have h2 : ∑ k ∈ Finset.range n, t ^ (k + 1) * (n.choose (k + 1) : ℂ)
      = ∑ k ∈ Finset.range n, (n.choose (k + 1) : ℂ) * t ^ (k + 1) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [h2] at h
  rw [h]
  ring


/-- **The Fourier transform of the Bombieri--Lagarias test function.**
`ĝ_n(z) = 1 - (1 - 1/s)ⁿ` with `s = 1/2 - iz`. -/
theorem suzukiEntireFourier_liTestFun (n : ℕ) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.im) :
    suzukiEntireFourier (suzukiLiTestFun n) z = 1 - (1 - 1 / (1 / 2 - I * z)) ^ n := by
  set s : ℂ := 1 / 2 - I * z with hsdef
  have hsre : 0 < s.re := by
    have hval : s.re = 1 / 2 + z.im := by
      rw [hsdef]
      simp [Complex.sub_re, Complex.mul_re]
    rw [hval]
    linarith
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hsre
    simp at hsre
  set c : ℕ → ℂ :=
    fun k => (n.choose (k + 1) : ℂ) * (-1) ^ k / ((k.factorial : ℕ) : ℂ) with hcdef
  have hae : (fun x : ℝ => suzukiLiTestFun n x * Complex.exp (I * z * (x : ℂ)))
      =ᵐ[volume] Set.indicator (Ioi (0 : ℝ))
        (fun x : ℝ => ∑ k ∈ Finset.range n, c k * ((x : ℂ) ^ k * Complex.exp (-(s * x)))) := by
    have hnull : volume ({(0 : ℝ)} : Set ℝ) = 0 := by simp
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
    have hx0 : x ≠ 0 := fun h => hx (by simp [h])
    rcases lt_or_gt_of_ne hx0 with hlt | hgt
    · rw [Set.indicator_of_notMem (by simpa using hlt.le)]
      rw [suzukiLiTestFun, if_neg (by linarith), if_neg hx0, zero_mul]
    · rw [Set.indicator_of_mem (by simpa using hgt), suzukiLiTestFun, if_pos hgt]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hexp : Complex.exp (-((x : ℂ) / 2)) * Complex.exp (I * z * (x : ℂ))
          = Complex.exp (-(s * x)) := by
        rw [← Complex.exp_add]
        congr 1
        rw [hsdef]
        ring
      calc Complex.exp (-((x : ℂ) / 2)) *
              ((n.choose (k + 1) : ℂ) * (-1) ^ k / ((k.factorial : ℕ) : ℂ) * (x : ℂ) ^ k) *
              Complex.exp (I * z * (x : ℂ))
          = ((n.choose (k + 1) : ℂ) * (-1) ^ k / ((k.factorial : ℕ) : ℂ)) * (x : ℂ) ^ k *
              (Complex.exp (-((x : ℂ) / 2)) * Complex.exp (I * z * (x : ℂ))) := by ring
        _ = c k * ((x : ℂ) ^ k * Complex.exp (-(s * x))) := by
              rw [hexp]
              simp only [hcdef]
              ring
  rw [suzukiEntireFourier, MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [MeasureTheory.integral_finsetSum _ (fun k _ =>
    (integrableOn_natPow_mul_cexp hsre k).const_mul (c k))]
  have hterm : ∀ k ∈ Finset.range n,
      (∫ x in Ioi (0 : ℝ), c k * ((x : ℂ) ^ k * Complex.exp (-(s * x))))
        = (n.choose (k + 1) : ℂ) * (-1) ^ k / s ^ (k + 1) := by
    intro k _
    rw [MeasureTheory.integral_const_mul, integral_Ioi_pow_mul_cexp hsre k, hcdef]
    have hfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero k
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hre : ∀ k ∈ Finset.range n,
      (n.choose (k + 1) : ℂ) * (-1) ^ k / s ^ (k + 1)
        = -((n.choose (k + 1) : ℂ) * (-(1 / s)) ^ (k + 1)) := by
    intro k _
    have hexp : (-(1 / s)) ^ (k + 1) = ((-1) ^ k * (-1)) / s ^ (k + 1) := by
      rw [neg_pow, div_pow, one_pow, pow_succ]
      ring
    rw [hexp]
    have hspow : s ^ (k + 1) ≠ 0 := pow_ne_zero _ hsne
    field_simp
  rw [Finset.sum_congr rfl hre]
  have hneg : ∑ k ∈ Finset.range n, -((n.choose (k + 1) : ℂ) * (-(1 / s)) ^ (k + 1))
      = -(∑ k ∈ Finset.range n, (n.choose (k + 1) : ℂ) * (-(1 / s)) ^ (k + 1)) := by
    simp
  rw [hneg, sum_choose_succ_pow (-(1 / s)) n,
    show -(1 / s) + 1 = 1 - 1 / s from by ring]
  ring


/-! ## The Weil form of `g_n` -/

theorem abs_im_xiSpectralPointSupport_lt (ρ : XiDivisorSupport) :
    -(1 / 2 : ℝ) < (xiSpectralPointSupport ρ).im ∧ (xiSpectralPointSupport ρ).im < 1 / 2 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit ρ
  rw [im_xiSpectralPointSupport]
  constructor <;> linarith

theorem half_sub_I_mul_neg_spectral (ρ : XiDivisorSupport) :
    1 / 2 - Complex.I * (-(xiSpectralPointSupport ρ)) = (ρ : ℂ) := by
  show 1 / 2 - Complex.I * (-(((ρ : ℂ) - 1 / 2) * (-Complex.I))) = (ρ : ℂ)
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (1 / 2 - (ρ : ℂ)) * hI

theorem conj_half_ofReal : (starRingEnd ℂ) ((1 : ℂ) / 2) = 1 / 2 := by
  rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]

theorem conj_half_sub_I_mul_conj_neg_spectral (ρ : XiDivisorSupport) :
    (starRingEnd ℂ) (1 / 2 - Complex.I *
        ((starRingEnd ℂ) (-(xiSpectralPointSupport ρ)))) = 1 - (ρ : ℂ) := by
  have hρ := half_sub_I_mul_neg_spectral ρ
  have hstep : (1 : ℂ) / 2 - Complex.I * ((starRingEnd ℂ) (-(xiSpectralPointSupport ρ)))
      = (starRingEnd ℂ) (1 / 2 - Complex.I * (xiSpectralPointSupport ρ)) := by
    rw [map_sub, map_mul, Complex.conj_I, conj_half_ofReal, map_neg]
    ring
  rw [hstep, Complex.conj_conj]
  linear_combination -hρ

/-- **The Weil hermitian form of `g_n` is the paired Li coefficient.**  Term by term,
`ĝ_n(-γ) (ĝ_n)^♯(-γ) = (1 - w_ρⁿ)(1 - w_ρ⁻ⁿ) = 2 - w_ρⁿ - w_ρ⁻ⁿ`. -/
theorem suzukiEntireFourier_liTestFun_term (n : ℕ) (ρ : XiDivisorSupport) :
    suzukiEntireFourier (suzukiLiTestFun n) (-(xiSpectralPointSupport ρ))
        * (starRingEnd ℂ) (suzukiEntireFourier (suzukiLiTestFun n)
            ((starRingEnd ℂ) (-(xiSpectralPointSupport ρ))))
      = liTerm (xiRootW ((ρ : XiDivisorSupport) : ℂ)) n := by
  obtain ⟨hlo, hhi⟩ := abs_im_xiSpectralPointSupport_lt ρ
  have him : (ρ : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero ρ
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have h1 : (ρ : ℂ) ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
  -- the first factor
  have hz1 : -(1 / 2 : ℝ) < (-(xiSpectralPointSupport ρ)).im := by
    rw [Complex.neg_im]
    linarith
  have hfirst : suzukiEntireFourier (suzukiLiTestFun n) (-(xiSpectralPointSupport ρ))
      = 1 - xiRootW ((ρ : XiDivisorSupport) : ℂ) ^ n := by
    rw [suzukiEntireFourier_liTestFun n hz1, half_sub_I_mul_neg_spectral ρ, xiRootW]
  -- the second factor
  have hz2 : -(1 / 2 : ℝ) < ((starRingEnd ℂ) (-(xiSpectralPointSupport ρ))).im := by
    rw [Complex.conj_im, Complex.neg_im, neg_neg]
    linarith
  have hsecond : (starRingEnd ℂ) (suzukiEntireFourier (suzukiLiTestFun n)
        ((starRingEnd ℂ) (-(xiSpectralPointSupport ρ))))
      = 1 - (xiRootW ((ρ : XiDivisorSupport) : ℂ))⁻¹ ^ n := by
    rw [suzukiEntireFourier_liTestFun n hz2]
    rw [map_sub, map_one, map_pow, map_sub, map_one, map_div₀, map_one,
      conj_half_sub_I_mul_conj_neg_spectral ρ]
    rw [← xiRootW_one_sub h0 h1, xiRootW]
  have hwne : xiRootW ((ρ : XiDivisorSupport) : ℂ) ≠ 0 := xiRootW_ne_zero h0 h1
  have hcancel : xiRootW ((ρ : XiDivisorSupport) : ℂ) ^ n
      * (xiRootW ((ρ : XiDivisorSupport) : ℂ))⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hwne, one_pow]
  rw [hfirst, hsecond, liTerm]
  linear_combination hcancel


/-! ## Corollary 4.6 -/

theorem summable_liTerm_xiZeroCopy (n : ℕ) :
    Summable fun q : XiZeroCopy => liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) n := by
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  have hmult : ∀ ρ : XiDivisorSupport,
      (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    intro ρ
    exact_mod_cast xi_divisor_pos_on_support ρ
  -- the inverse-square weight is summable over the copies
  have hgnn : ∀ ρ : XiDivisorSupport, (0 : ℝ) ≤ 1 / ‖(ρ : ℂ)‖ ^ 2 := fun ρ => by positivity
  have houter : Summable fun ρ : XiDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2) := by
    refine xi_zero_multiplicity_inv_sq_summable.congr fun ρ => ?_
    rw [mul_one_div]
  have hfibR : ∀ ρ : XiDivisorSupport,
      HasSum (fun _ : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
        1 / ‖(ρ : ℂ)‖ ^ 2)
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by
    intro ρ
    have hb := hasSum_fintype
      (fun _ : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
        1 / ‖(ρ : ℂ)‖ ^ 2)
    have hcast : ((Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) : ℕ) : ℝ)
        = ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      have hpos := (xi_divisor_pos_on_support ρ).le
      exact_mod_cast Int.toNat_of_nonneg hpos
    simpa [Finset.sum_const, nsmul_eq_mul, hcast] using hb
  have hcopy : Summable fun q : XiZeroCopy => 1 / ‖((q.1 : XiDivisorSupport) : ℂ)‖ ^ 2 := by
    rw [summable_sigma_of_nonneg (fun q => hgnn q.1)]
    exact ⟨fun ρ => (hfibR ρ).summable,
      houter.congr fun ρ => ((hfibR ρ).tsum_eq).symm⟩
  refine Summable.of_norm_bounded (hcopy.mul_left ((n : ℝ) ^ 2 * M ^ n)) fun q => ?_
  set ρ : XiDivisorSupport := q.1 with hρ
  have him : (ρ : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero ρ
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have h1 : (ρ : ℂ) ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
  have hwne : xiRootW ((ρ : XiDivisorSupport) : ℂ) ≠ 0 := xiRootW_ne_zero h0 h1
  have hbase := norm_liTerm_le hwne n
  rw [norm_xiRootW_sub_one] at hbase
  have hMn : max ‖xiRootW ((ρ : XiDivisorSupport) : ℂ)‖
      ‖xiRootW ((ρ : XiDivisorSupport) : ℂ)‖⁻¹ ^ n ≤ M ^ n :=
    pow_le_pow_left₀ (le_trans (norm_nonneg _) (le_max_left _ _)) (hMb ρ) n
  have hsq : (1 / ‖(ρ : ℂ)‖) ^ 2 = 1 / ‖(ρ : ℂ)‖ ^ 2 := by rw [div_pow, one_pow]
  refine le_trans hbase ?_
  rw [hsq]
  have hnn : (0 : ℝ) ≤ 1 / ‖(ρ : ℂ)‖ ^ 2 := hgnn ρ
  have hnn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  rw [mul_assoc, mul_assoc]
  gcongr

theorem hasSum_liTerm_xiZeroCopy (n : ℕ) :
    HasSum (fun q : XiZeroCopy => liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) n)
      (xiLiPaired n) := by
  have hsum := summable_liTerm_xiZeroCopy n
  have hfib : ∀ ρ : XiDivisorSupport,
      HasSum (fun _ : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
        liTerm (xiRootW ((ρ : XiDivisorSupport) : ℂ)) n) (xiLiPairedTerm n ρ) := by
    intro ρ
    have hb := hasSum_fintype
      (fun _ : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
        liTerm (xiRootW ((ρ : XiDivisorSupport) : ℂ)) n)
    have hcast : ((Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) : ℕ) : ℂ)
        = (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) := by
      have hpos := (xi_divisor_pos_on_support ρ).le
      exact_mod_cast Int.toNat_of_nonneg hpos
    simpa [xiLiPairedTerm, Finset.sum_const, nsmul_eq_mul, hcast] using hb
  have h2 := hsum.hasSum.sigma hfib
  have huniq := h2.unique (summable_xiLiPairedTerm n).hasSum
  rw [xiLiPaired, ← huniq]
  exact hsum.hasSum

/-- **The Weil hermitian form of the Bombieri--Lagarias test function**, written exactly as
Suzuki (1.2): `⟨g_n, g_n⟩_W = Σ_γ m_γ ĝ_n(-γ) (ĝ_n)^♯(-γ)`. -/
def suzukiLiWeilForm (n : ℕ) : ℂ :=
  ∑' q : XiZeroCopy,
    suzukiEntireFourier (suzukiLiTestFun n) (-xiSpectralPoint q)
      * (starRingEnd ℂ) (suzukiEntireFourier (suzukiLiTestFun n)
          ((starRingEnd ℂ) (-xiSpectralPoint q)))

/-- **`⟨g_n,g_n⟩_W = 2λ_n`** — the identification behind [BoLa99, §4]. -/
theorem suzukiLiWeilForm_eq_xiLiPaired (n : ℕ) : suzukiLiWeilForm n = xiLiPaired n := by
  rw [suzukiLiWeilForm]
  have hterm : ∀ q : XiZeroCopy,
      suzukiEntireFourier (suzukiLiTestFun n) (-xiSpectralPoint q)
        * (starRingEnd ℂ) (suzukiEntireFourier (suzukiLiTestFun n)
            ((starRingEnd ℂ) (-xiSpectralPoint q)))
      = liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) n := by
    intro q
    rw [xiSpectralPoint_eq_support]
    exact suzukiEntireFourier_liTestFun_term n q.1
  rw [tsum_congr hterm]
  exact (hasSum_liTerm_xiZeroCopy n).tsum_eq

/-- **Suzuki, Corollary 4.6.**  If the Weil hermitian form of every Bombieri--Lagarias test
function `g_n` is a nonnegative real — in particular if it equals `‖g_n‖₀²`, which is Suzuki's
equality (4.11) — then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_forall_re_suzukiLiWeilForm_nonneg
    (h : ∀ n : ℕ, 0 ≤ (suzukiLiWeilForm n).re) : RiemannHypothesis := by
  refine riemannHypothesis_of_forall_re_xiLiPaired_nonneg fun n => ?_
  rw [← suzukiLiWeilForm_eq_xiLiPaired n]
  exact h n

/-- **Suzuki, Corollary 4.6, in the source's form.**  `‖g_n‖₀²` is by definition a nonnegative
real, so the equality `‖g_n‖₀² = ⟨g_n,g_n⟩_W` for every `n` forces RH. -/
theorem riemannHypothesis_of_forall_norm_sq_eq_suzukiLiWeilForm {N : ℕ → ℝ}
    (hN : ∀ n, 0 ≤ N n) (h : ∀ n : ℕ, ((N n : ℝ) : ℂ) = suzukiLiWeilForm n) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_re_suzukiLiWeilForm_nonneg fun n => ?_
  rw [← h n, Complex.ofReal_re]
  exact hN n

/-- Conversely, RH makes every `⟨g_n,g_n⟩_W` a nonnegative real. -/
theorem re_suzukiLiWeilForm_nonneg_of_rh (hRH : RiemannHypothesis) (n : ℕ) :
    0 ≤ (suzukiLiWeilForm n).re := by
  rw [suzukiLiWeilForm_eq_xiLiPaired n]
  exact re_xiLiPaired_nonneg_of_rh hRH n

end RHTower
