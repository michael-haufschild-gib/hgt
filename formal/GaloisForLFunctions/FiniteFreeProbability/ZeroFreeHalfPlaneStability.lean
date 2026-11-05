import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeHalfPlaneCriterion
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment
import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn

/-!
# Zero-free half-planes make the shifted Jensen polynomials weakly stable

Let `σ ≥ 1/2`, `δ = σ − 1/2`, and expand `ξ` on the line `Re s = σ`: `G_σ(w) = ξ(σ + iw) = Ξ(w − iδ)`.
The Hadamard product `Ξ(z) = Ξ(0) Π_q E₁(z/a_q)` (genus one, over the zeros `a_q` of `Ξ` with
multiplicity) gives, for every finite set `F` of zeros,

`Π_{q∈F} E₁((w − iδ)/a_q) = c_F · Π_{q∈F} (1 − w/(a_q + iδ)) · e^{w Σ_F 1/a_q}`.

If `ξ` has no zero with `Re ρ > σ`, then `Im a_q ≥ −δ`, so each linear piece has its reversed
Jensen root `d/(a_q + iδ)` in `Im ≤ 0`; Walsh keeps the finite free product there and the
exponential translates by `−Σ_F 1/a_q`, whose imaginary part `τ_F = Σ_F Im a_q/|a_q|²` tends to
`0` (the zeros are symmetric under conjugation). The Taylor coefficients of the partial products
converge to those of `G_σ`, and a closed-set Hurwitz argument places every root of
`R_d(G_σ)` in `Im ≤ 0`.

**Theorem.** For `σ ≥ 1/2`: `ξ` has no zero with `Re ρ > σ` iff every root of every `R_d(G_σ)` has
`Im ≤ 0`, iff some bound `Im ≤ K` holds along infinitely many degrees. For `σ ≥ 1` this holds
unconditionally.
-/

open Polynomial Filter Topology Complex Metric
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-! ## Taylor series of entire functions -/

/-- The Taylor series at `0` of a function `ℂ → ℂ`. -/
def taylorPS (h : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => iteratedDeriv k h 0 / (k.factorial : ℂ)

theorem taylorPS_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    taylorPS (f * g) = taylorPS f * taylorPS g := by
  ext k
  simp only [taylorPS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [iteratedDeriv_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hc : (k.choose i : ℂ) * (i.factorial : ℂ) * ((k - i).factorial : ℂ) = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
  have h1 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2 : ((k - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h3 : (k.choose i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hik).ne'
  rw [← hc]
  field_simp

theorem taylorPS_one : taylorPS (fun _ => 1) = 1 := by
  ext k
  rcases k with _ | k
  · simp [taylorPS]
  · simp [taylorPS, iteratedDeriv_const, PowerSeries.coeff_one]

theorem taylorPS_prod {ι : Type*} [DecidableEq ι] (F : Finset ι) (h : ι → ℂ → ℂ)
    (hd : ∀ i, Differentiable ℂ (h i)) :
    taylorPS (fun w => ∏ i ∈ F, h i w) = ∏ i ∈ F, taylorPS (h i) := by
  induction F using Finset.induction_on with
  | empty => simpa using taylorPS_one
  | insert a F ha ih =>
    rw [Finset.prod_insert ha, ← ih]
    have hfun : (fun w => ∏ i ∈ insert a F, h i w) = h a * fun w => ∏ i ∈ F, h i w := by
      funext w; simp [Finset.prod_insert ha]
    rw [hfun]
    exact taylorPS_mul (hd a) (by fun_prop)

theorem iteratedDeriv_eval_polynomial (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun w => p.eval w) = fun w => (derivative^[n] p).eval w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    rw [Polynomial.deriv, Function.iterate_succ_apply']

theorem taylorPS_polynomial (p : ℂ[X]) : taylorPS (fun w => p.eval w) = (p : PowerSeries ℂ) := by
  ext k
  simp only [taylorPS, PowerSeries.coeff_mk, Polynomial.coeff_coe, iteratedDeriv_eval_polynomial]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]
  have : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp

theorem taylorPS_exp (c : ℂ) : taylorPS (fun w => Complex.exp (c * w)) = expSeries c := by
  ext k
  rw [taylorPS, expSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, iteratedDeriv_cexp_const_mul]
  simp

/-! ## The shifted genus-one factors -/

/-- The polynomial part `E₁(−iδ/a)·(1 − w/(a + iδ))` of the shifted factor `E₁((w − iδ)/a)`. -/
def shiftedFactorPoly (δ : ℝ) (a : ℂ) : ℂ[X] :=
  C (weierstrassE1 (-(I * δ) / a)) * (1 - C (1 / (a + I * δ)) * X)

theorem weierstrassE1_shift (δ : ℝ) {a : ℂ} (ha : a ≠ 0) (hb : a + I * δ ≠ 0) (w : ℂ) :
    weierstrassE1 ((w - I * δ) / a) =
      (shiftedFactorPoly δ a).eval w * Complex.exp ((1 / a) * w) := by
  simp only [shiftedFactorPoly, weierstrassE1, eval_mul, eval_C, eval_sub, eval_one, eval_X]
  rw [show (w - I * δ) / a = (1 / a) * w + (-(I * δ) / a) by field_simp; ring, Complex.exp_add]
  field_simp
  ring

theorem taylorPS_shiftedFactor (δ : ℝ) {a : ℂ} (ha : a ≠ 0) (hb : a + I * δ ≠ 0) :
    taylorPS (fun w => weierstrassE1 ((w - I * δ) / a)) =
      (shiftedFactorPoly δ a : PowerSeries ℂ) * expSeries (1 / a) := by
  rw [show (fun w => weierstrassE1 ((w - I * δ) / a)) =
      (fun w => (shiftedFactorPoly δ a).eval w) * (fun w => Complex.exp ((1 / a) * w)) from
    funext (weierstrassE1_shift δ ha hb),
    taylorPS_mul (Polynomial.differentiable _) (by fun_prop), taylorPS_polynomial, taylorPS_exp]

/-! ## Walsh bound for finite products of linear pieces -/

theorem eval_jensenRev_linear (β : ℂ) (m : ℕ) (x : ℂ) :
    (jensenRev (m + 1) ((1 - C β * X : ℂ[X]) : PowerSeries ℂ)).eval x =
      x ^ m * (x - β * (m + 1)) := by
  rw [jensenRev_eq_sum, eval_finsetSum, Finset.sum_range_succ', Finset.sum_range_succ']
  rw [Finset.sum_eq_zero fun i _ => by simp]
  simp
  ring

theorem im_le_zero_of_isRoot_jensenRev_linear {β : ℂ} (hβ : β.im ≤ 0) {d : ℕ} (hd : 1 ≤ d)
    {x : ℂ} (hx : (jensenRev d ((1 - C β * X : ℂ[X]) : PowerSeries ℂ)).IsRoot x) : x.im ≤ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [IsRoot, eval_jensenRev_linear] at hx
  rcases mul_eq_zero.1 hx with h | h
  · rw [pow_eq_zero_iff'] at h; rw [h.1]; simp
  · rw [sub_eq_zero.1 h]
    simp only [mul_im, add_im, natCast_im, one_im, add_zero, add_re, natCast_re, one_re]
    nlinarith [hβ]

theorem constantCoeff_coe_prod_linear {ι : Type*} (F : Finset ι) (β : ι → ℂ) :
    PowerSeries.constantCoeff ((∏ i ∈ F, (1 - C (β i) * X) : ℂ[X]) : PowerSeries ℂ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_eq_eval_zero, eval_prod]
  simp

theorem im_le_zero_of_isRoot_jensenRev_prod_linear {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (β : ι → ℂ) (hβ : ∀ i ∈ F, (β i).im ≤ 0) {d : ℕ} (hd : 1 ≤ d) {x : ℂ}
    (hx : (jensenRev d ((∏ i ∈ F, (1 - C (β i) * X) : ℂ[X]) : PowerSeries ℂ)).IsRoot x) :
    x.im ≤ 0 := by
  induction F using Finset.induction_on generalizing x with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coe_one] at hx
    have h1 : jensenRev d (1 : PowerSeries ℂ) = X ^ d := by
      have e : (1 : PowerSeries ℂ) = PowerSeries.mk fun k => (0 : ℂ) ^ k / (k.factorial : ℂ) := by
        ext k; rcases k with _ | k <;> simp [PowerSeries.coeff_one]
      rw [e, jensenRev_exp]; simp
    rw [h1, IsRoot, eval_pow, eval_X, pow_eq_zero_iff (by omega)] at hx
    rw [hx]; simp
  | insert a F ha ih =>
    rw [Finset.prod_insert ha, Polynomial.coe_mul, jensenRev_mul] at hx
    have hc1 : PowerSeries.constantCoeff ((1 - C (β a) * X : ℂ[X]) : PowerSeries ℂ) ≠ 0 := by
      simp
    have hc2 := constantCoeff_coe_prod_linear F β
    have := ffConv_root_im_le (jensenRev_ne_zero hc1) (natDegree_jensenRev hc1)
      (jensenRev_ne_zero (by rw [hc2]; exact one_ne_zero)) (natDegree_jensenRev_le _ _)
      (a := 0) (b := 0)
      (fun r hr => im_le_zero_of_isRoot_jensenRev_linear (hβ a (Finset.mem_insert_self a F)) hd hr)
      (fun μ hμ => ih (fun i hi => hβ i (Finset.mem_insert_of_mem hi)) hμ) hx
    linarith

/-! ## Partial products of the shifted canonical product -/

/-- The partial product `Π_{q∈F} E₁((w − iδ)/a_q)` over finitely many zeros of `Ξ`. -/
def shiftedPartialProduct (δ : ℝ) (F : Finset XiZeroCopy) (w : ℂ) : ℂ :=
  ∏ q ∈ F, weierstrassE1 ((w - I * δ) / xiSpectralPoint q)

theorem xiSpectralPoint_add_ne {δ : ℝ} (q : XiZeroCopy) : xiSpectralPoint q + I * δ ≠ 0 := by
  intro h
  have hz := XiC_xiSpectralPoint_eq_zero q
  rw [show xiSpectralPoint q = -(I * δ) by linear_combination h, XiC,
    show (1 / 2 : ℂ) + -(I * δ) * I = (((1 / 2 + δ : ℝ)) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring]
    at hz
  exact xi_ne_zero_of_real _ hz

theorem differentiable_shiftedPartialProduct (δ : ℝ) (F : Finset XiZeroCopy) :
    Differentiable ℂ (shiftedPartialProduct δ F) := by
  unfold shiftedPartialProduct weierstrassE1; fun_prop

theorem taylorPS_shiftedPartialProduct (δ : ℝ) (F : Finset XiZeroCopy) :
    taylorPS (shiftedPartialProduct δ F) =
      ((∏ q ∈ F, shiftedFactorPoly δ (xiSpectralPoint q) : ℂ[X]) : PowerSeries ℂ) *
        expSeries (∑ q ∈ F, 1 / xiSpectralPoint q) := by
  classical
  rw [show shiftedPartialProduct δ F = fun w => ∏ q ∈ F, weierstrassE1 ((w - I * δ) /
      xiSpectralPoint q) from rfl,
    taylorPS_prod F (fun q w => weierstrassE1 ((w - I * δ) / xiSpectralPoint q))
      (fun q => by unfold weierstrassE1; fun_prop),
    Finset.prod_congr rfl fun q _ => taylorPS_shiftedFactor δ (xiSpectralPoint_ne_zero q)
      (xiSpectralPoint_add_ne q),
    Finset.prod_mul_distrib, prod_expSeries]
  congr 1
  simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]

theorem weierstrassE1_ne_zero_of_ne_one {z : ℂ} (hz : z ≠ 1) : weierstrassE1 z ≠ 0 :=
  mul_ne_zero (sub_ne_zero.2 (Ne.symm hz)) (Complex.exp_ne_zero _)

/-- **Walsh for the partial products.** If every zero has `Im a_q ≥ −δ`, the reversed Jensen
roots of the partial product satisfy `Im x ≤ −Im Σ_F 1/a_q`. -/
theorem im_le_of_isRoot_jensenRev_shiftedPartialProduct {δ : ℝ}
    (hzf : ∀ q : XiZeroCopy, -δ ≤ (xiSpectralPoint q).im) (F : Finset XiZeroCopy) {d : ℕ}
    (hd : 1 ≤ d) {x : ℂ}
    (hx : (jensenRev d (taylorPS (shiftedPartialProduct δ F))).IsRoot x) :
    x.im ≤ -(∑ q ∈ F, 1 / xiSpectralPoint q).im := by
  classical
  rw [taylorPS_shiftedPartialProduct, mul_comm, jensenRev_expSeries_mul] at hx
  have hroot : (jensenRev d ((∏ q ∈ F, shiftedFactorPoly δ (xiSpectralPoint q) : ℂ[X]) :
      PowerSeries ℂ)).IsRoot (x + ∑ q ∈ F, 1 / xiSpectralPoint q) := by
    rw [IsRoot, eval_comp, eval_add, eval_X, eval_C] at hx
    exact hx
  have hpoly : ∏ q ∈ F, shiftedFactorPoly δ (xiSpectralPoint q) =
      C (∏ q ∈ F, weierstrassE1 (-(I * δ) / xiSpectralPoint q)) *
        ∏ q ∈ F, (1 - C (1 / (xiSpectralPoint q + I * δ)) * X) := by
    simp only [shiftedFactorPoly, Finset.prod_mul_distrib, map_prod]
  rw [hpoly, Polynomial.coe_mul, Polynomial.coe_C, jensenRev_C_mul, IsRoot, eval_mul,
    eval_C] at hroot
  have hc : ∏ q ∈ F, weierstrassE1 (-(I * δ) / xiSpectralPoint q) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => weierstrassE1_ne_zero_of_ne_one fun h => by
      have := xiSpectralPoint_add_ne (δ := δ) q
      apply this
      have ha := xiSpectralPoint_ne_zero q
      field_simp at h
      linear_combination -h
  have hr := im_le_zero_of_isRoot_jensenRev_prod_linear F
    (fun q => 1 / (xiSpectralPoint q + I * δ)) (fun q _ => by
      rw [one_div, Complex.inv_im]
      have him : 0 ≤ (xiSpectralPoint q + I * δ).im := by
        simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
        linarith [hzf q]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 him) (Complex.normSq_nonneg _))
    hd ((mul_eq_zero.1 hroot).resolve_left hc)
  rw [add_im] at hr
  linarith

/-! ## The drift vanishes -/

theorem summable_im_inv_xiSpectralPoint :
    Summable fun q : XiZeroCopy => (1 / xiSpectralPoint q).im := by
  refine Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left (1 / 2)) fun q => ?_
  have ha := xiSpectralPoint_ne_zero q
  have hb := xiSpectralPoint_im_mem_openHalf q
  have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := pow_pos (norm_pos_iff.2 ha) 2
  have habs : |(xiSpectralPoint q).im| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩
  calc ‖(1 / xiSpectralPoint q).im‖ = |(xiSpectralPoint q).im| / ‖xiSpectralPoint q‖ ^ 2 := by
        rw [one_div, Complex.inv_im, Real.norm_eq_abs, abs_div, abs_neg,
          Complex.normSq_eq_norm_sq, abs_of_pos hpos]
    _ ≤ (1 / 2) / ‖xiSpectralPoint q‖ ^ 2 := div_le_div_of_nonneg_right habs hpos.le
    _ = 1 / 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

/-- The zeros of `Ξ` are symmetric under conjugation, so `Σ_q Im(1/a_q) = 0`. -/
theorem tsum_im_inv_xiSpectralPoint : ∑' q : XiZeroCopy, (1 / xiSpectralPoint q).im = 0 := by
  have h := (xiZeroCopyLineConjEquiv).tsum_eq fun q => (1 / xiSpectralPoint q).im
  have hneg : ∀ q, (1 / xiSpectralPoint (xiZeroCopyLineConjEquiv q)).im =
      -(1 / xiSpectralPoint q).im := fun q => by
    rw [xiSpectralPoint_lineConj, one_div, one_div, ← map_inv₀, Complex.conj_im]
  simp only [hneg, tsum_neg] at h
  linarith

/-! ## Passage to the limit -/

theorem xiCanonicalProduct_shift (δ : ℝ) (w : ℂ) :
    xiCanonicalProduct (w - I * δ) = (XiC 0)⁻¹ * xi (((1 / 2 + δ : ℝ) : ℂ) + I * w) := by
  have h := congrFun XiC_eq_constant_mul_canonicalProduct (w - I * δ)
  simp only [Pi.mul_apply] at h
  have h0 : XiC 0 ≠ 0 := XiC_zero_ne
  rw [eq_inv_mul_iff_mul_eq₀ h0, ← h, XiC]
  congr 1
  push_cast; ring_nf; rw [I_sq]; ring

theorem tendstoLocallyUniformlyOn_shiftedPartialProduct (δ : ℝ) :
    TendstoLocallyUniformlyOn (fun F => shiftedPartialProduct δ F)
      (fun w => xiCanonicalProduct (w - I * δ)) atTop Set.univ :=
  xiCanonicalProduct_hasProdLocallyUniformlyOn.comp (fun w : ℂ => w - I * δ)
    (Set.mapsTo_univ _ _) (by fun_prop : Continuous fun w : ℂ => w - I * δ).continuousOn

theorem tendsto_coeff_taylorPS_shiftedPartialProduct (δ : ℝ) (k : ℕ) :
    Tendsto (fun F => PowerSeries.coeff k (taylorPS (shiftedPartialProduct δ F))) atTop
      (𝓝 (xiShiftCoeff (1 / 2 + δ) k / XiC 0)) := by
  have h := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ
    (tendstoLocallyUniformlyOn_shiftedPartialProduct δ)
    (Eventually.of_forall fun F => (differentiable_shiftedPartialProduct δ F).differentiableOn) k
    (Set.mem_univ 0)
  have hfun : (fun w => xiCanonicalProduct (w - I * δ)) =
      fun w => (XiC 0)⁻¹ * xi (((1 / 2 + δ : ℝ) : ℂ) + I * w) :=
    funext (xiCanonicalProduct_shift δ)
  rw [hfun, iteratedDeriv_const_mul_field] at h
  simp only [taylorPS, PowerSeries.coeff_mk, xiShiftCoeff]
  convert h.div_const (k.factorial : ℂ) using 2
  push_cast
  ring

theorem coeff_jensenRev (d : ℕ) (f : PowerSeries ℂ) {j : ℕ} (hj : j ≤ d) :
    (jensenRev d f).coeff j = PowerSeries.coeff (d - j) f * (d.descFactorial (d - j) : ℂ) := by
  rw [jensenRev_eq_sum, finsetSum_coeff, Finset.sum_eq_single (d - j)]
  · rw [coeff_C_mul_X_pow, if_pos (by omega)]
  · intro i hi hij
    rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.1 hi; omega)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem coeff_jensenRev_of_lt (d : ℕ) (f : PowerSeries ℂ) {j : ℕ} (hj : d < j) :
    (jensenRev d f).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_jensenRev_le d f) hj)

/-- **Hurwitz for polynomials of bounded degree.** If the coefficients of `P n` converge to those
of `L ≠ 0` and the roots of `P n` satisfy `Im ≤ τ n → 0`, the roots of `L` satisfy `Im ≤ 0`. -/
theorem im_le_zero_of_tendsto_coeff {P : ℕ → ℂ[X]} {L : ℂ[X]} {d : ℕ}
    (hdeg : ∀ n, (P n).natDegree ≤ d) (hLd : L.natDegree ≤ d) (hL : L ≠ 0)
    (hconv : ∀ j, Tendsto (fun n => (P n).coeff j) atTop (𝓝 (L.coeff j)))
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝 0)) (hroots : ∀ n x, (P n).IsRoot x → x.im ≤ τ n)
    {x : ℂ} (hx : L.IsRoot x) : x.im ≤ 0 := by
  have hconv' : TendstoLocallyUniformly (fun n z => (P n).eval z) (fun z => L.eval z) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    set R := max R₀ 0
    have hKR : ∀ u ∈ K, ‖u‖ ≤ R := fun u hu => by
      have := hR₀ hu; rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    set e : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (d + 1), ‖(P n).coeff j - L.coeff j‖ * R ^ j
    have he : Tendsto e atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range (d + 1)) fun j (_ : j ∈ Finset.range (d + 1)) =>
        (((hconv j).sub (tendsto_const_nhds (x := L.coeff j))).norm).mul_const (R ^ j)
      simpa using this
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn u hu
    rw [dist_eq_norm, eval_eq_sum_range' (n := d + 1) (by omega),
      eval_eq_sum_range' (n := d + 1) (lt_of_le_of_lt (hdeg n) (by omega)), ← Finset.sum_sub_distrib]
    refine lt_of_le_of_lt ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)) hn
    rw [← sub_mul, norm_mul, norm_sub_rev, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) (hKR u hu) j) (norm_nonneg _)
  obtain ⟨a, ha⟩ : ∃ a, L.eval a ≠ 0 := by
    by_contra h; push Not at h
    exact hL (Polynomial.funext fun a => by rw [h a, eval_zero])
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hmem := RHTower.zero_mem_closed_of_tendstoLocallyUniformly hconv'
    (fun w _ => (Polynomial.differentiable L).analyticAt w)
    (Eventually.of_forall fun n => Polynomial.differentiable _)
    (isClosed_le Complex.continuous_im continuous_const : IsClosed {z : ℂ | z.im ≤ ε})
    ((hτ.eventually (gt_mem_nhds hε)).mono fun n hn w hw => (hroots n w hw).trans hn.le) ha hx
  simpa using hmem

/-- **Zero-free half-planes give weak stability.** If every zero of `Ξ` has `Im a_q ≥ −δ`
(equivalently `ξ ≠ 0` on `Re s > 1/2 + δ`), every root of every `R_d(ξ(1/2 + δ + i·))` has
`Im ≤ 0`. -/
theorem im_le_zero_of_isRoot_jensenRev_xiShift {δ : ℝ}
    (hzf : ∀ q : XiZeroCopy, -δ ≤ (xiSpectralPoint q).im) (d : ℕ) {x : ℂ}
    (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff (1 / 2 + δ)))).IsRoot x) : x.im ≤ 0 := by
  set σ : ℝ := 1 / 2 + δ
  have h0 : XiC 0 ≠ 0 := XiC_zero_ne
  set ℓ : ℕ → ℂ := fun k => xiShiftCoeff σ k / XiC 0
  have hmk : PowerSeries.mk (xiShiftCoeff σ) = PowerSeries.C (XiC 0) * PowerSeries.mk ℓ := by
    ext k; simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ℓ]; field_simp
  set L := jensenRev d (PowerSeries.mk ℓ)
  have hxL : L.IsRoot x := by
    rw [hmk, jensenRev_C_mul, IsRoot, eval_mul, eval_C] at hx
    exact (mul_eq_zero.1 hx).resolve_left h0
  have hℓ0 : ℓ 0 ≠ 0 := div_ne_zero (xiShiftCoeff_zero_ne σ) h0
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    rw [IsRoot, show L = jensenRev 0 (PowerSeries.mk ℓ) from rfl, jensenRev_eq_sum] at hxL
    simp at hxL
    exact hℓ0 hxL
  obtain ⟨Fseq, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset XiZeroCopy))
  have hLne : L ≠ 0 := fun h => by
    have := coeff_jensenRev d (PowerSeries.mk ℓ) (le_refl d)
    rw [← show L = jensenRev d (PowerSeries.mk ℓ) from rfl, h, coeff_zero, Nat.sub_self,
      PowerSeries.coeff_mk, Nat.descFactorial_zero, Nat.cast_one, mul_one] at this
    exact hℓ0 this.symm
  have hsum : HasSum (fun q : XiZeroCopy => (1 / xiSpectralPoint q).im) 0 := by
    have := summable_im_inv_xiSpectralPoint.hasSum
    rwa [tsum_im_inv_xiSpectralPoint] at this
  refine im_le_zero_of_tendsto_coeff (P := fun n => jensenRev d (taylorPS
    (shiftedPartialProduct δ (Fseq n)))) (fun n => natDegree_jensenRev_le _ _)
    (natDegree_jensenRev_le _ _) hLne
    (fun j => ?_) (τ := fun n => -(∑ q ∈ Fseq n, 1 / xiSpectralPoint q).im) ?_
    (fun n y hy => im_le_of_isRoot_jensenRev_shiftedPartialProduct hzf (Fseq n) hd hy) hxL
  · rcases le_or_gt j d with hj | hj
    · simp only [coeff_jensenRev d _ hj, PowerSeries.coeff_mk]
      exact ((tendsto_coeff_taylorPS_shiftedPartialProduct δ (d - j)).comp hF).mul_const _
    · simp only [coeff_jensenRev_of_lt d _ hj]
      exact tendsto_const_nhds
  · have := (hsum.comp hF).neg
    simp only [Function.comp_def, neg_zero] at this
    refine this.congr fun n => ?_
    rw [Complex.im_sum]

/-- **Weak stability on lines to the right of all zeros.** If `ξ` has no zero with `Re ρ > σ`, every
root of every reversed Jensen polynomial of `ξ(σ + i·)` has `Im ≤ 0`. -/
theorem im_le_zero_of_zeroFree {σ : ℝ} (hzf : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ) (d : ℕ) {x : ℂ}
    (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x) : x.im ≤ 0 := by
  refine im_le_zero_of_isRoot_jensenRev_xiShift (δ := σ - 1 / 2) (fun q => ?_) d
    (by rwa [show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring])
  rw [xiSpectralPoint_im]
  have := hzf _ (xi_eq_zero_of_mem_divisor_support q.1)
  linarith

/-- **Unconditional finite free stability at `Re s ≥ 1`.** For `σ ≥ 1`, every root of every reversed
Jensen polynomial of `ξ(σ + i·)` has `Im ≤ 0`. -/
theorem im_le_zero_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) (d : ℕ) {x : ℂ}
    (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x) : x.im ≤ 0 := by
  refine im_le_zero_of_isRoot_jensenRev_xiShift (δ := σ - 1 / 2) (fun q => ?_) d
    (by rwa [show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring])
  linarith [(xiSpectralPoint_im_mem_openHalf q).1]

/-- **The finite free zero-free half-plane theorem.** `ξ` has no zero with `Re ρ > σ` iff every root
of every `R_d(ξ(σ + i·))` has `Im ≤ 0`, iff for some `K` and infinitely many `d` the roots have
`Im ≤ K`. -/
theorem zeroFree_iff_forall_im_le_zero (σ : ℝ) :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ) ↔
      ∀ d : ℕ, ∀ x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x → x.im ≤ 0 :=
  ⟨fun h d _ hx => im_le_zero_of_zeroFree h d hx,
    fun h _ hρ => re_le_of_frequently_im_le (K := 0) (Frequently.of_forall fun d => h d) hρ⟩

theorem zeroFree_iff_exists_frequently_im_le (σ : ℝ) :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ) ↔ ∃ K : ℝ, ∃ᶠ d : ℕ in atTop,
      ∀ x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x → x.im ≤ K :=
  ⟨fun h => ⟨0, Frequently.of_forall fun d _ hx => im_le_zero_of_zeroFree h d hx⟩,
    fun ⟨_, hK⟩ _ hρ => re_le_of_frequently_im_le hK hρ⟩

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.zeroFree_iff_forall_im_le_zero
#print axioms FiniteFreeProbability.im_le_zero_of_one_le
