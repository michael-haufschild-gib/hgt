import GaloisForLFunctions.RHTower.MobiusHalfSelectionEulerProduct
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Holomorphic prime-square correction across the zeta pole

The exact half-selection Euler correction extends holomorphically to `Re s > 1/2`.
On every smaller half-plane its factor differences have a uniform summable
prime-square majorant. Locally uniform product limits retain holomorphy.
At one, each factor is the real number `1+1/(4p(p-1))`; finite products are
at least one, and so is the real part of their limit. Its imaginary part is zero.
This proves the nonvanishing factor needed by the PE5 holomorphic-square obstruction.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem prime_kernel_le (p : Nat.Primes) {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) :
    ‖((p:ℕ):ℂ)^(-s)‖ ≤ ((p:ℕ):ℝ)^(-σ) := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos,Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (neg_le_neg hs)

private theorem prime_kernel_le_two (p : Nat.Primes) {σ : ℝ} (hσ : 0<σ) {s : ℂ}
    (hs : σ ≤ s.re) : ‖((p:ℕ):ℂ)^(-s)‖ ≤ (2:ℝ)^(-σ) :=
  (prime_kernel_le p hs).trans (Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast p.2.two_le) (neg_nonpos.mpr hσ.le))

/-- Uniform prime-square majorant on each positive closed half-plane. -/
theorem norm_halfSelectionEulerCorrectionLocal_sub_one_le (p : Nat.Primes)
    {σ : ℝ} (hσ : 0<σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖halfSelectionEulerCorrectionLocal p s-1‖ ≤
      (1/(4*(1-(2:ℝ)^(-σ)))) * ((p:ℕ):ℝ)^(-(2*σ)) := by
  have hq : (2:ℝ)^(-σ)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hσ)
  have hd : 0 < 4*(1-(2:ℝ)^(-σ)) := by linarith
  have hnorm := norm_sub_norm_le (1:ℂ) (((p:ℕ):ℂ)^(-s))
  rw [norm_one] at hnorm
  have hden : 4*(1-(2:ℝ)^(-σ)) ≤ 4*‖1-((p:ℕ):ℂ)^(-s)‖ := by
    linarith [prime_kernel_le_two p hσ hs]
  have hnum : ‖((p:ℕ):ℂ)^(-s)‖^2 ≤ (((p:ℕ):ℝ)^(-σ))^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (prime_kernel_le p hs) 2
  have hp2 : (((p:ℕ):ℝ)^(-σ))^2 = ((p:ℕ):ℝ)^(-(2*σ)) := by
    rw [← Real.rpow_natCast (((p:ℕ):ℝ)^(-σ)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg (p:ℕ))]
    congr 1
    norm_num
    ring
  unfold halfSelectionEulerCorrectionLocal
  rw [add_sub_cancel_left,norm_div,norm_pow,norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (((p:ℕ):ℝ)^(-σ))^2/(4*‖1-((p:ℕ):ℂ)^(-s)‖) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (((p:ℕ):ℝ)^(-σ))^2/(4*(1-(2:ℝ)^(-σ))) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hd hden
    _ = _ := by rw [hp2]; ring

/-- Each literal local correction is holomorphic where the real part is positive. -/
theorem differentiableOn_halfSelectionEulerCorrectionLocal (p : Nat.Primes) :
    DifferentiableOn ℂ (halfSelectionEulerCorrectionLocal p) {s : ℂ | 0<s.re} := by
  intro s hs
  have hp0 : ((p:ℕ):ℂ)≠0 := by exact_mod_cast p.2.ne_zero
  have hx : DifferentiableAt ℂ (fun s : ℂ => ((p:ℕ):ℂ)^(-s)) s :=
    DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hp0)
  have hd : 1-((p:ℕ):ℂ)^(-s)≠0 := by
    intro h
    have he := sub_eq_zero.mp h
    have hn := norm_halfSelection_prime_cpow_neg_lt_one p hs
    rw [← he] at hn
    norm_num at hn
  have h1 : DifferentiableAt ℂ (fun _ : ℂ => (1:ℂ)) s := differentiableAt_const _
  have h4 : DifferentiableAt ℂ (fun _ : ℂ => (4:ℂ)) s := differentiableAt_const _
  exact (h1.add ((hx.pow 2).div (h4.mul (h1.sub hx))
      (mul_ne_zero (by norm_num) hd))).differentiableWithinAt

private theorem summable_prime_correction_majorant {σ : ℝ} (hσ : 1/2<σ) :
    Summable (fun p : Nat.Primes =>
      (1/(4*(1-(2:ℝ)^(-σ)))) * ((p:ℕ):ℝ)^(-(2*σ))) := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-(2*σ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (hs.comp_injective Nat.Primes.coe_nat_injective).mul_left _

/-- The exact correction product converges locally uniformly on every smaller strict half-plane. -/
theorem hasProdLocallyUniformlyOn_halfSelectionEulerCorrection {σ : ℝ} (hσ : 1/2<σ) :
    HasProdLocallyUniformlyOn (fun p => halfSelectionEulerCorrectionLocal p)
      halfSelectionEulerCorrection {s : ℂ | σ<s.re} := by
  have hopen : IsOpen {s : ℂ | σ<s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hσ0 : 0<σ := by linarith
  have hbound : ∀ᶠ p : Nat.Primes in cofinite, ∀ s ∈ {s : ℂ | σ<s.re},
      ‖halfSelectionEulerCorrectionLocal p s-1‖ ≤
        (1/(4*(1-(2:ℝ)^(-σ)))) * ((p:ℕ):ℝ)^(-(2*σ)) := by
    filter_upwards with p s hs
    exact norm_halfSelectionEulerCorrectionLocal_sub_one_le p hσ0 (le_of_lt hs)
  have hcont (p : Nat.Primes) :
      ContinuousOn (fun s => halfSelectionEulerCorrectionLocal p s-1) {s : ℂ | σ<s.re} := by
    apply ContinuousOn.sub _ continuousOn_const
    apply (differentiableOn_halfSelectionEulerCorrectionLocal p).continuousOn.mono
    intro s hs
    exact lt_trans hσ0 hs
  have hm := Summable.hasProdLocallyUniformlyOn_one_add hopen
    (summable_prime_correction_majorant hσ) hbound hcont
  have he : (fun (p : Nat.Primes) (s : ℂ) => 1+(halfSelectionEulerCorrectionLocal p s-1)) =
      (fun p s => halfSelectionEulerCorrectionLocal p s) := by funext p s; ring
  rw [he] at hm
  refine hm.congr_right ?_
  intro s hs
  unfold halfSelectionEulerCorrection
  apply tprod_congr
  intro p
  ring

/-- The correction product is holomorphic throughout `Re s > 1/2`. -/
theorem differentiableOn_halfSelectionEulerCorrection :
    DifferentiableOn ℂ halfSelectionEulerCorrection {s : ℂ | (1/2:ℝ)<s.re} := by
  intro s hs
  change (1/2:ℝ)<s.re at hs
  let σ : ℝ := ((1/2:ℝ)+s.re)/2
  have hσ : (1/2:ℝ)<σ := by dsimp [σ]; linarith
  have hσs : σ<s.re := by dsimp [σ]; linarith
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_halfSelectionEulerCorrection hσ)
  have hd : ∀ᶠ P : Finset Nat.Primes in atTop, DifferentiableOn ℂ
      (fun z : ℂ => ∏ p ∈ P, halfSelectionEulerCorrectionLocal p z) {s : ℂ | σ<s.re} := by
    filter_upwards with P
    refine DifferentiableOn.fun_finsetProd fun p hp => ?_
    apply (differentiableOn_halfSelectionEulerCorrectionLocal p).mono
    intro z hz
    change σ<z.re at hz
    dsimp [σ] at hz
    change 0<z.re
    linarith
  have hdiff := ht.differentiableOn hd (isOpen_lt continuous_const Complex.continuous_re)
  exact (hdiff.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσs)).differentiableWithinAt

/-- Analytic germs of the correction product throughout the strict half-plane. -/
theorem analyticOnNhd_halfSelectionEulerCorrection :
    AnalyticOnNhd ℂ halfSelectionEulerCorrection {s : ℂ | (1/2:ℝ)<s.re} :=
  differentiableOn_halfSelectionEulerCorrection.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Exact real local factor at one. -/
theorem halfSelectionEulerCorrectionLocal_one (p : Nat.Primes) :
    halfSelectionEulerCorrectionLocal p 1 =
      ((1+1/(4*((p:ℕ):ℝ)*(((p:ℕ):ℝ)-1)) : ℝ) : ℂ) := by
  have hp0 : ((p:ℕ):ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp1 : ((p:ℕ):ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (show (p:ℕ) ≠ 1 from p.2.ne_one))
  unfold halfSelectionEulerCorrectionLocal
  rw [Complex.cpow_neg_one]
  push_cast
  have hid : 1-((p:ℕ):ℂ)⁻¹ = (((p:ℕ):ℂ)-1)/((p:ℕ):ℂ) := by
    field_simp
  rw [hid]
  field_simp

private theorem halfSelectionCorrection_one_limit :
    Tendsto (fun P : Finset Nat.Primes => ∏ p ∈ P, halfSelectionEulerCorrectionLocal p 1)
      atTop (𝓝 (halfSelectionEulerCorrection 1)) :=
  (hasProdLocallyUniformlyOn_halfSelectionEulerCorrection (σ := 3/4) (by norm_num)).hasProd
    (by norm_num)

private theorem halfSelectionCorrection_finite_one_re (P : Finset Nat.Primes) :
    1 ≤ (∏ p ∈ P, halfSelectionEulerCorrectionLocal p 1).re := by
  simp_rw [halfSelectionEulerCorrectionLocal_one]
  rw [← Complex.ofReal_prod,Complex.ofReal_re]
  apply one_le_prod
  intro p hp
  have hpR : (1:ℝ)<(p:ℕ) := by exact_mod_cast p.2.one_lt
  have hd : 0<4*((p:ℕ):ℝ)*(((p:ℕ):ℝ)-1) := by positivity
  have hh : 0≤1/(4*((p:ℕ):ℝ)*(((p:ℕ):ℝ)-1)) := le_of_lt (one_div_pos.mpr hd)
  linarith

/-- The infinite correction retains the finite products' lower bound of one. -/
theorem one_le_halfSelectionEulerCorrection_one_re :
    1 ≤ (halfSelectionEulerCorrection 1).re := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp halfSelectionCorrection_one_limit
  exact ge_of_tendsto ht (Eventually.of_forall halfSelectionCorrection_finite_one_re)

/-- The correction at one is real. -/
theorem halfSelectionEulerCorrection_one_im : (halfSelectionEulerCorrection 1).im = 0 := by
  have ht := Complex.continuous_im.continuousAt.tendsto.comp halfSelectionCorrection_one_limit
  have hz : Tendsto (fun P : Finset Nat.Primes =>
      (∏ p ∈ P, halfSelectionEulerCorrectionLocal p 1).im) atTop (𝓝 0) := by
    have he (P : Finset Nat.Primes) : (∏ p ∈ P, halfSelectionEulerCorrectionLocal p 1).im=0 := by
      simp_rw [halfSelectionEulerCorrectionLocal_one]
      rw [← Complex.ofReal_prod,Complex.ofReal_im]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : Finset Nat.Primes => (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hz

/-- The actual correction factor is nonzero at one. -/
theorem halfSelectionEulerCorrection_one_ne_zero : halfSelectionEulerCorrection 1 ≠ 0 := by
  intro h
  have hp := one_le_halfSelectionEulerCorrection_one_re
  rw [h] at hp
  norm_num at hp

end RHTower
