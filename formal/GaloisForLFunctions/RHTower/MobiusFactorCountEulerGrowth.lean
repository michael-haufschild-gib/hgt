import GaloisForLFunctions.RHTower.MobiusFactorCountPrimeWork
import GaloisForLFunctions.HTGeometry.EulerLogTail
import GaloisForLFunctions.RHTower.ZetaGateProductAFEMainTermInputs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Euler-parameter growth in factor-count interpolation

The complete prime-work lower bound becomes a lower bound for the actual
parameter derivative of the corrected finite Euler product. All affine Euler
factors stay uniformly separated from zero on the moving height interval.
The zeta term and quadratic Euler correction are bounded uniformly in the
prime truncation.

The same factor separation controls the absolute derivative at every lower
parameter. Integer head and tail estimates give an initial-value bound, so
integration proves log-modulus growth of order `D^(4/3) / log D`. At integer
parameters this is the literal finite Euler product, whose norm is at least
`exp (D^(4/3) / (4096 log D))` throughout the stated sector.

No Riemann-hypothesis or cancellation premise is used. The theorem does not
bound the full signed interpolation, its Mellin inversion, or Möbius energy.
Those require retaining the lower interpolation parameters and the pole term.
-/

noncomputable section
namespace RHTower
open Filter Topology

private def primeBase (t : ℝ) (p : ℕ) : ℂ := mobiusFactorCountPrimeArgument 1 t p

private lemma primeArgument_eq (a t : ℝ) (p : ℕ) :
    mobiusFactorCountPrimeArgument a t p = (a : ℂ) * primeBase t p := by
  simp only [primeBase, mobiusFactorCountPrimeArgument, one_mul, Complex.ofReal_mul,
    mul_assoc]

private lemma norm_primeBase (t : ℝ) (p : ℕ) :
    ‖primeBase t p‖ = (p : ℝ) ^ (-(3/4 : ℝ)) := by
  rw [primeBase, mobiusFactorCountPrimeArgument, one_mul, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

private lemma normSq_affine (a : ℝ) (z : ℂ) :
    ‖1 + (a : ℂ) * z‖ ^ 2 = 1 + 2*a*z.re + a^2*‖z‖^2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im,
    zero_add]
  ring

private lemma hasDerivAt_logNorm_affine {a : ℝ} {z : ℂ} (hz : 1 + (a : ℂ)*z ≠ 0) :
    HasDerivAt (fun b : ℝ => Real.log ‖1 + (b : ℂ)*z‖)
      (z / (1 + (a : ℂ)*z)).re a := by
  have he (b : ℝ) : Real.log ‖1 + (b : ℂ)*z‖ =
      Real.log (1 + 2*b*z.re + b^2*‖z‖^2) / 2 := by
    rw [← normSq_affine, Real.log_pow]
    ring
  have hp : HasDerivAt (fun b : ℝ => 1 + 2*b*z.re + b^2*‖z‖^2)
      (2*z.re + 2*a*‖z‖^2) a := by
    convert! ((((hasDerivAt_id a).const_mul 2).mul_const z.re).const_add 1).add
      (((hasDerivAt_id a).pow 2).mul_const (‖z‖^2)) using 1; simp
  have hd : 1 + 2*a*z.re + a^2*‖z‖^2 ≠ 0 := by
    rw [← normSq_affine]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  convert! (hp.log hd).div_const 2 using 1
  · funext b
    exact he b
  · rw [Complex.div_re, ← normSq_affine, ← Complex.normSq_eq_norm_sq]
    have hden : Complex.normSq (1 + (a : ℂ)*z) ≠ 0 :=
      ne_of_gt (Complex.normSq_pos.mpr hz)
    field_simp
    simp only [← Complex.normSq_eq_norm_sq, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im,
      Complex.mul_im, zero_add, Complex.normSq_apply]
    ring

/-- Log modulus of the continuously parameterized corrected finite Euler product at real part three quarters. -/
def mobiusFactorCountLogModulus (N : ℕ) (a t : ℝ) : ℝ :=
  a * Real.log ‖riemannZeta ((3/4 : ℂ) + (t : ℂ)*Complex.I)‖ +
    ∑ p ∈ Nat.primesLE N,
      (Real.log ‖1 + (a : ℂ)*primeBase t p‖ + a * Real.log ‖1-primeBase t p‖)

private def correction (N : ℕ) (t : ℝ) : ℝ :=
  Real.log ‖riemannZeta ((3/4 : ℂ) + (t : ℂ)*Complex.I)‖ +
    ∑ p ∈ Nat.primesLE N, (Real.log ‖1-primeBase t p‖ + (primeBase t p).re)

private lemma hasDerivAt_logModulus {N : ℕ} {a t : ℝ}
    (ha : a ≠ 0) (hnz : ∀ p ∈ Nat.primesLE N, 1 + (a : ℂ)*primeBase t p ≠ 0) :
    HasDerivAt (fun b : ℝ => mobiusFactorCountLogModulus N b t)
      ((∑ p ∈ Nat.primesLE N,
          mobiusFactorCountParameterKernel (mobiusFactorCountPrimeArgument a t p)) / a +
        correction N t) a := by
  have hh := ((hasDerivAt_id a).mul_const
    (Real.log ‖riemannZeta ((3/4 : ℂ)+(t : ℂ)*Complex.I)‖)).add
    (HasDerivAt.fun_sum (fun p hp =>
      (hasDerivAt_logNorm_affine (hnz p hp)).add
        ((hasDerivAt_id a).mul_const (Real.log ‖1-primeBase t p‖))))
  convert! hh using 1
  simp only [one_mul, correction]
  rw [add_left_comm]
  congr 1
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [primeArgument_eq, mobiusFactorCountParameterKernel, Complex.sub_re]
  have hmul : ((a : ℂ)*primeBase t p / (1 + (a : ℂ)*primeBase t p)).re =
      a * (primeBase t p / (1 + (a : ℂ)*primeBase t p)).re := by
    rw [mul_div_assoc, Complex.mul_re]
    simp
  rw [hmul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp
  ring

private lemma correction_tail_bound {z : ℂ} {r : ℝ} (hr : r < 1) (hz : ‖z‖ ≤ r) :
    |Real.log ‖1-z‖ + z.re| ≤ ‖z‖^2 / (2*(1-r)) := by
  have he : Real.log ‖1-z‖ + z.re = -(GaloisForLFunctions.HTGeometry.logTail z).re := by
    simp [GaloisForLFunctions.HTGeometry.logTail, Complex.log_re, add_comm]
  rw [he, abs_neg]
  exact (Complex.abs_re_le_norm _).trans
    ((GaloisForLFunctions.HTGeometry.norm_logTail_le (hz.trans_lt hr)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)))


private lemma finite_correction_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ t : ℝ,
      |∑ p ∈ Nat.primesLE N, (Real.log ‖1-primeBase t p‖ + (primeBase t p).re)| ≤ B := by
  let r : ℝ := 2 ^ (-(3/4 : ℝ))
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(3/2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  let S : ℝ := ∑' n : ℕ, (n : ℝ)^(-(3/2 : ℝ))
  have hS : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  refine ⟨S / (2*(1-r)), by positivity, ?_⟩
  intro N t
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, |Real.log ‖1-primeBase t p‖ + (primeBase t p).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesLE N, (p : ℝ)^(-(3/2 : ℝ)) / (2*(1-r)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      have hn : ‖primeBase t p‖ ≤ r := by
        rw [norm_primeBase]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      have hh := correction_tail_bound hr1 hn
      rw [norm_primeBase, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ p)] at hh
      norm_num at hh
      exact hh
    _ = (∑ p ∈ Nat.primesLE N, (p : ℝ)^(-(3/2 : ℝ))) / (2*(1-r)) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (hs.sum_le_tsum _ (fun n hn => by positivity))
      (by positivity)

private lemma zeta_log_norm_locally_bounded :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ t : ℝ, |t| < δ →
      |Real.log ‖riemannZeta ((3/4 : ℂ)+(t : ℂ)*Complex.I)‖| ≤ B := by
  have hz0 : riemannZeta (3/4 : ℂ) ≠ 0 := by
    have hneg := re_riemannZeta_ofReal_neg (σ := 3/4) (by norm_num) (by norm_num)
    norm_num at hneg
    intro hz
    rw [hz] at hneg
    norm_num at hneg
  have hs1 : (3/4 : ℂ) ≠ 1 := by norm_num
  have hc : ContinuousAt (fun t : ℝ => Real.log ‖riemannZeta ((3/4 : ℂ)+(t : ℂ)*Complex.I)‖) 0 := by
    apply ContinuousAt.log
    · apply ContinuousAt.norm
      have hcurve : ContinuousAt (fun t : ℝ => (3/4 : ℂ)+(t : ℂ)*Complex.I) 0 := by fun_prop
      have hζ : ContinuousAt riemannZeta ((3/4 : ℂ)+(0 : ℂ)*Complex.I) := by
        simpa using (differentiableAt_riemannZeta hs1).continuousAt
      exact hζ.comp (f := fun t : ℝ => (3/4 : ℂ)+(t:ℂ)*Complex.I) (x := 0) hcurve
    · simpa using norm_ne_zero_iff.mpr hz0
  have he : ∀ᶠ t : ℝ in 𝓝 0,
      |Real.log ‖riemannZeta ((3/4 : ℂ)+(t : ℂ)*Complex.I)‖| <
        |Real.log ‖riemannZeta (3/4 : ℂ)‖|+1 := by
    have habs := hc.abs
    simpa using habs.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, |Real.log ‖riemannZeta (3/4 : ℂ)‖|+1, hδ, by positivity, ?_⟩
  intro t ht
  exact (hb (by simpa [Real.dist_eq] using ht)).le

private lemma re_primeBase (t : ℝ) (p : ℕ) :
    (primeBase t p).re = (p : ℝ) ^ (-(3/4 : ℝ)) * Real.cos (t*Real.log p) := by
  simp only [primeBase, mobiusFactorCountPrimeArgument, one_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
    Real.exp_zero, mul_one, Real.cos_neg]

private lemma norm_affine_lower {w : ℂ} (hw : -‖w‖ / 2 ≤ w.re) :
    (1+‖w‖)/2 ≤ ‖1+w‖ := by
  have he : ‖1+w‖^2 = 1 + 2*w.re + ‖w‖^2 := by
    simpa using normSq_affine 1 w
  nlinarith [norm_nonneg (1+w), norm_nonneg w, sq_nonneg (‖w‖-1)]

private lemma all_factors_separated {D a t : ℝ} (hD : 1 < D)
    (hsmall : D ^ (-(1/20) : ℝ) ≤ 1/2)
    (ha0 : 0 ≤ a) (haD : a ≤ D)
    (ht0 : 0 ≤ t) (htHi : t ≤ 15*Real.pi/(32*Real.log D))
    {p : ℕ} (hp : Nat.Prime p) :
    (1 + a * (p : ℝ)^(-(3/4 : ℝ)))/3 ≤ ‖1 + (a : ℂ)*primeBase t p‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hD0 : 0 < D := by linarith
  have hLD : 0 < Real.log D := Real.log_pos hD
  have hnorm : ‖(a : ℂ)*primeBase t p‖ = a * (p : ℝ)^(-(3/4 : ℝ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0, norm_primeBase]
  by_cases hple : (p : ℝ) ≤ D^(7/5 : ℝ)
  · have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hloghi := Real.log_le_log hp0 hple
    rw [Real.log_rpow hD0] at hloghi
    have hphase : t*Real.log p ≤ 2*Real.pi/3 := by
      have h1 := mul_le_mul_of_nonneg_left hloghi ht0
      have h2 := mul_le_mul_of_nonneg_right htHi (by positivity : 0 ≤ (7/5:ℝ)*Real.log D)
      have he : (15*Real.pi/(32*Real.log D))*((7/5:ℝ)*Real.log D) = 21*Real.pi/32 := by
        field_simp
        ring
      rw [he] at h2
      have hpi := Real.pi_pos
      linarith
    have hcos : -1/2 ≤ Real.cos (t*Real.log p) := by
      have hc : Real.cos (2*Real.pi/3) = -1/2 := by
        rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
        norm_num
      rw [← hc]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
        (by linarith [Real.pi_pos]) hphase
    have hre : -‖(a : ℂ)*primeBase t p‖/2 ≤ ((a : ℂ)*primeBase t p).re := by
      rw [hnorm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, re_primeBase]
      have hr : 0 ≤ a * (p : ℝ)^(-(3/4 : ℝ)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hcos hr]
    have hb := norm_affine_lower hre
    rw [hnorm] at hb
    nlinarith [Real.rpow_nonneg hp0.le (-(3/4 : ℝ))]
  · have hr : a * (p : ℝ)^(-(3/4 : ℝ)) ≤ 1/2 := by
      have hpow := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hD0 (7/5 : ℝ)) (le_of_not_ge hple)
        (by norm_num : -(3/4 : ℝ) ≤ 0)
      calc
        a * (p : ℝ)^(-(3/4 : ℝ)) ≤ D * (D^(7/5 : ℝ))^(-(3/4 : ℝ)) :=
          mul_le_mul haD hpow (by positivity) hD0.le
        _ = D ^ (-(1/20) : ℝ) := by
          rw [← Real.rpow_mul hD0.le]
          calc
            D*D^((7/5:ℝ)*(-(3/4:ℝ))) = D^(1:ℝ)*D^((7/5:ℝ)*(-(3/4:ℝ))) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hD0]; norm_num
        _ ≤ 1/2 := hsmall
    have htri : 1-‖(a : ℂ)*primeBase t p‖ ≤ ‖1 + (a : ℂ)*primeBase t p‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) (-((a : ℂ)*primeBase t p))
    rw [hnorm] at htri
    linarith

private lemma eventually_correction_bounded :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ D : ℝ in atTop, ∀ t : ℝ,
      0 ≤ t → t ≤ 15*Real.pi/(32*Real.log D) → ∀ N : ℕ, |correction N t| ≤ B := by
  obtain ⟨B₁, hB₁, h₁⟩ := finite_correction_bound
  obtain ⟨δ, B₂, hδ, hB₂, h₂⟩ := zeta_log_norm_locally_bounded
  refine ⟨B₂+B₁, add_nonneg hB₂ hB₁, ?_⟩
  have htend : Tendsto (fun D : ℝ => 15*Real.pi/(32*Real.log D)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 15*Real.pi)).div_atTop (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0:ℝ)<32))
    exact h
  filter_upwards [htend.eventually (gt_mem_nhds hδ)] with D hD
  intro t ht0 htHi N
  have ht : |t| < δ := by rw [abs_of_nonneg ht0]; exact htHi.trans_lt hD
  exact (abs_add_le _ _).trans (add_le_add (h₂ t ht) (h₁ N t))

private lemma eventually_correction_small (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ a : ℝ in atTop, B ≤ a^(1/3 : ℝ)/(512*Real.log a) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/3)).tendsto_div_nhds_zero
  have hb := hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/(512*(B+1))))
  filter_upwards [hb, eventually_gt_atTop (1:ℝ)] with a ha hA
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log a := Real.log_pos hA
  have hp : 0 < a^(1/3 : ℝ) := Real.rpow_pos_of_pos ha0 _
  have hsmall := (div_le_iff₀ hp).mp ha.le
  have hsmall' : 512*(B+1)*Real.log a ≤ a^(1/3 : ℝ) := by
    have he : (1/(512*(B+1))) * a^(1/3 : ℝ) = a^(1/3 : ℝ)/(512*(B+1)) := by ring
    rw [he] at hsmall
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<512*(B+1))).mp hsmall
    nlinarith
  apply (le_div_iff₀ (by positivity : (0:ℝ)<512*Real.log a)).mpr
  nlinarith

/-- The actual log-modulus derivative is positive and grows uniformly across the moving parameter sector. -/
theorem eventually_mobiusFactorCountLogModulus_derivative_lower :
    ∀ᶠ D : ℝ in atTop, ∀ a t : ℝ,
      D^(9/10 : ℝ) ≤ a → a ≤ D →
      7*Real.pi/(16*Real.log D) ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ N : ℕ, ⌊2*a^(4/3 : ℝ)⌋₊ ≤ N →
        DifferentiableAt ℝ (fun b : ℝ => mobiusFactorCountLogModulus N b t) a ∧
        a^(1/3 : ℝ)/(512*Real.log a) ≤ deriv (fun b : ℝ => mobiusFactorCountLogModulus N b t) a := by
  obtain ⟨B, hB, hcor⟩ := eventually_correction_bounded
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((eventually_correction_small B hB).and (eventually_gt_atTop (1:ℝ)))
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/10)).eventually (eventually_ge_atTop A)
  have hsmall : ∀ᶠ D : ℝ in atTop, D^(-(1/20):ℝ) ≤ 1/2 := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/20)).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
    exact h.mono (fun _ h => h.le)
  filter_upwards [eventually_mobiusFactorCountPrimeWork_lower, hcor,
    hlarge, hsmall, eventually_gt_atTop (1:ℝ)] with D hwork hcorD hDA hsmallD hD
  intro a t haLo haHi htLo htHi N hN
  obtain ⟨hBa, ha⟩ := hA a (hDA.trans haLo)
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log a := Real.log_pos ha
  have hLD : 0 < Real.log D := Real.log_pos hD
  have ht0 : 0 ≤ t :=
    (by positivity : 0 ≤ 7*Real.pi/(16*Real.log D)).trans htLo
  have hnz : ∀ p ∈ Nat.primesLE N, 1+(a:ℂ)*primeBase t p ≠ 0 := by
    intro p hp
    have hh := all_factors_separated hD hsmallD ha0.le haHi ht0 htHi (Nat.mem_primesLE.mp hp).2
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hh)
  have hd := hasDerivAt_logModulus ha0.ne' hnz
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  have hw := div_le_div_of_nonneg_right (hwork a t haLo haHi htLo htHi N hN) ha0.le
  have he : (a^(4/3 : ℝ)/(256*Real.log a))/a = a^(1/3 : ℝ)/(256*Real.log a) := by
    have hp : a^(4/3 : ℝ) = a*a^(1/3 : ℝ) := by
      calc
        _ = a^(1 : ℝ)*a^(1/3 : ℝ) := by rw [← Real.rpow_add ha0]; norm_num
        _ = _ := by rw [Real.rpow_one]
    rw [hp]
    field_simp
  rw [he] at hw
  have hc : -B ≤ correction N t := (abs_le.mp (hcorD t ht0 htHi N)).1
  have he2 : a^(1/3 : ℝ)/(256*Real.log a) = 2*(a^(1/3 : ℝ)/(512*Real.log a)) := by ring
  rw [he2] at hw
  linarith

private def slopeKernel (a : ℝ) (z : ℂ) : ℝ := (z / (1+(a:ℂ)*z)-z).re

private lemma hasDerivAt_logModulus_slope {N : ℕ} {a t : ℝ}
    (hnz : ∀ p ∈ Nat.primesLE N, 1+(a:ℂ)*primeBase t p ≠ 0) :
    HasDerivAt (fun b : ℝ => mobiusFactorCountLogModulus N b t)
      (correction N t + ∑ p ∈ Nat.primesLE N, slopeKernel a (primeBase t p)) a := by
  have hh := ((hasDerivAt_id a).mul_const
    (Real.log ‖riemannZeta ((3/4 : ℂ)+(t:ℂ)*Complex.I)‖)).add
    (HasDerivAt.fun_sum (fun p hp =>
      (hasDerivAt_logNorm_affine (hnz p hp)).add
        ((hasDerivAt_id a).mul_const (Real.log ‖1-primeBase t p‖))))
  convert! hh using 1
  simp only [correction, slopeKernel, one_mul, Complex.sub_re,
    add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

private lemma slopeKernel_abs_bounds {a : ℝ} {z : ℂ} (ha : 0 ≤ a)
    (hsep : (1+a*‖z‖)/3 ≤ ‖1+(a:ℂ)*z‖) :
    |slopeKernel a z| ≤ 3*‖z‖ ∧ |slopeKernel a z| ≤ 3*a*‖z‖^2 := by
  have hd : 0 < ‖1+(a:ℂ)*z‖ := lt_of_lt_of_le (by positivity) hsep
  have hnz : 1+(a:ℂ)*z ≠ 0 := norm_pos_iff.mp hd
  have he : z / (1+(a:ℂ)*z)-z = -((a:ℂ)*z^2)/(1+(a:ℂ)*z) := by
    apply (eq_div_iff hnz).mpr
    rw [sub_mul, div_mul_cancel₀ _ hnz]
    ring
  have hh : |slopeKernel a z| ≤ a*‖z‖^2 / ‖1+(a:ℂ)*z‖ := by
    calc
      _ ≤ ‖z / (1+(a:ℂ)*z)-z‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [he, norm_div, norm_neg, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_of_nonneg ha]
  constructor
  · apply hh.trans
    apply (div_le_iff₀ hd).mpr
    have h := mul_le_mul_of_nonneg_right hsep (norm_nonneg z)
    nlinarith [norm_nonneg z]
  · apply hh.trans
    apply (div_le_iff₀ hd).mpr
    have hden : 1/3 ≤ ‖1+(a:ℂ)*z‖ := by nlinarith [norm_nonneg z]
    have h := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 3*a*‖z‖^2)
    nlinarith

private def slopeHead (A : ℝ) (p : ℕ) : ℝ :=
  if p ≤ ⌊A^(4/3 : ℝ)⌋₊ then 3*(p:ℝ)^(-(3/4):ℝ) else 0

private def slopeTail (A : ℝ) (p : ℕ) : ℝ :=
  if ⌈A^(4/3 : ℝ)⌉₊ ≤ p then 3*A*(p:ℝ)^(-(3/2):ℝ) else 0

private lemma sum_slopeHead_le {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, slopeHead A p) ≤ 15*A^(1/3 : ℝ) := by
  classical
  let P := (Nat.primesLE N).filter (fun p => p ≤ ⌊A^(4/3 : ℝ)⌋₊)
  have hP : P ⊆ Finset.Icc 1 ⌊A^(4/3 : ℝ)⌋₊ := by
    intro p hp
    obtain ⟨hpN, hpL⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hpN).pos, hpL⟩
  have hint := Sieve.head_contribution_le (T := A) (a := 4/3)
    (c := 3/4) (θ := 0) (K := 1) hA (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (M := ⌊A^(4/3 : ℝ)⌋₊)
    (by simpa using Nat.floor_le (by positivity : 0 ≤ A^(4/3 : ℝ)))
  norm_num at hint
  calc
    _ = 3*∑ p ∈ P, (p:ℝ)^(-(3/4):ℝ) := by
      simp only [slopeHead, P, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ 3*∑ p ∈ Finset.Icc 1 ⌊A^(4/3 : ℝ)⌋₊, (p:ℝ)^(-(3/4):ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => by positivity)
    _ ≤ _ := by linarith

private lemma sum_slopeTail_le {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, slopeTail A p) ≤ 9*A^(1/3 : ℝ) := by
  classical
  let P := (Nat.primesLE N).filter (fun p => ⌈A^(4/3 : ℝ)⌉₊ ≤ p)
  have hP : P ⊆ Finset.Icc ⌈A^(4/3 : ℝ)⌉₊ N := by
    intro p hp
    obtain ⟨hpN, hpL⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpL, Nat.le_of_mem_primesLE hpN⟩
  have hceil := Nat.le_ceil (A^(4/3 : ℝ))
  have hR : 1 ≤ ⌈A^(4/3 : ℝ)⌉₊ := by
    exact_mod_cast (Real.one_le_rpow hA (by norm_num : (0:ℝ)≤4/3)).trans hceil
  have hint := Sieve.tail_contribution_le (T := A) (a := 4/3) (c := 3/2) (θ := 1)
    hA (by norm_num) (N := N) hR hceil
  norm_num at hint
  calc
    _ = 3*A*∑ p ∈ P, (p:ℝ)^(-(3/2):ℝ) := by
      simp only [slopeTail, P, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ 3*A*∑ p ∈ Finset.Icc ⌈A^(4/3 : ℝ)⌉₊ N, (p:ℝ)^(-(3/2):ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => by positivity)
    _ ≤ _ := by linarith

private lemma sum_abs_slopeKernel_le {D A a t : ℝ} (hD : 1 < D)
    (hsmall : D^(-(1/20):ℝ) ≤ 1/2) (hA : 1 ≤ A) (hAD : A ≤ D)
    (ha0 : 0 ≤ a) (haA : a ≤ A) (ht0 : 0 ≤ t)
    (htHi : t ≤ 15*Real.pi/(32*Real.log D)) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, |slopeKernel a (primeBase t p)|) ≤ 24*A^(1/3 : ℝ) := by
  have hpoint : ∀ p ∈ Nat.primesLE N,
      |slopeKernel a (primeBase t p)| ≤ slopeHead A p + slopeTail A p := by
    intro p hp
    have hsep := all_factors_separated hD hsmall ha0 (haA.trans hAD) ht0 htHi
      (Nat.prime_of_mem_primesLE hp)
    rw [← norm_primeBase t p] at hsep
    obtain ⟨hhead, htail⟩ := slopeKernel_abs_bounds ha0 hsep
    rw [norm_primeBase] at hhead htail
    have ht0' : 0 ≤ slopeTail A p := by unfold slopeTail; split_ifs <;> positivity
    have hh0' : 0 ≤ slopeHead A p := by unfold slopeHead; split_ifs <;> positivity
    by_cases hpl : p ≤ ⌊A^(4/3 : ℝ)⌋₊
    · rw [slopeHead, if_pos hpl]
      linarith
    · have hpr : A^(4/3 : ℝ) < (p:ℝ) := (Nat.floor_lt (by positivity)).mp (lt_of_not_ge hpl)
      have hph : ⌈A^(4/3 : ℝ)⌉₊ ≤ p := Nat.ceil_le.mpr hpr.le
      rw [slopeTail, if_pos hph]
      have he : ((p:ℝ)^(-(3/4):ℝ))^2 = (p:ℝ)^(-(3/2):ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
        norm_num
      rw [he] at htail
      have hm := mul_le_mul_of_nonneg_right haA (by positivity : 0 ≤ 3*(p:ℝ)^(-(3/2):ℝ))
      nlinarith
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hs
  linarith [sum_slopeHead_le hA N, sum_slopeTail_le hA N]

private lemma logModulus_abs_le {D A t B : ℝ} (hD : 1 < D)
    (hsmall : D^(-(1/20):ℝ) ≤ 1/2) (hA : 1 ≤ A) (hAD : A ≤ D)
    (ht0 : 0 ≤ t) (htHi : t ≤ 15*Real.pi/(32*Real.log D))
    (N : ℕ) (hcor : |correction N t| ≤ B) :
    |mobiusFactorCountLogModulus N A t| ≤ B*A + 24*A^(4/3 : ℝ) := by
  have hA0 : 0 < A := by linarith
  have hderiv : ∀ a ∈ Set.Icc (0:ℝ) A,
      DifferentiableAt ℝ (fun b : ℝ => mobiusFactorCountLogModulus N b t) a ∧
      |deriv (fun b : ℝ => mobiusFactorCountLogModulus N b t) a| ≤ B+24*A^(1/3 : ℝ) := by
    intro a ha
    have ha0 : 0 ≤ a := ha.1
    have hnz : ∀ p ∈ Nat.primesLE N, 1+(a:ℂ)*primeBase t p ≠ 0 := by
      intro p hp
      have hsep := all_factors_separated hD hsmall ha.1 (ha.2.trans hAD) ht0 htHi
        (Nat.prime_of_mem_primesLE hp)
      exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hsep)
    have hd := hasDerivAt_logModulus_slope hnz
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    calc
      _ ≤ |correction N t| + |∑ p ∈ Nat.primesLE N, slopeKernel a (primeBase t p)| := abs_add_le _ _
      _ ≤ B + ∑ p ∈ Nat.primesLE N, |slopeKernel a (primeBase t p)| :=
        add_le_add hcor (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ _ := add_le_add (le_refl B) (sum_abs_slopeKernel_le hD hsmall hA hAD ha.1 ha.2 ht0 htHi N)
  have hcont : ContinuousOn (fun b : ℝ => mobiusFactorCountLogModulus N b t) (Set.Icc 0 A) := by
    intro b hb
    exact (hderiv b hb).1.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun b : ℝ => mobiusFactorCountLogModulus N b t) (Set.Ioo 0 A) := by
    intro b hb
    exact (hderiv b ⟨hb.1.le, hb.2.le⟩).1.differentiableWithinAt
  obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope (fun b : ℝ => mobiusFactorCountLogModulus N b t) hA0 hcont hdiff
  have hzero : mobiusFactorCountLogModulus N 0 t = 0 := by simp [mobiusFactorCountLogModulus]
  have heabs := congrArg abs he
  simp only [hzero, sub_zero, abs_div, abs_of_pos hA0] at heabs
  have hb := (hderiv c ⟨hc.1.le, hc.2.le⟩).2
  rw [heabs] at hb
  have hbound := (div_le_iff₀ hA0).mp hb
  have hpow : A*A^(1/3 : ℝ) = A^(4/3 : ℝ) := by
    calc
      _ = A^(1:ℝ)*A^(1/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  nlinarith [hpow]

/-- Uniform control of every low parameter, including all primes up to an arbitrary truncation. -/
theorem eventually_mobiusFactorCountLogModulus_abs_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ D : ℝ in atTop, ∀ A t : ℝ,
      1 ≤ A → A ≤ D → 0 ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ N : ℕ, |mobiusFactorCountLogModulus N A t| ≤ B*A+24*A^(4/3 : ℝ) := by
  obtain ⟨B, hB, hcor⟩ := eventually_correction_bounded
  refine ⟨B, hB, ?_⟩
  have hsmall : ∀ᶠ D : ℝ in atTop, D^(-(1/20):ℝ) ≤ 1/2 := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/20)).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
    exact h.mono (fun _ h => h.le)
  filter_upwards [hcor, hsmall, eventually_gt_atTop (1:ℝ)] with D hcorD hsmallD hD
  intro A t hA hAD ht0 htHi N
  exact logModulus_abs_le hD hsmallD hA hAD ht0 htHi N (hcorD t ht0 htHi N)

private lemma logModulus_increment {N : ℕ} {t u v C : ℝ} (huv : u ≤ v)
    (hd : ∀ a ∈ Set.Icc u v,
      DifferentiableAt ℝ (fun b : ℝ => mobiusFactorCountLogModulus N b t) a ∧
      C ≤ deriv (fun b : ℝ => mobiusFactorCountLogModulus N b t) a) :
    C*(v-u) ≤ mobiusFactorCountLogModulus N v t - mobiusFactorCountLogModulus N u t := by
  rcases eq_or_lt_of_le huv with he | hl
  · rw [he]
    simp
  have hc : ContinuousOn (fun b : ℝ => mobiusFactorCountLogModulus N b t) (Set.Icc u v) :=
    fun a ha => (hd a ha).1.continuousAt.continuousWithinAt
  have hf : DifferentiableOn ℝ (fun b : ℝ => mobiusFactorCountLogModulus N b t) (Set.Ioo u v) :=
    fun a ha => (hd a ⟨ha.1.le, ha.2.le⟩).1.differentiableWithinAt
  obtain ⟨c, hcuv, he⟩ := exists_deriv_eq_slope (fun b : ℝ => mobiusFactorCountLogModulus N b t) hl hc hf
  have hbound := (hd c ⟨hcuv.1.le, hcuv.2.le⟩).2
  rw [he] at hbound
  exact (le_div_iff₀ (sub_pos.mpr hl)).mp hbound

private lemma eventually_initial_loss_small (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ D : ℝ in atTop,
      B*(D^(9/10 : ℝ))+24*(D^(9/10 : ℝ))^(4/3 : ℝ) ≤
        D^(4/3 : ℝ)/(4096*Real.log D) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<2/15)).tendsto_div_nhds_zero
  have hb := hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/(4096*(B+24))))
  filter_upwards [hb, eventually_gt_atTop (1:ℝ)] with D hsmall hD
  have hD0 : 0 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hpow : 0 < D^(2/15 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hs := (div_le_iff₀ hpow).mp hsmall.le
  have hs' : Real.log D*(4096*(B+24)) ≤ D^(2/15 : ℝ) := by
    have he : 1/(4096*(B+24))*D^(2/15 : ℝ) = D^(2/15 : ℝ)/(4096*(B+24)) := by ring
    rw [he] at hs
    exact (le_div_iff₀ (by positivity : (0:ℝ)<4096*(B+24))).mp hs
  have hm := mul_le_mul_of_nonneg_right hs' (Real.rpow_nonneg hD0.le (6/5 : ℝ))
  have he : D^(2/15 : ℝ)*D^(6/5 : ℝ) = D^(4/3 : ℝ) := by
    rw [← Real.rpow_add hD0]
    norm_num
  rw [he] at hm
  have hlow := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num : (9/10:ℝ)≤6/5)
  have hbig : (D^(9/10 : ℝ))^(4/3 : ℝ) = D^(6/5 : ℝ) := by
    rw [← Real.rpow_mul hD0.le]
    norm_num
  rw [hbig]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4096*Real.log D)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlow hB]

/-- The complete log modulus grows on the moving height sector after its initial value is retained. -/
theorem eventually_mobiusFactorCountLogModulus_growth :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ,
      7*Real.pi/(16*Real.log D) ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ N : ℕ, ⌊2*D^(4/3 : ℝ)⌋₊ ≤ N →
        D^(4/3 : ℝ)/(4096*Real.log D) ≤ mobiusFactorCountLogModulus N D t := by
  obtain ⟨B, hB, hlow⟩ := eventually_mobiusFactorCountLogModulus_abs_le
  have hhalf : ∀ᶠ D : ℝ in atTop, D^(9/10 : ℝ) ≤ D/2 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/10)).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
    filter_upwards [hh, eventually_gt_atTop (1:ℝ)] with D hsmall hD
    have hD0 : 0 < D := by linarith
    have hm := mul_le_mul_of_nonneg_left hsmall.le hD0.le
    have he : D*D^(-(1/10):ℝ) = D^(9/10 : ℝ) := by
      calc
        _ = D^(1:ℝ)*D^(-(1/10):ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hD0]; norm_num
    rw [he] at hm
    linarith
  filter_upwards [eventually_mobiusFactorCountLogModulus_derivative_lower, hlow, hhalf,
    eventually_initial_loss_small B hB, eventually_gt_atTop (1:ℝ)]
    with D hderivD hlowD hhalfD hlossD hD
  intro t htLo htHi N hN
  have hD0 : 0 < D := by linarith
  have hLD : 0 < Real.log D := Real.log_pos hD
  have ht0 : 0 ≤ t := (by positivity : 0 ≤ 7*Real.pi/(16*Real.log D)).trans htLo
  have hA1 : 1 ≤ D^(9/10 : ℝ) := Real.one_le_rpow hD.le (by norm_num)
  have hAD : D^(9/10 : ℝ) ≤ D := hhalfD.trans (by linarith)
  have hinitial := hlowD (D^(9/10 : ℝ)) t hA1 hAD ht0 htHi N
  have hderiv : ∀ a ∈ Set.Icc (D^(9/10 : ℝ)) D,
      DifferentiableAt ℝ (fun b : ℝ => mobiusFactorCountLogModulus N b t) a ∧
      a^(1/3 : ℝ)/(512*Real.log a) ≤ deriv (fun b : ℝ => mobiusFactorCountLogModulus N b t) a := by
    intro a ha
    apply hderivD a t ha.1 ha.2 htLo htHi N
    apply le_trans _ hN
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith [ha.1]) ha.2 (by norm_num)) (by norm_num)
  have hfirst : 0 ≤ mobiusFactorCountLogModulus N (D/2) t - mobiusFactorCountLogModulus N (D^(9/10 : ℝ)) t := by
    have h := logModulus_increment (N := N) (t := t) (C := 0) hhalfD ?_
    · simpa using h
    intro a ha
    have hd := hderiv a ⟨ha.1, ha.2.trans (by linarith)⟩
    refine ⟨hd.1, le_trans ?_ hd.2⟩
    have hloga : 0 ≤ Real.log a := Real.log_nonneg (hA1.trans ha.1)
    have ha0 : 0 ≤ a := le_trans (by norm_num : (0:ℝ)≤1) (hA1.trans ha.1)
    positivity
  have hsecond : D^(4/3 : ℝ)/(2048*Real.log D) ≤
      mobiusFactorCountLogModulus N D t - mobiusFactorCountLogModulus N (D/2) t := by
    have h := logModulus_increment (N := N) (t := t)
      (C := D^(1/3 : ℝ)/(1024*Real.log D)) (by linarith : D/2 ≤ D) ?_
    · have he : D^(1/3 : ℝ)/(1024*Real.log D)*(D-D/2) =
          D^(4/3 : ℝ)/(2048*Real.log D) := by
        have hpow : D^(4/3 : ℝ) = D*D^(1/3 : ℝ) := by
          calc
            _ = D^(1:ℝ)*D^(1/3:ℝ) := by rw [← Real.rpow_add hD0]; norm_num
            _ = _ := by rw [Real.rpow_one]
        rw [hpow]
        ring
      rwa [he] at h
    intro a ha
    have hda := hderiv a ⟨hhalfD.trans ha.1, ha.2⟩
    refine ⟨hda.1, le_trans ?_ hda.2⟩
    have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha.1
    have ha1 : 1 ≤ a := hA1.trans (hhalfD.trans ha.1)
    have hloga : 0 ≤ Real.log a := Real.log_nonneg ha1
    have hloghi : Real.log a ≤ Real.log D := Real.log_le_log ha0 ha.2
    have ha13 : D^(1/3 : ℝ) ≤ 2*a^(1/3 : ℝ) := by
      have hm := Real.rpow_le_rpow hD0.le (by linarith [ha.1] : D ≤ 2*a) (by norm_num : (0:ℝ)≤1/3)
      rw [Real.mul_rpow (by norm_num) ha0.le] at hm
      have htwo : (2:ℝ)^(1/3:ℝ) ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
          (by norm_num : (1/3:ℝ)≤1)
      exact hm.trans (mul_le_mul_of_nonneg_right htwo (by positivity))
    have haGt : 1 < a := by
      have hAgt : 1 < D^(9/10 : ℝ) := Real.one_lt_rpow hD (by norm_num)
      exact hAgt.trans_le (hhalfD.trans ha.1)
    have hlogaPos : 0 < Real.log a := Real.log_pos haGt
    calc
      _ ≤ (2*a^(1/3 : ℝ))/(1024*Real.log D) :=
        div_le_div_of_nonneg_right ha13 (by positivity)
      _ = a^(1/3 : ℝ)/(512*Real.log D) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hi := (abs_le.mp hinitial).1
  have he : D^(4/3 : ℝ)/(2048*Real.log D) = 2*(D^(4/3 : ℝ)/(4096*Real.log D)) := by ring
  rw [he] at hsecond
  linarith

/-- Finite Euler completion of the squarefree factor-count series at an integer parameter. -/
def mobiusFactorCountEulerPartial (N j : ℕ) (t : ℝ) : ℂ :=
  riemannZeta ((3/4 : ℂ)+(t:ℂ)*Complex.I)^j *
    ∏ p ∈ Nat.primesLE N, (1+(j:ℂ)*primeBase t p)*(1-primeBase t p)^j

private lemma one_sub_primeBase_ne_zero (t : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    1-primeBase t p ≠ 0 := by
  have hnorm : ‖primeBase t p‖ < 1 := by
    rw [norm_primeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
  intro h
  have he : primeBase t p = 1 := by linear_combination -h
  rw [he] at hnorm
  norm_num at hnorm

private lemma log_norm_eulerPartial {N j : ℕ} {t : ℝ}
    (hz : riemannZeta ((3/4 : ℂ)+(t:ℂ)*Complex.I) ≠ 0)
    (hp : ∀ p ∈ Nat.primesLE N, 1+(j:ℂ)*primeBase t p ≠ 0) :
    Real.log ‖mobiusFactorCountEulerPartial N j t‖ = mobiusFactorCountLogModulus N j t := by
  have hfac : ∀ p ∈ Nat.primesLE N,
      (1+(j:ℂ)*primeBase t p)*(1-primeBase t p)^j ≠ 0 := by
    intro p hpN
    exact mul_ne_zero (hp p hpN) (pow_ne_zero _ (one_sub_primeBase_ne_zero t
      (Nat.prime_of_mem_primesLE hpN)))
  rw [mobiusFactorCountEulerPartial, norm_mul, Real.log_mul
    (norm_ne_zero_iff.mpr (pow_ne_zero _ hz))
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr hfac)), norm_pow, Real.log_pow,
    norm_prod, Real.log_prod (fun p hpN => norm_ne_zero_iff.mpr (hfac p hpN))]
  unfold mobiusFactorCountLogModulus
  congr 1
  apply Finset.sum_congr rfl
  intro p hpN
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hp p hpN))
    (norm_ne_zero_iff.mpr (pow_ne_zero _ (one_sub_primeBase_ne_zero t
      (Nat.prime_of_mem_primesLE hpN)))), norm_pow, Real.log_pow]
  norm_cast

private lemma eventually_zeta_height_nonzero :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ,
      0 ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      riemannZeta ((3/4 : ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  have hz0 : riemannZeta (3/4 : ℂ) ≠ 0 := by
    have hneg := re_riemannZeta_ofReal_neg (σ := 3/4) (by norm_num) (by norm_num)
    norm_num at hneg
    intro hz
    rw [hz] at hneg
    norm_num at hneg
  have hc : ContinuousAt (fun t : ℝ => riemannZeta ((3/4 : ℂ)+(t:ℂ)*Complex.I)) 0 := by
    have hζ : ContinuousAt riemannZeta ((3/4 : ℂ)+(0:ℂ)*Complex.I) := by
      simpa using (differentiableAt_riemannZeta (by norm_num : (3/4:ℂ)≠1)).continuousAt
    apply hζ.comp (f := fun t : ℝ => (3/4 : ℂ)+(t:ℂ)*Complex.I) (x := 0)
    fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0, riemannZeta ((3/4 : ℂ)+(t:ℂ)*Complex.I) ≠ 0 :=
    hc.eventually_ne (by simpa using hz0)
  obtain ⟨δ, hδ, hδz⟩ := Metric.eventually_nhds_iff.mp he
  have htend : Tendsto (fun D : ℝ => 15*Real.pi/(32*Real.log D)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := 15*Real.pi)).div_atTop
      (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0:ℝ)<32))
  filter_upwards [htend.eventually (gt_mem_nhds hδ)] with D hD
  intro t ht0 htHi
  apply hδz
  simpa [Real.dist_eq, abs_of_nonneg ht0] using htHi.trans_lt hD

/-- Every integer parameter up to the current scale is nonzero and has the stated log modulus. -/
theorem eventually_mobiusFactorCountEulerPartial_logNorm :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ,
      0 ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ j : ℕ, (j:ℝ) ≤ D → ∀ N : ℕ,
        mobiusFactorCountEulerPartial N j t ≠ 0 ∧
        Real.log ‖mobiusFactorCountEulerPartial N j t‖ = mobiusFactorCountLogModulus N j t := by
  have hsmall : ∀ᶠ D : ℝ in atTop, D^(-(1/20):ℝ) ≤ 1/2 := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/20)).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
    exact h.mono (fun _ h => h.le)
  filter_upwards [eventually_zeta_height_nonzero, hsmall, eventually_gt_atTop (1:ℝ)]
    with D hz hs hD
  intro t ht0 htHi j hj N
  have hp : ∀ p ∈ Nat.primesLE N, 1+(j:ℂ)*primeBase t p ≠ 0 := by
    intro p hpN
    have hsep := all_factors_separated hD hs (Nat.cast_nonneg j) hj ht0 htHi
      (Nat.prime_of_mem_primesLE hpN)
    have hnz := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hsep)
    simpa only [Complex.ofReal_natCast] using hnz
  have hnz : mobiusFactorCountEulerPartial N j t ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (hz t ht0 htHi))
    apply Finset.prod_ne_zero_iff.mpr
    intro p hpN
    exact mul_ne_zero (hp p hpN) (pow_ne_zero _
      (one_sub_primeBase_ne_zero t (Nat.prime_of_mem_primesLE hpN)))
  exact ⟨hnz, log_norm_eulerPartial (hz t ht0 htHi) hp⟩

/-- The highest integer parameter has exponential growth, uniformly in all sufficiently long prime truncations. -/
theorem eventually_mobiusFactorCountEulerPartial_growth :
    ∀ᶠ D : ℕ in atTop, ∀ t : ℝ,
      7*Real.pi/(16*Real.log D) ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ N : ℕ, ⌊2*(D:ℝ)^(4/3 : ℝ)⌋₊ ≤ N →
        Real.exp ((D:ℝ)^(4/3 : ℝ)/(4096*Real.log D)) ≤ ‖mobiusFactorCountEulerPartial N D t‖ := by
  have he := tendsto_natCast_atTop_atTop.eventually
    (eventually_mobiusFactorCountLogModulus_growth.and
      (eventually_mobiusFactorCountEulerPartial_logNorm.and (eventually_gt_atTop (1:ℝ))))
  filter_upwards [he] with D hD
  intro t htLo htHi N hN
  obtain ⟨hg, hprod, hD1⟩ := hD
  have hLD : 0 < Real.log (D:ℝ) := Real.log_pos hD1
  have ht0 : 0 ≤ t := (by positivity : 0 ≤ 7*Real.pi/(16*Real.log (D:ℝ))).trans htLo
  obtain ⟨hnz, hlog⟩ := hprod t ht0 htHi D le_rfl N
  have hb := Real.exp_le_exp.mpr (hg t htLo htHi N hN)
  rwa [← hlog, Real.exp_log (norm_pos_iff.mpr hnz)] at hb

end RHTower
