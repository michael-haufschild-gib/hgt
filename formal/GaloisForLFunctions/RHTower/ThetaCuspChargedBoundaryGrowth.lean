import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Charged-cusp growth of the complete theta source

Integral comparison gives Gaussian-power bounds with the square-root scale.
At `exp(2z) = N^(-2)+2i`, every arithmetic phase is one. An exact finite
block then gives a lower bound proportional to `N^5`, while the entire
horizontal ray satisfies a matching `N^5 exp(-s/2)` upper bound.

These are unconditional estimates for the complete theta source. They do
not assert positivity of the tail kernel or settle RH. They supply the
boundary-growth test for proposed uniform Cauchy comparisons.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.ThetaCuspBoundaryAudit


theorem gaussian_sum_from_one_le {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-a * ((n+1 : ℕ) : ℝ)^2)) ≤ Real.sqrt (Real.pi/a)/2 := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-a*x^2)) (Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have hsq : x^2 ≤ y^2 := by nlinarith [show 0 ≤ x from hx, show 0 ≤ y from hy]
    nlinarith
  simpa only [integral_gaussian_Ioi] using
    hanti.tsum_add_one_le_integral (integrable_exp_neg_mul_sq ha).integrableOn
      (fun x hx => (Real.exp_pos _).le)

theorem even_power_gaussian_le {a : ℝ} (ha : 0 < a) (k : ℕ) (x : ℝ) :
    x^(2*k)*Real.exp (-a*x^2) ≤
      (k.factorial : ℝ)*(2/a)^k*Real.exp (-(a/2)*x^2) := by
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hpow := Real.pow_div_factorial_le_exp (a*x^2/2) (by positivity) k
  rw [div_le_iff₀ hfac] at hpow
  have he : (a*x^2/2)^k = (a/2)^k*x^(2*k) := by rw [pow_mul]; ring
  rw [he] at hpow
  have hi : (2/a)^k*(a/2)^k=1 := by rw [← mul_pow]; field_simp; simp
  have hb : x^(2*k) ≤ (k.factorial : ℝ)*(2/a)^k*Real.exp (a*x^2/2) := by
    calc
      _ = (2/a)^k*((a/2)^k*x^(2*k)) := by rw [← mul_assoc, hi, one_mul]
      _ ≤ (2/a)^k*(Real.exp (a*x^2/2)*k.factorial) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ((k.factorial : ℝ)*(2/a)^k*Real.exp (a*x^2/2))*Real.exp (-a*x^2) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem gaussian_even_power_sum_le {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 0 < k) :
    thetaGaussianPowerSum a (2*k) ≤
      (k.factorial : ℝ)*(2/a)^k*(Real.sqrt (Real.pi/(a/2))/2) := by
  have hf := summable_pow_mul_exp_neg_nat_sq (2*k) ha
  have hg0 := summable_pow_mul_exp_neg_nat_sq 0 (half_pos ha)
  simp only [pow_zero, one_mul] at hg0
  have hg := hg0.comp_injective (show Function.Injective (fun n : ℕ => n+1) from
    fun m n h => Nat.add_right_cancel h)
  have hf1 := hf.comp_injective (show Function.Injective (fun n : ℕ => n+1) from
    fun m n h => Nat.add_right_cancel h)
  have hs : thetaGaussianPowerSum a (2*k) =
      ∑' n : ℕ, (((n+1 : ℕ) : ℝ)^(2*k)*Real.exp (-a*((n+1 : ℕ) : ℝ)^2)) := by
    unfold thetaGaussianPowerSum
    rw [hf.tsum_eq_zero_add]
    simp [zero_pow (by omega : 2*k ≠ 0)]
  rw [hs]
  calc
    _ ≤ ∑' n : ℕ, (k.factorial : ℝ)*(2/a)^k*
        Real.exp (-(a/2)*((n+1 : ℕ) : ℝ)^2) :=
      hf1.tsum_le_tsum (fun n => even_power_gaussian_le ha k _) (hg.mul_left _)
    _ = (k.factorial : ℝ)*(2/a)^k*
        ∑' n : ℕ, Real.exp (-(a/2)*((n+1 : ℕ) : ℝ)^2) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_sum_from_one_le (half_pos ha)) (by positivity)


theorem source_norm_le_gaussian_sums {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2*δ < Real.pi/2) {z : ℂ} (him : |z.im| ≤ δ) :
    ‖thetaCuspStripSource z‖ ≤ Real.exp (z.re/2) *
      (4*Real.pi^2*Real.exp (4*z.re)*
          thetaGaussianPowerSum (Real.pi*Real.cos (2*δ)*Real.exp (2*z.re)) 4 +
        6*Real.pi*Real.exp (2*z.re)*
          thetaGaussianPowerSum (Real.pi*Real.cos (2*δ)*Real.exp (2*z.re)) 2) := by
  let a := Real.pi*Real.cos (2*δ)*Real.exp (2*z.re)
  have hc : 0 < Real.cos (2*δ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  have ha : 0 < a := by dsimp [a]; positivity
  let A := Real.exp (z.re/2)*(4*Real.pi^2*Real.exp (4*z.re))
  let B := Real.exp (z.re/2)*(6*Real.pi*Real.exp (2*z.re))
  let f := fun n : ℕ => A*((n:ℝ)^4*Real.exp (-a*(n:ℝ)^2)) +
    B*((n:ℝ)^2*Real.exp (-a*(n:ℝ)^2))
  have h4 := summable_pow_mul_exp_neg_nat_sq 4 ha
  have h2 := summable_pow_mul_exp_neg_nat_sq 2 ha
  have hf : Summable f := (h4.mul_left A).add (h2.mul_left B)
  have hdom : ∀ n, ‖thetaCuspComplexTerm z n‖ ≤ f n := by
    intro n
    convert norm_thetaCuspComplexTerm_le_pointwise hδ4.le him n using 1
    dsimp [f, A, B, a]
    rw [show -(Real.pi*Real.cos (2*δ)*Real.exp (2*z.re))*(n:ℝ)^2 =
      -(Real.pi*Real.cos (2*δ))*(n:ℝ)^2*Real.exp (2*z.re) by ring]
    ring
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdom hf
  have hb := (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hdom hf)
  have he : (∑' n, f n) = A*thetaGaussianPowerSum a 4 + B*thetaGaussianPowerSum a 2 := by
    dsimp only [f]
    rw [(h4.mul_left A).tsum_add (h2.mul_left B), tsum_mul_left, tsum_mul_left]
    rfl
  rw [he] at hb
  simpa only [A, B, a, thetaCuspStripSource, mul_add, mul_assoc] using hb

theorem source_norm_le_sharp_strip {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2*δ < Real.pi/2) {z : ℂ} (him : |z.im| ≤ δ) :
    ‖thetaCuspStripSource z‖ ≤
      (16/Real.cos (2*δ)^2+6/Real.cos (2*δ))*Real.sqrt (2/Real.cos (2*δ))*
        Real.exp (-z.re/2) := by
  let c := Real.cos (2*δ)
  let E := Real.exp z.re
  let a := Real.pi*c*E^2
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  have hE : 0 < E := Real.exp_pos _
  have ha : 0 < a := by dsimp [a]; positivity
  have e2 : Real.exp (2*z.re) = E^2 := by simpa [E] using Real.exp_nat_mul z.re 2
  have e4 : Real.exp (4*z.re) = E^4 := by simpa [E] using Real.exp_nat_mul z.re 4
  have h4 : thetaGaussianPowerSum a 4 ≤ 8/a^2*(Real.sqrt (Real.pi/(a/2))/2) := by
    calc
      _ ≤ (2:ℝ)*(2/a)^2*(Real.sqrt (Real.pi/(a/2))/2) := by
        simpa using gaussian_even_power_sum_le ha (show 0 < (2:ℕ) by omega)
      _ = _ := by ring
  have h2 : thetaGaussianPowerSum a 2 ≤ 2/a*(Real.sqrt (Real.pi/(a/2))/2) := by
    simpa using gaussian_even_power_sum_le ha (show 0 < (1:ℕ) by omega)
  have hsqrt : Real.sqrt (Real.pi/(a/2)) = Real.sqrt (2/c)/E := by
    have he : Real.pi/(a/2) = (2/c)/E^2 := by dsimp [a]; field_simp
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hE.le]
  have hx : Real.exp (z.re/2)/E = Real.exp (-z.re/2) := by
    change Real.exp (z.re/2)/Real.exp z.re = _
    rw [← Real.exp_sub]; congr 1; ring
  have h := source_norm_le_gaussian_sums hδ0 hδ4 him
  rw [e2, e4] at h
  change ‖thetaCuspStripSource z‖ ≤
    Real.exp (z.re/2)*(4*Real.pi^2*E^4*thetaGaussianPowerSum a 4+
      6*Real.pi*E^2*thetaGaussianPowerSum a 2) at h
  calc
    _ ≤ Real.exp (z.re/2)*(4*Real.pi^2*E^4*thetaGaussianPowerSum a 4+
        6*Real.pi*E^2*thetaGaussianPowerSum a 2) := h
    _ ≤ Real.exp (z.re/2)*(4*Real.pi^2*E^4*(8/a^2*(Real.sqrt (Real.pi/(a/2))/2))+
        6*Real.pi*E^2*(2/a*(Real.sqrt (Real.pi/(a/2))/2))) := by gcongr
    _ = (16/c^2+6/c)*Real.sqrt (2/c)*(Real.exp (z.re/2)/E) := by
      rw [hsqrt]; dsimp [a]; field_simp; ring
    _ = _ := by rw [hx]



theorem fourth_power_block_lower (N : ℕ) (hN : 0 < N) :
    (N:ℝ)^5*Real.exp (-4*Real.pi) ≤ thetaGaussianPowerSum (Real.pi/(N:ℝ)^2) 4 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have ha : 0 < Real.pi/(N:ℝ)^2 := by positivity
  have hs := summable_pow_mul_exp_neg_nat_sq 4 ha
  have hblock : ∀ n ∈ Finset.Ico N (2*N),
      (N:ℝ)^4*Real.exp (-4*Real.pi) ≤
        (n:ℝ)^4*Real.exp (-(Real.pi/(N:ℝ)^2)*(n:ℝ)^2) := by
    intro n hn
    obtain ⟨hn0, hn1⟩ := Finset.mem_Ico.mp hn
    have hnlo : (N:ℝ) ≤ n := by exact_mod_cast hn0
    have hnhi : (n:ℝ) ≤ 2*N := by exact_mod_cast hn1.le
    have hrat : (n:ℝ)^2/(N:ℝ)^2 ≤ 4 := by
      rw [div_le_iff₀ (sq_pos_of_pos hNr)]
      nlinarith [sq_nonneg ((n:ℝ)-2*N)]
    have he : Real.exp (-4*Real.pi) ≤
        Real.exp (-(Real.pi/(N:ℝ)^2)*(n:ℝ)^2) := by
      apply Real.exp_le_exp.mpr
      have hp := mul_le_mul_of_nonneg_left hrat Real.pi_pos.le
      calc
        -4*Real.pi ≤ -(Real.pi*((n:ℝ)^2/(N:ℝ)^2)) := by linarith
        _ = _ := by ring
    exact mul_le_mul (by gcongr) he (Real.exp_pos _).le (by positivity)
  have hsum := Finset.sum_le_sum hblock
  have hcard : (Finset.Ico N (2*N)).card = N := by simp; omega
  have he : (∑ n ∈ Finset.Ico N (2*N), (N:ℝ)^4*Real.exp (-4*Real.pi)) =
      (N:ℝ)^5*Real.exp (-4*Real.pi) := by rw [Finset.sum_const, hcard]; simp; ring
  rw [he] at hsum
  exact hsum.trans (hs.sum_le_tsum _ (fun n hn => by positivity))

theorem charged_cusp_gaussian_phase {z : ℂ} {eps : ℝ}
    (he : Complex.exp (2*z) = (eps:ℂ)+2*Complex.I) (n : ℕ) :
    Complex.exp (-(Real.pi:ℂ)*((n:ℂ)*Complex.exp z)^2) =
      (Real.exp (-Real.pi*eps*(n:ℝ)^2):ℂ) := by
  have hs : ((n:ℂ)*Complex.exp z)^2 = (n:ℂ)^2*((eps:ℂ)+2*Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [he]
  rw [hs]
  have hsplit : -(Real.pi:ℂ)*((n:ℂ)^2*((eps:ℂ)+2*Complex.I)) =
      ((-Real.pi*eps*(n:ℝ)^2:ℝ):ℂ)+
        ((n^2:ℕ):ℂ)*(-(2*(Real.pi:ℂ)*Complex.I)) := by push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg,
    Complex.exp_two_pi_mul_I]
  simp [Complex.ofReal_exp]


theorem charged_cusp_source_identity {z : ℂ} {eps : ℝ} (heps : 0 < eps)
    (he : Complex.exp (2*z) = (eps:ℂ)+2*Complex.I) :
    thetaCuspStripSource z = Complex.exp (z/2)*
      (4*(Real.pi:ℂ)^2*((eps:ℂ)+2*Complex.I)^2*(thetaGaussianPowerSum (Real.pi*eps) 4:ℂ)-
        6*(Real.pi:ℂ)*((eps:ℂ)+2*Complex.I)*(thetaGaussianPowerSum (Real.pi*eps) 2:ℂ)) := by
  let A : ℂ := 4*(Real.pi:ℂ)^2*((eps:ℂ)+2*Complex.I)^2
  let B : ℂ := 6*(Real.pi:ℂ)*((eps:ℂ)+2*Complex.I)
  let f := fun (k n : ℕ) => (((n:ℝ)^k*Real.exp (-(Real.pi*eps)*(n:ℝ)^2):ℝ):ℂ)
  have hterm : ∀ n, thetaCuspComplexTerm z n = Complex.exp (z/2)*(A*f 4 n-B*f 2 n) := by
    intro n
    unfold thetaCuspComplexTerm thetaCuspComplexSeed
    rw [charged_cusp_gaussian_phase he]
    rw [show -Real.pi*eps*(n:ℝ)^2= -(Real.pi*eps)*(n:ℝ)^2 by ring]
    have hs : ((n:ℂ)*Complex.exp z)^2 = (n:ℂ)^2*((eps:ℂ)+2*Complex.I) := by
      rw [mul_pow, ← Complex.exp_nat_mul]; norm_num only [Nat.cast_ofNat]; rw [he]
    have h4 : ((n:ℂ)*Complex.exp z)^4 = ((n:ℂ)^2*((eps:ℂ)+2*Complex.I))^2 := by
      rw [← hs]; ring
    rw [h4, hs]
    dsimp [A, B, f]
    push_cast
    ring
  have hsum (k : ℕ) : Summable (f k) := by
    exact (Complex.summable_ofReal).mpr (summable_pow_mul_exp_neg_nat_sq k (mul_pos Real.pi_pos heps))
  unfold thetaCuspStripSource
  simp_rw [hterm]
  rw [tsum_mul_left, ((hsum 4).mul_left A).tsum_sub ((hsum 2).mul_left B),
    tsum_mul_left, tsum_mul_left]
  simp only [f, ← Complex.ofReal_tsum, thetaGaussianPowerSum, A, B]


theorem charged_cusp_source_lower {z : ℂ} {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (he : Complex.exp (2*z) = (eps:ℂ)+2*Complex.I) :
    Real.exp (z.re/2)*(12*Real.pi^2*thetaGaussianPowerSum (Real.pi*eps) 4) ≤
      ‖thetaCuspStripSource z‖ := by
  let S4 := thetaGaussianPowerSum (Real.pi*eps) 4
  let S2 := thetaGaussianPowerSum (Real.pi*eps) 2
  let B : ℂ := 4*(Real.pi:ℂ)^2*((eps:ℂ)+2*Complex.I)^2*(S4:ℂ)-
    6*(Real.pi:ℂ)*((eps:ℂ)+2*Complex.I)*(S2:ℂ)
  have h4 : 0 ≤ S4 := thetaGaussianPowerSum_nonneg _ _
  have h2 : 0 ≤ S2 := thetaGaussianPowerSum_nonneg _ _
  have hre : B.re = 4*Real.pi^2*(eps^2-4)*S4-6*Real.pi*eps*S2 := by
    dsimp [B]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, pow_two]
    ring
  have hB : B.re ≤ -(12*Real.pi^2*S4) := by
    rw [hre]
    have hp : eps^2-4 ≤ -3 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hp (show 0 ≤ 4*Real.pi^2*S4 by positivity)
    have hn : 0 ≤ 6*Real.pi*eps*S2 := by positivity
    nlinarith
  have hn : 12*Real.pi^2*S4 ≤ ‖B‖ := by
    have hr := Complex.abs_re_le_norm B
    linarith [neg_le_abs B.re]
  rw [charged_cusp_source_identity heps he, norm_mul, Complex.norm_exp]
  simp only [Complex.div_ofNat_re]
  exact mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le


def chargedPoint (eps : ℝ) : ℂ := Complex.log ((eps:ℂ)+2*Complex.I)/2

theorem chargedPoint_exp {eps : ℝ} (heps : 0 < eps) :
    Complex.exp (2*chargedPoint eps) = (eps:ℂ)+2*Complex.I := by
  rw [chargedPoint, mul_div_cancel₀ _ (by norm_num : (2:ℂ) ≠ 0)]
  apply Complex.exp_log
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith

theorem chargedPoint_mem_strip {eps : ℝ} (heps : 0 < eps) :
    chargedPoint eps ∈ thetaCuspStrip := by
  have ha : |Complex.arg ((eps:ℂ)+2*Complex.I)| < Real.pi/2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using heps))
  change |(Complex.log ((eps:ℂ)+2*Complex.I)/2).im| < Real.pi/4
  rw [Complex.div_ofNat_im, Complex.log_im, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem chargedPoint_re_bounds {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    0 ≤ (chargedPoint eps).re ∧ (chargedPoint eps).re ≤ 1 := by
  have hlo : (2:ℝ) ≤ ‖(eps:ℂ)+2*Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((eps:ℂ)+2*Complex.I)
  have hhi : ‖(eps:ℂ)+2*Complex.I‖ ≤ 3 := by
    calc
      _ ≤ ‖(eps:ℂ)‖+‖2*Complex.I‖ := norm_add_le _ _
      _ ≤ 3 := by simpa [norm_mul, abs_of_pos heps] using (show eps+2 ≤ 3 by linarith)
  have hl0 := Real.log_nonneg (show 1 ≤ ‖(eps:ℂ)+2*Complex.I‖ by linarith)
  have hl1 := Real.log_le_sub_one_of_pos (show 0 < ‖(eps:ℂ)+2*Complex.I‖ by linarith)
  simp only [chargedPoint, Complex.div_ofNat_re, Complex.log_re]
  constructor <;> linarith

theorem chargedPoint_cos_bounds {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    eps/3 ≤ Real.cos (2*(chargedPoint eps).im) ∧
      Real.cos (2*(chargedPoint eps).im) ≤ 1 := by
  have he := congrArg Complex.re (chargedPoint_exp heps)
  have hen := congrArg norm (chargedPoint_exp heps)
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero, add_zero, Complex.add_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.I_im] at he
  have hn : Real.exp (2*(chargedPoint eps).re) ≤ 3 := by
    rw [Complex.norm_exp] at hen
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hen
    rw [hen]
    calc
      _ ≤ ‖(eps:ℂ)‖+‖2*Complex.I‖ := norm_add_le _ _
      _ ≤ 3 := by simpa [norm_mul, abs_of_pos heps] using (show eps+2 ≤ 3 by linarith)
  have hc : 0 < Real.cos (2*(chargedPoint eps).im) := by
    have hz := chargedPoint_mem_strip heps
    change |(chargedPoint eps).im| < Real.pi/4 at hz
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [le_abs_self (chargedPoint eps).im, neg_le_abs (chargedPoint eps).im]
  refine ⟨?_, Real.cos_le_one _⟩
  nlinarith [mul_le_mul_of_nonneg_right hn hc.le]

theorem chargedPoint_source_lower (N : ℕ) (hN : 0 < N) :
    12*Real.pi^2*Real.exp (-4*Real.pi)*(N:ℝ)^5 ≤
      ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖ := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have heps : 0 < 1/(N:ℝ)^2 := by positivity
  have heps1 : 1/(N:ℝ)^2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hr := (chargedPoint_re_bounds heps heps1).1
  have hlow := charged_cusp_source_lower heps heps1 (chargedPoint_exp heps)
  have hblock := fourth_power_block_lower N hN
  have hex : 1 ≤ Real.exp ((chargedPoint (1/(N:ℝ)^2)).re/2) :=
    Real.one_le_exp (by positivity)
  have heq : Real.pi*(1/(N:ℝ)^2) = Real.pi/(N:ℝ)^2 := by ring
  rw [heq] at hlow
  have hp := mul_le_mul_of_nonneg_left hblock (show 0 ≤ 12*Real.pi^2 by positivity)
  have hp2 := mul_le_mul_of_nonneg_right hex
    (show 0 ≤ 12*Real.pi^2*thetaGaussianPowerSum (Real.pi/(N:ℝ)^2) 4 from
      mul_nonneg (by positivity) (thetaGaussianPowerSum_nonneg _ _))
  nlinarith


theorem chargedPoint_source_horizontal_upper (N : ℕ) (hN : 0 < N)
    (s : ℝ) :
    ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖ ≤
      486*(N:ℝ)^5*Real.exp (-s/2) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have heps : 0 < 1/(N:ℝ)^2 := by positivity
  have heps1 : 1/(N:ℝ)^2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  let z := chargedPoint (1/(N:ℝ)^2)
  let c := Real.cos (2*z.im)
  have hz := chargedPoint_mem_strip heps
  change |z.im| < Real.pi/4 at hz
  have hc0 : 0 < c := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [le_abs_self z.im, neg_le_abs z.im]
  have hc := (chargedPoint_cos_bounds heps heps1).1
  change (1/(N:ℝ)^2)/3 ≤ c at hc
  have hi : 1/c ≤ 3*(N:ℝ)^2 := by
    rw [div_le_iff₀ hc0]
    have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*(N:ℝ)^2 by positivity)
    have he : 3*(N:ℝ)^2*((1/(N:ℝ)^2)/3) = 1 := by field_simp
    rw [he] at h
    exact h
  have hi2 : 1/c^2 ≤ 9*(N:ℝ)^4 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1/c) hi 2
    simpa only [div_pow, one_pow, mul_pow, show (3:ℝ)^2=9 by norm_num, ← pow_mul,
      show (2:ℕ)*2=4 by omega] using h
  have hN24 : (N:ℝ)^2 ≤ (N:ℝ)^4 := by
    have hN2 : 1 ≤ (N:ℝ)^2 := by nlinarith
    nlinarith [sq_nonneg ((N:ℝ)^2-1)]
  have hA : 16/c^2+6/c ≤ 162*(N:ℝ)^4 := by
    calc
      _ = 16*(1/c^2)+6*(1/c) := by ring
      _ ≤ 16*(9*(N:ℝ)^4)+6*(3*(N:ℝ)^2) := by gcongr
      _ ≤ _ := by nlinarith
  have hsqrt : Real.sqrt (2/c) ≤ 3*(N:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [show 2/c=2*(1/c) by ring]
  have hC : (16/c^2+6/c)*Real.sqrt (2/c) ≤ 486*(N:ℝ)^5 := by
    calc
      _ ≤ (162*(N:ℝ)^4)*(3*(N:ℝ)) := mul_le_mul hA hsqrt (by positivity) (by positivity)
      _ = _ := by ring
  have hcabs : Real.cos (2*|z.im|)=c := by
    dsimp [c]
    simpa only [abs_mul, abs_two] using Real.cos_abs (2*z.im)
  have hu := source_norm_le_sharp_strip (abs_nonneg z.im) (by linarith : 2*|z.im| < Real.pi/2)
    (z := z+(s:ℂ)) (by simp)
  rw [hcabs] at hu
  have hex : Real.exp (-(z+(s:ℂ)).re/2) ≤ Real.exp (-s/2) := by
    apply Real.exp_le_exp.mpr
    simp only [Complex.add_re, Complex.ofReal_re]
    have hz0 := (chargedPoint_re_bounds heps heps1).1
    change 0 ≤ z.re at hz0
    linarith
  exact hu.trans (mul_le_mul hC hex (by positivity) (by positivity))

end RHTower.ThetaCuspBoundaryAudit
