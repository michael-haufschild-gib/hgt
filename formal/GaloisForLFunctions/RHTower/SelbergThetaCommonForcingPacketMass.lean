import GaloisForLFunctions.RHTower.SelbergThetaNativeMeanCancellation
import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingMass
import Mathlib.Algebra.Polynomial.Roots

/-!
# Native theta packet mass from the arithmetic Cauchy density

Let `alpha q` denote `xiSpectralPoint q`. For native energies in the upper half-plane,
the exact source-pairing formula and the native Gram displacement identity give

`gram q r = (1/pi) * integral density(t) /
  (conj(t^2-alpha(q)^2) * (t^2-alpha(r)^2)) dt`.

The integral is absolutely admitted by the difference of the two admitted scalar
Cauchy transforms. Consequently every finite native packet has squared norm equal
to the integral of its squared rational response against this same nonnegative density.
For distinct squared spectral parameters, a nonzero coefficient vector gives a
nonzero numerator polynomial. Its real zero set is finite. A zero native packet
would therefore make the whole density vanish almost everywhere, contradicting
the diagonal source flux and the nonzero native response.

Thus every nontrivial finite packet in this chamber retains mass, including packets
whose coefficients cancel the common forcing. A cofinal occurrence construction
still requires control of the normalized full residual and its limiting native mass.
-/

open Complex Set Filter MeasureTheory
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
namespace RHTower.SelbergThetaCommonForcingPacketMass
noncomputable section
open SelbergThetaCommonForcing SelbergThetaCommonForcingGram
open SelbergThetaHorizontalBoundary SelbergThetaNativeScalarBoundary

/-- The complete nonnegative arithmetic boundary density. -/
def density (t : ℝ) : ℝ := Xi t ^ 2 * boundaryWeight t

/-- The real-frequency denominator of an actual Xi response. -/
def denominator (q : XiZeroCopy) (t : ℝ) : ℂ := (t:ℂ)^2 - (xiSpectralPoint q)^2

/-- The absolutely admitted native scalar Cauchy integrand. -/
def cauchy (q : XiZeroCopy) (t : ℝ) : ℂ := (density t : ℂ) / denominator q t

/-- The arithmetic density times the two rational response factors. -/
def kernel (q r : XiZeroCopy) (t : ℝ) : ℂ :=
  (density t : ℂ) / (conj (denominator q t) * denominator r t)

theorem density_nonneg (t : ℝ) : 0 ≤ density t :=
  mul_nonneg (sq_nonneg _) (boundaryWeight_bounds t).1

theorem denominator_ne_zero (q : XiZeroCopy)
    (hq : 0 < ((xiSpectralPoint q)^2).im) (t : ℝ) : denominator q t ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  change ((t:ℂ)^2 - (xiSpectralPoint q)^2).im = 0 at hi
  simp only [Complex.sub_im, ← Complex.ofReal_pow, Complex.ofReal_im] at hi
  linarith

theorem gap_ne_zero (q r : XiZeroCopy)
    (hq : 0 < ((xiSpectralPoint q)^2).im)
    (hr : 0 < ((xiSpectralPoint r)^2).im) :
    (xiSpectralPoint r)^2 - conj ((xiSpectralPoint q)^2) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.conj_im,Complex.zero_im] at hi
  linarith

theorem cauchy_integrable (q : XiZeroCopy) : Integrable (cauchy q) := by
  change Integrable (fun t : ℝ => (density t:ℂ)/denominator q t)
  simpa only [denominator,density,Complex.ofReal_mul,Complex.ofReal_pow]
    using native_cauchy_integrable q

theorem conj_cauchy_integrable (q : XiZeroCopy) :
    Integrable (fun t => conj (cauchy q t)) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (cauchy_integrable q)

theorem sourcePairing_cauchy (q : XiZeroCopy) :
    sourcePairing q = (1/(4*(Real.pi:ℂ)))*∫ t : ℝ, cauchy q t := by
  simpa only [cauchy,denominator,density,Complex.ofReal_mul,Complex.ofReal_pow]
    using SelbergThetaNativeMeanCancellation.sourcePairing_eq_cauchy q

theorem cauchy_sub (q r : XiZeroCopy)
    (hq : 0 < ((xiSpectralPoint q)^2).im)
    (hr : 0 < ((xiSpectralPoint r)^2).im) (t : ℝ) :
    cauchy r t - conj (cauchy q t) =
      ((xiSpectralPoint r)^2-conj ((xiSpectralPoint q)^2))*kernel q r t := by
  have hq0 := denominator_ne_zero q hq t
  have hr0 := denominator_ne_zero r hr t
  have hc0 : conj (denominator q t) ≠ 0 := by simpa using hq0
  simp only [cauchy,kernel,map_div₀,Complex.conj_ofReal]
  field_simp
  simp only [denominator,map_sub,map_pow,Complex.conj_ofReal]
  ring

theorem kernel_integrable (q r : XiZeroCopy)
    (hq : 0 < ((xiSpectralPoint q)^2).im)
    (hr : 0 < ((xiSpectralPoint r)^2).im) : Integrable (kernel q r) := by
  have h := ((cauchy_integrable r).sub (conj_cauchy_integrable q)).div_const
    ((xiSpectralPoint r)^2-conj ((xiSpectralPoint q)^2))
  apply h.congr
  exact Eventually.of_forall fun t => by
    change (cauchy r t-conj (cauchy q t)) /
      ((xiSpectralPoint r)^2-conj ((xiSpectralPoint q)^2)) = kernel q r t
    rw [cauchy_sub q r hq hr t]
    exact mul_div_cancel_left₀ _ (gap_ne_zero q r hq hr)

/-- Exact native Gram entry in the upper spectral half-plane. -/
theorem gram_eq_integral (q r : XiZeroCopy)
    (hq : 0 < ((xiSpectralPoint q)^2).im)
    (hr : 0 < ((xiSpectralPoint r)^2).im) :
    gram q r = (1/(Real.pi:ℂ))*∫ t : ℝ, kernel q r t := by
  have hi : ∫ t : ℝ, cauchy r t-conj (cauchy q t) =
      ((xiSpectralPoint r)^2-conj ((xiSpectralPoint q)^2))*∫ t : ℝ, kernel q r t := by
    simp_rw [cauchy_sub q r hq hr]
    exact integral_const_mul _ _
  rw [integral_sub (cauchy_integrable r) (conj_cauchy_integrable q),
    integral_conj] at hi
  have hg := gram_displacement q r
  rw [sourcePairing_cauchy,sourcePairing_cauchy] at hg
  simp only [map_mul,map_div₀,map_one,map_ofNat,Complex.conj_ofReal] at hg
  have he : energy r-conj (energy q) =
      ((xiSpectralPoint r)^2-conj ((xiSpectralPoint q)^2))/4 := by
    simp only [energy,map_div₀,map_add,map_ofNat]
    ring
  rw [he] at hg
  apply mul_left_cancel₀ (gap_ne_zero q r hq hr)
  linear_combination 4*hg + (1/(Real.pi:ℂ))*hi

/-- The finite rational response with the original packet coefficients. -/
def rationalPacket {ι : Type*} [Fintype ι] (q : ι → XiZeroCopy) (c : ι → ℂ)
    (t : ℝ) : ℂ := ∑ i, c i / denominator (q i) t

/-- The full nonnegative squared response density of a finite packet. -/
def packetDensity {ι : Type*} [Fintype ι] (q : ι → XiZeroCopy) (c : ι → ℂ)
    (t : ℝ) : ℝ := density t * Complex.normSq (rationalPacket q c t)

theorem packetDensity_nonneg {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) (t : ℝ) : 0 ≤ packetDensity q c t :=
  mul_nonneg (density_nonneg t) (Complex.normSq_nonneg _)

theorem packetDensity_eq_sum {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) (t : ℝ) :
    (packetDensity q c t : ℂ) = ∑ i, ∑ j, conj (c i)*c j*kernel (q i) (q j) t := by
  simp only [packetDensity,Complex.ofReal_mul,Complex.normSq_eq_conj_mul_self,
    rationalPacket,map_sum,map_div₀]
  rw [← mul_assoc,Finset.mul_sum (a := (density t:ℂ)),Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [kernel,div_eq_mul_inv,mul_inv_rev]
  ring

theorem packetDensity_integrable {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hq : ∀ i, 0 < ((xiSpectralPoint (q i))^2).im) : Integrable (packetDensity q c) := by
  have hsum : Integrable (fun t : ℝ =>
      ∑ i, ∑ j, conj (c i)*c j*kernel (q i) (q j) t) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (kernel_integrable (q i) (q j) (hq i) (hq j)).const_mul _
  have hreal := (Complex.reCLM : ℂ →L[ℝ] ℝ).integrable_comp hsum
  apply hreal.congr
  exact Eventually.of_forall fun t => by
    change (∑ i, ∑ j, conj (c i)*c j*kernel (q i) (q j) t).re = packetDensity q c t
    rw [← packetDensity_eq_sum]
    rfl

/-- The original native packet norm is exactly its arithmetic density integral. -/
theorem packet_norm_sq_eq_integral {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hq : ∀ i, 0 < ((xiSpectralPoint (q i))^2).im) :
    ‖∑ i, c i • vector (q i)‖^2 = (1/Real.pi)*∫ t : ℝ, packetDensity q c t := by
  have hrow (i : ι) : Integrable (fun t : ℝ =>
      ∑ j, conj (c i)*c j*kernel (q i) (q j) t) := by
    apply integrable_finsetSum
    intro j _
    exact (kernel_integrable (q i) (q j) (hq i) (hq j)).const_mul _
  have hint : (∫ t : ℝ, packetDensity q c t : ℝ) =
      (∑ i, ∑ j, conj (c i)*c j*∫ t : ℝ, kernel (q i) (q j) t).re := by
    have he : (∫ t : ℝ, (packetDensity q c t : ℂ)) =
        ∑ i, ∑ j, conj (c i)*c j*∫ t : ℝ, kernel (q i) (q j) t := by
      simp_rw [packetDensity_eq_sum]
      rw [integral_finsetSum _ (fun i _ => hrow i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ =>
        (kernel_integrable (q i) (q j) (hq i) (hq j)).const_mul _)]
      simp_rw [integral_const_mul]
    rw [integral_complex_ofReal] at he
    exact congrArg Complex.re he
  rw [packet_norm_sq,hint]
  simp_rw [gram_eq_integral _ _ (hq _) (hq _)]
  have halg : (∑ i, ∑ j, conj (c i)*c j*
      ((1/(Real.pi:ℂ))*∫ t : ℝ, kernel (q i) (q j) t)) =
      (1/(Real.pi:ℂ))*(∑ i, ∑ j, conj (c i)*c j*∫ t : ℝ, kernel (q i) (q j) t) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [halg]
  simp only [← Complex.ofReal_one,← Complex.ofReal_div,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

open Polynomial in
private def numeratorPoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) : ℂ[X] :=
  ∑ i, C (c i)*∏ j ∈ Finset.univ.erase i, (X^2-C ((xiSpectralPoint (q j))^2))

open Polynomial in
private theorem numeratorPoly_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) (t : ℝ)
    (hq : ∀ i, 0 < ((xiSpectralPoint (q i))^2).im) :
    (numeratorPoly q c).eval (t:ℂ) = (∏ i, denominator (q i) t)*rationalPacket q c t := by
  simp only [numeratorPoly,eval_finsetSum,eval_mul,eval_C,eval_prod,eval_sub,eval_pow,eval_X,
    rationalPacket]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change c i*(∏ j ∈ Finset.univ.erase i, denominator (q j) t) = _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hi := denominator_ne_zero (q i) (hq i) t
  field_simp

open Polynomial in
private theorem numeratorPoly_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hq : Function.Injective (fun i => (xiSpectralPoint (q i))^2))
    (hc : c ≠ 0) : numeratorPoly q c ≠ 0 := by
  intro hzero
  apply hc
  funext m
  have he : (numeratorPoly q c).eval (xiSpectralPoint (q m)) =
      c m * ∏ j ∈ Finset.univ.erase m,
        ((xiSpectralPoint (q m))^2-(xiSpectralPoint (q j))^2) := by
    simp only [numeratorPoly,eval_finsetSum,eval_mul,eval_C,eval_prod,eval_sub,eval_pow,eval_X]
    rw [Finset.sum_eq_single m]
    · intro i _ hi
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ m⟩)
        (sub_self _),mul_zero]
    · intro h
      exact (h (Finset.mem_univ m)).elim
  rw [hzero,eval_zero] at he
  have hp : (∏ j ∈ Finset.univ.erase m,
      ((xiSpectralPoint (q m))^2-(xiSpectralPoint (q j))^2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hq h).symm)
  exact (mul_eq_zero.mp he.symm).resolve_right hp

private theorem rationalPacket_ae_ne_zero {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hq : ∀ i, 0 < ((xiSpectralPoint (q i))^2).im)
    (hinj : Function.Injective (fun i => (xiSpectralPoint (q i))^2))
    (hc : c ≠ 0) : ∀ᵐ t : ℝ, rationalPacket q c t ≠ 0 := by
  classical
  have hfinite : {t : ℝ | rationalPacket q c t = 0}.Finite := by
    have hroots := Polynomial.finite_setOf_isRoot (numeratorPoly_ne_zero q c hinj hc)
    have hpre := hroots.preimage Complex.ofReal_injective.injOn
    apply hpre.subset
    intro t ht
    change (numeratorPoly q c).eval (t:ℂ) = 0
    rw [numeratorPoly_eval q c t hq,ht,mul_zero]
  rw [ae_iff]
  simpa only [not_not] using hfinite.measure_zero volume

private theorem density_not_ae_zero (q : XiZeroCopy)
    (hq : 0 < ((xiSpectralPoint q)^2).im) : ¬ density =ᵐ[volume] 0 := by
  intro hd
  have hc : cauchy q =ᵐ[volume] 0 := by
    filter_upwards [hd] with t ht
    simp only [cauchy,ht,Pi.zero_apply,Complex.ofReal_zero,zero_div]
  have hm : sourcePairing q = 0 := by
    rw [sourcePairing_cauchy,integral_congr_ae hc]
    simp
  have he : 0 < (energy q).im := by
    have heq : (energy q).im = ((xiSpectralPoint q)^2).im/4 := by
      simp [energy,Complex.div_ofNat_im]
    rw [heq]
    positivity
  have hpos := mul_pos he (sq_pos_of_pos (SelbergThetaCommonForcingMass.vector_norm_pos q))
  rw [← sourcePairing_im,hm] at hpos
  exact (lt_irrefl 0) hpos

/-- Distinct native responses in a strict spectral half-plane retain mass in every
nonzero finite combination, including combinations whose coefficients sum to zero. -/
theorem packet_ne_zero {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ)
    (hq : ∀ i, 0 < ((xiSpectralPoint (q i))^2).im)
    (hinj : Function.Injective (fun i => (xiSpectralPoint (q i))^2))
    (hc : c ≠ 0) : (∑ i, c i • vector (q i)) ≠ 0 := by
  intro hv
  have hn := packet_norm_sq_eq_integral q c hq
  rw [hv,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] at hn
  have hi : ∫ t : ℝ, packetDensity q c t = 0 :=
    (mul_eq_zero.mp hn.symm).resolve_left (one_div_ne_zero Real.pi_ne_zero)
  have hae := (integral_eq_zero_iff_of_nonneg (packetDensity_nonneg q c)
    (packetDensity_integrable q c hq)).mp hi
  have hrat := rationalPacket_ae_ne_zero q c hq hinj hc
  have hd : density =ᵐ[volume] 0 := by
    filter_upwards [hae,hrat] with t ht hrt
    exact (mul_eq_zero.mp ht).resolve_right (Complex.normSq_eq_zero.not.mpr hrt)
  have hnempty : Nonempty ι := by
    by_contra h
    apply hc
    funext i
    exact (h ⟨i⟩).elim
  obtain ⟨i⟩ := hnempty
  exact density_not_ae_zero (q i) (hq i) hd

end
end RHTower.SelbergThetaCommonForcingPacketMass
