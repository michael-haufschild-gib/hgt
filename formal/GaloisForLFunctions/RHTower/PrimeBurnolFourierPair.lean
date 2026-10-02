import GaloisForLFunctions.RHTower.PrimeBurnolFiniteOffDiagonalFaithfulness
import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import Mathlib.Analysis.Fourier.FourierTransformDeriv


/-!
# Literal Fourier-paired prime Burnol source

For every finite injective prime-depth packet, the even extensions of its clock-zero Burnol
columns together with their actual Fourier images are linearly independent in physical L2.
The full mixed Gram is consequently nonsingular at clock collision. The proof evaluates the
exact rational Fourier transforms and separates their distinct complex poles after clearing
all denominators; no cross entry is discarded.

The even extension here is unnormalized: its restriction to the positive half-line is exactly
the existing source. This theorem does not identify the new pair with the completed Gamma–Xi
seam, bound cofinal inverse Grams, transfer a Hardy index, or prove a sub-unit estimate.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem integrable_even_of_Ioi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E}
    (he : ∀ x, f (-x) = f x) (hi : IntegrableOn f (Ioi 0)) : Integrable f := by
  have hl : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, he, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hi

private def burnolEvenExponential (a x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) * Complex.exp (-((a : ℂ) * ((|x| : ℝ) : ℂ)))

private theorem integrable_burnolEvenExponential {a : ℝ} (ha : 0 < a) :
    Integrable (burnolEvenExponential a) := by
  apply integrable_even_of_Ioi (by intro x; simp [burnolEvenExponential])
  have h := integrableOn_natPow_mul_cexp (c := (a : ℂ)) ha 1
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  simp [burnolEvenExponential, abs_of_pos (show 0 < x from hx)]

private theorem burnolEvenExponential_fourier_integrand (a w x : ℝ) (hx : 0 < x) :
    Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) *
      burnolEvenExponential a x =
      (x : ℂ) * Complex.exp (-(((a : ℂ) + 2 * Real.pi * w * Complex.I) * x)) := by
  simp only [burnolEvenExponential, abs_of_pos (show 0 < x from hx)]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem burnolEvenExponential_fourier_reflect (a w x : ℝ) :
    Complex.exp ((-2 * Real.pi * (-x) * w : ℝ) * Complex.I) *
      burnolEvenExponential a (-x) =
      Complex.exp ((-2 * Real.pi * x * (-w) : ℝ) * Complex.I) *
        burnolEvenExponential a x := by
  simp only [burnolEvenExponential, abs_neg]
  rw [show -2 * Real.pi * (-x) * w = -2 * Real.pi * x * (-w) by ring]

private theorem fourier_burnolEvenExponential {a : ℝ} (ha : 0 < a) (w : ℝ) :
    𝓕 (burnolEvenExponential a) w =
      1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I)^2 +
      1 / ((a : ℂ) - 2 * Real.pi * w * Complex.I)^2 := by
  let g : ℝ → ℂ := fun x => Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) *
    burnolEvenExponential a x
  have hg : Integrable g := (integrable_burnolEvenExponential ha).bdd_mul (c := 1)
    (by fun_prop) (Filter.Eventually.of_forall fun x => by simp [Complex.norm_exp])
  have hhalf (t : ℝ) :
      (∫ x in Ioi (0 : ℝ), Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) *
        burnolEvenExponential a x) = 1 / ((a : ℂ) + 2 * Real.pi * t * Complex.I)^2 := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), (x : ℂ) *
          Complex.exp (-(((a : ℂ) + 2 * Real.pi * t * Complex.I) * x)) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx =>
          burnolEvenExponential_fourier_integrand a t x hx
      _ = _ := by
        simpa only [pow_one, Nat.factorial_one, Nat.cast_one, one_add_one_eq_two] using
          integral_Ioi_pow_mul_cexp
            (c := (a : ℂ) + 2 * Real.pi * t * Complex.I) (by simpa using ha) 1
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ x, g x) = _
  rw [← integral_add_compl measurableSet_Ioi hg, compl_Ioi]
  rw [show (∫ x in Ioi (0 : ℝ), g x) =
      1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I)^2 from hhalf w]
  congr 1
  rw [← neg_zero, ← integral_comp_neg_Ioi]
  change (∫ x in Ioi (0 : ℝ), Complex.exp ((-2 * Real.pi * (-x) * w : ℝ) * Complex.I) *
    burnolEvenExponential a (-x)) = _
  simp_rw [burnolEvenExponential_fourier_reflect]
  simpa [sub_eq_add_neg] using hhalf (-w)

private theorem fourier_burnolEvenExponential_rational {a : ℝ} (ha : 0 < a) (w : ℝ) :
    𝓕 (burnolEvenExponential a) w =
      2 * ((a : ℂ)^2 - (2 * Real.pi * w)^2) /
        ((a : ℂ)^2 + (2 * Real.pi * w)^2)^2 := by
  rw [fourier_burnolEvenExponential ha]
  have hp : (a : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hm : (a : ℂ) - 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hprod : ((a : ℂ) + 2 * Real.pi * w * Complex.I) *
      ((a : ℂ) - 2 * Real.pi * w * Complex.I) =
      (a : ℂ)^2 + (2 * Real.pi * w)^2 := by
    ring_nf
    simp [Complex.I_sq]
  rw [← hprod, mul_pow]
  field_simp
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

def primeBurnolEvenFeature (pe : Nat.Primes × ℕ) (x : ℝ) : ℂ :=
  primeBurnolWindowFeature pe 0 |x|

theorem continuous_primeBurnolEvenFeature (pe : Nat.Primes × ℕ) :
    Continuous (primeBurnolEvenFeature pe) :=
  (continuous_primeBurnolWindowFeature pe 0).comp continuous_abs

private theorem primeBurnolEvenFeature_eq (pe : Nat.Primes × ℕ) :
    primeBurnolEvenFeature pe = fun x =>
      primeBurnolAmplitude pe * burnolEvenExponential (primeBurnolLogFrequency pe) x := by
  funext x
  simp [primeBurnolEvenFeature, primeBurnolWindowFeature, primeBurnolComplexExponent,
    burnolEvenExponential, mul_assoc]

theorem integrable_primeBurnolEvenFeature (pe : Nat.Primes × ℕ) :
    Integrable (primeBurnolEvenFeature pe) := by
  rw [primeBurnolEvenFeature_eq]
  exact (integrable_burnolEvenExponential (primeBurnolLogFrequency_pos pe)).const_mul _

theorem memLp_primeBurnolEvenFeature (pe : Nat.Primes × ℕ) :
    MemLp (primeBurnolEvenFeature pe) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_primeBurnolEvenFeature pe).aestronglyMeasurable).2
  apply integrable_even_of_Ioi
    (by intro x; simp [primeBurnolEvenFeature, abs_neg])
  apply (integrableOn_norm_sq_primeBurnolWindowFeature pe 0).congr_fun _ measurableSet_Ioi
  intro x hx
  simp [primeBurnolEvenFeature, abs_of_pos (show 0 < x from hx)]

def primeBurnolEvenFeatureLp (pe : Nat.Primes × ℕ) : SoninL2 :=
  (memLp_primeBurnolEvenFeature pe).toLp (primeBurnolEvenFeature pe)

theorem primeBurnolEvenFeatureLp_coeFn (pe : Nat.Primes × ℕ) :
    (primeBurnolEvenFeatureLp pe : ℝ → ℂ) =ᵐ[volume] primeBurnolEvenFeature pe :=
  (memLp_primeBurnolEvenFeature pe).coeFn_toLp

theorem fourier_primeBurnolEvenFeature (pe : Nat.Primes × ℕ) (w : ℝ) :
    𝓕 (primeBurnolEvenFeature pe) w =
      2 * primeBurnolAmplitude pe * ((primeBurnolLogFrequency pe : ℂ)^2 -
        (2 * Real.pi * w)^2) /
      ((primeBurnolLogFrequency pe : ℂ)^2 + (2 * Real.pi * w)^2)^2 := by
  have hscale : 𝓕 (primeBurnolEvenFeature pe) w =
      primeBurnolAmplitude pe * 𝓕 (burnolEvenExponential (primeBurnolLogFrequency pe)) w := by
    rw [primeBurnolEvenFeature_eq, Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul]
    ring
  rw [hscale, fourier_burnolEvenExponential_rational (primeBurnolLogFrequency_pos pe)]
  ring

private theorem continuous_fourier_primeBurnolEvenFeature (pe : Nat.Primes × ℕ) :
    Continuous (𝓕 (primeBurnolEvenFeature pe)) := by
  have heq := funext (fourier_primeBurnolEvenFeature pe)
  rw [heq]
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  apply pow_ne_zero
  have h : (primeBurnolLogFrequency pe)^2 + (2 * Real.pi * x)^2 ≠ 0 := by
    have := primeBurnolLogFrequency_pos pe
    positivity
  exact_mod_cast h

theorem fourier_primeBurnolEvenFeatureLp_coeFn (pe : Nat.Primes × ℕ) :
    (fourierUnitary (primeBurnolEvenFeatureLp pe) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (primeBurnolEvenFeature pe) := by
  have hint : Integrable (primeBurnolEvenFeatureLp pe : ℝ → ℂ) :=
    (integrable_primeBurnolEvenFeature pe).congr (primeBurnolEvenFeatureLp_coeFn pe).symm
  exact (coeFn_fourierTransform_eq_fourierIntegral _ hint).trans
    (Filter.Eventually.of_forall fun x => Real.fourier_congr_ae
      (primeBurnolEvenFeatureLp_coeFn pe) x)

private def fourierDen (pe : Nat.Primes × ℕ) (z : ℂ) : ℂ :=
  (primeBurnolLogFrequency pe : ℂ)^2 + (2 * Real.pi * z)^2

private def fourierNum (pe : Nat.Primes × ℕ) (z : ℂ) : ℂ :=
  2 * primeBurnolAmplitude pe * ((primeBurnolLogFrequency pe : ℂ)^2 - (2 * Real.pi * z)^2)

private def fourierPole (pe : Nat.Primes × ℕ) : ℂ :=
  (primeBurnolLogFrequency pe : ℂ) * Complex.I / (2 * Real.pi)

private theorem scaled_fourierPole (pe : Nat.Primes × ℕ) :
    2 * Real.pi * fourierPole pe = (primeBurnolLogFrequency pe : ℂ) * Complex.I := by
  unfold fourierPole
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

private theorem fourierDen_pole (pe qe : Nat.Primes × ℕ) :
    fourierDen pe (fourierPole qe) =
      (primeBurnolLogFrequency pe : ℂ)^2 - (primeBurnolLogFrequency qe : ℂ)^2 := by
  rw [fourierDen, scaled_fourierPole, mul_pow, Complex.I_sq]
  ring

private theorem fourierDen_self (pe : Nat.Primes × ℕ) : fourierDen pe (fourierPole pe) = 0 := by
  rw [fourierDen_pole, sub_self]

private theorem fourierDen_other {pe qe : Nat.Primes × ℕ} (hne : pe ≠ qe) :
    fourierDen pe (fourierPole qe) ≠ 0 := by
  rw [fourierDen_pole]
  have h : (primeBurnolLogFrequency pe)^2 - (primeBurnolLogFrequency qe)^2 ≠ 0 := by
    intro hz
    have hp := primeBurnolLogFrequency_pos pe
    have hq := primeBurnolLogFrequency_pos qe
    apply hne
    apply primeBurnolLogFrequency_injective
    nlinarith
  exact_mod_cast h

private theorem fourierDen_real_ne (pe : Nat.Primes × ℕ) (x : ℝ) :
    fourierDen pe x ≠ 0 := by
  unfold fourierDen
  have h : (primeBurnolLogFrequency pe)^2 + (2 * Real.pi * x)^2 ≠ 0 := by
    have := primeBurnolLogFrequency_pos pe
    positivity
  exact_mod_cast h

private theorem fourierNum_self_ne (pe : Nat.Primes × ℕ) : fourierNum pe (fourierPole pe) ≠ 0 := by
  rw [fourierNum, scaled_fourierPole, mul_pow, Complex.I_sq]
  have heq : (primeBurnolLogFrequency pe : ℂ)^2 - (primeBurnolLogFrequency pe : ℂ)^2 * -1 =
      2 * (primeBurnolLogFrequency pe : ℂ)^2 := by ring
  rw [heq]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (primeBurnolAmplitude_ne_zero pe))
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (primeBurnolLogFrequency_pos pe).ne')))

private theorem finite_product_clear {N : ℕ} (q : Fin N → ℂ) (i : Fin N) (v : ℂ)
    (hi : q i ≠ 0) :
    (∏ j, q j^2) * (v / q i^2) = v * ∏ j ∈ Finset.univ.erase i, q j^2 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => q j^2) (Finset.mem_univ i)]
  field_simp

/-- Pole separation for the complete literal source/Fourier mixture. -/
private theorem fourier_coefficients_zero {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ)
    (a b : Fin N → ℂ)
    (hz : ∀ x : ℝ, 0 < x →
      (∑ i, a i * primeBurnolEvenFeature (pe i) x) +
        ∑ i, b i * 𝓕 (primeBurnolEvenFeature (pe i)) x = 0) :
    ∀ i, b i = 0 := by
  classical
  let D : ℂ → ℂ := fun z => ∏ i, fourierDen (pe i) z^2
  let H : ℂ → ℂ := fun z => ∑ i, a i * primeBurnolAmplitude (pe i) * z *
    Complex.exp (-((primeBurnolLogFrequency (pe i) : ℂ) * z))
  let F : ℂ → ℂ := fun z => D z * H z +
    ∑ i, (b i * fourierNum (pe i) z) * ∏ j ∈ Finset.univ.erase i, fourierDen (pe j) z^2
  have hdiff : Differentiable ℂ F := by
    dsimp [F, D, H, fourierDen, fourierNum]
    fun_prop
  have hFreal (x : ℝ) (hx : 0 < x) : F x = 0 := by
    have hH : H x = ∑ i, a i * primeBurnolEvenFeature (pe i) x := by
      apply Finset.sum_congr rfl
      intro i _
      simp [primeBurnolEvenFeature, primeBurnolWindowFeature, primeBurnolComplexExponent,
        abs_of_pos hx, mul_assoc]
    have hQ : (∑ i, (b i * fourierNum (pe i) x) *
        ∏ j ∈ Finset.univ.erase i, fourierDen (pe j) x^2) =
        D x * ∑ i, b i * 𝓕 (primeBurnolEvenFeature (pe i)) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [fourier_primeBurnolEvenFeature]
      change _ = D x * (b i * (fourierNum (pe i) x / fourierDen (pe i) x^2))
      rw [← mul_div_assoc]
      exact (finite_product_clear (fun j => fourierDen (pe j) x) i
        (b i * fourierNum (pe i) x) (fourierDen_real_ne (pe i) x)).symm
    change D x * H x + _ = 0
    rw [hH, hQ, ← mul_add, hz x hx, mul_zero]
  have hFall : ∀ z, F z = 0 := fun z =>
    entire_eq_zero_of_ae_vanishing_on_real_interval hdiff (t₀ := 2) (r := 1)
      (by norm_num) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact hFreal x (by have := hx.1; linarith)) z
  intro i
  have hDi : D (fourierPole (pe i)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [fourierDen_self, zero_pow (by decide)]
  have hdrop (j : Fin N) (hji : j ≠ i) :
      (∏ l ∈ Finset.univ.erase j, fourierDen (pe l) (fourierPole (pe i))^2) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)
    rw [fourierDen_self, zero_pow (by decide)]
  have hsum : (∑ j, (b j * fourierNum (pe j) (fourierPole (pe i))) *
      ∏ l ∈ Finset.univ.erase j, fourierDen (pe l) (fourierPole (pe i))^2) =
      (b i * fourierNum (pe i) (fourierPole (pe i))) *
        ∏ l ∈ Finset.univ.erase i, fourierDen (pe l) (fourierPole (pe i))^2 := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hdrop j hji, mul_zero]
    · simp
  have hproduct : (∏ l ∈ Finset.univ.erase i,
      fourierDen (pe l) (fourierPole (pe i))^2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    apply pow_ne_zero
    exact fourierDen_other (fun heq => (Finset.mem_erase.mp hl).1 (pe.injective heq))
  have h := hFall (fourierPole (pe i))
  change D _ * H _ + _ = 0 at h
  rw [hDi, zero_mul, zero_add, hsum] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hproduct)).resolve_right (fourierNum_self_ne (pe i))

private theorem sum_smul_coe {ι : Type*} [Fintype ι]
    (v : ι → SoninL2) (f : ι → ℝ → ℂ)
    (hv : ∀ i, (v i : ℝ → ℂ) =ᵐ[volume] f i) (c : ι → ℂ) :
    ((∑ i, c i • v i : SoninL2) : ℝ → ℂ) =ᵐ[volume] fun x => ∑ i, c i * f i x := by
  have hi (i : ι) : ((c i • v i : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => c i * f i x := by
    filter_upwards [Lp.coeFn_smul (c i) (v i), hv i] with x h1 h2
    simpa only [Pi.smul_apply, smul_eq_mul, h2] using h1
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • v i),
    ae_all_iff.mpr hi] with x hx hix
  rw [hx]
  exact Finset.sum_congr rfl fun i _ => hix i

/-- Both channels live on the actual even physical L2 carrier. -/
theorem primeBurnolEvenFeatureLp_mem_evenSubspace (pe : Nat.Primes × ℕ) :
    primeBurnolEvenFeatureLp pe ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hn := (primeBurnolEvenFeatureLp_coeFn pe).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (primeBurnolEvenFeatureLp pe), hn,
    primeBurnolEvenFeatureLp_coeFn pe] with x hx hn hx'
  rw [hx, hx']
  simpa only [Function.comp_apply, primeBurnolEvenFeature, abs_neg] using hn

/-- Literal source column and its actual Fourier image, before any inverse Gram is taken. -/
def primeBurnolFourierPair {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Fin N ⊕ Fin N → SoninL2 :=
  Sum.elim (fun i => primeBurnolEvenFeatureLp (pe i))
    (fun i => fourierUnitary (primeBurnolEvenFeatureLp (pe i)))

/-- Actual Fourier pairing removes the finite clock-zero collision kernel. -/
theorem primeBurnolFourierPair_linearIndependent {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) : LinearIndependent ℂ (primeBurnolFourierPair pe) := by
  classical
  let raw : Fin N ⊕ Fin N → ℝ → ℂ :=
    Sum.elim (fun i => primeBurnolEvenFeature (pe i))
      (fun i => 𝓕 (primeBurnolEvenFeature (pe i)))
  have hraw (i) : (primeBurnolFourierPair pe i : ℝ → ℂ) =ᵐ[volume] raw i := by
    cases i with
    | inl i => exact primeBurnolEvenFeatureLp_coeFn (pe i)
    | inr i => exact fourier_primeBurnolEvenFeatureLp_coeFn (pe i)
  have hcont (i) : Continuous (raw i) := by
    cases i with
    | inl i => exact continuous_primeBurnolEvenFeature (pe i)
    | inr i => exact continuous_fourier_primeBurnolEvenFeature (pe i)
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcoe := sum_smul_coe (primeBurnolFourierPair pe) raw hraw c
  rw [hc] at hcoe
  have hzraw : (fun x => ∑ j, c j * raw j x) =ᵐ[volume] fun _ => (0 : ℂ) :=
    hcoe.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  have hzpoint : ∀ x : ℝ, (∑ j, c (Sum.inl j) * primeBurnolEvenFeature (pe j) x) +
      ∑ j, c (Sum.inr j) * 𝓕 (primeBurnolEvenFeature (pe j)) x = 0 := by
    have heq := Measure.eq_of_ae_eq hzraw
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (hcont j))) continuous_const
    intro x
    simpa only [Fintype.sum_sum_type, raw, Sum.elim_inl, Sum.elim_inr] using congrFun heq x
  have hb := fourier_coefficients_zero pe (fun j => c (Sum.inl j))
    (fun j => c (Sum.inr j)) (fun x _ => hzpoint x)
  have haRaw (x : ℝ) (hx : 0 < x) :
      (∑ j, c (Sum.inl j) * primeBurnolWindowFeature (pe j) 0 x) = 0 := by
    have h := hzpoint x
    simpa only [hb, zero_mul, Finset.sum_const_zero, add_zero,
      primeBurnolEvenFeature, abs_of_pos hx] using h
  have haSum : (∑ j, c (Sum.inl j) • primeBurnolWindowFeatureLp (pe j) 0) = 0 := by
    apply Lp.ext
    have hs := coeFn_finset_sum_smul_primeBurnolWindowFeatureLp
      Finset.univ (fun j => c (Sum.inl j)) pe (fun _ => 0)
    have hzero : (fun x => ∑ j, c (Sum.inl j) * primeBurnolWindowFeature (pe j) 0 x)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => (0 : ℂ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact haRaw x hx
    exact hs.trans (hzero.trans ((Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))).symm))
  cases i with
  | inl i =>
    exact (Fintype.linearIndependent_iff.mp
      (primeBurnolWindowFeatureLp_linearIndependent pe pe.injective (fun _ => 0)))
      (fun j => c (Sum.inl j)) haSum i
  | inr i => exact hb i

/-- Complete source/Fourier Gram, retaining every mixed prime and Fourier cross entry. -/
def primeBurnolFourierPairGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ := Matrix.gram ℂ (primeBurnolFourierPair pe)

theorem det_primeBurnolFourierPairGram_ne_zero {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) : (primeBurnolFourierPairGram pe).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (primeBurnolFourierPair_linearIndependent pe)

end RHTower
