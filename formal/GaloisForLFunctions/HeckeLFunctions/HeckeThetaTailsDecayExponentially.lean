import GaloisForLFunctions.HeckeLFunctions.HeckeThetaHasAFiniteFourierTransform
import GaloisForLFunctions.HTGeometry.NumberFieldIdealThetaDecay

/-!
# Zero modes and exponential tails of Hecke theta

The zero value of a parity Gaussian is determined by its degree. Multiplicative
character orthogonality then identifies the exact physical and dual zero terms.
A fixed half-rate Gaussian majorizes every parity kernel for parameters at least
one. The arithmetic Gaussian-tail estimate therefore gives exponential decay of
the remaining physical and finite-Fourier theta sums, uniformly over bounded
place profiles. Every finite weight bound is discharged for the actual Hecke
character or its explicit finite Fourier coefficients.
-/

noncomputable section
open NumberField NumberField.InfinitePlace
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson

section Euclidean
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Parity degree vanishes exactly when every coordinate is even. -/
theorem parityDegree_eq_zero_iff (ε : ι → Bool) :
    parityDegree ε = 0 ↔ ∀ i, ε i = false := by
  rw [parityDegree, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies]
  apply forall_congr'
  intro i
  cases ε i <;> simp

/-- A parity Gaussian has zero value at the origin unless its degree is zero. -/
theorem parityGaussian_zero (ε : ι → Bool) (t : ℝ) :
    parityGaussian ε t 0 = if parityDegree ε = 0 then 1 else 0 := by
  rw [parityGaussian]
  simp only [gaussianKernel, norm_zero, Complex.ofReal_zero,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, Complex.exp_zero, mul_one]
  by_cases h : parityDegree ε = 0
  · have hi := (parityDegree_eq_zero_iff ε).mp h
    simp only [if_pos h, parityMonomial, hi, Bool.toNat_false, pow_zero,
      Finset.prod_const_one]
  · have hn : ¬∀ i, ε i = false := fun hh => h ((parityDegree_eq_zero_iff ε).mpr hh)
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    have ht : ε i = true := by cases he : ε i <;> simp_all
    rw [if_neg h, parityMonomial]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [ht])

/-- One half-rate Gaussian constant bounds all parity kernels for parameters at least one. -/
theorem exists_uniform_parityGaussian_majorant (ε : ι → Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ x : E,
      ‖parityGaussian ε t x‖ ≤ C * ‖gaussianKernel (Real.pi * (t / 2)) x‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_parityGaussian_norm_bound ε (by norm_num : (0 : ℝ) < 1)
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have hb := hbound x
  rw [norm_gaussianKernel] at hb
  calc
    _ = ‖parityGaussian ε 1 x‖ * Real.exp (-(Real.pi * (t - 1)) * ‖x‖^2) := by
      rw [parityGaussian, parityGaussian, norm_mul, norm_mul, norm_gaussianKernel,
        norm_gaussianKernel, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (C * Real.exp (-(Real.pi * (1 / 2)) * ‖x‖^2)) *
        Real.exp (-(Real.pi * (t - 1)) * ‖x‖^2) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = C * Real.exp (-(Real.pi * (t - 1 / 2)) * ‖x‖^2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      rw [norm_gaussianKernel]
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg (Real.pi_pos.le) (sq_nonneg ‖x‖)
      nlinarith only [mul_nonneg (sub_nonneg.mpr ht) h]

end Euclidean

variable {K : Type*} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "ι" => numberFieldMixedRealCoordinateIndex K

/-- The sum of the norms of all nonzero parity-Gaussian ideal terms. -/
def idealParityNormTail (I : FI) (ε : ι → Bool) (y : InfinitePlace K → ℝ) (t : ℝ) : ℝ :=
  ∑' a : I, if (a : K) = 0 then 0 else
    ‖parityGaussian ε t (numberFieldTraceCoordinates
      (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))‖

/-- Nonzero ideal parity norms decay exponentially, uniformly over upper-bounded place profiles. -/
theorem exists_uniform_exponential_idealParityNormTail (I : FIˣ) (ε : ι → Bool) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ y : InfinitePlace K → ℝ, (∀ w, y w ≤ M) →
      ∀ t : ℝ, 2 ≤ t → idealParityNormTail (I : FI) ε y t ≤ C * Real.exp (-c * t) := by
  obtain ⟨A, hA, hmajor⟩ := exists_uniform_parityGaussian_majorant ε
  obtain ⟨B, c, hB, hc, htail⟩ := exists_uniform_exponential_numberFieldIdealTheta_tail I M
  refine ⟨A*B, c/2, mul_pos hA hB, half_pos hc, ?_⟩
  intro y hy t ht
  have ht1 : 1 ≤ t := le_trans (by norm_num) ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hthalf : 1 ≤ t/2 := by linarith only [ht]
  have hps : Summable (fun a : (I : FI) => if (a : K) = 0 then 0 else
      ‖parityGaussian ε t (numberFieldTraceCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))‖) := by
    apply Summable.of_nonneg_of_le (fun a => by split_ifs <;> positivity)
      (fun a => ?_) (summable_norm_parityGaussian_fractionalIdeal I ε y htpos)
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hgs : Summable (fun a : (I : FI) => if (a : K) = 0 then 0 else
      Real.exp (-(Real.pi * (t / 2)) * ‖numberFieldTraceCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖^2)) := by
    apply Summable.of_nonneg_of_le (fun a => by split_ifs <;> positivity)
      (fun a => ?_) (summable_numberFieldScaledIdealTheta I y (half_pos htpos))
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hp (a : (I : FI)) :
      (if (a : K) = 0 then 0 else ‖parityGaussian ε t (numberFieldTraceCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))‖) ≤
      A * (if (a : K) = 0 then 0 else Real.exp (-(Real.pi * (t / 2)) *
        ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖^2)) := by
    split_ifs
    · simp only [mul_zero, le_refl]
    · simpa only [norm_gaussianKernel] using hmajor t ht1
        (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))
  calc
    _ ≤ ∑' a : (I : FI), A * (if (a : K) = 0 then 0 else
        Real.exp (-(Real.pi * (t / 2)) * ‖numberFieldTraceCoordinates
          (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖^2)) :=
      hps.tsum_le_tsum hp (hgs.mul_left A)
    _ = A * (numberFieldScaledIdealTheta (I : FI) y (t / 2) - 1) := by
      rw [tsum_mul_left, numberFieldScaledIdealTheta_sub_one_eq I y (half_pos htpos)]
    _ ≤ A * (B * Real.exp (-c*(t / 2))) :=
      mul_le_mul_of_nonneg_left (htail y hy (t / 2) hthalf).2 hA.le
    _ = _ := by
      rw [show -c*(t / 2) = -(c/2)*t by ring, mul_assoc]


/-- A bounded coefficient family is controlled by the nonzero parity norm tail. -/
private theorem weighted_idealParity_tail_bound (I : FIˣ) (ε : ι → Bool)
    (w : ↥(I : FI) → ℂ) (B : ℝ) (hw : ∀ a, ‖w a‖ ≤ B)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(∑' a : (I : FI), w a * parityGaussian ε t (numberFieldTraceCoordinates
      (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))) -
      w ⟨0,(I : FI).zero_mem⟩ * parityGaussian ε t 0‖ ≤
      B * idealParityNormTail (I : FI) ε y t := by
  let F (a : (I : FI)) := parityGaussian ε t (numberFieldTraceCoordinates
    (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))
  let z : (I : FI) := ⟨0,(I : FI).zero_mem⟩
  have hs : Summable (fun a : (I : FI) => ‖F a‖) :=
    summable_norm_parityGaussian_fractionalIdeal I ε y ht
  have hbound (a : (I : FI)) : ‖w a * F a‖ ≤ B * ‖F a‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hw a) (norm_nonneg _)
  have hws := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hs.mul_left B)
  have he := hws.of_norm.tsum_eq_add_tsum_ite z
  have hz : F z = parityGaussian ε t 0 := by
    dsimp only [F,z]
    simp only [map_zero]
  rw [hz] at he
  simp only [Subtype.ext_iff] at he
  have he' : (∑' a : (I : FI), w a * F a) - w z * parityGaussian ε t 0 =
      ∑' a : (I : FI), if (a : K) = 0 then 0 else w a * F a :=
    sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))
  change ‖(∑' a : (I : FI), w a * F a) - w z * parityGaussian ε t 0‖ ≤ _
  rw [he']
  have hp : Summable (fun a : (I : FI) => if (a : K) = 0 then 0 else ‖F a‖) := by
    apply Summable.of_nonneg_of_le (fun a => by split_ifs <;> positivity) (fun a => ?_) hs
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  calc
    _ ≤ ∑' a : (I : FI), B * (if (a : K) = 0 then 0 else ‖F a‖) := by
      apply tsum_of_norm_bounded (hp.mul_left B).hasSum
      intro a
      split_ifs
      · simp only [norm_zero, mul_zero, le_refl]
      · exact hbound a
    _ = _ := tsum_mul_left

variable (𝔪 : Modulus K)

/-- The norm-tail estimate survives every bounded coefficient family. -/
private theorem exists_uniform_exponential_weighted_idealParity_tail
    (I : FI) (hI : I ≠ 0) (ε : ι → Bool) (w : I → ℂ) (B : ℝ)
    (hw : ∀ a, ‖w a‖ ≤ B) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ y : InfinitePlace K → ℝ, (∀ v, y v ≤ M) →
      ∀ t : ℝ, 2 ≤ t →
        ‖(∑' a : I, w a * parityGaussian ε t (numberFieldTraceCoordinates
          (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))) -
          w ⟨0, I.zero_mem⟩ * parityGaussian ε t 0‖ ≤ C * Real.exp (-c * t) := by
  let J : FIˣ := Units.mk0 I hI
  obtain ⟨A, c, hA, hc, htail⟩ := exists_uniform_exponential_idealParityNormTail J ε M
  have hB : 0 ≤ B := (norm_nonneg (w ⟨0, I.zero_mem⟩)).trans (hw _)
  refine ⟨(B+1)*A, c, mul_pos (by linarith only [hB]) hA, hc, ?_⟩
  intro y hy t ht
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht
  calc
    _ ≤ B * idealParityNormTail I ε y t := weighted_idealParity_tail_bound J ε w B hw y htpos
    _ ≤ B * (A * Real.exp (-c * t)) := mul_le_mul_of_nonneg_left (htail y hy t ht) hB
    _ ≤ (B+1) * (A * Real.exp (-c * t)) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (mul_pos hA (Real.exp_pos _)).le
    _ = _ := by rw [mul_assoc]

/-- The finite weight at zero survives exactly for the unit finite modulus. -/
theorem integralHeckeWeight_zero (ψ : HeckeCharacter 𝔪) :
    integralHeckeWeight 𝔪 ψ 0 = if 𝔪.fin = ⊤ then 1 else 0 := by
  rw [integralHeckeWeight, map_zero]
  by_cases h : 𝔪.fin = ⊤
  · have hz : (0 : 𝓞 K ⧸ 𝔪.fin) = 1 := by
      change Ideal.Quotient.mk 𝔪.fin 0 = Ideal.Quotient.mk 𝔪.fin 1
      apply Ideal.Quotient.eq.mpr
      rw [h]
      exact Submodule.mem_top
    rw [hz, map_one, if_pos h]
  · letI : Nontrivial (𝓞 K ⧸ 𝔪.fin) := Ideal.Quotient.nontrivial_iff.mpr h
    rw [(finiteHeckeWeight 𝔪 ψ).map_zero, if_neg h]

/-- The physical zero term, independent of the place profile and Gaussian parameter. -/
def heckeThetaConstant (ψ : HeckeCharacter 𝔪) : ℂ :=
  if 𝔪.fin = ⊤ ∧ parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 then 1 else 0

/-- The actual physical zero term is exactly the classified constant. -/
theorem heckeThetaKernel_zero (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) (t : ℝ) :
    heckeThetaKernel 𝔪 ψ y t 0 = heckeThetaConstant 𝔪 ψ := by
  rw [heckeThetaKernel]
  simp only [map_zero]
  rw [integralHeckeWeight_zero, parityGaussian_zero]
  by_cases hm : 𝔪.fin = ⊤ <;>
    by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 <;>
    simp only [heckeThetaConstant, hm, hp, and_self, and_false, and_true,
      if_true, if_false, zero_mul, mul_zero, one_mul]

/-- The Fourier zero coefficient vanishes for a nontrivial finite character; otherwise it counts units. -/
theorem finiteHeckeFourierCoefficient_zero {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (ψ : HeckeCharacter 𝔪) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ 0 =
      if finiteHeckeWeight 𝔪 ψ = 1 then (Nat.card (𝓞 K ⧸ 𝔪.fin)ˣ : ℂ) else 0 := by
  letI := 𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔪.fin)
  rw [finiteHeckeFourierCoefficient, tsum_fintype]
  simp only [numberFieldTracePhase, mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one]
  by_cases h : finiteHeckeWeight 𝔪 ψ = 1
  · rw [if_pos h, h, MulChar.sum_one_eq_card_units, Nat.card_eq_fintype_card]
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h]

/-- The dual zero term counts residue units exactly when both finite character and parity are trivial. -/
def heckeDualThetaConstant (ψ : HeckeCharacter 𝔪) : ℂ :=
  if parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 ∧ finiteHeckeWeight 𝔪 ψ = 1
    then (Nat.card (𝓞 K ⧸ 𝔪.fin)ˣ : ℂ) else 0

/-- The actual finite Fourier-weighted zero term is exactly the classified dual constant. -/
theorem heckeDualTheta_zero_term {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) (t : ℝ) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ 0 * heckeParityKernel 𝔪 ψ y t 0 =
      heckeDualThetaConstant 𝔪 ψ := by
  rw [finiteHeckeFourierCoefficient_zero, heckeParityKernel]
  simp only [map_zero]
  rw [parityGaussian_zero]
  by_cases hχ : finiteHeckeWeight 𝔪 ψ = 1 <;>
    by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 <;>
    simp only [heckeDualThetaConstant, hχ, hp, and_self, and_false, and_true,
      if_true, if_false, mul_zero, mul_one]

/-- Every integral-ideal Hecke theta approaches its zero term exponentially and uniformly. -/
theorem exists_uniform_exponential_heckeIdealTheta_tail (ψ : HeckeCharacter 𝔪)
    (b : Ideal (𝓞 K)) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ y : InfinitePlace K → ℝ, (∀ v, y v ≤ M) →
      ∀ t : ℝ, 2 ≤ t →
        ‖heckeIdealTheta 𝔪 ψ b y t - heckeThetaConstant 𝔪 ψ‖ ≤ C * Real.exp (-c * t) := by
  by_cases hb0 : b = ⊥
  · subst b
    refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro y _ t _
    have hzero : heckeIdealTheta 𝔪 ψ ⊥ y t = heckeThetaConstant 𝔪 ψ := by
      calc
        _ = heckeThetaKernel 𝔪 ψ y t 0 := by
          apply tsum_eq_single (0 : (⊥ : Ideal (𝓞 K)))
          intro a ha
          have ha0 : a = 0 := by
            apply Subtype.ext
            exact a.2
          exact (ha ha0).elim
        _ = _ := heckeThetaKernel_zero 𝔪 ψ y t
    rw [hzero, sub_self, norm_zero]
    positivity
  · have hbFI : (b : FI) ≠ 0 := by
      rw [← coe_idealUnit hb0]
      exact (idealUnit hb0).ne_zero
    let e := integralIdealEquivFractional b
    let w (a : (b : FI)) : ℂ := integralHeckeWeight 𝔪 ψ (e.symm a : 𝓞 K)
    obtain ⟨C, c, hC, hc,hbound⟩ := exists_uniform_exponential_weighted_idealParity_tail
      (b : FI) hbFI (heckeCoordinateParity 𝔪 ψ) w 1
      (fun a => norm_integralHeckeWeight_le_one 𝔪 ψ _) M
    refine ⟨C, c, hC, hc,?_⟩
    intro y hy t ht
    have hsum : (∑' a : (b : FI), w a * parityGaussian (heckeCoordinateParity 𝔪 ψ) t
        (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))) =
        heckeIdealTheta 𝔪 ψ b y t := by
      calc
        _ = ∑' a : b, w (e a) * parityGaussian (heckeCoordinateParity 𝔪 ψ) t
            (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y
              (mixedEmbedding K (e a : K)))) :=
          (e.tsum_eq (fun a : (b : FI) => w a * parityGaussian (heckeCoordinateParity 𝔪 ψ) t
            (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y
              (mixedEmbedding K (a : K)))))).symm
        _ = _ := by
          apply tsum_congr
          intro a
          simp only [w, e.symm_apply_apply]
          rfl
    have hz : w ⟨0,(b : FI).zero_mem⟩ * parityGaussian (heckeCoordinateParity 𝔪 ψ) t 0 =
        heckeThetaConstant 𝔪 ψ := by
      have he : e.symm ⟨0,(b : FI).zero_mem⟩ = 0 := by
        apply e.injective
        rw [e.apply_symm_apply]
        apply Subtype.ext
        rfl
      have hwz : w ⟨0,(b : FI).zero_mem⟩ = integralHeckeWeight 𝔪 ψ 0 := by
        change integralHeckeWeight 𝔪 ψ (e.symm ⟨0,(b : FI).zero_mem⟩ : 𝓞 K) = _
        rw [he]
        rfl
      rw [hwz]
      simpa only [heckeThetaKernel, map_zero] using heckeThetaKernel_zero 𝔪 ψ y t
    have h := hbound y hy t ht
    rw [hsum, hz] at h
    exact h

/-- The finite Fourier-weighted theta sum on the arithmetic trace-dual ideal. -/
def heckeDualIdealTheta {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) (t : ℝ) : ℂ :=
  ∑' a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI),
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) * heckeParityKernel 𝔪 ψ y t (a : K)

/-- The actual dual Hecke theta approaches its zero term exponentially and uniformly. -/
theorem exists_uniform_exponential_heckeDualIdealTheta_tail {b : Ideal (𝓞 K)}
    (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ y : InfinitePlace K → ℝ, (∀ v, y v ≤ M) →
      ∀ t : ℝ, 2 ≤ t →
        ‖heckeDualIdealTheta 𝔪 hb ψ y t - heckeDualThetaConstant 𝔪 ψ‖ ≤ C * Real.exp (-c * t) := by
  have hJ : ((𝔪.fin * b : Ideal (𝓞 K)) : FI) ≠ 0 := by
    rw [← coe_idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)]
    exact (idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)).ne_zero
  let I := FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)
  have hI : I ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ hJ
  let w (a : I) : ℂ := finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K)
  obtain ⟨C, c, hC, hc,hbound⟩ := exists_uniform_exponential_weighted_idealParity_tail
    I hI (heckeCoordinateParity 𝔪 ψ) w (Ideal.absNorm 𝔪.fin : ℝ)
    (fun a => norm_finiteHeckeFourierCoefficient_le 𝔪 hb ψ (a : K)) M
  refine ⟨C, c, hC, hc,?_⟩
  intro y hy t ht
  have h := hbound y hy t ht
  change ‖heckeDualIdealTheta 𝔪 hb ψ y t - finiteHeckeFourierCoefficient 𝔪 hb ψ 0 *
    parityGaussian (heckeCoordinateParity 𝔪 ψ) t 0‖ ≤ _ at h
  have hz := heckeDualTheta_zero_term 𝔪 hb ψ y t
  simp only [heckeParityKernel, map_zero] at hz
  rw [hz] at h
  exact h


end GaloisForLFunctions.HeckeLFunctions
