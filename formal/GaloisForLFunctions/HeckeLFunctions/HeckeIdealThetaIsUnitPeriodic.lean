import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersSplitIntoFiniteCharactersAndRealParities
import GaloisForLFunctions.HTGeometry.ParityGaussianPoisson
import GaloisForLFunctions.HTGeometry.NumberFieldScaledIdealTheta

/-!
# Hecke ideal theta is periodic in global-unit logarithms

A ray class character supplies a bounded multiplicative weight on integral
residues and a parity monomial at the real places. Scaling by a unit logarithm
and multiplying the argument by that unit introduces reciprocal finite and
infinite character factors. Their proved global-unit relation makes the theta
kernel invariant. A Gaussian majorant proves absolute convergence over every
integral ideal, and unit reindexing proves periodicity of the actual sum.
-/

noncomputable section
open NumberField NumberField.InfinitePlace
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local notation "ι" => numberFieldMixedRealCoordinateIndex K

/-- The finite residue character, extended by zero on nonunits. -/
def finiteHeckeWeight (ψ : HeckeCharacter 𝔪) : MulChar (𝓞 K ⧸ 𝔪.fin) ℂ :=
  MulChar.ofUnitHom (finiteResidueCharacter 𝔪 ψ)

theorem finiteHeckeWeight_unit (ψ : HeckeCharacter 𝔪) (a : (𝓞 K ⧸ 𝔪.fin)ˣ) :
    finiteHeckeWeight 𝔪 ψ (a : 𝓞 K ⧸ 𝔪.fin) = finiteResidueCharacter 𝔪 ψ a :=
  MulChar.ofUnitHom_coe _ _

/-- Global-unit reduction agrees with the quotient ring homomorphism. -/
theorem reduce_globalUnit (u : (𝓞 K)ˣ) :
    reduce 𝔪 (globalUnitPrimeTo 𝔪 u) = Units.map (Ideal.Quotient.mk 𝔪.fin).toMonoidHom u := by
  have hu := not_mem_of_isUnit_mk 𝔪 (u.isUnit.map (Ideal.Quotient.mk 𝔪.fin))
  have h1 := not_mem_of_isUnit_mk 𝔪
    (show IsUnit (Ideal.Quotient.mk 𝔪.fin (1 : 𝓞 K)) by simp)
  rw [reduce_eq 𝔪 (globalUnitPrimeTo 𝔪 u) hu h1 (by simp [globalUnitPrimeTo])]
  have hunit : unitMod 𝔪 h1 = 1 := by ext; simp [coe_unitMod]
  rw [hunit, inv_one, mul_one]
  ext
  rfl

/-- The finite character evaluated on the residue of an algebraic integer. -/
def integralHeckeWeight (ψ : HeckeCharacter 𝔪) (a : 𝓞 K) : ℂ :=
  finiteHeckeWeight 𝔪 ψ (Ideal.Quotient.mk 𝔪.fin a)

/-- Finite Hecke weights have norm at most one, including for the trivial residue ring. -/
theorem norm_finiteHeckeWeight_le_one (ψ : HeckeCharacter 𝔪) (a : 𝓞 K ⧸ 𝔪.fin) :
    ‖finiteHeckeWeight 𝔪 ψ a‖ ≤ 1 := by
  letI := 𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [finiteHeckeWeight_unit]
    exact (norm_char_eq_one (finiteResidueCharacter 𝔪 ψ) u).le
  · rw [(finiteHeckeWeight 𝔪 ψ).map_nonunit ha, norm_zero]
    exact zero_le_one

theorem norm_integralHeckeWeight_le_one (ψ : HeckeCharacter 𝔪) (a : 𝓞 K) :
    ‖integralHeckeWeight 𝔪 ψ a‖ ≤ 1 :=
  norm_finiteHeckeWeight_le_one 𝔪 ψ _

theorem integralHeckeWeight_eq_zero (ψ : HeckeCharacter 𝔪) (a : 𝓞 K)
    (ha : ¬IsUnit (Ideal.Quotient.mk 𝔪.fin a)) : integralHeckeWeight 𝔪 ψ a = 0 :=
  (finiteHeckeWeight 𝔪 ψ).map_nonunit ha

theorem integralHeckeWeight_mul (ψ : HeckeCharacter 𝔪) (a b : 𝓞 K) :
    integralHeckeWeight 𝔪 ψ (a * b) = integralHeckeWeight 𝔪 ψ a * integralHeckeWeight 𝔪 ψ b := by
  simp only [integralHeckeWeight, map_mul]

theorem integralHeckeWeight_globalUnit (ψ : HeckeCharacter 𝔪) (u : (𝓞 K)ˣ) :
    integralHeckeWeight 𝔪 ψ (u : 𝓞 K) =
      finiteResidueCharacter 𝔪 ψ (reduce 𝔪 (globalUnitPrimeTo 𝔪 u)) := by
  rw [reduce_globalUnit]
  exact finiteHeckeWeight_unit 𝔪 ψ (Units.map (Ideal.Quotient.mk 𝔪.fin).toMonoidHom u)

/-- The finite weight cancels the real parity signs on every global unit. -/
theorem integralHeckeWeight_mul_parities_unit (ψ : HeckeCharacter 𝔪) (u : (𝓞 K)ˣ) :
    integralHeckeWeight 𝔪 ψ (u : 𝓞 K) *
      ∏ w : 𝔪.inf,
        ((signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) w : ℤ) : ℂ) ^
          heckeParity 𝔪 ψ w = 1 := by
  rw [integralHeckeWeight_globalUnit]
  exact finite_character_mul_parities_globalUnit 𝔪 ψ u

/-- The real-place parities in trace coordinates; all complex coordinates have parity zero. -/
def heckeCoordinateParity (ψ : HeckeCharacter 𝔪) : ι → Bool
  | Sum.inl w => if h : w ∈ 𝔪.inf then decide (heckeParity 𝔪 ψ ⟨w,h⟩ = 1) else false
  | Sum.inr _ => false

/-- The product of the selected real coordinates with their character parities. -/
def heckeRealMonomial (ψ : HeckeCharacter 𝔪) (z : mixedEmbedding.mixedSpace K) : ℂ :=
  ∏ w : 𝔪.inf, (z.1 w.1 : ℂ) ^ heckeParity 𝔪 ψ w

theorem heckeParity_decide (ψ : HeckeCharacter 𝔪) (w : 𝔪.inf) :
    (decide (heckeParity 𝔪 ψ w = 1)).toNat = heckeParity 𝔪 ψ w := by
  have h := heckeParity_le_one 𝔪 ψ w
  interval_cases hε : heckeParity 𝔪 ψ w <;> simp

/-- The Euclidean parity monomial is exactly the arithmetic real-place product. -/
theorem parityMonomial_heckeCoordinateParity (ψ : HeckeCharacter 𝔪)
    (z : mixedEmbedding.mixedSpace K) :
    parityMonomial (heckeCoordinateParity 𝔪 ψ) (numberFieldTraceCoordinates z) =
      heckeRealMonomial 𝔪 ψ z := by
  rw [parityMonomial, Fintype.prod_sum_type]
  simp only [heckeCoordinateParity, Bool.toNat_false, pow_zero, Finset.prod_const_one,
    mul_one]
  have heq (w : {w : InfinitePlace K // w.IsReal}) :
      ((numberFieldTraceCoordinates z) (Sum.inl w) : ℂ) ^
        (if h : w ∈ 𝔪.inf then decide (heckeParity 𝔪 ψ ⟨w,h⟩ = 1) else false).toNat =
      if h : w ∈ 𝔪.inf then (z.1 w : ℂ)^heckeParity 𝔪 ψ ⟨w,h⟩ else 1 := by
    split_ifs with h
    · rw [heckeParity_decide, numberFieldTraceCoordinates_apply]
      change (((1 : ℝ) * z.1 w : ℝ) : ℂ)^heckeParity 𝔪 ψ ⟨w,h⟩ = _
      rw [one_mul]
    · simp
  simp_rw [heq]
  rw [Fintype.prod_dite]
  simp only [Finset.prod_const_one, mul_one, heckeRealMonomial]

omit [NumberField K] in
/-- A unit logarithm removes the absolute value of a real unit embedding, leaving its sign. -/
theorem real_embedding_scaled_unit (y : InfinitePlace K → ℝ) (u : (𝓞 K)ˣ)
    (a : K) (w : {w : InfinitePlace K // w.IsReal}) :
    (numberFieldMixedPlaceScale (y + numberFieldUnitPlaceLogEmbeddings u)
      (mixedEmbedding K (((u : 𝓞 K) : K) * a))).1 w =
    ((signAt K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) w : ℤ) : ℝ) *
      (numberFieldMixedPlaceScale y (mixedEmbedding K a)).1 w := by
  have hu : 0 < w.1 (((u : 𝓞 K) : K)) := by
    rw [InfinitePlace.pos_iff]
    norm_cast
    exact u.ne_zero
  have hn := norm_embedding_of_isReal w.2 (((u : 𝓞 K) : K))
  rw [Real.norm_eq_abs] at hn
  change Real.exp (-((y + numberFieldUnitPlaceLogEmbeddings u) w.1)) *
      embedding_of_isReal w.2 (((u : 𝓞 K) : K) * a) = _
  simp only [Pi.add_apply, numberFieldUnitPlaceLogEmbeddings, neg_add_rev,
    Real.exp_add, Real.exp_neg, Real.exp_log hu, map_mul]
  have he : embedding_of_isReal w.2 (((u : 𝓞 K) : K)) ≠ 0 := by
    exact (map_ne_zero _).mpr (by norm_cast; exact u.ne_zero)
  change _ = (((if 0 < embedding_of_isReal w.2 (((u : 𝓞 K) : K))
    then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℝ) *
    (Real.exp (-y w.1) * embedding_of_isReal w.2 a)
  rcases he.lt_or_gt with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)]
    rw [abs_of_neg hneg] at hn
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    rw [← hn, Real.exp_neg]
    field_simp
  · rw [if_pos hpos]
    rw [abs_of_pos hpos] at hn
    simp only [Units.val_one, Int.cast_one, one_mul]
    rw [← hn, Real.exp_neg]
    field_simp

/-- Unit-log scaling multiplies the real monomial by the character parity signs. -/
theorem heckeRealMonomial_unit (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (u : (𝓞 K)ˣ) (a : K) :
    heckeRealMonomial 𝔪 ψ (numberFieldMixedPlaceScale
      (y + numberFieldUnitPlaceLogEmbeddings u) (mixedEmbedding K (((u : 𝓞 K) : K) * a))) =
    (∏ w : 𝔪.inf,
      ((signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) w : ℤ) : ℂ) ^
        heckeParity 𝔪 ψ w) *
      heckeRealMonomial 𝔪 ψ (numberFieldMixedPlaceScale y (mixedEmbedding K a)) := by
  simp only [heckeRealMonomial, real_embedding_scaled_unit, Complex.ofReal_mul,
    Complex.ofReal_intCast, mul_pow, Finset.prod_mul_distrib]
  rfl

/-- A half-rate Gaussian majorizes the parity kernel on every nonzero fractional ideal. -/
theorem summable_norm_parityGaussian_fractionalIdeal
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ)
    (ε : ι → Bool) (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =>
      ‖parityGaussian ε t (numberFieldTraceCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))‖) := by
  obtain ⟨C, _, hC⟩ := exists_parityGaussian_norm_bound ε ht
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun a => ?_) ((summable_numberFieldScaledIdealTheta I y (half_pos ht)).mul_left C)
  simpa only [norm_gaussianKernel] using hC
    (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))

/-- Every integral ideal embeds into the unit fractional ideal. -/
def integralIdealIntoOne (b : Ideal (𝓞 K)) (a : b) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  ⟨((a : 𝓞 K) : K), by
    rw [← FractionalIdeal.coeIdeal_top]
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K))
      (show (a : 𝓞 K) ∈ (⊤ : Ideal (𝓞 K)) from trivial)⟩

omit [NumberField K] in
theorem integralIdealIntoOne_injective (b : Ideal (𝓞 K)) :
    Function.Injective (integralIdealIntoOne b) := by
  intro a c h
  apply Subtype.ext
  have hh := congrArg (fun z : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) => (z : K)) h
  change ((a : 𝓞 K) : K) = ((c : 𝓞 K) : K) at hh
  exact Subtype.ext hh

/-- Restriction from the unit fractional ideal gives convergence on every integral ideal. -/
theorem summable_norm_parityGaussian_integralIdeal (b : Ideal (𝓞 K))
    (ε : ι → Bool) (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : b => ‖parityGaussian ε t (numberFieldTraceCoordinates
      (numberFieldMixedPlaceScale y (mixedEmbedding K ((a : 𝓞 K) : K))))‖) := by
  have h : Summable (fun a : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =>
      ‖parityGaussian ε t (numberFieldTraceCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))‖) :=
    summable_norm_parityGaussian_fractionalIdeal (K := K) 1 ε y ht
  have h' : Summable ((fun a : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =>
      ‖parityGaussian ε t (numberFieldTraceCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))‖) ∘ integralIdealIntoOne b) :=
    h.comp_injective (integralIdealIntoOne_injective b)
  exact h'

/-- The actual finite Hecke weight times its scaled archimedean parity Gaussian. -/
def heckeThetaKernel (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (t : ℝ) (a : 𝓞 K) : ℂ :=
  integralHeckeWeight 𝔪 ψ a * parityGaussian (heckeCoordinateParity 𝔪 ψ) t
    (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))

/-- Finite and infinite unit factors cancel in the actual Hecke theta kernel. -/
theorem heckeThetaKernel_unit (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (u : (𝓞 K)ˣ) (t : ℝ) (a : 𝓞 K) :
    heckeThetaKernel 𝔪 ψ (y + numberFieldUnitPlaceLogEmbeddings u) t ((u : 𝓞 K) * a) =
      heckeThetaKernel 𝔪 ψ y t a := by
  simp only [heckeThetaKernel, integralHeckeWeight_mul, parityGaussian,
    parityMonomial_heckeCoordinateParity, gaussianKernel_eq_ofReal]
  change integralHeckeWeight 𝔪 ψ (u : 𝓞 K) * integralHeckeWeight 𝔪 ψ a *
    (heckeRealMonomial 𝔪 ψ (numberFieldMixedPlaceScale
      (y + numberFieldUnitPlaceLogEmbeddings u)
      (mixedEmbedding K (((u : 𝓞 K) : K) * (a : K)))) *
    (Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale
      (y + numberFieldUnitPlaceLogEmbeddings u)
      (mixedEmbedding K (((u : 𝓞 K) : K) * (a : K))))‖^2) : ℂ)) = _
  rw [heckeRealMonomial_unit, norm_sq_numberFieldPlaceScale_unit]
  calc
    _ = (integralHeckeWeight 𝔪 ψ (u : 𝓞 K) *
      ∏ w : 𝔪.inf,
        ((signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) w : ℤ) : ℂ) ^
          heckeParity 𝔪 ψ w) * (integralHeckeWeight 𝔪 ψ a *
      (heckeRealMonomial 𝔪 ψ (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))) *
        (Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates
          (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖^2) : ℂ))) := by ring
    _ = _ := by rw [integralHeckeWeight_mul_parities_unit, one_mul]

/-- The actual Hecke theta series converges absolutely for every positive parameter. -/
theorem summable_norm_heckeThetaKernel (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : b => ‖heckeThetaKernel 𝔪 ψ y t (a : 𝓞 K)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
    (summable_norm_parityGaussian_integralIdeal b (heckeCoordinateParity 𝔪 ψ) y ht)
  rw [heckeThetaKernel, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_integralHeckeWeight_le_one 𝔪 ψ _)

/-- Hecke-weighted theta summed over actual elements of an integral ideal. -/
def heckeIdealTheta (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    (y : InfinitePlace K → ℝ) (t : ℝ) : ℂ :=
  ∑' a : b, heckeThetaKernel 𝔪 ψ y t (a : 𝓞 K)

/-- Multiplication by a global unit makes the theta family periodic in its place logarithm. -/
theorem heckeIdealTheta_unit (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    (y : InfinitePlace K → ℝ) (u : (𝓞 K)ˣ) (t : ℝ) :
    heckeIdealTheta 𝔪 ψ b (y + numberFieldUnitPlaceLogEmbeddings u) t =
      heckeIdealTheta 𝔪 ψ b y t := by
  let e : b ≃ b := MulAction.toPerm u
  have he (a : b) : (e a : 𝓞 K) = (u : 𝓞 K) * (a : 𝓞 K) := rfl
  unfold heckeIdealTheta
  calc
    _ = ∑' a : b, heckeThetaKernel 𝔪 ψ
        (y + numberFieldUnitPlaceLogEmbeddings u) t (e a : 𝓞 K) :=
      (e.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [he, heckeThetaKernel_unit]

end GaloisForLFunctions.HeckeLFunctions
