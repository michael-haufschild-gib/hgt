import GaloisForLFunctions.HeckeLFunctions.HeckeIdealThetaIsUnitPeriodic
import GaloisForLFunctions.HTGeometry.IntrinsicParityPoisson

/-!
# Hecke theta has a finite Fourier transform

Residues modulo the finite modulus parametrize the cosets of its product with a
coprime integral ideal. Applying parity Poisson summation to each coset gives a
sum on the arithmetic trace-dual ideal. Reciprocal archimedean scales cancel in
the trace pairing, so the dual coefficient is an explicit finite residue sum.
Its norm is bounded by the modulus norm, and the dual series is absolutely
convergent. The normalization includes the exact ideal norm, discriminant,
field degree, place scaling, and real-parity factor.
-/

noncomputable section
open NumberField NumberField.InfinitePlace
open scoped Classical
namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Reciprocal place scaling cancels in coordinatewise multiplication. -/
theorem numberFieldMixedPlaceScale_mul_neg (y : InfinitePlace K → ℝ)
    (z v : mixedEmbedding.mixedSpace K) :
    numberFieldMixedPlaceScale y z * numberFieldMixedPlaceScale (-y) v = z * v := by
  apply Prod.ext
  · funext w
    change (Real.exp (-y w.1) * z.1 w) * (Real.exp (-(-y w.1)) * v.1 w) = z.1 w * v.1 w
    rw [neg_neg, mul_mul_mul_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  · funext w
    change ((Real.exp (-y w.1) : ℂ) * z.2 w) *
      ((Real.exp (-(-y w.1)) : ℂ) * v.2 w) = z.2 w * v.2 w
    rw [neg_neg, mul_mul_mul_comm, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]

theorem inner_numberFieldTraceCoordinates_scaled_conjugate
    (y : InfinitePlace K → ℝ) (a b : K) :
    inner ℝ (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K a)))
      (numberFieldTraceCoordinates (numberFieldMixedConjugation
        (numberFieldMixedPlaceScale (-y) (mixedEmbedding K b)))) =
      (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [inner_numberFieldTraceCoordinates_conjugate, numberFieldMixedPlaceScale_mul_neg,
    ← map_mul, numberFieldMixedTrace_embedding]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "ι" => numberFieldMixedRealCoordinateIndex K
local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι

/-- The additive Fourier phase defined by the rational field trace. -/
def numberFieldTracePhase (a b : K) : ℂ :=
  Complex.exp (((2 * Real.pi * (Algebra.trace ℚ K (a * b) : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The Euclidean dual-lattice phase is exactly the arithmetic trace phase. -/
theorem latticePhase_scaled_trace (y : InfinitePlace K → ℝ) (a b : K) :
    latticePhase
      (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K a)))
      (numberFieldTraceCoordinates (numberFieldMixedConjugation
        (numberFieldMixedPlaceScale (-y) (mixedEmbedding K b)))) =
      numberFieldTracePhase a b := by
  rw [latticePhase, inner_numberFieldTraceCoordinates_scaled_conjugate]
  rfl

theorem norm_numberFieldTracePhase (a b : K) : ‖numberFieldTracePhase a b‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Real-place parities and Gaussian norms are unchanged by mixed conjugation. -/
theorem parityGaussian_hecke_conjugate (ψ : HeckeCharacter 𝔪) (t : ℝ)
    (z : mixedEmbedding.mixedSpace K) :
    parityGaussian (heckeCoordinateParity 𝔪 ψ) t
        (numberFieldTraceCoordinates (numberFieldMixedConjugation z)) =
      parityGaussian (heckeCoordinateParity 𝔪 ψ) t (numberFieldTraceCoordinates z) := by
  rw [parityGaussian, parityGaussian, parityMonomial_heckeCoordinateParity,
    parityMonomial_heckeCoordinateParity, gaussianKernel_eq_ofReal,
    gaussianKernel_eq_ofReal, norm_sq_traceCoordinates_conjugation]
  rfl

/-- The archimedean parity Gaussian of the actual Hecke character. -/
def heckeParityKernel (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (t : ℝ) (a : K) : ℂ :=
  parityGaussian (heckeCoordinateParity 𝔪 ψ) t
    (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K a)))

/-- An affine parity theta sum over actual fractional-ideal elements. -/
def idealParityTheta (ψ : HeckeCharacter 𝔪) (I : FI)
    (y : InfinitePlace K → ℝ) (t : ℝ) (c : K) : ℂ :=
  ∑' a : I, heckeParityKernel 𝔪 ψ y t ((a : K) + c)

/-- Actual ideal elements parametrize the shifted scaled-lattice sum. -/
theorem idealParityTheta_eq_intrinsic_affine (ψ : HeckeCharacter 𝔪) (I : FIˣ)
    (y : InfinitePlace K → ℝ) (t : ℝ) (c : K) :
    idealParityTheta 𝔪 ψ (I : FI) y t c =
      ∑' x : numberFieldScaledTraceLattice I y,
        parityGaussian (heckeCoordinateParity 𝔪 ψ) t
          (WithLp.toLp 2 (x : X) + numberFieldTraceCoordinates
            (numberFieldMixedPlaceScale y (mixedEmbedding K c))) := by
  unfold idealParityTheta
  calc
    _ = ∑' a : (I : FI), parityGaussian (heckeCoordinateParity 𝔪 ψ) t
        (WithLp.toLp 2 (numberFieldScaledIdealLatticeEquiv I y a : X) +
          numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K c))) := by
      apply tsum_congr
      intro a
      rw [toLp_numberFieldScaledIdealLatticeEquiv]
      simp only [heckeParityKernel, map_add]
    _ = _ := (numberFieldScaledIdealLatticeEquiv I y).tsum_eq
      (fun x : numberFieldScaledTraceLattice I y =>
        parityGaussian (heckeCoordinateParity 𝔪 ψ) t
          (WithLp.toLp 2 (x : X) + numberFieldTraceCoordinates
            (numberFieldMixedPlaceScale y (mixedEmbedding K c))))

/-- The intrinsic integer dual becomes the arithmetic trace-dual ideal. -/
theorem idealParity_dual_sum (ψ : HeckeCharacter 𝔪) (I : FIˣ)
    (y : InfinitePlace K → ℝ) (t : ℝ) (c : K) :
    (∑' x : DualZLattice.dual (numberFieldScaledTraceLattice I y),
      latticePhase (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K c)))
        (WithLp.toLp 2 (x : X)) *
        parityGaussian (heckeCoordinateParity 𝔪 ψ) t (WithLp.toLp 2 (x : X))) =
    ∑' a : FractionalIdeal.dual ℤ ℚ (I : FI),
      numberFieldTracePhase c (a : K) * heckeParityKernel 𝔪 ψ (-y) t (a : K) := by
  rw [dual_numberFieldScaledTraceLattice]
  calc
    _ = ∑' a : FractionalIdeal.dual ℤ ℚ (I : FI),
      latticePhase (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K c)))
        (WithLp.toLp 2 (numberFieldScaledDualIdealLatticeEquiv I y a : X)) *
        parityGaussian (heckeCoordinateParity 𝔪 ψ) t
          (WithLp.toLp 2 (numberFieldScaledDualIdealLatticeEquiv I y a : X)) :=
      ((numberFieldScaledDualIdealLatticeEquiv I y).tsum_eq
        (fun x : DualZLattice.linearImage (numberFieldPlaceDiagonal (-y))
            (DualZLattice.dual (numberFieldTraceLattice I)) =>
          latticePhase (numberFieldTraceCoordinates
            (numberFieldMixedPlaceScale y (mixedEmbedding K c))) (WithLp.toLp 2 (x : X)) *
            parityGaussian (heckeCoordinateParity 𝔪 ψ) t (WithLp.toLp 2 (x : X)))).symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [toLp_numberFieldScaledDualIdealLatticeEquiv, latticePhase_scaled_trace,
        parityGaussian_hecke_conjugate]
      rfl

/-- Affine ideal parity Poisson with the exact arithmetic normalization. -/
theorem idealParityTheta_poisson (ψ : HeckeCharacter 𝔪) (I : FIˣ)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) (c : K) :
    idealParityTheta 𝔪 ψ (I : FI) y t c =
      (Real.exp (∑ w : InfinitePlace K, (mult w : ℝ) * y w) : ℂ) *
        ((((FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹ : ℝ) : ℂ) *
        ((t ^ (-((Module.finrank ℚ K : ℝ) / 2)) : ℝ) : ℂ) *
        (-Complex.I / (t : ℂ)) ^ parityDegree (heckeCoordinateParity 𝔪 ψ) *
        ∑' a : FractionalIdeal.dual ℤ ℚ (I : FI),
          numberFieldTracePhase c (a : K) * heckeParityKernel 𝔪 ψ (-y) (1 / t) (a : K) := by
  have h := intrinsic_parity_basis_poisson (numberFieldScaledTraceBasis I y)
    (heckeCoordinateParity 𝔪 ψ) ht
    (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K c))) 0
  have hphase (x : E) : latticePhase x 0 = 1 := by simp [latticePhase]
  simp only [parityModulation, hphase, one_mul, sub_zero] at h
  rw [span_numberFieldScaledTraceBasis, ← idealParityTheta_eq_intrinsic_affine,
    idealParity_dual_sum, covolume_numberFieldScaledTraceLattice,
    numberFieldTraceCoordinates_finrank, mul_inv_rev, Real.exp_neg, inv_inv] at h
  rw [mul_comm
    (((FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹)
    (Real.exp (∑ w : InfinitePlace K, (mult w : ℝ) * y w)), Complex.ofReal_mul] at h
  exact h

/-- The phase-weighted arithmetic dual series converges absolutely. -/
theorem summable_norm_idealParity_dual (ψ : HeckeCharacter 𝔪) (I : FIˣ)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) (c : K) :
    Summable (fun a : FractionalIdeal.dual ℤ ℚ (I : FI) =>
      ‖numberFieldTracePhase c (a : K) * heckeParityKernel 𝔪 ψ (-y) t (a : K)‖) := by
  have h := summable_norm_intrinsic_dual_parity_basis (numberFieldScaledTraceBasis I y)
    (heckeCoordinateParity 𝔪 ψ) ht
    (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K c))) 0
  rw [span_numberFieldScaledTraceBasis, dual_numberFieldScaledTraceLattice] at h
  simp only [sub_zero] at h
  have hh := (numberFieldScaledDualIdealLatticeEquiv I y).summable_iff.mpr h
  refine hh.congr fun a => ?_
  simp only [Function.comp_def, toLp_numberFieldScaledDualIdealLatticeEquiv,
    latticePhase_scaled_trace, parityGaussian_hecke_conjugate, heckeParityKernel]

variable {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)

/-- A residue representative plus an element of the product ideal. -/
def residueIdealPoint (p : (𝓞 K ⧸ 𝔪.fin) × (𝔪.fin * b)) : b :=
  ⟨(p.2 : 𝓞 K) + residueRep 𝔪 hb p.1,
    add_mem (Ideal.mul_le_left p.2.2) (residueRep_mem hb _)⟩

omit [NumberField K] in
theorem mk_residueIdealPoint (p : (𝓞 K ⧸ 𝔪.fin) × (𝔪.fin * b)) :
    Ideal.Quotient.mk 𝔪.fin (residueIdealPoint 𝔪 hb p : 𝓞 K) = p.1 := by
  change Ideal.Quotient.mk 𝔪.fin ((p.2 : 𝓞 K) + residueRep 𝔪 hb p.1) = _
  rw [map_add, mk_residueRep hb,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right p.2.2), zero_add]

/-- Subtracting the residue representative lands in the product ideal. -/
def residueIdealRemainder (a : b) : 𝔪.fin * b :=
  ⟨(a : 𝓞 K) - residueRep 𝔪 hb (Ideal.Quotient.mk 𝔪.fin (a : 𝓞 K)), by
    rw [Ideal.mul_eq_inf_of_isCoprime
      (Ideal.isCoprime_iff_sup_eq.mpr (by rw [sup_comm, hb]))]
    refine ⟨?_, sub_mem a.2 (residueRep_mem hb _)⟩
    rw [SetLike.mem_coe, ← Ideal.Quotient.eq, mk_residueRep hb]⟩

/-- Residues and product-ideal elements parametrize a coprime integral ideal. -/
def residueIdealEquiv : ((𝓞 K ⧸ 𝔪.fin) × (𝔪.fin * b)) ≃ b where
  toFun := residueIdealPoint 𝔪 hb
  invFun a := (Ideal.Quotient.mk 𝔪.fin (a : 𝓞 K), residueIdealRemainder 𝔪 hb a)
  left_inv p := by
    apply Prod.ext
    · exact mk_residueIdealPoint 𝔪 hb p
    · apply Subtype.ext
      change (residueIdealPoint 𝔪 hb p : 𝓞 K) -
        residueRep 𝔪 hb (Ideal.Quotient.mk 𝔪.fin (residueIdealPoint 𝔪 hb p : 𝓞 K)) = p.2
      rw [mk_residueIdealPoint]
      change (p.2 : 𝓞 K) + residueRep 𝔪 hb p.1 - residueRep 𝔪 hb p.1 = _
      abel
  right_inv a := by
    apply Subtype.ext
    change ((a : 𝓞 K) - residueRep 𝔪 hb (Ideal.Quotient.mk 𝔪.fin (a : 𝓞 K))) +
      residueRep 𝔪 hb (Ideal.Quotient.mk 𝔪.fin (a : 𝓞 K)) = _
    abel

theorem integralHeckeWeight_residueIdealPoint (ψ : HeckeCharacter 𝔪)
    (p : (𝓞 K ⧸ 𝔪.fin) × (𝔪.fin * b)) :
    integralHeckeWeight 𝔪 ψ (residueIdealPoint 𝔪 hb p : 𝓞 K) =
      finiteHeckeWeight 𝔪 ψ p.1 := by
  rw [integralHeckeWeight, mk_residueIdealPoint]


/-- The canonical inclusion of an integral ideal into its fractional-ideal realization. -/
def integralIdealToFractional (J : Ideal (𝓞 K)) (a : J) : (J : FI) :=
  ⟨((a : 𝓞 K) : K), FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) a.2⟩

omit [NumberField K] in
theorem integralIdealToFractional_injective (J : Ideal (𝓞 K)) :
    Function.Injective (integralIdealToFractional J) := by
  intro a c h
  apply Subtype.ext
  have hh := congrArg (fun z : (J : FI) => (z : K)) h
  change ((a : 𝓞 K) : K) = ((c : 𝓞 K) : K) at hh
  exact Subtype.ext hh

/-- Integral and fractional realizations of the same ideal have identical elements. -/
def integralIdealEquivFractional (J : Ideal (𝓞 K)) : J ≃ (J : FI) :=
  Equiv.ofBijective (integralIdealToFractional J)
    ⟨integralIdealToFractional_injective J, by
      intro x
      obtain ⟨a, ha, hax⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp x.2
      exact ⟨⟨a,ha⟩, Subtype.ext hax⟩⟩

theorem integralParityTheta_eq (ψ : HeckeCharacter 𝔪) (J : Ideal (𝓞 K))
    (y : InfinitePlace K → ℝ) (t : ℝ) (c : K) :
    (∑' a : J, heckeParityKernel 𝔪 ψ y t (((a : 𝓞 K) : K) + c)) =
      idealParityTheta 𝔪 ψ (J : FI) y t c :=
  (integralIdealEquivFractional J).tsum_eq
    (fun a : (J : FI) => heckeParityKernel 𝔪 ψ y t ((a : K) + c))

/-- The finite character is constant on each residue coset. -/
theorem heckeIdealTheta_eq_residue_sum (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    heckeIdealTheta 𝔪 ψ b y t =
      ∑' ρ : 𝓞 K ⧸ 𝔪.fin, finiteHeckeWeight 𝔪 ψ ρ *
        idealParityTheta 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) y t (residueRep 𝔪 hb ρ : K) := by
  let e := residueIdealEquiv 𝔪 hb
  have hs : Summable (fun a : b => heckeThetaKernel 𝔪 ψ y t (a : 𝓞 K)) :=
    (summable_norm_heckeThetaKernel 𝔪 ψ b y ht).of_norm
  have hp := e.summable_iff.mpr hs
  calc
    _ = ∑' p : (𝓞 K ⧸ 𝔪.fin) × (𝔪.fin * b),
        heckeThetaKernel 𝔪 ψ y t (e p : 𝓞 K) :=
      (e.tsum_eq (fun a : b => heckeThetaKernel 𝔪 ψ y t (a : 𝓞 K))).symm
    _ = ∑' ρ : 𝓞 K ⧸ 𝔪.fin, ∑' a : 𝔪.fin * b,
        heckeThetaKernel 𝔪 ψ y t (e (ρ,a) : 𝓞 K) := hp.tsum_prod
    _ = ∑' ρ : 𝓞 K ⧸ 𝔪.fin, finiteHeckeWeight 𝔪 ψ ρ *
        ∑' a : 𝔪.fin * b, heckeParityKernel 𝔪 ψ y t
          (((a : 𝓞 K) : K) + (residueRep 𝔪 hb ρ : K)) := by
      apply tsum_congr
      intro ρ
      rw [← tsum_mul_left]
      apply tsum_congr
      intro a
      change heckeThetaKernel 𝔪 ψ y t (residueIdealPoint 𝔪 hb (ρ,a) : 𝓞 K) = _
      rw [heckeThetaKernel, integralHeckeWeight_residueIdealPoint]
      rfl
    _ = _ := by
      apply tsum_congr
      intro ρ
      rw [integralParityTheta_eq]

/-- The finite residue Fourier sum at a field-valued frequency. -/
def finiteHeckeFourierCoefficient (ψ : HeckeCharacter 𝔪) (a : K) : ℂ :=
  ∑' ρ : 𝓞 K ⧸ 𝔪.fin, finiteHeckeWeight 𝔪 ψ ρ *
    numberFieldTracePhase (residueRep 𝔪 hb ρ : K) a

/-- The finite Fourier coefficient is bounded by the finite modulus norm. -/
theorem norm_finiteHeckeFourierCoefficient_le (ψ : HeckeCharacter 𝔪) (a : K) :
    ‖finiteHeckeFourierCoefficient 𝔪 hb ψ a‖ ≤ (Ideal.absNorm 𝔪.fin : ℝ) := by
  change ‖finiteHeckeFourierCoefficient 𝔪 hb ψ a‖ ≤ (Nat.card (𝓞 K ⧸ 𝔪.fin) : ℝ)
  letI := 𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔪.fin)
  rw [finiteHeckeFourierCoefficient, tsum_fintype]
  calc
    _ ≤ ∑ ρ : 𝓞 K ⧸ 𝔪.fin, ‖finiteHeckeWeight 𝔪 ψ ρ *
        numberFieldTracePhase (residueRep 𝔪 hb ρ : K) a‖ := norm_sum_le _ _
    _ ≤ ∑ _ρ : 𝓞 K ⧸ 𝔪.fin, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ _
      rw [norm_mul, norm_numberFieldTracePhase, mul_one]
      exact norm_finiteHeckeWeight_le_one 𝔪 ψ ρ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]

/-- The covolume, degree, and parity normalization in arithmetic theta inversion. -/
def heckeThetaPoissonFactor (ψ : HeckeCharacter 𝔪) (I : FI)
    (y : InfinitePlace K → ℝ) (t : ℝ) : ℂ :=
  (Real.exp (∑ w : InfinitePlace K, (mult w : ℝ) * y w) : ℂ) *
    ((((FractionalIdeal.absNorm I : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹ : ℝ) : ℂ) *
    ((t ^ (-((Module.finrank ℚ K : ℝ) / 2)) : ℝ) : ℂ) *
    (-Complex.I / (t : ℂ)) ^ parityDegree (heckeCoordinateParity 𝔪 ψ)

/-- Finite-character Hecke theta transforms into its finite Fourier-weighted trace-dual sum. -/
theorem heckeIdealTheta_poisson (ψ : HeckeCharacter 𝔪) (hb0 : b ≠ ⊥)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    heckeIdealTheta 𝔪 ψ b y t =
      heckeThetaPoissonFactor 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) y t *
        ∑' a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI),
          finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
            heckeParityKernel 𝔪 ψ (-y) (1 / t) (a : K) := by
  letI := 𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔪.fin)
  let I := idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)
  have hI : (I : FI) = ((𝔪.fin * b : Ideal (𝓞 K)) : FI) := coe_idealUnit _
  rw [heckeIdealTheta_eq_residue_sum 𝔪 hb ψ y ht, tsum_fintype, ← hI]
  simp_rw [idealParityTheta_poisson 𝔪 ψ I y ht]
  change (∑ ρ : 𝓞 K ⧸ 𝔪.fin, finiteHeckeWeight 𝔪 ψ ρ *
    (heckeThetaPoissonFactor 𝔪 ψ (I : FI) y t *
      ∑' a : FractionalIdeal.dual ℤ ℚ (I : FI),
        numberFieldTracePhase (residueRep 𝔪 hb ρ : K) (a : K) *
          heckeParityKernel 𝔪 ψ (-y) (1 / t) (a : K))) = _
  let f (ρ : 𝓞 K ⧸ 𝔪.fin) (a : FractionalIdeal.dual ℤ ℚ (I : FI)) : ℂ :=
    finiteHeckeWeight 𝔪 ψ ρ * (numberFieldTracePhase (residueRep 𝔪 hb ρ : K) (a : K) *
      heckeParityKernel 𝔪 ψ (-y) (1 / t) (a : K))
  have hf (ρ : 𝓞 K ⧸ 𝔪.fin) : Summable (f ρ) :=
    ((summable_norm_idealParity_dual 𝔪 ψ I y (one_div_pos.mpr ht)
      (residueRep 𝔪 hb ρ : K)).of_norm).mul_left _
  calc
    _ = heckeThetaPoissonFactor 𝔪 ψ (I : FI) y t *
        ∑ ρ : 𝓞 K ⧸ 𝔪.fin, ∑' a, f ρ a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      simp only [f, tsum_mul_left]
      ring
    _ = heckeThetaPoissonFactor 𝔪 ψ (I : FI) y t *
        ∑' a, ∑ ρ : 𝓞 K ⧸ 𝔪.fin, f ρ a := by
      rw [Summable.tsum_finsetSum (fun ρ _ => hf ρ)]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro a
      rw [finiteHeckeFourierCoefficient, tsum_fintype, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ρ _
      exact (mul_assoc _ _ _).symm

/-- The complete finite Fourier-weighted dual series is absolutely convergent. -/
theorem summable_norm_finiteHeckeFourierKernel (ψ : HeckeCharacter 𝔪) (hb0 : b ≠ ⊥)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) =>
      ‖finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
        heckeParityKernel 𝔪 ψ (-y) t (a : K)‖) := by
  let I := idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)
  have hI : (I : FI) = ((𝔪.fin * b : Ideal (𝓞 K)) : FI) := coe_idealUnit _
  have hs : Summable (fun a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) =>
      ‖heckeParityKernel 𝔪 ψ (-y) t (a : K)‖) := by
    have h := summable_norm_idealParity_dual 𝔪 ψ I y ht 0
    rw [hI] at h
    simpa only [norm_mul, norm_numberFieldTracePhase, one_mul] using h
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
    (hs.mul_left (Ideal.absNorm 𝔪.fin : ℝ))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_finiteHeckeFourierCoefficient_le 𝔪 hb ψ (a : K))
    (norm_nonneg _)


end GaloisForLFunctions.HeckeLFunctions
