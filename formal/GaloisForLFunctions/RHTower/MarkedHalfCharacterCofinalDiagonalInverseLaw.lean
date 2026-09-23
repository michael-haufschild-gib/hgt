import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinCStarShilovBlindness
import GaloisForLFunctions.RHTower.EulerActivationSubcriticalOccupancy
import GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Marked half-character cofinal diagonal-inverse obstruction

Exact sequence-space and quotient-map formalization of Theorem 7.1 in the Stage-2 card
`marked-half-character-duality-soldering-and-cofinal-diagonal-inverse-obstruction-law.md`.
The ambient space is the full complex prime sequence module and the distinguished submodule is
exactly the summable (`ell^(1 : ℕ)`) sequences.  No quotient topology is asserted.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Algebraic all-prime quotient -/

/-- Full complex sequence module on ordinary primes. -/
abbrev AllPrimeComplexSequence := Nat.Primes → ℂ

/-- Algebraic `ell^(1 : ℕ)` submodule of all complex prime sequences. -/
def primeL1Submodule : Submodule ℂ AllPrimeComplexSequence where
  carrier f := Summable f
  zero_mem' := summable_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := by
    change Summable (fun p => c * f p)
    exact hf.mul_left c

/-- Fixed algebraic all-prime quotient `C^P / ell^(1 : ℕ)(P)`. -/
abbrev AllPrimeL1Quotient := AllPrimeComplexSequence ⧸ primeL1Submodule

/-- Pointwise diagonal multiplier on all prime sequences. -/
def primeDiagonalMultiplier (m : AllPrimeComplexSequence) :
    AllPrimeComplexSequence →ₗ[ℂ] AllPrimeComplexSequence where
  toFun f p := m p * f p
  map_add' f g := by
    funext p
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- A diagonal multiplier preserves the fixed `ell^(1 : ℕ)` submodule. -/
def PrimeDiagonalPreservesL1 (m : AllPrimeComplexSequence) : Prop :=
  primeL1Submodule ≤ Submodule.comap (primeDiagonalMultiplier m) primeL1Submodule

/-- A diagonal multiplier descends to the fixed algebraic quotient with its prescribed action on
representatives. -/
def HasPrimeDiagonalQuotientMap (m : AllPrimeComplexSequence) : Prop :=
  ∃ Q : AllPrimeL1Quotient →ₗ[ℂ] AllPrimeL1Quotient,
    ∀ f : AllPrimeComplexSequence,
      Q (Submodule.Quotient.mk f) =
        Submodule.Quotient.mk (primeDiagonalMultiplier m f)

/-- A bounded diagonal sequence preserves every summable sequence. -/
theorem primeDiagonalPreservesL1_of_isBounded
    {m : AllPrimeComplexSequence} (hm : Bornology.IsBounded (Set.range m)) :
    PrimeDiagonalPreservesL1 m := by
  obtain ⟨C, hC⟩ := hm.exists_norm_le
  intro f hf
  change Summable (fun p => m p * f p)
  refine Summable.of_norm_bounded (hf.norm.mul_left C) (fun p => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC (m p) ⟨p, rfl⟩) (norm_nonneg (f p))

/-- Coordinate functional `x ↦ m(p)x(p)` on literal prime-indexed `ell¹`. -/
def primeCoordinateMultiplierFunctional (m : AllPrimeComplexSequence) (p : Nat.Primes) :
    lp (fun _ : Nat.Primes => ℂ) 1 →L[ℂ] ℂ :=
  m p • lp.evalCLM ℂ (fun _ : Nat.Primes => ℂ) 1 p

@[simp]
theorem primeCoordinateMultiplierFunctional_apply
    (m : AllPrimeComplexSequence) (p : Nat.Primes)
    (x : lp (fun _ : Nat.Primes => ℂ) 1) :
    primeCoordinateMultiplierFunctional m p x = m p * x p := by
  rfl

/-- Converse multiplier theorem: preservation of every summable prime sequence forces the
diagonal coefficients to be bounded. -/
theorem primeDiagonalPreservesL1_isBounded
    {m : AllPrimeComplexSequence} (hm : PrimeDiagonalPreservesL1 m) :
    Bornology.IsBounded (Set.range m) := by
  have hpointwise :
      ∀ x : lp (fun _ : Nat.Primes => ℂ) 1,
        ∃ C : ℝ, ∀ p, ‖primeCoordinateMultiplierFunctional m p x‖ ≤ C := by
    intro x
    have hxsum : Summable (fun p : Nat.Primes => x p) :=
      x.2.summable_of_one
    have hout := hm hxsum
    change Summable (fun p : Nat.Primes => m p * x p) at hout
    have hbounded := Metric.isBounded_range_of_tendsto_cofinite hout.tendsto_cofinite_zero
    obtain ⟨C, hC⟩ := hbounded.exists_norm_le
    refine ⟨C, fun p => ?_⟩
    rw [primeCoordinateMultiplierFunctional_apply]
    exact hC (m p * x p) ⟨p, rfl⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun p : Nat.Primes => primeCoordinateMultiplierFunctional m p) hpointwise
  refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  let e : lp (fun _ : Nat.Primes => ℂ) 1 := lp.single 1 p 1
  have heNorm : ‖e‖ = 1 := by
    dsimp [e]
    rw [lp.norm_single (p := (1 : ENNReal)) (by norm_num) p 1]
    norm_num
  have happly : primeCoordinateMultiplierFunctional m p e = m p := by
    rw [primeCoordinateMultiplierFunctional_apply]
    simp [e]
  calc
    ‖m p‖ = ‖primeCoordinateMultiplierFunctional m p e‖ := by rw [happly]
    _ ≤ ‖primeCoordinateMultiplierFunctional m p‖ * ‖e‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖primeCoordinateMultiplierFunctional m p‖ := by rw [heNorm, mul_one]
    _ ≤ C := hC p

/-- Exact diagonal multiplier criterion used in Theorem 7.1. -/
theorem primeDiagonalPreservesL1_iff_isBounded (m : AllPrimeComplexSequence) :
    PrimeDiagonalPreservesL1 m ↔ Bornology.IsBounded (Set.range m) :=
  ⟨primeDiagonalPreservesL1_isBounded,
    primeDiagonalPreservesL1_of_isBounded⟩

/-- Preservation of `ell^(1 : ℕ)` produces the canonical quotient multiplier. -/
def primeDiagonalQuotientMap (m : AllPrimeComplexSequence)
    (hm : PrimeDiagonalPreservesL1 m) :
    AllPrimeL1Quotient →ₗ[ℂ] AllPrimeL1Quotient :=
  Submodule.mapQ primeL1Submodule primeL1Submodule (primeDiagonalMultiplier m) hm

/-- The canonical quotient multiplier acts by the pointwise multiplier on representatives. -/
@[simp]
theorem primeDiagonalQuotientMap_mk (m : AllPrimeComplexSequence)
    (hm : PrimeDiagonalPreservesL1 m) (f : AllPrimeComplexSequence) :
    primeDiagonalQuotientMap m hm (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (primeDiagonalMultiplier m f) := by
  exact Submodule.mapQ_apply primeL1Submodule primeL1Submodule
    (primeDiagonalMultiplier m) f

/-- Existence of a quotient map with the prescribed representative action is equivalent to
preservation of `ell^(1 : ℕ)`. -/
theorem hasPrimeDiagonalQuotientMap_iff_preservesL1
    (m : AllPrimeComplexSequence) :
    HasPrimeDiagonalQuotientMap m ↔ PrimeDiagonalPreservesL1 m := by
  constructor
  · rintro ⟨Q, hQ⟩ f hf
    have hzero : (Submodule.Quotient.mk f : AllPrimeL1Quotient) = 0 :=
      (Submodule.Quotient.mk_eq_zero primeL1Submodule).2 hf
    have hout :
        (Submodule.Quotient.mk (primeDiagonalMultiplier m f) : AllPrimeL1Quotient) = 0 := by
      rw [← hQ f, hzero, map_zero]
    exact (Submodule.Quotient.mk_eq_zero primeL1Submodule).1 hout
  · intro hm
    exact ⟨primeDiagonalQuotientMap m hm,
      fun f => primeDiagonalQuotientMap_mk m hm f⟩

/-- A pointwise nonzero diagonal multiplier induces a surjective quotient map whenever it
preserves `ell^(1 : ℕ)`.  Division is performed in the full sequence space, not in `ell^(1 : ℕ)`. -/
theorem primeDiagonalQuotientMap_surjective
    (m : AllPrimeComplexSequence) (hm : PrimeDiagonalPreservesL1 m)
    (hm0 : ∀ p, m p ≠ 0) :
    Function.Surjective (primeDiagonalQuotientMap m hm) := by
  intro y
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective primeL1Submodule y
  refine ⟨Submodule.Quotient.mk (fun p => f p / m p), ?_⟩
  rw [primeDiagonalQuotientMap_mk]
  congr 1
  funext p
  simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    m p * (f p / m p) = f p * (m p * (m p)⁻¹) := by
      rw [div_eq_mul_inv]
      ring
    _ = f p := by rw [mul_inv_cancel₀ (hm0 p), mul_one]

/-! ## Exact arithmetic coefficient -/

/-- Positive comparison coefficient `r_t(p)=d(p)(1+p^{-t})`. -/
def markedCofinalComparisonWeight (t : ℝ) (p : Nat.Primes) : ℝ :=
  primeActivationOccupancyFisherDensity p * (1 + (p : ℝ) ^ (-t))

/-- The comparison coefficient is the sum of the neutral Fisher density and reflected twist. -/
theorem markedCofinalComparisonWeight_eq_density_add_twist
    (t : ℝ) (p : Nat.Primes) :
    markedCofinalComparisonWeight t p =
      primeActivationOccupancyFisherDensity p +
        primeActivationOccupancyFisherTwist (-t) p := by
  simp only [markedCofinalComparisonWeight, primeActivationOccupancyFisherTwist]
  ring

/-- Every finite-prime comparison coefficient is strictly positive. -/
theorem markedCofinalComparisonWeight_pos (t : ℝ) (p : Nat.Primes) :
    0 < markedCofinalComparisonWeight t p := by
  rw [markedCofinalComparisonWeight]
  have hdensity : 0 < primeActivationOccupancyFisherDensity p := by
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
    exact lt_of_lt_of_le (one_div_pos.mpr (mul_pos (by norm_num) hp0))
      (primeActivationOccupancyFisherDensity_bounds p).1
  positivity

/-- The finite-prime coefficient in the exact Bockstein/residue comparison is nonzero. -/
theorem primeGammaResidueComparisonCoefficient_ne_zero
    (t : ℝ) (p : Nat.Primes) :
    (-(markedCofinalComparisonWeight t p : ℂ)) ≠ 0 := by
  exact neg_ne_zero.mpr (by
    exact_mod_cast (markedCofinalComparisonWeight_pos t p).ne')

/-- Prime-power majorant valid at every ordinary prime. -/
theorem markedCofinalComparisonWeight_le_model (t : ℝ) (p : Nat.Primes) :
    markedCofinalComparisonWeight t p ≤
      (p : ℝ) ^ (-1 : ℝ) + (p : ℝ) ^ (-t - 1) := by
  rw [markedCofinalComparisonWeight_eq_density_add_twist]
  exact add_le_add
    (by simpa only [Real.rpow_neg_one, one_div] using
      (primeActivationOccupancyFisherDensity_bounds p).2)
    (primeActivationOccupancyFisherTwist_bounds (-t) p).2

/-- In the open critical strip, the exact comparison coefficient tends to zero along ordinary
primes. -/
theorem markedCofinalComparisonWeight_tendsto_cofinite_zero
    {t : ℝ} (ht : |t| < 1) :
    Tendsto (markedCofinalComparisonWeight t) cofinite (𝓝 0) := by
  have hpNat : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Nat.Primes.coe_nat_injective.tendsto_cofinite
  have hpReal : Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop :=
    tendsto_natCast_atTop_atTop.comp hpNat
  have hfirst : Tendsto (fun p : Nat.Primes => (p : ℝ) ^ (-1 : ℝ))
      cofinite (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num)).comp hpReal
    change Tendsto ((fun x : ℝ => x ^ (-1 : ℝ)) ∘
      (fun p : Nat.Primes => (p : ℝ))) cofinite (𝓝 0)
    exact h
  have hsecond : Tendsto (fun p : Nat.Primes => (p : ℝ) ^ (-t - 1))
      cofinite (𝓝 0) := by
    have hpos : 0 < t + 1 := by linarith [neg_lt_of_abs_lt ht]
    have h := (tendsto_rpow_neg_atTop hpos).comp hpReal
    change Tendsto ((fun x : ℝ => x ^ (-t - 1)) ∘
      (fun p : Nat.Primes => (p : ℝ))) cofinite (𝓝 0)
    simpa only [show -(t + 1) = -t - 1 by ring] using h
  exact squeeze_zero
    (fun p => (markedCofinalComparisonWeight_pos t p).le)
    (fun p => markedCofinalComparisonWeight_le_model t p)
    (by simpa only [zero_add] using hfirst.add hsecond)

/-- The complex comparison sequence belongs to `ell^infinity`. -/
theorem markedCofinalComparisonWeight_isBounded
    {t : ℝ} (ht : |t| < 1) :
    Bornology.IsBounded
      (Set.range (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))) := by
  apply Metric.isBounded_range_of_tendsto_cofinite
  change Tendsto (Complex.ofReal ∘ markedCofinalComparisonWeight t)
    cofinite (𝓝 (Complex.ofReal 0))
  exact (Complex.continuous_ofReal.tendsto 0).comp
    (markedCofinalComparisonWeight_tendsto_cofinite_zero ht)

/-- Exact Bockstein/curvature coefficient identity
`b_t(p)=-r_t(p)(p^t-1)`. -/
theorem primeGammaCofinalBocksteinCoefficient_eq_neg_weight_mul_curvature
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient t p =
      -markedCofinalComparisonWeight t p * ((p : ℝ) ^ t - 1) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist,
    markedCofinalComparisonWeight, Real.rpow_neg hp0.le]
  field_simp [(Real.rpow_pos_of_pos hp0 t).ne']
  ring

/-- The Deninger half-density mate gain is the literal positive real power used by the
marked-holonomy chart. -/
theorem deningerHalfDensityMateGain_eq_rpow
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    deningerHalfDensityMateGain n s = (n : ℝ) ^ (2 * s.re - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [deningerHalfDensityMateGain, Real.rpow_def_of_pos hnR]
  congr 1
  ring

/-- Exact arithmetic Stokes/Bockstein comparison on every rational-adelic degree-one source:
the Gamma coefficient is the duality weight times the already-constructed physical residue. -/
theorem primeGammaBockstein_mul_xiLanding_eq_neg_weight_mul_residue
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    (primeGammaCofinalBocksteinCoefficient (2 * (rho : ℂ).re - 1) p : ℂ) *
        (thetaInternalJetLeadingSourceCoefficient rho *
          ccmRationalAdelicDegreeOneTrace x) =
      -(markedCofinalComparisonWeight (2 * (rho : ℂ).re - 1) p : ℂ) *
        ccmRationalAdelicTwoLegCyclicResidue
          (GaloisForLFunctions.HTGeometry.cyclicParacyclicEquivarianceDefect
            ccmRationalAdelicDegreeOneCyclicRotation
            (sourceDaggerNormalizedDegreeOneRotationLinear (p : ℕ) (rho : ℂ))
            (ccmMobiusThetaXiJetTwoLegLanding
              (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)) x) := by
  rw [GaloisForLFunctions.IrregularStokes.ccmXiResidue_eq_centralHolonomyDefect]
  rw [GaloisForLFunctions.IrregularStokes.centralHolonomyDefect,
    deningerHalfDensityMateGain_eq_rpow p.2.pos,
    primeGammaCofinalBocksteinCoefficient_eq_neg_weight_mul_curvature]
  push_cast
  ring

/-! ## Arithmetic positive-real rank energy -/

/-- Positive-real arithmetic half-character `u_p=p^(Re ρ-1/2)`. -/
def xiPrimeMarkedHalfCharacter (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ ((rho : ℂ).re - 1 / 2)

/-- Coarse arithmetic holonomy `z_p=p^(2 Re ρ-1)`. -/
def xiPrimeCoarseHolonomy (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (2 * (rho : ℂ).re - 1)

/-- The arithmetic marked half-character is an exact positive square root of coarse holonomy. -/
theorem xiPrimeMarkedHalfCharacter_sq
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiPrimeMarkedHalfCharacter rho p ^ 2 = xiPrimeCoarseHolonomy rho p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [xiPrimeMarkedHalfCharacter, xiPrimeCoarseHolonomy,
    Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Exact physical-rank reflection energy `(20)`, including its hyperbolic normal form. -/
theorem xiPrimeRankReflectionEnergy
    (rho : XiDivisorSupport) (p : Nat.Primes) (M : ℕ) :
    -((xiPrimeCoarseHolonomy rho p ^ M - 1) *
        ((xiPrimeCoarseHolonomy rho p)⁻¹ ^ M - 1)) =
        (xiPrimeMarkedHalfCharacter rho p ^ M -
          (xiPrimeMarkedHalfCharacter rho p)⁻¹ ^ M) ^ 2 ∧
      (xiPrimeMarkedHalfCharacter rho p ^ M -
          (xiPrimeMarkedHalfCharacter rho p)⁻¹ ^ M) ^ 2 =
        4 * Real.sinh
          ((M : ℝ) * ((rho : ℂ).re - 1 / 2) * Real.log (p : ℝ)) ^ 2 := by
  have hu : 0 < xiPrimeMarkedHalfCharacter rho p := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hz := xiPrimeMarkedHalfCharacter_sq rho p
  constructor
  · rw [← hz]
    have hpow : (xiPrimeMarkedHalfCharacter rho p ^ 2) ^ M =
        (xiPrimeMarkedHalfCharacter rho p ^ M) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hinvPow : ((xiPrimeMarkedHalfCharacter rho p ^ 2)⁻¹) ^ M =
        ((xiPrimeMarkedHalfCharacter rho p ^ M)⁻¹) ^ 2 := by
      rw [inv_pow, hpow, inv_pow]
    rw [hpow, hinvPow, inv_pow]
    have hlocal (a : ℝ) (ha : a ≠ 0) :
        -((a ^ 2 - 1) * ((a ^ 2)⁻¹ - 1)) = (a - a⁻¹) ^ 2 := by
      field_simp [ha]
      ring
    simpa only [inv_pow] using
      hlocal (xiPrimeMarkedHalfCharacter rho p ^ M) (pow_ne_zero M hu.ne')
  · have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    have huexp : xiPrimeMarkedHalfCharacter rho p =
        Real.exp (((rho : ℂ).re - 1 / 2) * Real.log (p : ℝ)) := by
      rw [xiPrimeMarkedHalfCharacter, Real.rpow_def_of_pos hp]
      congr 1
      ring
    let y : ℝ := (M : ℝ) * ((rho : ℂ).re - 1 / 2) * Real.log (p : ℝ)
    have huPow : xiPrimeMarkedHalfCharacter rho p ^ M = Real.exp y := by
      rw [huexp, ← Real.exp_nat_mul]
      congr 1
      dsimp [y]
      ring
    have huInvPow : (xiPrimeMarkedHalfCharacter rho p)⁻¹ ^ M = Real.exp (-y) := by
      rw [inv_pow, huPow, ← Real.exp_neg]
    rw [huPow, huInvPow]
    change (Real.exp y - Real.exp (-y)) ^ 2 = 4 * Real.sinh y ^ 2
    rw [Real.sinh_eq]
    ring

/-! ## Explicit kernel witness and inverse obstruction -/

/-- Prime harmonic sequence, viewed in the full complex sequence space. -/
def primeHarmonicComplexSequence : AllPrimeComplexSequence :=
  fun p => Complex.ofReal ((p : ℝ) ^ (-1 : ℝ))

/-- Prime harmonic sequence is not in the fixed `ell^(1 : ℕ)` submodule. -/
theorem not_summable_primeHarmonicComplexSequence :
    ¬ Summable primeHarmonicComplexSequence := by
  intro h
  change Summable (fun p : Nat.Primes =>
    Complex.ofReal ((p : ℝ) ^ (-1 : ℝ))) at h
  have hr : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-1 : ℝ)) :=
    Complex.summable_ofReal.mp h
  exact Nat.Primes.not_summable_one_div
    (by simpa only [Real.rpow_neg_one, one_div] using hr)

/-- Explicit nonzero quotient-kernel representative: `r_t(p)/p`. -/
def markedCofinalKernelWitness (t : ℝ) : AllPrimeComplexSequence :=
  fun p => (markedCofinalComparisonWeight t p : ℂ) *
    Complex.ofReal ((p : ℝ) ^ (-1 : ℝ))

/-- The explicit quotient-kernel representative is summable throughout the open critical strip. -/
theorem summable_markedCofinalKernelWitness
    {t : ℝ} (ht : |t| < 1) :
    Summable (markedCofinalKernelWitness t) := by
  have htLower : -1 < t := neg_lt_of_abs_lt ht
  have hsummableModel : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-2 : ℝ) + (p : ℝ) ^ (-t - 2)) :=
    ((Nat.Primes.summable_rpow).2 (by norm_num)).add
      ((Nat.Primes.summable_rpow).2 (by linarith))
  have hreal : Summable (fun p : Nat.Primes =>
      markedCofinalComparisonWeight t p * (p : ℝ) ^ (-1 : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun p =>
      mul_nonneg (markedCofinalComparisonWeight_pos t p).le
        (Real.rpow_nonneg (by positivity) _)) (fun p => ?_)
      hsummableModel
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
    calc
      markedCofinalComparisonWeight t p * (p : ℝ) ^ (-1 : ℝ) ≤
          ((p : ℝ) ^ (-1 : ℝ) + (p : ℝ) ^ (-t - 1)) *
            (p : ℝ) ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (markedCofinalComparisonWeight_le_model t p) (by positivity)
      _ = (p : ℝ) ^ (-2 : ℝ) + (p : ℝ) ^ (-t - 2) := by
        rw [add_mul, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
        congr 1 <;> ring
  have hcomplex : Summable (fun p : Nat.Primes =>
      ((markedCofinalComparisonWeight t p * (p : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hreal
  change Summable (fun p : Nat.Primes =>
    (markedCofinalComparisonWeight t p : ℂ) *
      Complex.ofReal ((p : ℝ) ^ (-1 : ℝ)))
  simpa only [Complex.ofReal_mul] using hcomplex

/-- Reciprocal diagonal multiplication sends the summable witness to the nonsummable prime
harmonic sequence. -/
theorem reciprocal_weight_mul_kernelWitness
    (t : ℝ) :
    primeDiagonalMultiplier
        (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)⁻¹)
        (markedCofinalKernelWitness t) =
      primeHarmonicComplexSequence := by
  funext p
  simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk,
    markedCofinalKernelWitness, primeHarmonicComplexSequence]
  have hweight : (markedCofinalComparisonWeight t p : ℂ) ≠ 0 := by
    exact_mod_cast (markedCofinalComparisonWeight_pos t p).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hweight, one_mul]

/-- Reciprocal comparison does not preserve the fixed all-prime `ell^(1 : ℕ)` submodule. -/
theorem reciprocal_markedCofinalComparisonWeight_not_preservesL1
    {t : ℝ} (ht : |t| < 1) :
    ¬ PrimeDiagonalPreservesL1
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)⁻¹) := by
  intro hpreserves
  have hout := hpreserves (summable_markedCofinalKernelWitness ht)
  change Summable
    (primeDiagonalMultiplier
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)⁻¹)
      (markedCofinalKernelWitness t)) at hout
  rw [reciprocal_weight_mul_kernelWitness] at hout
  exact not_summable_primeHarmonicComplexSequence hout

/-- The reciprocal coefficient sequence is not bounded. -/
theorem reciprocal_markedCofinalComparisonWeight_not_isBounded
    {t : ℝ} (ht : |t| < 1) :
    ¬ Bornology.IsBounded
      (Set.range (fun p : Nat.Primes =>
        (markedCofinalComparisonWeight t p : ℂ)⁻¹)) := by
  intro hbounded
  exact reciprocal_markedCofinalComparisonWeight_not_preservesL1 ht
    (primeDiagonalPreservesL1_of_isBounded hbounded)

/-- Bounded comparison multiplication preserves `ell^(1 : ℕ)`. -/
theorem markedCofinalComparisonWeight_preservesL1
    {t : ℝ} (ht : |t| < 1) :
    PrimeDiagonalPreservesL1
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)) :=
  primeDiagonalPreservesL1_of_isBounded
    (markedCofinalComparisonWeight_isBounded ht)

/-- The comparison multiplier descends to the fixed algebraic all-prime quotient. -/
theorem markedCofinalComparisonWeight_hasQuotientMap
    {t : ℝ} (ht : |t| < 1) :
    HasPrimeDiagonalQuotientMap
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)) :=
  (hasPrimeDiagonalQuotientMap_iff_preservesL1 _).2
    (markedCofinalComparisonWeight_preservesL1 ht)

/-- The canonical reciprocal diagonal multiplier does not descend to the fixed quotient. -/
theorem reciprocal_markedCofinalComparisonWeight_not_hasQuotientMap
    {t : ℝ} (ht : |t| < 1) :
    ¬ HasPrimeDiagonalQuotientMap
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)⁻¹) := by
  rw [hasPrimeDiagonalQuotientMap_iff_preservesL1]
  exact reciprocal_markedCofinalComparisonWeight_not_preservesL1 ht

/-- The descended comparison multiplier is not injective. -/
theorem markedCofinalComparisonWeight_quotientMap_not_injective
    {t : ℝ} (ht : |t| < 1) :
    ¬ Function.Injective
      (primeDiagonalQuotientMap
        (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
        (markedCofinalComparisonWeight_preservesL1 ht)) := by
  intro hinjective
  let q := primeDiagonalQuotientMap
    (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
    (markedCofinalComparisonWeight_preservesL1 ht)
  have hqzero : q (Submodule.Quotient.mk primeHarmonicComplexSequence) = 0 := by
    rw [show q = primeDiagonalQuotientMap
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
      (markedCofinalComparisonWeight_preservesL1 ht) from rfl,
      primeDiagonalQuotientMap_mk,
      Submodule.Quotient.mk_eq_zero]
    exact summable_markedCofinalKernelWitness ht
  have hmkzero :
      (Submodule.Quotient.mk primeHarmonicComplexSequence : AllPrimeL1Quotient) = 0 := by
    apply hinjective
    simpa only [map_zero] using hqzero
  exact not_summable_primeHarmonicComplexSequence
    ((Submodule.Quotient.mk_eq_zero primeL1Submodule).1 hmkzero)

/-- The descended comparison multiplier remains surjective because pointwise division is
available on the full sequence space. -/
theorem markedCofinalComparisonWeight_quotientMap_surjective
    {t : ℝ} (ht : |t| < 1) :
    Function.Surjective
      (primeDiagonalQuotientMap
        (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
        (markedCofinalComparisonWeight_preservesL1 ht)) := by
  exact primeDiagonalQuotientMap_surjective _ _
    (fun p => by exact_mod_cast (markedCofinalComparisonWeight_pos t p).ne')

/-- The surjective quotient comparison has a noncanonical algebraic linear right splitting.
This records exactly why Theorem 7.1 is not a categorical nonsplitting result. -/
theorem markedCofinalComparisonWeight_quotientMap_has_linear_rightInverse
    {t : ℝ} (ht : |t| < 1) :
    ∃ S : AllPrimeL1Quotient →ₗ[ℂ] AllPrimeL1Quotient,
      (primeDiagonalQuotientMap
        (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
        (markedCofinalComparisonWeight_preservesL1 ht)).comp S = LinearMap.id := by
  let Q := primeDiagonalQuotientMap
    (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
    (markedCofinalComparisonWeight_preservesL1 ht)
  have hsurj : Function.Surjective Q :=
    markedCofinalComparisonWeight_quotientMap_surjective ht
  obtain ⟨S, hS⟩ := Q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨S, hS⟩

/-- Quotient-level Bockstein comparison `[b_t] = -M_{r_t}[κ_t]`. -/
theorem primeGammaCofinalBockstein_quotient_comparison
    {t : ℝ} (ht : |t| < 1) :
    Submodule.Quotient.mk
        (fun p : Nat.Primes => (primeGammaCofinalBocksteinCoefficient t p : ℂ)) =
      -primeDiagonalQuotientMap
        (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
        (markedCofinalComparisonWeight_preservesL1 ht)
        (Submodule.Quotient.mk
          (fun p : Nat.Primes => (((p : ℝ) ^ t - 1 : ℝ) : ℂ))) := by
  rw [primeDiagonalQuotientMap_mk]
  apply congrArg Submodule.Quotient.mk
  funext p
  change (primeGammaCofinalBocksteinCoefficient t p : ℂ) =
    -((markedCofinalComparisonWeight t p : ℂ) * (((p : ℝ) ^ t - 1 : ℝ) : ℂ))
  exact_mod_cast (by
    rw [primeGammaCofinalBocksteinCoefficient_eq_neg_weight_mul_curvature]
    ring : primeGammaCofinalBocksteinCoefficient t p =
      -(markedCofinalComparisonWeight t p * ((p : ℝ) ^ t - 1)))

/-- Bundled exact form of the all-prime diagonal-inverse obstruction. -/
theorem markedCofinalDiagonalInverseObstruction
    {t : ℝ} (ht : |t| < 1) :
    Tendsto (markedCofinalComparisonWeight t) cofinite (𝓝 0) ∧
    Bornology.IsBounded
      (Set.range (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))) ∧
    ¬ Bornology.IsBounded
      (Set.range (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)⁻¹)) ∧
    HasPrimeDiagonalQuotientMap
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)) ∧
    ¬ HasPrimeDiagonalQuotientMap
      (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ)⁻¹) ∧
    ¬ Function.Injective
      (primeDiagonalQuotientMap
        (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
        (markedCofinalComparisonWeight_preservesL1 ht)) ∧
    Function.Surjective
      (primeDiagonalQuotientMap
        (fun p : Nat.Primes => (markedCofinalComparisonWeight t p : ℂ))
        (markedCofinalComparisonWeight_preservesL1 ht)) := by
  exact ⟨markedCofinalComparisonWeight_tendsto_cofinite_zero ht,
    markedCofinalComparisonWeight_isBounded ht,
    reciprocal_markedCofinalComparisonWeight_not_isBounded ht,
    markedCofinalComparisonWeight_hasQuotientMap ht,
    reciprocal_markedCofinalComparisonWeight_not_hasQuotientMap ht,
    markedCofinalComparisonWeight_quotientMap_not_injective ht,
    markedCofinalComparisonWeight_quotientMap_surjective ht⟩

end

end RHTower
