import GaloisForLFunctions.RHTower.MarkedHalfCharacterCofinalDiagonalInverseLaw

/-!
# Fisher-deconvolved same-carrier orientation law

The ordinary comparison coefficient factors as

`r_t(p) = d(p) * (1 + p^(-t))`,

where `d` is the source-selected Euler--Fisher density.  This module moves `d` into one fixed
weighted `ell^1` ideal.  The remaining normalized multiplier is then a coefficient-faithful
quotient automorphism exactly in one horizontal chamber; its reflected multiplier is an
automorphism in the opposite chamber.  Both descend on the same fixed carrier exactly at neutral
grade.

No Xi zero or critical-line hypothesis occurs in the construction.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Fixed Fisher-weighted carrier -/

/-- Preimage of literal prime `ell^1` under multiplication by the source Euler--Fisher density. -/
def fisherWeightedPrimeL1Submodule : Submodule ℂ AllPrimeComplexSequence :=
  Submodule.comap
    (primeDiagonalMultiplier
      (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ)))
    primeL1Submodule

/-- Fixed all-prime carrier after moving the Euler--Fisher density into the source ideal. -/
abbrev FisherDeconvolvedPrimeCarrier :=
  AllPrimeComplexSequence ⧸ fisherWeightedPrimeL1Submodule

/-- A diagonal multiplier preserves the fixed Fisher-weighted source ideal. -/
def PrimeDiagonalPreservesFisherWeightedL1 (m : AllPrimeComplexSequence) : Prop :=
  fisherWeightedPrimeL1Submodule ≤
    Submodule.comap (primeDiagonalMultiplier m) fisherWeightedPrimeL1Submodule

/-- Literal Euler--Fisher density is positive at every ordinary prime. -/
theorem primeActivationOccupancyFisherDensity_pos' (p : Nat.Primes) :
    0 < primeActivationOccupancyFisherDensity p := by
  rw [primeActivationOccupancyFisherDensity_eq]
  exact div_pos (by exact_mod_cast p.2.pos) (sq_pos_of_pos (by positivity))

/-- Moving the nowhere-zero Fisher density into the ideal does not change the diagonal
multiplier criterion: preservation is still exactly preservation of every `ell^1` sequence. -/
theorem primeDiagonalPreservesFisherWeightedL1_iff_preservesL1
    (m : AllPrimeComplexSequence) :
    PrimeDiagonalPreservesFisherWeightedL1 m ↔ PrimeDiagonalPreservesL1 m := by
  constructor
  · intro hm y hy
    change Summable y at hy
    let d : AllPrimeComplexSequence :=
      fun p => (primeActivationOccupancyFisherDensity p : ℂ)
    let x : AllPrimeComplexSequence := fun p => y p / d p
    have hd (p : Nat.Primes) : d p ≠ 0 := by
      dsimp [d]
      exact_mod_cast (primeActivationOccupancyFisherDensity_pos' p).ne'
    have hx : x ∈ fisherWeightedPrimeL1Submodule := by
      change Summable (primeDiagonalMultiplier d x)
      rw [show primeDiagonalMultiplier d x = y by
        funext p
        simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk, x]
        exact mul_div_cancel₀ (y p) (hd p)]
      exact hy
    have hout := hm hx
    change Summable
      (primeDiagonalMultiplier d (primeDiagonalMultiplier m x)) at hout
    change Summable (primeDiagonalMultiplier m y)
    rw [show primeDiagonalMultiplier m y =
        primeDiagonalMultiplier d (primeDiagonalMultiplier m x) by
      funext p
      simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk, x]
      field_simp [hd p]]
    exact hout
  · intro hm x hx
    change Summable
      (primeDiagonalMultiplier
        (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ)) x) at hx
    have hout := hm hx
    change Summable
      (primeDiagonalMultiplier m
        (primeDiagonalMultiplier
          (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ)) x)) at hout
    change Summable
      (primeDiagonalMultiplier
        (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ))
        (primeDiagonalMultiplier m x))
    rw [show primeDiagonalMultiplier
        (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ))
          (primeDiagonalMultiplier m x) =
        primeDiagonalMultiplier m
          (primeDiagonalMultiplier
            (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ)) x) by
      funext p
      simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk]
      ring]
    exact hout

/-- Exact boundedness criterion on the Fisher-weighted source ideal. -/
theorem primeDiagonalPreservesFisherWeightedL1_iff_isBounded
    (m : AllPrimeComplexSequence) :
    PrimeDiagonalPreservesFisherWeightedL1 m ↔
      Bornology.IsBounded (Set.range m) := by
  rw [primeDiagonalPreservesFisherWeightedL1_iff_preservesL1,
    primeDiagonalPreservesL1_iff_isBounded]

/-! ## Canonical Fisher deconvolution equivalence -/

/-- Multiplication by Fisher density sends the deconvolved carrier to the ordinary `ell^1`
quotient. -/
def fisherDensityPrimeCarrierMap :
    FisherDeconvolvedPrimeCarrier →ₗ[ℂ] AllPrimeL1Quotient :=
  Submodule.mapQ fisherWeightedPrimeL1Submodule primeL1Submodule
    (primeDiagonalMultiplier
      (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ)))
    (by
      intro x hx
      exact hx)

/-- Pointwise Fisher division is the inverse map between the two different quotient ideals. -/
def inverseFisherDensityPrimeCarrierMap :
    AllPrimeL1Quotient →ₗ[ℂ] FisherDeconvolvedPrimeCarrier :=
  Submodule.mapQ primeL1Submodule fisherWeightedPrimeL1Submodule
    (primeDiagonalMultiplier
      (fun p : Nat.Primes =>
        (primeActivationOccupancyFisherDensity p : ℂ)⁻¹))
    (by
      intro y hy
      change Summable
        (primeDiagonalMultiplier
          (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ))
          (primeDiagonalMultiplier
            (fun p : Nat.Primes =>
              (primeActivationOccupancyFisherDensity p : ℂ)⁻¹) y))
      rw [show primeDiagonalMultiplier
          (fun p : Nat.Primes => (primeActivationOccupancyFisherDensity p : ℂ))
          (primeDiagonalMultiplier
            (fun p : Nat.Primes =>
              (primeActivationOccupancyFisherDensity p : ℂ)⁻¹) y) = y by
        funext p
        simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← mul_assoc, mul_inv_cancel₀]
        · exact one_mul (y p)
        · exact_mod_cast (primeActivationOccupancyFisherDensity_pos' p).ne']
      exact hy)

theorem fisherDensityPrimeCarrierMap_comp_inverse :
    fisherDensityPrimeCarrierMap.comp inverseFisherDensityPrimeCarrierMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective primeL1Submodule q
  rw [LinearMap.comp_apply, fisherDensityPrimeCarrierMap,
    inverseFisherDensityPrimeCarrierMap, Submodule.mapQ_apply,
    Submodule.mapQ_apply, LinearMap.id_apply]
  congr 1
  funext p
  simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, mul_inv_cancel₀]
  · exact one_mul (f p)
  · exact_mod_cast (primeActivationOccupancyFisherDensity_pos' p).ne'

theorem inverseFisherDensityPrimeCarrierMap_comp :
    inverseFisherDensityPrimeCarrierMap.comp fisherDensityPrimeCarrierMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ :=
    Submodule.Quotient.mk_surjective fisherWeightedPrimeL1Submodule q
  rw [LinearMap.comp_apply, fisherDensityPrimeCarrierMap,
    inverseFisherDensityPrimeCarrierMap, Submodule.mapQ_apply,
    Submodule.mapQ_apply, LinearMap.id_apply]
  congr 1
  funext p
  simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, inv_mul_cancel₀]
  · exact one_mul (f p)
  · exact_mod_cast (primeActivationOccupancyFisherDensity_pos' p).ne'

/-- Canonical linear equivalence expressing exact Fisher deconvolution at quotient level. -/
def fisherDeconvolvedPrimeCarrierEquiv :
    FisherDeconvolvedPrimeCarrier ≃ₗ[ℂ] AllPrimeL1Quotient :=
  LinearEquiv.ofLinear fisherDensityPrimeCarrierMap inverseFisherDensityPrimeCarrierMap
    fisherDensityPrimeCarrierMap_comp_inverse
    inverseFisherDensityPrimeCarrierMap_comp

/-! ## Oriented normalized transport -/

/-- Comparison weight after removing only the universal Euler--Fisher density. -/
def fisherDeconvolvedComparisonWeight (t : ℝ) (p : Nat.Primes) : ℝ :=
  1 + (p : ℝ) ^ (-t)

/-- Every normalized transport coefficient is strictly positive. -/
theorem fisherDeconvolvedComparisonWeight_pos (t : ℝ) (p : Nat.Primes) :
    0 < fisherDeconvolvedComparisonWeight t p := by
  rw [fisherDeconvolvedComparisonWeight]
  positivity

/-- In the nonnegative horizontal chamber, normalized coefficients are uniformly bounded by
two. -/
theorem fisherDeconvolvedComparisonWeight_isBounded_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    Bornology.IsBounded
      (Set.range (fun p : Nat.Primes =>
        (fisherDeconvolvedComparisonWeight t p : ℂ))) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨2, ?_⟩
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  rw [Complex.norm_real, Real.norm_of_nonneg
    (fisherDeconvolvedComparisonWeight_pos t p).le]
  rw [fisherDeconvolvedComparisonWeight]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  have hpow : (p : ℝ) ^ (-t) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr ht)
  linarith

/-- In the negative horizontal chamber, normalized coefficients diverge along ordinary primes. -/
theorem fisherDeconvolvedComparisonWeight_tendsto_atTop_of_neg
    {t : ℝ} (ht : t < 0) :
    Tendsto (fisherDeconvolvedComparisonWeight t) cofinite atTop := by
  change Tendsto (fun p : Nat.Primes => 1 + (p : ℝ) ^ (-t)) cofinite atTop
  have hpNat : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Nat.Primes.coe_nat_injective.tendsto_cofinite
  have hpReal : Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop :=
    tendsto_natCast_atTop_atTop.comp hpNat
  have hpow : Tendsto (fun p : Nat.Primes => (p : ℝ) ^ (-t)) cofinite atTop :=
    (tendsto_rpow_atTop (neg_pos.mpr ht)).comp hpReal
  exact tendsto_const_nhds.add_atTop hpow

theorem fisherDeconvolvedComparisonWeight_not_isBounded_of_neg
    {t : ℝ} (ht : t < 0) :
    ¬ Bornology.IsBounded
      (Set.range (fun p : Nat.Primes =>
        (fisherDeconvolvedComparisonWeight t p : ℂ))) := by
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hevent : ∀ᶠ p : Nat.Primes in cofinite,
      C < fisherDeconvolvedComparisonWeight t p :=
    (fisherDeconvolvedComparisonWeight_tendsto_atTop_of_neg ht).eventually_gt_atTop C
  obtain ⟨p, hp⟩ := hevent.exists
  have hbound := hC
    (fisherDeconvolvedComparisonWeight t p : ℂ) ⟨p, rfl⟩
  rw [Complex.norm_real, Real.norm_of_nonneg
    (fisherDeconvolvedComparisonWeight_pos t p).le] at hbound
  exact (not_lt_of_ge hbound) hp

/-- Sharp boundedness wall for one normalized orientation. -/
theorem fisherDeconvolvedComparisonWeight_isBounded_iff
    (t : ℝ) :
    Bornology.IsBounded
      (Set.range (fun p : Nat.Primes =>
        (fisherDeconvolvedComparisonWeight t p : ℂ))) ↔ 0 ≤ t := by
  constructor
  · intro hb
    by_contra ht
    exact fisherDeconvolvedComparisonWeight_not_isBounded_of_neg
      (lt_of_not_ge ht) hb
  · exact fisherDeconvolvedComparisonWeight_isBounded_of_nonneg

/-- A normalized orientation preserves the fixed source ideal exactly in its half-space. -/
theorem fisherDeconvolvedComparisonWeight_preserves_iff (t : ℝ) :
    PrimeDiagonalPreservesFisherWeightedL1
      (fun p : Nat.Primes => (fisherDeconvolvedComparisonWeight t p : ℂ)) ↔
      0 ≤ t := by
  rw [primeDiagonalPreservesFisherWeightedL1_iff_isBounded,
    fisherDeconvolvedComparisonWeight_isBounded_iff]

/-- Forward and reflected normalized orientations preserve the same fixed ideal exactly at neutral
grade. -/
theorem both_fisherDeconvolvedComparisonWeights_preserve_iff (t : ℝ) :
    (PrimeDiagonalPreservesFisherWeightedL1
        (fun p : Nat.Primes => (fisherDeconvolvedComparisonWeight t p : ℂ)) ∧
      PrimeDiagonalPreservesFisherWeightedL1
        (fun p : Nat.Primes => (fisherDeconvolvedComparisonWeight (-t) p : ℂ))) ↔
      t = 0 := by
  rw [fisherDeconvolvedComparisonWeight_preserves_iff,
    fisherDeconvolvedComparisonWeight_preserves_iff]
  constructor
  · rintro ⟨ht, hneg⟩
    linarith
  · rintro rfl
    norm_num

/-! ## Literal quotient maps and coefficient faithfulness -/

/-- Existence of a prescribed diagonal action on the fixed Fisher-deconvolved quotient. -/
def HasFisherDeconvolvedPrimeDiagonalQuotientMap
    (m : AllPrimeComplexSequence) : Prop :=
  ∃ Q : FisherDeconvolvedPrimeCarrier →ₗ[ℂ] FisherDeconvolvedPrimeCarrier,
    ∀ f : AllPrimeComplexSequence,
      Q (Submodule.Quotient.mk f) =
        Submodule.Quotient.mk (primeDiagonalMultiplier m f)

/-- Canonical quotient map produced by preservation of the fixed source ideal. -/
def fisherDeconvolvedPrimeDiagonalQuotientMap
    (m : AllPrimeComplexSequence)
    (hm : PrimeDiagonalPreservesFisherWeightedL1 m) :
    FisherDeconvolvedPrimeCarrier →ₗ[ℂ] FisherDeconvolvedPrimeCarrier :=
  Submodule.mapQ fisherWeightedPrimeL1Submodule fisherWeightedPrimeL1Submodule
    (primeDiagonalMultiplier m) hm

@[simp]
theorem fisherDeconvolvedPrimeDiagonalQuotientMap_mk
    (m : AllPrimeComplexSequence)
    (hm : PrimeDiagonalPreservesFisherWeightedL1 m)
    (f : AllPrimeComplexSequence) :
    fisherDeconvolvedPrimeDiagonalQuotientMap m hm (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (primeDiagonalMultiplier m f) := by
  exact Submodule.mapQ_apply fisherWeightedPrimeL1Submodule
    fisherWeightedPrimeL1Submodule (primeDiagonalMultiplier m) f

/-- A prescribed quotient action exists exactly when its representative multiplier preserves the
fixed Fisher ideal. -/
theorem hasFisherDeconvolvedPrimeDiagonalQuotientMap_iff
    (m : AllPrimeComplexSequence) :
    HasFisherDeconvolvedPrimeDiagonalQuotientMap m ↔
      PrimeDiagonalPreservesFisherWeightedL1 m := by
  constructor
  · rintro ⟨Q, hQ⟩ f hf
    have hzero :
        (Submodule.Quotient.mk f : FisherDeconvolvedPrimeCarrier) = 0 :=
      (Submodule.Quotient.mk_eq_zero fisherWeightedPrimeL1Submodule).2 hf
    have hout :
        (Submodule.Quotient.mk (primeDiagonalMultiplier m f) :
          FisherDeconvolvedPrimeCarrier) = 0 := by
      rw [← hQ f, hzero, map_zero]
    exact (Submodule.Quotient.mk_eq_zero fisherWeightedPrimeL1Submodule).1 hout
  · intro hm
    exact ⟨fisherDeconvolvedPrimeDiagonalQuotientMap m hm,
      fisherDeconvolvedPrimeDiagonalQuotientMap_mk m hm⟩

/-- Reciprocal normalized coefficients are bounded by one at every real grade. -/
theorem reciprocal_fisherDeconvolvedComparisonWeight_isBounded (t : ℝ) :
    Bornology.IsBounded
      (Set.range (fun p : Nat.Primes =>
        (fisherDeconvolvedComparisonWeight t p : ℂ)⁻¹)) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (fisherDeconvolvedComparisonWeight_pos t p).le]
  rw [inv_le_one₀ (fisherDeconvolvedComparisonWeight_pos t p)]
  rw [fisherDeconvolvedComparisonWeight]
  exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)

/-- Reciprocal normalized multiplication always preserves the fixed Fisher ideal. -/
theorem reciprocal_fisherDeconvolvedComparisonWeight_preserves (t : ℝ) :
    PrimeDiagonalPreservesFisherWeightedL1
      (fun p : Nat.Primes =>
        (fisherDeconvolvedComparisonWeight t p : ℂ)⁻¹) :=
  (primeDiagonalPreservesFisherWeightedL1_iff_isBounded _).2
    (reciprocal_fisherDeconvolvedComparisonWeight_isBounded t)

/-- Whenever the normalized transport descends, its canonical quotient map is bijective. This is
the coefficient-faithfulness statement: Fisher deconvolution turns the comparison into an actual
automorphism, not the surjective noninjective map on `S / ell^1`. -/
theorem fisherDeconvolvedComparisonWeight_quotientMap_bijective
    {t : ℝ} (ht : 0 ≤ t) :
    Function.Bijective
      (fisherDeconvolvedPrimeDiagonalQuotientMap
        (fun p : Nat.Primes => (fisherDeconvolvedComparisonWeight t p : ℂ))
        ((fisherDeconvolvedComparisonWeight_preserves_iff t).2 ht)) := by
  let m : AllPrimeComplexSequence :=
    fun p => (fisherDeconvolvedComparisonWeight t p : ℂ)
  let hm : PrimeDiagonalPreservesFisherWeightedL1 m :=
    (fisherDeconvolvedComparisonWeight_preserves_iff t).2 ht
  let mi : AllPrimeComplexSequence := fun p => (m p)⁻¹
  let hmi : PrimeDiagonalPreservesFisherWeightedL1 mi :=
    reciprocal_fisherDeconvolvedComparisonWeight_preserves t
  let Q := fisherDeconvolvedPrimeDiagonalQuotientMap m hm
  let R := fisherDeconvolvedPrimeDiagonalQuotientMap mi hmi
  have hRQ : R.comp Q = LinearMap.id := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ :=
      Submodule.Quotient.mk_surjective fisherWeightedPrimeL1Submodule q
    rw [LinearMap.comp_apply, fisherDeconvolvedPrimeDiagonalQuotientMap_mk,
      fisherDeconvolvedPrimeDiagonalQuotientMap_mk, LinearMap.id_apply]
    congr 1
    funext p
    simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk, mi, m]
    rw [← mul_assoc, inv_mul_cancel₀]
    · exact one_mul (f p)
    · exact_mod_cast (fisherDeconvolvedComparisonWeight_pos t p).ne'
  have hQR : Q.comp R = LinearMap.id := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ :=
      Submodule.Quotient.mk_surjective fisherWeightedPrimeL1Submodule q
    rw [LinearMap.comp_apply, fisherDeconvolvedPrimeDiagonalQuotientMap_mk,
      fisherDeconvolvedPrimeDiagonalQuotientMap_mk, LinearMap.id_apply]
    congr 1
    funext p
    simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk, mi, m]
    rw [← mul_assoc, mul_inv_cancel₀]
    · exact one_mul (f p)
    · exact_mod_cast (fisherDeconvolvedComparisonWeight_pos t p).ne'
  have hleft : Function.LeftInverse R Q := fun q => by
    have h := LinearMap.congr_fun hRQ q
    simpa [LinearMap.comp_apply] using h
  have hright : Function.RightInverse R Q := fun q => by
    have h := LinearMap.congr_fun hQR q
    simpa [LinearMap.comp_apply] using h
  exact ⟨hleft.injective, hright.surjective⟩

/-- **Same-carrier orientation law.** Forward and reflected normalized transports have prescribed
maps on one fixed Fisher-deconvolved carrier exactly at neutral horizontal grade. -/
theorem fisherDeconvolvedSameCarrierOrientationLaw (t : ℝ) :
    (HasFisherDeconvolvedPrimeDiagonalQuotientMap
        (fun p : Nat.Primes => (fisherDeconvolvedComparisonWeight t p : ℂ)) ∧
      HasFisherDeconvolvedPrimeDiagonalQuotientMap
        (fun p : Nat.Primes => (fisherDeconvolvedComparisonWeight (-t) p : ℂ))) ↔
      t = 0 := by
  rw [hasFisherDeconvolvedPrimeDiagonalQuotientMap_iff,
    hasFisherDeconvolvedPrimeDiagonalQuotientMap_iff,
    both_fisherDeconvolvedComparisonWeights_preserve_iff]

/-- At neutral grade, both normalized orientations are literally multiplication by two. -/
theorem fisherDeconvolvedComparisonWeight_zero (p : Nat.Primes) :
    fisherDeconvolvedComparisonWeight 0 p = 2 := by
  simp [fisherDeconvolvedComparisonWeight]
  norm_num

/-! ## Exact arithmetic coefficient comparison -/

/-- The existing comparison coefficient is Fisher density times normalized transport. -/
theorem markedCofinalComparisonWeight_eq_fisherDensity_mul_deconvolved
    (t : ℝ) (p : Nat.Primes) :
    markedCofinalComparisonWeight t p =
      primeActivationOccupancyFisherDensity p *
        fisherDeconvolvedComparisonWeight t p := by
  rfl

/-- Exact Bockstein factorization with Fisher density stored separately from normalized transport. -/
theorem primeGammaCofinalBocksteinCoefficient_eq_fisherDeconvolved
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient t p =
      -primeActivationOccupancyFisherDensity p *
        fisherDeconvolvedComparisonWeight t p * ((p : ℝ) ^ t - 1) := by
  rw [primeGammaCofinalBocksteinCoefficient_eq_neg_weight_mul_curvature,
    markedCofinalComparisonWeight_eq_fisherDensity_mul_deconvolved]
  ring

/-! ## Both coefficient fields on one fixed carrier -/

/-- Normalized orientation as a literal class of the fixed Fisher-deconvolved quotient. Both
reflection orientations are defined in this same type for every real grade. -/
def fisherDeconvolvedOrientationClass (t : ℝ) :
    FisherDeconvolvedPrimeCarrier :=
  Submodule.Quotient.mk
    (fun p : Nat.Primes => (fisherDeconvolvedComparisonWeight t p : ℂ))

/-- Multiplying the normalized reflected difference by Fisher density recovers the exact signed
Gamma Bockstein coefficient, prime by prime. -/
theorem fisherDensity_mul_deconvolved_orientationDifference
    (t : ℝ) (p : Nat.Primes) :
    primeActivationOccupancyFisherDensity p *
        (fisherDeconvolvedComparisonWeight t p -
          fisherDeconvolvedComparisonWeight (-t) p) =
      primeGammaCofinalBocksteinCoefficient t p := by
  rw [fisherDeconvolvedComparisonWeight,
    fisherDeconvolvedComparisonWeight,
    primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist]
  ring_nf

/-- **Coefficient-field identification law.** The two normalized reflection transports are
literal elements of one fixed source carrier, and they coincide there exactly at neutral grade.
The proof uses absolute summability of their exact Gamma-Bockstein difference, so no bounded
scalar reader or equivariance premise enters. -/
theorem fisherDeconvolvedOrientationClass_eq_reflected_iff (t : ℝ) :
    fisherDeconvolvedOrientationClass t =
        fisherDeconvolvedOrientationClass (-t) ↔
      t = 0 := by
  rw [← sub_eq_zero, fisherDeconvolvedOrientationClass,
    fisherDeconvolvedOrientationClass, ← Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_eq_zero]
  have hweighted : (fun p : Nat.Primes =>
      (primeActivationOccupancyFisherDensity p : ℂ) *
        ((fisherDeconvolvedComparisonWeight t p : ℂ) -
          (fisherDeconvolvedComparisonWeight (-t) p : ℂ))) =
      fun p : Nat.Primes => (primeGammaCofinalBocksteinCoefficient t p : ℂ) := by
    funext p
    exact_mod_cast fisherDensity_mul_deconvolved_orientationDifference t p
  change Summable (fun p : Nat.Primes =>
    (primeActivationOccupancyFisherDensity p : ℂ) *
      ((fisherDeconvolvedComparisonWeight t p : ℂ) -
        (fisherDeconvolvedComparisonWeight (-t) p : ℂ))) ↔ t = 0
  rw [hweighted]
  have hnorm : (fun p : Nat.Primes =>
      ‖(primeGammaCofinalBocksteinCoefficient t p : ℂ)‖) =
      primeGammaCofinalBocksteinMagnitude t := by
    funext p
    rw [Complex.norm_real]
    rfl
  rw [← summable_norm_iff, hnorm,
    summable_primeGammaCofinalBocksteinMagnitude_iff]

end


end RHTower
