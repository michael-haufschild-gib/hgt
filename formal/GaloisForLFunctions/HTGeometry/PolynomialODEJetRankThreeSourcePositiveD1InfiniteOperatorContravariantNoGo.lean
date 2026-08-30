import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1MatrixContravariantNoGo

/-!
# No infinite positive operator-channel contravariant D1 carrier

The finite matrix-channel obstruction is not finite-dimensional.  Let the channel be an arbitrary
nontrivial complex Hilbert space and let the coefficient and every value of the D1 carrier pairing
be bounded operators.  Literal strict positivity of a nonzero diagonal pairing,

`0 < re ⟪z, pair p p z⟫` for every nonzero channel vector `z`,

makes that diagonal operator injective.  It also gives dense range directly: a vector orthogonal
to its range would contradict strict positivity when inserted into both slots.  Consequently a
bounded channel coefficient annihilated on either side by a positive diagonal must vanish.

The exact D1-generated vacuum string then gives the same two-step contradiction for both canonical
contravariant actions.  This uses neither finite dimension, determinant invertibility, coercivity,
separability, nor compactness.  Thus a positive bounded infinite-channel Shapovalov escape cannot
carry actual source D1.  Any representation-theoretic survivor must be singular/unbounded,
indefinite, or abandon the contravariant operator-pairing mechanism; direct cross-scale Hankel
geometry remains unaffected.
-/

open Complex Real

namespace HTGeometry

noncomputable section

section OperatorLemmas

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Strict quadratic positivity makes a bounded operator injective, without a coercivity floor. -/
theorem continuousLinearMap_injective_of_strictQuadraticPositive
    {T : K →L[ℂ] K}
    (hT : ∀ z : K, z ≠ 0 → 0 < (inner ℂ z (T z)).re) :
    Function.Injective T := by
  intro x y hxy
  have hzero : T (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hdiff : x - y = 0 := by
    by_contra hne
    have hpos := hT (x - y) hne
    rw [hzero, inner_zero_right] at hpos
    exact lt_irrefl 0 hpos
  exact sub_eq_zero.mp hdiff

variable [CompleteSpace K]

/-- Strict quadratic positivity also makes the range dense.  No self-adjointness field is needed:
orthogonality to the range can be tested on the same vector used in the positive quadratic form. -/
theorem continuousLinearMap_denseRange_of_strictQuadraticPositive
    {T : K →L[ℂ] K}
    (hT : ∀ z : K, z ≠ 0 → 0 < (inner ℂ z (T z)).re) :
    DenseRange T := by
  set M : Submodule ℂ K := LinearMap.range (T : K →ₗ[ℂ] K) with hM
  have hperp : Mᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    by_contra hz0
    have horth : inner ℂ (T z) z = 0 :=
      (Submodule.mem_orthogonal M z).mp hz (T z) ⟨z, rfl⟩
    have horth' : inner ℂ z (T z) = 0 := by
      have h := congrArg star horth
      simpa [inner_conj_symm] using h
    have hpos := hT z hz0
    rw [horth'] at hpos
    exact lt_irrefl 0 hpos
  have hclos := Submodule.orthogonal_orthogonal_eq_closure M
  rw [hperp, Submodule.bot_orthogonal_eq_top] at hclos
  have hdense : Dense (M : Set K) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos.symm
  have hset : (M : Set K) = Set.range (T : K → K) := by
    ext y
    simp [hM, LinearMap.mem_range, Set.mem_range]
  rw [hset] at hdense
  exact hdense

end OperatorLemmas

section OperatorCancellation

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- A bounded operator vanishing after a dense-range operator vanishes everywhere. -/
theorem continuousLinearMap_eq_zero_of_comp_eq_zero_of_denseRange
    {A C : K →L[ℂ] K} (hA : DenseRange A) (hCA : C * A = 0) : C = 0 := by
  have heq : (C : K → K) = fun _ => 0 :=
    C.continuous.ext_on hA continuous_const (by
      rintro _ ⟨y, rfl⟩
      have h := congrArg (fun T : K →L[ℂ] K => T y) hCA
      simpa using h)
  apply ContinuousLinearMap.ext
  intro z
  simpa using congrFun heq z

/-- An injective left factor cancels a zero bounded-operator product. -/
theorem continuousLinearMap_eq_zero_of_mul_eq_zero_of_injective
    {A C : K →L[ℂ] K} (hA : Function.Injective A) (hAC : A * C = 0) : C = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply hA
  have h := congrArg (fun T : K →L[ℂ] K => T z) hAC
  simpa using h

end OperatorCancellation

section D1Carrier

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [Nontrivial K]

/-- Positive bounded operator-valued contravariant data on an arbitrary source-`sl₂`-stable
polynomial carrier containing D1, with the adjoint coefficient acting on the right channel. -/
structure ModularThetaSourcePositiveD1RightOperatorContravariantCarrier where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  coefficient : K →L[ℂ] K
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → K →L[ℂ] K
  smul_left : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair (a • p) q = star a • pair p q
  smul_right : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair p (a • q) = a • pair p q
  positive : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → ∀ z : K, z ≠ 0 →
      0 < (inner ℂ z (pair p p z)).re
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        pair p (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q) *
          coefficient

omit [CompleteSpace K] [Nontrivial K] in
theorem ModularThetaSourcePositiveD1RightOperatorContravariantCarrier.sl2FIterate_mem
    (B : ModularThetaSourcePositiveD1RightOperatorContravariantCarrier (K := K))
    (n : ℕ) {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ B.carrier) :
    modularThetaSourcePositiveSl2FIterate n P ∈ B.carrier := by
  induction n with
  | zero => exact hP
  | succ n ih => exact B.sl2F_mem _ ih

omit [CompleteSpace K] in
/-- No positive bounded-operator right contravariant lift on any nontrivial Hilbert
channel contains actual source D1. -/
theorem modularThetaSourcePositive_no_D1_rightOperatorContravariantCarrier :
    ¬ Nonempty (ModularThetaSourcePositiveD1RightOperatorContravariantCarrier (K := K)) := by
  rintro ⟨B⟩
  rcases exists_modularThetaSourcePositiveReflectedEighth_vacuumString with
    ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, _hHv, hEv⟩
  have hcomponent : modularThetaSourcePositiveAdaptedComponent (n + 1)
      modularThetaSourcePositiveReflectedEighthPolynomial ∈ B.carrier :=
    modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
      B.carrier B.sl2E_mem B.sl2F_mem B.d1_mem (n + 1)
  have hvMem : v ∈ B.carrier := by
    rw [hvgen]
    exact B.sl2FIterate_mem n hcomponent
  have huMem : u ∈ B.carrier := by
    rw [hugen]
    exact B.sl2FIterate_mem (n + 1) hcomponent
  have hEvMem : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ∈
      B.carrier := B.sl2E_mem v hvMem
  have hzeroLeft : B.pair 0 v = 0 := by
    have h := B.smul_left (0 : ℂ) u v
    simpa using h
  have hcontra := B.contravariant u v huMem hvMem
  rw [hEu, hFv, hzeroLeft] at hcontra
  have hdiagInj : Function.Injective (B.pair u u) :=
    continuousLinearMap_injective_of_strictQuadraticPositive (B.positive u huMem hu)
  have hcoefficient : B.coefficient = 0 :=
    continuousLinearMap_eq_zero_of_mul_eq_zero_of_injective hdiagInj hcontra.symm
  have hcontraEv := B.contravariant v
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hvMem hEvMem
  rw [hcoefficient, mul_zero] at hcontraEv
  have hpairZero : B.pair
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v) = 0 :=
    hcontraEv
  obtain ⟨z, hz⟩ := exists_ne (0 : K)
  have hpos := B.positive
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hEvMem hEv z hz
  rw [hpairZero, zero_apply, inner_zero_right] at hpos
  exact lt_irrefl 0 hpos

/-- Positive bounded operator-valued contravariant data with the adjoint coefficient acting on the
left channel. -/
structure ModularThetaSourcePositiveD1LeftOperatorContravariantCarrier where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  coefficient : K →L[ℂ] K
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → K →L[ℂ] K
  smul_left : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair (a • p) q = star a • pair p q
  smul_right : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair p (a • q) = a • pair p q
  positive : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → ∀ z : K, z ≠ 0 →
      0 < (inner ℂ z (pair p p z)).re
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        coefficient *
          pair p (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q)

omit [CompleteSpace K] [Nontrivial K] in
theorem ModularThetaSourcePositiveD1LeftOperatorContravariantCarrier.sl2FIterate_mem
    (B : ModularThetaSourcePositiveD1LeftOperatorContravariantCarrier (K := K))
    (n : ℕ) {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ B.carrier) :
    modularThetaSourcePositiveSl2FIterate n P ∈ B.carrier := by
  induction n with
  | zero => exact hP
  | succ n ih => exact B.sl2F_mem _ ih

/-- No positive bounded-operator left contravariant lift on any nontrivial complete Hilbert
channel contains actual source D1. -/
theorem modularThetaSourcePositive_no_D1_leftOperatorContravariantCarrier :
    ¬ Nonempty (ModularThetaSourcePositiveD1LeftOperatorContravariantCarrier (K := K)) := by
  rintro ⟨B⟩
  rcases exists_modularThetaSourcePositiveReflectedEighth_vacuumString with
    ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, _hHv, hEv⟩
  have hcomponent : modularThetaSourcePositiveAdaptedComponent (n + 1)
      modularThetaSourcePositiveReflectedEighthPolynomial ∈ B.carrier :=
    modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
      B.carrier B.sl2E_mem B.sl2F_mem B.d1_mem (n + 1)
  have hvMem : v ∈ B.carrier := by
    rw [hvgen]
    exact B.sl2FIterate_mem n hcomponent
  have huMem : u ∈ B.carrier := by
    rw [hugen]
    exact B.sl2FIterate_mem (n + 1) hcomponent
  have hEvMem : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ∈
      B.carrier := B.sl2E_mem v hvMem
  have hzeroLeft : B.pair 0 v = 0 := by
    have h := B.smul_left (0 : ℂ) u v
    simpa using h
  have hcontra := B.contravariant u v huMem hvMem
  rw [hEu, hFv, hzeroLeft] at hcontra
  have hdiagDense : DenseRange (B.pair u u) :=
    continuousLinearMap_denseRange_of_strictQuadraticPositive (B.positive u huMem hu)
  have hcoefficient : B.coefficient = 0 :=
    continuousLinearMap_eq_zero_of_comp_eq_zero_of_denseRange hdiagDense hcontra.symm
  have hcontraEv := B.contravariant v
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hvMem hEvMem
  rw [hcoefficient, zero_mul] at hcontraEv
  have hpairZero : B.pair
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v) = 0 :=
    hcontraEv
  obtain ⟨z, hz⟩ := exists_ne (0 : K)
  have hpos := B.positive
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hEvMem hEv z hz
  rw [hpairZero, zero_apply, inner_zero_right] at hpos
  exact lt_irrefl 0 hpos

/-- **Infinite positive operator-channel D1 no-go.** Neither canonical side for a bounded
operator-valued contravariant coefficient admits a strictly positive carrier containing actual D1,
on any nontrivial complete complex Hilbert channel. -/
theorem modularThetaSourcePositive_no_D1_infiniteOperatorContravariantCarrier :
    (¬ Nonempty
      (ModularThetaSourcePositiveD1RightOperatorContravariantCarrier (K := K))) ∧
    (¬ Nonempty
      (ModularThetaSourcePositiveD1LeftOperatorContravariantCarrier (K := K))) :=
  ⟨modularThetaSourcePositive_no_D1_rightOperatorContravariantCarrier,
    modularThetaSourcePositive_no_D1_leftOperatorContravariantCarrier⟩

end D1Carrier

end


end HTGeometry
