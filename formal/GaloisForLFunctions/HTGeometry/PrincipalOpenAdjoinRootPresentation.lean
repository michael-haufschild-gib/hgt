import GaloisForLFunctions.HTGeometry.PrincipalOpenPowerBasisNumerator

/-!
# Principal-open adjoin-root presentations

A bijective localized power-coordinate map gives a power basis on the ordinary tensor scalar
extension.  Every power basis has a canonical presentation by the root algebra of its monic
minimal polynomial.  Together these facts upgrade module-level principal-open spreading to the
algebra equivalence consumed by finite-cover charts.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing
open scoped TensorProduct

/-- A bijective localized power-coordinate map gives a power basis on ordinary scalar extension
to the same localization. -/
noncomputable def localizedPowerBasisOfBijective
    (R : Type*) [CommRing R]
    (B : Type*) [CommRing B] [Algebra R B]
    (S : Submonoid R) (theta : B) (d : Nat)
    (hbij : Function.Bijective
      (LocalizedModule.map S (powerCombination (R := R) theta d))) :
    PowerBasis (Localization S) (TensorProduct R (Localization S) B) := by
  let f := powerCombination (R := R) theta d
  have hbase : Function.Bijective (f.baseChange (Localization S)) :=
    ABHN.baseChange_bijective_of_localized_bijective
      R S (Localization S) (Fin d →₀ R) B f hbij
  let e : TensorProduct R (Localization S) (Fin d →₀ R) ≃ₗ[Localization S]
      TensorProduct R (Localization S) B :=
    LinearEquiv.ofBijective (f.baseChange (Localization S)) hbase
  let sourceBasis : Module.Basis (Fin d) (Localization S)
      (TensorProduct R (Localization S) (Fin d →₀ R)) :=
    (Finsupp.basisSingleOne (R := R) (ι := Fin d)).baseChange (Localization S)
  let b := sourceBasis.map e
  let gen : TensorProduct R (Localization S) B :=
    Algebra.TensorProduct.includeRight theta
  apply PowerBasis.mk gen d b
  intro i
  rw [show b i = e (sourceBasis i) from Module.Basis.map_apply _ _ _]
  change f.baseChange (Localization S) (sourceBasis i) = gen ^ (i : Nat)
  dsimp only [sourceBasis]
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
  change (1 : Localization S) ⊗ₜ[R]
      powerCombination (R := R) theta d (Finsupp.single i 1) = gen ^ (i : Nat)
  rw [powerCombination_basisSingleOne]
  change Algebra.TensorProduct.includeRight (R := R) (A := Localization S) (B := B)
      (theta ^ (i : Nat)) = gen ^ (i : Nat)
  exact map_pow
    (Algebra.TensorProduct.includeRight (R := R) (A := Localization S) (B := B))
    theta (i : Nat)

/-- Every power basis is canonically the root algebra of its monic minimal polynomial. -/
noncomputable def powerBasisAdjoinRootEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) : AdjoinRoot pb.minpolyGen ≃ₐ[R] S := by
  have hgen : Polynomial.eval₂ (algebraMap R S) pb.gen pb.minpolyGen = 0 := by
    simpa only [Polynomial.aeval_def] using pb.aeval_minpolyGen
  let f : AdjoinRoot pb.minpolyGen →ₐ[R] S :=
    { toRingHom := AdjoinRoot.lift (algebraMap R S) pb.gen hgen
      commutes' := fun r => by simp }
  have hroot : Polynomial.aeval (AdjoinRoot.root pb.minpolyGen)
      (minpoly R pb.gen) = 0 := by
    rw [← pb.minpolyGen_eq]
    change Polynomial.eval₂ (AdjoinRoot.of pb.minpolyGen)
      (AdjoinRoot.root pb.minpolyGen) pb.minpolyGen = 0
    simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.IsRoot] using
      AdjoinRoot.isRoot_root pb.minpolyGen
  let g : S →ₐ[R] AdjoinRoot pb.minpolyGen :=
    pb.lift (AdjoinRoot.root pb.minpolyGen) hroot
  apply AlgEquiv.ofAlgHom f g
  · apply pb.algHom_ext
    change f (g pb.gen) = pb.gen
    rw [show g pb.gen = AdjoinRoot.root pb.minpolyGen from pb.lift_gen _ hroot]
    exact AdjoinRoot.lift_root hgen
  · apply AdjoinRoot.algHom_ext
    change g (f (AdjoinRoot.root pb.minpolyGen)) = AdjoinRoot.root pb.minpolyGen
    rw [show f (AdjoinRoot.root pb.minpolyGen) = pb.gen from AdjoinRoot.lift_root hgen]
    exact pb.lift_gen _ hroot

@[simp]
theorem powerBasisAdjoinRootEquiv_root
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) :
    powerBasisAdjoinRootEquiv pb (AdjoinRoot.root pb.minpolyGen) = pb.gen := by
  simp [powerBasisAdjoinRootEquiv]

/-- A bijective principal-open power-coordinate map produces an exact monic `AdjoinRoot`
presentation of the scalar-extended algebra. -/
theorem exists_adjoinRoot_equiv_of_localized_powerCombination_bijective
    (R : Type*) [CommRing R]
    (B : Type*) [CommRing B] [Algebra R B]
    (S : Submonoid R) (theta : B) (d : Nat)
    (hbij : Function.Bijective
      (LocalizedModule.map S (powerCombination (R := R) theta d))) :
    ∃ q : Polynomial (Localization S), q.Monic ∧
      ∃ e : AdjoinRoot q ≃ₐ[Localization S] TensorProduct R (Localization S) B,
        e (AdjoinRoot.root q) =
          Algebra.TensorProduct.includeRight (R := R) (A := Localization S) (B := B) theta := by
  let pb := localizedPowerBasisOfBijective R B S theta d hbij
  refine ⟨pb.minpolyGen, pb.minpolyGen_monic, powerBasisAdjoinRootEquiv pb, ?_⟩
  rw [powerBasisAdjoinRootEquiv_root]
  rfl

/-- A principal-open power-basis witness packages into an exact monic `AdjoinRoot` presentation. -/
theorem exists_principalOpen_adjoinRoot_equiv_of_global_numerator_powerBasis
    (R : Type*) [CommRing R]
    (B : Type*) [CommRing B] [Algebra R B]
    (p : Ideal R) (d : Nat)
    (h : ∃ theta : B, ∃ g ∉ p, Function.Bijective
      (LocalizedModule.map (Submonoid.powers g)
        (powerCombination (R := R) theta d))) :
    ∃ theta : B, ∃ g ∉ p, ∃ q : Polynomial (Localization (Submonoid.powers g)),
      q.Monic ∧
        ∃ e : AdjoinRoot q ≃ₐ[Localization (Submonoid.powers g)]
            TensorProduct R (Localization (Submonoid.powers g)) B,
          e (AdjoinRoot.root q) = Algebra.TensorProduct.includeRight
            (R := R) (A := Localization (Submonoid.powers g)) (B := B) theta := by
  obtain ⟨theta, g, hg, hbij⟩ := h
  obtain ⟨q, hq, he⟩ :=
    exists_adjoinRoot_equiv_of_localized_powerCombination_bijective
      R B (Submonoid.powers g) theta d hbij
  exact ⟨theta, g, hg, q, hq, he⟩

/-- A split closed fibre of a local normalization spreads to an exact monic `AdjoinRoot`
presentation on one principal-open neighbourhood. -/
theorem exists_principalOpen_adjoinRoot_equiv_of_split_residue_fibre
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [IsDomain N] [Algebra R N] [Algebra T N]
    [IsScalarTower R T N] [NoZeroSMulDivisors T N] [Module.Finite T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    [CharZero (IsLocalRing.ResidueField T)]
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((N ⧸ maxExt T N) ≃ₐ[IsLocalRing.ResidueField T]
      (ι → IsLocalRing.ResidueField T))) :
    ∃ theta : B, ∃ g ∉ p, ∃ q : Polynomial (Localization (Submonoid.powers g)),
      q.Monic ∧
        ∃ e : AdjoinRoot q ≃ₐ[Localization (Submonoid.powers g)]
            TensorProduct R (Localization (Submonoid.powers g)) B,
          e (AdjoinRoot.root q) = Algebra.TensorProduct.includeRight
            (R := R) (A := Localization (Submonoid.powers g)) (B := B) theta :=
  exists_principalOpen_adjoinRoot_equiv_of_global_numerator_powerBasis R B p
    (Module.finrank T N)
    (exists_global_numerator_powerBasis_of_split_residue_fibre R B p T N fN hsplit)

/-- A nondegenerate closed-fibre trace form spreads to an exact monic `AdjoinRoot` presentation on
one principal-open neighbourhood. -/
theorem exists_principalOpen_adjoinRoot_equiv_of_residue_traceForm_nondegenerate
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [IsDomain N] [Algebra R N] [Algebra T N]
    [IsScalarTower R T N] [NoZeroSMulDivisors T N] [Module.Finite T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    [CharZero (IsLocalRing.ResidueField T)] [IsAlgClosed (IsLocalRing.ResidueField T)]
    (h : (Algebra.traceForm (IsLocalRing.ResidueField T)
      (N ⧸ maxExt T N)).Nondegenerate) :
    ∃ theta : B, ∃ g ∉ p, ∃ q : Polynomial (Localization (Submonoid.powers g)),
      q.Monic ∧
        ∃ e : AdjoinRoot q ≃ₐ[Localization (Submonoid.powers g)]
            TensorProduct R (Localization (Submonoid.powers g)) B,
          e (AdjoinRoot.root q) = Algebra.TensorProduct.includeRight
            (R := R) (A := Localization (Submonoid.powers g)) (B := B) theta :=
  exists_principalOpen_adjoinRoot_equiv_of_global_numerator_powerBasis R B p
    (Module.finrank T N)
    (exists_global_numerator_powerBasis_of_residue_traceForm_nondegenerate R B p T N fN h)

end GaloisForLFunctions.HTGeometry
