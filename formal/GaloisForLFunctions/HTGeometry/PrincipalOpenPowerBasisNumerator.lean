import GaloisForLFunctions.HTGeometry.PrincipalOpenPowerBasis
import GaloisForLFunctions.HTGeometry.SplitResidueAdjoinRootPresentation

/-!
# Clearing a localized power-basis generator

A generator in a localization need not be the image of a global element.  Clearing one denominator
produces a global numerator.  Its powers differ from the original power basis by invertible
diagonal scalars, so they are again a basis.  Finite presentation then spreads this numerator basis
to one principal open in the base.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing

/-- Coordinatewise multiplication by successive powers of a unit. -/
noncomputable def unitPowPiLinearEquiv
    {R : Type*} [CommRing R] (u : Rˣ) (d : Nat) :
    (Fin d → R) ≃ₗ[R] (Fin d → R) where
  toFun x i := (u ^ (i : Nat) : R) * x i
  invFun x i := (↑((u ^ (i : Nat))⁻¹) : R) * x i
  left_inv x := by
    ext i
    change (↑((u ^ (i : Nat))⁻¹) : R) * ((↑(u ^ (i : Nat)) : R) * x i) = x i
    rw [← mul_assoc, ← Units.val_mul]
    simp
  right_inv x := by
    ext i
    change (↑(u ^ (i : Nat)) : R) * ((↑((u ^ (i : Nat))⁻¹) : R) * x i) = x i
    rw [← mul_assoc, ← Units.val_mul]
    simp
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' r x := by
    ext i
    simp [mul_assoc, mul_comm]

/-- A basis remains a basis after scaling its `i`-th vector by the `i`-th power of a unit. -/
noncomputable def unitPowScaledBasis
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {d : Nat} (b : Module.Basis (Fin d) R M) (u : Rˣ) : Module.Basis (Fin d) R M :=
  b.map (b.equivFun.trans ((unitPowPiLinearEquiv u d).trans b.equivFun.symm))

@[simp]
theorem unitPowScaledBasis_apply
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {d : Nat} (b : Module.Basis (Fin d) R M) (u : Rˣ) (i : Fin d) :
    unitPowScaledBasis b u i = (u ^ (i : Nat) : R) • b i := by
  classical
  rw [unitPowScaledBasis, Module.Basis.map_apply]
  apply b.equivFun.injective
  ext j
  simp [unitPowPiLinearEquiv, Module.Basis.equivFun_apply, Finsupp.single_apply]

/-- A localized power basis has a global numerator whose powers form a basis on a principal open. -/
theorem exists_global_numerator_powerBasis
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [Algebra R N] [Algebra T N] [IsScalarTower R T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    (pb : PowerBasis T N) :
    ∃ theta : B, ∃ g ∉ p, Function.Bijective
      (LocalizedModule.map (Submonoid.powers g)
        (powerCombination (R := R) theta pb.dim)) := by
  obtain ⟨⟨theta, s⟩, hs⟩ := IsLocalizedModule.surj p.primeCompl fN.toLinearMap pb.gen
  let hu : IsUnit (algebraMap R T s.1) := IsLocalization.map_units T s
  let u : Tˣ := hu.unit
  let b : Module.Basis (Fin pb.dim) T N := unitPowScaledBasis pb.basis u
  have hb (i : Fin pb.dim) : b i = fN.toLinearMap (theta ^ (i : Nat)) := by
    dsimp only [b]
    rw [unitPowScaledBasis_apply, pb.basis_eq_pow, Algebra.smul_def]
    change (algebraMap T N (u ^ (i : Nat) : T)) * pb.gen ^ (i : Nat) =
      fN (theta ^ (i : Nat))
    have htheta : fN theta = algebraMap T N (u : T) * pb.gen := by
      rw [hu.unit_spec, ← IsScalarTower.algebraMap_apply R T N, ← Algebra.smul_def]
      exact hs.symm
    rw [map_pow fN, htheta, mul_pow, map_pow]
  exact ⟨theta, exists_notMem_powerCombination_bijective_of_localized_basis
    R B p T N fN.toLinearMap theta pb.dim b hb⟩

/-- A monic `AdjoinRoot` presentation in the localization spreads to a global numerator power basis
on one principal open. -/
theorem exists_global_numerator_powerBasis_of_adjoinRoot_equiv
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [Algebra R N] [Algebra T N] [IsScalarTower R T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    {q : Polynomial T} (hq : q.Monic) (e : AdjoinRoot q ≃ₐ[T] N) :
    ∃ theta : B, ∃ g ∉ p, Function.Bijective
      (LocalizedModule.map (Submonoid.powers g)
        (powerCombination (R := R) theta q.natDegree)) := by
  let pb := (AdjoinRoot.powerBasis' hq).map e
  have hdim : pb.dim = q.natDegree :=
    (PowerBasis.map_dim (AdjoinRoot.powerBasis' hq) e).trans
      (AdjoinRoot.powerBasis'_dim hq)
  obtain ⟨theta, g, hg, hbij⟩ := exists_global_numerator_powerBasis R B p T N fN pb
  refine ⟨theta, g, hg, ?_⟩
  rw [← hdim]
  exact hbij

/-- A split closed fibre of the localized algebra produces a global numerator power basis on one
principal-open neighbourhood of the prime. -/
theorem exists_global_numerator_powerBasis_of_split_residue_fibre
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [IsDomain N] [Algebra R N] [Algebra T N]
    [IsScalarTower R T N] [NoZeroSMulDivisors T N] [Module.Finite T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    [CharZero (ResidueField T)]
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((N ⧸ maxExt T N) ≃ₐ[ResidueField T] (ι → ResidueField T))) :
    ∃ theta : B, ∃ g ∉ p, Function.Bijective
      (LocalizedModule.map (Submonoid.powers g)
        (powerCombination (R := R) theta (Module.finrank T N))) := by
  obtain ⟨x, hx, ⟨e⟩⟩ := exists_adjoinRoot_equiv_of_split_residue_fibre hsplit
  have hdim : (minpoly T x).natDegree = Module.finrank T N := by
    let pb := (AdjoinRoot.powerBasis' (minpoly.monic hx)).map e
    have hpbdeg : pb.dim = (minpoly T x).natDegree :=
      (PowerBasis.map_dim (AdjoinRoot.powerBasis' (minpoly.monic hx)) e).trans
        (AdjoinRoot.powerBasis'_dim (minpoly.monic hx))
    have hfin : Module.finrank T N = pb.dim := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis pb.basis
    exact hpbdeg.symm.trans hfin.symm
  obtain ⟨theta, g, hg, hbij⟩ :=
    exists_global_numerator_powerBasis_of_adjoinRoot_equiv R B p T N fN (minpoly.monic hx) e
  refine ⟨theta, g, hg, ?_⟩
  rw [← hdim]
  exact hbij

/-- A nondegenerate closed-fibre trace form produces a global numerator power basis on one
principal-open neighbourhood of the prime. -/
theorem exists_global_numerator_powerBasis_of_residue_traceForm_nondegenerate
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [IsDomain N] [Algebra R N] [Algebra T N]
    [IsScalarTower R T N] [NoZeroSMulDivisors T N] [Module.Finite T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    [CharZero (ResidueField T)] [IsAlgClosed (ResidueField T)]
    (h : (Algebra.traceForm (ResidueField T) (N ⧸ maxExt T N)).Nondegenerate) :
    ∃ theta : B, ∃ g ∉ p, Function.Bijective
      (LocalizedModule.map (Submonoid.powers g)
        (powerCombination (R := R) theta (Module.finrank T N))) := by
  obtain ⟨x, hx, ⟨e⟩⟩ := exists_adjoinRoot_equiv_of_residue_traceForm_nondegenerate h
  have hdim : (minpoly T x).natDegree = Module.finrank T N := by
    let pb := (AdjoinRoot.powerBasis' (minpoly.monic hx)).map e
    have hpbdeg : pb.dim = (minpoly T x).natDegree :=
      (PowerBasis.map_dim (AdjoinRoot.powerBasis' (minpoly.monic hx)) e).trans
        (AdjoinRoot.powerBasis'_dim (minpoly.monic hx))
    have hfin : Module.finrank T N = pb.dim := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis pb.basis
    exact hpbdeg.symm.trans hfin.symm
  obtain ⟨theta, g, hg, hbij⟩ :=
    exists_global_numerator_powerBasis_of_adjoinRoot_equiv R B p T N fN (minpoly.monic hx) e
  refine ⟨theta, g, hg, ?_⟩
  rw [← hdim]
  exact hbij

end GaloisForLFunctions.HTGeometry
