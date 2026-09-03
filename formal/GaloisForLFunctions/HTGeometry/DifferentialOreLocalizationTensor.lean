import GaloisForLFunctions.HTGeometry.DifferentialVariationalRank

/-!
# Noncommutative Ore-localization tensor carrier

For a left differential-operator module `M`, this file constructs the literal balanced scalar
extension `PseudoDiffOp K ⊗_{DiffOp K} M`.  Because the base operator ring is noncommutative,
mathlib's commutative tensor product is not applicable.  The carrier is therefore the quotient of
the free left pseudodifferential module on `M` by additivity and Ore-balance relations.

Every finite operator basis identifies this intrinsic quotient with the corresponding finite
pseudodifferential coordinate space.  Specializing to the torsion-free variational Kähler module
closes the middle scalar-extension equality in the differential variational rank formula.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential BigOperators

noncomputable section

namespace DiffOp

variable {K : Type u} [Field K] [Differential K]
variable {M : Type v} [AddCommGroup M] [Module (DiffOp K) M]

abbrev OreTensorFree (K : Type u) [Field K] [Differential K]
    (M : Type v) := M →₀ PseudoDiffOp K

def oreTensorRelationSet : Set (OreTensorFree K M) :=
  {z | (∃ x y : M,
      z = Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1) ∨
    z = Finsupp.single (0 : M) 1 ∨
    (∃ a : DiffOp K, ∃ x : M,
      z = Finsupp.single (a • x) 1 -
        Finsupp.single x (OreLocalization.numeratorRingHom a))}

def oreTensorRelationSubmodule : Submodule (PseudoDiffOp K) (OreTensorFree K M) :=
  Submodule.span (PseudoDiffOp K) (oreTensorRelationSet (K := K) (M := M))

abbrev OreTensor (K : Type u) [Field K] [Differential K]
    (M : Type v) [AddCommGroup M] [Module (DiffOp K) M] :=
  OreTensorFree K M ⧸ oreTensorRelationSubmodule (K := K) (M := M)

def oreTensorPure (x : M) : OreTensor K M :=
  (oreTensorRelationSubmodule (K := K) (M := M)).mkQ (Finsupp.single x 1)

theorem oreTensorPure_zero : oreTensorPure (K := K) (0 : M) = 0 := by
  rw [← map_zero (oreTensorRelationSubmodule (K := K) (M := M)).mkQ]
  apply (Submodule.Quotient.eq _).2
  simp only [sub_zero]
  exact Submodule.subset_span (Or.inr (Or.inl rfl))

theorem oreTensorPure_add (x y : M) :
    oreTensorPure (K := K) (x + y) = oreTensorPure x + oreTensorPure y := by
  unfold oreTensorPure
  rw [← (oreTensorRelationSubmodule (K := K) (M := M)).mkQ.map_add]
  apply (Submodule.Quotient.eq _).2
  apply Submodule.subset_span
  refine Or.inl ⟨x, y, ?_⟩
  abel

def oreTensorPureAddHom : M →+ OreTensor K M where
  toFun := oreTensorPure
  map_zero' := oreTensorPure_zero
  map_add' := oreTensorPure_add

theorem oreTensorPure_smul (a : DiffOp K) (x : M) :
    oreTensorPure (K := K) (a • x) =
      (OreLocalization.numeratorRingHom a : PseudoDiffOp K) • oreTensorPure x := by
  change (oreTensorRelationSubmodule (K := K) (M := M)).mkQ
      (Finsupp.single (a • x) 1) =
    (OreLocalization.numeratorRingHom a : PseudoDiffOp K) •
      (oreTensorRelationSubmodule (K := K) (M := M)).mkQ (Finsupp.single x 1)
  rw [← LinearMap.map_smul]
  apply (Submodule.Quotient.eq _).2
  have hsingle : (OreLocalization.numeratorRingHom a : PseudoDiffOp K) •
      Finsupp.single x (1 : PseudoDiffOp K) =
      Finsupp.single x (OreLocalization.numeratorRingHom a) := by
    ext y
    by_cases hy : y = x
    · subst y
      simp
    · simp [hy]
  rw [hsingle]
  exact Submodule.subset_span (Or.inr (Or.inr ⟨a, x, rfl⟩))

def oreTensorCoordinateMap {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) :
    OreTensorFree K M →ₗ[PseudoDiffOp K] (Fin r → PseudoDiffOp K) :=
  Finsupp.linearCombination (PseudoDiffOp K) (fun x i =>
    OreLocalization.numeratorRingHom (b.repr x i))

theorem oreTensorRelationSubmodule_le_coordinateMap_ker {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) :
    oreTensorRelationSubmodule (K := K) (M := M) ≤ (oreTensorCoordinateMap b).ker := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨x, y, rfl⟩ | rfl | ⟨a, x, rfl⟩
  · change oreTensorCoordinateMap b
      (Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1) = 0
    funext i
    simp only [oreTensorCoordinateMap, map_sub, Finsupp.linearCombination_single,
      one_smul, Pi.sub_apply, Pi.zero_apply]
    have hrepr := congrArg (fun w : Fin r →₀ DiffOp K => w i) (b.repr.map_add x y)
    rw [hrepr, Finsupp.add_apply]
    rw [(OreLocalization.numeratorRingHom : DiffOp K →+* PseudoDiffOp K).map_add]
    abel
  · change oreTensorCoordinateMap b (Finsupp.single (0 : M) 1) = 0
    funext i
    simp [oreTensorCoordinateMap]
  · change oreTensorCoordinateMap b
      (Finsupp.single (a • x) 1 -
        Finsupp.single x (OreLocalization.numeratorRingHom a)) = 0
    funext i
    simp only [oreTensorCoordinateMap, map_sub, Finsupp.linearCombination_single,
      one_smul, Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    have hrepr := congrArg (fun w : Fin r →₀ DiffOp K => w i) (b.repr.map_smul a x)
    rw [hrepr, Finsupp.smul_apply, smul_eq_mul]
    rw [(OreLocalization.numeratorRingHom : DiffOp K →+* PseudoDiffOp K).map_mul]
    abel

def oreTensorToCoordinates {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) :
    OreTensor K M →ₗ[PseudoDiffOp K] (Fin r → PseudoDiffOp K) :=
  (oreTensorRelationSubmodule (K := K) (M := M)).liftQ
    (oreTensorCoordinateMap b)
    (oreTensorRelationSubmodule_le_coordinateMap_ker b)

def oreTensorFromCoordinates {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) :
    (Fin r → PseudoDiffOp K) →ₗ[PseudoDiffOp K] OreTensor K M :=
  Fintype.linearCombination (PseudoDiffOp K) (fun i => oreTensorPure (K := K) (b i))

theorem oreTensorPure_eq_sum_basis {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) (x : M) :
    oreTensorPure (K := K) x = ∑ i,
      (OreLocalization.numeratorRingHom (b.repr x i) : PseudoDiffOp K) •
        oreTensorPure (K := K) (b i) := by
  calc
    oreTensorPure (K := K) x =
        oreTensorPure (K := K) (∑ i, (b.repr x i) • b i) := by
          rw [b.sum_repr]
    _ = ∑ i, oreTensorPure (K := K) ((b.repr x i) • b i) := by
          exact map_sum (oreTensorPureAddHom (K := K) (M := M)) _ Finset.univ
    _ = ∑ i,
        (OreLocalization.numeratorRingHom (b.repr x i) : PseudoDiffOp K) •
          oreTensorPure (K := K) (b i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact oreTensorPure_smul (b.repr x i) (b i)

theorem oreTensorToCoordinates_pure {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) (x : M) :
    oreTensorToCoordinates b (oreTensorPure (K := K) x) =
      fun i => OreLocalization.numeratorRingHom (b.repr x i) := by
  change ((oreTensorRelationSubmodule (K := K) (M := M)).liftQ
      (oreTensorCoordinateMap b) _)
      (Submodule.Quotient.mk (Finsupp.single x 1)) = _
  rw [Submodule.liftQ_apply, oreTensorCoordinateMap,
    Finsupp.linearCombination_single]
  simp

theorem oreTensorToCoordinates_fromCoordinates {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M)
    (v : Fin r → PseudoDiffOp K) :
    oreTensorToCoordinates b (oreTensorFromCoordinates b v) = v := by
  rw [oreTensorFromCoordinates, Fintype.linearCombination_apply, map_sum]
  -- scalar and pure-tensor maps are expanded coordinatewise below
  funext j
  simp only [Finset.sum_apply]
  classical
  rw [Finset.sum_eq_single j]
  · rw [(oreTensorToCoordinates b).map_smul, oreTensorToCoordinates_pure]
    rw [Pi.smul_apply, smul_eq_mul]
    rw [b.repr_self]
    rw [Finsupp.single_eq_same, map_one, mul_one]
  · intro i _ hij
    rw [(oreTensorToCoordinates b).map_smul, oreTensorToCoordinates_pure]
    simp [hij]
  · simp

theorem oreTensorFromCoordinates_toCoordinates {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M)
    (x : OreTensor K M) :
    oreTensorFromCoordinates b (oreTensorToCoordinates b x) = x := by
  obtain ⟨z, rfl⟩ :=
    (oreTensorRelationSubmodule (K := K) (M := M)).mkQ_surjective x
  suffices hmaps :
      (oreTensorFromCoordinates b).comp
          ((oreTensorToCoordinates b).comp
            (oreTensorRelationSubmodule (K := K) (M := M)).mkQ) =
        (oreTensorRelationSubmodule (K := K) (M := M)).mkQ by
    exact LinearMap.congr_fun hmaps z
  apply Finsupp.lhom_ext
  intro m q
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change oreTensorFromCoordinates b
      (((oreTensorRelationSubmodule (K := K) (M := M)).liftQ
        (oreTensorCoordinateMap b) _)
        (Submodule.Quotient.mk (Finsupp.single m q))) = _
  rw [Submodule.liftQ_apply]
  rw [oreTensorCoordinateMap, Finsupp.linearCombination_single]
  change oreTensorFromCoordinates b
      (q • fun i => OreLocalization.numeratorRingHom (b.repr m i)) =
    (oreTensorRelationSubmodule (K := K) (M := M)).mkQ (Finsupp.single m q)
  rw [(oreTensorFromCoordinates b).map_smul]
  change q • (∑ i,
      (OreLocalization.numeratorRingHom (b.repr m i) : PseudoDiffOp K) •
        oreTensorPure (K := K) (b i)) = _
  rw [← oreTensorPure_eq_sum_basis b m]
  change q • (oreTensorRelationSubmodule (K := K) (M := M)).mkQ
      (Finsupp.single m 1) = _
  rw [← LinearMap.map_smul]
  congr 1
  ext y
  by_cases hy : y = m
  · subst y
    simp
  · simp [hy]

def oreTensorCoordinatesEquiv {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) :
    OreTensor K M ≃ₗ[PseudoDiffOp K] (Fin r → PseudoDiffOp K) where
  toLinearMap := oreTensorToCoordinates b
  invFun := oreTensorFromCoordinates b
  left_inv := oreTensorFromCoordinates_toCoordinates b
  right_inv := oreTensorToCoordinates_fromCoordinates b

theorem oreTensor_finrank_eq {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) M) :
    Module.finrank (PseudoDiffOp K) (OreTensor K M) =
      Module.finrank (DiffOp K) M := by
  calc
    Module.finrank (PseudoDiffOp K) (OreTensor K M) =
        Module.finrank (PseudoDiffOp K) (Fin r → PseudoDiffOp K) :=
      (oreTensorCoordinatesEquiv b).finrank_eq
    _ = r := Module.finrank_fin_fun (PseudoDiffOp K)
    _ = Module.finrank (DiffOp K) M :=
      by simpa using (Module.finrank_eq_card_basis b).symm

abbrev DifferentialVariationalRationalCarrier
    (C K : Type u) [Field C] [Field K] [Algebra C K]
    [Differential K] [IsConstantBase C K] :=
  OreTensor K (VariationalOreModule C K)

theorem differentialVariationalRationalCarrier_rank_eq_differentialTranscendenceDegree
    {C K : Type u} [Field C] [Field K] [Algebra C K] [Differential K]
    [IsConstantBase C K] [CharZero C] {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤) :
    Module.rank (PseudoDiffOp K) (DifferentialVariationalRationalCarrier C K) =
      constantBaseDifferentialTranscendenceDegree C K := by
  obtain ⟨r, ⟨b⟩⟩ := exists_fin_basis_variationalOreModule hy
  letI : Module.Finite (DiffOp K) (VariationalOreModule C K) :=
    variationalOreModule_finite hy
  letI : Module.Finite (PseudoDiffOp K)
      (DifferentialVariationalRationalCarrier C K) :=
    Module.Finite.equiv (oreTensorCoordinatesEquiv b).symm
  calc
    Module.rank (PseudoDiffOp K) (DifferentialVariationalRationalCarrier C K) =
        (Module.finrank (PseudoDiffOp K)
          (DifferentialVariationalRationalCarrier C K) : Cardinal) :=
      (Module.finrank_eq_rank (PseudoDiffOp K)
        (DifferentialVariationalRationalCarrier C K)).symm
    _ = (Module.finrank (DiffOp K) (VariationalOreModule C K) : Cardinal) := by
      rw [oreTensor_finrank_eq b]
    _ = Module.rank (DiffOp K) (VariationalOreModule C K) :=
      Module.finrank_eq_rank (DiffOp K) (VariationalOreModule C K)
    _ = constantBaseDifferentialTranscendenceDegree C K :=
      variationalOreModule_rank_eq_differentialTranscendenceDegree hy

end DiffOp

end

end GaloisForLFunctions.HTGeometry
