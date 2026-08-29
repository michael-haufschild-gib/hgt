import GaloisForLFunctions.HTGeometry.RiccatiCoordinateExtension
import GaloisForLFunctions.HTGeometry.MahlerTraceCard
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinFiniteTrdeg
import GaloisForLFunctions.HTGeometry.ScaledDerivationTransfer
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# The Boltzmann coordinate of an ultrametric detector

De Sitter detailed balance evaluates the ultrametric thermal trace at the Boltzmann coordinate
`w = exp(-a/H)`.  Formally this is the adjunction of a coordinate `H` to the ambient differential
field with the Riccati relation `θH = H²/a`, which is exactly the derivative of `-a/log w` for the
Euler derivation.  The trace germ is one and the same element of the extended field, read in the
two coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc Differential

noncomputable section

variable {k : Type u_1} [Field k]

/-- The ambient field with the Boltzmann coordinate adjoined. -/
abbrev BoltzmannField (k : Type*) [Field k] := RatFunc (MahlerAmbient k)

/-- The Boltzmann coordinate `H = -a/log w`. -/
def boltzmannCoord (k : Type*) [Field k] : BoltzmannField k := RatFunc.X

/-- The prescribed derivative `H²/a` of the Boltzmann coordinate. -/
def boltzmannRate (a : k) : BoltzmannField k :=
  (boltzmannCoord k) ^ 2 * algebraMap (MahlerAmbient k) (BoltzmannField k)
    (algebraMap k (MahlerAmbient k) a⁻¹)

/-- The Euler differential structure of the extended field. -/
@[reducible] def boltzmannEuler [CharZero k] (a : k) : Differential (BoltzmannField k) := by
  letI := mahlerDifferential (k := k)
  exact riccatiDifferential (boltzmannRate a)

theorem boltzmannEuler_deriv_coord [CharZero k] (a : k) :
    (boltzmannEuler a).deriv (boltzmannCoord k) = boltzmannRate a := by
  letI := mahlerDifferential (k := k)
  exact riccatiDerivation_X (boltzmannRate a)

theorem boltzmannEuler_deriv_algebraMap [CharZero k] (a : k) (c : MahlerAmbient k) :
    (boltzmannEuler a).deriv (algebraMap (MahlerAmbient k) (BoltzmannField k) c)
      = algebraMap (MahlerAmbient k) (BoltzmannField k) (mahlerAmbientDeriv c) := by
  letI := mahlerDifferential (k := k)
  exact riccatiDerivation_algebraMap_const (boltzmannRate a) c

/-! ## The two coordinate embeddings -/

/-- The `w`-coordinate embedding of `k(w)` into the ambient field. -/
def kwToAmbient : RatFunc k →+* MahlerAmbient k :=
  (HahnSeries.C : HahnSeries ℚ k →+* MahlerAmbient k).comp ratFuncToHahn

theorem kwToAmbient_eq [CharZero k] (p : ℕ) (hp : 1 < p) (r : RatFunc k) :
    letI := perfectAlgebra (k := k) p hp
    letI := kwAmbientAlgebra (k := k) p hp
    algebraMap (RatFunc k) (MahlerAmbient k) r = kwToAmbient r := by
  letI := perfectAlgebra (k := k) p hp
  letI := kwAmbientAlgebra (k := k) p hp
  show mahlerPEmbed k p hp (algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp)
      (kwToPerfect p hp r)) = _
  rw [mahlerPEmbed_algebraMap_perfect]
  rfl

theorem mahlerAmbientDeriv_C [CharZero k] (x : HahnSeries ℚ k) :
    mahlerAmbientDeriv (HahnSeries.C x : MahlerAmbient k) = HahnSeries.C (hahnQEuler x) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerAmbientDeriv, coeff_C_hahn, coeff_C_hahn]
  by_cases h : n = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

/-- The `H`-coordinate embedding of `k(H)` into the extended field. -/
def kHToBoltzmann [CharZero k] : RatFunc k →+* BoltzmannField k :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k (MahlerAmbient k)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap k (MahlerAmbient k)).injective))

theorem kHToBoltzmann_X [CharZero k] :
    kHToBoltzmann (RatFunc.X : RatFunc k) = boltzmannCoord k := by
  have hX : (RatFunc.X : RatFunc k)
      = algebraMap (Polynomial k) (RatFunc k) Polynomial.X := (RatFunc.algebraMap_X).symm
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom (algebraMap k (MahlerAmbient k)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap k (MahlerAmbient k)).injective))
    (Polynomial.X : Polynomial k) 1
  simp only [map_one, div_one] at h
  rw [kHToBoltzmann, hX]
  show RatFunc.map (Polynomial.mapRingHom (algebraMap k (MahlerAmbient k)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap k (MahlerAmbient k)).injective))
    (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) = _
  rw [h, boltzmannCoord]
  simp

/-! ## The trace germ in the extended field -/

/-- The detailed-balance trace: the ultrametric thermal germ read in the extended field. -/
def deSitterTrace [CharZero k] (p : ℕ) (hp : 1 < p) : BoltzmannField k :=
  algebraMap (MahlerAmbient k) (BoltzmannField k) (HahnSeries.C (traceSeries p hp))

/-- The `w`-side algebra structure of the extended field. -/
@[reducible] def wBoltzmannAlgebra [CharZero k] : Algebra (RatFunc k) (BoltzmannField k) :=
  ((algebraMap (MahlerAmbient k) (BoltzmannField k)).comp kwToAmbient).toAlgebra

attribute [local instance] wBoltzmannAlgebra

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The trace germ stays hypertranscendental in the extended field**, over the Boltzmann
coordinate's own base `k(w)`. -/
theorem hypertranscendentalOver_deSitterTrace_w [CharZero k] {p : ℕ} (hp : 1 < p) (a : k) :
    letI := cylinderDifferential (1 : k)
    letI := boltzmannEuler (k := k) a
    HypertranscendentalOver (RatFunc k) (deSitterTrace (k := k) p hp) := by
  letI := perfectAlgebra (k := k) p hp
  letI := kwAmbientAlgebra (k := k) p hp
  letI := cylinderDifferential (1 : k)
  letI := mahlerDifferential (k := k)
  letI := boltzmannEuler (k := k) a
  haveI : DifferentialAlgebra (MahlerAmbient k) (BoltzmannField k) :=
    ⟨fun c => boltzmannEuler_deriv_algebraMap a c⟩
  let F : MahlerAmbient k →ₐ[RatFunc k] BoltzmannField k :=
    { algebraMap (MahlerAmbient k) (BoltzmannField k) with
      commutes' := fun r => by
        show algebraMap (MahlerAmbient k) (BoltzmannField k)
            (algebraMap (RatFunc k) (MahlerAmbient k) r)
          = algebraMap (RatFunc k) (BoltzmannField k) r
        rw [kwToAmbient_eq p hp]
        rfl }
  have hFinj : Function.Injective F :=
    (algebraMap (MahlerAmbient k) (BoltzmannField k)).injective
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hbase := hypertranscendentalOver_traceSeries_kw (k := k) p hp
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at hbase
  have hind := hbase.map' (f := F) hFinj
  have heq : (F ∘ fun q : Unit × ℕ =>
        differentialJet q.2 ((fun _ : Unit => HahnSeries.C (traceSeries (k := k) p hp)) q.1))
      = fun q : Unit × ℕ =>
        differentialJet q.2 ((fun _ : Unit => deSitterTrace (k := k) p hp) q.1) := by
    funext q
    show F (differentialJet q.2 (HahnSeries.C (traceSeries (k := k) p hp)))
      = differentialJet q.2 (deSitterTrace (k := k) p hp)
    rw [deSitterTrace, ← differentialJet_algebraMap (K' := BoltzmannField k)]
    rfl
  rw [heq] at hind
  exact hind

/-! ## The Boltzmann derivation and the coordinate change -/

/-- The Boltzmann derivation `d/dH = (a/H²)·θ`. -/
@[reducible] def boltzmannDeriv [CharZero k] (a : k) : Differential (BoltzmannField k) := by
  letI := boltzmannEuler (k := k) a
  exact ⟨(algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) a)
      / (boltzmannCoord k) ^ 2) • (boltzmannEuler (k := k) a).deriv⟩

theorem boltzmannDeriv_apply [CharZero k] (a : k) (y : BoltzmannField k) :
    (boltzmannDeriv a).deriv y
      = (algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) a)
        / (boltzmannCoord k) ^ 2) * (boltzmannEuler (k := k) a).deriv y := rfl

/-- The `H`-side algebra structure of the extended field. -/
@[reducible] def hBoltzmannAlgebra [CharZero k] : Algebra (RatFunc k) (BoltzmannField k) :=
  (kHToBoltzmann (k := k)).toAlgebra

/-- The field generated by the two coordinates. -/
def twoCoordField [CharZero k] : IntermediateField (RatFunc k) (BoltzmannField k) :=
  IntermediateField.adjoin (RatFunc k) {boltzmannCoord k}

theorem boltzmannCoord_mem_twoCoordField [CharZero k] :
    boltzmannCoord k ∈ twoCoordField (k := k) :=
  IntermediateField.subset_adjoin (RatFunc k) {boltzmannCoord k} rfl

theorem trdeg_twoCoordField [CharZero k] :
    Algebra.trdeg (RatFunc k) (twoCoordField (k := k)) < Cardinal.aleph0 := by
  have h := trdeg_intermediateFieldAdjoin_range_le (F := RatFunc k) (E := BoltzmannField k)
    (I := PUnit.{u_1 + 1}) (fun _ => boltzmannCoord k)
  have hrange : Set.range (fun _ : PUnit.{u_1 + 1} => boltzmannCoord k) = {boltzmannCoord k} := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      rfl
    · rintro rfl
      exact ⟨PUnit.unit, rfl⟩
  rw [hrange] at h
  refine lt_of_le_of_lt h ?_
  simpa using Cardinal.one_lt_aleph0

/-! ## Derivation closure of the two-coordinate field -/

theorem derivationClosed_adjoin_singleton {C E : Type*} [Field C] [Field E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E] (z : E)
    (hz : z′ ∈ IntermediateField.adjoin C {z}) :
    DerivationClosed (IntermediateField.adjoin C {z}) := by
  intro x hx
  refine IntermediateField.adjoin_induction C
    (p := fun y _ => y′ ∈ IntermediateField.adjoin C ({z} : Set E)) ?_ ?_ ?_ ?_ ?_ hx
  · rintro y rfl
    exact hz
  · intro c
    rw [deriv_algebraMap]
    exact IntermediateField.algebraMap_mem _ _
  · intro u v _ _ hu hv
    rw [map_add]
    exact IntermediateField.add_mem _ hu hv
  · intro u hu hu'
    rw [Derivation.leibniz_inv, smul_eq_mul, sq]
    exact IntermediateField.mul_mem _
      (IntermediateField.neg_mem _ (IntermediateField.mul_mem _
        (IntermediateField.inv_mem _ hu) (IntermediateField.inv_mem _ hu))) hu'
  · intro u v hu hv hu' hv'
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact IntermediateField.add_mem _ (IntermediateField.mul_mem _ hu hv')
      (IntermediateField.mul_mem _ hv hu')

theorem boltzmannEuler_deriv_wEmb [CharZero k] (a : k) (r : RatFunc k) :
    letI := cylinderDifferential (1 : k)
    (boltzmannEuler (k := k) a).deriv (algebraMap (RatFunc k) (BoltzmannField k) r)
      = algebraMap (RatFunc k) (BoltzmannField k) ((cylinderDifferential (1 : k)).deriv r) := by
  letI := cylinderDifferential (1 : k)
  show (boltzmannEuler (k := k) a).deriv
      (algebraMap (MahlerAmbient k) (BoltzmannField k) (kwToAmbient r))
    = algebraMap (MahlerAmbient k) (BoltzmannField k) (kwToAmbient (ratFuncEulerOp r))
  rw [boltzmannEuler_deriv_algebraMap]
  congr 1
  show mahlerAmbientDeriv (HahnSeries.C (ratFuncToHahn r))
    = HahnSeries.C (ratFuncToHahn (ratFuncEulerOp r))
  rw [mahlerAmbientDeriv_C, ratFuncToHahn_eulerOp]

theorem const_mem_twoCoordField [CharZero k] (c : k) :
    algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) c)
      ∈ twoCoordField (k := k) := by
  have hbase : algebraMap (RatFunc k) (BoltzmannField k) (algebraMap k (RatFunc k) c)
      ∈ twoCoordField (k := k) := IntermediateField.algebraMap_mem _ _
  have heq : algebraMap (RatFunc k) (BoltzmannField k) (algebraMap k (RatFunc k) c)
      = algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) c) := by
    show algebraMap (MahlerAmbient k) (BoltzmannField k)
        (kwToAmbient (algebraMap k (RatFunc k) c)) = _
    congr 1
    show HahnSeries.C (ratFuncToHahn (algebraMap k (RatFunc k) c)) = _
    rw [ratFuncToHahn_const, algebraMap_k_mahlerAmbient]
  rwa [heq] at hbase

theorem boltzmannRate_mem_twoCoordField [CharZero k] (a : k) :
    boltzmannRate (k := k) a ∈ twoCoordField (k := k) := by
  refine IntermediateField.mul_mem _ ?_ (const_mem_twoCoordField a⁻¹)
  exact IntermediateField.mul_mem _ boltzmannCoord_mem_twoCoordField
    boltzmannCoord_mem_twoCoordField |>.elim (fun _ => by
      rw [sq]
      exact IntermediateField.mul_mem _ boltzmannCoord_mem_twoCoordField
        boltzmannCoord_mem_twoCoordField) (fun _ => by
      rw [sq]
      exact IntermediateField.mul_mem _ boltzmannCoord_mem_twoCoordField
        boltzmannCoord_mem_twoCoordField)

end

end GaloisForLFunctions.HTGeometry
