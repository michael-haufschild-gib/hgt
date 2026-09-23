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
  (boltzmannCoord k) ^ (2 : ℕ) * algebraMap (MahlerAmbient k) (BoltzmannField k)
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
      / (boltzmannCoord k) ^ (2 : ℕ)) • (boltzmannEuler (k := k) a).deriv⟩

theorem boltzmannDeriv_apply [CharZero k] (a : k) (y : BoltzmannField k) :
    (boltzmannDeriv a).deriv y
      = (algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) a)
        / (boltzmannCoord k) ^ (2 : ℕ)) * (boltzmannEuler (k := k) a).deriv y := rfl

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
  rw [cylinderDifferential_deriv, cylDeriv_one_eq_ratFuncEulerOp]
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
  have hH := boltzmannCoord_mem_twoCoordField (k := k)
  rw [boltzmannRate, sq]
  exact IntermediateField.mul_mem _ (IntermediateField.mul_mem _ hH hH)
    (const_mem_twoCoordField a⁻¹)

theorem derivationClosed_twoCoordField_euler [CharZero k] (a : k) :
    letI := cylinderDifferential (1 : k)
    letI := boltzmannEuler (k := k) a
    DerivationClosed (twoCoordField (k := k)) := by
  letI := cylinderDifferential (1 : k)
  letI := boltzmannEuler (k := k) a
  haveI : DifferentialAlgebra (RatFunc k) (BoltzmannField k) :=
    ⟨fun r => boltzmannEuler_deriv_wEmb a r⟩
  refine derivationClosed_adjoin_singleton (boltzmannCoord k) ?_
  show (boltzmannEuler (k := k) a).deriv (boltzmannCoord k) ∈ twoCoordField (k := k)
  rw [boltzmannEuler_deriv_coord]
  exact boltzmannRate_mem_twoCoordField a

theorem boltzmannCoord_ne_zero [CharZero k] : (boltzmannCoord k) ≠ 0 := by
  rw [boltzmannCoord]
  exact RatFunc.X_ne_zero

theorem derivationClosed_twoCoordField_boltzmann [CharZero k] (a : k) :
    letI := cylinderDifferential (1 : k)
    letI := boltzmannDeriv (k := k) a
    DerivationClosed (twoCoordField (k := k)) := by
  letI := cylinderDifferential (1 : k)
  have hEuler := derivationClosed_twoCoordField_euler (k := k) a
  intro x hx
  show (boltzmannDeriv (k := k) a).deriv x ∈ twoCoordField (k := k)
  rw [boltzmannDeriv_apply]
  refine IntermediateField.mul_mem _ (IntermediateField.div_mem _ (const_mem_twoCoordField a) ?_)
    (hEuler hx)
  rw [sq]
  exact IntermediateField.mul_mem _ boltzmannCoord_mem_twoCoordField
    boltzmannCoord_mem_twoCoordField

theorem kHToBoltzmann_mem_twoCoordField [CharZero k] (r : RatFunc k) :
    kHToBoltzmann r ∈ twoCoordField (k := k) := by
  have hC : ∀ c : k, kHToBoltzmann (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c))
      = algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) c) := by
    intro c
    have h := RatFunc.map_apply_div (Polynomial.mapRingHom (algebraMap k (MahlerAmbient k)))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap k (MahlerAmbient k)).injective))
      (Polynomial.C c) 1
    simp only [map_one, div_one] at h
    show RatFunc.map (Polynomial.mapRingHom (algebraMap k (MahlerAmbient k)))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap k (MahlerAmbient k)).injective))
      (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)) = _
    rw [h]
    simp [RatFunc.algebraMap_C]
  have hX : kHToBoltzmann (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)
      = boltzmannCoord k := by
    rw [RatFunc.algebraMap_X]
    exact kHToBoltzmann_X
  have hpoly : ∀ P : Polynomial k,
      kHToBoltzmann (algebraMap (Polynomial k) (RatFunc k) P) ∈ twoCoordField (k := k) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add, map_add]
        exact IntermediateField.add_mem _ hp hq
    | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, hC, hX]
        exact IntermediateField.mul_mem _ (const_mem_twoCoordField c)
          (IntermediateField.pow_mem _ boltzmannCoord_mem_twoCoordField n)
  refine RatFunc.induction_on (P := fun r => kHToBoltzmann r ∈ twoCoordField (k := k)) r ?_
  intro P S _
  rw [map_div₀]
  exact IntermediateField.div_mem _ (hpoly P) (hpoly S)

/-! ## The coordinate change -/

set_option synthInstance.maxHeartbeats 800000 in
/-- **The detailed-balance trace is hypertranscendental in the Hubble coordinate.**  The Boltzmann
change of variable is differentially algebraic in both directions, so hypertranscendence over
`k(w)` for the Euler derivation transfers to hypertranscendence over `k(H)` for `d/dH`. -/
theorem hypertranscendentalOver_deSitterTrace_H [CharZero k] {p : ℕ} (hp : 1 < p) (a : k)
    (ha : a ≠ 0) :
    letI := cylinderDifferential (1 : k)
    @HypertranscendentalOver (RatFunc k) (BoltzmannField k) _ _ (hBoltzmannAlgebra (k := k))
      (boltzmannDeriv a) (deSitterTrace (k := k) p hp) := by
  letI := cylinderDifferential (1 : k)
  letI := boltzmannEuler (k := k) a
  haveI hcz : CharZero (BoltzmannField k) := by
    refine charZero_of_injective_algebraMap (R := RatFunc k) ?_
    exact (algebraMap (RatFunc k) (BoltzmannField k)).injective
  haveI : DifferentialAlgebra (RatFunc k) (BoltzmannField k) :=
    ⟨fun r => boltzmannEuler_deriv_wEmb a r⟩
  intro hDA
  -- the two-coordinate field, as an algebra over the `H`-base
  letI algFH : Algebra (RatFunc k) (twoCoordField (k := k)) :=
    (RingHom.codRestrict (kHToBoltzmann (k := k)) (twoCoordField (k := k)).toSubfield
      kHToBoltzmann_mem_twoCoordField).toAlgebra
  haveI towerH : @IsScalarTower (RatFunc k) (twoCoordField (k := k)) (BoltzmannField k)
      algFH.toSMul _ (hBoltzmannAlgebra (k := k)).toSMul :=
    @IsScalarTower.of_algebraMap_eq (RatFunc k) (twoCoordField (k := k)) (BoltzmannField k) _ _ _
      algFH _ (hBoltzmannAlgebra (k := k)) fun r => rfl
  -- Step A: enlarge the base from `k(H)` to the two-coordinate field
  have hDAF : @DifferentialAlgebraicOver (twoCoordField (k := k)) (BoltzmannField k) _ _ _
      (boltzmannDeriv a) (deSitterTrace (k := k) p hp) :=
    @differentialAlgebraicOver_mono (RatFunc k) (twoCoordField (k := k)) (BoltzmannField k)
      _ _ _ algFH _ (hBoltzmannAlgebra (k := k)) towerH (boltzmannDeriv a) _ hDA
  -- Step B: pass from `d/dH` to the Euler derivation
  letI diffFEuler : Differential (twoCoordField (k := k)) :=
    @derivationClosedDifferential (RatFunc k) (BoltzmannField k) _ _ _
      (boltzmannEuler (k := k) a) _ (derivationClosed_twoCoordField_euler a)
  letI diffFBoltz : Differential (twoCoordField (k := k)) :=
    @derivationClosedDifferential (RatFunc k) (BoltzmannField k) _ _ _
      (boltzmannDeriv (k := k) a) _ (derivationClosed_twoCoordField_boltzmann a)
  have hcompatE : ∀ y : twoCoordField (k := k),
      (boltzmannEuler (k := k) a).deriv
          (algebraMap (twoCoordField (k := k)) (BoltzmannField k) y)
        = algebraMap (twoCoordField (k := k)) (BoltzmannField k) (diffFEuler.deriv y) :=
    fun _ => rfl
  have hcompatB : ∀ y : twoCoordField (k := k),
      (boltzmannDeriv (k := k) a).deriv
          (algebraMap (twoCoordField (k := k)) (BoltzmannField k) y)
        = algebraMap (twoCoordField (k := k)) (BoltzmannField k) (diffFBoltz.deriv y) :=
    fun _ => rfl
  have hscaleElt : (algebraMap (MahlerAmbient k) (BoltzmannField k)
      (algebraMap k (MahlerAmbient k) a) / (boltzmannCoord k) ^ (2 : ℕ))
      ∈ twoCoordField (k := k) := by
    refine IntermediateField.div_mem _ (const_mem_twoCoordField a) ?_
    rw [sq]
    exact IntermediateField.mul_mem _ boltzmannCoord_mem_twoCoordField
      boltzmannCoord_mem_twoCoordField
  have hinvElt : ((boltzmannCoord k) ^ (2 : ℕ)
      / algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) a))
      ∈ twoCoordField (k := k) := by
    refine IntermediateField.div_mem _ ?_ (const_mem_twoCoordField a)
    rw [sq]
    exact IntermediateField.mul_mem _ boltzmannCoord_mem_twoCoordField
      boltzmannCoord_mem_twoCoordField
  have haL : algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) a)
      ≠ 0 := by
    intro h
    refine ha ?_
    have h1 := (injective_iff_map_eq_zero
      (algebraMap (MahlerAmbient k) (BoltzmannField k))).mp
      (algebraMap (MahlerAmbient k) (BoltzmannField k)).injective _ h
    exact (injective_iff_map_eq_zero (algebraMap k (MahlerAmbient k))).mp
      (algebraMap k (MahlerAmbient k)).injective _ h1
  have hscale : ∀ y : BoltzmannField k,
      (boltzmannEuler (k := k) a).deriv y
        = algebraMap (twoCoordField (k := k)) (BoltzmannField k) ⟨_, hinvElt⟩
          * (boltzmannDeriv (k := k) a).deriv y := by
    intro y
    rw [boltzmannDeriv_apply]
    show _ = ((boltzmannCoord k) ^ (2 : ℕ)
        / algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) a))
      * ((algebraMap (MahlerAmbient k) (BoltzmannField k) (algebraMap k (MahlerAmbient k) a)
        / (boltzmannCoord k) ^ (2 : ℕ)) * (boltzmannEuler (k := k) a).deriv y)
    have hH : (boltzmannCoord k) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ boltzmannCoord_ne_zero
    field_simp
    rw [mul_div_assoc, div_self boltzmannCoord_ne_zero, mul_one]
  have hDAFEuler : @DifferentialAlgebraicOver (twoCoordField (k := k)) (BoltzmannField k) _ _ _
      (boltzmannEuler (k := k) a) (deSitterTrace (k := k) p hp) :=
    @differentialAlgebraicOver_scaled (twoCoordField (k := k)) (BoltzmannField k) _ _ _ hcz
      diffFEuler diffFBoltz (boltzmannEuler (k := k) a) (boltzmannDeriv (k := k) a)
      ⟨_, hinvElt⟩ hcompatE hcompatB hscale _ hDAF
  -- Step C: descend the tower to `k(w)`
  have hDAw := @differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0 (RatFunc k)
    (BoltzmannField k) _ _ _ _ _ _ hcz (twoCoordField (k := k))
    (derivationClosed_twoCoordField_euler a) trdeg_twoCoordField _ hDAFEuler
  exact (hypertranscendentalOver_deSitterTrace_w hp a) hDAw

/-! ## The Hubble-scale constraint and the non-selection observation -/

/-- **The Hubble-scale constraint**: the detailed-balance trace satisfies the ultrametric Mahler
equation read in the Boltzmann coordinate. -/
theorem deSitterTrace_constraint [CharZero k] {p : ℕ} (hp : 1 < p) :
    deSitterTrace (k := k) p hp
      = algebraMap (MahlerAmbient k) (BoltzmannField k)
          (HahnSeries.C (HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p))
        + algebraMap (MahlerAmbient k) (BoltzmannField k)
          (HahnSeries.C (HahnSeries.C ((p : k))
            * mahlerHom (k := k) p (by omega) (traceSeries p hp))) := by
  rw [deSitterTrace, ← map_add, ← map_add]
  congr 2
  exact traceSeries_mahler_equation (k := k) p hp

/-- **The Hubble coordinate is not a formal germ in the Boltzmann coordinate**: `−a/log w` is
transcendental over the ambient field, which is what makes the constraint rigid only after
passing to the Boltzmann coordinate. -/
theorem boltzmannCoord_not_mem_ambient [CharZero k] :
    boltzmannCoord k ∉ Set.range (algebraMap (MahlerAmbient k) (BoltzmannField k)) := by
  rintro ⟨c, hc⟩
  have hC : algebraMap (MahlerAmbient k) (BoltzmannField k) c
      = algebraMap (Polynomial (MahlerAmbient k)) (BoltzmannField k) (Polynomial.C c) :=
    (RatFunc.algebraMap_C c).symm
  have hnum : (boltzmannCoord k).num = Polynomial.X := RatFunc.num_X
  rw [← hc, hC, RatFunc.num_algebraMap] at hnum
  have hdeg := congrArg Polynomial.natDegree hnum
  rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hdeg
  exact absurd hdeg.symm one_ne_zero

end

end GaloisForLFunctions.HTGeometry
