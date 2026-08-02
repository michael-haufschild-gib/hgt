import GaloisForLFunctions.HTGeometry.UniformGammaDatumAlgebra

/-!
# The exponential valuation direction created by adjoining Gamma

The boundary datum of §1 is a homomorphism.  Collecting the datum of every unit of `K_Γ` gives a group
map to `ℤ³ × ℂˣ`, whose first component — the `Γ`-exponent — is a surjective homomorphism onto `ℤ`
that kills every unit of the digamma field.

That is the statement of §4: adjoining `Γ` to `L` creates exactly one exponential valuation
direction, and `Γ` itself is a uniformizer for it.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance uniformDatHomDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance uniformDatHomIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance uniformDatHomDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance uniformDatHomComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance uniformDatHomRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance uniformDatHomRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance uniformDatHomRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- The Gamma field `K_Γ = ℂ(s)⟨Γ⟩`, as an intermediate field. -/
def gammaFieldK : IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField)

/-- The datum of `1` is trivial. -/
theorem hasGammaTubeDatum_one {M : ℝ} : HasGammaTubeDatum M (1 : upperEndMeroField) 0 0 0 1 := by
  refine ⟨one_ne_zero, fun _ _ => 1, ?_, ?_⟩
  · refine ⟨1, 1, fun _ => 1, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_one]
      rfl
    · rw [map_one]
      rfl
    · rw [map_one]
      exact one_ne_zero
    · rw [map_one, div_one]
    · intro σ t
      rw [div_one]
  · refine (tubeLimit_const (M := M) 1).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
    have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_le ht
    have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_le ht
    rw [gammaShapeZ, zpow_zero, zpow_zero, zpow_zero, mul_one, mul_one, div_one]

/-- A unit of the Gamma field is a nonzero member of it. -/
theorem coe_gammaFieldKUnit_mem (u : gammaFieldKˣ) :
    ((u : gammaFieldK) : upperEndMeroField)
      ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField) :=
  (u : gammaFieldK).2

/-- A unit of the Gamma field is nonzero in the ambient field. -/
theorem coe_gammaFieldKUnit_ne_zero (u : gammaFieldKˣ) :
    ((u : gammaFieldK) : upperEndMeroField) ≠ 0 := by
  intro h0
  refine u.ne_zero (Subtype.ext ?_)
  simp only [ZeroMemClass.coe_zero]
  exact h0

/-- Every unit of the Gamma field has a datum with a nonzero residue. -/
theorem exists_gammaFieldKUnit_datum (u : gammaFieldKˣ) :
    ∃ d : (ℤ × ℤ × ℤ) × ℂˣ,
      HasGammaTubeDatum 1 ((u : gammaFieldK) : upperEndMeroField)
        d.1.1 d.1.2.1 d.1.2.2 (d.2 : ℂ) := by
  obtain ⟨k, a, b, c, hdat⟩ :=
    exists_hasGammaTubeDatum one_pos (coe_gammaFieldKUnit_mem u) (coe_gammaFieldKUnit_ne_zero u)
  exact ⟨((k, a, b), Units.mk0 c hdat.1), hdat⟩

/-- The datum of a unit of the Gamma field: the `Γ`-exponent, the argument exponent, the logarithm
exponent and the residue. -/
def gammaUnitDatum (u : gammaFieldKˣ) : (ℤ × ℤ × ℤ) × ℂˣ :=
  Classical.choose (exists_gammaFieldKUnit_datum u)

theorem gammaUnitDatum_spec (u : gammaFieldKˣ) :
    HasGammaTubeDatum 1 ((u : gammaFieldK) : upperEndMeroField)
      (gammaUnitDatum u).1.1 (gammaUnitDatum u).1.2.1 (gammaUnitDatum u).1.2.2
      ((gammaUnitDatum u).2 : ℂ) :=
  Classical.choose_spec (exists_gammaFieldKUnit_datum u)

/-- The datum of a unit is the only one it has. -/
theorem gammaUnitDatum_eq_of {u : gammaFieldKˣ} {k a b : ℤ} {c : ℂˣ}
    (h : HasGammaTubeDatum 1 ((u : gammaFieldK) : upperEndMeroField) k a b (c : ℂ)) :
    gammaUnitDatum u = ((k, a, b), c) := by
  obtain ⟨h1, h2, h3, h4⟩ := hasGammaTubeDatum_unique one_pos (gammaUnitDatum_spec u) h
  refine Prod.ext ?_ (Units.ext h4)
  refine Prod.ext h1 (Prod.ext h2 h3)

/-- **The boundary datum is a group homomorphism.**  On a product the three exponents add and the
residues multiply. -/
def gammaDatumHom : gammaFieldKˣ →* Multiplicative (ℤ × ℤ × ℤ) × ℂˣ where
  toFun u := (Multiplicative.ofAdd (gammaUnitDatum u).1, (gammaUnitDatum u).2)
  map_one' := by
    have h1 : gammaUnitDatum (1 : gammaFieldKˣ) = ((0, 0, 0), 1) := by
      refine gammaUnitDatum_eq_of ?_
      have hval : ((((1 : gammaFieldKˣ) : gammaFieldK)) : upperEndMeroField) = 1 := by
        simp
      rw [hval]
      simpa using (hasGammaTubeDatum_one (M := 1))
    rw [h1]
    rfl
  map_mul' u v := by
    have hval : (((u * v : gammaFieldKˣ) : gammaFieldK) : upperEndMeroField)
        = ((u : gammaFieldK) : upperEndMeroField) * ((v : gammaFieldK) : upperEndMeroField) := by
      simp
    have hmul : HasGammaTubeDatum 1 ((((u * v : gammaFieldKˣ)) : gammaFieldK) : upperEndMeroField)
        ((gammaUnitDatum u).1.1 + (gammaUnitDatum v).1.1)
        ((gammaUnitDatum u).1.2.1 + (gammaUnitDatum v).1.2.1)
        ((gammaUnitDatum u).1.2.2 + (gammaUnitDatum v).1.2.2)
        ((((gammaUnitDatum u).2 * (gammaUnitDatum v).2 : ℂˣ)) : ℂ) := by
      rw [hval]
      simpa using (gammaUnitDatum_spec u).mul (gammaUnitDatum_spec v)
    rw [gammaUnitDatum_eq_of hmul]
    rfl

/-- **The `Γ`-exponent is a homomorphism to `ℤ`.** -/
def gammaExponentHom : gammaFieldKˣ →* Multiplicative ℤ :=
  (AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ (ℤ × ℤ))).comp
    ((MonoidHom.fst (Multiplicative (ℤ × ℤ × ℤ)) ℂˣ).comp gammaDatumHom)

theorem gammaExponentHom_apply (u : gammaFieldKˣ) :
    gammaExponentHom u = Multiplicative.ofAdd (gammaUnitDatum u).1.1 := rfl

/-- `Γ`, as a unit of the Gamma field. -/
def gammaUnit : gammaFieldKˣ :=
  Units.mk0 (⟨gammaUpperMero, subset_differentialAdjoin (RatFunc ℂ) _ (Set.mem_singleton _)⟩ :
      gammaFieldK)
    (by
      intro h0
      exact gammaUpperMero_ne_zero (by simpa using congrArg (Subtype.val) h0))

/-- **`Γ` is a uniformizer**: its `Γ`-exponent is `1`. -/
theorem gammaExponentHom_gammaUnit : gammaExponentHom gammaUnit = Multiplicative.ofAdd (1 : ℤ) := by
  have hval : ((gammaUnit : gammaFieldK) : upperEndMeroField) = gammaUpperMero := rfl
  have hdat : gammaUnitDatum gammaUnit = ((1, 0, 0), 1) := by
    refine gammaUnitDatum_eq_of ?_
    rw [hval]
    simpa using (hasGammaTubeDatum_gammaUpperMero (M := 1))
  rw [gammaExponentHom_apply, hdat]

/-- **The `Γ`-exponent is surjective**: every integer is the exponent of a power of `Γ`. -/
theorem gammaExponentHom_surjective : Function.Surjective gammaExponentHom := by
  intro n
  refine ⟨gammaUnit ^ (Multiplicative.toAdd n), ?_⟩
  rw [map_zpow, gammaExponentHom_gammaUnit, ← ofAdd_zsmul]
  simp

/-- **The digamma field lies in the kernel.**  A unit of `K_Γ` whose value lies in `ℂ(s)⟨ψ⟩` has
`Γ`-exponent `0`. -/
theorem gammaExponentHom_eq_one_of_mem_digammaAdjoin {u : gammaFieldKˣ}
    (hu : ((u : gammaFieldK) : upperEndMeroField)
      ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField)) :
    gammaExponentHom u = 1 := by
  obtain ⟨a, b, c, hdat⟩ :=
    exists_hasGammaTubeDatum_digammaField one_pos hu (coe_gammaFieldKUnit_ne_zero u)
  obtain ⟨h1, -, -, -⟩ := hasGammaTubeDatum_unique one_pos (gammaUnitDatum_spec u) hdat
  rw [gammaExponentHom_apply, h1]
  rfl

end

end GaloisForLFunctions.HTGeometry
