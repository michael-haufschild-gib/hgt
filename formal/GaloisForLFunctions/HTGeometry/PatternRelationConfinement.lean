import GaloisForLFunctions.HTGeometry.PacketValueFactorialBridge
import GaloisForLFunctions.HTGeometry.PacketPlacementAvoidance
import GaloisForLFunctions.HTGeometry.PolynomialVariableRescale

/-!
# A pattern relation confines the carrier jets to a proper zero set

This is the step that turns the rank-defect mechanism into a statement about the actual carrier.

Given a pattern relation with a nonzero coefficient vector, place the row packet so that every row
node is admissible and misses the finite degenerate set.  The relation, instantiated at that packet,
then says at *every* row that the carrier's jet vector lies in the zero set of a nonzero
multivariate polynomial.

Generic carriers violate exactly this, so no such relation can hold with a nonzero coefficient
vector.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-- **Placement plus relation confines the carrier jets.**  A pattern relation with a nonzero
coefficient vector forces, at every row of a suitably placed packet, the carrier's jet vector into
the zero set of a nonzero polynomial. -/
theorem exists_placed_relation_forcing_zeroSet
    {row ι κ : Type} [Fintype row] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (nu : ProbabilityMeasure ℝ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexp : Function.Injective exponent)
    (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) (β₀ : κ) {d₀ : Fin (degree + 1)}
    (hcoeff : coeff (β₀, d₀) ≠ 0)
    (hrel : probabilityCarrierExpandedPatternRelationHolds
      (row := row) nu degree orders exponent shift coeff)
    (z₀ : row → ℂ) (hz₀ : Function.Injective z₀) :
    ∃ (z : row → ℂ) (hz : Function.Injective z),
      (∀ r i, (z r + shift.1 i).im < 0) ∧
      ∀ r : row,
        (∑ β : κ, MvPolynomial.monomial (exponent β)
            (rowCoefficientPolynomial degree coeff β (z r))) ≠ 0 ∧
          MvPolynomial.eval
            (fun k => probabilityCarrierExpandedPacketValue nu orders ⟨z, hz⟩ shift (r, k))
            (∑ β : κ, MvPolynomial.monomial (exponent β)
              (rowCoefficientPolynomial degree coeff β (z r))) = 0 := by
  classical
  obtain ⟨z, hz, hupper, hnondeg⟩ :=
    exists_placed_lower_packet_all_rows_nondegenerate degree
      (Fintype.card (Σ i, Fin (orders i))) exponent hexp coeff β₀ hcoeff z₀ hz₀ shift.1
  refine ⟨z, hz, hupper, ?_⟩
  intro r
  refine ⟨hnondeg r, ?_⟩
  have hadm : ∀ x, (combinedProjectiveRowShiftPacket ⟨z, hz⟩ shift x).im < 0 := by
    intro x
    exact hupper x.1 x.2
  have hrow := hrel ⟨z, hz⟩ hadm r
  rw [← sum_coeff_mul_expandedDifferentialEvaluationMatrix degree
    (Fintype.card (Σ i, Fin (orders i))) z exponent
    (probabilityCarrierExpandedPacketValue nu orders ⟨z, hz⟩ shift) coeff r]
  exact hrow

/-- Nondegeneracy of a carrier's jets against every nonzero polynomial, at admissible packets.

**WARNING — this predicate is vacuous.**  For any point `y` of a nonempty jet index the polynomial
`X s - C (y s)` is nonzero and vanishes at `y`, so no carrier satisfies it.  The theorems below that
take it as a hypothesis are therefore true but not usable: the genericity development does *not*
establish this property, and cannot.

The correct nondegeneracy for the freeness predicate is rank-theoretic rather than pointwise: the
expanded evaluation matrix must have a nonvanishing minor, which is one polynomial condition per
pattern and packet, not one per coefficient vector.  That is the shape of
`MaximalTranslationFullRankWitness` and of `probabilityCarrierExpandedFullRankWitness`, and it is
the interface the genericity theorems can supply.  This definition is retained only to document the
dead end. -/
def CarrierJetNondegenerateAt
    {row ι : Type} [Fintype row] [Fintype ι]
    (nu : ProbabilityMeasure ℝ) (orders : ι → ℕ)
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∀ (z : row → ℂ) (hz : Function.Injective z),
    (∀ r i, (z r + shift.1 i).im < 0) →
    ∀ Q : MvPolynomial (Fin (Fintype.card (Σ i, Fin (orders i)))) ℂ, Q ≠ 0 →
      ∀ r : row,
        MvPolynomial.eval
          (fun k => probabilityCarrierExpandedPacketValue nu orders ⟨z, hz⟩ shift (r, k))
          Q ≠ 0

/-- **Refutation of a pattern relation.**  A carrier whose jets are nondegenerate against every
nonzero polynomial admits no pattern relation with a nonzero coefficient: the placement theorem
would otherwise produce a nonzero polynomial vanishing on those jets. -/
theorem coeff_eq_zero_of_relation_of_jetNondegenerate
    {row ι κ : Type} [Fintype row] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [Nonempty row]
    (nu : ProbabilityMeasure ℝ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexp : Function.Injective exponent)
    (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrel : probabilityCarrierExpandedPatternRelationHolds
      (row := row) nu degree orders exponent shift coeff)
    (z₀ : row → ℂ) (hz₀ : Function.Injective z₀)
    (hnd : CarrierJetNondegenerateAt (row := row) nu orders shift) :
    ∀ col, coeff col = 0 := by
  classical
  intro col
  by_contra hne
  obtain ⟨β₀, d₀⟩ := col
  obtain ⟨z, hz, hupper, hrows⟩ :=
    exists_placed_relation_forcing_zeroSet nu degree orders exponent hexp shift
      coeff β₀ hne hrel z₀ hz₀
  obtain ⟨r⟩ := ‹Nonempty row›
  obtain ⟨hQne, hQzero⟩ := hrows r
  exact hnd z hz hupper _ hQne r hQzero

/-- A finite index type admits an injective family of complex numbers. -/
theorem exists_injective_complexFamily {row : Type*} [Fintype row] :
    ∃ z : row → ℂ, Function.Injective z := by
  refine ⟨fun r => ((Fintype.equivFin row r : ℕ) : ℂ), ?_⟩
  intro a b hab
  have hnat : ((Fintype.equivFin row a : ℕ) : ℂ) = ((Fintype.equivFin row b : ℕ) : ℂ) := hab
  have hn : (Fintype.equivFin row a : ℕ) = (Fintype.equivFin row b : ℕ) := by
    exact_mod_cast hnat
  exact (Fintype.equivFin row).injective (Fin.ext hn)

/-- **Freeness from jet nondegeneracy.**  A carrier whose jets are nondegenerate against every
nonzero polynomial, at every pattern and shift configuration, is maximally
translation-differentially free.  The pattern's exponent enumeration is injective by
`carrierPatternExponent_injective`, and the initial row family is constructed, so jet nondegeneracy
is the only remaining input. -/
theorem maximalTranslationDifferentialFree_of_jetNondegenerate
    (nu : ProbabilityMeasure ℝ)
    (hnd : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      CarrierJetNondegenerateAt (row := CarrierPatternRow p) nu p.orders shift) :
    MaximalTranslationDifferentialFree nu := by
  intro p shift coeff hrel
  obtain ⟨z₀, hz₀⟩ := exists_injective_complexFamily (row := CarrierPatternRow p)
  exact coeff_eq_zero_of_relation_of_jetNondegenerate nu p.coefficientDegree p.orders
    (carrierPatternExponent p) (carrierPatternExponent_injective p) shift coeff hrel
    z₀ hz₀ (hnd p shift)

/-- **Nondegeneracy transfers from moment coordinates to packet coordinates.**  Packet values are
factorial multiples of kernel moments, and factorials are nonzero, so the two coordinate systems
differ by an invertible diagonal rescaling of the polynomial variables. -/
theorem carrierJetNondegenerateAt_of_momentNondegenerate
    {row ι : Type} [Fintype row] [Fintype ι]
    (nu : ProbabilityMeasure ℝ) (orders : ι → ℕ)
    (shift : InjectiveShiftConfiguration ι)
    (hmom : ∀ (z : row → ℂ) (hz : Function.Injective z),
      (∀ r i, (z r + shift.1 i).im < 0) →
      ∀ r : row,
        ∀ Q : MvPolynomial (Fin (Fintype.card (Σ i, Fin (orders i)))) ℂ, Q ≠ 0 →
          MvPolynomial.eval
            (fun k => cauchyKernelMoment (nu : Measure ℝ)
              (factorialBridgePacketOrder orders (r, k))
              (factorialBridgePacketNode orders ⟨z, hz⟩ shift (r, k))) Q ≠ 0) :
    CarrierJetNondegenerateAt (row := row) nu orders shift := by
  intro z hz hupper Q hQ r
  have hnode : ∀ k, (factorialBridgePacketNode orders ⟨z, hz⟩ shift (r, k)).im ≠ 0 := by
    intro k
    exact ne_of_lt (hupper r _)
  have hvals :
      (fun k => probabilityCarrierExpandedPacketValue nu orders ⟨z, hz⟩ shift (r, k)) =
        fun k => ((Nat.factorial (factorialBridgePacketOrder orders (r, k)) : ℕ) : ℂ) *
          cauchyKernelMoment (nu : Measure ℝ) (factorialBridgePacketOrder orders (r, k))
            (factorialBridgePacketNode orders ⟨z, hz⟩ shift (r, k)) := by
    funext k
    exact probabilityCarrierExpandedPacketValue_eq_factorial_moment nu orders
      ⟨z, hz⟩ shift (r, k) (hnode k)
  rw [hvals]
  refine eval_ne_zero_of_scaled
    (fun k => ((Nat.factorial (factorialBridgePacketOrder orders (r, k)) : ℕ) : ℂ)) ?_ _
    (hmom z hz hupper r) Q hQ
  intro k
  exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- **Freeness from moment-coordinate nondegeneracy.**  Composing the transfer with the refutation:
a carrier whose *kernel moments* are nondegenerate against every nonzero polynomial, at every
pattern and admissible packet, is maximally translation-differentially free.  This is the interface
the analytic genericity development speaks in. -/
theorem maximalTranslationDifferentialFree_of_momentNondegenerate
    (nu : ProbabilityMeasure ℝ)
    (hmom : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (z : CarrierPatternRow p → ℂ) (hz : Function.Injective z),
      (∀ r i, (z r + shift.1 i).im < 0) →
      ∀ r : CarrierPatternRow p,
        ∀ Q : MvPolynomial
          (Fin (Fintype.card (Σ i : CarrierPatternShift p, Fin (p.orders i)))) ℂ, Q ≠ 0 →
          MvPolynomial.eval
            (fun k => cauchyKernelMoment (nu : Measure ℝ)
              (factorialBridgePacketOrder p.orders (r, k))
              (factorialBridgePacketNode p.orders ⟨z, hz⟩ shift (r, k))) Q ≠ 0) :
    MaximalTranslationDifferentialFree nu :=
  maximalTranslationDifferentialFree_of_jetNondegenerate nu
    (fun p shift =>
      carrierJetNondegenerateAt_of_momentNondegenerate nu p.orders shift (hmom p shift))

end

end GaloisForLFunctions.HTGeometry
