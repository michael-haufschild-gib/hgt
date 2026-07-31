import GaloisForLFunctions.HTGeometry.HolographicLocalityBound
import GaloisForLFunctions.HTGeometry.SmoothWaringQuantumNormalFormUniversalityLaw

/-!
# Smooth Waring quantum normal form versus holographic locality

Injectivity of the full exterior endomorphism commutator is equivalent to linear independence of
the coordinate principal brackets.  The missing reverse implication turns every smooth Waring
quantum packet into a locality theorem: any bounded-valence membrane presentation must cover
every two-plane and obey the universal quadratic covering bound.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v

variable {ι : Type*} [LinearOrder ι]

/-- Increasing law pairs as order embeddings of `Fin 2`. -/
def quantumLawPairOrderEmbedding (p : QuantumLawPair ι) : Fin 2 ↪o ι :=
  OrderEmbedding.ofStrictMono ![p.lower, p.upper] (by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    exact p.isLt)

theorem quantumLawPairOrderEmbedding_injective :
    Function.Injective (quantumLawPairOrderEmbedding (ι := ι)) := by
  intro p q h
  have h0 := congrArg (fun e : Fin 2 ↪o ι => e 0) h
  have h1 := congrArg (fun e : Fin 2 ↪o ι => e 1) h
  cases p
  cases q
  simp [quantumLawPairOrderEmbedding] at h0 h1
  subst h0
  subst h1
  rfl

/-- The two-element coordinate subset underlying an increasing law pair. -/
def quantumLawPairPowerset (p : QuantumLawPair ι) : Set.powersetCard ι 2 :=
  Set.powersetCard.ofFinEmbEquiv (quantumLawPairOrderEmbedding p)

theorem quantumLawPairPowerset_injective :
    Function.Injective (quantumLawPairPowerset (ι := ι)) :=
  Set.powersetCard.ofFinEmbEquiv.injective.comp
    quantumLawPairOrderEmbedding_injective

variable {K : Type u} {M : Type v}
  [Field K] [AddCommGroup M] [Module K M] [Fintype ι]

theorem exteriorPower_basis_quantumLawPairPowerset
    (p : QuantumLawPair ι) :
    ((Pi.basisFun K ι).exteriorPower 2) (quantumLawPairPowerset p) =
      quantumPairWedge (K := K) p := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family quantumLawPairPowerset quantumPairWedge
  rw [Equiv.symm_apply_apply]
  rfl

theorem quantumPairWedge_linearIndependent :
    LinearIndependent K
      (quantumPairWedge (K := K) : QuantumLawPair ι → ⋀[K]^2 (ι → K)) := by
  have hbasis :=
    ((Pi.basisFun K ι).exteriorPower 2).linearIndependent.comp
      (quantumLawPairPowerset (ι := ι))
      quantumLawPairPowerset_injective
  have heq :
      ((fun s => ((Pi.basisFun K ι).exteriorPower 2) s) ∘
          quantumLawPairPowerset) =
        (quantumPairWedge (K := K) : QuantumLawPair ι → ⋀[K]^2 (ι → K)) := by
    funext p
    exact exteriorPower_basis_quantumLawPairPowerset p
  rw [heq] at hbasis
  exact hbasis

variable [CharZero K]

omit [CharZero K] in
/-- Injectivity of the complete exterior commutator forces independence of all coordinate
principal brackets. -/
theorem principalBracketPair_linearIndependent_of_endomorphismCommutatorMap_injective
    (symbol : (ι → K) →ₗ[K] Module.End K M)
    (hinjective : Function.Injective (endomorphismCommutatorMap symbol)) :
    LinearIndependent K (principalBracketPair symbol) := by
  have hmap :
      (fun p : QuantumLawPair ι =>
        endomorphismCommutatorMap symbol (quantumPairWedge (K := K) p)) =
        principalBracketPair symbol := by
    funext p
    rw [quantumPairWedge, endomorphismCommutatorMap_wedge]
    simp [principalBracketPair, LieRing.of_associative_ring_bracket]
  have himage :=
    (quantumPairWedge_linearIndependent (K := K) (ι := ι)).map'
      (endomorphismCommutatorMap symbol)
      (LinearMap.ker_eq_bot.mpr hinjective)
  change LinearIndependent K
    (fun p : QuantumLawPair ι =>
      endomorphismCommutatorMap symbol (quantumPairWedge (K := K) p)) at himage
  rw [hmap] at himage
  exact himage

omit [CharZero K] in
/-- Full exterior commutator injectivity is equivalent to coordinate principal-bracket
independence. -/
theorem principalBracketPair_linearIndependent_iff_endomorphismCommutatorMap_injective
    (symbol : (ι → K) →ₗ[K] Module.End K M) :
    LinearIndependent K (principalBracketPair symbol) ↔
      Function.Injective (endomorphismCommutatorMap symbol) :=
  ⟨endomorphismCommutatorMap_injective_of_principalBracketPair_linearIndependent symbol,
    principalBracketPair_linearIndependent_of_endomorphismCommutatorMap_injective symbol⟩

variable {d m n : ℕ} [NeZero d] [Fact (1 < d)]
  {H : Type*} [Fintype H]

/-- **Smooth Waring quantum-normal-form/locality universality law.**  A projectively smooth
Waring form retains its exact hypersurface horizon, maximal derivation symbol, independent
twisted-monomial normal form, and multiplication law.  Every membrane-local presentation of the
same Waring symbol is pair-complete and, at valence at most `Δ`, must satisfy the quadratic
two-plane covering bound. -/
theorem smoothMvWaring_normalForm_holographicLocalityUniversality
    (q : K) (hq : IsPrimitiveRoot q d)
    (a : Matrix (Fin n) (Fin m) K)
    (hsmooth : MvPolynomialProjectivelySmooth (mvWaringPolynomial d a))
    (support : H → Finset (Fin m)) (Δ : ℕ)
    (hmembrane :
      MembraneLocalPrincipalBrackets
        (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)
        support)
    (hlocal : MembraneValenceAtMost support Δ) :
    (({v : Fin m → K | ¬ AlgebraicIndependent K
          (generalizedCliffordShiftFieldJet
            (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin v)
            (finiteQuantumRoot (K := K) (ι := Fin n) (d := d)))} =
          {v : Fin m → K |
            MvPolynomial.eval v (mvWaringPolynomial d a) = 0}) ∧
        Function.Injective
          (derivationCommutatorMap
            (generalizedCliffordShiftFieldDerivationLaw
              (finiteQuantumWaringSymbol
                (d := d) q hq.pow_eq_one a.mulVecLin))) ∧
        LinearIndependent K
          (finiteQuantumMonomial (K := K) (ι := Fin n) (d := d) q hq.pow_eq_one) ∧
        ∀ x y : Fin n → ZMod d,
          finiteQuantumMonomial q hq.pow_eq_one x *
              finiteQuantumMonomial q hq.pow_eq_one y =
            (∏ i, finiteQuantumCharacter d q hq.pow_eq_one
                (-(y i * finiteQuantumTailCharge i x))) •
              finiteQuantumMonomial q hq.pow_eq_one (x + y)) ∧
      MembranePairComplete support ∧
      Nat.choose m 2 ≤ Fintype.card H * Nat.choose Δ 2 := by
  have hpacket := smoothMvWaring_normalForm_maximalHorizon q hq a hsmooth
  have hL := mvWaring_mulVecLin_injective_of_projectivelySmooth a hsmooth
  have hcommutator :
      Function.Injective
        (endomorphismCommutatorMap
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)) := by
    simpa [finiteQuantumWaringSymbol, finiteQuantumTorusSymbol] using
      (finiteQuantumTorus_endomorphismCommutatorMap_injective
        q hq.pow_eq_one (hq.ne_one Fact.out) a.mulVecLin hL)
  have hLI :
      LinearIndependent K
        (principalBracketPair
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)) :=
    principalBracketPair_linearIndependent_of_endomorphismCommutatorMap_injective
      _ hcommutator
  have hcomplete : MembranePairComplete support :=
    membranePairComplete_of_principalBracketPair_linearIndependent
      (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)
      support hmembrane hLI
  exact ⟨hpacket, hcomplete,
    by simpa using holographicLocality_choose_bound support Δ hcomplete hlocal⟩

end

end GaloisForLFunctions.HTGeometry
