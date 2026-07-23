import GaloisForLFunctions.HTGeometry.HolographicLocalityBound
import GaloisForLFunctions.HTGeometry.LinearWidthPrincipalSymbolCompletion
import GaloisForLFunctions.HTGeometry.QuadraticWidthPrincipalSymbolCompletion

/-!
# Principal-symbol detector compression–locality universality

The linear and quadratic detector completions can be applied to the same scalar pencil.  Above
three law directions the linear detector is strictly smaller, yet both completions have the same
exact dependence horizon, maximal exterior principal symbol, and the same representation-free
bounded-valence membrane obstruction.  Internal state compression therefore does not compress
the pair-covering cost visible at the membrane boundary.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-- Increasing law pairs are exactly increasing embeddings of `Fin 2`. -/
def quantumLawPairOrderEmbeddingEquiv {ι : Type*} [LinearOrder ι] :
    QuantumLawPair ι ≃ (Fin 2 ↪o ι) where
  toFun p :=
    OrderEmbedding.ofStrictMono ![p.lower, p.upper] (by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i
      exact p.isLt)
  invFun e := ⟨e 0, e 1, e.strictMono Fin.zero_lt_one⟩
  left_inv p := by
    cases p
    rfl
  right_inv e := by
    ext i
    fin_cases i <;> rfl

/-- Increasing law pairs are exactly two-element coordinate subsets. -/
def quantumLawPairPowersetEquiv {ι : Type*} [LinearOrder ι] :
    QuantumLawPair ι ≃ Set.powersetCard ι 2 :=
  quantumLawPairOrderEmbeddingEquiv.trans Set.powersetCard.ofFinEmbEquiv

noncomputable instance quantumLawPairFintype
    {ι : Type*} [Fintype ι] [LinearOrder ι] :
    Fintype (QuantumLawPair ι) :=
  Fintype.ofEquiv (Set.powersetCard ι 2)
    quantumLawPairPowersetEquiv.symm

/-- The number of increasing law pairs is `choose n 2`. -/
theorem quantumLawPair_card {ι : Type*} [Fintype ι] [LinearOrder ι] :
    Fintype.card (QuantumLawPair ι) =
      Nat.choose (Fintype.card ι) 2 := by
  rw [Fintype.card_congr quantumLawPairPowersetEquiv]
  exact completeBinaryMembrane_card

/-- The quadratic detector is the disjoint union of vacuum, single, and pair grades. -/
def quadraticQuantumDetectorIndexSumEquiv (n : ℕ) :
    QuadraticQuantumDetectorIndex n ≃
      (Unit ⊕ (Fin n ⊕ QuantumLawPair (Fin n))) where
  toFun
    | .root => Sum.inl ()
    | .single i => Sum.inr (Sum.inl i)
    | .pair p => Sum.inr (Sum.inr p)
  invFun
    | Sum.inl _ => .root
    | Sum.inr (Sum.inl i) => .single i
    | Sum.inr (Sum.inr p) => .pair p
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (_ | (i | p)) <;> rfl

noncomputable instance quadraticQuantumDetectorIndexFintype (n : ℕ) :
    Fintype (QuadraticQuantumDetectorIndex n) :=
  Fintype.ofEquiv (Unit ⊕ (Fin n ⊕ QuantumLawPair (Fin n)))
    (quadraticQuantumDetectorIndexSumEquiv n).symm

/-- Exact unclocked width of the three-grade quadratic detector. -/
theorem quadraticQuantumDetectorIndex_card (n : ℕ) :
    Fintype.card (QuadraticQuantumDetectorIndex n) =
      1 + n + Nat.choose n 2 := by
  rw [Fintype.card_congr (quadraticQuantumDetectorIndexSumEquiv n)]
  simp [quantumLawPair_card]
  omega

/-- Exact clocked coordinate width of the quadratic completion. -/
theorem quadraticPrincipalCompletionCoordinate_card {d n : ℕ} [NeZero d] :
    Fintype.card (QuadraticQuantumDetectorIndex n × ZMod d) =
      (1 + n + Nat.choose n 2) * d := by
  rw [Fintype.card_prod, quadraticQuantumDetectorIndex_card, ZMod.card]

/-- From four coordinates onward, the number of coordinate pairs strictly exceeds the number of
coordinates. -/
theorem lawCoordinate_lt_pairCount {n : ℕ} (hn : 4 ≤ n) :
    n < Nat.choose n 2 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _hn ih =>
      have hrec : Nat.choose (n + 1) 2 = n + Nat.choose n 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      rw [hrec]
      omega

/-- Above three law directions, the clocked linear detector is strictly smaller than the clocked
quadratic detector. -/
theorem linearPrincipalCompletionCoordinate_card_lt_quadratic
    {d n : ℕ} [NeZero d] [Fact (1 < d)] (hn : 4 ≤ n) :
    Fintype.card (LinearWidthDetectorIndex n × ZMod d) <
      Fintype.card (QuadraticQuantumDetectorIndex n × ZMod d) := by
  rw [linearPrincipalCompletionCoordinate_card,
    quadraticPrincipalCompletionCoordinate_card]
  have hpairs := lawCoordinate_lt_pairCount hn
  have hwidth : 2 * n + 1 < 1 + n + Nat.choose n 2 := by omega
  exact Nat.mul_lt_mul_of_pos_right hwidth (Nat.pos_of_ne_zero (NeZero.ne d))

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]
  {Hlin Hquad : Type*} [Fintype Hlin] [Fintype Hquad]

/-- **Principal-symbol detector compression–locality universality law.**  For the same scalar
pencil, the linear and quadratic completions have identical complete dependence horizons and
maximal exterior symbols.  In at least four law directions the linear realization is strictly
smaller, but every bounded-valence membrane presentation of either realization obeys the same
pair-covering lower bound. -/
theorem principalSymbolDetectorCompression_localityUniversality
    (hn : 4 ≤ n)
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id)
    (m : M) (hm : m ≠ 0)
    (supportLinear : Hlin → Finset (Fin n))
    (supportQuadratic : Hquad → Finset (Fin n))
    (Δlin Δquad : ℕ)
    (hmembraneLinear : MembraneLocalPrincipalBrackets
      (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)
      supportLinear)
    (hmembraneQuadratic : MembraneLocalPrincipalBrackets
      (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)
      supportQuadratic)
    (hlocalLinear : MembraneValenceAtMost supportLinear Δlin)
    (hlocalQuadratic : MembraneValenceAtMost supportQuadratic Δquad) :
    ({c : Fin n → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀ c)
          (linearPrincipalCompletionRoot (n := n) (d := d) m))} =
      {c : Fin n → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀ c)
          (quadraticPrincipalCompletionRoot (n := n) (d := d) m))}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀))) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀))) ∧
    Fintype.card (LinearWidthDetectorIndex n × ZMod d) <
      Fintype.card (QuadraticQuantumDetectorIndex n × ZMod d) ∧
    MembranePairComplete supportLinear ∧
    MembranePairComplete supportQuadratic ∧
    Nat.choose n 2 ≤ Fintype.card Hlin * Nat.choose Δlin 2 ∧
    Nat.choose n 2 ≤ Fintype.card Hquad * Nat.choose Δquad 2 := by
  have hlinear :=
    linearWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq hd A₀ F hA₀ m hm
  have hquadratic :=
    quadraticWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq A₀ F hA₀ m hm
  have hlinearLI :
      LinearIndependent K
        (principalBracketPair
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)) :=
    linearWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
      q hq A₀ m hm
  have hquadraticLI :
      LinearIndependent K
        (principalBracketPair
          (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)) :=
    quadraticWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
      q hq A₀ m hm
  have hcompleteLinear : MembranePairComplete supportLinear :=
    membranePairComplete_of_principalBracketPair_linearIndependent
      (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)
      supportLinear hmembraneLinear hlinearLI
  have hcompleteQuadratic : MembranePairComplete supportQuadratic :=
    membranePairComplete_of_principalBracketPair_linearIndependent
      (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)
      supportQuadratic hmembraneQuadratic hquadraticLI
  exact ⟨hlinear.1.trans hquadratic.1.symm,
    hlinear.2,
    hquadratic.2,
    linearPrincipalCompletionCoordinate_card_lt_quadratic hn,
    hcompleteLinear,
    hcompleteQuadratic,
    by simpa using
      holographicLocality_choose_bound
        supportLinear Δlin hcompleteLinear hlocalLinear,
    by simpa using
      holographicLocality_choose_bound
        supportQuadratic Δquad hcompleteQuadratic hlocalQuadratic⟩

end

end GaloisForLFunctions.HTGeometry
