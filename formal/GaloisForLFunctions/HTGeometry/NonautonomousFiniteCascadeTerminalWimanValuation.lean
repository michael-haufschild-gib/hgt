import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalValuationExtension
import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalStateEmbedding
import GaloisForLFunctions.HTGeometry.NonautonomousFinitePuiseuxValuationFlag

/-!
# Prescribed Wiman valuation on the literal terminal cascade component

The abstract rational state pair is identified exactly with the adjacent actual cascade states.
The prescribed two-stage Wiman root then receives the actual simple derivative component, and its
outer Laurent valuation prolongs to the full successor branch while every earlier state is a unit.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher HahnSeries Polynomial PowerSeries
open scoped LaurentSeries

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

theorem terminalEval_outer
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N
        (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
          Polynomial.X) =
      ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N 0,
        IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self 0)⟩ := by
  apply Subtype.ext
  rw [nonautonomousFiniteCascadeTerminalRationalStateEval_coe]
  change firstOrderRationalStateEval
      (nonautonomousFiniteCascadeLocalJet hfan (Fin.last N))
      (nonautonomousFiniteCascadeLocalStatePolynomialEval_injective
        hfan hall (Fin.last N))
      (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
        Polynomial.X) = _
  rw [firstOrderRationalStateEval_algebraMap]
  rw [← firstOrderStatePolynomialEquiv_X_zero]
  rw [firstOrderStatePolynomialEval_equiv]
  simp [nonautonomousFiniteCascadeLocalJet,
    nonautonomousFiniteCascadeTerminalStatePair]
  congr 1

theorem terminalEval_inner
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N
        (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
          (Polynomial.C Polynomial.X)) =
      ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N 1,
        IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self 1)⟩ := by
  apply Subtype.ext
  rw [nonautonomousFiniteCascadeTerminalRationalStateEval_coe]
  change firstOrderRationalStateEval
      (nonautonomousFiniteCascadeLocalJet hfan (Fin.last N))
      (nonautonomousFiniteCascadeLocalStatePolynomialEval_injective
        hfan hall (Fin.last N))
      (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
        (Polynomial.C Polynomial.X)) = _
  rw [firstOrderRationalStateEval_algebraMap]
  rw [← firstOrderStatePolynomialEquiv_X_one]
  rw [firstOrderStatePolynomialEval_equiv]
  simp [nonautonomousFiniteCascadeLocalJet,
    nonautonomousFiniteCascadeTerminalStatePair]
  congr 1

theorem terminalEval_fieldRange_eq_top
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    (nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N).fieldRange = ⊤ := by
  let e := nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N
  apply top_unique
  rintro ⟨y, hy⟩ _
  apply IntermediateField.adjoin_induction ℂ
    (p := fun y hy =>
      (⟨y, hy⟩ : NonautonomousFiniteCascadeTerminalPairField hfan N) ∈
        e.fieldRange) _ _ _ _ _ hy
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    fin_cases i
    · exact ⟨algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
          Polynomial.X, terminalEval_outer hfan hall N⟩
    · exact ⟨algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
          (Polynomial.C Polynomial.X), terminalEval_inner hfan hall N⟩
  · intro c
    exact e.fieldRange.algebraMap_mem c
  · intro x y _ _ hx hy
    exact e.fieldRange.add_mem hx hy
  · intro x _ hx
    exact e.fieldRange.inv_mem hx
  · intro x y _ _ hx hy
    exact e.fieldRange.mul_mem hx hy

theorem terminalEval_surjective
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    Function.Surjective
      (nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N) := by
  intro y
  have hy : y ∈
      (nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N).fieldRange := by
    rw [terminalEval_fieldRange_eq_top hfan hall N]
    trivial
  exact hy

noncomputable def terminalEvalEquiv
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    FirstOrderRationalStateField ≃ₐ[ℂ]
      NonautonomousFiniteCascadeTerminalPairField hfan N :=
  AlgEquiv.ofBijective
    (nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N)
    ⟨(nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N).injective,
      terminalEval_surjective hfan hall N⟩

theorem terminalVelocity_wimanRoot_pair
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    (((firstOrderDerivativePolynomial
          (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).P).map
        (nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N).toRingHom).map
      (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeBranchField hfan (N + 1)))).IsRoot
      (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N) := by
  let k : Fin (N + 1) := Fin.last N
  let p := firstOrderDerivativePolynomial
    (nonautonomousFiniteCascadeWimanData hall h1 k).P
  let e := nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k
  let eL := nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N
  let v := nonautonomousFiniteCascadeTerminalVelocitySucc hfan N
  have hroot :=
    nonautonomousFiniteCascadeVelocity_chosen_component_root hfan hall h1 k
  have hcomp :
      (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeBranchField hfan (N + 1))).comp
          eL.toRingHom = e.toRingHom := by
    apply DFunLike.ext _ _
    intro a
    exact nonautonomousFiniteCascadeTerminalRationalStateEval_coe hfan hall N a
  change (p.map e.toRingHom).IsRoot
    (nonautonomousFiniteCascadeLocalJet hfan k 2) at hroot
  have hv : nonautonomousFiniteCascadeLocalJet hfan k 2 = v := by
    change Fin.cases
        (nonautonomousFiniteCascadeStateInBranchField hfan (N + 1) k.castSucc)
        (fun i : Fin 2 => Fin.cases
          (nonautonomousFiniteCascadeStateInBranchField hfan (N + 1) k.succ)
          (fun _ : Fin 1 =>
            nonautonomousFiniteCascadeVelocityInBranchField hfan k.rev) i)
        (2 : Fin 3) =
      nonautonomousFiniteCascadeVelocityInBranchField hfan 0
    rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) by rfl, Fin.cases_succ]
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl, Fin.cases_succ]
    congr 1
    exact Fin.ext (by simp [k])
  rw [Polynomial.map_map, hcomp]
  rw [hv] at hroot
  exact hroot

theorem terminalVelocity_minpoly_associated_wiman_pair
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    Associated
      (minpoly (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N))
      ((firstOrderDerivativePolynomial
          (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).P).map
        (nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N).toRingHom) := by
  let E := terminalEvalEquiv hfan hall N
  let data := nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)
  let p := firstOrderDerivativePolynomial data.P
  let v := nonautonomousFiniteCascadeTerminalVelocitySucc hfan N
  have hp : Irreducible
      (p.map (nonautonomousFiniteCascadeTerminalRationalStateEval
        hfan hall N).toRingHom) := by
    have hp0 : Irreducible p := firstOrderDerivativePolynomial_irreducible data
    have hmapped := hp0.map (Polynomial.mapEquiv E.toRingEquiv)
    change Irreducible (p.map E.toRingEquiv.toRingHom) at hmapped
    convert hmapped using 1
    congr 1
  have hvAlg : IsAlgebraic
      (NonautonomousFiniteCascadeTerminalPairField hfan N) v :=
    nonautonomousFiniteCascadeTerminalVelocity_isAlgebraic_pairField
      hfan hall N h1
  have hvInt : IsIntegral
      (NonautonomousFiniteCascadeTerminalPairField hfan N) v :=
    isAlgebraic_iff_isIntegral.mp hvAlg
  have hdvd : minpoly (NonautonomousFiniteCascadeTerminalPairField hfan N) v ∣
      p.map (nonautonomousFiniteCascadeTerminalRationalStateEval
        hfan hall N).toRingHom := by
    apply minpoly.dvd (NonautonomousFiniteCascadeTerminalPairField hfan N)
    rw [Polynomial.aeval_def]
    simpa [Polynomial.eval_map] using
      (terminalVelocity_wimanRoot_pair hfan hall N h1)
  exact (minpoly.irreducible hvInt).associated_of_dvd hp hdvd

/-- Any root of the chosen Wiman polynomial over an arbitrary exact state realization receives
the literal actual terminal derivative component. -/
theorem exists_terminalComponentRingHom_of_wimanRoot
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    {M : Type*} [Field M] [Algebra ℂ M]
    (rse : FirstOrderRationalStateField →ₐ[ℂ] M) (W : M)
    (hW : ((firstOrderDerivativePolynomial
        (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).P).map
      rse.toRingHom).IsRoot W) :
    ∃ φ : NonautonomousFiniteCascadeTerminalComponentField hfan N →+* M,
      φ (IntermediateField.AdjoinSimple.gen
          (NonautonomousFiniteCascadeTerminalPairField hfan N)
          (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N)) = W ∧
      ∀ b : NonautonomousFiniteCascadeTerminalPairField hfan N,
        φ (algebraMap
          (NonautonomousFiniteCascadeTerminalPairField hfan N)
          (NonautonomousFiniteCascadeTerminalComponentField hfan N) b) =
        rse ((terminalEvalEquiv hfan hall N).symm b) := by
  let E := terminalEvalEquiv hfan hall N
  let ePair : NonautonomousFiniteCascadeTerminalPairField hfan N →ₐ[ℂ] M :=
    rse.comp E.symm.toAlgHom
  letI : Algebra (NonautonomousFiniteCascadeTerminalPairField hfan N) M :=
    ePair.toAlgebra
  let v := nonautonomousFiniteCascadeTerminalVelocitySucc hfan N
  let p := firstOrderDerivativePolynomial
    (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).P
  have hcomp : ePair.toRingHom.comp
      (nonautonomousFiniteCascadeTerminalRationalStateEval hfan hall N).toRingHom =
      rse.toRingHom := by
    apply DFunLike.ext _ _
    intro a
    simp [ePair, E, terminalEvalEquiv]
  have hpairRoot :
      ((p.map
        (nonautonomousFiniteCascadeTerminalRationalStateEval
          hfan hall N).toRingHom).map ePair.toRingHom).IsRoot W := by
    rw [Polynomial.map_map, hcomp]
    exact hW
  have hminRoot : Polynomial.eval₂ (algebraMap
      (NonautonomousFiniteCascadeTerminalPairField hfan N) M) W
      (minpoly (NonautonomousFiniteCascadeTerminalPairField hfan N) v) = 0 :=
    minpoly_isRoot_of_associated_mapped_isRoot v
      (terminalVelocity_minpoly_associated_wiman_pair hfan hall N h1) W hpairRoot
  have hvInt : IsIntegral
      (NonautonomousFiniteCascadeTerminalPairField hfan N) v :=
    isAlgebraic_iff_isIntegral.mp
      (nonautonomousFiniteCascadeTerminalVelocity_isAlgebraic_pairField
        hfan hall N h1)
  obtain ⟨φ, hφ⟩ := exists_adjoinSimple_algHom_of_minpoly_root
    v hvInt W hminRoot
  refine ⟨φ.toRingHom, hφ, ?_⟩
  intro b
  exact φ.commutes b

/-- Outer Laurent valuation ring, with the full coefficient field valuation-trivial. -/
noncomputable def laurentSeriesValuationSubring
    (K : Type*) [Field K] : ValuationSubring (LaurentSeries K) :=
  (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))).valuationSubring

theorem mem_laurentSeriesValuationSubring_iff
    {K : Type*} [Field K] (x : LaurentSeries K) :
    x ∈ laurentSeriesValuationSubring K ↔
      (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))) x ≤ 1 := by
  exact Valuation.mem_integer_iff _ _

/-- The exact two-stage Wiman place of the literal terminal component prolongs to the whole
successor branch while every earlier state remains a valuation unit. -/
theorem exists_nonautonomousFiniteCascadeTerminalWimanValuation
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∃ (M a q Nram : ℕ) (_hNram : Nram ≠ 0) (z₀ : PowerSeries ℂ)
        (R : ℕ) (_hR : R ≠ 0)
        (z : PowerSeries FirstOrderTerminalCoefficientField) (_hq : q ≠ 0)
        (φ : NonautonomousFiniteCascadeTerminalComponentField hfan N →+*
          FirstOrderTerminalLaurentField)
        (B : ValuationSubring
          (NonautonomousFiniteCascadeBranchField hfan (N + 1))),
      (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).slope =
        ((M : ℚ) - (a : ℚ)) / q ∧
      PowerSeries.constantCoeff z₀ =
        (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).root ∧
      PowerSeries.constantCoeff z =
        algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
          (HahnSeries.single (-((Nram * M : ℕ) : ℤ)) (1 : ℂ) *
            algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
              ((PowerSeries.X : PowerSeries ℂ) ^ (Nram * a) * z₀)) ∧
      let U := HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ)
      let V := HahnSeries.single (-((R : ℕ) : ℤ))
        (1 : FirstOrderTerminalCoefficientField)
      let W := HahnSeries.single (-((R : ℕ) : ℤ))
          (1 : FirstOrderTerminalCoefficientField) *
        algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
          FirstOrderTerminalLaurentField z
      letI : Algebra ℂ FirstOrderTerminalLaurentField :=
        firstOrderTerminalComplexMap.toAlgebra
      let hinj : Function.Injective
          (firstOrderStatePolynomialEval (firstOrderTerminalJet U V W)) :=
        firstOrderStatePolynomialEval_terminal_injective
          (-((Nram * q : ℕ) : ℤ)) (-((R : ℕ) : ℤ))
          (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (mul_ne_zero _hNram _hq)))
          (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr _hR)) W
      φ (IntermediateField.AdjoinSimple.gen
          (NonautonomousFiniteCascadeTerminalPairField hfan N)
          (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N)) = W ∧
      (∀ b : NonautonomousFiniteCascadeTerminalPairField hfan N,
        φ (algebraMap
          (NonautonomousFiniteCascadeTerminalPairField hfan N)
          (NonautonomousFiniteCascadeTerminalComponentField hfan N) b) =
        firstOrderRationalStateEval (firstOrderTerminalJet U V W) hinj
          ((terminalEvalEquiv hfan hall N).symm b)) ∧
      B.comap (algebraMap
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        (NonautonomousFiniteCascadeBranchField hfan (N + 1))) =
          (laurentSeriesValuationSubring
            FirstOrderTerminalCoefficientField).comap φ ∧
      ∀ i, nonautonomousFiniteCascadeTerminalStateTail hfan N i ∈ B ∧
        (nonautonomousFiniteCascadeTerminalStateTail hfan N i)⁻¹ ∈ B := by
  let data := nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)
  obtain ⟨M, a, q, Nram, hNram, z₀, R, hR, z, hq,
      hslope, hz₀, hz, hroot⟩ :=
    exists_entireFirstOrderWiman_rationalDerivativePuiseuxRoot data
  let U := HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ)
  let V := HahnSeries.single (-((R : ℕ) : ℤ))
    (1 : FirstOrderTerminalCoefficientField)
  let W := HahnSeries.single (-((R : ℕ) : ℤ))
      (1 : FirstOrderTerminalCoefficientField) *
    algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField z
  letI : Algebra ℂ FirstOrderTerminalLaurentField :=
    firstOrderTerminalComplexMap.toAlgebra
  let hinj : Function.Injective
      (firstOrderStatePolynomialEval (firstOrderTerminalJet U V W)) :=
    firstOrderStatePolynomialEval_terminal_injective
      (-((Nram * q : ℕ) : ℤ)) (-((R : ℕ) : ℤ))
      (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (mul_ne_zero hNram hq)))
      (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr hR)) W
  let rse := firstOrderRationalStateEval (firstOrderTerminalJet U V W) hinj
  obtain ⟨φ, hφgen, hφbase⟩ :=
    exists_terminalComponentRingHom_of_wimanRoot
      hfan hall N h1 rse W hroot
  obtain ⟨B, hBcomap, hBtail⟩ :=
    exists_nonautonomousFiniteCascadeTerminalComponentValuation_extension
      hfan hall N h1
        ((laurentSeriesValuationSubring
          FirstOrderTerminalCoefficientField).comap φ)
  refine ⟨M, a, q, Nram, hNram, z₀, R, hR, z, hq, φ, B,
    hslope, hz₀, hz, ?_⟩
  dsimp only
  exact ⟨hφgen, hφbase, hBcomap, hBtail⟩

end

end GaloisForLFunctions.HTGeometry
