import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalResidue
import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalBiHahn
import GaloisForLFunctions.HTGeometry.LogCoordinateDerivationTransport
import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalLowerRetention

/-!
# Exact terminal Wiman residue coefficient in the full actual branch

The prescribed outer Wiman unit is first a residue class of the literal terminal derivative
component.  Exact contraction transports that same class into the residue field of the complete
successor branch, while the complete lower branch remains faithfully embedded.  Its other exact
transport is the literal nonzero Puiseux coefficient in the inner Laurent field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher HahnSeries Polynomial PowerSeries
open scoped LaurentSeries

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

local instance (priority := high) terminalResidueCoefficientComplexAlgebra :
    Algebra ℂ FirstOrderTerminalLaurentField :=
  firstOrderTerminalComplexMap.toAlgebra

local instance (priority := high) terminalResidueCoefficientInnerHahnComplexAlgebra :
    Algebra ℂ FirstOrderTerminalInnerHahnField :=
  firstOrderTerminalInnerHahnComplexAlgebra

local instance (priority := high) terminalResidueCoefficientBiHahnCoefficientComplexAlgebra :
    Algebra ℂ FirstOrderTerminalBiHahnCoefficientField :=
  firstOrderTerminalBiHahnCoefficientComplexAlgebra

local instance (priority := high) terminalResidueCoefficientBiHahnComplexAlgebra :
    Algebra ℂ FirstOrderTerminalBiHahnField :=
  firstOrderTerminalBiHahnComplexAlgebra

/-- The faithful two-level Hahn transport as a complex-algebra embedding for the terminal source
algebra used in this module. -/
private noncomputable def terminalResidueCoefficientBiHahnAlgHom :
    FirstOrderTerminalLaurentField →ₐ[ℂ] FirstOrderTerminalBiHahnField :=
  { firstOrderTerminalBiHahnEmbedding with
    commutes' := by
      intro c
      unfold firstOrderTerminalBiHahnEmbedding
      change laurentToHahn
        (firstOrderTerminalLaurentBaseChange (laurentToHahn (k := ℂ))
          (firstOrderTerminalComplexMap c)) = _
      change laurentToHahn
        (firstOrderTerminalLaurentBaseChange (laurentToHahn (k := ℂ))
          (firstOrderTerminalOuterCoefficientMap
            (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
              (algebraMap ℂ (LaurentSeries ℂ) c)))) = _
      rw [firstOrderTerminalOuterCoefficientMap,
        firstOrderTerminalLaurentBaseChange_algebraMap,
        firstOrderTerminalCoefficientBaseChange_algebraMap,
        laurentToHahn_algebraMap, laurentToHahn_algebraMap]
      change HahnSeries.ofPowerSeries ℚ FirstOrderTerminalBiHahnCoefficientField
          (PowerSeries.C _) = HahnSeries.C _
      rw [HahnSeries.ofPowerSeries_C]
      congr 1
      change algebraMap FirstOrderTerminalInnerHahnField
          FirstOrderTerminalBiHahnCoefficientField
          (HahnSeries.ofPowerSeries ℚ ℂ (PowerSeries.C c)) =
        algebraMap FirstOrderTerminalInnerHahnField
          FirstOrderTerminalBiHahnCoefficientField (HahnSeries.C c)
      rw [HahnSeries.ofPowerSeries_C] }

/-- A source element mapped to a negative inner Laurent monomial becomes a genuine pole in the
pulled-back inner residue valuation. -/
theorem firstOrderTerminalPulledInnerResidue_inputPole
    {E : Type*} [Field E] (phi : E →+* FirstOrderTerminalLaurentField)
    (u : E) (R : ℕ) (hR : R ≠ 0)
    (hu : phi u =
      algebraMap FirstOrderTerminalCoefficientField
        FirstOrderTerminalLaurentField
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
          (HahnSeries.single (-((R : ℕ) : ℤ)) (1 : ℂ))))
    (huA : u ∈ (laurentSeriesValuationSubring
      FirstOrderTerminalCoefficientField).comap phi) :
    IsLocalRing.residue
        ((laurentSeriesValuationSubring
          FirstOrderTerminalCoefficientField).comap phi)
        (⟨u, huA⟩ : (laurentSeriesValuationSubring
          FirstOrderTerminalCoefficientField).comap phi) ∉
      firstOrderTerminalPulledInnerResidueValuationSubring phi := by
  rw [mem_firstOrderTerminalPulledInnerResidueValuationSubring_iff,
    firstOrderTerminalCoefficientResidueEmbedding_residue_algebraMap
      phi u _ hu huA,
    algebraMap_mem_firstOrderTerminalInnerValuationSubring_iff]
  exact hahnSingle_negative_not_mem_laurentSeriesValuationSubring R hR

/-- The residue of the literal normalized terminal velocity has two exact faithful images: its
prescribed nonzero Wiman coefficient and its residue in the complete actual successor branch.
The complete lower actual branch is simultaneously retained in that successor residue field. -/
theorem exists_nonautonomousFiniteCascadeTerminal_normalizedVelocity_residueCoefficient
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∃ (M a q Nram : ℕ) (_hNram : Nram ≠ 0) (z₀ : PowerSeries ℂ)
      (R : ℕ) (_hR : R ≠ 0)
      (z : PowerSeries FirstOrderTerminalCoefficientField) (_hq : q ≠ 0)
      (phi : NonautonomousFiniteCascadeTerminalComponentField hfan N →+*
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
      a < M + q ∧
      hahnGrade (Int.castAddHom ℂ)
          (HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ) *
            (HahnSeries.single (-((Nram * M : ℕ) : ℤ)) (1 : ℂ) *
              algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
                ((PowerSeries.X : PowerSeries ℂ) ^ (Nram * a) * z₀))) ≠ 0 ∧
      firstOrderTerminalBiHahnInnerEuler
          (firstOrderTerminalBiHahnEmbedding
            (firstOrderTerminalOuterCoefficientMap
              (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
                (HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ) *
                  (HahnSeries.single (-((Nram * M : ℕ) : ℤ)) (1 : ℂ) *
                    algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
                      ((PowerSeries.X : PowerSeries ℂ) ^ (Nram * a) * z₀)))))) ≠ 0 ∧
      let A := (laurentSeriesValuationSubring
        FirstOrderTerminalCoefficientField).comap phi
      let g := algebraMap
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        (NonautonomousFiniteCascadeBranchField hfan (N + 1))
      let u : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
        algebraMap (NonautonomousFiniteCascadeTerminalPairField hfan N)
          (NonautonomousFiniteCascadeTerminalComponentField hfan N)
          ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N 0,
            IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self 0)⟩
      let y : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
        algebraMap (NonautonomousFiniteCascadeTerminalPairField hfan N)
          (NonautonomousFiniteCascadeTerminalComponentField hfan N)
          ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N 1,
            IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self 1)⟩
      let v : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
        IntermediateField.AdjoinSimple.gen
          (NonautonomousFiniteCascadeTerminalPairField hfan N)
          (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N)
      let x := v / y
      ∃ (hB : B.comap g = A)
        (hstate : ∀ s : NonautonomousRamifiedCascadeStateField hfan N,
          nonautonomousFiniteCascadeLowerStateInclusionSucc hfan N s ∈ B)
        (hxA : x ∈ A) (hxB : g x ∈ B)
        (huA : u ∈ A) (huB : g u ∈ B)
        (C : ValuationSubring (IsLocalRing.ResidueField B))
        (_hC : C.comap (valuationSubringResidueMapOfComapEq g A B hB) =
          firstOrderTerminalPulledInnerResidueValuationSubring phi),
        PowerSeries.constantCoeff z ≠ 0 ∧
        firstOrderTerminalCoefficientResidueEmbedding phi
            (IsLocalRing.residue A (⟨u, huA⟩ : A)) =
          algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
            (HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ)) ∧
        firstOrderTerminalCoefficientResidueEmbedding phi
            (IsLocalRing.residue A (⟨x, hxA⟩ : A)) =
          PowerSeries.constantCoeff z ∧
        ABHN.laurentSeriesResidueFieldEquiv FirstOrderTerminalCoefficientField
            (valuationSubringResidueMapOfComapEq phi A
              (laurentSeriesValuationSubring FirstOrderTerminalCoefficientField) rfl
              (IsLocalRing.residue A (⟨x, hxA⟩ : A))) =
          PowerSeries.constantCoeff z ∧
        valuationSubringResidueMapOfComapEq g A B
            hB
            (IsLocalRing.residue A (⟨x, hxA⟩ : A)) =
          IsLocalRing.residue B (⟨g x, hxB⟩ : B) ∧
        Function.Injective
          (nonautonomousFiniteCascadeLowerBranchResidueEmbedding
            hfan hall (fun k hk => h1 k (by omega)) B
              hstate) ∧
        IsLocalRing.residue B (⟨g u, huB⟩ : B) ∉ C ∧
        firstOrderTerminalBiHahnInnerEuler
          (firstOrderTerminalBiHahnEmbedding (phi (u * x))) ≠ 0 ∧
        ∃ D : Derivation ℂ
            (NonautonomousFiniteCascadeTerminalComponentField hfan N)
            (NonautonomousFiniteCascadeTerminalComponentField hfan N),
          D u = algebraMap ℂ
              (NonautonomousFiniteCascadeTerminalComponentField hfan N)
              ((-((Nram * q : ℕ) : ℤ) : ℂ)) * u ∧
          D y = 0 ∧
          (∀ w : NonautonomousFiniteCascadeTerminalComponentField hfan N,
            firstOrderTerminalBiHahnEmbedding (phi (D w)) =
              firstOrderTerminalBiHahnInnerEuler
                (firstOrderTerminalBiHahnEmbedding (phi w))) ∧
          D (u * x) ≠ 0 := by
  obtain ⟨M, a, q, Nram, hNram, z₀, R, hR, z, hq, phi, B₀,
      hslope, hz₀, hz, hdata⟩ :=
    exists_nonautonomousFiniteCascadeTerminalWimanValuation hfan hall N h1
  dsimp only at hdata
  rcases hdata with ⟨hphiGen, hphiBase, hB₀, htail⟩
  let U := HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ)
  let V := HahnSeries.single (-((R : ℕ) : ℤ))
    (1 : FirstOrderTerminalCoefficientField)
  let W := HahnSeries.single (-((R : ℕ) : ℤ))
      (1 : FirstOrderTerminalCoefficientField) *
    algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField z
  let hinj : Function.Injective
      (firstOrderStatePolynomialEval (firstOrderTerminalJet U V W)) :=
    firstOrderStatePolynomialEval_terminal_injective
      (-((Nram * q : ℕ) : ℤ)) (-((R : ℕ) : ℤ))
      (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (mul_ne_zero hNram hq)))
      (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr hR)) W
  let A := (laurentSeriesValuationSubring
    FirstOrderTerminalCoefficientField).comap phi
  let g := algebraMap
    (NonautonomousFiniteCascadeTerminalComponentField hfan N)
    (NonautonomousFiniteCascadeBranchField hfan (N + 1))
  let b₀ : NonautonomousFiniteCascadeTerminalPairField hfan N :=
    ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N 0,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self 0)⟩
  let u : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
    algebraMap (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) b₀
  let b₁ : NonautonomousFiniteCascadeTerminalPairField hfan N :=
    ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N 1,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self 1)⟩
  let y : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
    algebraMap (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) b₁
  let v : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
    IntermediateField.AdjoinSimple.gen
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N)
  let x := v / y
  have hphiU : phi u =
      algebraMap FirstOrderTerminalCoefficientField
        FirstOrderTerminalLaurentField
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U) := by
    change phi (algebraMap
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) b₀) = _
    rw [hphiBase]
    exact firstOrderTerminalRationalStateEval_pair_zero
      hfan hall N U V W hinj
  have hphiY : phi y = V := by
    change phi (algebraMap
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) b₁) = V
    rw [hphiBase]
    exact firstOrderTerminalRationalStateEval_pair_one
      hfan hall N U V W hinj
  have hphiX : phi x =
      algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
        FirstOrderTerminalLaurentField z := by
    change phi (v / y) = _
    rw [map_div₀ phi, show phi v = W from hphiGen, hphiY,
      terminalWiman_W_div_V R z]
  have hphiC (c : ℂ) :
      phi (algebraMap ℂ
        (NonautonomousFiniteCascadeTerminalComponentField hfan N) c) =
        algebraMap ℂ FirstOrderTerminalLaurentField c := by
    change phi (algebraMap
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N)
      (algebraMap ℂ (NonautonomousFiniteCascadeTerminalPairField hfan N) c)) = _
    rw [hphiBase]
    simp
  let pairCoordinate : Fin 2 →
      NonautonomousFiniteCascadeTerminalPairField hfan N := fun i =>
    ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N i,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩
  let pairIndex : Fin 2 → Fin (N + 2) := fun i => ⟨N + i, by omega⟩
  have hpairIndex : Function.Injective pairIndex := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    simp only [pairIndex] at hv
    omega
  have hpairAmbient : AlgebraicIndependent ℂ
      (nonautonomousFiniteCascadeTerminalStatePair hfan N) := by
    have hfull :=
      algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField
        hfan hall (N + 1)
    have hsub := hfull.comp pairIndex hpairIndex
    convert hsub using 1
    funext i
    rfl
  have hpairAI : AlgebraicIndependent ℂ pairCoordinate := by
    let incl : NonautonomousFiniteCascadeTerminalPairField hfan N →ₐ[ℂ]
        NonautonomousFiniteCascadeBranchField hfan (N + 1) :=
      IsScalarTower.toAlgHom ℂ
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeBranchField hfan (N + 1))
    apply AlgebraicIndependent.of_comp incl
    convert hpairAmbient using 1
    funext i
    rfl
  have hpairTop : IntermediateField.adjoin ℂ (Set.range pairCoordinate) = ⊤ := by
    simpa [pairCoordinate] using
      (adjoin_range_lift_eq_top
        (nonautonomousFiniteCascadeTerminalStatePair hfan N)
        (nonautonomousFiniteCascadeTerminalStatePair hfan N) rfl)
  have hzNe : PowerSeries.constantCoeff z ≠ 0 :=
    terminalWimanPowerSeries_constantCoeff_ne_zero
      M a Nram z₀ z
      (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).root
      (nonautonomousFiniteCascadeWimanData_root_ne_zero hall h1 (Fin.last N))
      hz₀ hz
  have hchargeNat : a < M + q := by
    have hqpos : (0 : ℚ) < q := by
      exact_mod_cast (Nat.pos_of_ne_zero hq)
    have hchargeReal :=
      nonautonomousFiniteCascadeWimanData_charge_pos hall h1 (Fin.last N)
    have hchargeRat : (0 : ℚ) <
        (nonautonomousFiniteCascadeWimanData hall h1 (Fin.last N)).slope + 1 := by
      exact_mod_cast hchargeReal
    rw [hslope] at hchargeRat
    have hmul : (0 : ℚ) <
        (((M : ℚ) - (a : ℚ)) / q + 1) * q :=
      mul_pos hchargeRat hqpos
    field_simp [hq] at hmul
    have hcast : (a : ℚ) < M + q := by linarith
    exact_mod_cast hcast
  have hterminalCharge :
      hahnGrade (Int.castAddHom ℂ)
          (HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ) *
            (HahnSeries.single (-((Nram * M : ℕ) : ℤ)) (1 : ℂ) *
              algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
                ((PowerSeries.X : PowerSeries ℂ) ^ (Nram * a) * z₀))) ≠ 0 := by
    apply hahnGrade_terminalWimanChargedCoefficient_ne_zero
      M a q Nram hNram hchargeNat z₀
    rw [hz₀]
    exact nonautonomousFiniteCascadeWimanData_root_ne_zero hall h1 (Fin.last N)
  have hterminalBiHahnCharge :
      firstOrderTerminalBiHahnInnerEuler
          (firstOrderTerminalBiHahnEmbedding
            (firstOrderTerminalOuterCoefficientMap
              (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
                (HahnSeries.single (-((Nram * q : ℕ) : ℤ)) (1 : ℂ) *
                  (HahnSeries.single (-((Nram * M : ℕ) : ℤ)) (1 : ℂ) *
                    algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
                      ((PowerSeries.X : PowerSeries ℂ) ^ (Nram * a) * z₀)))))) ≠ 0 := by
    apply firstOrderTerminalBiHahnInnerEuler_charged_ne_zero
      M a q Nram hNram hchargeNat z₀
    rw [hz₀]
    exact nonautonomousFiniteCascadeWimanData_root_ne_zero hall h1 (Fin.last N)
  have hterminalActualBiHahnCharge :
      firstOrderTerminalBiHahnInnerEuler
        (firstOrderTerminalBiHahnEmbedding (phi (u * x))) ≠ 0 := by
    rw [map_mul, hphiU, hphiX]
    apply firstOrderTerminalBiHahnInnerEuler_outer_mul_coe_ne_zero
    rw [hz, ← map_mul]
    exact hterminalBiHahnCharge
  let phiAlg : NonautonomousFiniteCascadeTerminalComponentField hfan N →ₐ[ℂ]
      FirstOrderTerminalLaurentField :=
    { phi with commutes' := hphiC }
  let rho : NonautonomousFiniteCascadeTerminalComponentField hfan N →ₐ[ℂ]
      FirstOrderTerminalBiHahnField :=
    terminalResidueCoefficientBiHahnAlgHom.comp phiAlg
  let cPair : NonautonomousFiniteCascadeTerminalPairField hfan N :=
    algebraMap ℂ (NonautonomousFiniteCascadeTerminalPairField hfan N)
      ((-((Nram * q : ℕ) : ℤ) : ℂ))
  have hinnerU : firstOrderTerminalBiHahnInnerEuler (rho u) =
      rho (algebraMap (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N) cPair * u) := by
    rw [show rho u = firstOrderTerminalBiHahnEmbedding (phi u) by rfl, hphiU]
    change firstOrderTerminalBiHahnInnerEuler
        (firstOrderTerminalBiHahnEmbedding
          (firstOrderTerminalOuterCoefficientMap
            (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U))) = _
    dsimp only [U]
    rw [firstOrderTerminalBiHahnInnerEuler_inner_single]
    rw [map_mul]
    rw [show rho (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N) cPair) =
          firstOrderTerminalBiHahnEmbedding
            (phi (algebraMap
              (NonautonomousFiniteCascadeTerminalPairField hfan N)
              (NonautonomousFiniteCascadeTerminalComponentField hfan N) cPair)) by rfl,
      show rho u = firstOrderTerminalBiHahnEmbedding (phi u) by rfl]
    rw [show phi (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N) cPair) =
          algebraMap ℂ FirstOrderTerminalLaurentField
            ((-((Nram * q : ℕ) : ℤ) : ℂ)) by
      rw [hphiBase]
      simp [cPair]]
    rw [hphiU]
    rw [← map_mul]
    apply congrArg firstOrderTerminalBiHahnEmbedding
    rw [show algebraMap ℂ FirstOrderTerminalLaurentField
        ((-((Nram * q : ℕ) : ℤ) : ℂ)) =
      algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
          (algebraMap ℂ (LaurentSeries ℂ)
            ((-((Nram * q : ℕ) : ℤ) : ℂ)))) by rfl]
    rw [← map_mul, ← map_mul]
    congr 2
    dsimp only [U]
    rw [LaurentSeries.algebraMap_apply]
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have hinnerY : firstOrderTerminalBiHahnInnerEuler (rho y) = 0 := by
    rw [show rho y = firstOrderTerminalBiHahnEmbedding (phi y) by rfl, hphiY]
    exact firstOrderTerminalBiHahnInnerEuler_outer_single_one _
  letI : Algebra.IsAlgebraic
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) :=
    nonautonomousFiniteCascadeTerminalComponent_isAlgebraic hfan hall N h1
  obtain ⟨D, hDu, hDy, hDtransport⟩ :=
    exists_logCoordinateDerivation_intertwining_of_isAlgebraic_tower_coefficient
      pairCoordinate hpairAI hpairTop rho firstOrderTerminalBiHahnInnerEuler cPair
      (by
        change firstOrderTerminalBiHahnInnerEuler (rho u) =
          rho (algebraMap (NonautonomousFiniteCascadeTerminalPairField hfan N)
            (NonautonomousFiniteCascadeTerminalComponentField hfan N) cPair * u)
        exact hinnerU)
      (by
        change firstOrderTerminalBiHahnInnerEuler (rho y) = 0
        exact hinnerY)
  have hDu' : D u = algebraMap ℂ
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        ((-((Nram * q : ℕ) : ℤ) : ℂ)) * u := by
    change D (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        (pairCoordinate 0)) = _ at hDu
    rw [hDu]
    change algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N) cPair * u = _
    rw [show algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N) cPair =
          algebraMap ℂ
            (NonautonomousFiniteCascadeTerminalComponentField hfan N)
            ((-((Nram * q : ℕ) : ℤ) : ℂ)) by
      simp [cPair]]
  have hDy' : D y = 0 := by
    change D (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        (pairCoordinate 1)) = 0 at hDy
    exact hDy
  have hDtransport' (w : NonautonomousFiniteCascadeTerminalComponentField hfan N) :
      firstOrderTerminalBiHahnEmbedding (phi (D w)) =
        firstOrderTerminalBiHahnInnerEuler
          (firstOrderTerminalBiHahnEmbedding (phi w)) := by
    exact hDtransport w
  have hDnonzero : D (u * x) ≠ 0 := by
    intro hzero
    apply hterminalActualBiHahnCharge
    rw [← hDtransport' (u * x), hzero]
    have hrhoZero := map_zero rho
    exact hrhoZero
  have hAtriv : A.comap
      (IntermediateField.adjoin ℂ
        ({terminalLeadingStateInComponent hfan N} :
          Set (NonautonomousFiniteCascadeTerminalComponentField hfan N))).val.toRingHom = ⊤ :=
    terminalWimanComponentValuation_trivial_leadingState
      hfan hall N U V W hinj phi hphiBase
  obtain ⟨B, hB, hstate⟩ :=
    exists_nonautonomousFiniteCascadeTerminalComponentValuation_extension_lowerState
      hfan hall N h1 A hAtriv
  have hxA : x ∈ A := by
    change phi x ∈ laurentSeriesValuationSubring FirstOrderTerminalCoefficientField
    rw [hphiX]
    exact coe_terminalWimanPowerSeries_mem z hzNe
  have hxB : g x ∈ B := by
    change x ∈ B.comap g
    rw [hB]
    exact hxA
  have huA : u ∈ A := by
    change phi u ∈ laurentSeriesValuationSubring FirstOrderTerminalCoefficientField
    rw [hphiU]
    exact algebraMap_mem_laurentSeriesValuationSubring _
  have huB : g u ∈ B := by
    change u ∈ B.comap g
    rw [hB]
    exact huA
  obtain ⟨C, hC⟩ :=
    exists_firstOrderTerminalPulledInnerResidueValuation_extension
      phi g B hB
  have huPoleA : IsLocalRing.residue A (⟨u, huA⟩ : A) ∉
      firstOrderTerminalPulledInnerResidueValuationSubring phi :=
    firstOrderTerminalPulledInnerResidue_inputPole
      phi u (Nram * q) (mul_ne_zero hNram hq) hphiU huA
  have huPoleB : IsLocalRing.residue B (⟨g u, huB⟩ : B) ∉ C := by
    intro huC
    apply huPoleA
    have himage : valuationSubringResidueMapOfComapEq g A B hB
        (IsLocalRing.residue A (⟨u, huA⟩ : A)) ∈ C := by
      rw [valuationSubringResidueMapOfComapEq_residue]
      convert huC
    have hsource : IsLocalRing.residue A (⟨u, huA⟩ : A) ∈
        C.comap (valuationSubringResidueMapOfComapEq g A B hB) :=
      himage
    rw [hC] at hsource
    exact hsource
  refine ⟨M, a, q, Nram, hNram, z₀, R, hR, z, hq, phi, B,
    hslope, hz₀, hz, hchargeNat, hterminalCharge, hterminalBiHahnCharge, ?_⟩
  dsimp only
  refine ⟨hB, hstate, hxA, hxB, huA, huB, C, hC, hzNe, ?_, ?_, ?_⟩
  · exact firstOrderTerminalCoefficientResidueEmbedding_residue_algebraMap
      phi u _ hphiU huA
  · exact firstOrderTerminalCoefficientResidueEmbedding_residue_coe
      phi x z hphiX hxA
  obtain ⟨hcoeff, hext⟩ :=
    firstOrderTerminalResidue_coefficient_and_extension
      phi g B x z hphiX hxA hB
  exact ⟨hcoeff, hext,
    nonautonomousFiniteCascadeLowerBranchResidueEmbedding_injective
      hfan hall (fun k hk => h1 k (by omega)) B hstate,
    huPoleB, hterminalActualBiHahnCharge,
    D, hDu', hDy', hDtransport', hDnonzero⟩

/-- Terminal output state, lifted from the adjacent pair field to the terminal component. -/
noncomputable def nonautonomousFiniteCascadeTerminalOutputInComponent
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
  algebraMap
    (NonautonomousFiniteCascadeTerminalPairField hfan N)
    (NonautonomousFiniteCascadeTerminalComponentField hfan N)
    ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N 1,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self 1)⟩

/-- Terminal constituent velocity inside its simple component field. -/
noncomputable def nonautonomousFiniteCascadeTerminalVelocityInComponent
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
  IntermediateField.AdjoinSimple.gen
    (NonautonomousFiniteCascadeTerminalPairField hfan N)
    (nonautonomousFiniteCascadeTerminalVelocitySucc hfan N)

/-- Literal terminal Wiman charge carrier `X_N f'_{N+1}(X_N) / X_{N+1}`. -/
noncomputable def nonautonomousFiniteCascadeTerminalChargedVelocityInComponent
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
  terminalLeadingStateInComponent hfan N *
    (nonautonomousFiniteCascadeTerminalVelocityInComponent hfan N /
      nonautonomousFiniteCascadeTerminalOutputInComponent hfan N)

/-- The exact terminal Wiman charge is detected by a literal Kronecker coordinate derivation on
the complete actual successor branch field. -/
theorem exists_nonautonomousFiniteCascadeTerminal_coordinateDerivation_response
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    let B := NonautonomousFiniteCascadeBranchField hfan (N + 1)
    let state : Fin (N + 2) → B :=
      nonautonomousFiniteCascadeStateInBranchField hfan (N + 1)
    let g := algebraMap
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) B
    ∃ P : Derivation ℂ B B,
      (∀ i, P (state i) = algebraMap ℂ B (if (i : ℕ) = N then 1 else 0)) ∧
      P (g (nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan N)) ≠ 0 := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan (N + 1)
  let state : Fin (N + 2) → B :=
    nonautonomousFiniteCascadeStateInBranchField hfan (N + 1)
  let g := algebraMap
    (NonautonomousFiniteCascadeTerminalComponentField hfan N) B
  obtain ⟨M, a, q, Nram, hNram, z₀, R, hR, z, hq, phi, Bv,
      hslope, hz₀, hz, hcharge, hgrade, hbiGrade, hdata⟩ :=
    exists_nonautonomousFiniteCascadeTerminal_normalizedVelocity_residueCoefficient
      hfan hall N h1
  rcases hdata with ⟨hBv, hstate, hxA, hxB, huA, huB, C, hC, hzNe,
    hresU, hresX, hcoeff, hext, hlowerInj, huPole, hactualCharge,
    D, hDu, hDy, hDtransport, hDnonzero⟩
  have hfullAI : AlgebraicIndependent ℂ state := by
    exact algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField
      hfan hall (N + 1)
  let val : Fin (N + 2) → ℂ := fun i => if (i : ℕ) = N then 1 else 0
  obtain ⟨P, hP⟩ := exists_derivation_prescribed hfullAI val
  let u := terminalLeadingStateInComponent hfan N
  let y := nonautonomousFiniteCascadeTerminalOutputInComponent hfan N
  let w := nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan N
  let c : NonautonomousFiniteCascadeTerminalComponentField hfan N :=
    algebraMap ℂ _ ((-((Nram * q : ℕ) : ℤ) : ℂ))
  have hDu' : D u = c * u := by
    simpa [u, c, terminalLeadingStateInComponent] using hDu
  have hDy' : D y = 0 := by
    simpa [y, nonautonomousFiniteCascadeTerminalOutputInComponent] using hDy
  have hDnonzero' : D w ≠ 0 := by
    simpa [w, nonautonomousFiniteCascadeTerminalChargedVelocityInComponent,
      nonautonomousFiniteCascadeTerminalVelocityInComponent,
      nonautonomousFiniteCascadeTerminalOutputInComponent,
      terminalLeadingStateInComponent] using hDnonzero
  letI : IsScalarTower ℂ
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let DL : Derivation ℂ B B := g (c * u) • P
  let pairCoordinate : Fin 2 →
      NonautonomousFiniteCascadeTerminalPairField hfan N := fun i =>
    ⟨nonautonomousFiniteCascadeTerminalStatePair hfan N i,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩
  have hpairTop : IntermediateField.adjoin ℂ (Set.range pairCoordinate) = ⊤ := by
    simpa [pairCoordinate] using
      (adjoin_range_lift_eq_top
        (nonautonomousFiniteCascadeTerminalStatePair hfan N)
        (nonautonomousFiniteCascadeTerminalStatePair hfan N) rfl)
  letI : Algebra.IsAlgebraic
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) :=
    nonautonomousFiniteCascadeTerminalComponent_isAlgebraic hfan hall N h1
  have hgu : g u = state ⟨N, by omega⟩ := by
    rfl
  have hgy : g y = state ⟨N + 1, by omega⟩ := by
    rfl
  have hmapPair : ∀ i : Fin 2,
      g (D (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        (pairCoordinate i))) =
      DL (g (algebraMap
        (NonautonomousFiniteCascadeTerminalPairField hfan N)
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        (pairCoordinate i))) := by
    intro i
    fin_cases i
    · change g (D u) = DL (g u)
      rw [hDu']
      rw [hgu]
      simp [DL, hP, val]
    · change g (D y) = DL (g y)
      rw [hDy', map_zero]
      rw [hgy]
      simp [DL, hP, val]
  have hintertwine : ∀ a : NonautonomousFiniteCascadeTerminalComponentField hfan N,
      g (D a) = DL (g a) :=
    derivation_map_eq_of_isAlgebraic_tower_adjoin
      pairCoordinate hpairTop
      (IsScalarTower.toAlgHom ℂ
        (NonautonomousFiniteCascadeTerminalComponentField hfan N) B)
      D DL hmapPair
  refine ⟨P, hP, ?_⟩
  change P (g w) ≠ 0
  intro hzero
  apply hDnonzero'
  apply g.injective
  rw [hintertwine w]
  simp [DL, hzero]

end

end GaloisForLFunctions.HTGeometry
