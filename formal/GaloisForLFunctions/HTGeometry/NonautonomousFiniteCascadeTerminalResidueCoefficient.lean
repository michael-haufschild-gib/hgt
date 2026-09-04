import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalResidue
import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalBiHahn
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
        (hC : C.comap (valuationSubringResidueMapOfComapEq g A B hB) =
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
          (firstOrderTerminalBiHahnEmbedding (phi (u * x))) ≠ 0 := by
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
    huPoleB, hterminalActualBiHahnCharge⟩

end

end GaloisForLFunctions.HTGeometry
