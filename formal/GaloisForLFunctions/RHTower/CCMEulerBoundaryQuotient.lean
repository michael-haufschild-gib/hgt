import GaloisForLFunctions.RHTower.CCMEulerAnnularRange
import GaloisForLFunctions.RHTower.CCMEulerMovingCarrierRadical
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The actual finite Euler boundary quotient and its return map

The source-defined boundary is a bounded surjection onto a closed even Fourier
annulus. Its kernel is the enlarged Fourier gap. The induced Banach quotient
equivalence retains the original adjoint return and therefore reconstructs the
complete cleared current on the Sonin carrier.
-/

noncomputable section

open IsDedekindDomain

namespace RHTower

/-- The actual even Fourier annulus of a finite Euler boundary. -/
def ccmEulerBoundaryAnnulus (S : Finset (HeightOneSpectrum ℤ)) (b c : ℝ) :
    Submodule ℂ evenSubspace :=
  (evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)).ker ⊓
    (1 - evenFourierCutoff c).ker

theorem mem_ccmEulerBoundaryAnnulus_iff (S : Finset (HeightOneSpectrum ℤ))
    (b c : ℝ) (u : evenSubspace) :
    u ∈ ccmEulerBoundaryAnnulus S b c ↔
      evenFourierCutoff (b / ccmFiniteEulerCarrierScale S) u = 0 ∧
        evenFourierCutoff c u = u := by
  change (_ = 0 ∧ u - evenFourierCutoff c u = 0) ↔ _
  rw [sub_eq_zero]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem ccmEulerBoundaryAnnulus_isClosed (S : Finset (HeightOneSpectrum ℤ)) (b c : ℝ) :
    IsClosed (ccmEulerBoundaryAnnulus S b c : Set evenSubspace) :=
  (evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)).isClosed_ker.inter
    (1 - evenFourierCutoff c).isClosed_ker

/-- In the active chamber this is the range of the literal difference of Fourier cutoffs. -/
theorem ccmEulerBoundaryAnnulus_eq_range (S : Finset (HeightOneSpectrum ℤ)) (b c : ℝ)
    (hbc : b / ccmFiniteEulerCarrierScale S ≤ c) :
    ccmEulerBoundaryAnnulus S b c =
      (evenFourierCutoff c - evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)).range := by
  ext u
  rw [mem_ccmEulerBoundaryAnnulus_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨u, ?_⟩
    change (evenFourierCutoff c - evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)) u = u
    simp only [_root_.sub_apply, hhi, hlo, sub_zero]
  · rintro ⟨v, rfl⟩
    have hlo : evenFourierCutoff (b / ccmFiniteEulerCarrierScale S) *
        (evenFourierCutoff c - evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)) = 0 := by
      rw [mul_sub, evenFourierCutoff_mul_of_le _ _ hbc,
        evenFourierCutoff_mul_of_le _ _ le_rfl, sub_self]
    have hhi : evenFourierCutoff c *
        (evenFourierCutoff c - evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)) =
          evenFourierCutoff c - evenFourierCutoff (b / ccmFiniteEulerCarrierScale S) := by
      rw [mul_sub, evenFourierCutoff_mul_of_le _ _ le_rfl,
        evenFourierCutoff_mul_of_le_rev _ _ hbc]
    exact ⟨DFunLike.congr_fun hlo v, DFunLike.congr_fun hhi v⟩

instance ccmEulerBoundaryAnnulus_completeSpace
    (S : Finset (HeightOneSpectrum ℤ)) (b c : ℝ) :
    CompleteSpace (ccmEulerBoundaryAnnulus S b c) :=
  (ccmEulerBoundaryAnnulus_isClosed S b c).completeSpace_coe

/-- The original physical boundary map with its proved annular codomain. -/
def ccmEulerBoundaryMap (S : Finset (HeightOneSpectrum ℤ))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    evenCentralSoninCarrier b →L[ℂ] ccmEulerBoundaryAnnulus S b c :=
  (((evenFourierCutoff c * ccmFiniteEulerDenominator S).comp
    (evenCentralSoninCarrier b).subtypeL)).codRestrict (ccmEulerBoundaryAnnulus S b c)
      (fun f => (mem_ccmEulerBoundaryAnnulus_iff S b c _).mpr
        ((ccmFiniteEulerDenominator_range_iff_annulus S b c hb hc _).mp
          ⟨f, f.property, rfl⟩))

theorem ccmEulerBoundaryMap_surjective (S : Finset (HeightOneSpectrum ℤ))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Function.Surjective (ccmEulerBoundaryMap S b c hb hc) := by
  intro u
  have hu := (mem_ccmEulerBoundaryAnnulus_iff S b c u).mp u.property
  obtain ⟨f, hf, hfu⟩ := exists_sonin_ccmFiniteEulerDenominator_preimage S b c hb hc hu.1 hu.2
  refine ⟨⟨f, hf⟩, ?_⟩
  exact Subtype.ext hfu

/-- The boundary quotient removes exactly the enlarged Fourier gap inside the Sonin source. -/
theorem ccmEulerBoundaryMap_ker (S : Finset (HeightOneSpectrum ℤ))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (ccmEulerBoundaryMap S b c hb hc).ker =
      ((evenFourierCutoff (ccmFiniteEulerCarrierScale S * c)).comp
        (evenCentralSoninCarrier b).subtypeL).ker := by
  ext f
  change (ccmEulerBoundaryMap S b c hb hc f = 0) ↔
    evenFourierCutoff (ccmFiniteEulerCarrierScale S * c) (f : evenSubspace) = 0
  have hgap := ccmFiniteEulerDenominator_fourierGap_iff S hc hb
    ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b f).mp f.property).2
  constructor
  · intro h
    apply hgap.mp
    exact congrArg (fun u : ccmEulerBoundaryAnnulus S b c => (u : evenSubspace)) h
  · intro h
    exact Subtype.ext (hgap.mpr h)

instance ccmEulerBoundaryMap_ker_isClosed (S : Finset (HeightOneSpectrum ℤ))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    IsClosed ((ccmEulerBoundaryMap S b c hb hc).ker : Set (evenCentralSoninCarrier b)) :=
  (ccmEulerBoundaryMap S b c hb hc).isClosed_ker

/-- The source-defined boundary identifies its Banach quotient with the actual annulus. -/
def ccmEulerBoundaryQuotientEquiv (S : Finset (HeightOneSpectrum ℤ))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (evenCentralSoninCarrier b ⧸ (ccmEulerBoundaryMap S b c hb hc).ker) ≃L[ℂ]
      ccmEulerBoundaryAnnulus S b c := by
  let B := ccmEulerBoundaryMap S b c hb hc
  letI : NormedSpace ℂ (evenCentralSoninCarrier b ⧸ B.ker) :=
    @Submodule.Quotient.normedSpace (evenCentralSoninCarrier b)
      (inferInstance : SeminormedAddCommGroup (evenCentralSoninCarrier b))
      ℂ inferInstance inferInstance B.ker ℂ inferInstance
      (inferInstance : NormedSpace ℂ (evenCentralSoninCarrier b)) inferInstance inferInstance
  let L : (evenCentralSoninCarrier b ⧸ B.ker) →L[ℂ] ccmEulerBoundaryAnnulus S b c :=
    B.ker.liftQL B le_rfl
  refine ContinuousLinearEquiv.ofBijective (𝕜 := ℂ) (𝕜' := ℂ)
    (σ := RingHom.id ℂ) (σ' := RingHom.id ℂ)
    (E := evenCentralSoninCarrier b ⧸ B.ker) (F := ccmEulerBoundaryAnnulus S b c) L ?_ ?_
  · exact Submodule.ker_liftQ_eq_bot B.ker B.toLinearMap le_rfl le_rfl
  · change LinearMap.range (B.ker.liftQ B.toLinearMap le_rfl) = ⊤
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.mpr (ccmEulerBoundaryMap_surjective S b c hb hc)

/-- The quotient equivalence evaluates to the original boundary on every source vector. -/
theorem ccmEulerBoundaryQuotientEquiv_apply_mk (S : Finset (HeightOneSpectrum ℤ))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (f : evenCentralSoninCarrier b) :
    ccmEulerBoundaryQuotientEquiv S b c hb hc (Submodule.Quotient.mk f) =
      ccmEulerBoundaryMap S b c hb hc f := rfl

/-- Retaining the actual adjoint return reconstructs the full source current from its
boundary quotient; replacing it by the boundary norm would lose this identity. -/
theorem ccmEulerBoundaryQuotient_reconstructs_current
    (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) (hb : 1 ≤ b)
    (f : evenCentralSoninCarrier b) :
    ccmFiniteEulerSourceCurrent S (f : evenSubspace) =
      -ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)
        (ccmEulerBoundaryQuotientEquiv S b 1 (zero_lt_one.trans_le hb) zero_lt_one
          (Submodule.Quotient.mk f) : evenSubspace) := by
  rw [ccmEulerBoundaryQuotientEquiv_apply_mk]
  exact ccmFiniteEulerSourceCurrent_apply_sonin S hb f.property

end RHTower
