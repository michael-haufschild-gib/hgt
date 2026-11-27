import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.TwGood
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefficientEmbeddingReflectsContinuity
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CuspidalPointParameters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusPolynomialsOfCuspidalPoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeComplement
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleScalarDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleBlockRepresentations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneScalarTwist

/-! An integral model of the full Hecke representation at a point provides
an integral model of its cuspidal factor by taking the lattice quotient
by the auxiliary character lines and undoing the normalizing twist. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.MainNotions.BlochKatoReduction
open ReciprocityTheory.Gal GlobalTheory.SSComplement

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc)
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "O" => D.nd.O i
local notation "K" => FractionRing (D.nd.O i)
local notation "L" => Qbar (D.nd.l i)
local notation "r₀" => D.R.r
local notation "t₀" => D.R.t

/-- Taking the cuspidal factor of a full point lattice preserves continuity
and the prescribed Frobenius polynomials. -/
theorem lattice_of_cuspidal_point (x : D.nd.X i) (π : D.naut.CG r₀)
    (P : D.naut.AV i) (hx : D.naut.ptV i P = some x)
    (hLoc : ∀ w, IsSplitPl D.host w →
      isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨r₀, π, 1⟩] ++ [muPart D.nd D.naut i])
        D.naut.etaTinv) w = D.naut.locV i P w)
    (hUnr : ∀ w, (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
      D.naut.unr (D.naut.locG π w))
    (ξ : Γ →* Oˣ) (hξc : Continuous fun g => (ξ g : O))
    (hξ : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      ∀ (B : ValuationSubring D.nd.Om) (g : Γ),
        IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) g →
        D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(t₀ : ℝ) / 2)) =
          {iotaO D.nd D.naut i (ξ g : O)})
    (ρ : Γ →* GL (Fin r₀) L) (hc : Continuous fun g => (ρ g).val) (hs : IsSSRep ρ)
    (hFrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.locG π w) →
      ∀ (B : ValuationSubring D.nd.Om) (g : Γ),
        IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) g →
        (ρ g).val.charpoly.map (D.naut.iotaQC i).toRingHom =
          galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (r₀ : ℝ)) / 2)))
    (hModel : ∀ (R : Γ →* GL (Fin D.R.nV) L), (Continuous fun g => (R g).val) → IsSSRep R →
      (∀ w, SplitOut D.nd i w → ∀ (B : ValuationSubring D.nd.Om) (g : Γ),
        IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) g →
          (R g).val.charpoly = (heckePol D.nd i x w).map (iotaOQ D.nd D.naut i)) →
      ∃ (M : Γ →* GL (Fin D.R.nV) O) (C : GL (Fin D.R.nV) L),
        ∀ g, mapRep (iotaOQ D.nd D.naut i) M g = C⁻¹ * R g * C) :
    ∃ M : Γ →* GL (Fin r₀) O, IsRepOfSig D.nd D.naut i [⟨r₀, π, 1⟩] M := by
  let j := iotaOQ D.nd D.naut i
  let ι := D.naut.iotaQ i
  let e := (D.naut.iotaQC i).toRingHom
  have hej : e.comp j = iotaO D.nd D.naut i := rfl
  have hj : Continuous j := continuous_iotaOQ D i
  let ξL := (Units.map j.toMonoidHom).comp ξ
  have hξL : Continuous fun g => (ξL g : L) := hj.comp hξc
  let ρ₁ := twGL ρ ξL⁻¹
  have hc₁ : Continuous fun g => (ρ₁ g).val := continuous_twGL ρ _ hc (by
    change Continuous fun g => (↑(ξL⁻¹ g) : L)
    simp only [MonoidHom.inv_apply, ← map_inv]
    exact hξL.comp continuous_inv)
  have hs₁ : IsSSRep ρ₁ := isSSRep_twGL ρ _ hs
  have h₁ (g : Γ) : ((ρ₁ g).val.map e) =
      iotaO D.nd D.naut i (ξ g : O) • (ρ g).val.map e := by
    rw [val_twGL, MonoidHom.inv_apply, inv_inv, map_smul_matrix]
    rfl
  let χ (c : Fin t₀) := D.nd.chi i ((c : ℕ) + 1)
  let χL (c : Fin t₀) := (Units.map j.toMonoidHom).comp (χ c)
  let full : Γ →* GL (Fin D.R.nV) L :=
    (blockM finSumFinEquiv ρ₁ (diagM χL).toHomUnits).toHomUnits
  have hcFull : Continuous fun g => (full g).val := by
    change Continuous fun g => Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (ρ₁ g).val 0 0 (Matrix.diagonal fun c : Fin t₀ => j (χ c g : O)))
    exact (hc₁.matrix_fromBlocks continuous_const continuous_const
      (Continuous.matrix_diagonal (continuous_pi fun c => hj.comp (D.nd.chi_cont i _)))).matrix_reindex _ _
  have hsFull : IsSSRep full := blockM_ss _ _ _ hs₁ (diagM_ss χL)
  have hFull (g : Γ) : (full g).val.charpoly =
      (ρ₁ g).val.charpoly * ∏ c : Fin t₀, (X - C (j (χ c g : O))) := by
    change (blockM finSumFinEquiv ρ₁ (diagM χL).toHomUnits g).charpoly = _
    rw [blockM_charpoly]
    change (ρ₁ g).val.charpoly * (diagM χL g).charpoly = _
    rw [diagM_charpoly]
    rfl
  have hPoint (w : PlE D.host) (hw : SplitOut D.nd i w) (B : ValuationSubring D.nd.Om) (g : Γ)
      (hBw : IsPlaceOver (F := D.host.E) B w) (hg : IsFrob (F := D.host.E) B (normV w) g) :
      (full g).val.charpoly = (heckePol D.nd i x w).map j := by
    have hu : D.naut.unr (D.naut.locG π w) := hUnr w fun k hk => hw.2.2.1 ((D.nd.S_def i w).mpr (by
      fin_cases k
      · exact ⟨Or.inl hk, hw.2.1⟩
      · exact ⟨Or.inr (Or.inl hk), hw.2.1⟩))
    apply Polynomial.map_injective e e.injective
    rw [hFull, Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, h₁,
      Polynomial.map_map, hej, hecke_polynomial_of_cuspidal_point D.nd D.naut i x π P hx hw (hLoc w hw.1) hu hBw hg,
      galPol_normalized_twist D.nd D.naut π hu _ (hξ w hw.2.1 B g hBw hg)]
    have hf : ((ρ g).val.map e).charpoly =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (r₀ : ℝ)) / 2)) := by
      rw [Matrix.charpoly_map]
      exact hFrob w hw.2.1 hu B g hBw hg
    rw [charpoly_smul_of_prod _ _ _ hf, Multiset.map_map]
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] <;> rfl
  obtain ⟨M, P₀, hM⟩ := hModel full hcFull hsFull hPoint
  have hval (g : Γ) : (M g).val.map j = (P₀⁻¹).val * (full g).val * P₀.val :=
    congrArg Units.val (hM g)
  have hcM : Continuous fun g => (M g).val := by
    have h : Continuous fun g => (M g).val.map j := by
      simp only [hval]
      exact (continuous_const.matrix_mul hcFull).matrix_mul continuous_const
    exact continuous_pi fun s => continuous_pi fun t =>
      continuous_of_continuous_iotaOQ D i (h.matrix_elem s t)
  have hsM : IsSSRep (mapRep (algebraMap O K) M) := by
    apply GlobalTheory.RetractionComplement.isSSRep_of_mapRep ι
    have he : mapRep ι (mapRep (algebraMap O K) M) = mapRep j M := by
      apply MonoidHom.ext
      intro g
      apply Units.ext
      exact Matrix.map_map
    rw [he]
    exact isSSRep_conj P₀⁻¹ (fun g => by simpa only [inv_inv] using hM g) hsFull
  letI : CharZero K := (RingHom.charZero_iff ι.injective).mpr inferInstance
  have hChar (g : Γ) : (M g).val.charpoly.map j =
      (ρ₁ g).val.charpoly * ∏ c : Fin t₀, (X - C (j (χ c g : O))) := by
    rw [← Matrix.charpoly_map, hval, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hFull]
  obtain ⟨M', hc', hs', hM'⟩ := GlobalTheory.LatticeComplement.exists_lattice_complement Γ O K r₀ t₀ M χ
    hcM hsM ⟨L, inferInstance, ι, ρ₁, hChar⟩
  have hSmall (g : Γ) : (M' g).val.charpoly.map j = (ρ₁ g).val.charpoly := by
    have h := congrArg (Polynomial.map j) (hM' g)
    change (M g).val.charpoly.map j =
      ((M' g).val.charpoly * ∏ c : Fin t₀, (X - C (χ c g : O))).map j at h
    rw [hChar, Polynomial.map_mul, Polynomial.map_prod] at h
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    exact (mul_right_cancel₀ (monic_prod_of_monic _ _ (fun c _ => monic_X_sub_C _)).ne_zero h).symm
  refine ⟨twGL M' ξ, continuous_twGL M' ξ hc' hξc, ?_, ?_⟩
  · rw [mapRep_twGL]
    exact isSSRep_twGL _ _ hs'
  · have hfinite := MainNotions.placesOver_finite_av D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfinite.eventually_cofinite_notMem, D.naut.locG_unr_ae π] with w hw hu B g hBw hg
    rw [isoLoc_single]
    have hf : ((ρ g).val.map e).charpoly =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (r₀ : ℝ)) / 2)) := by
      rw [Matrix.charpoly_map]
      exact hFrob w hw hu B g hBw hg
    have hscaled : ((M' g).val.map (iotaO D.nd D.naut i)).charpoly =
        (((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (r₀ : ℝ)) / 2))).map
          (· * iotaO D.nd D.naut i (ξ g : O))).map fun a => X - C a).prod := by
      calc
        _ = ((ρ₁ g).val.map e).charpoly := by
          simpa only [Matrix.charpoly_map, Polynomial.map_map, hej] using
            congrArg (Polynomial.map e) (hSmall g)
        _ = _ := by
          rw [h₁, Multiset.map_map]
          exact charpoly_smul_of_prod _ _ _ hf
    rw [← Matrix.charpoly_map, val_twGL, map_smul_matrix, charpoly_smul_of_prod _ _ _ hscaled,
      Multiset.map_map]
    have hcanc : iotaO D.nd D.naut i (ξ g : O) * iotaO D.nd D.naut i (((ξ g)⁻¹ : Oˣ) : O) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    unfold galPol
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
    simp only [Function.comp_apply, mul_assoc, hcanc, mul_one]

end WindowedLandauTheory.NormalizedTypes
