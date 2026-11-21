import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.DesignExistsOfChoices
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV

/-! Design families with the closed lattice estimates supply connected window certificates. -/

namespace WindowedLandauTheory.MainNotions

open WindowedLandauTheory.BasicNotions

namespace Pk

/-- The prime divisors of the local covolume denominator are bounded by the rank. -/
def DGamSmooth {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (p : ℕ),
    p.Prime → p ∣ ((Fm.D x i).mem u).C.DGam →
      p ≤ 2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1

end Pk

theorem J.dGamSmooth_of_dvd {eps : ℝ} (Fm : FamP eps) (h : DGamDvdF Fm) : Pk.DGamSmooth Fm := by
  obtain ⟨x₀, hdiv⟩ := h
  exact ⟨x₀, fun x hx i u p hp hdvd => prime_le_of_dvd_minkM hp (hdvd.trans (hdiv x hx i u))⟩

abbrev WithSm (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ Pk.DGamSmooth Fm

abbrev Des (𝒞 : FamClass) (C0 : ℝ) : FamClass :=
  fun Fm => WithTw (WithSm 𝒞) Fm ∧ (∃ CH : ℝ, ChosenE Fm C0 CH) ∧ TuSize Fm ∧ DGamSize Fm

end WindowedLandauTheory.MainNotions

namespace UpperTheory.Top

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions

theorem topDesWin (𝒞 𝒞' ℰ : FamClass) (Cabs C0 eD eL : ℝ)
    (hEx : DesignExists (WithTw (WithSm 𝒞')) C0)
    (hsub : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm)
    (hwin : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → ℰ Fm)
    (hV : ∀ {eps : ℝ} (Fm : FamP eps), ℰ Fm → HypV Fm.toFamCore)
    (hN : Closed (Des 𝒞 C0) fun Fm _ => LinkN Fm)
    (hEta : Closed (Des 𝒞 C0) fun Fm _ => LinkEta Fm)
    (hIRR : Closed (Des 𝒞 C0) fun Fm _ => LinkIRR Fm)
    (hZ : Closed (Des 𝒞 C0) fun Fm _ => SmallLevelRankEq Fm)
    (hDIV : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH)
    (hRk : Closed (Des 𝒞 C0) fun Fm CH => ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm)
    (hG : Closed (Des 𝒞 C0) fun Fm _ => LinkG Fm)
    (hS : Closed (Des 𝒞 C0) fun Fm _ => TuSize Fm → LinkS Fm C0)
    (hGL : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 eD eL) :
    FamilyClassConnected ℰ := by
  obtain ⟨ε₁, hε₁, hlinks⟩ := hN.and (hDIV.and (hEta.and (hIRR.and (hZ.and (hRk.and (hG.and (hS.and hGL)))))))
  obtain ⟨ε₃, hε₃, hex⟩ := hEx
  refine ⟨eD, eL, min ε₁ ε₃, lt_min hε₁ hε₃, fun ε hε hlt => ?_⟩
  obtain ⟨K, hK⟩ := hlinks ε hε (hlt.le.trans (min_le_left _ _))
  obtain ⟨Fm, CH, hc, _, hL, hCh, hT, hDG⟩ := hex ε hε (hlt.le.trans (min_le_right _ _)) K
  have hdesign : Des 𝒞 C0 Fm := ⟨⟨⟨hsub Fm hc.1.1, hc.1.2⟩, hc.2⟩, ⟨CH, hCh⟩, hT, hDG⟩
  obtain ⟨aN, aD, aE, aI, aZ, aR, aG, aS, aGL⟩ := hK Fm CH hdesign hL
  have hFm := hwin Fm hc.1.1
  have hin := divinN_of_hypV Fm hε (hV Fm hFm) aN aZ
  have hD := aD hT hDG aE hin
  obtain ⟨hFull, hRank⟩ := aR hCh
  have hMu := J.linkMu_of_linkDIV Fm hD hFull hRank (muTu_of_tuSize Fm hε hT) (J.muDGam_of_fact Fm hDG)
  exact ⟨Fm, hFm, aGL hT hDG hCh ⟨aG, aS hT, aI, hD, hMu⟩⟩

end UpperTheory.Top
