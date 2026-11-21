import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

/-! Slope and character data for the window inequality at one host. -/

noncomputable section

namespace UpperTheory.Comparison₂

open Deduction.CH WindowedLandauTheory WindowedLandauTheory.HC WindowedLandauTheory.D5 WindowedLandauTheory.RankGapBounds.WeightedMeanData WindowedLandauTheory.LFunctionChainParameters.WeightedSlopeBounds WindowedLandauTheory.LFunctionChainParameters.characterSumData WindowedLandauTheory.LFunctionChainParameters.ThickSetMeanBounds WindowedLandauTheory.LFunctionChainParameters.LErr
  WindowedLandauTheory.LFunctionChainParameters.LChain WindowedLandauTheory.LFunctionChainParameters.LHost

def chr (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) : φ.Char := (ψ.toMonoidHom.comp (toE φ)).toHomUnits

variable {φ : Frame}

def HostAddCharCompatible (H : HostRaw φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ) : Prop :=
  ∀ ψ : AddChar (E0 × φ.A) ℂ, ψ ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    (∀ n : ℕ, n ≠ 0 → χ (n : ZMod N) = primVal (arith H) ψ n) → ell ψ = An.logDerivativeAtOne χ

open Classical in

def keptA (Λ : Level) (H : HostRaw φ) : Finset (AddChar (E0 × φ.A) ℂ) :=
  Finset.univ.filter fun ψ => H.Kept Λ.KEPT (chr φ ψ)

def koOf (Λ : Level) : ℝ := ∑ ψ ∈ Λ.KEPT, ‖An.logDerivativeAtOne ψ.χ‖

def CoreAtH (H : HostRaw φ) (TT : Finset φ.A) (eD eL K cHH eK eps x : ℝ) : Prop :=
  ∃ (U0 : Type) (_ : Fintype U0) (tr : U0 → φ.A)
    (W : U0 → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (Top : Type) (_ : Fintype Top)
    (m f : ℕ) (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (ell : AddChar (E0 × φ.A) ℂ → ℂ) (N : ℕ) (T2 : Finset φ.A) (a : φ.A → ℝ)
    (w : φ.A → Fin m → E0 × φ.A → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := φ.A)) (η X' θ : ℝ),
    HostAddCharCompatible H ell ∧ Dd.x = x ∧ Dd.ε = eps ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    (∀ s ∈ φ.A0, ∃ u, tr u = s) ∧ IdentU Dd tr (arith H) N ell TT a w eT eP ∧
    WindowedLandauTheory.LFunctionChainParameters.LChain.SizeData₂ Dd C Xpp ∧ ErrWindows Dd C Xpp eK K ∧ BNBoundsU Dd T2 ∧
    SizesA φ.A0 TT T2 a w N x Dd.b Dd.b' η X' θ ∧ ThinScales (arith H) ell X' θ ∧
    CostWindows x (fPl φ.A) Dd.b η θ ∧
    RestSize eps x (Fintype.card φ.A) TT.card T2.card m Dd.b Dd.k Dd.a ∧
    ∀ s ∈ T2, s ∈ φ.A0

end UpperTheory.Comparison₂

end
