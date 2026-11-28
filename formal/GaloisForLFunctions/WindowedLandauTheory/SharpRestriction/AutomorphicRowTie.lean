import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

/-! The automorphic counting datum and arithmetic rows have the
same signatures, lowest types, levels and dimensions. The join
uses the prescribed Jacquet idempotents at the two auxiliary primes. -/

noncomputable section

open NumberField WindowedLandauTheory.BasicNotions

namespace WindowedLandauTheory.MainNotions.S

/-- Product of the local archimedean formal degrees. -/
def fdegAll (B : RowsAut) : ℝ :=
  ∏ v : InfinitePlace B.I.F, fdegOf (REAL.muG (B.I.ε v)) (B.σ v) (B.w v)

def SplitsCompl (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
    Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2

structure AutTie (D : D7) (B : RowsAut) (pl : InfinitePlace B.I.F ≃ D.what₂.Tau) : Prop where
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  rd_eq : B.I.rd = D.host.rdE
  eps_eq : ∀ v (i : Fin B.I.n), B.I.ε v i = epsS D.R (Fin.cast n_eq i)
  lam_eq : ∀ v (i : Fin B.I.n), B.lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i)
  ds : ∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)
  low : ∀ v, IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v)
  g_eq : B.g = D.host.g 0 * D.host.g 1
  g0_eq : B.g₀ = D.host.g 0
  D_eq : B.D = D.what₂.Dall
  Dstar_eq : D.what₂.Dstar = B.I.Dstar (fdegAll B) B.μf B.fund B.e

def RowsTie (D : D7) (B : RowsAut) : Prop :=
  (∃ pl : InfinitePlace B.I.F ≃ D.what₂.Tau, AutTie D B pl) ∧
    (∀ v, QuantumDeterminants.IsHCParam (B.lam v)) ∧
    (SplitsCompl D.host.E (D.host.g 0) → SplitsCompl B.I.E B.g₀)

end WindowedLandauTheory.MainNotions.S

namespace WindowedLandauTheory.MainNotions.ArithmeticCylinders

variable {D : D7}

def LevelSharp (A : AllRows D) : Prop :=
  ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k), A.eVec k v = eJk D k (ψ₀ k)

structure AllJoinA (A : AllRows D) : Prop where
  bundle : S.RowsTie D A.B
  level : LevelSharp A

end WindowedLandauTheory.MainNotions.ArithmeticCylinders
