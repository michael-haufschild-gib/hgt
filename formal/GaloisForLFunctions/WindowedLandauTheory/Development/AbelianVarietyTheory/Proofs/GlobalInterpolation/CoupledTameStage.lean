import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostTameInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedTypeStage

/-! At the empty local stage, the unramified parameter model admits the
coupled inertia generators while preserving the finite-group idempotents. -/

noncomputable section

open Polynomial IsLocalRing
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes
open WindowedLandauTheory.MainNotions.N ReciprocityTheory.Gal GlobalTheory.GLq

namespace GlobalTheory.EmptyLocalStage

private theorem prod_rootsBar_X_sub_one_pow {p : ℕ} [Fact p.Prime] (t : Fbar p →* ℂ) (n : ℕ) :
    ((rootsBar ((X - 1 : (ZMod p)[X]) ^ n)).map fun x => X - C (t x)).prod =
      (X - 1 : ℂ[X]) ^ n := by
  rw [rootsBar, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, roots_pow, ← C_1, roots_X_sub_C,
    Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton, map_one, C_1, Multiset.prod_singleton]

/-- The empty local stage retains the same auxiliary places after replacing its local parameter model. -/
def unramifiedNAutAtHost (D : D7) [IsEmpty D.nd.Loc] : NAut D.nd :=
  unramifiedNAut D.nd D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj

/-- Install a coupled generator at each auxiliary place before the local rows are attached. -/
def ntypesOfTameGenerators (D : D7) [hE : IsEmpty D.nd.Loc]
    (σ : ∀ k, D.nd.PlG k → G D.host.E D.nd.Om)
    (hσ : ∀ k v, σ k v ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)))
    (hgen : ∀ k v, TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) (σ k v)) :
    NTypes (unramifiedNAutAtHost D) :=
  { D.ntypes with
    tg := σ
    tg_mem := hσ
    tg_gen := hgen
    heckeLoc_gamma_places := fun i => hE.elim i
    chiT_tg := fun i => hE.elim i
    inertiaCharpoly_type := by
      intro k v P _
      letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      exact (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k)
        ((unramifiedNAutAtHost D).lpDim P)).symm
    Par := Empty
    labPar := fun _ P => P.elim
    labPar_monic := fun _ P => P.elim
    locPar := fun P => P.elim
    locPar_dim := fun P => P.elim
    labPar_def := fun _ P => P.elim
    MtPar := fun _ _ P => P.elim
    AmbPar := fun _ P => P.elim }

/-- Replacing the empty local parameter model leaves the finite-group
actions and the coefficients of the trivial-character idempotent unchanged. -/
def withTameGenerators (D : D7) [hE : IsEmpty D.nd.Loc]
    (σ : ∀ k, D.nd.PlG k → G D.host.E D.nd.Om)
    (hσ : ∀ k v, σ k v ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)))
    (hgen : ∀ k v, TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) (σ k v)) : D7 :=
  { D with
    naut := unramifiedNAutAtHost D
    nbc := emptyNBC (unramifiedNAutAtHost D)
    ntypes := ntypesOfTameGenerators D σ hσ hgen
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat
    nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    loc_tie := fun i => hE.elim i
    bc_tie := fun i => hE.elim i
    rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i
    Z_tie := fun i => hE.elim i
    Zgood_tie := fun i => hE.elim i }

/-- Compatible inertia generators can be chosen simultaneously in an empty
local stage for the prescribed label data at both type primes. -/
theorem exists_coupled_tame_stage (D : D7) [IsEmpty D.nd.Loc]
    (L : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; LabelDatum (D.host.g k)) :
    ∃ (σ : ∀ k, D.nd.PlG k → G D.host.E D.nd.Om)
      (hσ : ∀ k v, σ k v ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)))
      (hgen : ∀ k v, TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) (σ k v))
      (κ : ∀ k v, ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Fb (D.host.g k) (D.host.g_prime k)),
      ∀ k v, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (κ k v)
          ((withTameGenerators D σ hσ hgen).ntypes.tg k v) (L k).gen := by
  have h := fun k v => GlobalTheory.TameKummer.exists_coupled_tame_generator_at_host D k v (L k)
  choose κ σ hσ hgen hT using h
  exact ⟨σ, hσ, hgen, κ, hT⟩

end GlobalTheory.EmptyLocalStage
