import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoupledTameInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitPlaceOrder

/-! The split auxiliary primes of a host have order one at every designated
place, so the prescribed label generators come from tame inertia. -/

noncomputable section

open IsLocalRing WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes
open ReciprocityTheory.Gal GlobalTheory.GLq

namespace GlobalTheory.TameKummer

theorem exists_coupled_tame_generator_at_host (D : D7) (k : Fin 2) (v : D.nd.PlG k) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ L : LabelDatum (D.host.g k), ∃ κ : ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Fbar (D.host.g k),
      ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) σ ∧
        TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ σ L.gen := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  letI := D.nd.acOm
  intro L
  let w := D.naut.plGw k v
  have hw := D.naut.plGw_over k v
  have hsq := (normV_and_notMem_sq_of_split (D.host.g_prime k) (D.nd.g_split k) w hw).2
  exact exists_coupled_tame_generator (D.nd.plOm.1 w) w (D.nd.plOm.2 w) hw hsq L

end GlobalTheory.TameKummer
