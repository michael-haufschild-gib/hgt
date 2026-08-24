import GaloisForLFunctions.HTGeometry.HypertranscendentalJetHilbertReconstruction

/-!
# Finite evaluation Hasse reconstruction

A square packet of evaluation places with proved dual recovery is packaged as local-global data.
Its local packet map is injective, hence equality and vanishing of global coefficient families are
detected placewise, while every failure has one explicit evaluation-place witness.  The canonical
initial Gamma and digamma jets provide unconditional concrete instances.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- Chosen finite places and dual weights giving exact recovery of a finite function family. -/
structure FiniteEvaluationHasseData
    {J α : Type*} [Fintype J] [DecidableEq J] (u : J → α → ℂ) where
  points : J → α
  dual : J → J → ℂ
  points_injective : Function.Injective points
  dual_delta : ∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0
  dual_recovery : ∀ (a : J → ℂ) q,
    ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q

/-- Extract the Hasse reconstruction data from a complete finite Hilbert-reconstruction packet. -/
noncomputable def finiteEvaluationHasseDataOf
    {J α : Type*} [Fintype J] [DecidableEq J] {u : J → α → ℂ}
    (h : FiniteEvaluationHilbertReconstruction u) :
    FiniteEvaluationHasseData u := by
  let points := Classical.choose h
  have hpoints := Classical.choose_spec h
  let dual := Classical.choose hpoints
  have hs := Classical.choose_spec hpoints
  exact ⟨points, dual, hs.1, hs.2.1, hs.2.2.1⟩

namespace FiniteEvaluationHasseData

variable {J α : Type*} [Fintype J] [DecidableEq J] {u : J → α → ℂ}

/-- Local values of one global coefficient family at every chosen evaluation place. -/
def localPacket (D : FiniteEvaluationHasseData u) (a : J → ℂ) : J → ℂ :=
  fun i => ∑ r, a r * u r (D.points i)

/-- Reconstruct global coefficients from a local value packet using the chosen dual weights. -/
def reconstruct (D : FiniteEvaluationHasseData u) (packet : J → ℂ) : J → ℂ :=
  fun q => ∑ i, D.dual q i * packet i

/-- Dual reconstruction is a left inverse to the local packet map. -/
@[simp] theorem reconstruct_localPacket (D : FiniteEvaluationHasseData u)
    (a : J → ℂ) : D.reconstruct (D.localPacket a) = a := by
  funext q
  exact D.dual_recovery a q

/-- The chosen finite places jointly separate global coefficient families. -/
theorem localPacket_injective (D : FiniteEvaluationHasseData u) :
    Function.Injective D.localPacket := by
  intro a b hab
  rw [← D.reconstruct_localPacket a, ← D.reconstruct_localPacket b, hab]

/-- Local evaluation as a linear endomorphism of the finite coefficient space. -/
def localPacketLinearMap (D : FiniteEvaluationHasseData u) :
    (J → ℂ) →ₗ[ℂ] (J → ℂ) where
  toFun := D.localPacket
  map_add' a b := by
    funext i
    simp [localPacket, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext i
    simp [localPacket, Finset.mul_sum, mul_assoc]

/-- The finite local evaluation linear map is injective. -/
theorem localPacketLinearMap_injective (D : FiniteEvaluationHasseData u) :
    Function.Injective D.localPacketLinearMap :=
  D.localPacket_injective

/-- Equal finite dimensions upgrade local separation to realization of every local packet. -/
theorem localPacket_surjective (D : FiniteEvaluationHasseData u) :
    Function.Surjective D.localPacket := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    D.localPacketLinearMap_injective

/-- **Finite evaluation Hasse gluing.**  Every local value packet has one unique global coefficient
family. -/
theorem localPacket_existsUnique (D : FiniteEvaluationHasseData u)
    (packet : J → ℂ) : ∃! a : J → ℂ, D.localPacket a = packet := by
  obtain ⟨a, ha⟩ := D.localPacket_surjective packet
  exact ⟨a, ha, fun b hb => D.localPacket_injective (hb.trans ha.symm)⟩

/-- Global finite coefficients and complete local evaluation packets are linearly equivalent. -/
noncomputable def localPacketLinearEquiv (D : FiniteEvaluationHasseData u) :
    (J → ℂ) ≃ₗ[ℂ] (J → ℂ) :=
  LinearEquiv.ofBijective D.localPacketLinearMap
    ⟨D.localPacketLinearMap_injective, D.localPacket_surjective⟩

/-- Finite evaluation Hasse congruence: all local values agree exactly when global coefficients
agree. -/
theorem localPacket_congr_hasse_iff (D : FiniteEvaluationHasseData u)
    (a b : J → ℂ) :
    (∀ i, D.localPacket a i = D.localPacket b i) ↔ a = b := by
  constructor
  · intro h
    apply D.localPacket_injective
    funext i
    exact h i
  · rintro rfl i
    rfl

/-- A global coefficient family vanishes exactly when every chosen local evaluation vanishes. -/
theorem localPacket_eq_zero_hasse_iff (D : FiniteEvaluationHasseData u)
    (a : J → ℂ) :
    (∀ i, D.localPacket a i = 0) ↔ a = 0 := by
  rw [← D.localPacket_congr_hasse_iff a 0]
  simp [localPacket]

/-- Inequality of global coefficient families has a witness at one evaluation place. -/
theorem ne_iff_exists_localPacket_ne (D : FiniteEvaluationHasseData u)
    (a b : J → ℂ) :
    a ≠ b ↔ ∃ i, D.localPacket a i ≠ D.localPacket b i := by
  classical
  constructor
  · intro hab
    by_contra hno
    apply hab
    apply (D.localPacket_congr_hasse_iff a b).mp
    intro i
    by_contra hi
    exact hno ⟨i, hi⟩
  · rintro ⟨i, hi⟩ hab
    exact hi (by rw [hab])

end FiniteEvaluationHasseData

/-! ## Unconditional Gamma and digamma instances -/

/-- Chosen Hasse evaluation data for the initial Gamma jet of depth `d`. -/
noncomputable def gammaInitialJetHasseData (d : ℕ) :
    FiniteEvaluationHasseData
      (hypertranscendentalDerivativeOrderFamily Complex.Gamma (initialDerivativeOrder d)) :=
  finiteEvaluationHasseDataOf (gammaInitialJet_finiteEvaluationHilbertReconstruction d)

/-- Chosen Hasse evaluation data for the initial digamma jet of depth `d`. -/
noncomputable def digammaInitialJetHasseData (d : ℕ) :
    FiniteEvaluationHasseData
      (hypertranscendentalDerivativeOrderFamily Complex.digamma (initialDerivativeOrder d)) :=
  finiteEvaluationHasseDataOf (digammaInitialJet_finiteEvaluationHilbertReconstruction d)

/-- Initial Gamma-jet coefficients are recovered exactly from their chosen local values. -/
theorem gammaInitialJetHasse_reconstruct (d : ℕ) (a : Fin d → ℂ) :
    (gammaInitialJetHasseData d).reconstruct
        ((gammaInitialJetHasseData d).localPacket a) = a :=
  (gammaInitialJetHasseData d).reconstruct_localPacket a

/-- Equality of initial Gamma jets is detected at every chosen evaluation place. -/
theorem gammaInitialJet_congr_hasse_iff (d : ℕ) (a b : Fin d → ℂ) :
    (∀ i, (gammaInitialJetHasseData d).localPacket a i =
      (gammaInitialJetHasseData d).localPacket b i) ↔ a = b :=
  (gammaInitialJetHasseData d).localPacket_congr_hasse_iff a b

/-- An initial Gamma jet is zero exactly when all chosen local evaluations are zero. -/
theorem gammaInitialJet_eq_zero_hasse_iff (d : ℕ) (a : Fin d → ℂ) :
    (∀ i, (gammaInitialJetHasseData d).localPacket a i = 0) ↔ a = 0 :=
  (gammaInitialJetHasseData d).localPacket_eq_zero_hasse_iff a

/-- Distinct initial Gamma jets differ at a chosen evaluation place. -/
theorem gammaInitialJet_ne_iff_exists_localWitness (d : ℕ) (a b : Fin d → ℂ) :
    a ≠ b ↔ ∃ i, (gammaInitialJetHasseData d).localPacket a i ≠
      (gammaInitialJetHasseData d).localPacket b i :=
  (gammaInitialJetHasseData d).ne_iff_exists_localPacket_ne a b

/-- Every finite packet of values at the chosen Gamma places has one unique global jet
coefficient family. -/
theorem gammaInitialJetHasse_existsUnique (d : ℕ) (packet : Fin d → ℂ) :
    ∃! a : Fin d → ℂ, (gammaInitialJetHasseData d).localPacket a = packet :=
  (gammaInitialJetHasseData d).localPacket_existsUnique packet

/-- Initial digamma-jet coefficients are recovered exactly from their chosen local values. -/
theorem digammaInitialJetHasse_reconstruct (d : ℕ) (a : Fin d → ℂ) :
    (digammaInitialJetHasseData d).reconstruct
        ((digammaInitialJetHasseData d).localPacket a) = a :=
  (digammaInitialJetHasseData d).reconstruct_localPacket a

/-- Equality of initial digamma jets is detected at every chosen evaluation place. -/
theorem digammaInitialJet_congr_hasse_iff (d : ℕ) (a b : Fin d → ℂ) :
    (∀ i, (digammaInitialJetHasseData d).localPacket a i =
      (digammaInitialJetHasseData d).localPacket b i) ↔ a = b :=
  (digammaInitialJetHasseData d).localPacket_congr_hasse_iff a b

/-- An initial digamma jet is zero exactly when all chosen local evaluations are zero. -/
theorem digammaInitialJet_eq_zero_hasse_iff (d : ℕ) (a : Fin d → ℂ) :
    (∀ i, (digammaInitialJetHasseData d).localPacket a i = 0) ↔ a = 0 :=
  (digammaInitialJetHasseData d).localPacket_eq_zero_hasse_iff a

/-- Distinct initial digamma jets differ at a chosen evaluation place. -/
theorem digammaInitialJet_ne_iff_exists_localWitness (d : ℕ) (a b : Fin d → ℂ) :
    a ≠ b ↔ ∃ i, (digammaInitialJetHasseData d).localPacket a i ≠
      (digammaInitialJetHasseData d).localPacket b i :=
  (digammaInitialJetHasseData d).ne_iff_exists_localPacket_ne a b

/-- Every finite packet of values at the chosen digamma places has one unique global jet
coefficient family. -/
theorem digammaInitialJetHasse_existsUnique (d : ℕ) (packet : Fin d → ℂ) :
    ∃! a : Fin d → ℂ, (digammaInitialJetHasseData d).localPacket a = packet :=
  (digammaInitialJetHasseData d).localPacket_existsUnique packet

end


end GaloisForLFunctions.HTGeometry
