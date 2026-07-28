import GaloisForLFunctions.RHTower.FermionicSpinChainRealization
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Fermionic Fock isospectrality

For every particle number, the free-fermion lift of a finite one-particle
spectrum has the subset sums of the one-particle energies as a complete
eigenvalue list.  Changing the one-particle eigenbasis conjugates the entire
sector and leaves this many-body spectrum unchanged.

This is the exact exterior-power lift needed to distinguish a genuine
many-body isospectral statement from a claim about only the one-excitation
block.
-/

open Module
open scoped BigOperators

noncomputable section

namespace RHTower.ParityForecast

/-- Standard one-particle coordinate basis. -/
def standardOneParticleBasis (r : ℕ) :
    Basis (Fin r) ℂ (FiniteIndexClockSpace (Fin r)) :=
  (EuclideanSpace.basisFun (Fin r) ℂ).toBasis

/-- Canonical Slater basis in the `k`-fermion sector. -/
def fermionicSectorBasis (r k : ℕ) :
    Basis (Set.powersetCard (Fin r) k) ℂ
      (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :=
  (standardOneParticleBasis r).exteriorPower k

/-- Sum of the occupied one-particle energies. -/
def fermionicSubsetEnergy {r k : ℕ} (energy : Fin r → ℝ)
    (S : Set.powersetCard (Fin r) k) : ℝ :=
  ∑ j ∈ S.val, energy j

/-! ## Intrinsic second quantization -/

/-- Apply the one-particle operator in slot `i`, and the identity elsewhere. -/
def fermionicSlotLinearMap {r k : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (i j : Fin k) :
    FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r) :=
  if j = i then A else LinearMap.id

/--
Sum of the `k` slotwise one-particle actions before antisymmetrization.
This is the tensor-level differential of the exterior-power action.
-/
def secondQuantizationMultilinear {r k : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    MultilinearMap ℂ
      (fun _ : Fin k => FiniteIndexClockSpace (Fin r))
      (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :=
  ∑ i : Fin k,
    (exteriorPower.ιMulti ℂ k).toMultilinearMap.compLinearMap
      (fermionicSlotLinearMap A i)

/--
Canonical alternating form of the slotwise sum.  Factorial normalization
removes the scale introduced by alternatization.
-/
def secondQuantizationAlternating {r k : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    (FiniteIndexClockSpace (Fin r))
      [⋀^Fin k]→ₗ[ℂ]
        (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :=
  ((k.factorial : ℂ)⁻¹) •
    MultilinearMap.alternatization
      (secondQuantizationMultilinear (k := k) A)

/--
Intrinsic fermionic second quantization `dΓ(A)` on the `k`-particle
exterior-power sector.
-/
def secondQuantization {r k : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) →ₗ[ℂ]
      (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :=
  exteriorPower.alternatingMapLinearEquiv
    (secondQuantizationAlternating (k := k) A)

theorem secondQuantizationMultilinear_apply_eigen {r k : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (v : Fin k → FiniteIndexClockSpace (Fin r))
    (lam : Fin k → ℂ)
    (heig : ∀ i, A (v i) = lam i • v i) :
    secondQuantizationMultilinear A v =
      (∑ i, lam i) • exteriorPower.ιMulti ℂ k v := by
  unfold secondQuantizationMultilinear
  rw [MultilinearMap.sum_apply]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [MultilinearMap.compLinearMap_apply]
  have hslot :
      (fun j => fermionicSlotLinearMap A i j (v j)) =
        Function.update v i (A (v i)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [fermionicSlotLinearMap]
    · simp [fermionicSlotLinearMap, hji]
  rw [hslot, heig i]
  calc
    exteriorPower.ιMulti ℂ k
          (Function.update v i (lam i • v i)) =
        lam i • exteriorPower.ιMulti ℂ k
          (Function.update v i (v i)) :=
      AlternatingMap.map_update_smul
        (exteriorPower.ιMulti ℂ k) v i (lam i) (v i)
    _ = lam i • exteriorPower.ιMulti ℂ k v := by
      congr 1
      apply congrArg (exteriorPower.ιMulti ℂ k)
      funext j
      by_cases hji : j = i <;> simp [hji]

theorem secondQuantizationAlternating_apply_eigen {r k : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (v : Fin k → FiniteIndexClockSpace (Fin r))
    (lam : Fin k → ℂ)
    (heig : ∀ i, A (v i) = lam i • v i) :
    secondQuantizationAlternating A v =
      (∑ i, lam i) • exteriorPower.ιMulti ℂ k v := by
  unfold secondQuantizationAlternating
  rw [AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply]
  have hperm : ∀ σ : Equiv.Perm (Fin k),
      secondQuantizationMultilinear A (fun j => v (σ j)) =
        (∑ i, lam i) •
          (Equiv.Perm.sign σ : ℂ) •
            exteriorPower.ιMulti ℂ k v := by
    intro σ
    change secondQuantizationMultilinear A (v ∘ σ) =
      (∑ i, lam i) •
        (Equiv.Perm.sign σ : ℂ) •
          exteriorPower.ιMulti ℂ k v
    rw [secondQuantizationMultilinear_apply_eigen
      A (v ∘ σ) (lam ∘ σ)]
    · change (∑ i, lam (σ i)) •
          exteriorPower.ιMulti ℂ k (v ∘ σ) =
        (∑ i, lam i) •
          (Equiv.Perm.sign σ : ℂ) •
            exteriorPower.ιMulti ℂ k v
      rw [Equiv.sum_comp σ lam]
      rw [(exteriorPower.ιMulti ℂ k).map_perm]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simp [hs]
      · rw [hs, Units.neg_smul]
        have hcast : ((((-1 : ℤˣ) : ℤ) : ℂ)) = -1 := by norm_num
        rw [hcast]
        have hinner :
            ((-1 : ℂ) • exteriorPower.ιMulti ℂ k v) =
              -(exteriorPower.ιMulti ℂ k v) := by
          simpa only [one_smul] using
            (neg_smul (1 : ℂ) (exteriorPower.ιMulti ℂ k v))
        rw [one_smul, hinner, smul_neg]
    · intro i
      simpa only [Function.comp_apply] using heig (σ i)
  simp only [MultilinearMap.domDomCongr_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ) •
          secondQuantizationMultilinear A (fun j => v (σ j)) =
        (∑ i, lam i) • exteriorPower.ιMulti ℂ k v := by
    intro σ
    rw [hperm σ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · rw [hs, Units.neg_smul]
      have hcast : ((((-1 : ℤˣ) : ℤ) : ℂ)) = -1 := by norm_num
      rw [hcast]
      have hinner :
          ((-1 : ℂ) • exteriorPower.ιMulti ℂ k v) =
            -(exteriorPower.ιMulti ℂ k v) := by
        simpa only [one_smul] using
          (neg_smul (1 : ℂ) (exteriorPower.ιMulti ℂ k v))
      rw [one_smul, hinner, smul_neg, neg_neg]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  rw [Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  change ((k.factorial : ℂ)⁻¹) •
      ((k.factorial : ℂ) •
        ((∑ i, lam i) • exteriorPower.ιMulti ℂ k v)) =
    (∑ i, lam i) • exteriorPower.ιMulti ℂ k v
  rw [← mul_smul, inv_mul_cancel₀]
  · simp
  · exact_mod_cast Nat.factorial_ne_zero k

/-- Slater determinants of one-particle eigenvectors have summed energy. -/
theorem secondQuantization_apply_ιMulti_eigen {r k : ℕ}
    (A : FiniteIndexClockSpace (Fin r) →ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (v : Fin k → FiniteIndexClockSpace (Fin r))
    (lam : Fin k → ℂ)
    (heig : ∀ i, A (v i) = lam i • v i) :
    secondQuantization A (exteriorPower.ιMulti ℂ k v) =
      (∑ i, lam i) • exteriorPower.ιMulti ℂ k v := by
  rw [secondQuantization,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact secondQuantizationAlternating_apply_eigen A v lam heig

/-- Increasing enumeration of a fixed-cardinality subset. -/
def powersetOrderEquiv {r k : ℕ}
    (S : Set.powersetCard (Fin r) k) :
    Fin k ≃ {j : Fin r // j ∈ S.val} where
  toFun i :=
    ⟨Set.powersetCard.ofFinEmbEquiv.symm S i,
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        S _).mp ⟨i, rfl⟩⟩
  invFun j :=
    Classical.choose
      ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        S j.val).mpr j.prop)
  left_inv i := by
    apply (Set.powersetCard.ofFinEmbEquiv.symm S).injective
    exact Classical.choose_spec
      ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        S (Set.powersetCard.ofFinEmbEquiv.symm S i)).mpr
          ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
            S _).mp ⟨i, rfl⟩))
  right_inv j := by
    apply Subtype.ext
    exact Classical.choose_spec
      ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        S j.val).mpr j.prop)

/-- Ordered sum and finite-subset sum are the same occupied energy. -/
theorem orderedFermionicSubsetEnergy_eq {r k : ℕ}
    (energy : Fin r → ℝ)
    (S : Set.powersetCard (Fin r) k) :
    (∑ i : Fin k,
        energy (Set.powersetCard.ofFinEmbEquiv.symm S i)) =
      fermionicSubsetEnergy energy S := by
  unfold fermionicSubsetEnergy
  rw [Finset.sum_subtype S.val (fun _ => Iff.rfl) energy]
  exact Fintype.sum_equiv (powersetOrderEquiv S)
    _ _ (fun _ => rfl)

/-- Diagonal free-fermion Hamiltonian on a fixed particle-number sector. -/
def diagonalFermionicSectorHamiltonian {r k : ℕ}
    (energy : Fin r → ℝ) :
    (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) →ₗ[ℂ]
      (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :=
  (fermionicSectorBasis r k).constr ℂ
    (fun S => (fermionicSubsetEnergy energy S : ℂ) •
      fermionicSectorBasis r k S)

@[simp] theorem diagonalFermionicSectorHamiltonian_basis {r k : ℕ}
    (energy : Fin r → ℝ)
    (S : Set.powersetCard (Fin r) k) :
    diagonalFermionicSectorHamiltonian energy
        (fermionicSectorBasis r k S) =
      (fermionicSubsetEnergy energy S : ℂ) •
        fermionicSectorBasis r k S := by
  exact Module.Basis.constr_basis _ _ _ _

/-- Exterior-power linear equivalence induced by a one-particle equivalence. -/
def exteriorPowerLinearEquiv {r k : ℕ}
    (U : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) ≃ₗ[ℂ]
      (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) where
  toLinearMap := exteriorPower.map k U.toLinearMap
  invFun := exteriorPower.map k U.symm.toLinearMap
  left_inv x := by
    change
      ((exteriorPower.map k U.symm.toLinearMap).comp
        (exteriorPower.map k U.toLinearMap)) x = x
    rw [← exteriorPower.map_comp]
    simp
  right_inv x := by
    change
      ((exteriorPower.map k U.toLinearMap).comp
        (exteriorPower.map k U.symm.toLinearMap)) x = x
    rw [← exteriorPower.map_comp]
    simp

/--
Free-fermion sector Hamiltonian obtained by transporting the common
subset-sum diagonal Hamiltonian through the induced exterior equivalence.
-/
def fermionicSectorHamiltonian {r k : ℕ}
    (energy : Fin r → ℝ)
    (U : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) →ₗ[ℂ]
      (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :=
  (exteriorPowerLinearEquiv U).symm.toLinearMap.comp
    ((diagonalFermionicSectorHamiltonian energy).comp
      (exteriorPowerLinearEquiv U).toLinearMap)

theorem fermionicSectorHamiltonian_intertwines {r k : ℕ}
    (energy : Fin r → ℝ)
    (U : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (x : ⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :
    exteriorPowerLinearEquiv U
        (fermionicSectorHamiltonian energy U x) =
      diagonalFermionicSectorHamiltonian energy
        (exteriorPowerLinearEquiv U x) := by
  simp [fermionicSectorHamiltonian]

/-- Slater eigenvector in the physical one-particle basis. -/
def fermionicSectorEigenvector {r k : ℕ}
    (U : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (S : Set.powersetCard (Fin r) k) :
    ⋀[ℂ]^k (FiniteIndexClockSpace (Fin r)) :=
  (exteriorPowerLinearEquiv U).symm
    (fermionicSectorBasis r k S)

theorem fermionicSectorHamiltonian_eigenvector {r k : ℕ}
    (energy : Fin r → ℝ)
    (U : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (S : Set.powersetCard (Fin r) k) :
    fermionicSectorHamiltonian energy U
        (fermionicSectorEigenvector U S) =
      (fermionicSubsetEnergy energy S : ℂ) •
        fermionicSectorEigenvector U S := by
  apply (exteriorPowerLinearEquiv U).injective
  simp [fermionicSectorEigenvector,
    fermionicSectorHamiltonian_intertwines]

/-- Complete Slater eigenbasis of the transported sector Hamiltonian. -/
def fermionicSectorEigenbasis {r k : ℕ}
    (U : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    Basis (Set.powersetCard (Fin r) k) ℂ
      (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r))) :=
  (fermionicSectorBasis r k).map
    (exteriorPowerLinearEquiv U).symm

@[simp] theorem fermionicSectorEigenbasis_apply {r k : ℕ}
    (U : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r))
    (S : Set.powersetCard (Fin r) k) :
    fermionicSectorEigenbasis U S =
      fermionicSectorEigenvector U S := by
  rfl

/--
Any two free-fermion sector Hamiltonians built from the same one-particle
energy list are similar.  The intertwiner is the exterior lift of the
change of one-particle eigenbasis.
-/
theorem fermionicSectorHamiltonian_similar {r k : ℕ}
    (energy : Fin r → ℝ)
    (U V : FiniteIndexClockSpace (Fin r) ≃ₗ[ℂ]
      FiniteIndexClockSpace (Fin r)) :
    let W :=
      (exteriorPowerLinearEquiv (k := k) U).trans
        (exteriorPowerLinearEquiv (k := k) V).symm
    W.toLinearMap.comp
        (fermionicSectorHamiltonian (k := k) energy U) =
      (fermionicSectorHamiltonian (k := k) energy V).comp
        W.toLinearMap := by
  dsimp only
  ext x
  simp [fermionicSectorHamiltonian]

/--
Every fixed-protocol member, at every particle number, has a complete
Slater eigenbasis with the same subset-sum energy list.  This includes the
perfect-return endpoint because the exterior lift needs no positive-weight
cyclicity assumption.
-/
theorem fixedProtocol_fullFermionicSpectrum {T : ℝ} (n k : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ∃ b : Basis (Set.powersetCard (Fin (n + 1)) k) ℂ
        (⋀[ℂ]^k (ClockSpace n)),
      ∀ S : Set.powersetCard (Fin (n + 1)) k,
        fermionicSectorHamiltonian (k := k)
            (angularEnergy T n) U.toLinearEquiv (b S) =
          (fermionicSubsetEnergy (angularEnergy T n) S : ℂ) •
            b S := by
  refine ⟨fermionicSectorEigenbasis U.toLinearEquiv, ?_⟩
  intro S
  exact fermionicSectorHamiltonian_eigenvector
    (angularEnergy T n) U.toLinearEquiv S

/-! ## Intrinsic many-body spectrum of the fixed protocol -/

/-- Physical one-particle eigenvectors of a fixed-protocol Hamiltonian. -/
theorem fixedProtocolHamiltonian_standard_eigenvector
    (T : ℝ) (n : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n)
    (j : Fin (n + 1)) :
    (fixedProtocolHamiltonian T n U).toLinearMap
        (U.symm (standardOneParticleBasis (n + 1) j)) =
      (angularEnergy T n j : ℂ) •
        U.symm (standardOneParticleBasis (n + 1) j) := by
  apply U.injective
  change U (fixedProtocolHamiltonian T n U
      (U.symm (standardOneParticleBasis (n + 1) j))) =
    U ((angularEnergy T n j : ℂ) •
      U.symm (standardOneParticleBasis (n + 1) j))
  rw [fixedProtocolHamiltonian_intertwines, map_smul,
    LinearIsometryEquiv.apply_symm_apply]
  ext i
  by_cases h : i = j
  · subst i
    simp [scaledClockHamiltonian,
      standardOneParticleBasis,
      EuclideanSpace.basisFun_apply]
  · simp [scaledClockHamiltonian,
      standardOneParticleBasis,
      EuclideanSpace.basisFun_apply, h]

/-- Complete Slater basis built from the physical one-particle eigenbasis. -/
def fixedProtocolSecondQuantizedEigenbasis
    (n k : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    Basis (Set.powersetCard (Fin (n + 1)) k) ℂ
      (⋀[ℂ]^k (ClockSpace n)) :=
  ((standardOneParticleBasis (n + 1)).map
    U.toLinearEquiv.symm).exteriorPower k

/--
The intrinsic second quantization of every fixed-protocol Hamiltonian has
a complete Slater eigenbasis and the common subset-sum energy list.  This
proves the many-body spectrum rather than defining an operator by
transporting a desired diagonal list.
-/
theorem fixedProtocol_intrinsicFermionicSpectrum
    (T : ℝ) (n k : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ∃ b : Basis (Set.powersetCard (Fin (n + 1)) k) ℂ
        (⋀[ℂ]^k (ClockSpace n)),
      ∀ S : Set.powersetCard (Fin (n + 1)) k,
        secondQuantization
            (k := k) (fixedProtocolHamiltonian T n U).toLinearMap
            (b S) =
          (fermionicSubsetEnergy (angularEnergy T n) S : ℂ) •
            b S := by
  refine ⟨fixedProtocolSecondQuantizedEigenbasis n k U, ?_⟩
  intro S
  rw [← orderedFermionicSubsetEnergy_eq]
  rw [fixedProtocolSecondQuantizedEigenbasis,
    exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  push_cast
  apply secondQuantization_apply_ιMulti_eigen
    (lam := fun i =>
      (angularEnergy T n
        (Set.powersetCard.ofFinEmbEquiv.symm S i) : ℂ))
  intro i
  exact fixedProtocolHamiltonian_standard_eigenvector
    T n U (Set.powersetCard.ofFinEmbEquiv.symm S i)

/--
Universal fixed-protocol law for nearest-neighbour free fermions.  One
finite one-particle spectrum, one preparation, and one return test admit
every terminal probability in `[0,1]` while an arbitrarily long earlier
record and arbitrarily many moments are common.  At every particle number,
the intrinsic second-quantized Hamiltonian has the same complete subset-sum
spectrum.
-/
theorem one_fixed_nearestNeighbor_freeFermion_every_future_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      ‖fixedClock n‖ = 1 ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        ∃ U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n,
          U (fixedClock n) =
              interpolatedClock n (Real.sqrt p) ∧
          NearestNeighborHamiltonian
            (fixedProtocolHamiltonian T n U) ∧
          (∀ q : ℕ, q ≤ m →
            inner ℂ (fixedClock n)
                (((fixedProtocolHamiltonian T n U) ^ q)
                  (fixedClock n)) =
              (∑ j : Fin (n + 1),
                fullWeight n j *
                  angularEnergy T n j ^ q : ℝ)) ∧
          ContinuousLinearMap.adjoint
              (fixedProtocolHamiltonian T n U) =
            fixedProtocolHamiltonian T n U ∧
          (∀ x : ClockSpace n,
            U (fixedProtocolHamiltonian T n U x) =
              scaledClockHamiltonian T n (U x)) ∧
          (∀ t : ℝ, |t| ≤ H →
            |fixedProtocolProbability
                T n (Real.sqrt p) t U -
              scaledFullProbability T n t| < δ) ∧
          fixedProtocolProbability
              T n (Real.sqrt p) T U = p ∧
          ∀ k : ℕ,
            ∃ b : Basis (Set.powersetCard (Fin (n + 1)) k) ℂ
                (⋀[ℂ]^k (ClockSpace n)),
              ∀ S : Set.powersetCard (Fin (n + 1)) k,
                secondQuantization
                    (k := k)
                    (fixedProtocolHamiltonian T n U).toLinearMap
                    (b S) =
                  (fermionicSubsetEnergy
                    (angularEnergy T n) S : ℂ) • b S := by
  obtain ⟨n, hmn, hnorm, hall⟩ :=
    one_fixed_nearestNeighbor_chain_every_future_probability
      m T H hT hH0 hHT hδ
  refine ⟨n, hmn, hnorm, ?_⟩
  intro p hp
  obtain ⟨U, hU, hNN, hmom, hAdj, hInter, hwindow, htarget⟩ :=
    hall p hp
  refine ⟨U, hU, hNN, hmom, hAdj, hInter, hwindow,
    htarget, ?_⟩
  intro k
  exact fixedProtocol_intrinsicFermionicSpectrum T n k U

end RHTower.ParityForecast
