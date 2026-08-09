import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.FittingPresentation

/-!
# Presentation independence of the determinant ideal

The determinant ideal of a finite generating family does not depend on the family.  Two finite
generating families are compared through their concatenation, which is reached from either one by
adjoining generators one at a time and reindexing.

* `reindexGen`, `presDetIdeal_reindexGen` — invariance under reindexing the generators;
* `addGens`, `addGens_apply` — adjoining a finite list of generators, and its closed form;
* `presDetIdeal_addGens` — adjoining generators does not change the determinant ideal;
* `presDetIdeal_eq_of_surjective` — any two finite generating families give the same ideal;
* `fittingIdealZero` — the zeroth Fitting ideal of a module, and
  `fittingIdealZero_eq_presDetIdeal`, which computes it from an arbitrary finite generating family.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u v

section Reindex

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Reindex a finite generating family along an equivalence of index sets. -/
def reindexGen {p q : ℕ} (π : (Fin q → R) →ₗ[R] M) (e : Fin p ≃ Fin q) :
    (Fin p → R) →ₗ[R] M :=
  π ∘ₗ LinearMap.funLeft R R e.symm

@[simp] theorem reindexGen_apply {p q : ℕ} (π : (Fin q → R) →ₗ[R] M) (e : Fin p ≃ Fin q)
    (x : Fin p → R) : reindexGen π e x = π fun i => x (e.symm i) := rfl

theorem reindexGen_surjective {p q : ℕ} {π : (Fin q → R) →ₗ[R] M} (e : Fin p ≃ Fin q)
    (hπ : Function.Surjective π) : Function.Surjective (reindexGen π e) := by
  intro m
  obtain ⟨x, hx⟩ := hπ m
  exact ⟨fun i => x (e i), by simpa using hx⟩

theorem presDetIdeal_reindexGen_le {p q : ℕ} (π : (Fin q → R) →ₗ[R] M) (e : Fin p ≃ Fin q) :
    presDetIdeal (reindexGen π e) ≤ presDetIdeal π := by
  refine presDetIdeal_le fun A hA => ?_
  have hrel : IsRelMatrix π (A.submatrix e.symm e.symm) := by
    intro j
    have := hA (e.symm j)
    simpa using this
  have hdet : (A.submatrix e.symm e.symm).det = A.det :=
    Matrix.det_submatrix_equiv_self e.symm A
  rw [← hdet]
  exact det_mem_presDetIdeal hrel

/-- Reindexing the generators does not change the determinant ideal. -/
theorem presDetIdeal_reindexGen {p q : ℕ} (π : (Fin q → R) →ₗ[R] M) (e : Fin p ≃ Fin q) :
    presDetIdeal (reindexGen π e) = presDetIdeal π := by
  refine le_antisymm (presDetIdeal_reindexGen_le π e) ?_
  have hback : reindexGen (reindexGen π e) e.symm = π := by
    ext x
    simp
  calc presDetIdeal π = presDetIdeal (reindexGen (reindexGen π e) e.symm) := by rw [hback]
    _ ≤ presDetIdeal (reindexGen π e) := presDetIdeal_reindexGen_le _ _

end Reindex

section AddGens

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}

/-- Adjoin a finite list of generators to a finite generating family. -/
def addGens (π : (Fin n → R) →ₗ[R] M) :
    ∀ (m : ℕ), (Fin m → M) → (Fin (n + m) → R) →ₗ[R] M
  | 0, _ => π
  | (m + 1), g => extendGen (addGens π m fun j => g j.castSucc) (g (Fin.last m))

@[simp] theorem addGens_zero (π : (Fin n → R) →ₗ[R] M) (g : Fin 0 → M) :
    addGens π 0 g = π := rfl

@[simp] theorem addGens_succ (π : (Fin n → R) →ₗ[R] M) (m : ℕ) (g : Fin (m + 1) → M) :
    addGens π (m + 1) g = extendGen (addGens π m fun j => g j.castSucc) (g (Fin.last m)) := rfl

theorem addGens_surjective {π : (Fin n → R) →ₗ[R] M} (hπ : Function.Surjective π) :
    ∀ (m : ℕ) (g : Fin m → M), Function.Surjective (addGens π m g)
  | 0, _ => hπ
  | (m + 1), _g => extendGen_surjective (addGens_surjective hπ m _) _

/-- **Adjoining generators does not change the determinant ideal.** -/
theorem presDetIdeal_addGens {π : (Fin n → R) →ₗ[R] M} (hπ : Function.Surjective π) :
    ∀ (m : ℕ) (g : Fin m → M), presDetIdeal (addGens π m g) = presDetIdeal π
  | 0, _ => rfl
  | (m + 1), g => by
      rw [addGens_succ, presDetIdeal_extendGen (addGens_surjective hπ m _),
        presDetIdeal_addGens hπ m]

theorem addGens_apply (π : (Fin n → R) →ₗ[R] M) :
    ∀ (m : ℕ) (g : Fin m → M) (x : Fin (n + m) → R),
      addGens π m g x = π (fun i => x (Fin.castAdd m i)) + ∑ j, x (Fin.natAdd n j) • g j
  | 0, g, x => by
      have hx : (fun i => x (Fin.castAdd 0 i)) = x := by
        funext i; congr 1
      rw [addGens_zero, hx]
      simp
  | (m + 1), g, x => by
      rw [addGens_succ, extendGen_apply, addGens_apply π m]
      have h1 : ∀ i : Fin n, (Fin.castAdd m i).castSucc = Fin.castAdd (m + 1) i := by
        intro i; exact Fin.ext rfl
      have h2 : ∀ j : Fin m, (Fin.natAdd n j).castSucc = Fin.natAdd n j.castSucc := by
        intro j; exact Fin.ext rfl
      have h3 : (Fin.last (n + m)) = Fin.natAdd n (Fin.last m) := by
        exact Fin.ext (by simp)
      rw [Fin.sum_univ_castSucc (f := fun j : Fin (m + 1) => x (Fin.natAdd n j) • g j)]
      simp only [h1, h2, h3]
      rw [add_assoc]

end AddGens

section Invariance

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem linearMap_eq_sum_single {m : ℕ} (f : (Fin m → R) →ₗ[R] M) (y : Fin m → R) :
    f y = ∑ j, y j • f (Pi.single j 1) := by
  have hy : y = ∑ j, y j • (Pi.single j 1 : Fin m → R) := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  conv_lhs => rw [hy]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul f _ _

/-- The concatenation of two finite generating families. -/
theorem addGens_std_apply {n m : ℕ} (π : (Fin n → R) →ₗ[R] M) (π' : (Fin m → R) →ₗ[R] M)
    (x : Fin (n + m) → R) :
    addGens π m (fun j => π' (Pi.single j 1)) x
      = π (fun i => x (Fin.castAdd m i)) + π' (fun j => x (Fin.natAdd n j)) := by
  rw [addGens_apply]
  congr 1
  exact (linearMap_eq_sum_single π' _).symm

/-- The block swap `Fin (n+m) ≃ Fin (m+n)`. -/
def blockSwap (n m : ℕ) : Fin (n + m) ≃ Fin (m + n) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin m))).trans finSumFinEquiv

theorem blockSwap_symm_castAdd (n m : ℕ) (j : Fin m) :
    (blockSwap n m).symm (Fin.castAdd n j) = Fin.natAdd n j := by
  simp [blockSwap]

theorem blockSwap_symm_natAdd (n m : ℕ) (i : Fin n) :
    (blockSwap n m).symm (Fin.natAdd m i) = Fin.castAdd m i := by
  simp [blockSwap]

/-- **Presentation independence.**  Any two finite generating families of `M` define the same
determinant ideal. -/
theorem presDetIdeal_eq_of_surjective {n m : ℕ} {π : (Fin n → R) →ₗ[R] M}
    {π' : (Fin m → R) →ₗ[R] M} (hπ : Function.Surjective π) (hπ' : Function.Surjective π') :
    presDetIdeal π = presDetIdeal π' := by
  set ψ := addGens π m (fun j => π' (Pi.single j 1)) with hψ
  set ψ' := addGens π' n (fun i => π (Pi.single i 1)) with hψ'
  have hcomp : reindexGen ψ' (blockSwap n m) = ψ := by
    refine LinearMap.ext fun x => ?_
    rw [reindexGen_apply, hψ', hψ, addGens_std_apply, addGens_std_apply]
    simp only [blockSwap_symm_castAdd, blockSwap_symm_natAdd]
    rw [add_comm]
  calc presDetIdeal π = presDetIdeal ψ := (presDetIdeal_addGens hπ m _).symm
    _ = presDetIdeal (reindexGen ψ' (blockSwap n m)) := by rw [hcomp]
    _ = presDetIdeal ψ' := presDetIdeal_reindexGen _ _
    _ = presDetIdeal π' := presDetIdeal_addGens hπ' n _

variable (R M)

/-- **The zeroth Fitting ideal** of a module: the determinant ideal of any finite generating
family, taken as the supremum over all of them. -/
def fittingIdealZero : Ideal R :=
  ⨆ (n : ℕ) (π : (Fin n → R) →ₗ[R] M) (_ : Function.Surjective π), presDetIdeal π

variable {R M}

/-- The zeroth Fitting ideal is computed by any finite generating family. -/
theorem fittingIdealZero_eq_presDetIdeal {n : ℕ} {π : (Fin n → R) →ₗ[R] M}
    (hπ : Function.Surjective π) : fittingIdealZero R M = presDetIdeal π := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun m => iSup_le fun π' => iSup_le fun hπ' => ?_
    exact le_of_eq (presDetIdeal_eq_of_surjective hπ' hπ)
  · exact le_iSup_of_le n (le_iSup_of_le π (le_iSup_of_le hπ le_rfl))

end Invariance

end GaloisForLFunctions.HTGeometry.DerivedSelection
