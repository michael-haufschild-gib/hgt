/-
# The several-variable sufficiency step

Adding the several-variable micro-spectrum block to a truncated pencil produces a finite-rank pencil
whose power traces below the order are the truncation's own plus exactly the prescribed homogeneous
defects, and which stays within an arbitrarily small Schatten distance of the truncation.  This is
the several-variable form of the step that `OperatorDeterminantSufficiency` performs in one
variable.

Main results:
* `hasRankLE_finsetSum`, `hasRankLE_pencilOperator` — a pencil of finite-rank coefficients has
  finite rank at every parameter.
* `pencilOperator_add`, `pencilOperator_sub` — the pencil construction is additive.
* `exists_finiteRankPencil_lowTrace` — **the several-variable sufficiency step**.
-/
import GaloisForLFunctions.HTGeometry.PencilMicroBlock

open ContinuousLinearMap Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem hasRankLE_finsetSum {ι : Type*} (s : Finset ι) (X : ι → (H →L[ℂ] H)) {N : ℕ}
    (hX : ∀ i ∈ s, HasRankLE (X i) N) : HasRankLE (∑ i ∈ s, X i) (s.card * N) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hasRankLE_zero (H := H) 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.succ_mul]
      have hrest := ih fun i hi => hX i (Finset.mem_insert_of_mem hi)
      have hstep := (hrest.add (hX a (Finset.mem_insert_self a s)))
      have hcomm : X a + ∑ i ∈ s, X i = (∑ i ∈ s, X i) + X a := by abel
      rw [hcomm]
      exact hstep

omit [CompleteSpace H] in
theorem hasRankLE_pencilOperator {d N : ℕ} {X : Fin d → (H →L[ℂ] H)}
    (hX : ∀ j, HasRankLE (X j) N) (v : Fin d → ℂ) :
    HasRankLE (pencilOperator X v) (d * N) := by
  have h := hasRankLE_finsetSum (Finset.univ : Finset (Fin d))
    (fun j => v j • X j) (fun j _ => (hX j).smul (v j))
  rwa [Finset.card_univ, Fintype.card_fin] at h

omit [CompleteSpace H] in
theorem pencilOperator_add {d : ℕ} (X Y : Fin d → (H →L[ℂ] H)) (v : Fin d → ℂ) :
    pencilOperator (fun j => X j + Y j) v = pencilOperator X v + pencilOperator Y v := by
  rw [pencilOperator, pencilOperator, pencilOperator, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_add]

/-- **The several-variable sufficiency step.**  Beside a truncated pencil there is a finite-rank
pencil whose power traces below the order are the truncation's own plus exactly the prescribed
homogeneous defects, at arbitrarily small Schatten distance from the truncation. -/
theorem exists_finiteRankPencil_lowTrace (hH : ¬ FiniteDimensional ℂ H) {p d : ℕ} (hp : 0 < p)
    (B : Fin d → (H →L[ℂ] H)) (n : ℕ) (Q : ℕ → (Fin d → ℂ) → ℂ)
    (hQ : ∀ k, 1 ≤ k → k ≤ p - 1 → Q k ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Fin d → (H →L[ℂ] H),
      (∀ j, ∃ N : ℕ, HasRankLE (F j) N) ∧
      (∀ (v : Fin d → ℂ) (k : ℕ), 1 ≤ k → k ≤ p - 1 →
        opTrace ((pencilOperator F v) ^ k)
          = opTrace ((pencilOperator (fun j => greedyTrunc (B j) n) v) ^ k) + Q k v) ∧
      (∀ v : Fin d → ℂ,
        schattenNorm (p : ℝ)
            (pencilOperator F v - pencilOperator (fun j => greedyTrunc (B j) n) v) ^ (p : ℝ)
          ≤ ε * ‖v‖ ^ p) := by
  obtain ⟨C, hCrank, hAC, hCA, hCtrace, hCcost⟩ :=
    exists_pencilMicroBlock hH hp B n Q hQ hε
  refine ⟨fun j => greedyTrunc (B j) n + C j, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨N, hN⟩ := hCrank j
    exact ⟨n + N, (hasRankLE_greedyTrunc (B j) n).add hN⟩
  · intro v k hk1 hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j, HasRankLE (C j) N := by
      classical
      choose Nf hNf using hCrank
      exact ⟨Finset.univ.sup Nf, fun j => (hNf j).mono (Finset.le_sup (Finset.mem_univ j))⟩
    rw [pencilOperator_add]
    rw [opTrace_add_pow_succ_of_orthogonal
      (hasRankLE_pencilOperator (fun j => hasRankLE_greedyTrunc (B j) n) v)
      (hasRankLE_pencilOperator hN v) (hAC v) (hCA v) k']
    rw [hCtrace v (k' + 1) hk1 hk]
  · intro v
    have hsub : pencilOperator (fun j => greedyTrunc (B j) n + C j) v
        - pencilOperator (fun j => greedyTrunc (B j) n) v = pencilOperator C v := by
      rw [pencilOperator_add]
      abel
    rw [hsub]
    exact hCcost v

end

end GaloisForLFunctions.HTGeometry
