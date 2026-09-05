/-
# The several-variable micro-spectrum block

The block that corrects the low power traces of a truncated pencil must itself be a *pencil*: its
eigenvalues are linear forms in the parameter, so the block operator is linear in the parameter and
its coefficients are the blocks of the coordinate forms.  Placed beside the whole family of greedy
truncations it annihilates the truncated pencil in both orders, its power traces below the order are
exactly the prescribed homogeneous defects, and its Schatten cost is arbitrarily small.

Main results:
* `msIndex`, `ms_sum_eq_finSum` — listing a multiset as a finite family.
* `blockOp_finsetSum`, `blockOp_pencil` — **the diagonal block of a family of linear forms is a
  linear pencil**.
* `exists_pencilMicroBlock` — **the several-variable micro-spectrum block**.
-/
import GaloisForLFunctions.HTGeometry.PencilBlockPlacement
import GaloisForLFunctions.HTGeometry.PencilTracePolynomial
import GaloisForLFunctions.HTGeometry.BlockOperatorSchatten

open ContinuousLinearMap Finset
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-! ## Listing a multiset -/

/-- The listing of a multiset as a family indexed by a finite type. -/
def msIndex {α : Type*} (S : Multiset α) : Fin S.toList.length → α := fun i => S.toList.get i

theorem ms_sum_eq_finSum {α β : Type*} [AddCommMonoid β] (S : Multiset α) (f : α → β) :
    (S.map f).sum = ∑ i, f (msIndex S i) := by
  conv_lhs => rw [← Multiset.coe_toList S]
  rw [Multiset.map_coe, Multiset.sum_coe]
  have hlist : S.toList.map f
      = List.ofFn (fun i : Fin S.toList.length => f (msIndex S i)) := by
    rw [show (fun i : Fin S.toList.length => f (msIndex S i)) = f ∘ S.toList.get from rfl,
      ← List.map_ofFn, List.ofFn_get]
  rw [hlist, List.sum_ofFn]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The block of a family of linear forms is a pencil -/

omit [CompleteSpace H] in
theorem blockOp_finsetSum {m : ℕ} (e : Fin m → H) {ι : Type*} (s : Finset ι)
    (a : ι → Fin m → ℂ) :
    blockOp e (fun i => ∑ j ∈ s, a j i) = ∑ j ∈ s, blockOp e (a j) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [blockOp_apply, _root_.sum_apply]
  have hterm : ∀ i : Fin m, ((∑ j ∈ s, a j i) * ⟪e i, x⟫_ℂ) • e i
      = ∑ j ∈ s, ((a j i * ⟪e i, x⟫_ℂ) • e i) := by
    intro i
    rw [Finset.sum_mul, Finset.sum_smul]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hterm i,
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (blockOp_apply e (a j) x).symm

omit [CompleteSpace H] in
theorem blockOp_smul_entries {m : ℕ} (e : Fin m → H) (c : ℂ) (μ : Fin m → ℂ) :
    blockOp e (fun i => c * μ i) = c • blockOp e μ := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [blockOp_apply, smul_apply, blockOp_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; ring_nf

omit [CompleteSpace H] in
/-- **The diagonal block of a family of linear forms is a linear pencil**, with the blocks of the
coordinate forms as its coefficients. -/
theorem blockOp_pencil {m d : ℕ} (e : Fin m → H) (μ : Fin m → ((Fin d → ℂ) →L[ℂ] ℂ))
    (v : Fin d → ℂ) :
    blockOp e (fun i => μ i v)
      = pencilOperator (fun j => blockOp e fun i => μ i (Pi.single j 1)) v := by
  classical
  have hcoord : ∀ i : Fin m, μ i v = ∑ j, v j * μ i (Pi.single j 1) := by
    intro i
    have hv : v = ∑ j, v j • (Pi.single j (1 : ℂ) : Fin d → ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  have hfun : (fun i => μ i v) = fun i => ∑ j, v j * μ i (Pi.single j 1) := funext hcoord
  rw [hfun, blockOp_finsetSum e Finset.univ (fun j i => v j * μ i (Pi.single j 1)),
    pencilOperator]
  exact Finset.sum_congr rfl fun j _ => blockOp_smul_entries e (v j) _

/-! ## The several-variable micro-spectrum block -/

/-- **The several-variable micro-spectrum block.**  Beside a family of greedy truncations there is a
finite-rank *pencil* which annihilates the truncated pencil in both orders, whose power traces below
the order are exactly the prescribed homogeneous defects, and whose Schatten cost is arbitrarily
small. -/
theorem exists_pencilMicroBlock (hH : ¬ FiniteDimensional ℂ H) {p d : ℕ} (hp : 0 < p)
    (B : Fin d → (H →L[ℂ] H)) (n : ℕ) (T : ℕ → (Fin d → ℂ) → ℂ)
    (hT : ∀ k, 1 ≤ k → k ≤ p - 1 → T k ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Fin d → (H →L[ℂ] H),
      (∀ j, ∃ N : ℕ, HasRankLE (C j) N) ∧
      (∀ v : Fin d → ℂ,
        pencilOperator (fun j => greedyTrunc (B j) n) v * pencilOperator C v = 0) ∧
      (∀ v : Fin d → ℂ,
        pencilOperator C v * pencilOperator (fun j => greedyTrunc (B j) n) v = 0) ∧
      (∀ (v : Fin d → ℂ) (k : ℕ), 1 ≤ k → k ≤ p - 1 →
        opTrace ((pencilOperator C v) ^ k) = T k v) ∧
      (∀ v : Fin d → ℂ,
        schattenNorm (p : ℝ) (pencilOperator C v) ^ (p : ℝ) ≤ ε * ‖v‖ ^ p) := by
  classical
  obtain ⟨S, hSmom, hScost⟩ :=
    exists_pencilForms_moment_realization (V := Fin d → ℂ) p (p - 1) (by omega) T hT ε hε
  obtain ⟨e, he, he0, he1⟩ :=
    exists_orthonormal_beside_greedyFamily hH B n S.toList.length
  refine ⟨fun j => blockOp e (fun i => msIndex S i (Pi.single j 1)), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨S.toList.length, hasRankLE_blockOp e _⟩
  · intro v
    show pencilOperator (fun j => greedyTrunc (B j) n) v ∘L
        pencilOperator (fun j => blockOp e fun i => msIndex S i (Pi.single j 1)) v = 0
    rw [← blockOp_pencil e (msIndex S) v]
    exact comp_blockOp_eq_zero _
      (fun i => pencilOperator_apply_eq_zero (fun j => he0 j i) v) _
  · intro v
    show pencilOperator (fun j => blockOp e fun i => msIndex S i (Pi.single j 1)) v ∘L
        pencilOperator (fun j => greedyTrunc (B j) n) v = 0
    rw [← blockOp_pencil e (msIndex S) v]
    exact blockOp_comp_eq_zero _
      (fun i x => inner_pencilOperator_eq_zero (fun j y => he1 j i y) v x) _
  · intro v k hk1 hk
    rw [← blockOp_pencil e (msIndex S) v]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [blockOp_pow he _ k', opTrace_blockOp he]
    rw [← ms_sum_eq_finSum S (fun m => (m v) ^ (k' + 1))]
    exact hSmom (k' + 1) hk1 hk v
  · intro v
    rw [← blockOp_pencil e (msIndex S) v]
    refine le_trans (schattenNorm_blockOp_rpow_le he _ (by exact_mod_cast hp)) ?_
    have hcast : ∀ i, ‖msIndex S i v‖ ^ ((p : ℕ) : ℝ) = ‖msIndex S i v‖ ^ p := fun i =>
      Real.rpow_natCast _ p
    rw [Finset.sum_congr rfl fun i _ => hcast i]
    have hbound : ∀ i, ‖msIndex S i v‖ ^ p ≤ ‖msIndex S i‖ ^ p * ‖v‖ ^ p := by
      intro i
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((msIndex S i).le_opNorm v) p
    refine le_trans (Finset.sum_le_sum fun i _ => hbound i) ?_
    rw [← Finset.sum_mul, ← ms_sum_eq_finSum S (fun m => ‖m‖ ^ p)]
    exact mul_le_mul_of_nonneg_right hScost.le (by positivity)

end

end GaloisForLFunctions.HTGeometry
