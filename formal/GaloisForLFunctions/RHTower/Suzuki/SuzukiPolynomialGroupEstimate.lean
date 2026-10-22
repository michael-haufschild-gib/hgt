import GaloisForLFunctions.RHTower.Suzuki.SuzukiPositionCommutatorGroup
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# The weighted evolution grows polynomially

A coordinate word passed through a finite-range lattice evolution becomes the same word in the
shifted coordinates, and the shift is a bounded symbol multiplied by the time.  Expanding the
shifted word therefore produces a polynomial in the time whose coefficients are operators of the
form

`bounded symbol × coordinate word`,

with the word length dropping by one for every power of the time that is taken.  Such an operator
is bounded by the position graph norm of the corresponding order, so the whole word is bounded by
the top graph norm times `(1 + |x|)` to the power of the word length.

Since the evolution is isometric, this is exactly the weighted group estimate: conjugating the
evolution by a position weight of order `m` costs at most `(1 + |x|)^m`.
-/

open Finset

noncomputable section

namespace RHTower

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {ι : Type*} [Fintype ι]

/-! ## Coordinate words -/

/-- The ordered product of coordinates along a word. -/
def wordProd (X : ι → (V →ₗ[𝕜] V)) {k : ℕ} (w : Fin k → ι) : V →ₗ[𝕜] V :=
  (List.ofFn fun j => X (w j)).prod

omit [Fintype ι] in
@[simp] theorem wordProd_nil (X : ι → (V →ₗ[𝕜] V)) (w : Fin 0 → ι) :
    wordProd X w = 1 := by
  simp [wordProd]

omit [Fintype ι] in
theorem wordProd_cons (X : ι → (V →ₗ[𝕜] V)) (i : ι) {k : ℕ} (w : Fin k → ι) :
    wordProd X (Fin.cons i w : Fin (k + 1) → ι) = X i * wordProd X w := by
  rw [wordProd, wordProd, List.ofFn_succ, List.prod_cons]
  simp

/-- The position graph norm of order `n`. -/
def posNorm (X : ι → (V →ₗ[𝕜] V)) (n : ℕ) (v : V) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ w : Fin k → ι, ‖wordProd X w v‖

theorem posNorm_nonneg (X : ι → (V →ₗ[𝕜] V)) (n : ℕ) (v : V) : 0 ≤ posNorm X n v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem posNorm_mono (X : ι → (V →ₗ[𝕜] V)) {n m : ℕ} (h : n ≤ m) (v : V) :
    posNorm X n v ≤ posNorm X m v := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (m + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    fun k _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_wordProd_le_posNorm (X : ι → (V →ₗ[𝕜] V)) {n k : ℕ} (hk : k ≤ n)
    (w : Fin k → ι) (v : V) : ‖wordProd X w v‖ ≤ posNorm X n v := by
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun k => ∑ w : Fin k → ι, ‖wordProd X w v‖)
    (fun j _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (n + 1)))
  exact Finset.single_le_sum (f := fun w : Fin k → ι => ‖wordProd X w v‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ w)

/-! ## Operators of bounded order -/

/-- Operators carried by a symbol class: a finite sum of bounded symbols times coordinate words of
length at most `n`. -/
inductive DiffOp (S : Set (V →ₗ[𝕜] V)) (X : ι → (V →ₗ[𝕜] V)) : ℕ → (V →ₗ[𝕜] V) → Prop
  | zero (n : ℕ) : DiffOp S X n 0
  | add {n : ℕ} {T U : V →ₗ[𝕜] V} : DiffOp S X n T → DiffOp S X n U → DiffOp S X n (T + U)
  | mono {n : ℕ} {T : V →ₗ[𝕜] V} : DiffOp S X n T → DiffOp S X (n + 1) T
  | symbolWord {n k : ℕ} (B : V →ₗ[𝕜] V) (hB : B ∈ S) (hk : k ≤ n) (w : Fin k → ι) :
      DiffOp S X n (B * wordProd X w)

variable {S : Set (V →ₗ[𝕜] V)} {X C : ι → (V →ₗ[𝕜] V)}

omit [Fintype ι] in
theorem DiffOp.pos_mul (hS : ∀ i : ι, ∀ T ∈ S, X i * T - T * X i ∈ S) (i : ι) {n : ℕ}
    {T : V →ₗ[𝕜] V} (h : DiffOp S X n T) : DiffOp S X (n + 1) (X i * T) := by
  induction h with
  | zero n => simpa using DiffOp.zero (S := S) (X := X) (n + 1)
  | add _ _ ih1 ih2 =>
      rw [mul_add]
      exact ih1.add ih2
  | mono _ ih => exact ih.mono
  | symbolWord B hB hk w =>
      have key : X i * (B * wordProd X w)
          = B * wordProd X (Fin.cons i w : Fin (_ + 1) → ι)
            + (X i * B - B * X i) * wordProd X w := by
        rw [wordProd_cons]
        noncomm_ring
      rw [key]
      exact (DiffOp.symbolWord B hB (by omega) _).add
        (DiffOp.symbolWord _ (hS i B hB) (by omega) w)

omit [Fintype ι] in
theorem DiffOp.symbol_mul (hmul : ∀ T ∈ S, ∀ U ∈ S, T * U ∈ S) {B : V →ₗ[𝕜] V} (hB : B ∈ S)
    {n : ℕ} {T : V →ₗ[𝕜] V} (h : DiffOp S X n T) : DiffOp S X n (B * T) := by
  induction h with
  | zero n => simpa using DiffOp.zero (S := S) (X := X) n
  | add _ _ ih1 ih2 =>
      rw [mul_add]
      exact ih1.add ih2
  | mono _ ih => exact ih.mono
  | symbolWord B' hB' hk w =>
      have key : B * (B' * wordProd X w) = (B * B') * wordProd X w := by noncomm_ring
      rw [key]
      exact DiffOp.symbolWord _ (hmul B hB B' hB') hk w

/-- An operator of order `n` is bounded by the position graph norm of order `n`. -/
theorem DiffOp.exists_bound (hbdd : ∀ T ∈ S, ∃ M : ℝ, ∀ v, ‖T v‖ ≤ M * ‖v‖) {n : ℕ}
    {T : V →ₗ[𝕜] V} (h : DiffOp S X n T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v, ‖T v‖ ≤ M * posNorm X n v := by
  induction h with
  | zero n =>
      refine ⟨0, le_refl _, fun v => ?_⟩
      simp
  | add _ _ ih1 ih2 =>
      obtain ⟨M1, hM1, h1⟩ := ih1
      obtain ⟨M2, hM2, h2⟩ := ih2
      refine ⟨M1 + M2, by linarith, fun v => ?_⟩
      calc ‖_‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
        _ ≤ M1 * posNorm X _ v + M2 * posNorm X _ v := add_le_add (h1 v) (h2 v)
        _ = (M1 + M2) * posNorm X _ v := by ring
  | @mono n T _ ih =>
      obtain ⟨M, hM, h1⟩ := ih
      refine ⟨M, hM, fun v => ?_⟩
      exact le_trans (h1 v) (mul_le_mul_of_nonneg_left (posNorm_mono X (by omega) v) hM)
  | symbolWord B hB hk w =>
      obtain ⟨M, hM⟩ := hbdd B hB
      refine ⟨max M 0, le_max_right _ _, fun v => ?_⟩
      have h1 : ‖(B * wordProd X w) v‖ ≤ max M 0 * ‖wordProd X w v‖ := by
        rw [Module.End.mul_apply]
        exact le_trans (hM _) (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      exact le_trans h1 (mul_le_mul_of_nonneg_left
        (norm_wordProd_le_posNorm X hk w v) (le_max_right _ _))

/-! ## The polynomial expansion of a shifted word -/

omit [Fintype ι] in
/-- The shifted coordinate word is a polynomial in the time whose coefficient of `t^k` is an
operator of order at most the word length minus `k`. -/
theorem exists_diffOp_expansion (hS : ∀ i : ι, ∀ T ∈ S, X i * T - T * X i ∈ S)
    (hmul : ∀ T ∈ S, ∀ U ∈ S, T * U ∈ S) (hone : (1 : V →ₗ[𝕜] V) ∈ S)
    (hC : ∀ i, C i ∈ S) (l : List ι) :
    ∃ P : ℕ → (V →ₗ[𝕜] V), (∀ k, DiffOp S X (l.length - k) (P k)) ∧
      (∀ k, l.length < k → P k = 0) ∧
      ∀ t : 𝕜, (l.map fun i => X i + t • C i).prod
        = ∑ k ∈ Finset.range (l.length + 1), t ^ k • P k := by
  induction l with
  | nil =>
      refine ⟨fun k => if k = 0 then 1 else 0, ?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = 0
        · subst hk
          simpa using
            DiffOp.symbolWord (S := S) (X := X) (n := 0) 1 hone (le_refl 0) (fun j => j.elim0)
        · simp only [if_neg hk]
          exact DiffOp.zero _
      · intro k hk
        simp only [List.length_nil] at hk
        show (if k = 0 then (1 : V →ₗ[𝕜] V) else 0) = 0
        rw [if_neg (by omega : ¬ k = 0)]
      · intro t
        simp
  | cons i l ih =>
      obtain ⟨P, hPd, hP0, hP⟩ := ih
      refine ⟨fun k => X i * P k + C i * (if k = 0 then 0 else P (k - 1)), ?_, ?_, ?_⟩
      · intro k
        have hXP : DiffOp S X ((l.length + 1) - k) (X i * P k) := by
          by_cases hk : k ≤ l.length
          · have hrw : (l.length + 1) - k = (l.length - k) + 1 := by omega
            rw [hrw]
            exact (hPd k).pos_mul hS i
          · have hz : P k = 0 := hP0 k (by omega)
            rw [hz, mul_zero]
            exact DiffOp.zero _
        have hCP : DiffOp S X ((l.length + 1) - k)
            (C i * (if k = 0 then 0 else P (k - 1))) := by
          cases k with
          | zero =>
              rw [if_pos rfl, mul_zero]
              exact DiffOp.zero _
          | succ j =>
              have hnat : l.length + 1 - (j + 1) = l.length - j := by omega
              rw [if_neg (Nat.succ_ne_zero j), Nat.succ_sub_one, hnat]
              exact (hPd j).symbol_mul hmul (hC i)
        simpa [List.length_cons] using hXP.add hCP
      · intro k hk
        simp only [List.length_cons] at hk
        cases k with
        | zero => omega
        | succ j =>
            have h1 : P (j + 1) = 0 := hP0 _ (by omega)
            have h2 : P j = 0 := hP0 _ (by omega)
            show X i * P (j + 1) + C i * (if j + 1 = 0 then 0 else P (j + 1 - 1)) = 0
            rw [if_neg (Nat.succ_ne_zero j), Nat.succ_sub_one, h1, h2, mul_zero, mul_zero,
              add_zero]
      · intro t
        have hPn : P (l.length + 1) = 0 := hP0 _ (by omega)
        have hA : X i * ∑ k ∈ Finset.range (l.length + 1), t ^ k • P k
            = ∑ k ∈ Finset.range (l.length + 1), t ^ k • (X i * P k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => mul_smul_comm _ _ _
        have hB : (t • C i) * ∑ k ∈ Finset.range (l.length + 1), t ^ k • P k
            = ∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (C i * P k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
          congr 1
          ring
        have hshift : ∑ k ∈ Finset.range (l.length + 1 + 1),
              t ^ k • (X i * P k + C i * (if k = 0 then 0 else P (k - 1)))
            = (∑ k ∈ Finset.range (l.length + 1),
                t ^ (k + 1) • (X i * P (k + 1) + C i * P k)) + X i * P 0 := by
          rw [Finset.sum_range_succ' (fun k => t ^ k •
            (X i * P k + C i * (if k = 0 then 0 else P (k - 1)))) (l.length + 1)]
          norm_num
        have hxsum : ∑ k ∈ Finset.range (l.length + 1), t ^ k • (X i * P k)
            = (∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (X i * P (k + 1)))
              + X i * P 0 := by
          rw [Finset.sum_range_succ (fun k => t ^ (k + 1) • (X i * P (k + 1))) l.length, hPn,
            mul_zero, smul_zero, add_zero,
            Finset.sum_range_succ' (fun k => t ^ k • (X i * P k)) l.length]
          norm_num
        rw [List.map_cons, List.prod_cons, hP t, List.length_cons, add_mul, hA, hB, hshift,
          hxsum]
        have hsplit : ∑ k ∈ Finset.range (l.length + 1),
              t ^ (k + 1) • (X i * P (k + 1) + C i * P k)
            = (∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (X i * P (k + 1)))
              + ∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (C i * P k) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => smul_add _ _ _
        rw [hsplit]
        abel

/-! ## The polynomial bound -/

/-- **`(17)`: the shifted coordinate word grows at most polynomially in the time**, with a constant
uniform in the time. -/
theorem exists_polynomial_word_bound (hS : ∀ i : ι, ∀ T ∈ S, X i * T - T * X i ∈ S)
    (hmul : ∀ T ∈ S, ∀ U ∈ S, T * U ∈ S) (hone : (1 : V →ₗ[𝕜] V) ∈ S)
    (hbdd : ∀ T ∈ S, ∃ M : ℝ, ∀ v, ‖T v‖ ≤ M * ‖v‖) (hC : ∀ i, C i ∈ S) (l : List ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : 𝕜) (v : V),
      ‖(l.map fun i => X i + t • C i).prod v‖
        ≤ M * (1 + ‖t‖) ^ l.length * posNorm X l.length v := by
  obtain ⟨P, hPd, -, hP⟩ := exists_diffOp_expansion hS hmul hone hC l
  choose M hM0 hMle using fun k => (hPd k).exists_bound hbdd
  refine ⟨∑ k ∈ Finset.range (l.length + 1), M k, Finset.sum_nonneg fun k _ => hM0 k, ?_⟩
  intro t v
  have hbase : (1 : ℝ) ≤ 1 + ‖t‖ := le_add_of_nonneg_right (norm_nonneg t)
  rw [hP t]
  have h1 : ‖(∑ k ∈ Finset.range (l.length + 1), t ^ k • P k) v‖
      ≤ ∑ k ∈ Finset.range (l.length + 1), ‖t‖ ^ k * ‖P k v‖ := by
    rw [LinearMap.sum_apply]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [LinearMap.smul_apply, norm_smul, norm_pow]
  refine le_trans h1 ?_
  have h2 : ∀ k ∈ Finset.range (l.length + 1),
      ‖t‖ ^ k * ‖P k v‖ ≤ M k * ((1 + ‖t‖) ^ l.length * posNorm X l.length v) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkle : k ≤ l.length := by omega
    have hp : ‖t‖ ^ k ≤ (1 + ‖t‖) ^ l.length := by
      calc ‖t‖ ^ k ≤ (1 + ‖t‖) ^ k := by
            exact pow_le_pow_left₀ (norm_nonneg t) (by linarith) k
        _ ≤ (1 + ‖t‖) ^ l.length := pow_le_pow_right₀ hbase hkle
    have hq : ‖P k v‖ ≤ M k * posNorm X l.length v :=
      le_trans (hMle k v) (mul_le_mul_of_nonneg_left
        (posNorm_mono X (by omega) v) (hM0 k))
    calc ‖t‖ ^ k * ‖P k v‖ ≤ (1 + ‖t‖) ^ l.length * (M k * posNorm X l.length v) :=
          mul_le_mul hp hq (norm_nonneg _) (by positivity)
      _ = M k * ((1 + ‖t‖) ^ l.length * posNorm X l.length v) := by ring
  refine le_trans (Finset.sum_le_sum h2) ?_
  rw [← Finset.sum_mul]
  ring_nf
  exact le_refl _

/-! ## The evolution -/

omit [Fintype ι] in
/-- A coordinate word passes through an intertwining evolution and becomes the shifted word. -/
theorem wordProd_comp_evolution {U : V →ₗ[𝕜] V} {t : 𝕜}
    (hU : ∀ (i : ι) (v : V), X i (U v) = U (X i v + t • C i v)) (l : List ι) (v : V) :
    (l.map X).prod (U v) = U ((l.map fun i => X i + t • C i).prod v) := by
  induction l generalizing v with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [ih v, hU i]
      simp [LinearMap.add_apply, LinearMap.smul_apply]

/-- **`(17)`: the position-weighted evolution grows at most polynomially in the time.**  A
coordinate word of length `m` applied after an isometric intertwining evolution is bounded by the
position graph norm of order `m`, with a constant times `(1 + |x|)^m`. -/
theorem exists_polynomial_group_bound (hS : ∀ i : ι, ∀ T ∈ S, X i * T - T * X i ∈ S)
    (hmul : ∀ T ∈ S, ∀ U ∈ S, T * U ∈ S) (hone : (1 : V →ₗ[𝕜] V) ∈ S)
    (hbdd : ∀ T ∈ S, ∃ M : ℝ, ∀ v, ‖T v‖ ≤ M * ‖v‖) (hC : ∀ i, C i ∈ S) (l : List ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : 𝕜) (U : V →ₗ[𝕜] V),
      (∀ (i : ι) (v : V), X i (U v) = U (X i v + t • C i v)) → (∀ v, ‖U v‖ = ‖v‖) →
      ∀ v, ‖(l.map X).prod (U v)‖ ≤ M * (1 + ‖t‖) ^ l.length * posNorm X l.length v := by
  obtain ⟨M, hM0, hM⟩ := exists_polynomial_word_bound hS hmul hone hbdd hC l
  refine ⟨M, hM0, fun t U hU hiso v => ?_⟩
  rw [wordProd_comp_evolution hU l v, hiso]
  exact hM t v

end RHTower
