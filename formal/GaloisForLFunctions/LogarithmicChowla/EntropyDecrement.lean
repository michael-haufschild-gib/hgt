import GaloisForLFunctions.LogarithmicChowla.LimitFunctional
import GaloisForLFunctions.LogarithmicChowla.FiniteEntropy

/-!
# The entropy decrement

Under a limit functional `L_U` every finite-valued sequence `g` has an entropy `H(g)` (`entU`).
Shift invariance of `L_U` makes it stationary, and pushforwards make it monotone, invariant under
bijections and submodular.

For the sign blocks `X_H(n) = (sgn λ(n+i))_{i<H}` (`blk`) and the residues `n mod M` (`res`), the
conditional entropy `H(X_H | n mod M)` (`condEnt`) satisfies

* `H(X_{2H} | n mod M) ≤ 2 H(X_H | n mod M)` (`condEnt_add_le`): submodularity for
  `(X_H, X_H(·+H), n mod M)`, and the shift by `H` permutes the residues;
* `H(X_H | n mod MP) = H(X_H | n mod M) − I` for coprime `M, P` (`condEnt_mul`), where
  `I = H(X_H, n mod M) + log P − H(X_H, n mod M, n mod P)` (`mutInf`) is the conditional mutual
  information of `X_H` and `n mod P` given `n mod M` (residues are uniform, `entU_res`);
* `0 ≤ H(X_H | n mod M) ≤ H log 2` (`condEnt_nonneg`, `condEnt_le`).

Along scales `H_{k+1} = 2H_k`, `M_{k+1} = M_k P_k` the normalised conditional entropy decreases by
`I_k/H_k` at each step, so `Σ_{K ≤ k < K'} I_k/H_k ≤ log 2` (`sum_mutInf_div_le`), and some `k`
in `[K, K')` has `I_k/H_k ≤ δ/k` once `δ log(K'/K) > log 2` (`exists_good_scale`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Real

noncomputable section

/-- Entropy of a finite-valued sequence under `L_U`. -/
def entU (U : Ultrafilter ℝ) {α : Type*} [Fintype α] [DecidableEq α] (g : ℕ → α) : ℝ :=
  ent (law U g)

variable {U : Ultrafilter ℝ}
variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
  [DecidableEq γ]

omit [Fintype β] in
theorem law_comp_eq_push (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) (F : α → β) :
    law U (fun n => F (g n)) = push F (law U g) := by
  funext b
  rw [law_comp hU g F b]
  rfl

theorem entU_comp_le (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) (F : α → β) :
    entU U (fun n => F (g n)) ≤ entU U g := by
  rw [entU, law_comp_eq_push hU]
  exact ent_push_le F (law_nonneg hU g)

theorem entU_comp_equiv (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) (e : α ≃ β) :
    entU U (fun n => e (g n)) = entU U g := by
  rw [entU, law_comp_eq_push hU]
  exact ent_push_equiv e _

theorem entU_shift (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) (m : ℕ) :
    entU U (fun n => g (n + m)) = entU U g := by
  rw [entU, entU, law_shift_add hU]

theorem entU_nonneg (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) : 0 ≤ entU U g :=
  ent_nonneg (law_nonneg hU g) (sum_law hU g)

theorem entU_le_log_card (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) :
    entU U g ≤ log (Fintype.card α) :=
  ent_le_log_card (law_nonneg hU g) (sum_law hU g)

/-- **Submodularity.** `H(A,B,C) + H(C) ≤ H(A,C) + H(B,C)`. -/
theorem entU_submod (hU : (U : Filter ℝ) ≤ atTop) (A : ℕ → α) (B : ℕ → β) (C : ℕ → γ) :
    entU U (fun n => (A n, B n, C n)) + entU U C
      ≤ entU U (fun n => (A n, C n)) + entU U (fun n => (B n, C n)) := by
  have h := ent_add_ent_le (law_nonneg hU fun n => (A n, B n, C n))
  have e1 : law U (fun n => (A n, C n))
      = push (fun t : α × β × γ => (t.1, t.2.2)) (law U fun n => (A n, B n, C n)) :=
    law_comp_eq_push hU (fun n => (A n, B n, C n)) fun t => (t.1, t.2.2)
  have e2 : law U (fun n => (B n, C n))
      = push (fun t : α × β × γ => (t.2.1, t.2.2)) (law U fun n => (A n, B n, C n)) :=
    law_comp_eq_push hU (fun n => (A n, B n, C n)) fun t => (t.2.1, t.2.2)
  have e3 : law U C = push (fun t : α × β × γ => t.2.2) (law U fun n => (A n, B n, C n)) :=
    law_comp_eq_push hU (fun n => (A n, B n, C n)) fun t => t.2.2
  rw [entU, entU, entU, entU, e1, e2, e3]
  exact h

/-- The entropy of a constant sequence vanishes. -/
theorem entU_unit (hU : (U : Filter ℝ) ≤ atTop) : entU U (fun _ : ℕ => ()) = 0 := by
  have h1 := entU_nonneg hU (fun _ : ℕ => ())
  have h2 := entU_le_log_card hU (fun _ : ℕ => ())
  simp only [Fintype.card_unit, Nat.cast_one, log_one] at h2
  linarith

/-- **Subadditivity.** `H(A,C) ≤ H(A) + H(C)`. -/
theorem entU_pair_le (hU : (U : Filter ℝ) ≤ atTop) (A : ℕ → α) (C : ℕ → γ) :
    entU U (fun n => (A n, C n)) ≤ entU U A + entU U C := by
  have h := entU_submod hU A C fun _ => ()
  have e1 : entU U (fun n => (A n, C n, ())) = entU U (fun n => (A n, C n)) := by
    have := entU_comp_equiv hU (fun n => (A n, C n, ()))
      ((Equiv.refl α).prodCongr (Equiv.prodPUnit γ))
    simpa using this.symm
  have e2 : entU U (fun n => (A n, ())) = entU U A := by
    have := entU_comp_equiv hU (fun n => (A n, ())) (Equiv.prodPUnit α)
    simpa using this.symm
  have e3 : entU U (fun n => (C n, ())) = entU U C := by
    have := entU_comp_equiv hU (fun n => (C n, ())) (Equiv.prodPUnit γ)
    simpa using this.symm
  rw [e1, e2, e3, entU_unit hU] at h
  linarith

/-! ## Liouville signs and residues -/

/-- `λ(n)` as a real number. -/
def lam (n : ℕ) : ℝ := (ArithmeticFunction.liouville n : ℝ)

theorem lam_mul (m n : ℕ) : lam (m * n) = lam m * lam n := by
  simp [lam, ArithmeticFunction.liouville_apply_mul]

theorem lam_prime {p : ℕ} (hp : p.Prime) : lam p = -1 := by
  simp [lam, ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]

theorem lam_eq_one_or {n : ℕ} (hn : n ≠ 0) : lam n = 1 ∨ lam n = -1 := by
  simp only [lam, ArithmeticFunction.liouville_apply hn]
  rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors n) with h | h <;> simp [h]

theorem abs_lam_le (n : ℕ) : |lam n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [lam]
  · rcases lam_eq_one_or hn with h | h <;> simp [h]

theorem bdd_lam : Bdd lam := ⟨1, abs_lam_le⟩

/-- The sign of `λ(n)`. -/
def sgn (n : ℕ) : Bool := decide (lam n = 1)

/-- `true ↦ 1`, `false ↦ −1`. -/
def toSign (b : Bool) : ℝ := if b then 1 else -1

theorem toSign_sgn {n : ℕ} (hn : n ≠ 0) : toSign (sgn n) = lam n := by
  rcases lam_eq_one_or hn with h | h <;> norm_num [toSign, sgn, h]

theorem abs_toSign (b : Bool) : |toSign b| = 1 := by
  cases b <;> simp [toSign]

/-- The sign block `X_H(n) = (sgn λ(n+i))_{i<H}`. -/
def blk (H n : ℕ) : Fin H → Bool := fun i => sgn (n + i)

/-- A block of length `H + H'` is the block of length `H` followed by the shifted block. -/
theorem appendEquiv_blk (H H' n : ℕ) :
    Fin.appendEquiv H H' (blk H n, blk H' (n + H)) = blk (H + H') n := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [Fin.appendEquiv, blk, Fin.append_left]
  · simp only [Fin.appendEquiv, Equiv.coe_fn_mk, Fin.append_right, blk, Fin.val_natAdd]
    congr 1
    ring

/-- The residue `n mod M`. -/
def res (M n : ℕ) : ZMod M := n

theorem res_add (M n m : ℕ) : res M (n + m) = res M n + m := by
  simp [res]

theorem law_res (hU : (U : Filter ℝ) ≤ atTop) (M : ℕ) [NeZero M] (r : ZMod M) :
    law U (res M) r = 1 / M :=
  limAvg_residue hU r

/-- Residues are uniform: `H(n mod M) = log M`. -/
theorem entU_res (hU : (U : Filter ℝ) ≤ atTop) (M : ℕ) [NeZero M] : entU U (res M) = log M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  rw [entU, ent]
  simp only [law_res hU, negMulLog, sum_const, card_univ, ZMod.card, nsmul_eq_mul, one_div,
    log_inv]
  field_simp

/-! ## Conditional entropy of sign blocks -/

/-- `H(X_H | n mod M)`. -/
def condEnt (U : Ultrafilter ℝ) (H M : ℕ) [NeZero M] : ℝ :=
  entU U (fun n => (blk H n, res M n)) - entU U (res M)

/-- The conditional mutual information of `X_H` and `n mod P` given `n mod M`. -/
def mutInf (U : Ultrafilter ℝ) (H M P : ℕ) [NeZero M] [NeZero P] : ℝ :=
  entU U (fun n => (blk H n, res M n)) + log P - entU U (fun n => (blk H n, res M n, res P n))

theorem condEnt_nonneg (hU : (U : Filter ℝ) ≤ atTop) (H M : ℕ) [NeZero M] :
    0 ≤ condEnt U H M := by
  have := entU_comp_le hU (fun n => (blk H n, res M n)) Prod.snd
  simp only at this
  rw [condEnt]
  linarith

theorem condEnt_le (hU : (U : Filter ℝ) ≤ atTop) (H M : ℕ) [NeZero M] :
    condEnt U H M ≤ H * log 2 := by
  have h1 := entU_pair_le hU (blk H) (res M)
  have h2 := entU_le_log_card hU (blk H)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, log_pow] at h2
  rw [condEnt]
  linarith

/-- **Doubling.** `H(X_{2H} | n mod M) ≤ 2 H(X_H | n mod M)`. -/
theorem condEnt_add_le (hU : (U : Filter ℝ) ≤ atTop) (H M : ℕ) [NeZero M] :
    condEnt U (H + H) M ≤ 2 * condEnt U H M := by
  have hsub := entU_submod hU (blk H) (fun n => blk H (n + H)) (res M)
  have e1 : entU U (fun n => (blk H n, blk H (n + H), res M n))
      = entU U (fun n => (blk (H + H) n, res M n)) := by
    have := entU_comp_equiv hU (fun n => (blk H n, blk H (n + H), res M n))
      (((Equiv.prodAssoc _ _ _).symm.trans
        ((Fin.appendEquiv H H).prodCongr (Equiv.refl (ZMod M)))))
    rw [← this]
    congr 1
    funext n
    simp [appendEquiv_blk]
  have e2 : entU U (fun n => (blk H (n + H), res M n)) = entU U (fun n => (blk H n, res M n)) := by
    have h1 := entU_comp_equiv hU (fun n => (blk H (n + H), res M (n + H)))
      ((Equiv.refl _).prodCongr (Equiv.addRight (-(H : ZMod M))))
    have h2 := entU_shift hU (fun n => (blk H n, res M n)) H
    rw [← h2, ← h1]
    congr 1
    funext n
    simp [res_add]
  rw [e1, e2] at hsub
  rw [condEnt, condEnt]
  linarith

/-- **Refinement.** For coprime `M, P`: `H(X_H | n mod MP) = H(X_H | n mod M) − I`. -/
theorem condEnt_mul (hU : (U : Filter ℝ) ≤ atTop) (H M P : ℕ) [NeZero M] [NeZero P]
    [NeZero (M * P)] (hMP : M.Coprime P) :
    condEnt U H (M * P) = condEnt U H M - mutInf U H M P := by
  have e1 : entU U (fun n => (blk H n, res (M * P) n))
      = entU U (fun n => (blk H n, res M n, res P n)) := by
    have := entU_comp_equiv hU (fun n => (blk H n, res (M * P) n))
      ((Equiv.refl _).prodCongr (ZMod.chineseRemainder hMP).toEquiv)
    rw [← this]
    congr 1
    funext n
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, res,
      RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_natCast]
    rfl
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hP : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  rw [condEnt, condEnt, mutInf, e1, entU_res hU, entU_res hU, Nat.cast_mul,
    log_mul hM.ne' hP.ne']
  ring

/-- The joint residue `(n mod M, n mod P)` is uniform: its entropy is `log M + log P`. -/
theorem entU_res_pair (hU : (U : Filter ℝ) ≤ atTop) (M P : ℕ) [NeZero M] [NeZero P]
    [NeZero (M * P)] (hMP : M.Coprime P) :
    entU U (fun n => (res M n, res P n)) = log M + log P := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hP : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  have := entU_comp_equiv hU (res (M * P)) (ZMod.chineseRemainder hMP).toEquiv
  rw [entU_res hU, Nat.cast_mul, log_mul hM.ne' hP.ne'] at this
  rw [← this]
  congr 1
  funext n
  simp only [res, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_natCast]
  rfl

/-- The conditional mutual information is nonnegative. -/
theorem mutInf_nonneg (hU : (U : Filter ℝ) ≤ atTop) (H M P : ℕ) [NeZero M] [NeZero P]
    [NeZero (M * P)] (hMP : M.Coprime P) : 0 ≤ mutInf U H M P := by
  have hsub := entU_submod hU (blk H) (res P) (res M)
  have e1 : entU U (fun n => (blk H n, res P n, res M n))
      = entU U (fun n => (blk H n, res M n, res P n)) := by
    have := entU_comp_equiv hU (fun n => (blk H n, res P n, res M n))
      ((Equiv.refl _).prodCongr (Equiv.prodComm _ _))
    rw [← this]
    rfl
  have e2 : entU U (fun n => (res P n, res M n)) = entU U (fun n => (res M n, res P n)) := by
    have := entU_comp_equiv hU (fun n => (res P n, res M n)) (Equiv.prodComm _ _)
    rw [← this]
    rfl
  rw [e1, e2, entU_res_pair hU M P hMP, entU_res hU] at hsub
  rw [mutInf]
  linarith

/-- `condEnt_mul` for a modulus given as a product. -/
theorem condEnt_mul' (hU : (U : Filter ℝ) ≤ atTop) (H M P M' : ℕ) [NeZero M] [NeZero P]
    [NeZero M'] (hM' : M' = M * P) (hMP : M.Coprime P) :
    condEnt U H M' = condEnt U H M - mutInf U H M P := by
  subst hM'
  exact condEnt_mul hU H M P hMP

/-! ## Scales -/

/-- Along `H_{k+1} = 2H_k`, `M_{k+1} = M_k P_k` (coprime), the mutual informations are summable:
`Σ_{K ≤ k < K'} I_k/H_k ≤ log 2`. -/
theorem sum_mutInf_div_le (hU : (U : Filter ℝ) ≤ atTop) (H M P : ℕ → ℕ) [∀ k, NeZero (M k)]
    [∀ k, NeZero (P k)] (hH : ∀ k, 0 < H k) (hHs : ∀ k, H (k + 1) = H k + H k)
    (hMs : ∀ k, M (k + 1) = M k * P k) (hcop : ∀ k, (M k).Coprime (P k)) (K K' : ℕ) :
    ∑ k ∈ Ico K K', mutInf U (H k) (M k) (P k) / H k ≤ log 2 := by
  set φ : ℕ → ℝ := fun k => condEnt U (H k) (M k) / H k with hφ
  have hstep : ∀ k, φ (k + 1) ≤ φ k - mutInf U (H k) (M k) (P k) / H k := by
    intro k
    have hHk : (0 : ℝ) < H k := by exact_mod_cast hH k
    have h1 := condEnt_add_le hU (H k) (M (k + 1))
    have h2 := condEnt_mul' hU (H k) (M k) (P k) (M (k + 1)) (hMs k) (hcop k)
    have h3 : condEnt U (H (k + 1)) (M (k + 1)) = condEnt U (H k + H k) (M (k + 1)) := by
      rw [hHs k]
    show condEnt U (H (k + 1)) (M (k + 1)) / (H (k + 1) : ℝ)
      ≤ condEnt U (H k) (M k) / H k - mutInf U (H k) (M k) (P k) / H k
    rw [h3, hHs k, Nat.cast_add, div_le_iff₀ (by positivity)]
    have e : (condEnt U (H k) (M k) / H k - mutInf U (H k) (M k) (P k) / H k)
        * ((H k : ℝ) + H k) = 2 * (condEnt U (H k) (M k) - mutInf U (H k) (M k) (P k)) := by
      field_simp
      ring
    rw [e]
    linarith
  have htel : ∀ K', K ≤ K' →
      ∑ k ∈ Ico K K', mutInf U (H k) (M k) (P k) / H k ≤ φ K - φ K' := by
    intro K' hK'
    induction K', hK' using Nat.le_induction with
    | base => simp
    | succ K' hK' ih =>
      rw [sum_Ico_succ_top hK']
      linarith [hstep K']
  rcases le_or_gt K K' with hKK | hKK
  · have h0 : 0 ≤ φ K' := div_nonneg (condEnt_nonneg hU _ _) (Nat.cast_nonneg _)
    have h1 : φ K ≤ log 2 := by
      have hHK : (0 : ℝ) < H K := by exact_mod_cast hH K
      rw [hφ, div_le_iff₀ hHK, mul_comm]
      exact condEnt_le hU _ _
    linarith [htel K' hKK]
  · rw [Ico_eq_empty_of_le hKK.le, sum_empty]
    exact log_nonneg (by norm_num)

/-- **A good scale, weighted form.** For weights `w ≥ 0` with `δ Σ_{K ≤ k < K'} w_k > log 2`, some
`k ∈ [K, K')` has `w_k > 0` and `I_k/H_k ≤ δ w_k`. -/
theorem exists_good_scale_weighted (hU : (U : Filter ℝ) ≤ atTop) (H M P : ℕ → ℕ)
    [∀ k, NeZero (M k)] [∀ k, NeZero (P k)] (hH : ∀ k, 0 < H k)
    (hHs : ∀ k, H (k + 1) = H k + H k) (hMs : ∀ k, M (k + 1) = M k * P k)
    (hcop : ∀ k, (M k).Coprime (P k)) (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) {K K' : ℕ} {δ : ℝ}
    (hlog : log 2 < δ * ∑ k ∈ Ico K K', w k) :
    ∃ k ∈ Ico K K', 0 < w k ∧ mutInf U (H k) (M k) (P k) / H k ≤ δ * w k := by
  by_contra hcon
  push Not at hcon
  have hsum := sum_mutInf_div_le hU H M P hH hHs hMs hcop K K'
  have hlow : δ * ∑ k ∈ Ico K K', w k
      ≤ ∑ k ∈ Ico K K', mutInf U (H k) (M k) (P k) / H k := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rcases (hw k).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      haveI : NeZero (M k * P k) := ⟨by rw [← hMs k]; exact NeZero.ne _⟩
      exact div_nonneg (mutInf_nonneg hU _ _ _ (hcop k)) (Nat.cast_nonneg _)
    · exact (hcon k hk hpos).le
  linarith

/-- `Σ_{K ≤ k < K'} 1/k ≥ log(K'/K)`. -/
theorem log_div_le_sum_Ico_inv {K K' : ℕ} (hK : 0 < K) (hKK : K ≤ K') :
    log ((K' : ℝ) / K) ≤ ∑ k ∈ Ico K K', (1 : ℝ) / k := by
  induction K', hKK using Nat.le_induction with
  | base =>
    have : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    simp [div_self this]
  | succ K' hK' ih =>
    rw [sum_Ico_succ_top hK']
    have hK'pos : (0 : ℝ) < K' := by exact_mod_cast lt_of_lt_of_le hK hK'
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hstep : log (((K' + 1 : ℕ) : ℝ) / K) ≤ log ((K' : ℝ) / K) + 1 / K' := by
      rw [log_div (by positivity) hKpos.ne', log_div hK'pos.ne' hKpos.ne']
      have h := log_le_sub_one_of_pos (show (0 : ℝ) < ((K' + 1 : ℕ) : ℝ) / K' by positivity)
      rw [log_div (by positivity) hK'pos.ne'] at h
      have : ((K' + 1 : ℕ) : ℝ) / K' - 1 = 1 / K' := by
        push_cast
        field_simp
        ring
      linarith
    linarith

/-- **A good scale.** If `δ log(K'/K) > log 2`, some `k ∈ [K, K')` has `I_k/H_k ≤ δ/k`. -/
theorem exists_good_scale (hU : (U : Filter ℝ) ≤ atTop) (H M P : ℕ → ℕ) [∀ k, NeZero (M k)]
    [∀ k, NeZero (P k)] (hH : ∀ k, 0 < H k) (hHs : ∀ k, H (k + 1) = H k + H k)
    (hMs : ∀ k, M (k + 1) = M k * P k) (hcop : ∀ k, (M k).Coprime (P k)) {K K' : ℕ}
    (hK : 0 < K) (hKK : K ≤ K') {δ : ℝ} (hδ : 0 < δ) (hlog : log 2 < δ * log ((K' : ℝ) / K)) :
    ∃ k ∈ Ico K K', mutInf U (H k) (M k) (P k) / H k ≤ δ / k := by
  by_contra hcon
  push Not at hcon
  have hsum := sum_mutInf_div_le hU H M P hH hHs hMs hcop K K'
  have hlow : δ * ∑ k ∈ Ico K K', (1 : ℝ) / k ≤ ∑ k ∈ Ico K K', mutInf U (H k) (M k) (P k) / H k := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [← mul_div_assoc, mul_one]
    exact (hcon k hk).le
  have hharm := log_div_le_sum_Ico_inv hK hKK
  nlinarith

end

end GaloisForLFunctions.LogarithmicChowla
