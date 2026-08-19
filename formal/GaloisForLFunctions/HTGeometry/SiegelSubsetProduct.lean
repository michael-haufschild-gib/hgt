import GaloisForLFunctions.HTGeometry.SiegelMinorComparison

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- A strictly monotone map between finite index types does not decrease the index. -/
theorem le_val_of_strictMono {k n : ℕ} {g : Fin k → Fin n} (hg : StrictMono g) (j : Fin k) :
    (j : ℕ) ≤ (g j : ℕ) := by
  have key : ∀ m : ℕ, ∀ j : Fin k, (j : ℕ) = m → m ≤ (g j : ℕ) := by
    intro m
    induction m with
    | zero => intro j _; exact Nat.zero_le _
    | succ m ih =>
        intro j hj
        have hlt : m < k := by have := j.isLt; omega
        have hstep : (⟨m, hlt⟩ : Fin k) < j := by
          rw [Fin.lt_def]
          show m < (j : ℕ)
          omega
        have h2 : (g ⟨m, hlt⟩ : ℕ) < (g j : ℕ) := Fin.lt_def.1 (hg hstep)
        have h1 : m ≤ (g ⟨m, hlt⟩ : ℕ) := ih ⟨m, hlt⟩ rfl
        omega
  exact key (j : ℕ) j rfl

/-- **An injective index selection cannot decrease a product of an increasing weight.**  The
selected indices, listed in order, are pointwise at least the first `k` indices, so each factor
drops by at most the growth constant. -/
theorem prod_castLE_le_prod_of_injective {k n : ℕ} (hk : k ≤ n) {d : Fin n → ℝ}
    (hd : ∀ i, 0 < d i) {K : ℝ}
    (hmono : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → d i ≤ K * d j)
    {f : Fin k → Fin n} (hf : Function.Injective f) :
    (∏ j : Fin k, d (Fin.castLE hk j)) ≤ K ^ k * ∏ j : Fin k, d (f j) := by
  classical
  set S : Finset (Fin n) := Finset.image f Finset.univ with hS
  have hcard : S.card = k := by
    rw [hS, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  set e := S.orderIsoOfFin hcard with he
  set g : Fin k → Fin n := fun j => ((e j : Fin n)) with hg
  have hgmono : StrictMono g := by
    intro a b hab
    exact Subtype.coe_lt_coe.mpr (e.strictMono hab)
  have hprodS : (∏ m ∈ S, d m) = ∏ j : Fin k, d (g j) := by
    rw [← Finset.prod_coe_sort S d]
    exact (Equiv.prod_comp e.toEquiv (fun m : S => d (m : Fin n))).symm
  have hprodf : (∏ m ∈ S, d m) = ∏ j : Fin k, d (f j) := by
    rw [hS]
    exact Finset.prod_image (fun a _ b _ hab => hf hab)
  have hstep : ∀ j : Fin k, d (Fin.castLE hk j) ≤ K * d (g j) :=
    fun j => hmono _ _ (by simpa using le_val_of_strictMono hgmono j)
  calc (∏ j : Fin k, d (Fin.castLE hk j)) ≤ ∏ j : Fin k, (K * d (g j)) :=
        Finset.prod_le_prod (fun j _ => (hd _).le) (fun j _ => hstep j)
    _ = K ^ k * ∏ j : Fin k, d (g j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = K ^ k * ∏ j : Fin k, d (f j) := by rw [← hprodS, hprodf]

end GaloisForLFunctions.HTGeometry
