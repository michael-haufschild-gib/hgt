import GaloisForLFunctions.RHTower.WeilLogShiftRecoveryAdaptive

/-!
# Fine-mesh histories are coefficient coordinates

Every real recovery history has a unique coefficient realization after fixing
the two invisible coordinates to zero. A staged triangular inverse supplies
this realization. Both maps are continuous for the product topology, giving
a homeomorphism between the coefficient subspace and arbitrary real sequences.
No growth, summability, sign, or RH assumption is used.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Reindex the visible recovery mesh by all natural numbers. -/
def weilLogShiftRecoveryHistory (lam : ℕ → ℝ) (k : ℕ) : ℝ :=
  weilLogShiftRecoveryProbe lam (k + 2)

theorem weilLogShiftRecoveryHistory_eq_iff (lam mu : ℕ → ℝ) :
    weilLogShiftRecoveryHistory lam = weilLogShiftRecoveryHistory mu ↔
      ∀ n : ℕ, 2 ≤ n → lam n = mu n := by
  constructor
  · intro h
    apply (weilLogShiftRecoveryProbe_eq_iff lam mu).mp
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
    exact congrFun h k
  · intro h
    funext k
    exact (weilLogShiftRecoveryProbe_eq_iff lam mu).mpr h (k + 2) (by omega)

theorem continuous_weilLogShiftRecoveryHistory : Continuous weilLogShiftRecoveryHistory := by
  apply continuous_pi
  intro k
  exact continuous_weilLogShiftRecoveryProbe (k + 2)

/-- The stabilized triangular inverse, with the two invisible coefficients fixed to zero. -/
def weilLogShiftRecoveryInverse (height : ℕ → ℝ) : ℕ → ℝ :=
  weilLogShiftRecoveryAdaptive (fun _ => 0) (fun k _ => height k)

theorem weilLogShiftRecoveryInverse_head (height : ℕ → ℝ) :
    weilLogShiftRecoveryInverse height 0 = 0 ∧ weilLogShiftRecoveryInverse height 1 = 0 :=
  weilLogShiftRecoveryAdaptive_head (fun _ => 0) (fun k _ => height k)

/-- Every prescribed real history is realized exactly by the stabilized inverse. -/
theorem weilLogShiftRecoveryHistory_inverse (height : ℕ → ℝ) :
    weilLogShiftRecoveryHistory (weilLogShiftRecoveryInverse height) = height := by
  funext k
  exact weilLogShiftRecoveryAdaptive_probe (fun _ => 0) (fun j _ => height j) k

/-- Reading and reconstructing a coefficient system changes only its two
invisible coordinates, which are reset to zero. -/
theorem weilLogShiftRecoveryInverse_history (lam : ℕ → ℝ) :
    weilLogShiftRecoveryInverse (weilLogShiftRecoveryHistory lam) =
      fun n => if 2 ≤ n then lam n else 0 := by
  have hcoef := (weilLogShiftRecoveryHistory_eq_iff
    (weilLogShiftRecoveryInverse (weilLogShiftRecoveryHistory lam)) lam).mp
      (weilLogShiftRecoveryHistory_inverse (weilLogShiftRecoveryHistory lam))
  have hhead := weilLogShiftRecoveryInverse_head (weilLogShiftRecoveryHistory lam)
  funext n
  by_cases hn : 2 ≤ n
  · rw [if_pos hn]
    exact hcoef n hn
  · rw [if_neg hn]
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · exact hhead.1
    · exact hhead.2

private theorem normalize_eq_of_zero_head (lam : ℕ → ℝ) (h0 : lam 0 = 0) (h1 : lam 1 = 0) :
    (fun n => if 2 ≤ n then lam n else 0) = lam := by
  funext n
  by_cases hn : 2 ≤ n
  · exact if_pos hn
  · rw [if_neg hn]
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · exact h0.symm
    · exact h1.symm

/-- Every recovery history has exactly one coefficient representative with zero head. -/
theorem existsUnique_weilLogShiftRecoveryHistory (height : ℕ → ℝ) :
    ∃! lam : ℕ → ℝ, lam 0 = 0 ∧ lam 1 = 0 ∧ weilLogShiftRecoveryHistory lam = height := by
  have hhead := weilLogShiftRecoveryInverse_head height
  refine ⟨weilLogShiftRecoveryInverse height,
    ⟨hhead.1, hhead.2, weilLogShiftRecoveryHistory_inverse height⟩, ?_⟩
  intro lam hlam
  have h := (weilLogShiftRecoveryInverse_history lam).trans
    (normalize_eq_of_zero_head lam hlam.1 hlam.2.1)
  rw [hlam.2.2] at h
  exact h.symm

/-- The inverse is continuous for coordinatewise convergence of recovery histories. -/
theorem continuous_weilLogShiftRecoveryInverse : Continuous weilLogShiftRecoveryInverse :=
  continuous_weilLogShiftRecoveryAdaptive_height (fun _ => 0)

/-- Fine-mesh first-probe data are unrestricted coefficient coordinates, with
a continuous inverse in the product topology. -/
def weilLogShiftRecoveryHomeomorph :
    {lam : ℕ → ℝ // lam 0 = 0 ∧ lam 1 = 0} ≃ₜ (ℕ → ℝ) where
  toEquiv :=
    { toFun := fun lam => weilLogShiftRecoveryHistory lam.1
      invFun := fun height =>
        ⟨weilLogShiftRecoveryInverse height, weilLogShiftRecoveryInverse_head height⟩
      left_inv := by
        intro lam
        apply Subtype.ext
        exact (weilLogShiftRecoveryInverse_history lam.1).trans
          (normalize_eq_of_zero_head lam.1 lam.2.1 lam.2.2)
      right_inv := weilLogShiftRecoveryHistory_inverse }
  continuous_toFun := continuous_weilLogShiftRecoveryHistory.comp continuous_subtype_val
  continuous_invFun := continuous_weilLogShiftRecoveryInverse.subtype_mk
    weilLogShiftRecoveryInverse_head

end RHTower
