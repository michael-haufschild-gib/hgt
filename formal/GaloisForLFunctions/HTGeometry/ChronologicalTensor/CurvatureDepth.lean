import GaloisForLFunctions.HTGeometry.ChronologicalTensor.EnclosureCurvature
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.EnclosureCone

/-!
# Enclosure depth and reconstruction from finite curvature

The first depth reaching monotone capacity exists for every finite window form.
Curvature is positive precisely below that depth and zero thereafter. Finite
telescoping recovers capacity drops and the complete capacity profile from this
curvature sequence and the monotone capacity.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem sealedCapacity_has_depth {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) : ∃ k : ℕ, sealedCapacity D c k = monotoneCapacity D c := by
  obtain ⟨N,hN⟩ := eventual_exact_sealing D c
  exact ⟨N,by simpa only [Nat.add_zero] using hN 0⟩

def enclosureDepth {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) : ℕ := by
  classical
  exact Nat.find (sealedCapacity_has_depth D c)

theorem enclosureDepth_spec {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) : sealedCapacity D c (enclosureDepth D c) = monotoneCapacity D c := by
  classical
  exact Nat.find_spec (sealedCapacity_has_depth D c)

theorem enclosureDepth_le_iff {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    enclosureDepth D c ≤ k ↔ sealedCapacity D c k = monotoneCapacity D c := by
  classical
  constructor
  · intro hk
    apply le_antisymm _ (monotoneCapacity_le_sealed D c k)
    have h := sealedCapacity_add_depth D c (enclosureDepth D c) (k-enclosureDepth D c)
    have he : enclosureDepth D c+(k-enclosureDepth D c) = k := by omega
    rw [he,enclosureDepth_spec] at h
    exact h
  · intro hk
    exact Nat.find_min' (sealedCapacity_has_depth D c) hk

theorem enclosureDepth_degree_bound {n r m : ℕ}
    (D : Fin m → Fin (r+2) → Finset (Fin (n+1))) (c : Fin m → ℝ) :
    enclosureDepth D c ≤ (r+2)*(r+1) :=
  (enclosureDepth_le_iff D c _).mpr (quadratic_sealing_capacity D c)

theorem enclosureCurvature_support {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    0 < enclosureCurvature D c k ↔ k < enclosureDepth D c := by
  rw [enclosureCurvature_pos_iff]
  have hm := monotoneCapacity_le_sealed D c k
  constructor
  · intro hk
    by_contra hn
    have hle : enclosureDepth D c ≤ k := by omega
    have he := (enclosureDepth_le_iff D c k).mp hle
    linarith only [hk,he]
  · intro hk
    by_contra hn
    have he : sealedCapacity D c k = monotoneCapacity D c := by linarith only [hm,hn]
    have hle := (enclosureDepth_le_iff D c k).mpr he
    omega

theorem enclosureCurvature_tail {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    enclosureCurvature D c k = 0 ↔ enclosureDepth D c ≤ k :=
  (enclosureCurvature_zero_iff D c k).trans (enclosureDepth_le_iff D c k).symm

theorem sixWindows_reversal_depth : enclosureDepth sixWindows ![27,-1] = 1 := by
  apply Nat.le_antisymm
  · apply (enclosureDepth_le_iff sixWindows (![27,-1] : Fin 2 → ℝ) 1).mpr
    rw [sixWindows_reversal_monotoneCapacity]
    exact sixWindows_reversal_sealed_one 0
  · have h := enclosureDepth_spec sixWindows (![27,-1] : Fin 2 → ℝ)
    rw [sixWindows_reversal_monotoneCapacity] at h
    exact (sixWindows_reversal_exact_depth _).mp h

theorem second_difference_telescope (C : ℕ → ℝ) (N k : ℕ) :
    (∑ j ∈ Finset.range N, (C (k+j)-2*C (k+j+1)+C (k+j+2))) =
      C k-C (k+1)-C (k+N)+C (k+N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [Nat.add_succ]
    ring

theorem weighted_second_difference_telescope (C : ℕ → ℝ) (N k : ℕ) :
    (∑ j ∈ Finset.range N, ((j : ℝ)+1)*(C (k+j)-2*C (k+j+1)+C (k+j+2))) =
      C k-((N : ℝ)+1)*C (k+N)+(N : ℝ)*C (k+N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [Nat.add_succ]
    push_cast
    ring

theorem enclosureCurvature_mass {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range (enclosureDepth D c), enclosureCurvature D c (k+j)) =
      sealedCapacity D c k-sealedCapacity D c (k+1) := by
  unfold enclosureCurvature
  rw [second_difference_telescope]
  have h0 := (enclosureDepth_le_iff D c (k+enclosureDepth D c)).mp (by omega)
  have h1 := (enclosureDepth_le_iff D c (k+enclosureDepth D c+1)).mp (by omega)
  rw [h0,h1]
  ring

theorem enclosureCurvature_reconstruction {n r m : ℕ}
    (D : Fin m → Fin r → Finset (Fin (n+1))) (c : Fin m → ℝ) (k : ℕ) :
    sealedCapacity D c k = monotoneCapacity D c +
      ∑ j ∈ Finset.range (enclosureDepth D c), ((j : ℝ)+1)*enclosureCurvature D c (k+j) := by
  unfold enclosureCurvature
  rw [weighted_second_difference_telescope]
  have h0 := (enclosureDepth_le_iff D c (k+enclosureDepth D c)).mp (by omega)
  have h1 := (enclosureDepth_le_iff D c (k+enclosureDepth D c+1)).mp (by omega)
  rw [h0,h1]
  ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
