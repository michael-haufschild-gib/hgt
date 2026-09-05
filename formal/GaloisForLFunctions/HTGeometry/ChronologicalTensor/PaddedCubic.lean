import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Padding

/-!
# The cubic reversal form remains sealed with free padding

The padding gap is arbitrary and contributes to the same variation budget.
The unsealed 8/7 envelope and the one-enclosure quartic bound imply that this
additional freedom still leaves minimal enclosure depth exactly one.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem padded_reversal_bound (p a b c d e : ℝ) :
    |(p+(a+b+c+d+e))*reversalResponse a b c d e| ≤
      (|p|+sixCost a b c d e)^4 := by
  let V := sixCost a b c d e
  let P := reversalResponse a b c d e
  let S := a+b+c+d+e
  have hV : 0 ≤ V := by dsimp [V,sixCost]; positivity
  have hP : |P| ≤ (8/7 : ℝ)*V^3 := cubic_rational_envelope a b c d e
  have hSP : |S*P| ≤ V^4 := one_enclosure_reversal_bound a b c d e
  have hgap : (|p|+V)^4 - (|p| *((8/7 : ℝ)*V^3)+V^4) =
      |p|^4+4*|p|^3*V+6*|p|^2*V^2+(20/7 : ℝ)*|p| *V^3 := by ring
  have hn : 0 ≤ |p|^4+4*|p|^3*V+6*|p|^2*V^2+(20/7 : ℝ)*|p| *V^3 := by positivity
  change |(p+S)*P| ≤ (|p|+V)^4
  calc
    |(p+S)*P| = |p*P+S*P| := by congr 1; ring
    _ ≤ |p*P|+|S*P| := abs_add_le _ _
    _ = |p| * |P|+|S*P| := by rw [abs_mul]
    _ ≤ |p| *((8/7 : ℝ)*V^3)+V^4 :=
      add_le_add (mul_le_mul_of_nonneg_left hP (abs_nonneg p)) hSP
    _ ≤ (|p|+V)^4 := by linarith only [hgap,hn]

theorem padded_reversal_capacity_one_le :
    sealedCapacity (padWindows sixWindows) ![27,-1] 1 ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g,rfl⟩
  dsimp only
  rw [pow_one,familyValue_pad,sixWindows_reversal_value]
  let p := (normalizeProbe g) 0
  let h : Fin 5 → ℝ := fun i => (normalizeProbe g) i.succ
  have hd : displacement (normalizeProbe g) = p+(h 0+h 1+h 2+h 3+h 4) := by
    rw [displacement,Fin.sum_univ_succ]
    change p+displacement h = p+(h 0+h 1+h 2+h 3+h 4)
    simp only [displacement,Fin.sum_univ_five]
  rw [hd]
  have hb := padded_reversal_bound p (h 0) (h 1) (h 2) (h 3) (h 4)
  have hv := normalizeProbe_budget g
  rw [variation,Fin.sum_univ_succ] at hv
  change |p|+variation h ≤ 1 at hv
  rw [variation_six] at hv
  have hn : 0 ≤ |p|+sixCost (h 0) (h 1) (h 2) (h 3) (h 4) := by
    unfold sixCost; positivity
  have hp := pow_le_pow_left₀ hn hv 4
  rw [one_pow] at hp
  exact hb.trans hp

theorem padded_reversal_capacity (k : ℕ) :
    sealedCapacity (padWindows sixWindows) ![27,-1] (1+k) = 1 := by
  apply le_antisymm
  · exact (sealedCapacity_add_depth (padWindows sixWindows) (![27,-1] : Fin 2 → ℝ) 1 k).trans
      padded_reversal_capacity_one_le
  · have h := monotoneCapacity_le_sealed (padWindows sixWindows) (![27,-1] : Fin 2 → ℝ) (1+k)
    rw [monotoneCapacity_pad,sixWindows_reversal_monotoneCapacity] at h
    exact h

theorem padded_reversal_depth : enclosureDepth (padWindows sixWindows) ![27,-1] = 1 := by
  apply Nat.le_antisymm
  · apply (enclosureDepth_le_iff (padWindows sixWindows) (![27,-1] : Fin 2 → ℝ) 1).mpr
    rw [monotoneCapacity_pad,sixWindows_reversal_monotoneCapacity]
    exact padded_reversal_capacity 0
  · have h := padding_depth_monotone sixWindows (![27,-1] : Fin 2 → ℝ)
    rw [sixWindows_reversal_depth] at h
    exact h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
