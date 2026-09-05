import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CurvatureDepth

/-!
# Padding a chronological window family

Adding an unused gap preserves both signed and monotone capacity. Once the
net displacement is used as an enclosure factor, the new gap can affect the
response, so enclosed capacity and minimal depth can only increase. The
universal degree bound remains valid because the polynomial degree is unchanged.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def padWindows {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n)) :
    Fin m → Fin r → Finset (Fin (n+1)) := fun j k => (D j k).map (Fin.succEmb n)

theorem windowValue_pad {n : ℕ} (W : Finset (Fin n)) (g : Fin (n+1) → ℝ) :
    windowValue (W.map (Fin.succEmb n)) g = windowValue W (fun i => g i.succ) := by
  simp only [windowValue,Finset.sum_map,Fin.coe_succEmb]

theorem familyValue_pad {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin (n+1) → ℝ) :
    familyValue (padWindows D) c g = familyValue D c (fun i => g i.succ) := by
  simp only [familyValue,diagramValue,padWindows,windowValue_pad]

theorem variation_cons {n : ℕ} (p : ℝ) (g : Fin n → ℝ) :
    variation (Fin.cons p g) = |p|+variation g := by
  simp only [variation,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem displacement_cons {n : ℕ} (p : ℝ) (g : Fin n → ℝ) :
    displacement (Fin.cons p g) = p+displacement g := by
  simp only [displacement,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem normalizeProbe_zero_cons {n : ℕ} (g : Fin n → ℝ) :
    normalizeProbe (Fin.cons 0 g) = Fin.cons 0 (normalizeProbe g) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [normalizeProbe,variation_cons]
  · simp [normalizeProbe,variation_cons]

theorem normalized_tail_budget {n : ℕ} (g : Fin (n+1) → ℝ) :
    variation (fun i : Fin n => (normalizeProbe g) i.succ) ≤ 1 := by
  have h := normalizeProbe_budget g
  simp only [variation,Fin.sum_univ_succ] at h
  change (∑ i : Fin n, |(normalizeProbe g) i.succ|) ≤ 1
  linarith only [h,abs_nonneg ((normalizeProbe g) 0)]

theorem familyCapacity_pad {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : familyCapacity (padWindows D) c = familyCapacity D c := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    rw [familyValue_pad]
    let h : Fin n → ℝ := fun i => (normalizeProbe g) i.succ
    have hf : normalizeProbe h = h := (normalizeProbe_fixed_iff h).mpr (normalized_tail_budget g)
    have hb := familyCapacity_probe_bound D c h
    rw [hf] at hb
    exact hb
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    have hb := familyCapacity_probe_bound (padWindows D) c (Fin.cons 0 g)
    rw [normalizeProbe_zero_cons,familyValue_pad] at hb
    simpa only [Fin.cons_succ] using hb

theorem monotoneCapacity_pad {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : monotoneCapacity (padWindows D) c = monotoneCapacity D c := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    rw [familyValue_pad]
    let h : Fin n → ℝ := fun i => (normalizeProbe g) i.succ
    have hf : normalizeProbe h = h := (normalizeProbe_fixed_iff h).mpr (normalized_tail_budget g)
    have hb := monotoneCapacity_probe_bound D c h
    have he : monotoneProbe h = fun i => monotoneProbe g i.succ := by
      funext i
      simp only [monotoneProbe,hf]
      rfl
    rw [he] at hb
    exact hb
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    change |familyValue D c (fun i => |(normalizeProbe g) i|)| ≤ monotoneCapacity (padWindows D) c
    have hb := monotoneCapacity_probe_bound (padWindows D) c (Fin.cons 0 g)
    rw [familyValue_pad] at hb
    simpa only [monotoneProbe,normalizeProbe_zero_cons,Fin.cons_succ] using hb

theorem sealedCapacity_le_pad {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) : sealedCapacity D c k ≤ sealedCapacity (padWindows D) c k := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g,rfl⟩
  dsimp only
  have hb := sealedCapacity_probe_bound (padWindows D) c k (Fin.cons 0 g)
  rw [normalizeProbe_zero_cons,familyValue_pad,displacement_cons] at hb
  simpa only [Fin.cons_succ,zero_add] using hb

theorem padded_degree_sealing {n r m : ℕ} (D : Fin m → Fin (r+2) → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) :
    sealedCapacity (padWindows D) c ((r+2)*(r+1)+k) = monotoneCapacity D c := by
  rw [quadratic_sealing_allDepths,monotoneCapacity_pad]

theorem padding_depth_monotone {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) : enclosureDepth D c ≤ enclosureDepth (padWindows D) c := by
  apply (enclosureDepth_le_iff D c _).mpr
  apply le_antisymm _ (monotoneCapacity_le_sealed D c _)
  have h := sealedCapacity_le_pad D c (enclosureDepth (padWindows D) c)
  rw [enclosureDepth_spec,monotoneCapacity_pad] at h
  exact h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
