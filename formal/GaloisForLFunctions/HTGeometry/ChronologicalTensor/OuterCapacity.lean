import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CommonCut
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.PaddedCubic

/-!
# Full outer-window capacity equals padded enclosure capacity

Payload and padding probes share one variation budget. Common-cut concentration
proves equality of the full outer response supremum with the padded enclosed
capacity, independently of the remaining outer-window arrangement. This
transfers finite degree sealing and the exact cubic result to free padding.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def jointNormalizer {n l : ℕ} (g : Fin n → ℝ) (q : Fin l → ℝ) : ℝ :=
  max 1 (variation g+variation q)

def outerProbeValue {n r m l k : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (W : Fin k → Finset (Fin l))
    (g : Fin n → ℝ) (q : Fin (l+1) → ℝ) : ℝ :=
  outerResponse W (displacement (fun i => g i / jointNormalizer g q))
    (familyValue D c (fun i => g i / jointNormalizer g q))
    (fun i => q i / jointNormalizer g q)

def outerCapacity {n r m l k : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (W : Fin k → Finset (Fin l)) : ℝ :=
  sSup (Set.range (fun x : (Fin n → ℝ) × (Fin (l+1) → ℝ) => |outerProbeValue D c W x.1 x.2|))

theorem variation_div {n : ℕ} (g : Fin n → ℝ) (t : ℝ) :
    variation (fun i => g i/t) = variation g / |t| := by
  simp only [variation,abs_div,Finset.sum_div]

theorem jointNormalizer_pos {n l : ℕ} (g : Fin n → ℝ) (q : Fin l → ℝ) :
    0 < jointNormalizer g q :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

theorem joint_normalized_budget {n l : ℕ} (g : Fin n → ℝ) (q : Fin l → ℝ) :
    variation (fun i => g i/jointNormalizer g q)+
      variation (fun i => q i/jointNormalizer g q) ≤ 1 := by
  rw [variation_div,variation_div,abs_of_pos (jointNormalizer_pos g q),← add_div]
  apply (div_le_iff₀ (jointNormalizer_pos g q)).mpr
  change variation g+variation q ≤ 1*max 1 (variation g+variation q)
  rw [one_mul]
  exact le_max_right _ _

theorem outerProbeValue_bound {n r m l k : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (W : Fin k → Finset (Fin l)) (g : Fin n → ℝ) (q : Fin (l+1) → ℝ) :
    |outerProbeValue D c W g q| ≤ sealedCapacity (padWindows D) c k := by
  let h : Fin n → ℝ := fun i => g i/jointNormalizer g q
  let t : Fin (l+1) → ℝ := fun i => q i/jointNormalizer g q
  let p := alignedPadding (displacement h) t
  let v : Fin (n+1) → ℝ := Fin.cons p h
  have hv : variation v ≤ 1 := by
    change variation (Fin.cons p h) ≤ 1
    rw [variation_cons]
    have he : |p| = variation t := (alignedPadding_data (displacement h) t).1
    rw [he]
    have hb := joint_normalized_budget g q
    change variation h+variation t ≤ 1 at hb
    linarith only [hb]
  have hn : normalizeProbe v = v := (normalizeProbe_fixed_iff v).mpr hv
  have hs := sealedCapacity_probe_bound (padWindows D) c k v
  rw [hn] at hs
  change |displacement (Fin.cons p h)^k*familyValue (padWindows D) c (Fin.cons p h)| ≤ _ at hs
  rw [familyValue_pad,displacement_cons] at hs
  simp only [Fin.cons_succ] at hs
  have hb := commonCut_collapse_dominates W (displacement h) (familyValue D c h) t
  rw [outerResponse_collapsed] at hb
  change |outerResponse W (displacement h) (familyValue D c h) t| ≤ _
  apply hb.trans
  change |familyValue D c h*(displacement h+p)^k| ≤ sealedCapacity (padWindows D) c k
  rw [add_comm (displacement h) p,mul_comm]
  exact hs

theorem outer_values_bddAbove {n r m l k : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (W : Fin k → Finset (Fin l)) :
    BddAbove (Set.range (fun x : (Fin n → ℝ) × (Fin (l+1) → ℝ) => |outerProbeValue D c W x.1 x.2|)) := by
  refine ⟨sealedCapacity (padWindows D) c k,?_⟩
  rintro _ ⟨⟨g,q⟩,rfl⟩
  exact outerProbeValue_bound D c W g q

theorem outerCapacity_eq_padded {n r m l k : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (W : Fin k → Finset (Fin l)) :
    outerCapacity D c W = sealedCapacity (padWindows D) c k := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨⟨g,q⟩,rfl⟩
    exact outerProbeValue_bound D c W g q
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨v,rfl⟩
    dsimp only
    let p := (normalizeProbe v) 0
    let h : Fin n → ℝ := fun i => (normalizeProbe v) i.succ
    let q : Fin (l+1) → ℝ := Fin.cons p (fun _ => 0)
    have hq : variation q = |p| := by
      change variation (Fin.cons p (fun _ : Fin l => 0)) = |p|
      rw [variation_cons]
      simp [variation]
    have hv := normalizeProbe_budget v
    rw [variation,Fin.sum_univ_succ] at hv
    change |p|+variation h ≤ 1 at hv
    have hd : jointNormalizer h q = 1 := by
      apply max_eq_left
      rw [hq]
      linarith only [hv]
    have hdv : displacement (normalizeProbe v) = p+displacement h := by
      rw [displacement,Fin.sum_univ_succ]
      rfl
    have hb := le_csSup (outer_values_bddAbove D c W) (Set.mem_range_self (h,q))
    change |outerProbeValue D c W h q| ≤ outerCapacity D c W at hb
    simp only [outerProbeValue,hd,div_one] at hb
    change |outerResponse W (displacement h) (familyValue D c h) (Fin.cons p (fun _ => 0))| ≤ _ at hb
    rw [outerResponse_collapsed] at hb
    rw [familyValue_pad,hdv]
    change |(p+displacement h)^k*familyValue D c h| ≤ outerCapacity D c W
    convert hb using 1
    rw [add_comm p (displacement h),mul_comm]

theorem outerCapacity_windows_independent {n r m l l' k : ℕ}
    (D : Fin m → Fin r → Finset (Fin n)) (c : Fin m → ℝ)
    (W : Fin k → Finset (Fin l)) (W' : Fin k → Finset (Fin l')) :
    outerCapacity D c W = outerCapacity D c W' := by
  rw [outerCapacity_eq_padded,outerCapacity_eq_padded]

theorem outerCapacity_degree_sealing {n r m l : ℕ}
    (D : Fin m → Fin (r+2) → Finset (Fin n)) (c : Fin m → ℝ) (k : ℕ)
    (W : Fin ((r+2)*(r+1)+k) → Finset (Fin l)) :
    outerCapacity D c W = monotoneCapacity D c := by
  rw [outerCapacity_eq_padded,padded_degree_sealing]

theorem outerCapacity_reversal {l k : ℕ} (W : Fin (1+k) → Finset (Fin l)) :
    outerCapacity sixWindows ![27,-1] W = 1 := by
  rw [outerCapacity_eq_padded,padded_reversal_capacity]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
