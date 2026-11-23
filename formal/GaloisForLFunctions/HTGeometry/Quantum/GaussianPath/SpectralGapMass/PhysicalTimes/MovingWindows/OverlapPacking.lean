import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Packing dates with large overlap against one target -/
open Finset MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- A fixed target with overlap at least κ cannot see more than
2/κ² vectors whose mutual overlaps are at most κ²/2. -/
theorem common_target_card {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset I) (u : I → E) (z : E) {κ : ℝ} (hκ : 0 < κ) (hz : ‖z‖ ≤ 1)
    (hu : ∀ i∈S, ‖u i‖ ≤ 1) (hh : ∀ i∈S, κ ≤ ‖inner ℂ (u i) z‖)
    (hsep : ∀ i∈S, ∀ j∈S, i≠j → ‖inner ℂ (u i) (u j)‖ ≤ κ^2/2) :
    (S.card:ℝ) ≤ 2/κ^2 := by
  classical
  let d := κ^2/2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hrow (i) (hi : i∈S) : ∑ j∈S, ‖inner ℂ (u i) (u j)‖ ≤ 1+S.card*d := by
    calc _ ≤ ∑ j∈S, ((if j=i then (1:ℝ) else 0)+d) := by
           apply sum_le_sum
           intro j hj
           by_cases h : j=i
           · subst j
             rw [if_pos rfl]
             exact (norm_inner_le_norm (𝕜:=ℂ) _ _).trans
               (((mul_le_mul (hu i hi) (hu i hi) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)).trans
                 (le_add_of_nonneg_right hd))
           · simpa only [if_neg h,zero_add] using hsep i hi j hj (Ne.symm h)
         _ = _ := by simp [sum_add_distrib,hi]
  have hs := _root_.RHTower.Sieve.sum_norm_inner_sq_le_of_schur S u
    (show 0 ≤ 1+(S.card:ℝ)*d by positivity) hrow z
  have hhit : (S.card:ℝ)*κ^2 ≤ ∑ i∈S, ‖inner ℂ (u i) z‖^2 := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum
      (fun i hi => pow_le_pow_left₀ hκ.le (hh i hi) 2)
  have hnorm : ‖z‖^2 ≤ 1 := (pow_le_pow_left₀ (norm_nonneg z) hz 2).trans_eq (one_pow _)
  have hb := hhit.trans (hs.trans (mul_le_of_le_one_right (by positivity) hnorm))
  apply (le_div_iff₀ (sq_pos_of_pos hκ)).mpr
  dsimp only [d] at hb
  linarith only [hb]

/-- A finite packing bound gives an interval cover without any
measurability assumption on the set of dates. -/
theorem cover_of_separated_card (B : ℕ) (s : Set ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hpack : ∀ F : Finset ℝ, (↑F : Set ℝ) ⊆ s →
      (∀ x∈F, ∀ y∈F, x≠y → r < |x-y|) → F.card ≤ B) :
    ∃ F : Finset ℝ, F.card ≤ B ∧ s ⊆ ⋃ x∈F, Icc (x-r) (x+r) := by
  classical
  induction B generalizing s with
  | zero =>
    refine ⟨∅,by simp,?_⟩
    intro x hx
    have h := hpack {x} (by simpa using hx) (by simp)
    simp at h
  | succ B ih =>
    rcases s.eq_empty_or_nonempty with h|⟨x,hx⟩
    · exact ⟨∅,by simp,h ▸ empty_subset _⟩
    let A := s \ Icc (x-r) (x+r)
    have hprev (F : Finset ℝ) (hF : (↑F : Set ℝ) ⊆ A)
        (hd : ∀ v∈F, ∀ w∈F, v≠w → r < |v-w|) : F.card ≤ B := by
      have hfar (v) (hv : v∈F) : r < |v-x| := by
        apply lt_of_not_ge
        intro hc
        obtain ⟨h₁,h₂⟩ := abs_le.mp hc
        exact (hF hv).2 ⟨by linarith only [h₁],by linarith only [h₂]⟩
      have hxF : x∉F := fun h => (by simpa only [sub_self,abs_zero] using hfar x h : r < 0).not_ge hr
      have hp := hpack (insert x F) (by
        intro v hv
        rcases mem_insert.mp hv with rfl|hv
        · exact hx
        · exact (hF hv).1) (by
        intro v hv w hw hne
        by_cases hvx : v=x
        · subst v
          rw [abs_sub_comm]
          exact hfar w ((mem_insert.mp hw).resolve_left (Ne.symm hne))
        · have hvF := (mem_insert.mp hv).resolve_left hvx
          rcases mem_insert.mp hw with hwx|hwF
          · rw [hwx]; exact hfar v hvF
          · exact hd v hvF w hwF hne)
      rwa [card_insert_of_notMem hxF,Nat.succ_le_succ_iff] at hp
    obtain ⟨F,hsize,hcover⟩ := ih A hprev
    refine ⟨insert x F,(card_insert_le ..).trans (Nat.succ_le_succ hsize),?_⟩
    intro v hv
    by_cases h : v∈Icc (x-r) (x+r)
    · exact mem_iUnion₂.mpr ⟨x,mem_insert_self ..,h⟩
    · obtain ⟨w,hw,hv'⟩ := mem_iUnion₂.mp (hcover (show v∈A from ⟨hv,h⟩))
      exact mem_iUnion₂.mpr ⟨w,mem_insert_of_mem hw,hv'⟩

/-- The length of any set admitting at most B separated dates is at most 2Br. -/
theorem volume_of_separated_card (B : ℕ) (s : Set ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hpack : ∀ F : Finset ℝ, (↑F : Set ℝ) ⊆ s →
      (∀ x∈F, ∀ y∈F, x≠y → r < |x-y|) → F.card ≤ B) :
    volume.real s ≤ B*(2*r) := by
  obtain ⟨F,hF,hsub⟩ := cover_of_separated_card B s hr hpack
  let I (x : ℝ) := Icc (x-r) (x+r)
  have hfin : volume (⋃ x∈F, I x)≠⊤ := by
    apply ne_top_of_le_ne_top _ (measure_biUnion_finset_le F I)
    exact ENNReal.sum_ne_top.mpr (fun x _ => measure_Icc_lt_top.ne)
  apply (measureReal_mono hsub hfin).trans
  apply (measureReal_biUnion_finset_le F I).trans
  have hlen (x) : volume.real (I x)=2*r := by
    dsimp only [I]
    rw [Real.volume_real_Icc_of_le (by linarith only [hr])]
    ring
  simp only [hlen,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hF) (by positivity)

#print axioms common_target_card
#print axioms volume_of_separated_card
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
