import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Outgoing
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.SingleReading

/-! # Signed damping from the first unequal peak-relative loss of one unlabeled law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Peak.Ranks Peak.Ranks.Capped _root_.HTGeometry
open scoped ComplexConjugate

/-- The model identifies which edge owns its first unmatched level. The measured edge
identifies the sign, while the location of that level gives the absolute scale. -/
def oriented (d : ℝ) (L A B : Set ℝ) : ℝ := by
  classical
  let v := sInf (differences A B)
  exact if A=B then 0 else if (d ∈ L ↔ v ∈ A) then v/d else -(v/d)

private theorem oriented_congr {d : ℝ} {L U : Set ℝ} (A B : Set ℝ) (h : d ∈ L ↔ d ∈ U) :
    oriented d L A B = oriented d U A B := by
  classical
  by_cases he : A=B
  · simp only [oriented,if_pos he]
  · simp only [oriented,if_neg he,h]

private theorem mem_scale {p x : ℝ} (hp : 0 < p) (A : Set ℝ) :
    p*x ∈ scale p A ↔ x ∈ A := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact (mul_right_injective₀ hp.ne' he) ▸ hy
  · intro hx; exact ⟨x,hx,rfl⟩

private theorem orient_scale {L U : Set ℝ} {d p : ℝ} (hd : 0 < d) (h : IsLeast (differences L U) d)
    (hp : 0 < p) :
    oriented d L (scale p L) (scale p U) = p ∧ oriented d L (scale p U) (scale p L) = -p := by
  classical
  have hv : IsLeast (differences (scale p L) (scale p U)) (p*d) := least_scaled hp h
  have hv' : IsLeast (differences (scale p U) (scale p L)) (p*d) := by
    simpa only [differences,Set.union_comm] using hv
  have hne : scale p L ≠ scale p U := by
    intro he
    have bad := hv.1
    simp only [he,differences,Set.sdiff_self,Set.union_self,Set.mem_empty_iff_false] at bad
  have flip : ¬(d ∈ L ↔ p*d ∈ scale p U) := by
    rw [mem_scale hp]
    rcases h.1 with h | h
    · exact fun he => h.2 (he.mp h.1)
    · exact fun he => h.2 (he.mpr h.1)
  constructor
  · rw [oriented,if_neg hne,hv.csInf_eq,if_pos (mem_scale hp L).symm,mul_div_cancel_right₀ _ hd.ne']
  · rw [oriented,if_neg hne.symm,hv'.csInf_eq,if_neg flip,mul_div_cancel_right₀ _ hd.ne']

variable {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ)

theorem first_positive (h : (candidates c m).Nonempty) : 0 < (candidates c m).min' h := by
  let d := (candidates c m).min' h
  obtain ⟨w⟩ := state_of_candidate c m ((candidates c m).min'_mem h)
  obtain ⟨g,u,_,_,lo,hi,ext⟩ := anchors w
  have lz : (0 : ℝ) ∈ lowerEdge c m := ⟨g,by rw [lo]; exact sub_self _⟩
  have uz : (0 : ℝ) ∈ upperEdge c m := ⟨u,by rw [hi]; exact sub_self _⟩
  have dim : d ∈ differences (lowerEdge c m) (upperEdge c m) := (first_unpaired c m h).1
  change 0 < d
  rcases dim with ⟨⟨x,hx⟩,hn⟩ | ⟨⟨x,hx⟩,hn⟩
  · change energy (level x)-baseline price c m = d at hx
    exact lt_of_le_of_ne (by linarith only [hx,lo,(ext x).1]) (fun eq => hn (eq ▸ uz))
  · change -energy (level x)-baseline reversePrice c m = d at hx
    exact lt_of_le_of_ne (by linarith only [hx,hi,(ext x).2]) (fun eq => hn (eq ▸ lz))

theorem thermal_orientation (h : (candidates c m).Nonempty) (t : ℝ) :
    oriented ((candidates c m).min' h) (lowerEdge c m) (thermalLosses c m t) (thermalLosses c m (-t)) = t := by
  obtain ⟨w⟩ := state_of_candidate c m ((candidates c m).min'_mem h)
  rcases lt_trichotomy 0 t with pos | zero | neg
  · obtain ⟨hl,hu⟩ := thermal_edges c m w t pos.le
    rw [hl,hu]
    exact (orient_scale (first_positive c m h) (first_unpaired c m h) pos).1
  · subst t; simp [oriented]
  · have pos := neg_pos.mpr neg
    obtain ⟨hl,hu⟩ := thermal_edges c m w (-t) pos.le
    rw [neg_neg] at hu
    rw [hl,hu]
    simpa only [neg_neg] using (orient_scale (first_positive c m h) (first_unpaired c m h) pos).2

def decode (h : (candidates c m).Nonempty) (P : State c m → ℝ) :=
  oriented ((candidates c m).min' h) (↑(readings price c (center c m) m)) (losses P) (losses (reciprocalLaw P))

/-- Every sector with an asymmetric energy spectrum recovers signed damping from a single
outgoing distribution, even when many leading relative probabilities agree under reflection. -/
theorem decode_outgoing (h : (candidates c m).Nonempty) (s : ℂ) :
    decode c m h (fun x => outgoingShare s x) = 2*s.re-1 := by
  rw [decode,reciprocal_outgoing S c m s]
  change oriented _ _ (outputSpectrum c m s) (outputSpectrum c m (1-conj s)) = _
  rw [spectrum_eq,spectrum_eq,opposite]
  have side := candidate_side c m ((candidates c m).min'_mem h)
  exact (oriented_congr _ _ side).trans (thermal_orientation c m h (2*s.re-1))

theorem decode_zero_iff_isometry (h : (candidates c m).Nonempty) (s : ℂ) :
    decode c m h (fun x => outgoingShare s x) = 0 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [decode_outgoing,split_isometric_iff]
  constructor <;> intro he <;> linarith only [he]

#print axioms first_positive
#print axioms thermal_orientation
#print axioms decode_outgoing
#print axioms decode_zero_iff_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
