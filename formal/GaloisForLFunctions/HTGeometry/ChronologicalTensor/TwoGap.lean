import GaloisForLFunctions.HTGeometry.ChronologicalTensor.ThreeBlock
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Sealing

/-!
# Two-gap probes cannot reveal pairing reversal advantage

Enumerated perfect pairings are represented by actual interval windows,
with orientation signs absorbed into coefficients. Two ordered cuts give
three consecutive endpoint blocks. Three-block factorization then proves
that replacing both increments by their absolute values increases absolute
response without changing the two-gap cost. Every normalized two-gap probe
is consequently bounded by the full monotone capacity.

Gap space includes a terminal unused coordinate, so each endpoint and each
cut share Fin (2*d); this coordinate never belongs to an interval window.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def endpointOrderSign {n : ℕ} (a b : Fin n) : ℝ := if a ≤ b then 1 else -1

def endpointPulse {n : ℕ} (a : Fin n) (w : ℝ) (q : Fin n) : ℝ := if a < q then w else 0

def twoGapProbe {n : ℕ} (a b : Fin n) (u v : ℝ) : Fin n → ℝ :=
  fun q => (if q=a then u else 0)+(if q=b then v else 0)

def twoGapPositions {n : ℕ} (a b : Fin n) (u v : ℝ) : Fin n → ℝ :=
  fun q => endpointPulse a u q+endpointPulse b v q

def enumeratedPairingWindows {d : ℕ} (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) :
    Fin d → Finset (Fin (2*d)) := fun i =>
  Finset.Ico (min (e (Sum.inl i)) (e (Sum.inr i))) (max (e (Sum.inl i)) (e (Sum.inr i)))

def enumeratedPairingSign {d : ℕ} (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) : ℝ :=
  ∏ i, endpointOrderSign (e (Sum.inl i)) (e (Sum.inr i))

def enumeratedFamilyWindows {d m : ℕ} (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) :
    Fin m → Fin d → Finset (Fin (2*d)) := fun j => enumeratedPairingWindows (E j)

def enumeratedFamilyCoefficients {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) : Fin m → ℝ :=
  fun j => c j*enumeratedPairingSign (E j)

theorem windowValue_twoGap {n : ℕ} (W : Finset (Fin n)) (a b : Fin n) (u v : ℝ) :
    windowValue W (twoGapProbe a b u v) =
      (if a∈W then u else 0)+(if b∈W then v else 0) := by
  simp [windowValue,twoGapProbe,Finset.sum_add_distrib]

theorem endpointPulse_difference {n : ℕ} (cut a b : Fin n) (w : ℝ) :
    endpointPulse cut w b-endpointPulse cut w a = endpointOrderSign a b*
      (if cut ∈ Finset.Ico (min a b) (max a b) then w else 0) := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab,max_eq_right hab]
    simp only [endpointPulse,endpointOrderSign,if_pos hab,one_mul,Finset.mem_Ico]
    split_ifs <;> simp_all <;> omega
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba,max_eq_left hba]
    simp only [endpointPulse,endpointOrderSign,if_neg hab,neg_one_mul,Finset.mem_Ico]
    split_ifs <;> simp_all <;> omega

theorem enumeratedPairing_twoGap_value {d : ℕ}
    (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) (a b : Fin (2*d)) (u v : ℝ) :
    enumeratedPairingValue e (twoGapPositions a b u v) = enumeratedPairingSign e*
      diagramValue (enumeratedPairingWindows e) (twoGapProbe a b u v) := by
  have hi (i : Fin d) :
      twoGapPositions a b u v (e (Sum.inr i))-twoGapPositions a b u v (e (Sum.inl i)) =
        endpointOrderSign (e (Sum.inl i)) (e (Sum.inr i))*
          windowValue (enumeratedPairingWindows e i) (twoGapProbe a b u v) := by
    dsimp only [twoGapPositions]
    rw [show endpointPulse a u (e (Sum.inr i))+endpointPulse b v (e (Sum.inr i))-
        (endpointPulse a u (e (Sum.inl i))+endpointPulse b v (e (Sum.inl i))) =
      (endpointPulse a u (e (Sum.inr i))-endpointPulse a u (e (Sum.inl i)))+
      (endpointPulse b v (e (Sum.inr i))-endpointPulse b v (e (Sum.inl i))) by ring]
    rw [endpointPulse_difference,endpointPulse_difference,windowValue_twoGap]
    unfold enumeratedPairingWindows
    ring
  simp only [enumeratedPairingValue,hi,Finset.prod_mul_distrib,enumeratedPairingSign,diagramValue]

theorem enumeratedFamily_twoGap_value {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (a b : Fin (2*d)) (u v : ℝ) :
    familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
      (twoGapProbe a b u v) = enumeratedPairingFamilyValue E c (twoGapPositions a b u v) := by
  simp only [familyValue,enumeratedFamilyWindows,enumeratedFamilyCoefficients,
    enumeratedPairingFamilyValue,enumeratedPairing_twoGap_value,mul_assoc]

def secondCut {n : ℕ} (a : Fin n) (offset : Fin (n-a.val-1)) : Fin n :=
  ⟨a.val+1+offset.val,by have h := offset.isLt; omega⟩

theorem secondCut_after {n : ℕ} (a : Fin n) (offset : Fin (n-a.val-1)) :
    a < secondCut a offset := by
  change a.val < a.val+1+offset.val
  omega

def consecutiveColors {n : ℕ} (a b : Fin n) (q : Fin n) : Fin 3 :=
  if q ≤ a then 0 else if q ≤ b then 1 else 2

theorem twoGapPositions_threeBlock {n : ℕ} (a : Fin n) (offset : Fin (n-a.val-1)) (u v : ℝ) :
    twoGapPositions a (secondCut a offset) u v =
      fun q => threeBlockPosition u v (consecutiveColors a (secondCut a offset) q) := by
  have hab := secondCut_after a offset
  ext q
  by_cases hqa : q ≤ a
  · have hqb : q ≤ secondCut a offset := hqa.trans hab.le
    simp [twoGapPositions,endpointPulse,consecutiveColors,threeBlockPosition,hqa,
      not_lt.mpr hqa,not_lt.mpr hqb]
  · by_cases hqb : q ≤ secondCut a offset
    · simp [twoGapPositions,endpointPulse,consecutiveColors,threeBlockPosition,hqa,hqb,
        lt_of_not_ge hqa,not_lt.mpr hqb]
    · simp [twoGapPositions,endpointPulse,consecutiveColors,threeBlockPosition,hqa,hqb,
        lt_of_not_ge hqa,lt_of_not_ge hqb]

theorem twoGapProbe_absolute {n : ℕ} (a : Fin n) (offset : Fin (n-a.val-1)) (u v : ℝ) :
    (fun q => |twoGapProbe a (secondCut a offset) u v q|) =
      twoGapProbe a (secondCut a offset) (|u|) (|v|) := by
  have hne : a ≠ secondCut a offset := ne_of_lt (secondCut_after a offset)
  ext q
  by_cases hqa : q=a
  · subst q
    simp [twoGapProbe,hne]
  · by_cases hqb : q=secondCut a offset
    · subst q
      simp [twoGapProbe,hne.symm]
    · simp [twoGapProbe,hqa,hqb]

theorem enumeratedFamily_twoGap_absolute {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (a : Fin (2*d)) (offset : Fin (2*d-a.val-1)) (u v : ℝ) :
    |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
      (twoGapProbe a (secondCut a offset) u v)| ≤
      |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
        (fun q => |twoGapProbe a (secondCut a offset) u v q|)| := by
  rw [twoGapProbe_absolute,enumeratedFamily_twoGap_value,enumeratedFamily_twoGap_value,
    twoGapPositions_threeBlock,twoGapPositions_threeBlock]
  exact enumeratedPairingFamily_threeBlock_absolute E c _ u v

theorem normalizeProbe_twoGap {n : ℕ} (a b : Fin n) (u v : ℝ) :
    normalizeProbe (twoGapProbe a b u v) = twoGapProbe a b
      (u/max 1 (variation (twoGapProbe a b u v))) (v/max 1 (variation (twoGapProbe a b u v))) := by
  ext q
  simp only [normalizeProbe,twoGapProbe,add_div]
  split_ifs <;> simp

theorem enumeratedFamily_twoGap_capacity_bound {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (a : Fin (2*d)) (offset : Fin (2*d-a.val-1)) (u v : ℝ) :
    |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
      (normalizeProbe (twoGapProbe a (secondCut a offset) u v))| ≤
      monotoneCapacity (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) := by
  let g := twoGapProbe a (secondCut a offset) u v
  have h := enumeratedFamily_twoGap_absolute E c a offset
    (u/max 1 (variation g)) (v/max 1 (variation g))
  have hn := normalizeProbe_twoGap a (secondCut a offset) u v
  change normalizeProbe g = _ at hn
  rw [← hn] at h
  exact h.trans (monotoneCapacity_probe_bound (enumeratedFamilyWindows E)
    (enumeratedFamilyCoefficients E c) g)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
