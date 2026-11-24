import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LeftOriginWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechSubsequence
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCoverSubcovers
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SingletonColumnBoundaries

/-! The joined Koszul column combines the homogeneous graph
equations with the left origin equations. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder κ] {d : ℕ}
  (T : WeightedChartSystem k d S E)

abbrev jointDegrees (n : κ → ℕ × ℕ) (l : κ ⊕ₗ Fin d) : ℕ × ℕ :=
  Sum.elim n (fun _ => (1, 0)) (ofLex l)

abbrev jointWeights (z : κ → S) (l : κ ⊕ₗ Fin d) : S :=
  Sum.elim z T.leftOriginWeights (ofLex l)

omit [LinearOrder κ] in
/-- Both halves of the joint column retain their original chart
normalizations. -/
theorem jointWeights_admitted (hT : T.Good) {n : κ → ℕ × ℕ} {z : κ → S}
    (hz : T.Admitted n z) : T.Admitted (jointDegrees n) (T.jointWeights z) := by
  intro i j l
  obtain ⟨l, rfl⟩ := (toLex : κ ⊕ Fin d ≃ κ ⊕ₗ Fin d).surjective l
  rcases l with a | b
  · exact hz i j a
  · exact T.leftOriginWeights_admitted hT i j b

theorem restrict_joint_left_mem_cycles {n : κ → ℕ × ℕ} {z : κ → S} {m : ℤ}
    {c : Finset (ChartPair d ⊕ₗ (κ ⊕ₗ Fin d)) → E}
    (hc : c ∈ (T.complex (jointDegrees (d := d) n) (T.jointWeights z)).Z m) :
    restrictKoszulIndices (joinedLeft (κ := Fin d)) c ∈ (T.complex n z).Z m := by
  let e : κ ↪o κ ⊕ₗ Fin d := joinedLeft
  let N : κ ⊕ₗ Fin d → ℕ × ℕ := jointDegrees n
  let W := T.jointWeights z
  have hn : N ∘ e = n := funext fun _ => rfl
  have hw : W ∘ e = z := funext fun _ => rfl
  have h := T.restrictKoszulIndices_mem_cycles e (n := N) (z := W) (p := m) (a := c) hc
  exact (congrArg₂ (fun a b => T.complex a b) hn hw) ▸ h

theorem restrict_joint_right_mem_cycles {n : κ → ℕ × ℕ} {z : κ → S} {m : ℤ}
    {c : Finset (ChartPair d ⊕ₗ (κ ⊕ₗ Fin d)) → E}
    (hc : c ∈ (T.complex (jointDegrees (d := d) n) (T.jointWeights z)).Z m) :
    restrictKoszulIndices (joinedRight (ι := κ)) c ∈
      (T.complex (fun _ => (1, 0)) T.leftOriginWeights).Z m := by
  let e : Fin d ↪o κ ⊕ₗ Fin d := joinedRight
  let N : κ ⊕ₗ Fin d → ℕ × ℕ := jointDegrees n
  let W := T.jointWeights z
  have hn : N ∘ e = fun _ => (1, 0) := funext fun _ => rfl
  have hw : W ∘ e = T.leftOriginWeights := funext fun _ => rfl
  have h := T.restrictKoszulIndices_mem_cycles e (n := N) (z := W) (p := m) (a := c) hc
  exact (congrArg₂ (fun a b => T.complex a b) hn hw) ▸ h

/-- Comparing both restrictions of a joint cocycle on singleton columns
identifies the two chart projections modulo a mixed Čech boundary. -/
theorem chartPart_sub_mem_boundary_of_joint [Fintype κ]
    (hT : T.Good) {n : κ → ℕ × ℕ} {z : κ → S} (hz : T.Admitted n z)
    {c : Finset (ChartPair d ⊕ₗ (κ ⊕ₗ Fin d)) → E}
    {g : Finset (ChartPair d ⊕ₗ κ) → E} {t : Finset (ChartPair d ⊕ₗ Fin d) → E}
    (hc : c ∈ (T.complex (jointDegrees (d := d) n) (T.jointWeights z)).Z ((d : ℤ) + 2))
    (hg : g ∈ (T.complex n z).Z ((d : ℤ) + 2))
    (ht : t ∈ (T.complex (fun _ => (1, 0)) T.leftOriginWeights).Z ((d : ℤ) + 2))
    (hexG : ∀ I J, I.Nonempty → J.Nonempty → ∀ m < (d : ℤ),
      (T.columnComplex n z I J).Z m ≤ (T.columnComplex n z I J).B m)
    (hexT : ∀ I J, I.Nonempty → J.Nonempty → ∀ m < (d : ℤ),
      (T.columnComplex (fun _ => (1, 0)) T.leftOriginWeights I J).Z m ≤
        (T.columnComplex (fun _ => (1, 0)) T.leftOriginWeights I J).B m)
    (hcolG : ∀ i j : Fin (d + 1), (fun L => g (uni (uni {i} {j}) L) -
      c (uni (uni {i} {j}) (uni L ∅))) ∈ (T.columnComplex n z {i} {j}).B (d : ℤ))
    (hcolT : ∀ i j : Fin (d + 1), (fun L => c (uni (uni {i} {j}) (uni ∅ L)) -
      t (uni (uni {i} {j}) L)) ∈
        (T.columnComplex (fun _ => (1, 0)) T.leftOriginWeights {i} {j}).B (d : ℤ)) :
    chartPart g - chartPart t ∈ (mixedCech T.M).B ((d : ℤ) + 2) := by
  let eG : κ ↪o κ ⊕ₗ Fin d := joinedLeft
  let eT : Fin d ↪o κ ⊕ₗ Fin d := joinedRight
  let cG := restrictKoszulIndices eG c
  let cT := restrictKoszulIndices eT c
  have hcG : cG ∈ (T.complex n z).Z ((d : ℤ) + 2) :=
    T.restrict_joint_left_mem_cycles (n := n) (z := z) hc
  have hcT : cT ∈ (T.complex (fun _ => (1, 0)) T.leftOriginWeights).Z ((d : ℤ) + 2) :=
    T.restrict_joint_right_mem_cycles (n := n) (z := z) hc
  have hbG : chartPart (g - cG) ∈ (mixedCech T.M).B ((d : ℤ) + 2) := by
    refine T.chartPart_mem_boundaries_of_singletonColumns hT hz hexG (sub_mem hg hcG) ?_
    intro i j
    simpa only [Pi.sub_apply, cG, eG, restrictKoszulIndices, lft_uni, rgt_uni, map_joinedLeft]
      using hcolG i j
  have hbT : chartPart (cT - t) ∈ (mixedCech T.M).B ((d : ℤ) + 2) := by
    refine T.chartPart_mem_boundaries_of_singletonColumns hT
      (T.leftOriginWeights_admitted hT) hexT (sub_mem hcT ht) ?_
    intro i j
    simpa only [Pi.sub_apply, cT, eT, restrictKoszulIndices, lft_uni, rgt_uni, map_joinedRight]
      using hcolT i j
  change chartPart g - chartPart cG ∈ _ at hbG
  change chartPart cT - chartPart t ∈ _ at hbT
  rw [show chartPart cG = chartPart c from chartPart_restrictKoszulIndices eG c] at hbG
  rw [show chartPart cT = chartPart c from chartPart_restrictKoszulIndices eT c] at hbT
  simpa only [sub_add_sub_cancel] using add_mem hbG hbT

end GlobalTheory.WH.WeightedChartSystem
