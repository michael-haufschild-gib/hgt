import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SelectedOverlap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SeamDensity

/-! # Reading a physical bond signal from a finite coefficient window -/
open MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
open WeakBonds
noncomputable section

abbrev WindowRows (L : ℕ) := (Fin L × PathPauliDirections) → ℝ

def readWindow (j L : ℕ) (ω : PathPauliDisorder) : WindowRows L :=
  fun q => ω (j+q.1.val,q.2)

def extendWindow {L : ℕ} (j : ℕ) (x : WindowRows L) : PathPauliDisorder :=
  fun q => if h : j≤q.1 ∧ q.1-j<L then x (⟨q.1-j,h.2⟩,q.2) else 0

theorem measurable_extendWindow {L : ℕ} (j : ℕ) : Measurable (extendWindow (L:=L) j) := by
  apply measurable_pi_lambda
  intro q
  by_cases h : j≤q.1 ∧ q.1-j<L
  · simpa only [extendWindow,dif_pos h] using (measurable_pi_apply ((⟨q.1-j,h.2⟩ : Fin L),q.2) :
      Measurable (fun x : WindowRows L => x (⟨q.1-j,h.2⟩,q.2)))
  · simp only [extendWindow,dif_neg h]
    exact measurable_const

theorem recover_window {L j k : ℕ} (ω : PathPauliDisorder) (hj : j≤k) (hk : k<j+L)
    (d : PathPauliDirections) : extendWindow j (readWindow j L ω) (k,d)=ω (k,d) := by
  simp only [extendWindow,dif_pos (show j≤k ∧ k-j<L from ⟨hj,by omega⟩),readWindow]
  rw [Nat.add_sub_of_le hj]

private theorem edge_congr {n : ℕ} (ω ω' : PathPauliDisorder) (e : Fin (n+1))
    (h : ∀ d : PathPauliDirections, ω (e.val,d)=ω' (e.val,d)) :
    edgePart (pathPauliDisorderShell ω n) e=edgePart (pathPauliDisorderShell ω' n) e := by
  unfold edgePart
  exact Finset.sum_congr rfl fun q _ => by
    change (ω (e.val,.inr q):ℂ) • _=(ω' (e.val,.inr q):ℂ) • _
    rw [h]

private theorem packet_congr {n : ℕ} (ω ω' : PathPauliDisorder) (a b : Fin (n+1))
    (h : ∀ i : ℕ, a.val ≤ i → i≤b.val → ∀ d : PathPauliDirections, ω (i,d)=ω' (i,d)) :
    packet (pathPauliDisorderShell ω n) (middleBlock a b)=
      packet (pathPauliDisorderShell ω' n) (middleBlock a b) := by
  have ht {v : Fin (n+2)} (hv : v∈middleBlock a b) : a.val≤v.val ∧ v.val≤b.val :=
    ⟨(Finset.mem_Ioc.mp hv).1.le,(Finset.mem_Ioc.mp hv).2⟩
  unfold packet
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    split
    next hi =>
      unfold onsiteAt
      apply Finset.sum_congr rfl
      intro q _
      change (ω (i.val,.inl q):ℂ) • _=(ω' (i.val,.inl q):ℂ) • _
      rw [h i.val (ht hi).1 (ht hi).2]
    next => rfl
  · apply Finset.sum_congr rfl
    intro e _
    split
    next he => exact edge_congr ω ω' e (h e.val (ht he.1).1 (ht he.1).2)
    next => rfl

/-- Resampling the entire exterior of a window changes the middle bond
signal by at most four times the time and total bracketing edge norm. -/
theorem window_signal_change {n : ℕ} (ω ω' : PathPauliDisorder) {a b e : Fin (n+1)}
    (ha : a<e) (hb : e<b) (t : ℝ)
    (h : ∀ i : ℕ, a.val ≤ i → i≤b.val → ∀ d : PathPauliDirections, ω (i,d)=ω' (i,d)) :
    |bondSignal e (pathPauliDisorderShell ω n) t-bondSignal e (pathPauliDisorderShell ω' n) t| ≤
      4*|t| *(‖edgePart (pathPauliDisorderShell ω n) a‖+‖edgePart (pathPauliDisorderShell ω n) b‖) := by
  let u := pathPauliDisorderShell ω n
  let v := pathPauliDisorderShell ω' n
  have hab : a.val≤b.val := (ha.trans hb).le
  have h₁ := bond_packet_signal_error u ha hb t
  have h₂ := bond_packet_signal_error v ha hb t
  rw [←packet_congr ω ω' a b h,←edge_congr ω ω' a (h _ le_rfl hab),
    ←edge_congr ω ω' b (h _ hab le_rfl)] at h₂
  have hdist := abs_sub_le (bondSignal e u t)
    (signal (packet u (middleBlock a b)) (bondOutput e) (bondInput e) t) (bondSignal e v t)
  rw [abs_sub_comm (signal (packet u (middleBlock a b)) (bondOutput e) (bondInput e) t)
    (bondSignal e v t)] at hdist
  exact hdist.trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- On an interior bond with a weak edge on both sides, setting all rows
outside the window to zero changes the signal by at most 72|t|γ. -/
theorem masked_signal_error {n R : ℕ} (ω : PathPauliDisorder) (e : Fin (n+1)) (t γ : ℝ)
    (hl : R≤e.val) (hr : e.val+R≤n) (hs : ω∉failedStrips γ R e.val) :
    let j := e.val-R
    let L := 2*R+2
    let ω' := extendWindow j (readWindow j L ω)
    |bondSignal e (pathPauliDisorderShell ω' n) t-bondSignal e (pathPauliDisorderShell ω n) t| ≤
      72*|t| *γ := by
  intro j L ω'
  classical
  have hmiss : e∉missedBonds n R γ ω := fun h => hs (Finset.mem_filter.mp h).2
  obtain ⟨a,b,ha,hb,hleft,hright,hna,hnb⟩ := brackets_of_not_missed ω hl hr hmiss
  have hrows (i : ℕ) (hi : a.val ≤ i) (hi' : i≤b.val) (d : PathPauliDirections) :
      ω' (i,d)=ω (i,d) := recover_window ω (by dsimp only [j]; omega) (by dsimp only [j,L]; omega) d
  rw [abs_sub_comm]
  have h := window_signal_change ω ω' ha hb t (fun i hi hi' d => (hrows i hi hi' d).symm)
  exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add hna hnb) (mul_nonneg (by norm_num)
    (abs_nonneg t))).trans_eq (by ring))

#print axioms masked_signal_error
#print axioms window_signal_change
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
