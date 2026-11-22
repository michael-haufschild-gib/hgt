import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathOverlap

/-! # Squared coupling mass within two overlaps of selected bonds -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section
variable {n : ℕ}

/-- Adding the centre makes each radius-one ball contain its centre by definition. -/
def ball (l : PathLabel n) := insert l (pathOverlaps l)

theorem ball_card (l : PathLabel n) : (ball l).card ≤ 43 :=
  (Finset.card_insert_le ..).trans (Nat.succ_le_succ (pathOverlaps_card_le l))

private theorem ball_symm (l q : PathLabel n) : q ∈ ball l ↔ l ∈ ball q := by
  simp only [ball,Finset.mem_insert,mem_pathOverlaps,eq_comm (a:=q) (b:=l),disjoint_comm (a:=labelSupport (pathWord l)) (b:=labelSupport (pathWord q))]

private theorem sum_ball_le (w : PathLabel n → ℝ) (hw : ∀ l, 0≤w l) :
    (∑ l : PathLabel n, ∑ q ∈ ball l, w q) ≤ 43*∑ q, w q := by
  classical
  have hr (l : PathLabel n) (f : PathLabel n → ℝ) :
      (∑ q ∈ ball l, f q) = ∑ q : PathLabel n, if q ∈ ball l then f q else 0 := by
    rw [←Finset.sum_filter]; simp
  have hf : (∑ l : PathLabel n, ∑ q ∈ ball l, w q)=∑ l : PathLabel n, ∑ _q ∈ ball l, w l := by
    simp_rw [hr]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => if_congr (ball_symm q l) rfl rfl
  rw [hf,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast ball_card i) (hw i)

def zz (e : Fin (n+1)) : PathLabel n := .inr (e,2,2)

def localMass (u : PathShell n) (e : Fin (n+1)) := ∑ l∈ball (zz e), ∑ q∈ball l, (u q)^2

theorem localMass_nonneg (u : PathShell n) (e : Fin (n+1)) : 0 ≤ localMass u e :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Bounded degree counts each squared coefficient at most 43² times. -/
theorem sum_localMass (u : PathShell n) : (∑ e, localMass u e) ≤ 43^2*‖u‖^2 := by
  classical
  let v (l : PathLabel n) := ∑ q ∈ ball l, (u q)^2
  let w (k : PathLabel n) := ∑ l ∈ ball k, v l
  have hn (l) : 0 ≤ v l := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hj : Function.Injective (zz (n:=n)) := by intro i j h; simpa [zz] using h
  have hsub : (∑ e, w (zz e)) ≤ ∑ k, w k := by
    rw [←Finset.sum_image (fun i _ j _ hij => hj hij)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => Finset.sum_nonneg fun l _ => hn l)
  have hv := sum_ball_le (fun l => (u l)^2) (fun _ => sq_nonneg _)
  have hs : (∑ l, (u l)^2)=‖u‖^2 := by simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [hs] at hv
  change (∑ l, v l) ≤ 43*‖u‖^2 at hv
  have hw : (∑ k, w k) ≤ 43*∑ l, v l := sum_ball_le v hn
  change (∑ e, w (zz e)) ≤ _
  linarith only [hsub,hw,hv]

/-- A local mass bound controls every coefficient within two overlaps. -/
theorem coord_le_localMass (u : PathShell n) (e : Fin (n+1)) {l q : PathLabel n}
    (hl : l∈ball (zz e)) (hq : q∈ball l) : (u q)^2 ≤ localMass u e := by
  apply (Finset.single_le_sum (f:=fun k => (u k)^2) (fun _ _ => sq_nonneg _) hq).trans
  exact Finset.single_le_sum (f:=fun k => ∑ i∈ball k, (u i)^2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hl

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
