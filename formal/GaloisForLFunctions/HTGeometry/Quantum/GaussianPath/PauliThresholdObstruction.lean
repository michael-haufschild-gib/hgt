import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliLineObstruction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldBlocks

/-!
# Pauli line-graph obstruction after coefficient pruning

A second bond on the right edge distinguishes the two leaves that share
their left axis. The six terms then use just two independent coefficient
rows. Above every fixed coefficient cutoff, such blocks occur arbitrarily
far out along almost every Gaussian draw.
-/

open MeasureTheory Filter Set

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- For two words on the same bond with a common left axis, only the right
axis determines commutation. -/
theorem commute_coupling_same_left_iff (e : Fin (n + 1)) (a b c : Fin 3) :
    Commute (finitePauliMatrix (couplingWord e (a, b)))
      (finitePauliMatrix (couplingWord e (a, c))) ↔ b = c := by
  rw [finitePauli_commute_iff_sign, finitePauliConjugationSign,
    Finset.prod_eq_single e.succ]
  · have hneg := neg_ne_self.mpr (one_ne_zero : (1 : ℂ) ≠ 0)
    by_cases h : b = c <;>
      simp [couplingWord, e.castSucc_lt_succ.ne', boolPauliConjugationSign, h, hneg]
  · intro i _ hi
    by_cases hl : i = e.castSucc <;> simp [couplingWord, boolPauliConjugationSign, hl, hi]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- The path frustration graph has the active labels as vertices. -/
abbrev pathFrustrationAdj (S : Set (PathLabel n)) (p q : S) : Prop :=
  ¬Commute (finitePauliMatrix (pathWord p.1)) (finitePauliMatrix (pathWord q.1))

/-- The onsite words X₀, X₁, Z₀ and the bonds Z₀Z₁, X₁X₂, X₁Z₂
form a twin-separated claw on any consecutive pair of edges. -/
theorem path_no_twinLineModel_of_adjacent_rows {ρ : Type*} [DecidableEq ρ]
    (S : Set (PathLabel n)) (e f : Fin (n + 1)) (hef : e.succ = f.castSucc)
    (ho : Sum.inr (e, 2, 2) ∈ S) (hc : Sum.inr (f, 0, 0) ∈ S)
    (ha : Sum.inl (e.castSucc, 0) ∈ S) (hb : Sum.inl (f.castSucc, 0) ∈ S)
    (hz : Sum.inl (e.castSucc, 2) ∈ S) (hw : Sum.inr (f, 0, 2) ∈ S) :
    IsEmpty (TwinLineModel (pathFrustrationAdj S) ρ) := by
  let o : S := ⟨.inr (e, 2, 2), ho⟩
  let a : S := ⟨.inl (e.castSucc, 0), ha⟩
  let b : S := ⟨.inl (f.castSucc, 0), hb⟩
  let c : S := ⟨.inr (f, 0, 0), hc⟩
  let z : S := ⟨.inl (e.castSucc, 2), hz⟩
  let w : S := ⟨.inr (f, 0, 2), hw⟩
  have haxis : (0 : Fin 3) ≠ 2 := fun h => Nat.zero_ne_add_one 1 (congrArg Fin.val h)
  have hleft : e.castSucc < f.castSucc := hef ▸ e.castSucc_lt_succ
  have hoa : pathFrustrationAdj S o a := fun h => haxis
    (((commute_onsite_coupling_iff e.castSucc 0 e (2, 2)).mp h.symm).1 rfl)
  have hob : pathFrustrationAdj S o b := fun h => haxis
    (((commute_onsite_coupling_iff f.castSucc 0 e (2, 2)).mp h.symm).2 hef.symm)
  have hoc : pathFrustrationAdj S o c := fun h => haxis
    (((commute_consecutive_coupling_iff e f hef (2, 2) (0, 0)).mp h).symm)
  have hab : ¬pathFrustrationAdj S a b := fun h => h
    ((commute_onsitePauli_iff e.castSucc f.castSucc 0 0).mpr (Or.inl hleft.ne))
  have hac : ¬pathFrustrationAdj S a c := fun h => h
    ((commute_onsite_coupling_iff e.castSucc 0 f (0, 0)).mpr ⟨fun _ => rfl, fun _ => rfl⟩)
  have hcb : ¬pathFrustrationAdj S c b := fun h => h
    (((commute_onsite_coupling_iff f.castSucc 0 f (0, 0)).mpr
      ⟨fun _ => rfl, fun _ => rfl⟩).symm)
  have haz : pathFrustrationAdj S a z := fun h =>
    ((commute_onsitePauli_iff e.castSucc e.castSucc 0 2).mp h).elim (fun he => he rfl) haxis
  have hbz : ¬pathFrustrationAdj S b z := fun h => h
    ((commute_onsitePauli_iff f.castSucc e.castSucc 0 2).mpr (Or.inl hleft.ne'))
  have hcz : ¬pathFrustrationAdj S c z := fun h => h
    (((commute_onsite_coupling_iff e.castSucc 2 f (0, 0)).mpr
      ⟨fun he => (hleft.ne he).elim, fun he => ((hleft.trans f.castSucc_lt_succ).ne he).elim⟩).symm)
  have hcw : pathFrustrationAdj S c w :=
    fun h => haxis ((commute_coupling_same_left_iff f 0 0 2).mp h)
  have hbw : ¬pathFrustrationAdj S b w := fun h => h
    ((commute_onsite_coupling_iff f.castSucc 0 f (0, 2)).mpr
      ⟨fun _ => rfl, fun he => (f.castSucc_lt_succ.ne he).elim⟩)
  exact isEmpty_twinLineModel_of_claw (pathFrustrationAdj S)
    (fun {_ _} h hc => h hc.symm) (fun _ h => h (Commute.refl _))
    o a c b hoa hoc hob hac hab hcb ⟨z, haz, hcz⟩ ⟨z, haz, hbz⟩ ⟨w, hcw, hbw⟩

private theorem gaussian_ae_unbounded_blocks_above_nat (q : ℕ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ J : ℕ,
      ∃ j ≥ J, ∀ i, (q : ℝ) < pathPauliBlock ω j i := by
  classical
  let lo : PathPauliBlockLabel → ℝ := fun _ => (q : ℝ) + 1
  let hi : PathPauliBlockLabel → ℝ := fun _ => (q : ℝ) + 2
  obtain ⟨p, hp, hfreq⟩ := gaussian_pauli_block_positive_density lo hi
    (fun i => by dsimp [lo, hi]; linarith)
  filter_upwards [hfreq] with ω hω
  intro J
  obtain ⟨k, hk⟩ := eventually_atTop.mp hω
  obtain ⟨r, hr⟩ := exists_nat_gt ((J : ℝ) / p)
  let m := max k r
  let G := (Finset.range m).filter (fun j => ∀ i, pathPauliBlock ω j i ∈ Icc (lo i) (hi i))
  have hfreq' : p * (m : ℝ) ≤ G.card := hk m (le_max_left _ _)
  have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_right k r
  have hmass : (J : ℝ) < p * (m : ℝ) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hp).mp (hr.trans_le hrm)
  by_contra hnone
  have hsub : G ⊆ Finset.range J := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hj'
    apply hnone
    refine ⟨j, le_of_not_gt hj', fun i => ?_⟩
    have hbox := (Finset.mem_filter.mp hj).2 i
    exact (show (q : ℝ) < lo i by dsimp [lo]; linarith).trans_le hbox.1
  have hc : G.card ≤ J := by simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hc' : (G.card : ℝ) ≤ J := by exact_mod_cast hc
  exact (not_lt_of_ge hc') (hmass.trans_le hfreq')

/-- A common Gaussian draw has arbitrarily late blocks above every real cutoff. -/
theorem gaussian_ae_unbounded_blocks_above :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ cutoff : ℝ, ∀ J : ℕ,
      ∃ j ≥ J, ∀ i, cutoff < pathPauliBlock ω j i := by
  filter_upwards [ae_all_iff.mpr gaussian_ae_unbounded_blocks_above_nat] with ω hω
  intro cutoff J
  obtain ⟨q, hq⟩ := exists_nat_ge cutoff
  obtain ⟨j, hj, hbig⟩ := hω q J
  exact ⟨j, hj, fun i => hq.trans_lt (hbig i)⟩

/-- Row and direction of the Gaussian coefficient of a path label. -/
def pathPauliSourceCoordinate : PathLabel n → ℕ × PathPauliDirections
  | .inl (i, a) => (i.val, .inl a)
  | .inr (e, ab) => (e.val, .inr ab)

theorem pathPauliDisorderShell_apply_source (ω : PathPauliDisorder) (l : PathLabel n) :
    pathPauliDisorderShell ω n l = ω (pathPauliSourceCoordinate l) := by
  cases l <;> rfl

/-- Keeping every term above the cutoff after any fixed initial segment
forces the line-graph obstruction on all sufficiently long prefixes.
The common probability-one event works for every cutoff and initial segment. -/
theorem gaussian_path_ae_no_twinLineModel_above_cutoff {ρ : Type*} [DecidableEq ρ] :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ cutoff : ℝ, ∀ J : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ∀ S : Set (PathLabel n),
        (∀ l, J ≤ (pathPauliSourceCoordinate l).1 →
          cutoff < |pathPauliDisorderShell ω n l| → l ∈ S) →
        IsEmpty (TwinLineModel (pathFrustrationAdj S) ρ) := by
  filter_upwards [gaussian_ae_unbounded_blocks_above] with ω hω
  intro cutoff J
  obtain ⟨j, hj, hbig⟩ := hω cutoff J
  refine ⟨2 * j + 1, fun n hn S hS => ?_⟩
  let e : Fin (n + 1) := ⟨2 * j, by omega⟩
  let f : Fin (n + 1) := ⟨2 * j + 1, by omega⟩
  have hef : e.succ = f.castSucc := Fin.ext rfl
  have hleft : J ≤ 2 * j := by omega
  have hright : J ≤ 2 * j + 1 := hleft.trans (Nat.le_succ _)
  have large (i : PathPauliBlockLabel) : cutoff < |pathPauliBlock ω j i| :=
    (hbig i).trans_le (le_abs_self _)
  exact path_no_twinLineModel_of_adjacent_rows S e f hef
    (hS _ hleft (large (0, .inr (2, 2)))) (hS _ hright (large (1, .inr (0, 0))))
    (hS _ hleft (large (0, .inl 0))) (hS _ hright (large (1, .inl 0)))
    (hS _ hleft (large (0, .inl 2))) (hS _ hright (large (1, .inr (0, 2))))

#print axioms path_no_twinLineModel_of_adjacent_rows
#print axioms gaussian_ae_unbounded_blocks_above
#print axioms gaussian_path_ae_no_twinLineModel_above_cutoff

end GaloisForLFunctions.HTGeometry
