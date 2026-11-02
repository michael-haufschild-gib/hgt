import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineExactNullseries

/-!
# Sparse support for exact spline nullseries

Cumulative block rank embeds every height truncation into a finite interval.
Distinct real levels and distinct heights within each block give unit
multiplicity and unattained positive real width.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def PrescribedSplineSchedule.atomOffset {a b d D : ℝ} (s : PrescribedSplineSchedule a b d D) (k : ℕ) : ℕ :=
  ∑ j ∈ range k, s.size j

def PrescribedSplineSchedule.atomRank {a b d D : ℝ} (s : PrescribedSplineSchedule a b d D)
    (i : s.AtomIndex) : ℕ := s.atomOffset i.1+i.2.val

lemma PrescribedSplineSchedule.atomOffset_mono {a b d D : ℝ} (s : PrescribedSplineSchedule a b d D) :
    Monotone s.atomOffset := by
  apply monotone_nat_of_le_succ
  intro k
  change (∑ j ∈ range k, s.size j) ≤ ∑ j ∈ range (k+1), s.size j
  rw [sum_range_succ]
  exact Nat.le_add_right _ _

lemma PrescribedSplineSchedule.atomRank_lt_prefix {a b d D : ℝ} (s : PrescribedSplineSchedule a b d D)
    (i : s.AtomIndex) : s.atomRank i < gridPrefixSize s.size i.1 := by
  rw [PrescribedSplineSchedule.atomRank, PrescribedSplineSchedule.atomOffset, gridPrefixSize, sum_range_succ]
  exact Nat.add_lt_add_left i.2.isLt _

lemma PrescribedSplineSchedule.atomRank_injective {a b d D : ℝ} (s : PrescribedSplineSchedule a b d D) :
    Function.Injective s.atomRank := by
  have hlt : ∀ i j : s.AtomIndex, i.1 < j.1 → s.atomRank i < s.atomRank j := by
    intro i j hij
    have h := s.atomOffset_mono (Nat.succ_le_of_lt hij)
    rw [PrescribedSplineSchedule.atomOffset, sum_range_succ] at h
    have hi := i.2.isLt
    change (∑ k ∈ range i.1, s.size k)+s.size i.1 ≤ s.atomOffset j.1 at h
    dsimp only [PrescribedSplineSchedule.atomRank, PrescribedSplineSchedule.atomOffset]
    dsimp only [PrescribedSplineSchedule.atomOffset] at h
    omega
  intro i j hij
  have hfst : i.1=j.1 := by
    rcases lt_trichotomy i.1 j.1 with h | h | h
    · exact False.elim ((ne_of_lt (hlt i j h)) hij)
    · exact h
    · exact False.elim ((ne_of_lt (hlt j i h)) hij.symm)
  rcases i with ⟨k,i⟩
  rcases j with ⟨l,j⟩
  dsimp only at hfst
  subst l
  have hval : i.val=j.val := Nat.add_left_cancel hij
  exact congrArg (fun t : Fin (s.size k) => (⟨k,t⟩ : s.AtomIndex)) (Fin.ext hval)


/-- Prescribed spline coefficients admit an absolutely convergent nullseries
on the positive two-prime cone, with distinct atoms and unattained width. -/
theorem exists_two_prime_prescribed_spline_nullseries {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D : ℝ}
    (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ),
      Function.Injective z ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧
      (∀ i, 1 ≤ (z i).im) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, splineMomentCoefficient (z i) ≠ 0) ∧
      Summable (fun i => ‖splineMomentCoefficient (z i)‖) ∧
      (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2 ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ t : ℝ, Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t : ℂ)*z i))) ∧
      (∀ t : PositiveCone (Real.log p) (Real.log q),
        HasSum (fun i => splineMomentCoefficient (z i)*Complex.exp ((t.val : ℂ)*z i)) 0) := by
  classical
  obtain ⟨s⟩ := exists_two_prime_spline_tail_schedule hp hq hpq hd hdD
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨γ,hγ,hinj,hzero⟩ := exists_spline_prefix_heights s ha hb hd hdD
  let z := s.atom γ
  have hzre (i : s.AtomIndex) : (z i).re=approachLevel d D (s.start+i.1) := s.point_re γ i.1 i.2
  have hzim (i : s.AtomIndex) : (z i).im=γ i.1 i.2 := s.point_im γ i.1 i.2
  have hzinj : Function.Injective z := by
    intro i j he
    have hre := congrArg Complex.re he
    rw [hzre,hzre] at hre
    have hk : i.1=j.1 := Nat.add_left_cancel ((strictMono_approachLevel hdD).injective hre)
    rcases i with ⟨k,i⟩
    rcases j with ⟨l,j⟩
    dsimp only at hk
    subst l
    have him := congrArg Complex.im he
    rw [hzim,hzim] at him
    exact congrArg (fun v : Fin (s.size k) => (⟨k,v⟩ : s.AtomIndex)) (hinj k him)
  have hrank (i : s.AtomIndex) : ((s.atomRank i+1 : ℕ) : ℝ) ≤ (z i).im := by
    have hn : s.atomRank i+1 ≤ gridPrefixSize s.size i.1 :=
      Nat.succ_le_iff.mpr (s.atomRank_lt_prefix i)
    have hnR : ((s.atomRank i+1 : ℕ) : ℝ) ≤ (gridPrefixSize s.size i.1 : ℝ) := by exact_mod_cast hn
    rw [hzim]
    exact hnR.trans ((s.prefix_le_height i.1).trans (hγ i.1 i.2).1)
  have hcount : ∀ T : ℝ, Nonempty ({i : s.AtomIndex // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊) := by
    intro T
    refine ⟨{
      toFun := fun i => ⟨s.atomRank i.val,Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.le_floor ((hrank i.val).trans ((le_abs_self _).trans i.property)))⟩
      inj' := by
        intro i j hij
        apply Subtype.ext
        exact s.atomRank_injective (congrArg Fin.val hij)
    }⟩
  refine ⟨s.AtomIndex,inferInstance,z,hzinj,?_,?_,?_,?_,
    summable_prescribed_spline_norm s hd hdD (fun k j => (hγ k j).1),
    tsum_prescribed_spline_norm_le_two s hd hdD (fun k j => (hγ k j).1),hcount,
    summable_prescribed_spline_moment s hd hdD (fun k j => (hγ k j).1),
    hasSum_prescribed_spline_atomic_moment s hd hdD (fun k j => (hγ k j).1) hzero⟩
  · intro i
    rw [hzre]
    exact ⟨approachLevel_lower hdD _,approachLevel_lt hdD _⟩
  · intro i
    rw [hzim]
    exact (s.height_one i.1).trans (hγ i.1 i.2).1
  · intro r hr
    have he : ∀ᶠ k : ℕ in atTop, r < approachLevel d D k :=
      (tendsto_approachLevel d D).eventually (eventually_gt_nhds hr)
    obtain ⟨k,hk⟩ := he.exists
    refine ⟨⟨k,⟨0,s.size_pos k⟩⟩,?_⟩
    rw [hzre]
    exact hk.trans_le ((strictMono_approachLevel hdD).monotone (show k ≤ s.start+k by omega))
  · intro i
    exact splineMomentCoefficient_ne_zero (hd.trans_le (approachLevel_lower hdD _)) _

#print axioms exists_two_prime_prescribed_spline_nullseries
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
