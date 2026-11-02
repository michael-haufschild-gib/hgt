import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveGridNullseries
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.EighthPowerHeightBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveQuartetsWithBoundedConeCoupling

/-!
# Two-prime cone cancellation with eighth-power weights

For any two distinct primes and any positive interval of real parts, there is
a countable positive atomic measure of mass two with distinct support, linear
height count, unattained upper width, and exact zero moments on the positive
prime-logarithm cone. Its weights are bounded above and below by fixed multiples
of inverse eighth powers of height. The associated even Hermitian quartet
kernel has mixed cone coupling at most twenty.

The grid schedule supplies exact corrections; supergeometric block masses
absorb cumulative node counts. These freely chosen weights are not identified
with a prescribed complex spline factor times integer zero multiplicities.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Exact two-prime cone cancellation coexists with distinct sparse support,
unattained positive width, and weights comparable to the inverse eighth power of height. -/
theorem exists_two_prime_spline_sized_cone_model {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {d D : ℝ} (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ) (w : ι → ℝ) (C : ℝ),
      0 < C ∧ Function.Injective z ∧ (∀ i, 0 < w i) ∧ HasSum w 2 ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, 1/(1+|(z i).im|)^8 ≤ w i ∧ w i ≤ C/(1+|(z i).im|)^8) ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ t : PositiveCone (Real.log p) (Real.log q),
        HasSum (fun i => (w i : ℂ)*Complex.exp ((t.val : ℂ)*z i)) 0) ∧
      (∀ m n : ℕ,
        ‖quartetKernel z w (m*Real.log p+n*Real.log q)-quartetKernel z w (m*Real.log p)-
          quartetKernel z w (n*Real.log q)+quartetKernel z w 0‖ ≤ 20) := by
  classical
  obtain ⟨s⟩ := exists_two_prime_grid_schedule hp hq hpq hdD
  obtain ⟨U, R, hU, hR, hsize⟩ := s.size_growth
  let F := fun k => (gridPrefixSize s.size k : ℝ)
  let H := fun k => max (massRadius (correctionMass k) (s.size k)) ((Real.pi+2)*F k)
  have hF1 : ∀ k, 1 ≤ F k := by
    intro k
    change (1 : ℝ) ≤ (gridPrefixSize s.size k : ℝ)
    exact_mod_cast (Nat.succ_le_iff.mpr (gridPrefixSize_pos s.size_pos k))
  have hnF : ∀ k, (s.size k : ℝ) ≤ F k := by
    intro k
    have h : s.size k ≤ gridPrefixSize s.size k :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_self k))
    change (s.size k : ℝ) ≤ (gridPrefixSize s.size k : ℝ)
    exact_mod_cast h
  have hKsum := summable_weighted_prefix_count hU hR hsize
  let K := ∑' k, correctionMass k*F k^8
  have hK0 : 0 ≤ K := tsum_nonneg fun k => mul_nonneg (correctionMass_pos k).le
    (pow_nonneg (Nat.cast_nonneg (gridPrefixSize s.size k)) 8)
  have hK : ∀ k, correctionMass k*F k^8 ≤ K := fun k =>
    hKsum.le_tsum k (fun j _ => mul_nonneg (correctionMass_pos j).le
      (pow_nonneg (Nat.cast_nonneg (gridPrefixSize s.size j)) 8))
  obtain ⟨v, hv, hmass, hzero⟩ := exists_grid_weights s hdD H
  let z := s.atom H
  let W := s.atomWeight v
  let B := (3 : ℝ)^9/2*(2+(Real.pi+2)^8*K)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hWpos : ∀ i, 0 < W i := fun i => (hv i.1 i.2).1
  have hWbound : ∀ i, 1/(1+|(z i).im|)^8 ≤ W i ∧ W i ≤ B/(1+|(z i).im|)^8 := by
    intro i
    have hi := grid_height_interval (A := correctionMass i.1)
      (s.size_pos i.1) (s.radius_one_le i.1) (hnF i.1) i.2
    have h := height_weight_bounds (correctionMass_pos i.1) (s.size_pos i.1) (hF1 i.1) (hK i.1)
      hi.1 hi.2 (hv i.1 i.2).2.1 (hv i.1 i.2).2.2
    simpa only [z, W, B, PositiveGridSchedule.atom, PositiveGridSchedule.atomWeight, s.point_im, H] using h
  have hzinj : Function.Injective z := by
    intro i j hij
    have hk : i.1=j.1 := (strictMono_approachLevel hdD).injective (by
      have h := congrArg Complex.re hij
      simpa only [z, PositiveGridSchedule.atom, s.point_re] using h)
    rcases i with ⟨k,i⟩
    rcases j with ⟨l,j⟩
    dsimp only at hk
    subst l
    have him := congrArg Complex.im hij
    simp only [z, PositiveGridSchedule.atom, s.point_im] at him
    have he := grid_height_injective (lt_of_lt_of_le (by norm_num) (s.radius_one_le k)) (H k) (s.size k) him
    exact congrArg (fun t : Fin (s.size k) => (⟨k,t⟩ : s.AtomIndex)) he
  have hrank : ∀ i : s.AtomIndex, ((s.atomRank i+1 : ℕ) : ℝ) ≤ (z i).im := by
    intro i
    have hF : F i.1 ≤ H i.1 := by
      have hF0 := (show (0 : ℝ) ≤ 1 by norm_num).trans (hF1 i.1)
      have h := le_mul_of_one_le_left hF0 (show 1 ≤ Real.pi+2 by linarith only [Real.pi_pos])
      exact h.trans (le_max_right _ _)
    have hi := (grid_height_interval (A := correctionMass i.1)
      (s.size_pos i.1) (s.radius_one_le i.1) (hnF i.1) i.2).1
    have hNat : s.atomRank i+1 ≤ gridPrefixSize s.size i.1 := Nat.succ_le_iff.mpr (s.atomRank_lt_prefix i)
    have hReal : ((s.atomRank i+1 : ℕ) : ℝ) ≤ F i.1 := by
      change ((s.atomRank i+1 : ℕ) : ℝ) ≤ (gridPrefixSize s.size i.1 : ℝ)
      exact_mod_cast hNat
    simpa only [z, PositiveGridSchedule.atom, s.point_im] using hReal.trans (hF.trans hi)
  have hcount : ∀ T : ℝ, Nonempty ({i : s.AtomIndex // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊) := by
    intro T
    refine ⟨{
      toFun := fun i => ⟨s.atomRank i.val, Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.le_floor ((hrank i.val).trans ((le_abs_self _).trans i.property)))⟩
      inj' := by
        intro i j hij
        apply Subtype.ext
        exact s.atomRank_injective (congrArg Fin.val hij)
    }⟩
  let M := ∑' k, correctionMass k
  have hMpos : 0 < M := (correctionMass_pos 0).trans_le
    (correctionMass_summable.le_tsum 0 (fun j _ => (correctionMass_pos j).le))
  have hMle : M ≤ 2 := correctionMass_tsum_le_two
  let c := 2/M
  have hc : 0 < c := div_pos (by norm_num) hMpos
  have hc1 : 1 ≤ c := (le_div_iff₀ hMpos).mpr (by simpa only [one_mul] using hMle)
  let w := fun i : s.AtomIndex => c*W i
  have hw : ∀ i, 0 < w i := fun i => mul_pos hc (hWpos i)
  have hs : HasSum w 2 := by
    have h := (hasSum_grid_weight s v (fun k j => (hv k j).1.le) hmass).mul_left c
    have he : c*M=2 := div_mul_cancel₀ _ hMpos.ne'
    change HasSum w (c*M) at h
    rwa [he] at h
  have hzstrip : ∀ i, d ≤ (z i).re ∧ (z i).re < D := by
    intro i
    simp only [z, PositiveGridSchedule.atom, s.point_re]
    exact ⟨approachLevel_lower hdD i.1, approachLevel_lt hdD i.1⟩
  have hmoment : ∀ t : PositiveCone (Real.log p) (Real.log q),
      HasSum (fun i => (w i : ℂ)*Complex.exp ((t.val : ℂ)*z i)) 0 := by
    intro t
    have h := (hasSum_grid_atomic_moment s H v hd hdD (fun k j => (hv k j).1) hmass hzero t).mul_left (c : ℂ)
    simpa only [w, W, z, Complex.ofReal_mul, mul_assoc, mul_zero] using h
  refine ⟨s.AtomIndex, inferInstance, z, w, c*B, mul_pos hc hB, hzinj, hw, hs,
    hzstrip, ?_, ?_, hcount, hmoment, ?_⟩
  · intro r hr
    have he : ∀ᶠ k : ℕ in atTop, r < approachLevel d D k :=
      (tendsto_approachLevel d D).eventually (eventually_gt_nhds hr)
    obtain ⟨k, hk⟩ := he.exists
    refine ⟨⟨k, ⟨0, s.size_pos k⟩⟩, ?_⟩
    simpa only [z, PositiveGridSchedule.atom, s.point_re] using hk
  · intro i
    refine ⟨(hWbound i).1.trans (le_mul_of_one_le_left (hWpos i).le hc1), ?_⟩
    have h := mul_le_mul_of_nonneg_left (hWbound i).2 hc.le
    simpa only [w, mul_div_assoc] using h
  · have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
    exact quartet_coupling_le_twenty z w ha hb (fun i => (hw i).le) hs
      (fun i => hd.le.trans (hzstrip i).1) hmoment

#print axioms exists_two_prime_spline_sized_cone_model
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
