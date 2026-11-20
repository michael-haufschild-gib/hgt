import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheLowerCountingOrderOfMertensExcursions
import GaloisForLFunctions.ExceptionalLayerTheory.FiniteRanksUnderErasureAndReplacement
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheLongestSignedExcursionsOfTheMertensSum

/-!
# Polynomial ranks of the absolute Mertens prefixes

The order-statistic/counting-function inversion in Ponge's Lemma B.5
suggests ranking the actual prefix magnitudes inside each finite window.
Any number of deletions bounded by a fixed power below one leaves a
prefix of every subcritical order, now measured against the final
cutoff N. Consequently even the optimally chosen deletions preserve the
ordinary logarithmic order of the largest remaining reading.
-/
noncomputable section
open Finset Filter
open scoped Topology NNReal
open _root_.RHTower GaloisForLFunctions.ArithmeticPowerMass
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Members of a prefix window reaching a threshold on its final scale. -/
def mertensWindowExcursions (b C : ℝ) (N : ℕ) : Finset ℕ :=
  (range (N+1)).filter (fun k => C*((N:ℝ)+1)^b < ‖mobiusMertensPartialSum k‖)

/-- Every sublinear-power deletion leaves a large Mertens value, at
every sufficiently large cutoff, even when the deleted indices depend
on the entire window. -/
theorem mertens_survivor_above_cutoff_power {b g : ℝ} (hb : b<zetaZeroAbscissa)
    (hg : g<1) (C K : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ D : Finset ℕ, (D.card:ℝ)≤K*((N:ℝ)+1)^g →
       ∃ k ∈ mertensWindowExcursions b C N, k∉D := by
  have hθ : 0<zetaZeroAbscissa := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  obtain ⟨a,ha,haθ⟩ := exists_between (max_lt hθ hb)
  have ha0 := (le_max_left 0 b).trans_lt ha
  have hba := (le_max_right 0 b).trans_lt ha
  obtain ⟨d,hd,hd1⟩ := exists_between (max_lt hg ((div_lt_one ha0).mpr hba))
  have hgd := (le_max_left g (b/a)).trans_lt hd
  have hbda := (div_lt_iff₀ ha0).mp ((le_max_right g (b/a)).trans_lt hd)
  filter_upwards [all_cutoffs_many_mertens_excursions haθ hd1 (|C|+1) (|K|+2)] with N hpop
  intro D hD
  let S := mertensExcursions a (|C|+1) N
  let T := S \ D
  let X := (N:ℝ)+1
  have hX : 1≤X := by dsimp only [X]; linarith only [Nat.cast_nonneg (α:=ℝ) N]
  have hx := zero_lt_one.trans_le hX
  have hT : X^d<(T.card:ℝ) := by
    have hpart : (S.card:ℝ) ≤ (T.card:ℝ)+(D.card:ℝ) := by
      exact_mod_cast (card_le_card_sdiff_add_card (s:=S) (t:=D))
    have hsize := hD.trans (mul_le_mul (le_abs_self K)
      (Real.rpow_le_rpow_of_exponent_le hX hgd.le) (Real.rpow_nonneg hx.le _) (abs_nonneg K))
    change (|K|+2)*X^d<(S.card:ℝ) at hpop
    change _ ≤ |K| * X^d at hsize
    linarith only [hpop,hpart,hsize,Real.rpow_pos_of_pos hx d]
  have hn : T.Nonempty := card_pos.mp (by exact_mod_cast (Real.rpow_pos_of_pos hx d).trans hT)
  let k := T.max' hn
  have hk : k∈T := T.max'_mem hn
  have hcard : T.card≤k+1 := by
    have hh : T⊆range (k+1) := fun n h => mem_range.mpr (Nat.lt_succ_of_le (T.le_max' n h))
    simpa only [card_range] using card_le_card hh
  have hindex : X^d < (k:ℝ)+1 := hT.trans_le (by exact_mod_cast hcard)
  have hm := (mem_filter.mp (mem_sdiff.mp hk).1).2
  change (|C|+1)*((k:ℝ)+1)^a < |shiftedMertensReal k| at hm
  rw [←norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal] at hm
  have hscale : X^b≤((k:ℝ)+1)^a := by
    apply (Real.rpow_le_rpow_of_exponent_le hX hbda.le).trans
    rw [Real.rpow_mul hx.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hindex.le ha0.le
  exact ⟨k,mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp hk).1).1,
    (mul_le_mul ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one)) hscale
      (Real.rpow_nonneg hx.le b) (by positivity : 0≤|C|+1)).trans_lt hm⟩,(mem_sdiff.mp hk).2⟩

/-- Cutoff-relative superlevel populations exceed every power below
one, at every sufficiently large window. -/
theorem mertens_cutoff_relative_population {b g : ℝ} (hb : b<zetaZeroAbscissa)
    (hg : g<1) (C K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K*((N:ℝ)+1)^g < ((mertensWindowExcursions b C N).card:ℝ) := by
  filter_upwards [mertens_survivor_above_cutoff_power hb hg C K] with N hs
  by_contra! h
  obtain ⟨k,hk,hn⟩ := hs _ h
  exact hn hk

/-- The maximum after a prescribed erasure, with value zero on an empty window. -/
def remainingMertensPeak (N : ℕ) (D : Finset ℕ) : ℝ≥0 :=
  ((range (N+1)) \ D).sup (fun k => ‖mobiusMertensPartialSum k‖₊)

/-- The (r+1)-st largest magnitude equals the smallest possible peak
after erasing at most r sites. Repeated magnitudes count with multiplicity. -/
def mertensRank (N r : ℕ) : ℝ≥0 :=
  FiniteRanks.erasedPeak (range (N+1)) (fun k => ‖mobiusMertensPartialSum k‖₊) r

/-- The strict counting function inverts the finite Mertens rank exactly. -/
theorem lt_mertensRank_iff (N r : ℕ) (y : ℝ≥0) :
    y < mertensRank N r ↔ r < ((range (N+1)).filter fun k => y < ‖mobiusMertensPartialSum k‖₊).card :=
  FiniteRanks.lt_erasedPeak_iff _ _ _ _

private theorem rank_le_undeleted (N r : ℕ) : mertensRank N r≤remainingMertensPeak N ∅ := by
  unfold mertensRank FiniteRanks.erasedPeak
  apply Finset.inf'_le
  simp

private theorem upper_peak {b : ℝ} (hb : zetaZeroAbscissa<b) :
    ∃ A : ℝ, 0≤A ∧ ∀ N, (remainingMertensPeak N ∅:ℝ) ≤ A*((N:ℝ)+1)^b := by
  obtain ⟨A,hA,h⟩ := mobiusMertens_subpower_zetaZeroAbscissa (b-zetaZeroAbscissa) (sub_pos.mpr hb)
  have hb0 : 0≤b := le_trans (by linarith only [half_le_zetaZeroAbscissa]) hb.le
  rw [show zetaZeroAbscissa+(b-zetaZeroAbscissa)=b by ring] at h
  refine ⟨A,hA,fun N => ?_⟩
  let B : ℝ≥0 := ⟨A*((N:ℝ)+1)^b,mul_nonneg hA (Real.rpow_nonneg (by positivity) _)⟩
  change remainingMertensPeak N ∅≤B
  apply Finset.sup_le
  intro k hk
  have hkn := Nat.lt_succ_iff.mp (mem_range.mp (mem_sdiff.mp hk).1)
  exact (h k).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
    (add_le_add (Nat.cast_le.mpr hkn) (le_refl (1:ℝ))) hb0) hA)

/-- Every polynomial rank below full population has ordinary growth
exponent Θ, including the leading rank and arbitrarily data-dependent ranks. -/
theorem mertens_polynomial_rank_order (r : ℕ → ℕ) {g K : ℝ} (hg : g<1)
    (hr : ∀ᶠ N : ℕ in atTop, (r N:ℝ)≤K*((N:ℝ)+1)^g) :
    Tendsto (fun N : ℕ => Real.log (1+(mertensRank N (r N):ℝ))/Real.log ((N:ℝ)+1))
      atTop (𝓝 zetaZeroAbscissa) := by
  apply log_order_of_power_envelope ((by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa)
    (fun N => (mertensRank N (r N)).property)
  · intro b _ hb
    filter_upwards [hr,mertens_survivor_above_cutoff_power hb hg 1 K] with N hN hsurv
    let y : ℝ≥0 := ⟨((N:ℝ)+1)^b, Real.rpow_nonneg (by positivity) _⟩
    change y < mertensRank N (r N)
    apply (lt_mertensRank_iff N (r N) y).mpr
    by_contra! hc
    obtain ⟨k,hk,hd⟩ := hsurv _ ((Nat.cast_le.mpr hc).trans hN)
    obtain ⟨hkN,hs⟩ := mem_filter.mp hk
    apply hd
    refine mem_filter.mpr ⟨hkN, ?_⟩
    change ((N : ℝ) + 1)^b < ‖mobiusMertensPartialSum k‖
    simpa only [one_mul] using hs
  · intro b hb
    obtain ⟨A,hA,h⟩ := upper_peak hb
    exact ⟨A,hA,fun N => (show (mertensRank N (r N):ℝ) ≤ (remainingMertensPeak N ∅:ℝ) from
      rank_le_undeleted N (r N)).trans (h N)⟩

/-- An adversary may replace q readings in each window with arbitrary
nonnegative numbers. Trimming at least q top readings still recovers Θ
at every sublinear polynomial rank, regardless of the replacement values. -/
theorem corrupted_mertens_rank_order (w : ℕ → ℕ → ℝ≥0) (q r : ℕ → ℕ)
    {g K : ℝ} (hg : g<1)
    (hr : ∀ᶠ N : ℕ in atTop, ((r N+q N:ℕ):ℝ)≤K*((N:ℝ)+1)^g)
    (hqr : ∀ᶠ N : ℕ in atTop, q N≤r N)
    (hw : ∀ᶠ N : ℕ in atTop,
      ((range (N+1)).filter fun k => ‖mobiusMertensPartialSum k‖₊ ≠ w N k).card ≤ q N) :
    Tendsto (fun N : ℕ => Real.log (1+(FiniteRanks.erasedPeak (α := ℝ≥0)
      (range (N+1)) (w N) (r N):ℝ))/Real.log ((N:ℝ)+1)) atTop (𝓝 zetaZeroAbscissa) := by
  let v := fun k => ‖mobiusMertensPartialSum k‖₊
  have hlo := mertens_polynomial_rank_order (fun N => r N+q N) hg hr
  have hhi := mertens_polynomial_rank_order (fun N => r N-q N) hg
    (hr.mono (fun N h => (Nat.cast_le.mpr
      ((Nat.sub_le _ _).trans (Nat.le_add_right _ _))).trans h))
  have logMono (N : ℕ) {x y : ℝ≥0} (hxy : x ≤ y) :
      Real.log (1 + (x : ℝ)) / Real.log ((N : ℝ) + 1) ≤
      Real.log (1 + (y : ℝ)) / Real.log ((N : ℝ) + 1) :=
    div_le_div_of_nonneg_right (Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one x.property)
      (add_le_add le_rfl (show (x : ℝ) ≤ (y : ℝ) from hxy)))
      (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hw] with N h
    have hh := FiniteRanks.replacement_interlacing _ v (w N) (r N) (q N) h
    exact logMono N hh
  · filter_upwards [hw,hqr] with N h he
    have hs : ((range (N+1)).filter fun k => w N k ≠ v k).card ≤ q N := by
      simpa only [ne_comm] using h
    have hh := FiniteRanks.replacement_interlacing _ (w N) v (r N-q N) (q N) hs
    rw [Nat.sub_add_cancel he] at hh
    exact logMono N hh

/-- The longest interval whose every Mertens sum has the same sign
and magnitude at least its length grows with ordinary exponent Θ.
This includes the case in which all zeros lie on the critical line. -/
theorem signed_mertens_run_log_order :
    Tendsto (fun N : ℕ => Real.log (1+(signedRunDepth shiftedMertensReal N:ℝ)) /
      Real.log ((N:ℝ)+1)) atTop (𝓝 zetaZeroAbscissa) := by
  apply log_order_of_power_envelope ((by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa)
    (fun _ => Nat.cast_nonneg _)
  · intro b hb hw
    filter_upwards [mertens_survivor_above_cutoff_power hw (g:=0) zero_lt_one 6 0] with N h
    obtain ⟨k,hk,_⟩ := h ∅ (by simp)
    obtain ⟨hkn,hlarge⟩ := mem_filter.mp hk
    change 6 * ((N : ℝ) + 1)^b < ‖mobiusMertensPartialSum k‖ at hlarge
    have hl := mertens_half_peak_le_signed_depth (Nat.lt_succ_iff.mp (mem_range.mp hkn))
    have hf := Nat.lt_floor_add_one (‖mobiusMertensPartialSum k‖/2)
    have hpow := Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) N)) hb
    have hdepth : (⌊‖mobiusMertensPartialSum k‖ / 2⌋₊ : ℝ) ≤ signedRunDepth shiftedMertensReal N :=
      Nat.cast_le.mpr hl
    linarith only [hf,hdepth,hlarge,hpow]
  · intro b hb
    obtain ⟨A,hA,h⟩ := upper_peak hb
    refine ⟨A,hA,fun N => ?_⟩
    apply (signed_depth_le_envelope _ _ (remainingMertensPeak N ∅).property ?_).trans (h N)
    intro k hk
    rw [←norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal]
    exact Finset.le_sup (s:=(range (N+1)) \ ∅) (f:=fun n => ‖mobiusMertensPartialSum n‖₊)
      (Finset.mem_sdiff.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hk),Finset.notMem_empty _⟩)

#print axioms signed_mertens_run_log_order
#print axioms corrupted_mertens_rank_order
#print axioms mertens_survivor_above_cutoff_power
#print axioms mertens_cutoff_relative_population
#print axioms mertens_polynomial_rank_order
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
