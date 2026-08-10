import GaloisForLFunctions.HTGeometry.ScheffeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Real.Sqrt

set_option maxHeartbeats 800000

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

def CoalitionalProbabilityVector (p : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ HasSum p 1

def CoalitionalUniformlyTight (mu : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ n, 1 - ε < ∑ i ∈ F, mu n i

private def coalitionalCubePoint (mu : ℕ → ℕ → ℝ)
    (h0 : ∀ n i, 0 ≤ mu n i) (h1 : ∀ n i, mu n i ≤ 1) (n : ℕ) :
    ℕ → Set.Icc (0 : ℝ) 1 := fun i => ⟨mu n i, h0 n i, h1 n i⟩

private theorem coalitional_exists_coordinate_subseq (mu : ℕ → ℕ → ℝ)
    (h0 : ∀ n i, 0 ≤ mu n i) (h1 : ∀ n i, mu n i ≤ 1) :
    ∃ (p : ℕ → ℝ) (phi : ℕ → ℕ), StrictMono phi ∧
      ∀ i, Tendsto (fun n => mu (phi n) i) atTop (nhds (p i)) := by
  obtain ⟨q, phi, hphi, hq⟩ :=
    CompactSpace.tendsto_subseq (fun n => coalitionalCubePoint mu h0 h1 n)
  refine ⟨fun i => q i, phi, hphi, ?_⟩
  intro i
  have hi : Tendsto (fun n => coalitionalCubePoint mu h0 h1 (phi n) i)
      atTop (nhds (q i)) := tendsto_pi_nhds.mp hq i
  exact continuous_subtype_val.continuousAt.tendsto.comp hi

private theorem coalitional_probability_le_one {p : ℕ → ℝ}
    (hp : CoalitionalProbabilityVector p) (i : ℕ) : p i ≤ 1 := by
  have hle : p i ≤ ∑' j, p j := by
    have hs := hp.2.summable.sum_le_tsum {i} (fun j _ => hp.1 j)
    simpa using hs
  simpa [hp.2.tsum_eq] using hle

private theorem coalitional_limit_probability
    (mu : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (phi : ℕ → ℕ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (htight : CoalitionalUniformlyTight mu)
    (hcoord : ∀ i, Tendsto (fun n => mu (phi n) i) atTop (nhds (p i))) :
    CoalitionalProbabilityVector p := by
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    exact ge_of_tendsto (hcoord i) (Eventually.of_forall fun n => (hprob (phi n)).1 i)
  have hfinle : ∀ F : Finset ℕ, ∑ i ∈ F, p i ≤ 1 := by
    intro F
    have hsum : Tendsto (fun n => ∑ i ∈ F, mu (phi n) i) atTop
        (nhds (∑ i ∈ F, p i)) := by
      exact tendsto_finsetSum F (fun i _ => hcoord i)
    exact le_of_tendsto hsum (Eventually.of_forall fun n => by
      have hle := (hprob (phi n)).2.summable.sum_le_tsum F
        (fun i _ => (hprob (phi n)).1 i)
      simpa [(hprob (phi n)).2.tsum_eq] using hle)
  have hpsum : Summable p := summable_of_sum_le hp0 hfinle
  have htsum_le : ∑' i, p i ≤ 1 := hpsum.tsum_le_of_sum_le hfinle
  have htsum_ge : 1 ≤ ∑' i, p i := by
    by_contra hnot
    have hlt : ∑' i, p i < 1 := lt_of_not_ge hnot
    let ε : ℝ := (1 - ∑' i, p i) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨F, hF⟩ := htight ε hε
    have hsum : Tendsto (fun n => ∑ i ∈ F, mu (phi n) i) atTop
        (nhds (∑ i ∈ F, p i)) := tendsto_finsetSum F (fun i _ => hcoord i)
    have hlower : 1 - ε ≤ ∑ i ∈ F, p i :=
      ge_of_tendsto hsum (Eventually.of_forall fun n => le_of_lt (hF (phi n)))
    have hheadle : ∑ i ∈ F, p i ≤ ∑' i, p i :=
      hpsum.sum_le_tsum F (fun i _ => hp0 i)
    dsimp [ε] at hlower
    linarith
  have heq : ∑' i, p i = 1 := le_antisymm htsum_le htsum_ge
  exact ⟨hp0, by simpa [heq] using hpsum.hasSum⟩

private theorem coalitional_weighted_summable
    {p a : ℕ → ℝ} (hp : CoalitionalProbabilityVector p)
    {B : ℝ} (hB : ∀ i, |a i| ≤ B) : Summable (fun i => p i * a i) := by
  have habs : Summable (fun i => |p i * a i|) := by
    refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_)
      ((hp.2.summable).mul_right B)
    rw [abs_mul, abs_of_nonneg (hp.1 i)]
    have : p i * |a i| ≤ p i * B := mul_le_mul_of_nonneg_left (hB i) (hp.1 i)
    simpa [mul_comm] using this
  exact habs.of_abs

private theorem coalitional_vector_weighted_summable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℕ → ℝ} {a : ℕ → E} (hp : CoalitionalProbabilityVector p)
    {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B) : Summable (fun i => p i • a i) := by
  apply Summable.of_norm_bounded ((hp.2.summable).mul_right B)
  intro i
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp.1 i)]
  exact mul_le_mul_of_nonneg_left (hB i) (hp.1 i)

private theorem coalitional_vector_barycenter_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (a : ℕ → E) (phi : ℕ → ℕ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (hpprob : CoalitionalProbabilityVector p)
    (hcoord : ∀ i, Tendsto (fun n => mu (phi n) i) atTop (nhds (p i)))
    {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B) :
    Tendsto (fun n => ∑' i, mu (phi n) i • a i) atTop
      (nhds (∑' i, p i • a i)) := by
  have hl1 := tendsto_tsum_abs_sub_of_tendsto
    (fun n i => (hprob (phi n)).1 i) (fun n => (hprob (phi n)).2) hpprob.2 hcoord
  have hnonneg : 0 ≤ B := le_trans (norm_nonneg (a 0)) (hB 0)
  have hbound : ∀ n,
      ‖(∑' i, mu (phi n) i • a i) - ∑' i, p i • a i‖ ≤
        B * ∑' i, |mu (phi n) i - p i| := by
    intro n
    have hmu := coalitional_vector_weighted_summable (hprob (phi n)) hB
    have hp := coalitional_vector_weighted_summable hpprob hB
    rw [← hmu.tsum_sub hp]
    have habsdiff := summable_abs_sub (hprob (phi n)).1 hpprob.1
      (hprob (phi n)).2.summable hpprob.2.summable
    have hnorm : Summable (fun i => ‖(mu (phi n) i - p i) • a i‖) := by
      apply Summable.of_nonneg_of_le (fun i => norm_nonneg _)
        (fun i => ?_) (habsdiff.mul_left B)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)
    calc
      ‖∑' i, mu (phi n) i • a i - p i • a i‖ =
          ‖∑' i, (mu (phi n) i - p i) • a i‖ := by
            congr 2
            funext i
            rw [sub_smul]
      _ ≤ ∑' i, ‖(mu (phi n) i - p i) • a i‖ :=
        norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' i, B * |mu (phi n) i - p i| :=
        Summable.tsum_le_tsum (fun i => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _))
          hnorm (habsdiff.mul_left B)
      _ = B * ∑' i, |mu (phi n) i - p i| := by rw [tsum_mul_left]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hBlim : Tendsto (fun n => B * ∑' i, |mu (phi n) i - p i|) atTop (nhds 0) := by
    simpa using hl1.const_mul B
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hBlim ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hb := hbound n
  have hr := hN n hn
  rw [dist_zero] at hr
  have hzero : 0 ≤ B * ∑' i, |mu (phi n) i - p i| :=
    mul_nonneg hnonneg (tsum_nonneg fun i => abs_nonneg _)
  rw [abs_of_nonneg hzero] at hr
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hb hr

/-- Route-independent Banach-valued attainment: bounded law atoms and tight zero-residual
coalitions produce an actual countable positive carrier. -/
theorem coalitional_tight_attainment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : ℕ → ℕ → ℝ) (a : ℕ → E)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (htight : CoalitionalUniformlyTight mu)
    {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B)
    (hres : Tendsto (fun n => ∑' i, mu n i • a i) atTop (nhds 0)) :
    ∃ p : ℕ → ℝ, CoalitionalProbabilityVector p ∧ ∑' i, p i • a i = 0 := by
  have h0 : ∀ n i, 0 ≤ mu n i := fun n => (hprob n).1
  have h1 : ∀ n i, mu n i ≤ 1 := fun n i => coalitional_probability_le_one (hprob n) i
  obtain ⟨p, phi, hphi, hcoord⟩ := coalitional_exists_coordinate_subseq mu h0 h1
  have hpprob := coalitional_limit_probability mu p phi hprob htight hcoord
  have hbary := coalitional_vector_barycenter_tendsto mu p a phi hprob hpprob hcoord hB
  have hresSub : Tendsto (fun n => ∑' i, mu (phi n) i • a i) atTop (nhds 0) :=
    hres.comp hphi.tendsto_atTop
  exact ⟨p, hpprob, tendsto_nhds_unique hbary hresSub⟩

/-- Tight zero-residual coalitions attain an exact scalar carrier. -/
theorem coalitional_tight_attainment_scalar
    (mu : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (htight : CoalitionalUniformlyTight mu)
    {B : ℝ} (hB : ∀ i, |a i| ≤ B)
    (hres : Tendsto (fun n => ∑' i, mu n i * a i) atTop (nhds 0)) :
    ∃ p : ℕ → ℝ, CoalitionalProbabilityVector p ∧ ∑' i, p i * a i = 0 := by
  have h0 : ∀ n i, 0 ≤ mu n i := fun n => (hprob n).1
  have h1 : ∀ n i, mu n i ≤ 1 := fun n i => coalitional_probability_le_one (hprob n) i
  obtain ⟨p, phi, hphi, hcoord⟩ := coalitional_exists_coordinate_subseq mu h0 h1
  have hpprob := coalitional_limit_probability mu p phi hprob htight hcoord
  have hbary := coalitional_vector_barycenter_tendsto mu p a phi hprob hpprob hcoord
    (by simpa [Real.norm_eq_abs] using hB)
  have hresSub : Tendsto (fun n => ∑' i, mu (phi n) i * a i) atTop (nhds 0) :=
    hres.comp hphi.tendsto_atTop
  have heq : (∑' i, p i * a i) = 0 := tendsto_nhds_unique hbary hresSub
  exact ⟨p, hpprob, heq⟩

def CoalitionalProperPrice (W : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ W i) ∧ Tendsto W atTop atTop

def coalitionalCost (p W : ℕ → ℝ) : ℝ := ∑' i, p i * W i

/-- A uniform proper-price bound forces uniform tightness. -/
theorem coalitional_proper_price_forces_tightness
    (mu : ℕ → ℕ → ℝ) (W : ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (hW : CoalitionalProperPrice W)
    (hcostsum : ∀ n, Summable (fun i => mu n i * W i))
    {C : ℝ} (hC0 : 0 ≤ C) (hcost : ∀ n, coalitionalCost (mu n) W ≤ C) :
    CoalitionalUniformlyTight mu := by
  intro ε hε
  let M : ℝ := (C + 1) / ε
  have hM0 : 0 < M := div_pos (by linarith) hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Filter.tendsto_atTop.mp hW.2) M)
  refine ⟨Finset.range N, fun n => ?_⟩
  let T : Type := ↥(((↑(Finset.range N) : Set ℕ))ᶜ)
  have hmuTail : Summable (fun i : T => mu n (i : ℕ)) :=
    (hprob n).2.summable.subtype _
  have hcostTail : Summable (fun i : T => mu n (i : ℕ) * W (i : ℕ)) :=
    (hcostsum n).subtype _
  have htailCompare :
      M * (∑' i : T, mu n (i : ℕ)) ≤
        ∑' i : T, mu n (i : ℕ) * W (i : ℕ) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun i => by
      have hiN : N ≤ (i : ℕ) := by
        simpa [T, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range,
          not_lt] using i.property
      exact mul_le_mul_of_nonneg_left (hN (i : ℕ) hiN) ((hprob n).1 (i : ℕ)))
      (hmuTail.mul_left M) hcostTail
  have htailCostLe :
      (∑' i : T, mu n (i : ℕ) * W (i : ℕ)) ≤ coalitionalCost (mu n) W := by
    have hsplit := (hcostsum n).sum_add_tsum_compl (s := Finset.range N)
    have hhead0 : 0 ≤ ∑ i ∈ Finset.range N, mu n i * W i := by
      exact Finset.sum_nonneg fun i _ => mul_nonneg ((hprob n).1 i) (hW.1 i)
    dsimp [coalitionalCost]
    linarith
  have htailBound : M * (∑' i : T, mu n (i : ℕ)) ≤ C :=
    le_trans htailCompare (le_trans htailCostLe (hcost n))
  have htail0 : 0 ≤ ∑' i : T, mu n (i : ℕ) :=
    tsum_nonneg fun i => (hprob n).1 (i : ℕ)
  have htailLt : (∑' i : T, mu n (i : ℕ)) < ε := by
    dsimp [M] at htailBound
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp [hεne] at htailBound
    nlinarith
  have hmassSplit := (hprob n).2.summable.sum_add_tsum_compl (s := Finset.range N)
  rw [(hprob n).2.tsum_eq] at hmassSplit
  linarith

/-- Bounded proper price upgrades approximate scalar balance to an actual carrier. -/
theorem coalitional_price_bounded_attainment_scalar
    (mu : ℕ → ℕ → ℝ) (a W : ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (hW : CoalitionalProperPrice W)
    (hcostsum : ∀ n, Summable (fun i => mu n i * W i))
    {C : ℝ} (hC0 : 0 ≤ C) (hcost : ∀ n, coalitionalCost (mu n) W ≤ C)
    {B : ℝ} (hB : ∀ i, |a i| ≤ B)
    (hres : Tendsto (fun n => ∑' i, mu n i * a i) atTop (nhds 0)) :
    ∃ p : ℕ → ℝ, CoalitionalProbabilityVector p ∧ ∑' i, p i * a i = 0 := by
  exact coalitional_tight_attainment_scalar mu a hprob
    (coalitional_proper_price_forces_tightness mu W hprob hW hcostsum hC0 hcost) hB hres

/-- If no actual carrier exists, every approximate history escapes every proper price. -/
theorem coalitional_no_carrier_universal_escape_scalar
    (mu : ℕ → ℕ → ℝ) (a W : ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (hW : CoalitionalProperPrice W)
    (hcostsum : ∀ n, Summable (fun i => mu n i * W i))
    {B : ℝ} (hB : ∀ i, |a i| ≤ B)
    (hres : Tendsto (fun n => ∑' i, mu n i * a i) atTop (nhds 0))
    (hno : ¬ ∃ p : ℕ → ℝ,
      CoalitionalProbabilityVector p ∧ ∑' i, p i * a i = 0) :
    Tendsto (fun n => coalitionalCost (mu n) W) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro C
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hfreq : ∃ᶠ n in atTop, coalitionalCost (mu n) W < C := by
    simpa only [not_le] using hnot
  obtain ⟨phi, hphi, hphiCost⟩ := extraction_of_frequently_atTop hfreq
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hcostSub : ∀ n, coalitionalCost (mu (phi n)) W ≤ C0 := by
    intro n
    exact le_trans (le_of_lt (hphiCost n)) (le_max_left _ _)
  have hresSub : Tendsto (fun n => ∑' i, mu (phi n) i * a i) atTop (nhds 0) :=
    hres.comp hphi.tendsto_atTop
  apply hno
  exact coalitional_price_bounded_attainment_scalar (fun n => mu (phi n)) a W
    (fun n => hprob (phi n)) hW (fun n => hcostsum (phi n)) hC0 hcostSub hB hresSub

/-- Bounded proper resource price upgrades approximate Banach-valued balance to attainment. -/
theorem coalitional_price_bounded_attainment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : ℕ → ℕ → ℝ) (a : ℕ → E) (W : ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (hW : CoalitionalProperPrice W)
    (hcostsum : ∀ n, Summable (fun i => mu n i * W i))
    {C : ℝ} (hC0 : 0 ≤ C) (hcost : ∀ n, coalitionalCost (mu n) W ≤ C)
    {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B)
    (hres : Tendsto (fun n => ∑' i, mu n i • a i) atTop (nhds 0)) :
    ∃ p : ℕ → ℝ, CoalitionalProbabilityVector p ∧ ∑' i, p i • a i = 0 := by
  exact coalitional_tight_attainment mu a hprob
    (coalitional_proper_price_forces_tightness mu W hprob hW hcostsum hC0 hcost) hB hres

/-- If no Banach-valued carrier exists, every approximate history escapes every proper price. -/
theorem coalitional_no_carrier_universal_escape
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : ℕ → ℕ → ℝ) (a : ℕ → E) (W : ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (hW : CoalitionalProperPrice W)
    (hcostsum : ∀ n, Summable (fun i => mu n i * W i))
    {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B)
    (hres : Tendsto (fun n => ∑' i, mu n i • a i) atTop (nhds 0))
    (hno : ¬ ∃ p : ℕ → ℝ,
      CoalitionalProbabilityVector p ∧ ∑' i, p i • a i = 0) :
    Tendsto (fun n => coalitionalCost (mu n) W) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro C
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hfreq : ∃ᶠ n in atTop, coalitionalCost (mu n) W < C := by
    simpa only [not_le] using hnot
  obtain ⟨phi, hphi, hphiCost⟩ := extraction_of_frequently_atTop hfreq
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hcostSub : ∀ n, coalitionalCost (mu (phi n)) W ≤ C0 := fun n =>
    le_trans (le_of_lt (hphiCost n)) (le_max_left _ _)
  have hresSub : Tendsto (fun n => ∑' i, mu (phi n) i • a i) atTop (nhds 0) :=
    hres.comp hphi.tendsto_atTop
  apply hno
  exact coalitional_price_bounded_attainment (fun n => mu (phi n)) a W
    (fun n => hprob (phi n)) hW (fun n => hcostsum (phi n)) hC0 hcostSub hB hresSub

private def coalitionalTailTerm (cut : ℕ → ℕ) (p : ℕ → ℝ) (k i : ℕ) : ℝ :=
  if cut k ≤ i then p i else 0

def coalitionalThresholdPrice (cut : ℕ → ℕ) (i : ℕ) : ℝ :=
  ∑' k, if cut k ≤ i then (1 : ℝ) else 0

private theorem coalitional_tailTerm_tsum_eq
    (cut : ℕ → ℕ) (p : ℕ → ℝ) (k : ℕ) :
    (∑' i, coalitionalTailTerm cut p k i) =
      ∑' i : ↥(((↑(Finset.range (cut k)) : Set ℕ))ᶜ), p (i : ℕ) := by
  rw [tsum_subtype]
  apply tsum_congr
  intro i
  simp only [coalitionalTailTerm, Set.indicator]
  by_cases hi : cut k ≤ i
  · have hmem : i ∈ ((↑(Finset.range (cut k)) : Set ℕ))ᶜ := by
      simpa [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt] using hi
    simp [hi, hmem]
  · have hnotmem : i ∉ ((↑(Finset.range (cut k)) : Set ℕ))ᶜ := by
      simpa [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt] using hi
    simp [hi, hnotmem]

private theorem coalitional_threshold_indicator_summable
    (cut : ℕ → ℕ) (hcut : ∀ k, k + 1 ≤ cut k) (i : ℕ) :
    Summable (fun k => if cut k ≤ i then (1 : ℝ) else 0) := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_range i).subset ?_
  intro k hk
  simp only [Function.support, ne_eq, Set.mem_setOf_eq]
  by_contra hki
  have hik : i ≤ k := Nat.le_of_not_gt hki
  have : i < cut k := lt_of_le_of_lt hik (lt_of_lt_of_le (Nat.lt_succ_self k) (hcut k))
  simp [not_le.mpr this] at hk

private theorem coalitional_threshold_price_proper
    (cut : ℕ → ℕ) (hcut : ∀ k, k + 1 ≤ cut k) :
    CoalitionalProperPrice (coalitionalThresholdPrice cut) := by
  constructor
  · intro i
    exact tsum_nonneg fun k => by split_ifs <;> positivity
  · rw [Filter.tendsto_atTop]
    intro C
    obtain ⟨K : ℕ, hCK⟩ := exists_nat_ge C
    let M : ℕ := ∑ k ∈ Finset.range K, cut k
    filter_upwards [eventually_ge_atTop M] with i hi
    have hsumle : (K : ℝ) ≤ coalitionalThresholdPrice cut i := by
      have hind : ∀ k ∈ Finset.range K, (if cut k ≤ i then (1 : ℝ) else 0) = 1 := by
        intro k hk
        have hcutleM : cut k ≤ M := by
          dsimp [M]
          exact Finset.single_le_sum (fun j _ => Nat.zero_le (cut j)) hk
        rw [if_pos (le_trans hcutleM hi)]
      have hsum : ∑ k ∈ Finset.range K, (if cut k ≤ i then (1 : ℝ) else 0) = K := by
        simp_rw [hind]
        simp
      rw [coalitionalThresholdPrice, ← hsum]
      exact (coalitional_threshold_indicator_summable cut hcut i).sum_le_tsum
        (Finset.range K) (fun _ _ => by split_ifs <;> positivity)
    exact le_trans hCK hsumle

private theorem coalitional_tailTerm_summable
    (cut : ℕ → ℕ) (p : ℕ → ℝ) (hp : CoalitionalProbabilityVector p) (k : ℕ) :
    Summable (fun i => coalitionalTailTerm cut p k i) := by
  exact Summable.of_nonneg_of_le
    (fun i => by simp [coalitionalTailTerm, hp.1 i])
    (fun i => by simp only [coalitionalTailTerm]; split_ifs <;> linarith [hp.1 i])
    hp.2.summable

private theorem coalitional_threshold_cost_identity
    (cut : ℕ → ℕ) (hcut : ∀ k, k + 1 ≤ cut k) (p : ℕ → ℝ) (i : ℕ) :
    (∑' k, coalitionalTailTerm cut p k i) =
      p i * coalitionalThresholdPrice cut i := by
  calc
    (∑' k, coalitionalTailTerm cut p k i) =
        ∑' k, p i * (if cut k ≤ i then (1 : ℝ) else 0) := by
          apply tsum_congr
          intro k
          simp only [coalitionalTailTerm]
          split_ifs <;> ring
    _ = p i * ∑' k, (if cut k ≤ i then (1 : ℝ) else 0) := by
          exact (coalitional_threshold_indicator_summable cut hcut i).tsum_mul_left (p i)
    _ = p i * coalitionalThresholdPrice cut i := rfl

/-- A geometric tail schedule constructs one proper source price with uniformly bounded cost. -/
theorem coalitional_geometric_tails_construct_proper_price
    (mu : ℕ → ℕ → ℝ) (cut : ℕ → ℕ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (hcut : ∀ k, k + 1 ≤ cut k)
    (htail : ∀ k n,
      (∑' i : ↥(((↑(Finset.range (cut k)) : Set ℕ))ᶜ), mu n (i : ℕ)) <
        (1 / 2 : ℝ) ^ (k + 1)) :
    CoalitionalProperPrice (coalitionalThresholdPrice cut) ∧
      (∀ n, Summable (fun i => mu n i * coalitionalThresholdPrice cut i)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ n, coalitionalCost (mu n) (coalitionalThresholdPrice cut) ≤ C := by
  have heps : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
    have h := summable_geometric_two.comp_injective Nat.succ_injective
    simpa [Function.comp_def] using h
  have heps0 : ∀ k : ℕ, 0 ≤ (1 / 2 : ℝ) ^ (k + 1) := fun k => by positivity
  have hrow (n k : ℕ) : Summable (fun i => coalitionalTailTerm cut (mu n) k i) :=
    coalitional_tailTerm_summable cut (mu n) (hprob n) k
  have hrow0 (n k : ℕ) : 0 ≤ ∑' i, coalitionalTailTerm cut (mu n) k i :=
    tsum_nonneg fun i => by simp [coalitionalTailTerm, (hprob n).1 i]
  have hrowLe (n k : ℕ) :
      (∑' i, coalitionalTailTerm cut (mu n) k i) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    rw [coalitional_tailTerm_tsum_eq]
    exact le_of_lt (htail k n)
  have hrowTotals (n : ℕ) :
      Summable (fun k => ∑' i, coalitionalTailTerm cut (mu n) k i) :=
    Summable.of_nonneg_of_le (hrow0 n) (hrowLe n) heps
  have hdouble (n : ℕ) :
      Summable (Function.uncurry (coalitionalTailTerm cut (mu n))) := by
    exact (summable_prod_of_nonneg (fun ki => by
      simp [coalitionalTailTerm, (hprob n).1 ki.2])).2 ⟨hrow n, hrowTotals n⟩
  have hcostsum (n : ℕ) :
      Summable (fun i => mu n i * coalitionalThresholdPrice cut i) := by
    exact (hdouble n).prod.congr (fun i =>
      coalitional_threshold_cost_identity cut hcut (mu n) i)
  refine ⟨coalitional_threshold_price_proper cut hcut, hcostsum, ?_⟩
  refine ⟨∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1), tsum_nonneg heps0, ?_⟩
  intro n
  have hcomm := (hdouble n).tsum_comm
  have hleft :
      (∑' i, ∑' k, coalitionalTailTerm cut (mu n) k i) =
        coalitionalCost (mu n) (coalitionalThresholdPrice cut) := by
    dsimp [coalitionalCost]
    apply tsum_congr
    intro i
    exact coalitional_threshold_cost_identity cut hcut (mu n) i
  have hright :
      (∑' k, ∑' i, coalitionalTailTerm cut (mu n) k i) ≤
        ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1) :=
    Summable.tsum_le_tsum (hrowLe n) (hrowTotals n) heps
  rw [hleft] at hcomm
  exact le_trans hcomm.ge hright

/-- Every uniformly tight countable family constructs its own proper uniformly bounded price. -/
theorem coalitional_tightness_constructs_proper_price
    (mu : ℕ → ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    (htight : CoalitionalUniformlyTight mu) :
    ∃ W : ℕ → ℝ, CoalitionalProperPrice W ∧
      (∀ n, Summable (fun i => mu n i * W i)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, coalitionalCost (mu n) W ≤ C := by
  classical
  let eps : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (k + 1)
  have heps : ∀ k, 0 < eps k := fun k => by dsimp [eps]; positivity
  choose F hF using fun k => htight (eps k) (heps k)
  choose rawCut hraw using fun k => Finset.exists_nat_subset_range (F k)
  let cut : ℕ → ℕ := fun k => max (rawCut k) (k + 1)
  have hcut : ∀ k, k + 1 ≤ cut k := fun k => le_max_right _ _
  have hFcut : ∀ k, F k ⊆ Finset.range (cut k) := by
    intro k
    exact (hraw k).trans (Finset.range_mono (le_max_left _ _))
  have htail : ∀ k n,
      (∑' i : ↥(((↑(Finset.range (cut k)) : Set ℕ))ᶜ), mu n (i : ℕ)) <
        (1 / 2 : ℝ) ^ (k + 1) := by
    intro k n
    have hheadLe : ∑ i ∈ F k, mu n i ≤ ∑ i ∈ Finset.range (cut k), mu n i :=
      Finset.sum_le_sum_of_subset_of_nonneg (hFcut k)
        (fun i _ _ => (hprob n).1 i)
    have hhead : 1 - eps k < ∑ i ∈ Finset.range (cut k), mu n i :=
      lt_of_lt_of_le (hF k n) hheadLe
    have hsplit := (hprob n).2.summable.sum_add_tsum_compl
      (s := Finset.range (cut k))
    rw [(hprob n).2.tsum_eq] at hsplit
    dsimp [eps] at hhead
    linarith
  let W := coalitionalThresholdPrice cut
  have hbuilt := coalitional_geometric_tails_construct_proper_price mu cut hprob hcut htail
  exact ⟨W, hbuilt⟩

/-- Full countable effectivity equivalence: tight approximation and bounded proper pricing are
interchangeable hypotheses for scalar carrier attainment. -/
theorem coalitional_tight_or_priced_attainment_scalar
    (mu : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hprob : ∀ n, CoalitionalProbabilityVector (mu n))
    {B : ℝ} (hB : ∀ i, |a i| ≤ B)
    (hres : Tendsto (fun n => ∑' i, mu n i * a i) atTop (nhds 0)) :
    (CoalitionalUniformlyTight mu ↔
      ∃ W : ℕ → ℝ, CoalitionalProperPrice W ∧
        (∀ n, Summable (fun i => mu n i * W i)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, coalitionalCost (mu n) W ≤ C) ∧
      (CoalitionalUniformlyTight mu →
        ∃ p : ℕ → ℝ, CoalitionalProbabilityVector p ∧ ∑' i, p i * a i = 0) := by
  constructor
  · constructor
    · exact coalitional_tightness_constructs_proper_price mu hprob
    · rintro ⟨W, hW, hsum, C, hC0, hcost⟩
      exact coalitional_proper_price_forces_tightness mu W hprob hW hsum hC0 hcost
  · intro htight
    exact coalitional_tight_attainment_scalar mu a hprob htight hB hres

private theorem coalitional_probability_exists_pos {p : ℕ → ℝ}
    (hp : CoalitionalProbabilityVector p) : ∃ j, 0 < p j := by
  by_contra hnot
  push_neg at hnot
  have hpzero : p = 0 := by
    funext j
    exact le_antisymm (hnot j) (hp.1 j)
  have hz : HasSum p 0 := by simpa [hpzero] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have := hp.2.unique hz
  norm_num at this

def coalitionalNormalizedPrefix (p : ℕ → ℝ) (j n i : ℕ) : ℝ :=
  if i < j + n + 1 then p i / (∑ k ∈ Finset.range (j + n + 1), p k) else 0

private theorem coalitional_normalizedPrefix_probability
    {p : ℕ → ℝ} (hp : CoalitionalProbabilityVector p) {j : ℕ} (hj : 0 < p j) (n : ℕ) :
    CoalitionalProbabilityVector (coalitionalNormalizedPrefix p j n) := by
  let s : ℝ := ∑ k ∈ Finset.range (j + n + 1), p k
  have hjmem : j ∈ Finset.range (j + n + 1) := by simp; omega
  have hspos : 0 < s := by
    dsimp [s]
    exact lt_of_lt_of_le hj (Finset.single_le_sum (fun k _ => hp.1 k) hjmem)
  have hnonneg : ∀ i, 0 ≤ coalitionalNormalizedPrefix p j n i := by
    intro i
    simp only [coalitionalNormalizedPrefix]
    split_ifs
    · exact div_nonneg (hp.1 i) hspos.le
    · exact le_rfl
  refine ⟨hnonneg, ?_⟩
  have hsum : HasSum (coalitionalNormalizedPrefix p j n)
      (∑ i ∈ Finset.range (j + n + 1), coalitionalNormalizedPrefix p j n i) := by
    apply hasSum_sum_of_ne_finset_zero
    intro i hi
    simp [coalitionalNormalizedPrefix, Finset.mem_range.mp (by simpa using hi)]
  convert hsum using 1
  simp only [coalitionalNormalizedPrefix]
  have hsumdiv :
      (∑ i ∈ Finset.range (j + n + 1),
        if i < j + n + 1 then p i / s else 0) = s / s := by
    simp only [Finset.mem_range, ↓reduceIte]
    dsimp [s]
    rw [Finset.sum_div]
  rw [hsumdiv, div_self hspos.ne']

private theorem coalitional_normalizedPrefix_finite_support
    (p : ℕ → ℝ) (j n : ℕ) :
    (Function.support (coalitionalNormalizedPrefix p j n)).Finite := by
  refine (Set.finite_range (j + n + 1)).subset ?_
  intro i hi
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at hi
  simp only [Set.mem_range]
  by_contra hnot
  have : ¬ i < j + n + 1 := by omega
  simp [coalitionalNormalizedPrefix, this] at hi

private theorem coalitional_normalizedPrefix_coordinate_tendsto
    {p : ℕ → ℝ} (hp : CoalitionalProbabilityVector p) {j : ℕ} (hj : 0 < p j) (i : ℕ) :
    Tendsto (fun n => coalitionalNormalizedPrefix p j n i) atTop (nhds (p i)) := by
  have hcut : Tendsto (fun n : ℕ => j + n + 1) atTop atTop := by
    simpa [add_assoc, add_comm, add_left_comm] using tendsto_add_atTop_nat (j + 1)
  have hpartial : Tendsto
      (fun n => ∑ k ∈ Finset.range (j + n + 1), p k) atTop (nhds 1) :=
    hp.2.tendsto_sum_nat.comp hcut
  have hdiv : Tendsto
      (fun n => p i / (∑ k ∈ Finset.range (j + n + 1), p k))
      atTop (nhds (p i)) := by
    simpa using (tendsto_const_nhds.div hpartial one_ne_zero)
  apply hdiv.congr'
  filter_upwards [(Filter.tendsto_atTop.mp hcut) (i + 1)] with n hn
  have hi : i < j + n + 1 := by omega
  simp [coalitionalNormalizedPrefix, hi]

private theorem coalitional_normalizedPrefix_tight
    {p : ℕ → ℝ} (hp : CoalitionalProbabilityVector p) {j : ℕ} (hj : 0 < p j) :
    CoalitionalUniformlyTight (fun n => coalitionalNormalizedPrefix p j n) := by
  intro ε hε
  have hcoord : ∀ i, Tendsto (fun n => coalitionalNormalizedPrefix p j n i)
      atTop (nhds (p i)) := fun i => coalitional_normalizedPrefix_coordinate_tendsto hp hj i
  obtain ⟨F, hFev⟩ := exists_finset_eventually_tsum_compl_lt
    (fun n i => (coalitional_normalizedPrefix_probability hp hj n).1 i)
    (fun n => (coalitional_normalizedPrefix_probability hp hj n).2) hp.2 hcoord hε
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hFev
  let G : Finset ℕ := F ∪ Finset.range (j + N0 + 1)
  refine ⟨G, fun n => ?_⟩
  by_cases hn : N0 ≤ n
  · have htailF := hN0 n hn
    have hsplit :=
      (coalitional_normalizedPrefix_probability hp hj n).2.summable.sum_add_tsum_compl (s := F)
    rw [(coalitional_normalizedPrefix_probability hp hj n).2.tsum_eq] at hsplit
    have hFleG :
        ∑ i ∈ F, coalitionalNormalizedPrefix p j n i ≤
          ∑ i ∈ G, coalitionalNormalizedPrefix p j n i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun i _ _ => (coalitional_normalizedPrefix_probability hp hj n).1 i)
    linarith
  · have hnlt : n < N0 := Nat.lt_of_not_ge hn
    have hsupp : ∀ i ∉ G, coalitionalNormalizedPrefix p j n i = 0 := by
      intro i hi
      have hirange : i ∉ Finset.range (j + N0 + 1) := by
        intro hir
        exact hi (Finset.mem_union_right F hir)
      have hnotlt : ¬ i < j + n + 1 := by
        simp only [Finset.mem_range, not_lt] at hirange
        omega
      simp [coalitionalNormalizedPrefix, hnotlt]
    have hsumG : HasSum (coalitionalNormalizedPrefix p j n)
        (∑ i ∈ G, coalitionalNormalizedPrefix p j n i) :=
      hasSum_sum_of_ne_finset_zero hsupp
    have : ∑ i ∈ G, coalitionalNormalizedPrefix p j n i = 1 :=
      hsumG.unique (coalitional_normalizedPrefix_probability hp hj n).2
    linarith

/-- Every exact scalar carrier is the limit of tight finite-support coalitions. -/
theorem coalitional_exact_carrier_has_tight_finite_approximation_scalar
    (p a : ℕ → ℝ) (hp : CoalitionalProbabilityVector p)
    {B : ℝ} (hB : ∀ i, |a i| ≤ B) (hzero : ∑' i, p i * a i = 0) :
    ∃ mu : ℕ → ℕ → ℝ,
      (∀ n, CoalitionalProbabilityVector (mu n)) ∧
      (∀ n, (Function.support (mu n)).Finite) ∧
      CoalitionalUniformlyTight mu ∧
      Tendsto (fun n => ∑' i, mu n i * a i) atTop (nhds 0) := by
  obtain ⟨j, hj⟩ := coalitional_probability_exists_pos hp
  let mu : ℕ → ℕ → ℝ := fun n => coalitionalNormalizedPrefix p j n
  have hprob : ∀ n, CoalitionalProbabilityVector (mu n) := fun n =>
    coalitional_normalizedPrefix_probability hp hj n
  have hcoord : ∀ i, Tendsto (fun n => mu n i) atTop (nhds (p i)) := fun i =>
    coalitional_normalizedPrefix_coordinate_tendsto hp hj i
  have hbary := coalitional_vector_barycenter_tendsto mu p a id hprob hp
    (by simpa using hcoord) (by simpa [Real.norm_eq_abs] using hB)
  have hbary0 : Tendsto (fun n => ∑' i, mu n i * a i) atTop (nhds 0) := by
    simpa [Function.comp_def, hzero] using hbary
  exact ⟨mu, hprob, fun n => coalitional_normalizedPrefix_finite_support p j n,
    coalitional_normalizedPrefix_tight hp hj, hbary0⟩

/-- Every exact Banach-valued carrier is approximated by tight finite-support coalitions. -/
theorem coalitional_exact_carrier_has_tight_finite_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : ℕ → ℝ) (a : ℕ → E) (hp : CoalitionalProbabilityVector p)
    {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B) (hzero : ∑' i, p i • a i = 0) :
    ∃ mu : ℕ → ℕ → ℝ,
      (∀ n, CoalitionalProbabilityVector (mu n)) ∧
      (∀ n, (Function.support (mu n)).Finite) ∧
      CoalitionalUniformlyTight mu ∧
      Tendsto (fun n => ∑' i, mu n i • a i) atTop (nhds 0) := by
  obtain ⟨j, hj⟩ := coalitional_probability_exists_pos hp
  let mu : ℕ → ℕ → ℝ := fun n => coalitionalNormalizedPrefix p j n
  have hprob : ∀ n, CoalitionalProbabilityVector (mu n) := fun n =>
    coalitional_normalizedPrefix_probability hp hj n
  have hcoord : ∀ i, Tendsto (fun n => mu n i) atTop (nhds (p i)) := fun i =>
    coalitional_normalizedPrefix_coordinate_tendsto hp hj i
  have hbary := coalitional_vector_barycenter_tendsto mu p a id hprob hp
    (by simpa using hcoord) hB
  have hbary0 : Tendsto (fun n => ∑' i, mu n i • a i) atTop (nhds 0) := by
    simpa [Function.comp_def, hzero] using hbary
  exact ⟨mu, hprob, fun n => coalitional_normalizedPrefix_finite_support p j n,
    coalitional_normalizedPrefix_tight hp hj, hbary0⟩

/-- Central CAM equivalence: an actual positive carrier exists exactly when zero is approached
by a tight history of finite positive coalitions. -/
theorem coalitional_attainment_iff_tight_finite_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a : ℕ → E) {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B) :
    (∃ p : ℕ → ℝ, CoalitionalProbabilityVector p ∧ ∑' i, p i • a i = 0) ↔
      ∃ mu : ℕ → ℕ → ℝ,
        (∀ n, CoalitionalProbabilityVector (mu n)) ∧
        (∀ n, (Function.support (mu n)).Finite) ∧
        CoalitionalUniformlyTight mu ∧
        Tendsto (fun n => ∑' i, mu n i • a i) atTop (nhds 0) := by
  constructor
  · rintro ⟨p, hp, hzero⟩
    exact coalitional_exact_carrier_has_tight_finite_approximation p a hp hB hzero
  · rintro ⟨mu, hprob, _hfinite, htight, hres⟩
    exact coalitional_tight_attainment mu a hprob htight hB hres

/-- Priced form of the central equivalence: actual positive carriers are exactly finite
zero-residual histories bounded by some proper source price. -/
theorem coalitional_attainment_iff_proper_priced_finite_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a : ℕ → E) {B : ℝ} (hB : ∀ i, ‖a i‖ ≤ B) :
    (∃ p : ℕ → ℝ, CoalitionalProbabilityVector p ∧ ∑' i, p i • a i = 0) ↔
      ∃ (mu : ℕ → ℕ → ℝ) (W : ℕ → ℝ) (C : ℝ),
        (∀ n, CoalitionalProbabilityVector (mu n)) ∧
        (∀ n, (Function.support (mu n)).Finite) ∧
        CoalitionalProperPrice W ∧
        (∀ n, Summable (fun i => mu n i * W i)) ∧
        0 ≤ C ∧
        (∀ n, coalitionalCost (mu n) W ≤ C) ∧
        Tendsto (fun n => ∑' i, mu n i • a i) atTop (nhds 0) := by
  constructor
  · rintro ⟨p, hp, hzero⟩
    obtain ⟨mu, hprob, hfinite, htight, hres⟩ :=
      coalitional_exact_carrier_has_tight_finite_approximation p a hp hB hzero
    obtain ⟨W, hW, hsum, C, hC0, hcost⟩ :=
      coalitional_tightness_constructs_proper_price mu hprob htight
    exact ⟨mu, W, C, hprob, hfinite, hW, hsum, hC0, hcost, hres⟩
  · rintro ⟨mu, W, C, hprob, _hfinite, hW, hsum, hC0, hcost, hres⟩
    exact coalitional_price_bounded_attainment mu a W hprob hW hsum hC0 hcost hB hres

/-- Reciprocal pricing is a finite, coordinate-free Cauchy--Schwarz obstruction:
if every active law atom has response-times-price at least `κ`, then coalition response
times coalition cost is at least `κ`. -/
theorem coalitional_reciprocal_pricing
    {ι : Type*} (F : Finset ι) (mu response price : ι → ℝ)
    (hmu : ∀ i ∈ F, 0 ≤ mu i)
    (hresponse : ∀ i ∈ F, 0 ≤ response i)
    (hprice : ∀ i ∈ F, 0 ≤ price i)
    (hmass : ∑ i ∈ F, mu i = 1)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hreciprocal : ∀ i ∈ F, κ ≤ response i * price i) :
    κ ≤ (∑ i ∈ F, mu i * response i) * ∑ i ∈ F, mu i * price i := by
  have hpoint : ∀ i ∈ F,
      (mu i * Real.sqrt κ) ^ 2 ≤
        (mu i * response i) * (mu i * price i) := by
    intro i hi
    calc
      (mu i * Real.sqrt κ) ^ 2 = (mu i) ^ 2 * κ := by
        rw [mul_pow, Real.sq_sqrt hκ]
      _ ≤ (mu i) ^ 2 * (response i * price i) :=
        mul_le_mul_of_nonneg_left (hreciprocal i hi) (sq_nonneg _)
      _ = (mu i * response i) * (mu i * price i) := by ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
    (fun i hi => mul_nonneg (hmu i hi) (hresponse i hi))
    (fun i hi => mul_nonneg (hmu i hi) (hprice i hi)) hpoint
  have hsqrt : ∑ i ∈ F, mu i * Real.sqrt κ = Real.sqrt κ := by
    rw [← Finset.sum_mul, hmass, one_mul]
  rw [hsqrt, Real.sq_sqrt hκ] at hcs
  exact hcs

/-- Banach-valued residual--resource uncertainty. A continuous linear separator converts the
finite reciprocal-pricing inequality into a norm bound on collective defect. -/
theorem coalitional_banach_reciprocal_pricing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (F : Finset ι) (mu : ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    (hmu : ∀ i ∈ F, 0 ≤ mu i)
    (hresponse : ∀ i ∈ F, 0 ≤ φ (a i))
    (hprice : ∀ i ∈ F, 0 ≤ price i)
    (hmass : ∑ i ∈ F, mu i = 1)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hreciprocal : ∀ i ∈ F, κ ≤ φ (a i) * price i) :
    κ ≤ ‖φ‖ * ‖∑ i ∈ F, mu i • a i‖ * ∑ i ∈ F, mu i * price i := by
  have hbase := coalitional_reciprocal_pricing F mu (fun i => φ (a i)) price
    hmu hresponse hprice hmass hκ hreciprocal
  have hcost0 : 0 ≤ ∑ i ∈ F, mu i * price i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hmu i hi) (hprice i hi)
  have hmap : ∑ i ∈ F, mu i * φ (a i) = φ (∑ i ∈ F, mu i • a i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  have hresponseBound : ∑ i ∈ F, mu i * φ (a i) ≤
      ‖φ‖ * ‖∑ i ∈ F, mu i • a i‖ := by
    rw [hmap]
    exact le_trans (le_abs_self _) (φ.le_opNorm _)
  exact le_trans hbase (mul_le_mul_of_nonneg_right hresponseBound hcost0)

theorem coalitional_banach_reciprocal_pricing_div
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (F : Finset ι) (mu : ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    (hmu : ∀ i ∈ F, 0 ≤ mu i)
    (hresponse : ∀ i ∈ F, 0 ≤ φ (a i))
    (hprice : ∀ i ∈ F, 0 ≤ price i)
    (hmass : ∑ i ∈ F, mu i = 1)
    {κ : ℝ} (hκ : 0 ≤ κ) (hφ : 0 < ‖φ‖)
    (hreciprocal : ∀ i ∈ F, κ ≤ φ (a i) * price i) :
    κ / ‖φ‖ ≤ ‖∑ i ∈ F, mu i • a i‖ * ∑ i ∈ F, mu i * price i := by
  apply (div_le_iff₀ hφ).2
  rw [mul_assoc]
  exact coalitional_banach_reciprocal_pricing F mu a price φ hmu hresponse hprice hmass
    hκ hreciprocal

/-- Canonical scalar escape law: atom `i` has positive defect `1/(i+1)`. -/
def coalitionalEscapeRule (i : ℕ) : ℝ := 1 / (i + 1 : ℝ)

/-- Coalition concentrated on a single index. -/
def coalitionalDiracHistory (n i : ℕ) : ℝ := if i = n then 1 else 0

theorem coalitional_dirac_probability (n : ℕ) :
    CoalitionalProbabilityVector (coalitionalDiracHistory n) := by
  constructor
  · intro i
    simp [coalitionalDiracHistory]
  · simpa [coalitionalDiracHistory] using (hasSum_ite_eq n (1 : ℝ))

theorem coalitional_dirac_finite_support (n : ℕ) :
    (Function.support (coalitionalDiracHistory n)).Finite := by
  refine Set.Finite.subset (Set.finite_singleton n) ?_
  intro i hi
  simp [Function.support, coalitionalDiracHistory] at hi ⊢

theorem coalitional_dirac_barycenter (n : ℕ) :
    ∑' i, coalitionalDiracHistory n i * coalitionalEscapeRule i =
      coalitionalEscapeRule n := by
  rw [tsum_congr (fun i => by simp [coalitionalDiracHistory])]
  exact tsum_ite_eq n (coalitionalEscapeRule n)

theorem coalitional_escapeRule_tendsto_zero :
    Tendsto coalitionalEscapeRule atTop (nhds 0) := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  simpa [coalitionalEscapeRule, Nat.cast_add, Nat.cast_one] using
    tendsto_one_div_atTop_nhds_zero_nat.comp hshift

/-- Positive coalitions cannot realize zero for the canonical escape law. -/
theorem coalitional_escapeRule_has_no_carrier
    (p : ℕ → ℝ) (hp : CoalitionalProbabilityVector p) :
    0 < ∑' i, p i * coalitionalEscapeRule i := by
  obtain ⟨j, hj⟩ := coalitional_probability_exists_pos hp
  have hrule0 : 0 < coalitionalEscapeRule j := by
    simp [coalitionalEscapeRule]
    positivity
  have hsum : Summable (fun i => p i * coalitionalEscapeRule i) := by
    apply coalitional_weighted_summable hp (B := 1)
    intro i
    rw [abs_of_nonneg]
    · exact one_div_le_one (by positivity) (by norm_num)
    · positivity
  have hle : p j * coalitionalEscapeRule j ≤
      ∑' i, p i * coalitionalEscapeRule i := by
    have := hsum.sum_le_tsum {j} (fun i _ => mul_nonneg (hp.1 i) (by
      simp [coalitionalEscapeRule]
      positivity))
    simpa using this
  exact lt_of_lt_of_le (mul_pos hj hrule0) hle

/-- Linear price is proper and exactly reciprocal to the canonical escape rule. -/
theorem coalitional_escapeRule_reciprocal (i : ℕ) :
    coalitionalEscapeRule i * (i + 1 : ℝ) = 1 := by
  rw [coalitionalEscapeRule, one_div, inv_mul_cancel₀]
  positivity

/-- Sharp mirage: finite positive coalitions have residual tending to zero, but no exact
positive carrier exists; every proper price diverges along this same history. -/
theorem coalitional_sharp_escape_countermodel :
    (∀ n, CoalitionalProbabilityVector (coalitionalDiracHistory n)) ∧
    (∀ n, (Function.support (coalitionalDiracHistory n)).Finite) ∧
    Tendsto
      (fun n => ∑' i, coalitionalDiracHistory n i * coalitionalEscapeRule i)
      atTop (nhds 0) ∧
    (∀ p, CoalitionalProbabilityVector p →
      ∑' i, p i * coalitionalEscapeRule i ≠ 0) ∧
    (∀ W : ℕ → ℝ, CoalitionalProperPrice W →
      Tendsto (fun n => coalitionalCost (coalitionalDiracHistory n) W) atTop atTop) := by
  refine ⟨coalitional_dirac_probability, coalitional_dirac_finite_support, ?_, ?_, ?_⟩
  · simpa [coalitional_dirac_barycenter] using coalitional_escapeRule_tendsto_zero
  · intro p hp
    exact ne_of_gt (coalitional_escapeRule_has_no_carrier p hp)
  · intro W hW
    have hcost : ∀ n, coalitionalCost (coalitionalDiracHistory n) W = W n := by
      intro n
      simp [coalitionalCost, coalitionalDiracHistory, tsum_ite_eq]
    simpa only [hcost] using hW.2

end

end GaloisForLFunctions.HTGeometry
