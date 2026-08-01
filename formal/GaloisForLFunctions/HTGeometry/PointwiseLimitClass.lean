import Mathlib.Topology.Order.Bornology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The structural class of a pointwise limit

Oddness, monotonicity, a uniform Lipschitz bound, a uniform range bound and a normalization at a
point all pass to a pointwise limit.  Each is a closed condition, so the limit of a family obeying
them obeys them too.

This is the class half of a cofinal extraction statement: the extraction produces a limit, and these
lemmas say what the limit inherits.  Nothing here needs the extraction itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {ι : Type*} {l : Filter ι} [l.NeBot] {U : ι → ℝ → ℝ} {Ulim : ℝ → ℝ}

/-- Oddness passes to a pointwise limit. -/
theorem odd_of_tendsto (hodd : ∀ i y, U i (-y) = -U i y)
    (hlim : ∀ y, Tendsto (fun i => U i y) l (nhds (Ulim y))) (y : ℝ) :
    Ulim (-y) = -Ulim y := by
  have h1 : Tendsto (fun i => U i (-y)) l (nhds (Ulim (-y))) := hlim (-y)
  have h3 : (fun i => U i (-y)) = fun i => -U i y := funext fun i => hodd i y
  rw [h3] at h1
  exact tendsto_nhds_unique h1 (hlim y).neg

/-- An odd function vanishes at the origin. -/
theorem eq_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ y, f (-y) = -f y) : f 0 = 0 := by
  have h := hodd 0
  rw [neg_zero] at h
  linarith

/-- Monotonicity passes to a pointwise limit. -/
theorem monotone_of_tendsto (hmono : ∀ i, Monotone (U i))
    (hlim : ∀ y, Tendsto (fun i => U i y) l (nhds (Ulim y))) : Monotone Ulim := by
  intro y z hyz
  exact le_of_tendsto_of_tendsto' (hlim y) (hlim z) fun i => hmono i hyz

/-- A uniform Lipschitz bound passes to a pointwise limit. -/
theorem lipschitzBound_of_tendsto {K : ℝ} (hlip : ∀ i y z, |U i y - U i z| ≤ K * |y - z|)
    (hlim : ∀ y, Tendsto (fun i => U i y) l (nhds (Ulim y))) (y z : ℝ) :
    |Ulim y - Ulim z| ≤ K * |y - z| := by
  have habs : Tendsto (fun i => |U i y - U i z|) l (nhds |Ulim y - Ulim z|) :=
    ((hlim y).sub (hlim z)).abs
  exact le_of_tendsto habs (Eventually.of_forall fun i => hlip i y z)

/-- A uniform range bound passes to a pointwise limit. -/
theorem mem_Icc_of_tendsto {a b : ℝ} (hmem : ∀ i y, U i y ∈ Set.Icc a b)
    (hlim : ∀ y, Tendsto (fun i => U i y) l (nhds (Ulim y))) (y : ℝ) :
    Ulim y ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · exact ge_of_tendsto (hlim y) (Eventually.of_forall fun i => (hmem i y).1)
  · exact le_of_tendsto (hlim y) (Eventually.of_forall fun i => (hmem i y).2)

/-- **The structural class of a cofinal limit.**  A pointwise limit of odd, monotone, uniformly
Lipschitz functions with values in a fixed interval is odd, monotone, Lipschitz with the same
constant, valued in the same interval, and centered at the origin. -/
theorem limitClass_of_tendsto {K a b : ℝ}
    (hodd : ∀ i y, U i (-y) = -U i y) (hmono : ∀ i, Monotone (U i))
    (hlip : ∀ i y z, |U i y - U i z| ≤ K * |y - z|)
    (hmem : ∀ i y, U i y ∈ Set.Icc a b)
    (hlim : ∀ y, Tendsto (fun i => U i y) l (nhds (Ulim y))) :
    (∀ y, Ulim (-y) = -Ulim y) ∧ Monotone Ulim ∧
      (∀ y z, |Ulim y - Ulim z| ≤ K * |y - z|) ∧ (∀ y, Ulim y ∈ Set.Icc a b) ∧ Ulim 0 = 0 :=
  ⟨odd_of_tendsto hodd hlim, monotone_of_tendsto hmono hlim,
    lipschitzBound_of_tendsto hlip hlim, mem_Icc_of_tendsto hmem hlim,
    eq_zero_of_odd (odd_of_tendsto hodd hlim)⟩

/-! ## The extraction

A uniformly bounded, equi-Lipschitz sequence has a pointwise convergent subsequence.  Restricted to
the rationals the family lives in a countable product of compact intervals, which is compact and
metrizable, hence sequentially compact.  The Lipschitz bound then makes the subsequence Cauchy at
every real point, so the limit exists everywhere. -/

theorem exists_subseq_tendsto_of_equiLipschitz
    {a b K : ℝ} (hK : 0 ≤ K) {U : ℕ → ℝ → ℝ}
    (hmem : ∀ n y, U n y ∈ Set.Icc a b)
    (hlip : ∀ n y z, |U n y - U n z| ≤ K * |y - z|) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ Ulim : ℝ → ℝ,
      ∀ y, Tendsto (fun k => U (ns k) y) atTop (nhds (Ulim y)) := by
  classical
  set F : ℕ → (ℚ → Set.Icc a b) :=
    fun n => fun q : ℚ => (⟨U n (q : ℝ), hmem n (q : ℝ)⟩ : Set.Icc a b) with hFdef
  obtain ⟨L, -, ns, hns, hL⟩ :=
    (isCompact_univ (X := ℚ → Set.Icc a b)).tendsto_subseq (x := F) (fun n => Set.mem_univ _)
  have hQ : ∀ q : ℚ,
      Tendsto (fun k => U (ns k) (q : ℝ)) atTop (nhds ((L q : Set.Icc a b) : ℝ)) := by
    intro q
    exact (continuous_subtype_val.tendsto _).comp ((tendsto_pi_nhds.mp hL) q)
  have hcauchy : ∀ y : ℝ, CauchySeq (fun k => U (ns k) y) := by
    intro y
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hKpos : (0 : ℝ) < 4 * (K + 1) := by linarith
    obtain ⟨q, hq⟩ := exists_rat_near y (by positivity : 0 < ε / (4 * (K + 1)))
    have hqc := (hQ q).cauchySeq
    rw [Metric.cauchySeq_iff] at hqc
    obtain ⟨N, hN⟩ := hqc (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmid := hN m hm n hn
    have h1 : |U (ns m) y - U (ns m) (q : ℝ)| ≤ K * |y - q| := hlip _ _ _
    have h2 : |U (ns n) y - U (ns n) (q : ℝ)| ≤ K * |y - q| := hlip _ _ _
    have hbound : K * |y - (q : ℝ)| ≤ ε / 4 := by
      have hle : K * |y - (q : ℝ)| ≤ K * (ε / (4 * (K + 1))) :=
        mul_le_mul_of_nonneg_left (le_of_lt hq) hK
      have hfrac : K * (ε / (4 * (K + 1))) ≤ ε / 4 := by
        have key : K * (ε / (4 * (K + 1))) = (K * ε) / (4 * (K + 1)) := by ring
        rw [key, div_le_div_iff₀ hKpos (by norm_num : (0:ℝ) < 4)]
        nlinarith [hε.le, hK]
      linarith
    rw [Real.dist_eq] at hmid ⊢
    have hsplit : |U (ns m) y - U (ns n) y| ≤
        |U (ns m) y - U (ns m) (q : ℝ)| + |U (ns m) (q : ℝ) - U (ns n) (q : ℝ)|
          + |U (ns n) (q : ℝ) - U (ns n) y| := by
      have t1 : |U (ns m) y - U (ns n) y| ≤
          |U (ns m) y - U (ns m) (q : ℝ)| + |U (ns m) (q : ℝ) - U (ns n) y| := by
        simpa [Real.norm_eq_abs, sub_add_sub_cancel] using
          norm_add_le (U (ns m) y - U (ns m) (q : ℝ)) (U (ns m) (q : ℝ) - U (ns n) y)
      have t2 : |U (ns m) (q : ℝ) - U (ns n) y| ≤
          |U (ns m) (q : ℝ) - U (ns n) (q : ℝ)| + |U (ns n) (q : ℝ) - U (ns n) y| := by
        simpa [Real.norm_eq_abs, sub_add_sub_cancel] using
          norm_add_le (U (ns m) (q : ℝ) - U (ns n) (q : ℝ))
            (U (ns n) (q : ℝ) - U (ns n) y)
      linarith
    have habs2 : |U (ns n) (q : ℝ) - U (ns n) y| ≤ K * |y - (q : ℝ)| := by
      rw [abs_sub_comm]
      exact h2
    linarith
  choose Ulim hUlim using fun y => cauchySeq_tendsto_of_complete (hcauchy y)
  exact ⟨ns, hns, Ulim, hUlim⟩

/-- **Mass extraction.**  A sequence of families indexed by a countable set and valued in a fixed
interval has a pointwise convergent subsequence, the limits lying in the same interval. -/
theorem exists_subseq_tendsto_of_mem_Icc {ι : Type*} [Countable ι] {a b : ℝ} {p : ℕ → ι → ℝ}
    (hmem : ∀ n k, p n k ∈ Set.Icc a b) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ plim : ι → ℝ,
      (∀ k, plim k ∈ Set.Icc a b) ∧
        ∀ k, Tendsto (fun j => p (ns j) k) atTop (nhds (plim k)) := by
  classical
  set P : ℕ → (ι → Set.Icc a b) :=
    fun n => fun k : ι => (⟨p n k, hmem n k⟩ : Set.Icc a b) with hPdef
  obtain ⟨L, -, ns, hns, hL⟩ :=
    (isCompact_univ (X := ι → Set.Icc a b)).tendsto_subseq (x := P) (fun n => Set.mem_univ _)
  refine ⟨ns, hns, fun k => ((L k : Set.Icc a b) : ℝ), fun k => (L k).2, fun k => ?_⟩
  exact (continuous_subtype_val.tendsto _).comp ((tendsto_pi_nhds.mp hL) k)

/-- **A common subsequence for both extractions.**  Along one subsequence the phase profiles
converge pointwise and the mass families converge coordinatewise.  Extract for the profiles first,
then thin further for the masses; a subsequence of a convergent sequence still converges. -/
theorem exists_subseq_tendsto_joint {ι : Type*} [Countable ι] {a b c d K : ℝ} (hK : 0 ≤ K)
    {U : ℕ → ℝ → ℝ} {p : ℕ → ι → ℝ}
    (hmemU : ∀ n y, U n y ∈ Set.Icc a b)
    (hlip : ∀ n y z, |U n y - U n z| ≤ K * |y - z|)
    (hmemp : ∀ n k, p n k ∈ Set.Icc c d) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ (Ulim : ℝ → ℝ) (plim : ι → ℝ),
      (∀ y, Tendsto (fun j => U (ns j) y) atTop (nhds (Ulim y))) ∧
      (∀ k, plim k ∈ Set.Icc c d) ∧
      (∀ k, Tendsto (fun j => p (ns j) k) atTop (nhds (plim k))) := by
  obtain ⟨ns₁, hns₁, Ulim, hU⟩ := exists_subseq_tendsto_of_equiLipschitz hK hmemU hlip
  obtain ⟨ns₂, hns₂, plim, hpmem, hp⟩ :=
    exists_subseq_tendsto_of_mem_Icc (p := fun j k => p (ns₁ j) k) (fun j k => hmemp _ _)
  refine ⟨ns₁ ∘ ns₂, hns₁.comp hns₂, Ulim, plim, ?_, hpmem, hp⟩
  intro y
  exact (hU y).comp hns₂.tendsto_atTop

end GaloisForLFunctions.HTGeometry
