import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Multiplication by a measurable function is a closed operator on `L²`

The graph of multiplication by a fixed measurable symbol,

`{(u, v) : v = m · u almost everywhere}`,

is closed in `L² × L²`.  Convergence in `L²` forces convergence in measure, hence an almost
everywhere convergent subsequence, and the defining identity passes to that limit.  This is the
closedness that makes a Fourier-multiplier graph domain complete: no boundedness of the symbol is
used, so it applies to symbols that grow, such as the logarithmic frequency weight.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The graph of multiplication by a measurable symbol. -/
def multiplierGraph (m : α → ℂ) (μ : Measure α) : Set (Lp ℂ 2 μ × Lp ℂ 2 μ) :=
  {p | (p.2 : α → ℂ) =ᵐ[μ] fun x => m x * (p.1 : α → ℂ) x}

/-- An `L²`-convergent sequence has an almost everywhere convergent subsequence. -/
theorem exists_subseq_ae_tendsto {f : ℕ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ}
    (hf : Tendsto f atTop (𝓝 g)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i => (f (ns i) : α → ℂ) x) atTop (𝓝 ((g : α → ℂ) x)) := by
  have hmeasure : TendstoInMeasure μ (fun n => (f n : α → ℂ)) atTop (g : α → ℂ) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun n => (Lp.aestronglyMeasurable (f n)))
      (Lp.aestronglyMeasurable g)
    have hnorm : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0) := by
      have hsub : Tendsto (fun n => f n - g) atTop (𝓝 (0 : Lp ℂ 2 μ)) := by
        have h := hf.sub (tendsto_const_nhds (x := g) (f := atTop (α := ℕ)))
        simpa using h
      have h2 := (continuous_norm (E := Lp ℂ 2 μ)).tendsto (0 : Lp ℂ 2 μ) |>.comp hsub
      simpa [Function.comp_def] using h2
    have hconv : ∀ n : ℕ, eLpNorm ((f n : α → ℂ) - (g : α → ℂ)) 2 μ = ENNReal.ofReal ‖f n - g‖ := by
      intro n
      rw [Lp.norm_def, ENNReal.ofReal_toReal (by
        exact (Lp.eLpNorm_ne_top (f n - g)))]
      exact (eLpNorm_congr_ae (Lp.coeFn_sub (f n) g)).symm
    have hgoal : Tendsto (fun n => eLpNorm ((f n : α → ℂ) - (g : α → ℂ)) 2 μ) atTop (𝓝 0) := by
      rw [tendsto_congr hconv]
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
    exact hgoal
  exact hmeasure.exists_seq_tendsto_ae

/-- **The multiplier graph is closed.** -/
theorem isClosed_multiplierGraph (m : α → ℂ) : IsClosed (multiplierGraph m μ) := by
  refine IsSeqClosed.isClosed ?_
  intro p q hp hconv
  have hfst : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hconv
  have hsnd : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hconv
  obtain ⟨ns, hns, hae1⟩ := exists_subseq_ae_tendsto hfst
  obtain ⟨ms, hms, hae2⟩ := exists_subseq_ae_tendsto
    (hsnd.comp (strictMono_nat_of_lt_succ (fun n => hns (Nat.lt_succ_self n))).tendsto_atTop)
  have hae1' : ∀ᵐ x ∂μ,
      Tendsto (fun i => ((p (ns (ms i))).1 : α → ℂ) x) atTop (𝓝 ((q.1 : α → ℂ) x)) := by
    filter_upwards [hae1] with x hx
    exact hx.comp hms.tendsto_atTop
  have hgraph : ∀ᵐ x ∂μ, ∀ i : ℕ,
      ((p (ns (ms i))).2 : α → ℂ) x = m x * ((p (ns (ms i))).1 : α → ℂ) x := by
    rw [ae_all_iff]
    intro i
    exact hp (ns (ms i))
  filter_upwards [hae1', hae2, hgraph] with x hx1 hx2 hxg
  have hlim1 : Tendsto (fun i => m x * ((p (ns (ms i))).1 : α → ℂ) x) atTop
      (𝓝 (m x * (q.1 : α → ℂ) x)) := hx1.const_mul _
  have hlim2 : Tendsto (fun i => ((p (ns (ms i))).2 : α → ℂ) x) atTop
      (𝓝 ((q.2 : α → ℂ) x)) := hx2
  have heq : (fun i => ((p (ns (ms i))).2 : α → ℂ) x)
      = fun i => m x * ((p (ns (ms i))).1 : α → ℂ) x := funext fun i => hxg i
  rw [heq] at hlim2
  exact tendsto_nhds_unique hlim2 hlim1

/-- The profiles supported in a fixed measurable set. -/
def supportedIn (S : Set α) (μ : Measure α) : Set (Lp ℂ 2 μ) :=
  {u | (u : α → ℂ) =ᵐ[μ] Set.indicator S (u : α → ℂ)}

/-- **The support condition is closed.** -/
theorem isClosed_supportedIn (S : Set α) :
    IsClosed (supportedIn S μ) := by
  refine IsSeqClosed.isClosed ?_
  intro f g hf hconv
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto hconv
  have hsupp : ∀ᵐ x ∂μ, ∀ i : ℕ,
      ((f (ns i) : α → ℂ)) x = Set.indicator S ((f (ns i) : α → ℂ)) x := by
    rw [ae_all_iff]
    intro i
    exact hf (ns i)
  filter_upwards [hae, hsupp] with x hx hxs
  by_cases hmem : x ∈ S
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem]
    have hzero : ∀ i : ℕ, ((f (ns i) : α → ℂ)) x = 0 := by
      intro i
      rw [hxs i, Set.indicator_of_notMem hmem]
    have hlim : Tendsto (fun i => ((f (ns i) : α → ℂ)) x) atTop (𝓝 (0 : ℂ)) := by
      simp only [hzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hx hlim

/-- **`(19)`: the multiplier graph domain with the support condition is closed**, hence complete in
the graph norm. -/
theorem isClosed_multiplierGraph_supported (m : α → ℂ) (S : Set α) :
    IsClosed (multiplierGraph m μ ∩ {p : Lp ℂ 2 μ × Lp ℂ 2 μ | p.1 ∈ supportedIn S μ}) :=
  (isClosed_multiplierGraph m).inter ((isClosed_supportedIn S).preimage continuous_fst)

end GaloisForLFunctions.HTGeometry
