import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactness.Lindelof

/-!
# Path connected nonzero loci of entire functions

A complex affine line reduces avoidance to a countable set of isolated zeros in the
plane. This extends the corpus polynomial-complement construction to entire functions
on complex normed spaces, without a finite-dimensional assumption.
-/

open Set Filter Topology unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Zeros of a nonzero entire function form a countable set. -/
theorem countable_zeros_of_entire_nonzero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z : ℂ} (hz : f z ≠ 0) :
    {t | f t = 0}.Countable := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun t _ => hf.analyticAt t
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with he | he
  · exact (hz (he (Set.mem_univ z))).elim
  · have hn : {t | f t = 0}ᶜ ∈ codiscrete ℂ := he
    exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (compl_mem_codiscrete_iff.mp hn).2

/-- Any two nonzeros of an entire complex function on a normed vector space can be joined
through nonzeros, by bending their affine-line parameter around its countable zero set. -/
theorem exists_path_avoiding_entire_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : Differentiable ℂ f) {x y : E} (hx : f x ≠ 0) (hy : f y ≠ 0) :
    ∃ p : Path x y, ∀ t : I, f (p t) ≠ 0 := by
  let line : ℂ → E := fun t => x + t • (y - x)
  have hl : Differentiable ℂ line := by unfold line; fun_prop
  have hzero : line 0 = x := by simp [line]
  have hone : line 1 = y := by simp [line]
  have hz : (f ∘ line) 0 ≠ 0 := by simpa only [Function.comp_apply, hzero] using hx
  have hc : {t | (f ∘ line) t = 0}.Countable :=
    countable_zeros_of_entire_nonzero (hf.comp hl) hz
  have hp : IsPathConnected {t | (f ∘ line) t = 0}ᶜ := by
    apply hc.isPathConnected_compl_of_one_lt_rank
    rw [Complex.rank_real_complex]
    norm_num
  have h0 : (0 : ℂ) ∈ {t | (f ∘ line) t = 0}ᶜ := hz
  have h1 : (1 : ℂ) ∈ {t | (f ∘ line) t = 0}ᶜ := by
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, Function.comp_apply, hone] using hy
  let joined := hp.joinedIn 0 h0 1 h1
  let p : Path x y :=
    { toFun := fun t => line (joined.somePath t)
      continuous_toFun := hl.continuous.comp joined.somePath.continuous
      source' := by rw [joined.somePath.source, hzero]
      target' := by rw [joined.somePath.target, hone] }
  exact ⟨p, fun t => joined.somePath_mem t⟩

/-- Nonempty nonzero loci of entire functions on complex normed vector spaces are path connected. -/
theorem isPathConnected_entire_nonzeroLocus {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f)
    {x : E} (hx : f x ≠ 0) : IsPathConnected {y | f y ≠ 0} := by
  refine ⟨x, hx, ?_⟩
  intro y hy
  obtain ⟨p, hp⟩ := exists_path_avoiding_entire_zero hf hx hy
  exact ⟨p, hp⟩

end
end GaloisForLFunctions.HTGeometry
