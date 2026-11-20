import GaloisForLFunctions.HTGeometry.PathShellDelayFloor
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Almost sure coefficient bounds for growing Gaussian Pauli chains

Each site has three independent onsite coordinates and nine independent
couplings to its successor. A finite open chain omits the last edge.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

abbrev PathPauliDirections := Fin 3 ⊕ (Fin 3 × Fin 3)
abbrev PathPauliDisorder := (ℕ × PathPauliDirections) → ℝ

/-- Independent standard Gaussian coefficients for an infinite path. -/
def pathPauliDisorderLaw : Measure PathPauliDisorder :=
  Measure.infinitePi (fun _ => gaussianReal 0 1)

/-- Restriction of the disorder to the first n+2 sites and their n+1 edges. -/
def pathPauliDisorderShell (ω : PathPauliDisorder) (n : ℕ) : PathShell n :=
  WithLp.toLp 2 fun l => match l with
    | .inl (s,a) => ω (s.val,.inl a)
    | .inr (e,ab) => ω (e.val,.inr ab)

private theorem gaussian_direction_slln (d : PathPauliDirections) (f : ℝ → ℝ)
    (hf : Measurable f) (hi : Integrable f (gaussianReal 0 1)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
      (fun N : ℕ => (∑ i ∈ Finset.range N, f (ω (i,d))) / N)
      atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  let X (i : ℕ) (ω : PathPauliDisorder) := f (ω (i,d))
  have hident (i : ℕ) : IdentDistrib (X i) f pathPauliDisorderLaw (gaussianReal 0 1) := by
    have h := measurePreserving_eval_infinitePi (fun _ : ℕ × PathPauliDirections => gaussianReal 0 1) (i,d)
    have h' : IdentDistrib (Function.eval (i,d)) id pathPauliDisorderLaw (gaussianReal 0 1) :=
      ⟨h.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact h.map_eq⟩
    exact h'.comp hf
  have hindep : iIndepFun X pathPauliDisorderLaw := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ × PathPauliDirections => gaussianReal 0 1)
      (X := fun _ x => f x) (fun _ => hf)
    exact h.precomp (g := fun i : ℕ => (i,d)) (fun _ _ e => congrArg Prod.fst e)
  have h := strong_law_ae_real X ((hident 0).integrable_iff.mpr hi)
    (fun _ _ hij => hindep.indepFun hij) (fun i => (hident i).trans (hident 0).symm)
  rwa [(hident 0).integral_eq] at h

private def gaussianAbsMean : ℝ := ∫ x : ℝ, |x| ∂gaussianReal 0 1
private def gaussianSquareMean : ℝ := ∫ x : ℝ, x^2 ∂gaussianReal 0 1

private theorem gaussian_abs_integrable : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
  have h : MemLp id 1 (gaussianReal 0 1) := memLp_id_gaussianReal' _ (by simp)
  simpa [Real.norm_eq_abs] using (memLp_one_iff_integrable.mp h).norm

private theorem gaussian_abs_mean_pos : 0 < gaussianAbsMean := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  apply (integral_pos_iff_support_of_nonneg (fun _ => abs_nonneg _) gaussian_abs_integrable).mpr
  have he : Function.support (fun x : ℝ => |x|) = ({0} : Set ℝ)ᶜ := by ext x; simp [Function.support]
  rw [he,measure_compl (measurableSet_singleton 0) (by simp)]
  simp

private theorem disorder_sq_le (ω : PathPauliDisorder) (n : ℕ) :
    ‖pathPauliDisorderShell ω n‖^2 ≤
      ∑ d : PathPauliDirections, ∑ i ∈ Finset.range (n+2), (ω (i,d))^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Real.norm_eq_abs,sq_abs]
  change (∑ s : Fin (n+2), ∑ a : Fin 3, (ω (s.val,.inl a))^2) +
    (∑ e : Fin (n+1), ∑ a : Fin 3, ∑ b : Fin 3, (ω (e.val,.inr (a,b)))^2) ≤ _
  apply add_le_add
  · rw [Finset.sum_comm]
    exact le_of_eq (Finset.sum_congr rfl fun a _ =>
      Fin.sum_univ_eq_sum_range (fun i => (ω (i,.inl a))^2) (n+2))
  · rw [Fin.sum_univ_eq_sum_range (fun e => ∑ a : Fin 3, ∑ b : Fin 3, (ω (e,.inr (a,b)))^2)]
    calc
      _ ≤ ∑ e ∈ Finset.range (n+2), ∑ a : Fin 3, ∑ b : Fin 3, (ω (e,.inr (a,b)))^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- The same constants work eventually almost surely: the onsite longitudinal
mass grows at least linearly and the total squared mass grows at most linearly. -/
theorem gaussian_path_eventual_coefficient_mass :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      a*(n+2:ℕ) ≤ ∑ s : Fin (n+2), |pathPauliDisorderShell ω n (.inl (s,2))| ∧
      ‖pathPauliDisorderShell ω n‖^2 ≤ b*(n+2:ℕ) := by
  have hs : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_sq
  have hb : 0 < gaussianSquareMean + 1 := by
    have h : 0 ≤ gaussianSquareMean := integral_nonneg fun _ => sq_nonneg _
    linarith
  refine ⟨gaussianAbsMean/2,12*(gaussianSquareMean+1),by linarith [gaussian_abs_mean_pos],
    mul_pos (by norm_num) hb,?_⟩
  have H (d : PathPauliDirections) := gaussian_direction_slln d (fun x => x^2) (by fun_prop) hs
  filter_upwards [gaussian_direction_slln (.inl 2) abs measurable_abs gaussian_abs_integrable,
    ae_all_iff.mpr H] with ω hab hsq
  have hz := hab.eventually_const_lt (show gaussianAbsMean/2 < gaussianAbsMean by linarith [gaussian_abs_mean_pos])
  have hu (d : PathPauliDirections) := (hsq d).eventually_lt_const
    (show gaussianSquareMean < gaussianSquareMean + 1 by linarith)
  have ha := (Filter.eventually_all.mpr hu).and hz
  have hN : Tendsto (fun n : ℕ => n+2) atTop atTop := tendsto_add_atTop_nat 2
  filter_upwards [hN.eventually ha] with n hn
  have hp : 0 < ((n+2:ℕ):ℝ) := by positivity
  constructor
  · change _ ≤ ∑ s : Fin (n+2), |ω (s.val,.inl 2)|
    rw [Fin.sum_univ_eq_sum_range (fun j => |ω (j,.inl 2)|)]
    exact ((lt_div_iff₀ hp).mp hn.2).le
  · apply (disorder_sq_le ω n).trans
    calc
      _ ≤ ∑ _d : PathPauliDirections, (gaussianSquareMean+1)*((n+2:ℕ):ℝ) :=
        Finset.sum_le_sum fun d _ => ((div_lt_iff₀ hp).mp (hn.1 d)).le
      _ = _ := by simp [PathPauliDirections,Fintype.card_sum,Fintype.card_prod]; ring

#print axioms gaussian_path_eventual_coefficient_mass
end
end GaloisForLFunctions.HTGeometry
