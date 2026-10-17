import GaloisForLFunctions.RHTower.MobiusDivisorPrimeWindowSynthesis
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Actual-prime realization of a Banach-valued positive clock cone

This is the arithmetic transfer step. A separate source theorem must establish
membership in the positive cone in the chosen Banach norm.
-/

noncomputable section
open Finset Set Filter Topology
open scoped NNReal

namespace RHTower.PrimePreparation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def clockAtom (q : ℝ → E) (N p : ℕ) : E :=
  (Real.sqrt N / p) • q (Real.log ((N : ℝ) / p))

private def clockRatioSource (q : ℝ → E) (r : ℝ) : E := r⁻¹ • q (-Real.log r)

private theorem continuousAt_clockRatioSource (q : ℝ → E) (hq : Continuous q)
    {r : ℝ} (hr : 0 < r) : ContinuousAt (clockRatioSource q) r :=
  (continuousAt_inv₀ hr.ne').smul (hq.continuousAt.comp (Real.continuousAt_log hr.ne').neg)

private theorem clockRatioSource_normalized (q : ℝ → E) {N p : ℕ}
    (hN : 0 < N) (hp : 0 < p) :
    (Real.sqrt N)⁻¹ • clockRatioSource q ((p : ℝ) / N) = clockAtom q N p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hl : -Real.log ((p : ℝ) / N) = Real.log ((N : ℝ) / p) := by
    rw [Real.log_div hp0.ne' hN0.ne', Real.log_div hN0.ne' hp0.ne']
    ring
  unfold clockRatioSource clockAtom
  rw [smul_smul, hl]
  congr 1
  field_simp [hs.ne', hp0.ne', hN0.ne']
  nlinarith only [Real.sq_sqrt hN0.le]

theorem eventually_exists_prime_clock_synthesis (q : ℝ → E) (hq : Continuous q)
    (T : ℝ) (f : E)
    (hf : f ∈ closure (PointedCone.hull ℝ
      (Set.range fun t : {t : ℝ // T < t} => q t) : Set E))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T < Real.log ((N : ℝ) / p)) ∧
      ‖(∑ p ∈ S, clockAtom q N p) - f‖ < ε ∧
      (∑ p ∈ S, ‖clockAtom q N p‖ ^ 2) < ε := by
  classical
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf (ε / 2) (by positivity)
  obtain ⟨c₀, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  let c : {t : ℝ // T < t} →₀ ℝ≥0 := c₀
  have hc : ‖c.sum (fun t b => b • q t) - f‖ < ε / 2 := by
    rw [dist_eq_norm, norm_sub_rev] at hdist
    convert hdist using 1
    congr 2
  let r (t : {t : ℝ // T < t}) : ℝ := Real.exp (-t.val)
  let w (t : {t : ℝ // T < t}) : ℝ := (c t : ℝ) * r t
  have hr (t : {t : ℝ // T < t}) (_ht : t ∈ c.support) :
      0 < r t ∧ r t < Real.exp (-T) :=
    ⟨Real.exp_pos _, Real.exp_lt_exp.mpr (neg_lt_neg t.property)⟩
  have hw (t : {t : ℝ // T < t}) (_ht : t ∈ c.support) : 0 ≤ w t := by
    dsimp [w, r]
    positivity
  have hinj : Set.InjOn r (↑c.support) := by
    intro t ht s hs he
    apply Subtype.ext
    exact neg_injective (Real.exp_injective he)
  have hsource (t : {t : ℝ // T < t}) (ht : t ∈ c.support) :
      ContinuousAt (clockRatioSource q) (r t) := continuousAt_clockRatioSource q hq (hr t ht).1
  have he := eventually_exists_prime_vector_synthesis c.support r w (clockRatioSource q)
    (show (0 : ℝ) < ε / 2 by positivity) hr hw hinj hsource
  have hmixture : (∑ t ∈ c.support, w t • clockRatioSource q (r t)) =
      c.sum (fun t b => b • q t) := by
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro t ht
    simp only [w, clockRatioSource, r, Real.log_exp, neg_neg, smul_smul, NNReal.smul_def]
    rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos (-t.val)).ne', mul_one]
  rw [hmixture] at he
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  obtain ⟨S, hS, happ, hdiag⟩ := hN
  have ha (p : ℕ) (hp : p ∈ S) := clockRatioSource_normalized q hN0 (hS p hp).1.pos
  have hsum : (∑ p ∈ S, (Real.sqrt N)⁻¹ • clockRatioSource q ((p : ℝ) / N)) =
      ∑ p ∈ S, clockAtom q N p := Finset.sum_congr rfl ha
  rw [hsum] at happ
  have hsum2 : (∑ p ∈ S, ‖(Real.sqrt N)⁻¹ • clockRatioSource q ((p : ℝ) / N)‖ ^ 2) =
      ∑ p ∈ S, ‖clockAtom q N p‖ ^ 2 := Finset.sum_congr rfl fun p hp => by rw [ha p hp]
  rw [hsum2] at hdiag
  refine ⟨S, ?_, ?_, hdiag.trans (by linarith only [hε])⟩
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
    have hl := Real.log_lt_log (div_pos hp0 hN') (hS p hp).2.2
    rw [Real.log_exp, Real.log_div hp0.ne' hN'.ne'] at hl
    refine ⟨(hS p hp).1, (hS p hp).2.1, ?_⟩
    rw [Real.log_div hN'.ne' hp0.ne']
    linarith only [hl]
  · calc
      _ = ‖((∑ p ∈ S, clockAtom q N p) - c.sum (fun t b => b • q t)) +
          (c.sum (fun t b => b • q t) - f)‖ := by congr 1; abel
      _ ≤ ‖(∑ p ∈ S, clockAtom q N p) - c.sum (fun t b => b • q t)‖ +
          ‖c.sum (fun t b => b • q t) - f‖ := norm_add_le _ _
      _ < ε := (add_lt_add happ hc).trans_eq (by ring)

end RHTower.PrimePreparation
