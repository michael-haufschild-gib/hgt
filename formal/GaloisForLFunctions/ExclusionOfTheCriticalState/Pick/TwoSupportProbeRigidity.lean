import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.WeilProbeCutBudget
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxWeilParityEulerRayWeld

/-!
# Exact nullspace of two-support Weil probe tests

The complete Xi Euler-response determinant is strictly positive on two
distinct positive real nodes. Transport to the actual Weil probe kernel
shows that repeated probes carry only their aggregated coefficients.
For distinct exponents both aggregates must vanish; for coincident
exponents only their total must vanish. Every resulting sign cut obeys
the exact aligned-energy budget, independently of the number of terms.
-/

open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
open _root_.RHTower ProbeCuts
noncomputable section

def safeProbeEntry (s t : ℝ) : ℝ := bareMixedEnergy (probe (node s)) (probe (node t))

/-- The literal Weil entry equals the complete, multiplicity-exact Xi Euler response. -/
theorem safeProbeEntry_eq_fullKernel (s t : ℝ) :
    safeProbeEntry s t = xiSquaredEulerFullKernel (node s) (node t) := by
  have hs : (1 / 2 : ℝ) < node s := by unfold node; linarith only [abs_nonneg s]
  have ht : (1 / 2 : ℝ) < node t := by unfold node; linarith only [abs_nonneg t]
  have he (x : ℝ) (hx : 1 / 2 < x) : probeSymbol x = xiSquaredEulerFullQ x := by
    have h := (probeSymbol_eq_logDeriv_xiCent hx).trans (logDeriv_xiCent_ofReal_eq_fullQ hx)
    exact_mod_cast h
  rw [safeProbeEntry, bareMixedEnergy_probe hs ht, he _ hs, he _ ht]
  rfl

private theorem safeProbeEntry_symm (s t : ℝ) : safeProbeEntry s t = safeProbeEntry t s := by
  rw [safeProbeEntry_eq_fullKernel, safeProbeEntry_eq_fullKernel]
  simp only [xiSquaredEulerFullKernel, eulerRayResponseKernel, add_comm]

private theorem safeProbeEntry_det_pos (s t : ℝ) (hst : node s ≠ node t) :
    0 < safeProbeEntry s s * safeProbeEntry t t - safeProbeEntry s t ^ 2 := by
  rw [safeProbeEntry_eq_fullKernel, safeProbeEntry_eq_fullKernel, safeProbeEntry_eq_fullKernel]
  have hs : 0 < node s := by unfold node; linarith only [abs_nonneg s]
  have ht : 0 < node t := by unfold node; linarith only [abs_nonneg t]
  rcases lt_or_gt_of_ne hst with h | h
  · exact xiSquaredEulerFullKernel_twoPoint_det_pos hs h
  · have hp := xiSquaredEulerFullKernel_twoPoint_det_pos ht h
    have he : xiSquaredEulerFullKernel (node t) (node s) =
        xiSquaredEulerFullKernel (node s) (node t) := by
      simp only [xiSquaredEulerFullKernel, eulerRayResponseKernel, add_comm]
    rw [he, mul_comm] at hp
    exact hp

/-- The full two-probe energy, retaining its mixed term. -/
def twoProbeQuadratic (s t u v : ℝ) : ℝ :=
  safeProbeEntry s s * u ^ 2 + safeProbeEntry t t * v ^ 2 +
    2 * safeProbeEntry s t * u * v

private theorem twoProbeQuadratic_completion (s t u v : ℝ) :
    safeProbeEntry s s * twoProbeQuadratic s t u v =
      (safeProbeEntry s s * u + safeProbeEntry s t * v) ^ 2 +
        (safeProbeEntry s s * safeProbeEntry t t - safeProbeEntry s t ^ 2) * v ^ 2 := by
  unfold twoProbeQuadratic
  ring

private theorem twoProbeQuadratic_pos (s t u v : ℝ) (hst : node s ≠ node t)
    (huv : ¬ (u = 0 ∧ v = 0)) : 0 < twoProbeQuadratic s t u v := by
  have hA : 0 < safeProbeEntry s s := probeEntry_pos s s
  by_cases hv : v = 0
  · have hu : u ≠ 0 := fun hu => huv ⟨hu, hv⟩
    simp only [twoProbeQuadratic, hv, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, add_zero]
    exact mul_pos hA (sq_pos_of_ne_zero hu)
  · have hp := mul_pos (safeProbeEntry_det_pos s t hst) (sq_pos_of_ne_zero hv)
    have he := twoProbeQuadratic_completion s t u v
    have hprod : 0 < safeProbeEntry s s * twoProbeQuadratic s t u v := by
      rw [he]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) hp
    rcases mul_pos_iff.mp hprod with hp | hn
    · exact hp.2
    · exact False.elim ((not_lt_of_ge hA.le) hn.1)

private theorem twoProbeQuadratic_coincident (s t u v : ℝ) (hst : node s = node t) :
    twoProbeQuadratic s t u v = safeProbeEntry s s * (u + v) ^ 2 := by
  unfold twoProbeQuadratic safeProbeEntry
  rw [← hst]
  ring

/-- Every actual two-support probe form is nonnegative, including coincident exponents. -/
theorem twoProbeQuadratic_nonneg (s t u v : ℝ) : 0 ≤ twoProbeQuadratic s t u v := by
  by_cases hst : node s = node t
  · rw [twoProbeQuadratic_coincident s t u v hst]
    exact mul_nonneg (probeEntry_pos s s).le (sq_nonneg _)
  · by_cases huv : u = 0 ∧ v = 0
    · rcases huv with ⟨rfl, rfl⟩
      simp only [twoProbeQuadratic, zero_pow (by decide : (2 : ℕ) ≠ 0),
        mul_zero, add_zero, le_refl]
    · exact (twoProbeQuadratic_pos s t u v hst huv).le

/-- Exact two-probe nullspace, including the rank-one collision boundary. -/
theorem twoProbeQuadratic_zero_iff (s t u v : ℝ) :
    twoProbeQuadratic s t u v = 0 ↔
      if node s = node t then u + v = 0 else u = 0 ∧ v = 0 := by
  by_cases hst : node s = node t
  · have hA : safeProbeEntry s s ≠ 0 := (probeEntry_pos s s).ne'
    rw [if_pos hst, twoProbeQuadratic_coincident s t u v hst,
      mul_eq_zero, or_iff_right hA, sq_eq_zero_iff]
  · rw [if_neg hst]
    constructor
    · intro hz
      by_contra huv
      exact (twoProbeQuadratic_pos s t u v hst huv).ne' hz
    · rintro ⟨rfl, rfl⟩
      simp only [twoProbeQuadratic, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero]

/-- Aggregate one of the two coefficient fibers before evaluating energy. -/
def probeFiberSum {n : ℕ} (σ : Fin n → Bool) (c : Fin n → ℝ) (b : Bool) : ℝ :=
  ∑ i, if σ i = b then c i else 0

/-- Arbitrarily many repeated probes collapse exactly to their two aggregated coefficients. -/
theorem twoSupport_probe_collapse {n : ℕ} (s t : ℝ) (σ : Fin n → Bool) (c : Fin n → ℝ) :
    sourceQuadratic n (fun i => if σ i then s else t) c =
      twoProbeQuadratic s t (probeFiberSum σ c true) (probeFiberSum σ c false) := by
  have he (U V : ℝ) : twoProbeQuadratic s t U V =
      safeProbeEntry s s * (U * U) + safeProbeEntry t t * (V * V) +
        safeProbeEntry s t * (U * V) + safeProbeEntry t s * (V * U) := by
    rw [safeProbeEntry_symm t s]
    unfold twoProbeQuadratic
    ring
  rw [he]
  unfold probeFiberSum sourceQuadratic
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsym : bareMixedEnergy (probe (node t)) (probe (node s)) =
      bareMixedEnergy (probe (node s)) (probe (node t)) := safeProbeEntry_symm t s
  cases σ i <;> cases σ j <;> simp [safeProbeEntry, hsym] <;> ring

/-- The complete kernel of any finite two-support family is determined by coefficient fibers. -/
theorem twoSupport_probe_zero_iff {n : ℕ} (s t : ℝ) (σ : Fin n → Bool) (c : Fin n → ℝ) :
    sourceQuadratic n (fun i => if σ i then s else t) c = 0 ↔
      if node s = node t then probeFiberSum σ c true + probeFiberSum σ c false = 0
      else probeFiberSum σ c true = 0 ∧ probeFiberSum σ c false = 0 := by
  rw [twoSupport_probe_collapse, twoProbeQuadratic_zero_iff]

/-- Every sign partition of a two-support probe family respects the full cut budget. -/
theorem twoSupport_probe_cut_budget {n : ℕ} (s t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → ℝ) (τ : Fin n → Bool) :
    cutWeight (fun i => if σ i then s else t) a τ ≤
      alignedEnergy (fun i => if σ i then s else t) a / 4 := by
  apply (probe_form_nonnegative_iff_cut_budget n (fun i => if σ i then s else t)).mp
  intro c
  rw [twoSupport_probe_collapse]
  exact twoProbeQuadratic_nonneg _ _ _ _

#print axioms safeProbeEntry_eq_fullKernel
#print axioms twoProbeQuadratic_nonneg
#print axioms twoProbeQuadratic_zero_iff
#print axioms twoSupport_probe_collapse
#print axioms twoSupport_probe_zero_iff
#print axioms twoSupport_probe_cut_budget
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
