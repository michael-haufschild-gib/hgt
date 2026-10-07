import GaloisForLFunctions.Bottcher.AlgebraicBranch
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Exact logarithmic coordinates for a meromorphic cosine pole

Scalar analytic submersion produces the unit in the quadratic cosine identity.
A normalized local logarithm removes any condition on the unit’s argument.
These are classical local analytic dependencies for the algebraic-fiber argument.
-/

namespace GaloisForLFunctions.HTGeometry.CosinePoleUnit

open Complex
open scoped Topology

noncomputable section

theorem exists_analytic_log {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L 0 ∧ L 0 = log (f 0) ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), exp (L s) = f s := by
  let L := fun s => log (f s / f 0) + log (f 0)
  have hL : AnalyticAt ℂ L 0 :=
    ((hf.div analyticAt_const h0).clog (by simp [h0])).add analyticAt_const
  refine ⟨L, hL, by simp [L, h0], ?_⟩
  filter_upwards [hf.continuousAt.eventually_ne h0] with s hs
  dsimp [L]
  rw [exp_add, exp_log (div_ne_zero hs h0), exp_log h0, div_mul_cancel₀ _ h0]

def unitEquation (A : ℂ → ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  p.2 ^ 2 - 2 * A p.1 * p.2 + p.1 ^ (2 * m)

theorem exists_unit {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (hA0 : A 0 ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a 0 ∧ a 0 = 2 * A 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), a s ^ 2 - 2 * A s * a s + s ^ (2 * m) = 0 := by
  have hf : AnalyticAt ℂ (unitEquation A m) (0, 2 * A 0) := by
    have hAs : AnalyticAt ℂ (fun p : ℂ × ℂ => A p.1) (0, 2 * A 0) :=
      hA.comp (f := fun p : ℂ × ℂ => p.1) analyticAt_fst
    exact ((analyticAt_snd.pow 2).sub ((analyticAt_const.mul hAs).mul analyticAt_snd)).add
      (analyticAt_fst.pow (2 * m))
  have hroot : unitEquation A m (0, 2 * A 0) = 0 := by
    simp only [unitEquation, zero_pow (by omega : 2 * m ≠ 0), add_zero]
    ring
  have hd : HasDerivAt (fun z => unitEquation A m (0, z)) (2 * A 0) (2 * A 0) := by
    convert! ((hasDerivAt_pow 2 (2 * A 0)).sub
      ((hasDerivAt_id (2 * A 0)).const_mul (2 * A 0))).add_const ((0 : ℂ) ^ (2 * m)) using 1
    norm_num
    ring
  exact Bottcher.exists_analyticAt_branch_of_hasDerivAt hf.contDiffAt hroot hd
    (mul_ne_zero (by norm_num) hA0)

theorem exists_logarithmic_unit {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (hA0 : A 0 ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    ∃ α : ℂ → ℂ, AnalyticAt ℂ α 0 ∧ exp (α 0) = 2 * A 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ),
        exp (α s) ^ 2 - 2 * A s * exp (α s) + s ^ (2 * m) = 0 := by
  obtain ⟨a, ha, ha0, heq⟩ := exists_unit hA hA0 m hm
  have ha0ne : a 0 ≠ 0 := by rw [ha0]; exact mul_ne_zero (by norm_num) hA0
  obtain ⟨α, hα, hα0, hαeq⟩ := exists_analytic_log ha ha0ne
  refine ⟨α, hα, ?_, ?_⟩
  · rw [hα0, exp_log ha0ne, ha0]
  · filter_upwards [heq, hαeq] with s hs hsα
    rwa [hsα]

theorem cosine_of_unit_equation {A E s U : ℂ} {m : ℕ}
    (hs : s ≠ 0) (hE : E ≠ 0)
    (heq : E ^ 2 - 2 * A * E + s ^ (2 * m) = 0)
    (hexp : exp (U * I) = E / s ^ m) : cos U = A / s ^ m := by
  have hz : exp (U * I) ≠ 0 := exp_ne_zero _
  have hc := Complex.two_cos U
  rw [neg_mul, exp_neg] at hc
  have h : 2 * exp (U * I) * cos U = 1 + exp (U * I) ^ 2 := by
    linear_combination exp (U * I) * hc + mul_inv_cancel₀ hz
  rw [hexp] at h
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hs
  have heq' : E ^ 2 - 2 * A * E + (s ^ m) ^ 2 = 0 := by
    simpa only [← pow_mul, Nat.mul_comm m 2] using heq
  field_simp at h
  apply (eq_div_iff hsm).mpr
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hE)
  linear_combination h + heq'

end

end GaloisForLFunctions.HTGeometry.CosinePoleUnit
