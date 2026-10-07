import GaloisForLFunctions.HTGeometry.CosinePoleUnit
import Mathlib.Analysis.Analytic.Order

/-! # A ramified analytic cosine inverse, including both critical values

Exact finite-order factorization gives a square root of any analytic germ
after the substitution s ↦ s². The quadratic exponential identity and a
local logarithm then give a cosine inverse. Nonconstant input yields a
positive finite-order displacement. These are classical analytic facts.
-/

namespace GaloisForLFunctions.HTGeometry.CosineRamifiedInverse

open Complex Filter
open scoped Topology

noncomputable section

theorem exists_ramified_square_root {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ), g s ^ 2 = f (s ^ 2) := by
  have hsq : AnalyticAt ℂ (fun s : ℂ => s ^ 2) 0 := analyticAt_id.pow 2
  have hp : Tendsto (fun s : ℂ => s ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using hsq.continuousAt.tendsto
  by_cases hz : ∀ᶠ s in 𝓝 (0 : ℂ), f s = 0
  · refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [hp.eventually hz] with s hs
    simp [hs]
  obtain ⟨k, h, hh, hh0, hfact⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
  obtain ⟨L, hL, _, hLeq⟩ := CosinePoleUnit.exists_analytic_log hh hh0
  let g := fun s : ℂ => s ^ k * exp (L (s ^ 2) / 2)
  have hL' : AnalyticAt ℂ L ((0 : ℂ) ^ 2) := by simpa using hL
  have hLc : AnalyticAt ℂ (fun s : ℂ => L (s ^ 2)) 0 :=
    hL'.comp (f := fun s : ℂ => s ^ 2) hsq
  refine ⟨g, (analyticAt_id.pow k).mul
    ((Complex.differentiable_exp.analyticAt _).comp (hLc.div analyticAt_const (by norm_num))), ?_⟩
  filter_upwards [hp.eventually hfact, hp.eventually hLeq] with s hs hLs
  dsimp [g]
  rw [mul_pow, ← exp_nat_mul, Nat.cast_ofNat,
    show (2 : ℂ) * (L (s ^ 2) / 2) = L (s ^ 2) by ring, hLs]
  simpa only [sub_zero, smul_eq_mul, ← pow_mul, Nat.mul_comm k 2] using hs.symm

theorem exists_ramified_cosine_inverse {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ), cos (u s) = f (s ^ 2) := by
  obtain ⟨g, hg, hgsq⟩ := exists_ramified_square_root ((hf.pow 2).sub analyticAt_const
    : AnalyticAt ℂ (fun s => f s ^ 2 - 1) 0)
  let E := fun s : ℂ => f (s ^ 2) + g s
  have hsq : AnalyticAt ℂ (fun s : ℂ => s ^ 2) 0 := analyticAt_id.pow 2
  have hf' : AnalyticAt ℂ f ((0 : ℂ) ^ 2) := by simpa using hf
  have hf2 : AnalyticAt ℂ (fun s : ℂ => f (s ^ 2)) 0 :=
    hf'.comp (f := fun s : ℂ => s ^ 2) hsq
  have hE : AnalyticAt ℂ E 0 := hf2.add hg
  have heq : ∀ᶠ s in 𝓝 (0 : ℂ), E s ^ 2 - 2 * f (s ^ 2) * E s + 1 = 0 := by
    filter_upwards [hgsq] with s hs
    change g s ^ 2 = f (s ^ 2) ^ 2 - 1 at hs
    dsimp [E]
    linear_combination hs
  have hE0 : E 0 ≠ 0 := by
    intro hzero
    have h := heq.self_of_nhds
    simp [hzero] at h
  obtain ⟨L, hL, _, hLeq⟩ := CosinePoleUnit.exists_analytic_log hE hE0
  refine ⟨fun s => -I * L s, analyticAt_const.mul hL, ?_⟩
  filter_upwards [heq, hLeq, hE.continuousAt.eventually_ne hE0] with s hs hLs hEs
  have hexp : exp ((-I * L s) * I) = E s := by
    rw [show (-I * L s) * I = L s by linear_combination -(L s) * I_sq]
    exact hLs
  simpa only [one_pow, div_one] using CosinePoleUnit.cosine_of_unit_equation
    (m := 0) (s := 1) (U := -I * L s) (by norm_num) hEs (by simpa using hs)
    (by simpa only [one_pow, div_one] using hexp)

theorem nonconstant_ramified {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hnc : ∀ c : ℂ, ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = c) (N : ℕ) (hN : 0 < N) :
    ∀ c : ℂ, ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f (s ^ N) = c := by
  have hpow : AnalyticAt ℂ (fun s : ℂ => s ^ N) 0 := analyticAt_id.pow N
  have hp : Tendsto (fun s : ℂ => s ^ N) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa [Nat.ne_zero_of_lt hN] using
        hpow.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact pow_ne_zero N hs
  intro c hc
  have hn := (hf.eventually_eq_or_eventually_ne
    (show AnalyticAt ℂ (fun _ : ℂ => c) 0 from analyticAt_const)).resolve_left (hnc c)
  obtain ⟨s, hsne, hseq⟩ := ((hp.eventually hn).and (hc.filter_mono nhdsWithin_le_nhds)).exists
  exact hsne hseq

theorem exists_nonconstant_cosine_inverse {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hnc : ∀ c : ℂ, ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = c) :
    ∃ (u H : ℂ → ℂ) (k : ℕ), AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      0 < k ∧ (∀ᶠ s in 𝓝 (0 : ℂ), cos (u s) = f (s ^ 2)) ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), u s - u 0 = s ^ k * H s := by
  obtain ⟨u, hu, hcos⟩ := exists_ramified_cosine_inverse hf
  have hunc : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), u s - u 0 = 0 := by
    intro hc
    apply nonconstant_ramified hf hnc 2 (by omega) (cos (u 0))
    filter_upwards [hcos, hc] with s hs hc'
    rw [← hs, sub_eq_zero.mp hc']
  obtain ⟨k, H, hH, hH0, hfact⟩ :=
    (hu.sub analyticAt_const).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hunc
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hz := hfact.self_of_nhds
    have hz' : H 0 = 0 := by simpa [hk0] using hz.symm
    exact hH0 hz'
  refine ⟨u, H, k, hu, hH, hH0, hk, hcos, ?_⟩
  filter_upwards [hfact] with s hs
  simpa only [Pi.sub_apply, sub_zero, smul_eq_mul] using hs

end

end GaloisForLFunctions.HTGeometry.CosineRamifiedInverse
