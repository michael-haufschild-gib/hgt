import GaloisForLFunctions.RHTower.HigherPoleResidueMode
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiDivisorContour
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.WideZeroLocations

/-! Laurent residues of the truncated Perron integrand at the origin, the principal pole, and the zeros. -/

open Complex DirichletCharacter Filter Topology
open GaloisForLFunctions.HTGeometry

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

/-- The integrand for the ordinary, unsmoothed Chebyshev sum. -/
def primitivePerronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (u : ℝ) (s : ℂ) : ℂ := -logDeriv χ.LFunction s * (u : ℂ) ^ s / s

private theorem analyticAt_perron_power {u : ℝ} (hu : 0 < u) (p : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) p :=
  analyticAt_const.cpow analyticAt_id (ofReal_mem_slitPlane.mpr hu)

theorem analyticAt_primitivePerronIntegrand {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {u : ℝ} (hu : 0 < u) {s : ℂ}
    (h₀ : s ≠ 0) (h₁ : s ≠ 1) (hL : χ.LFunction s ≠ 0) :
    AnalyticAt ℂ (primitivePerronIntegrand χ u) s := by
  have hA : AnalyticAt ℂ χ.LFunction s :=
    analyticAt_iff_eventually_differentiableAt.mpr
      ((eventually_ne_nhds h₁).mono fun p hp => differentiableAt_LFunction χ p (.inl hp))
  exact (((hA.deriv.div hA hL).neg.mul (analyticAt_perron_power hu s)).div analyticAt_id h₀)

private theorem simple_perron_residue {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {u : ℝ} (hu : 0 < u) {p k : ℂ} (hp : p ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p)
    (h : logDeriv χ.LFunction =ᶠ[𝓝[≠] p] fun s => k / (s - p) + g s) :
    MeromorphicAt (primitivePerronIntegrand χ u) p ∧
      laurentCoeff (primitivePerronIntegrand χ u) p (-1) = -(k * ((u : ℂ) ^ p / p)) := by
  let A (s : ℂ) : ℂ := -(k + (s - p) * g s) * ((u : ℂ) ^ s / s)
  have ha : AnalyticAt ℂ A p := ((analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hg)).neg).mul
    ((analyticAt_perron_power hu p).div analyticAt_id hp)
  have e : primitivePerronIntegrand χ u =ᶠ[𝓝[≠] p] fun s => A s / (s - p) := by
    filter_upwards [h, self_mem_nhdsWithin, (eventually_ne_nhds hp).filter_mono nhdsWithin_le_nhds]
      with s hs (hn : s ≠ p) h₀
    have hsp := sub_ne_zero.mpr hn
    dsimp only [primitivePerronIntegrand, A]
    rw [hs]
    field_simp [hsp, h₀]
  have hm := (ha.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt).congr e.symm
  refine ⟨hm, (laurentCoeff_congr hm e (-1)).trans ?_⟩
  rw [laurentCoeff_analytic_div_sub ha]
  simp [A]

theorem perron_origin_residue {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {u : ℝ} (hu : 0 < u) {m : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (h : logDeriv χ.LFunction =ᶠ[𝓝[≠] (0 : ℂ)] fun s => (m : ℂ) / s + g s) :
    MeromorphicAt (primitivePerronIntegrand χ u) 0 ∧
      laurentCoeff (primitivePerronIntegrand χ u) 0 (-1) = -((m : ℂ) * (Real.log u : ℂ) + g 0) := by
  let A (s : ℂ) : ℂ := -((m : ℂ) + s * g s) * (u : ℂ) ^ s
  have ha : AnalyticAt ℂ A 0 := ((analyticAt_const.add (analyticAt_id.mul hg)).neg).mul
    (analyticAt_perron_power hu 0)
  have e : primitivePerronIntegrand χ u =ᶠ[𝓝[≠] (0 : ℂ)] fun s => (s ^ 2)⁻¹ * A s := by
    filter_upwards [h, self_mem_nhdsWithin] with s hs (hn : s ≠ 0)
    dsimp only [primitivePerronIntegrand, A]
    rw [hs]
    field_simp [hn] <;> ring
  have hId : AnalyticAt ℂ (id : ℂ → ℂ) 0 := analyticAt_id
  have hm : MeromorphicAt (primitivePerronIntegrand χ u) 0 :=
    ((hId.pow 2).meromorphicAt.inv.mul ha.meromorphicAt).congr e.symm
  refine ⟨hm, (laurentCoeff_congr hm e (-1)).trans ?_⟩
  have h := RHTower.laurentCoeff_inv_pow_mul_analytic ha (show 1 ≤ (2 : ℕ) by decide)
  simp only [sub_zero, zero_add, Nat.reduceSub, taylorCoeffZero, iteratedDeriv_one, Nat.factorial_one,
    Nat.cast_one, div_one] at h
  rw [h]
  have hu₀ : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hpow : HasDerivAt (fun s : ℂ => (u : ℂ) ^ s) (Real.log u : ℂ) 0 := by
    simpa only [cpow_zero, one_mul, ofReal_log hu.le] using
      (hasStrictDerivAt_const_cpow (x := (u : ℂ)) (y := 0) (.inl hu₀)).hasDerivAt
  have hA : HasDerivAt A _ 0 :=
    (((hasDerivAt_id (0 : ℂ)).fun_mul hg.differentiableAt.hasDerivAt).const_add (m : ℂ)).neg.fun_mul hpow
  change deriv A 0 = _
  rw [hA.deriv]
  simp only [Pi.neg_apply, id_eq, one_mul, zero_mul, add_zero, cpow_zero, mul_one]
  ring

private theorem logDeriv_pole_correction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {p : ℂ} (h₁ : p ≠ 1) :
    AnalyticAt ℂ (fun s : ℂ => if χ = 1 then 1 / (s - 1) else 0) p := by
  split_ifs
  · exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr h₁)
  · exact analyticAt_const

theorem perron_one_residue {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {u : ℝ} (hu : 0 < u) :
    MeromorphicAt (primitivePerronIntegrand χ u) 1 ∧
      laurentCoeff (primitivePerronIntegrand χ u) 1 (-1) = if χ = 1 then (u : ℂ) else 0 := by
  let f := entireCharacterL χ
  have ha := (differentiable_entireCharacterL χ).analyticAt 1
  have hne : f 1 ≠ 0 := entireCharacterL_ne_zero_of_one_le_re (by simp)
  have hg : AnalyticAt ℂ (logDeriv f) 1 := ha.deriv.div ha hne
  let k : ℂ := if χ = 1 then -1 else 0
  have e : logDeriv χ.LFunction =ᶠ[𝓝[≠] (1 : ℂ)] fun s => k / (s - 1) + logDeriv f s := by
    filter_upwards [self_mem_nhdsWithin, ha.continuousAt.eventually_ne hne |>.filter_mono nhdsWithin_le_nhds]
      with s (hs : s ≠ 1) hz
    rw [logDeriv_entireCharacterL hs (fun e => hz ((entireCharacterL_eq_zero_iff hs).2 e))]
    dsimp only [k]
    split_ifs <;> ring
  obtain ⟨hm, hr⟩ := simple_perron_residue hu one_ne_zero hg e
  refine ⟨hm, hr.trans ?_⟩
  simp only [k, cpow_one, div_one]
  split_ifs <;> simp

theorem perron_zero_residue {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {u : ℝ} (hu : 0 < u) {ρ : ℂ} (h₀ : ρ ≠ 0) (h₁ : ρ ≠ 1) :
    MeromorphicAt (primitivePerronIntegrand χ u) ρ ∧
      laurentCoeff (primitivePerronIntegrand χ u) ρ (-1) =
        -((analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) := by
  let f := entireCharacterL χ
  have ha := (differentiable_entireCharacterL χ).analyticAt
  have ht : analyticOrderAt f ρ ≠ ⊤ := entireCharacterL_order_ne_top
  obtain ⟨g, hg, he⟩ := RiemannGaussian.AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic (ha ρ) ht
  let P (s : ℂ) : ℂ := if χ = 1 then 1 / (s - 1) else 0
  have hP : AnalyticAt ℂ P ρ := logDeriv_pole_correction χ h₁
  refine simple_perron_residue hu h₀ (hg.sub hP) ?_
  have hn : ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 :=
    (ha ρ).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun e => ht (analyticOrderAt_eq_top.mpr e)
  filter_upwards [he, hn, (eventually_ne_nhds h₁).filter_mono nhdsWithin_le_nhds] with s hs hf hne
  change logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + g s at hs
  rw [logDeriv_entireCharacterL hne (fun e => hf ((entireCharacterL_eq_zero_iff hne).2 e)),
    analyticOrderNatAt_entireCharacterL h₁] at hs
  change logDeriv χ.LFunction s + P s = _ at hs
  change logDeriv χ.LFunction s =
    (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ) + (g s - P s)
  linear_combination hs

end QH.PrimeProgressions
