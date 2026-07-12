import GaloisForLFunctions.CompositionResidueLaw
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Reciprocal-Gamma pole branches

This file constructs the analytic local inverse of reciprocal Gamma at every
negative integer and proves that finite shifts of these inverse branches are
conjugated by the ascending-factorial value relation.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

/-- Reciprocal Gamma has derivative `(-1)^k k!` at its zero `-k`. -/
theorem hasDerivAt_oneDivGamma_neg_nat (k : ℕ) :
    HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹)
      ((-1 : ℂ) ^ k * (k.factorial : ℂ)) (-(k : ℂ)) := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hr : ((-1 : ℂ) ^ k / (k.factorial : ℂ)) ≠ 0 :=
    div_ne_zero (pow_ne_zero k (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
  have h := (gamma_residue k).inv₀ hr
  have hlim : ((-1 : ℂ) ^ k / (k.factorial : ℂ))⁻¹ =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) := by
    rw [inv_div]
    field_simp
    rw [← pow_mul]
    simp
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  rw [slope_def_field, Complex.Gamma_neg_nat_eq_zero, inv_zero, sub_zero]
  have hsub : z - -(k : ℂ) = z + (k : ℂ) := by ring
  rw [hsub, mul_inv_rev, div_eq_mul_inv]

/-- An analytic local inverse branch of reciprocal Gamma based at its zero `-k`,
parameterized so that `1 / Gamma (z x) = -x`. -/
structure ReciprocalGammaPoleBranch (k : ℕ) where
  toFun : ℂ → ℂ
  analyticAt_zero : AnalyticAt ℂ toFun 0
  map_zero : toFun 0 = -(k : ℂ)
  right_inverse :
    (fun x : ℂ => (Complex.Gamma (toFun x))⁻¹) =ᶠ[𝓝 0] (fun x => -x)
  left_inverse :
    (fun w : ℂ => toFun (-((Complex.Gamma w)⁻¹))) =ᶠ[𝓝 (-(k : ℂ))] id
  hasDerivAt_zero :
    HasDerivAt toFun (-((-1 : ℂ) ^ k / (k.factorial : ℂ))) 0

instance (k : ℕ) : CoeFun (ReciprocalGammaPoleBranch k) (fun _ => ℂ → ℂ) :=
  ⟨ReciprocalGammaPoleBranch.toFun⟩

/-- Every negative-integer zero of reciprocal Gamma has a normalized analytic inverse branch. -/
theorem reciprocalGammaPoleBranch_nonempty (k : ℕ) :
    Nonempty (ReciprocalGammaPoleBranch k) := by
  let H : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹
  let a : ℂ := -(k : ℂ)
  let d : ℂ := (-1 : ℂ) ^ k * (k.factorial : ℂ)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact mul_ne_zero (pow_ne_zero k (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero k)
  have hHder : HasDerivAt H d a := by
    simpa [H, d, a] using hasDerivAt_oneDivGamma_neg_nat k
  have hHan : AnalyticAt ℂ H a := by
    exact (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ)
      a (Set.mem_univ a)
  have hD : deriv H a = d := hHder.deriv
  have hDne : deriv H a ≠ 0 := hD.symm ▸ hd
  have hstrict : HasStrictDerivAt H (deriv H a) a := hHan.hasStrictDerivAt
  let g : ℂ → ℂ := hstrict.localInverse H (deriv H a) a hDne
  let z : ℂ → ℂ := fun x => g (-x)
  have hHa : H a = 0 := by
    simp [H, a, Complex.Gamma_neg_nat_eq_zero]
  have hgan : AnalyticAt ℂ g 0 := by
    have h := hHan.analyticAt_localInverse hDne
    rwa [hHa] at h
  have hzan : AnalyticAt ℂ z 0 := by
    have hinner : AnalyticAt ℂ (fun x : ℂ => -x) 0 := by fun_prop
    have hgan' : AnalyticAt ℂ g ((fun x : ℂ => -x) 0) := by simpa using hgan
    simpa [z, Function.comp_def] using hgan'.comp hinner
  have hga : g 0 = a := by
    have h := hstrict.eventually_left_inverse hDne |>.self_of_nhds
    simpa [g, hHa] using h
  have hright : (fun y => H (g y)) =ᶠ[𝓝 0] id := by
    have h := hstrict.eventually_right_inverse hDne
    rwa [hHa] at h
  have hleft : (fun w => g (H w)) =ᶠ[𝓝 a] id :=
    hstrict.eventually_left_inverse hDne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa using (continuousAt_id.neg : ContinuousAt (fun x : ℂ => -x) 0).tendsto
  have hzright : (fun x => H (z x)) =ᶠ[𝓝 0] (fun x => -x) := by
    filter_upwards [hneg.eventually hright] with x hx
    simpa [z] using hx
  have hgder : HasDerivAt g d⁻¹ 0 := by
    have h : HasDerivAt g (deriv H a)⁻¹ 0 := by
      simpa [g, hHa] using (hstrict.to_localInverse hDne).hasDerivAt
    convert h using 1
    rw [hD]
  have hzder : HasDerivAt z (d⁻¹ * (-1 : ℂ)) 0 := by
    have hminus : HasDerivAt (fun x : ℂ => -x) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).neg
    have hgder' : HasDerivAt g d⁻¹ ((fun x : ℂ => -x) 0) := by simpa using hgder
    simpa [z, Function.comp_def] using hgder'.comp 0 hminus
  refine ⟨⟨z, hzan, ?_, ?_, ?_, ?_⟩⟩
  · simp [z, hga, a]
  · simpa [H] using hzright
  · filter_upwards [hleft] with w hw
    simpa [z, H, a] using hw
  · convert hzder using 1
    dsimp [d]
    field_simp
    rw [← pow_mul]
    simp

private theorem ascPochhammer_eval_neg_nat_ne_zero {n k : ℕ} (hk : k ≤ n) :
    (ascPochhammer ℂ k).eval (-(n : ℂ)) ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro j hj heq
  have hjne : j ≠ n := by omega
  apply hjne
  have heq' : (j : ℂ) = (n : ℂ) := by simpa using heq
  exact_mod_cast heq'

/-- **Finite reciprocal-Gamma branch conjugacy.**  If `k ≤ n`, shifting the branch based at
`-n` by `k` conjugates its inverse-value parameter by the rising-factorial value:

`z_(n-k) (x / (z_n(x))_k) = z_n(x) + k`

for all `x` sufficiently close to zero. -/
theorem ReciprocalGammaPoleBranch.finite_cocycle
    {n k : ℕ} (hk : k ≤ n)
    (zn : ReciprocalGammaPoleBranch n)
    (zt : ReciprocalGammaPoleBranch (n - k)) :
    (fun x : ℂ => zt (x / (ascPochhammer ℂ k).eval (zn x))) =ᶠ[𝓝 0]
      (fun x => zn x + (k : ℂ)) := by
  let P : ℂ → ℂ := fun x => (ascPochhammer ℂ k).eval (zn x)
  have hP0 : P 0 ≠ 0 := by
    simpa [P, zn.map_zero] using ascPochhammer_eval_neg_nat_ne_zero hk
  have hPcont : ContinuousAt P 0 := by
    exact (ascPochhammer ℂ k).continuousAt.comp zn.analyticAt_zero.continuousAt
  have hPne : ∀ᶠ x in 𝓝 0, P x ≠ 0 := hPcont.eventually_ne hP0
  have hzncont : Tendsto zn (𝓝 0) (𝓝 (-(n : ℂ))) := by
    rw [← zn.map_zero]
    exact zn.analyticAt_zero.continuousAt
  have hy : Tendsto (fun x : ℂ => x / P x) (𝓝 0) (𝓝 0) := by
    convert tendsto_id.div hPcont.tendsto hP0 using 1
    simp [P]
  have htarget : -(n : ℂ) + (k : ℂ) = -((n - k : ℕ) : ℂ) := by
    rw [Nat.cast_sub hk]
    ring
  have hw : Tendsto (fun x : ℂ => zn x + (k : ℂ)) (𝓝 0)
      (𝓝 (-((n - k : ℕ) : ℂ))) := by
    rw [← htarget]
    exact hzncont.add_const (k : ℂ)
  have hleft := hw.eventually zt.left_inverse
  have hright := zn.right_inverse
  filter_upwards [hPne, hleft, hright] with x hPx hleftx hrightx
  have hpoles : ∀ j < k, zn x + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    apply hPx
    change (ascPochhammer ℂ k).eval (zn x) = 0
    rw [ascPochhammer_eval_eq_zero_iff]
    exact ⟨j, hj, by
      linear_combination hzero⟩
  have hGamma := Complex.Gamma_add_nat_eq_ascPochhammer_mul (zn x) k hpoles
  have hHshift : (Complex.Gamma (zn x + (k : ℂ)))⁻¹ = -(x / P x) := by
    rw [hGamma, mul_inv_rev, hrightx]
    simp only [P]
    field_simp [hPx]
  have h := hleftx
  rw [hHshift] at h
  simpa using h

/-- The one-step reciprocal-Gamma branch conjugacy
`z_n (x / z_(n+1)(x)) = z_(n+1)(x) + 1`. -/
theorem ReciprocalGammaPoleBranch.one_step_cocycle
    {n : ℕ}
    (zn : ReciprocalGammaPoleBranch (n + 1))
    (zt : ReciprocalGammaPoleBranch n) :
    (fun x : ℂ => zt (x / zn x)) =ᶠ[𝓝 0] (fun x => zn x + 1) := by
  simpa using zn.finite_cocycle (n := n + 1) (k := 1) (by omega) zt

end GaloisForLFunctions
