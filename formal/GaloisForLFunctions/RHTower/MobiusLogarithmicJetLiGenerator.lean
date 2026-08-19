import GaloisForLFunctions.RHTower.XiLogDerivNotHolonomic
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing

/-!
# The Möbius logarithmic jet and the Li generator

`mobius-logarithmic-jet-ht-transfer-li-no-holonomic-route.md`.

For a Möbius change `r` and a nonzero meromorphic `F`, the Möbius logarithmic jet is

```text
J_r(F)(z) = r'(z) F'(r(z)) / F(r(z)) = logDeriv (F ∘ r) (z) ,
```

by the chain rule.  With Riemann's `r(z) = 1/(1-z)` and `F = xi`, `J_r(xi)` is the Keiper--Li
generating function `sum_n lambda_n z^{n-1}`.

Since `xi ∘ r` is analytic near every preimage of a `xi` zero and vanishes there, the corpus
logarithmic-derivative residue engine applies verbatim: every iterated derivative of `J_r(xi)` has a
pole of exact order `j+1` with nonvanishing leading coefficient at each such preimage.  Given the
classical infinitude of nontrivial zeros, `J_r(xi)` therefore satisfies **no** linear differential
equation with polynomial coefficients — the Li sequence is not `P`-recursive.
-/

open Complex Filter Finset Topology GaloisForLFunctions

noncomputable section
namespace RHTower

/-! ### The Möbius chart and its logarithmic jet -/

/-- Riemann's Li chart `r(z) = 1/(1-z)`. -/
def liChart (z : ℂ) : ℂ := 1 / (1 - z)

/-- Its inverse `q(w) = 1 - 1/w`. -/
def liChartInv (w : ℂ) : ℂ := 1 - 1 / w

theorem liChart_liChartInv {w : ℂ} (hw : w ≠ 0) : liChart (liChartInv w) = w := by
  rw [liChart, liChartInv]
  field_simp
  ring

theorem liChartInv_liChart {z : ℂ} (hz : z ≠ 1) : liChartInv (liChart z) = z := by
  have h : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [liChartInv, liChart]
  field_simp
  ring

theorem liChartInv_injective : Function.Injective liChartInv := by
  intro a b hab
  rw [liChartInv, liChartInv] at hab
  have h : (1 : ℂ) / a = 1 / b := by linear_combination -hab
  rw [one_div, one_div] at h
  exact inv_injective h

theorem analyticAt_liChart {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ liChart z := by
  have h : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  exact (analyticAt_const.div ((analyticAt_const).sub analyticAt_id) h)

theorem liChart_ne_one_of_ne_zero {w : ℂ} (hw : w ≠ 0) : liChartInv w ≠ 1 := by
  intro h
  rw [liChartInv] at h
  have : (1 : ℂ) / w = 0 := by linear_combination -h
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · exact one_ne_zero h1
  · exact hw h1

/-- The Keiper--Li generating function, as the logarithmic derivative of the charted `xi`. -/
def liGenerator (z : ℂ) : ℂ := logDeriv (fun w : ℂ => xi (liChart w)) z

/-- **The Möbius logarithmic jet identity.**  `J_r(xi) = r' · (xi'/xi) ∘ r`. -/
theorem liGenerator_eq_jet {z : ℂ} (hz : z ≠ 1) (hxi : xi (liChart z) ≠ 0) :
    liGenerator z = (1 - z) ^ (-2 : ℤ) * xiLogDeriv (liChart z) := by
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hr : HasDerivAt liChart ((1 - z) ^ (-2 : ℤ)) z := by
    have hden : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
    have h := (hasDerivAt_const z (1 : ℂ)).div hden h1
    simp only [zero_mul, one_mul, zero_sub] at h
    have hval : -(-1 : ℂ) / (1 - z) ^ 2 = (1 - z) ^ (-2 : ℤ) := by
      rw [zpow_neg, zpow_ofNat]
      field_simp
    rw [← hval]
    exact h
  have hxiA : AnalyticAt ℂ xi (liChart z) := xi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hcomp : HasDerivAt (fun w : ℂ => xi (liChart w))
      (deriv xi (liChart z) * (1 - z) ^ (-2 : ℤ)) z :=
    (hxiA.differentiableAt.hasDerivAt).comp z hr
  rw [liGenerator, logDeriv_apply, hcomp.deriv, xiLogDeriv]
  field_simp

/-! ### Non-holonomicity of the Li generator -/

/-- The charted `xi` is analytic away from the pole of the chart. -/
theorem analyticAt_xi_comp_liChart {z : ℂ} (hz : z ≠ 1) :
    AnalyticAt ℂ (fun w : ℂ => xi (liChart w)) z := by
  have h := (xi_analyticOnNhd_univ (liChart z) (Set.mem_univ _)).comp (analyticAt_liChart hz)
  exact h

/-- The charted `xi` is not identically zero near any chart preimage. -/
theorem analyticOrderAt_xi_comp_liChart_ne_top {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (fun v : ℂ => xi (liChart v)) (liChartInv w) ≠ ⊤ := by
  intro htop
  have hev := analyticOrderAt_eq_top.mp htop
  have hq : Tendsto liChartInv (nhds w) (nhds (liChartInv w)) := by
    have hcont : ContinuousAt liChartInv w := by
      have : ContinuousAt (fun v : ℂ => 1 - 1 / v) w :=
        continuousAt_const.sub (continuousAt_const.div continuousAt_id hw)
      exact this
    exact hcont.tendsto
  have hxi0 : ∀ᶠ v : ℂ in nhds w, xi (liChart (liChartInv v)) = 0 := hq.eventually hev
  have hxi : ∀ᶠ v : ℂ in nhds w, xi v = 0 := by
    filter_upwards [hxi0, isOpen_compl_singleton.mem_nhds (by
      simpa using hw : w ∈ ({0} : Set ℂ)ᶜ)] with v h1 h2
    have hv : v ≠ 0 := by simpa using h2
    rwa [liChart_liChartInv hv] at h1
  exact xi_order_ne_top w (analyticOrderAt_eq_top.mpr hxi)

/-- **The Li generator is not holonomic.**  Given any injective sequence of nonzero `xi` zeros, the
Keiper--Li generating function satisfies no linear differential equation with polynomial
coefficients; equivalently, the Li sequence is not `P`-recursive. -/
theorem liGenerator_not_holonomic (ρ : ℕ → ℂ) (hinj : Function.Injective ρ)
    (hne : ∀ k, ρ k ≠ 0) (hz : ∀ k, xi (ρ k) = 0) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
      (∀ z : ℂ, ∑ j ∈ range (n + 1), (c j).eval z * iteratedDeriv j liGenerator z = 0) →
      ∀ j ∈ range (n + 1), c j = 0 := by
  set p : ℕ → ℂ := fun k => liChartInv (ρ k) with hp_def
  have hpinj : Function.Injective p := liChartInv_injective.comp hinj
  have hpne : ∀ k, p k ≠ 1 := fun k => liChart_ne_one_of_ne_zero (hne k)
  have hzero : ∀ k, (fun w : ℂ => xi (liChart w)) (p k) = 0 := by
    intro k
    simp only [hp_def]
    rw [liChart_liChartInv (hne k)]
    exact hz k
  refine not_holonomic_master liGenerator p hpinj 1
    (fun i k => ((analyticOrderAt (fun w : ℂ => xi (liChart w)) (p k)).toNat : ℂ) *
      ((-1) ^ i * (i.factorial : ℂ)))
    (fun i k => ?_) (fun i k => ?_)
  · have hm1 : 1 ≤ (analyticOrderAt (fun w : ℂ => xi (liChart w)) (p k)).toNat := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have hzeroOrd : analyticOrderAt (fun w : ℂ => xi (liChart w)) (p k) = 0 := by
        rw [(ENat.coe_toNat (analyticOrderAt_xi_comp_liChart_ne_top (hne k))).symm, h0]
        rfl
      rcases analyticOrderAt_eq_zero.mp hzeroOrd with h | h
      · exact h (analyticAt_xi_comp_liChart (hpne k))
      · exact h (hzero k)
    have hmne : ((analyticOrderAt (fun w : ℂ => xi (liChart w)) (p k)).toNat : ℂ) ≠ 0 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hm1
    exact mul_ne_zero hmne
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast i.factorial_ne_zero))
  · exact logDeriv_iteratedDeriv_residue_of_zero
      (analyticAt_xi_comp_liChart (hpne k))
      (analyticOrderAt_xi_comp_liChart_ne_top (hne k)) (hzero k) i


/-! ### The unconditional form -/

theorem xi_zeroSet_infinite : {z : ℂ | xi z = 0}.Infinite := by
  have hset : {z : ℂ | xi z = 0} = {z : ℂ | riemannXi z = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, xi_eq_riemannXi]
  rw [hset]
  exact riemannXi_zeroSet_infinite

theorem xi_zero_ne_zero : xi 0 ≠ 0 := by
  rw [xi_eq_riemannXi, riemannXi_zero]
  norm_num

/-- **The Li generator is unconditionally not holonomic.**  Riemann's `xi` has infinitely many
zeros, all nonzero, so the Keiper--Li generating function satisfies no linear differential equation
with polynomial coefficients: the Li sequence is not `P`-recursive. -/
theorem liGenerator_not_holonomic_unconditional :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
      (∀ z : ℂ, ∑ j ∈ range (n + 1), (c j).eval z * iteratedDeriv j liGenerator z = 0) →
      ∀ j ∈ range (n + 1), c j = 0 := by
  obtain e := xi_zeroSet_infinite.natEmbedding
  refine liGenerator_not_holonomic (fun k => (e k : ℂ)) ?_ ?_ ?_
  · intro a b hab
    exact e.injective (Subtype.ext hab)
  · intro k h0
    have hk : xi ((e k : ℂ)) = 0 := (e k).2
    rw [h0] at hk
    exact xi_zero_ne_zero hk
  · intro k
    exact (e k).2

end RHTower

