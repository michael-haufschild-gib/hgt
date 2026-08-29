import GaloisForLFunctions.HTGeometry.TotallyRamifiedOrder
import GaloisForLFunctions.HTGeometry.ZeroFreeRadius

/-!
# Values of a composition are counted at least as often as the inner values

If `f b = a` and `g z = b`, then `z` is an `a`-point of `f ∘ g` of multiplicity at least that of the
`b`-point of `g`: factor `f w − a = (w − b)^k · h w` with `h b ≠ 0` and compose.

Summing over `n` distinct `f`-preimages of the same value `a`, whose `g`-divisors have disjoint
supports, gives

```text
N(r, a, f ∘ g) ≥ ∑_j N(r, b_j, g).
```
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn Function
open scoped Topology

/-- **Composition multiplies value multiplicities.**  A `b`-point of `g` is an `a`-point of `f ∘ g`
of at least the same multiplicity. -/
theorem analyticOrderAt_le_comp {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {a b : ℂ} (hfb : f b = a) {z : ℂ} (hgz : g z = b) :
    analyticOrderAt (fun w => g w - b) z ≤ analyticOrderAt (fun w => f (g w) - a) z := by
  classical
  have hgt : Filter.Tendsto g (𝓝 z) (𝓝 b) := by
    have h : Filter.Tendsto g (𝓝 z) (𝓝 (g z)) := (hg z).continuousAt
    rwa [hgz] at h
  have hFan : AnalyticAt ℂ (fun w => f w - a) b := (hf.analyticAt b).sub analyticAt_const
  have hFb : (fun w => f w - a) b = 0 := by simp [hfb]
  by_cases htop : analyticOrderAt (fun w => f w - a) b = ⊤
  · rw [analyticOrderAt_eq_top] at htop
    have hcomp : ∀ᶠ w in 𝓝 z, f (g w) - a = 0 := hgt.eventually htop
    rw [analyticOrderAt_eq_top.mpr hcomp]
    exact le_top
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (fun w => f w - a) b = (k : ℕ∞) := by
      cases h : analyticOrderAt (fun w => f w - a) b with
      | top => exact absurd h htop
      | coe k => exact ⟨k, rfl⟩
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        rw [h] at hk
        rcases analyticOrderAt_eq_zero.mp (by exact_mod_cast hk) with h' | h'
        · exact h' hFan
        · exact h' hFb
      · exact h
    obtain ⟨h, hhan, hhb, hfac⟩ := (hFan.analyticOrderAt_eq_natCast (n := k)).mp hk
    have hcomp : (fun w => f (g w) - a)
        =ᶠ[𝓝 z] ((fun w => g w - b) ^ k) * (fun w => h (g w)) := by
      filter_upwards [hgt.eventually hfac] with w hw
      simp only [Pi.mul_apply, Pi.pow_apply, smul_eq_mul] at hw ⊢
      exact hw
    have hgb : AnalyticAt ℂ (fun w => g w - b) z := (hg.analyticAt z).sub analyticAt_const
    have hhg : AnalyticAt ℂ (fun w => h (g w)) z := by
      have hhz : AnalyticAt ℂ h (g z) := by rwa [hgz]
      exact hhz.comp (hg.analyticAt z)
    have hordh : analyticOrderAt (fun w => h (g w)) z = 0 := by
      refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
      rw [hgz]
      exact hhb
    rw [analyticOrderAt_congr hcomp, analyticOrderAt_mul (hgb.pow k) hhg,
      analyticOrderAt_pow hgb k, hordh, add_zero, nsmul_eq_mul]
    exact le_mul_of_one_le_left zero_le (by exact_mod_cast hk1)

/-- **The counting bridge for a composition.**  With `A` an injective family of `f`-preimages of
`a`, the `a`-counting function of `f ∘ g` dominates the sum of the counting functions of `g` at the
values `A j`. -/
theorem sum_logCounting_le_logCounting_comp {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {a : ℂ} {q : ℕ} (A : Fin q → ℂ) (hAinj : Function.Injective A)
    (hA : ∀ j, f (A j) = a)
    (hgo : ∀ j : Fin q, ∀ z, meromorphicOrderAt (fun w => g w - A j) z ≠ ⊤)
    (hco : ∀ z, meromorphicOrderAt (fun w => f (g w) - a) z ≠ ⊤)
    {r : ℝ} (hr : 1 ≤ r) :
    (∑ j, ValueDistribution.logCounting g (A j : WithTop ℂ) r)
      ≤ ValueDistribution.logCounting (fun w => f (g w)) (a : WithTop ℂ) r := by
  classical
  have hcomp : Differentiable ℂ fun w => f (g w) := fun z => (hf (g z)).comp z (hg z)
  set D : ℂ → Function.locallyFinsupp ℂ ℤ :=
    fun b => (divisor (fun w => g w - b) Set.univ)⁺ with hD
  set E : Function.locallyFinsupp ℂ ℤ := (divisor (fun w => f (g w) - a) Set.univ)⁺ with hE
  have hgdiff : ∀ b : ℂ, Differentiable ℂ fun w => g w - b :=
    fun b => hg.sub (differentiable_const _)
  have hcdiff : Differentiable ℂ fun w => f (g w) - a := hcomp.sub (differentiable_const _)
  have hdivnn : ∀ F : ℂ → ℂ, Differentiable ℂ F → (∀ z, meromorphicOrderAt F z ≠ ⊤) →
      ∀ z, (0 : ℤ) ≤ divisor F Set.univ z := by
    intro F hF hFo z
    rw [divisor_eq_analyticOrder_toNat (fun w => hF.analyticAt w) hFo (Set.mem_univ z)]
    exact_mod_cast Nat.zero_le _
  have hle : (∑ j, D (A j)) ≤ E := by
    intro z
    have hEz : (0 : ℤ) ≤ E z := le_max_right _ _
    have hsum : (∑ j, D (A j)) z = ∑ j, (D (A j)) z := by
      simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [hsum]
    by_cases hex : ∃ j : Fin q, g z = A j
    · obtain ⟨j₀, hj₀⟩ := hex
      have hsingle : ∑ j, (D (A j)) z = (D (A j₀)) z := by
        refine Finset.sum_eq_single j₀ ?_ (fun hcon => absurd (Finset.mem_univ j₀) hcon)
        intro j _ hjne
        have hgz : g z - A j ≠ 0 := by
          rw [sub_ne_zero, hj₀]
          exact fun hcon => hjne (hAinj hcon.symm)
        have h0 : divisor (fun w => g w - A j) Set.univ z = 0 :=
          divisor_eq_zero_of_ne_zero (hgdiff (A j)) (hgo j) (Set.mem_univ z) hgz
        show max (divisor (fun w => g w - A j) Set.univ z) 0 = 0
        rw [h0]
        rfl
      rw [hsingle]
      have hDb : (D (A j₀)) z = divisor (fun w => g w - A j₀) Set.univ z := by
        show max (divisor (fun w => g w - A j₀) Set.univ z) 0 = _
        exact max_eq_left (hdivnn _ (hgdiff (A j₀)) (hgo j₀) z)
      have hEeq : E z = divisor (fun w => f (g w) - a) Set.univ z := by
        show max (divisor (fun w => f (g w) - a) Set.univ z) 0 = _
        exact max_eq_left (hdivnn _ hcdiff hco z)
      rw [hDb, hEeq]
      rw [divisor_eq_analyticOrder_toNat (fun w => (hgdiff (A j₀)).analyticAt w) (hgo j₀)
          (Set.mem_univ z),
        divisor_eq_analyticOrder_toNat (fun w => hcdiff.analyticAt w) hco (Set.mem_univ z)]
      have hord := analyticOrderAt_le_comp hf hg (hA j₀) hj₀
      have hfin2 : analyticOrderAt (fun w => f (g w) - a) z ≠ ⊤ := by
        intro hcon
        exact hco z (by rw [(hcdiff.analyticAt z).meromorphicOrderAt_eq, hcon]; rfl)
      exact Int.ofNat_le.mpr (ENat.toNat_le_toNat hord hfin2)
    · push_neg at hex
      refine le_trans (le_of_eq ?_) hEz
      refine Finset.sum_eq_zero ?_
      intro j _
      have hgz : g z - A j ≠ 0 := sub_ne_zero.mpr (hex j)
      have h0 : divisor (fun w => g w - A j) Set.univ z = 0 :=
        divisor_eq_zero_of_ne_zero (hgdiff (A j)) (hgo j) (Set.mem_univ z) hgz
      show max (divisor (fun w => g w - A j) Set.univ z) 0 = 0
      rw [h0]
      rfl
  have hcount := Function.locallyFinsuppWithin.logCounting_le hle hr
  have hleft : Function.locallyFinsuppWithin.logCounting (∑ j, D (A j)) r
      = ∑ j, ValueDistribution.logCounting g (A j : WithTop ℂ) r := by
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [hD, ValueDistribution.logCounting]
  have hright : Function.locallyFinsuppWithin.logCounting E r
      = ValueDistribution.logCounting (fun w => f (g w)) (a : WithTop ℂ) r := by
    simp [hE, ValueDistribution.logCounting]
  rw [hleft, hright] at hcount
  exact hcount

end GaloisForLFunctions.HTGeometry
