import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Divisor
import GaloisForLFunctions.HTGeometry.SmallGrowthDerivative

/-!
# Total ramification and the order of the derivative

A value `a` is totally ramified for `f` when the derivative vanishes at every `a`-point.  For an
entire `f` this says exactly that every `a`-point is a zero of `f − a` of order at least two, and the
order of the derivative there is one less.  Consequently

```text
order_{z₀}(f − a) ≤ 2 · order_{z₀}(f'),
```

the pointwise divisor inequality behind `N(r, a) ≤ 2 N(r, 1/f')` — the step that turns Nevanlinna's
second main theorem into a bound on the number of totally ramified values.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Total ramification doubles the order.**  At an `a`-point of a totally ramified value the zero
of `f − a` has order `m ≥ 2` and `f'` vanishes to order `m − 1`. -/
theorem order_deriv_of_totallyRamified {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a z₀ : ℂ} (hram : ∀ z, f z = a → deriv f z = 0) (hz : f z₀ = a)
    {m : ℕ} (hm : analyticOrderAt (fun w => f w - a) z₀ = (m : ℕ∞)) :
    2 ≤ m ∧ analyticOrderAt (deriv f) z₀ = ((m - 1 : ℕ) : ℕ∞) := by
  have hg : AnalyticAt ℂ (fun w => f w - a) z₀ := (hf.analyticAt z₀).sub analyticAt_const
  have hgz : (fun w => f w - a) z₀ = 0 := by simp [hz]
  have hderivEq : deriv (fun w => f w - a) = deriv f := by
    funext w
    simp [deriv_sub_const]
  -- the order is at least one
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    have := (AnalyticAt.analyticOrderAt_eq_zero hg).mp (by exact_mod_cast hm)
    exact this hgz
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hord : analyticOrderAt (deriv (fun w => f w - a)) z₀ = (n : ℕ∞) :=
    analyticOrderAt_deriv_of_pos hg (by exact_mod_cast hm)
  rw [hderivEq] at hord
  -- the order of the derivative is not zero, since the derivative vanishes there
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hord
    have hdz : deriv f z₀ ≠ 0 :=
      (AnalyticAt.analyticOrderAt_eq_zero ((hf.deriv).analyticAt z₀)).mp (by exact_mod_cast hord)
    exact hdz (hram z₀ hz)
  refine ⟨by omega, ?_⟩
  have hsimp : (n + 1 - 1 : ℕ) = n := by omega
  rw [hsimp]
  exact hord

/-- **The pointwise divisor inequality.**  At an `a`-point of a totally ramified value, the order of
`f − a` is at most twice the order of `f'`. -/
theorem order_le_two_mul_order_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a z₀ : ℂ} (hram : ∀ z, f z = a → deriv f z = 0) (hz : f z₀ = a)
    {m k : ℕ} (hm : analyticOrderAt (fun w => f w - a) z₀ = (m : ℕ∞))
    (hk : analyticOrderAt (deriv f) z₀ = (k : ℕ∞)) : m ≤ 2 * k := by
  obtain ⟨hm2, hord⟩ := order_deriv_of_totallyRamified hf hram hz hm
  rw [hk] at hord
  have hkm : k = m - 1 := by exact_mod_cast hord
  omega


/-! ## From analytic orders to divisors -/

/-- For an entire function of finite order at every point, the divisor is the analytic order. -/
theorem divisor_eq_analyticOrder_toNat {g : ℂ → ℂ} (hg : ∀ z, AnalyticAt ℂ g z)
    (hne : ∀ z, meromorphicOrderAt g z ≠ ⊤) {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    MeromorphicOn.divisor g U u = (((analyticOrderAt g u).toNat : ℕ) : ℤ) := by
  have hU : MeromorphicOn g U := fun z _ => (hg z).meromorphicAt
  have hval := MeromorphicOn.divisor_apply hU hu
  have hmap : meromorphicOrderAt g u = ENat.map Nat.cast (analyticOrderAt g u) :=
    (hg u).meromorphicOrderAt_eq
  have hfin : analyticOrderAt g u ≠ ⊤ := by
    intro h
    apply hne u
    rw [hmap, h]
    rfl
  obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt g u = (n : ℕ∞) := by
    cases h : analyticOrderAt g u with
    | top => exact absurd h hfin
    | coe n => exact ⟨n, rfl⟩
  rw [hval, hmap, hn]
  simp

/-- **The pointwise divisor inequality for a totally ramified value.** -/
theorem divisor_sub_le_two_mul_divisor_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a : ℂ} (hram : ∀ z, f z = a → deriv f z = 0)
    (hfa : ∀ z, meromorphicOrderAt (fun w => f w - a) z ≠ ⊤)
    (hfd : ∀ z, meromorphicOrderAt (deriv f) z ≠ ⊤)
    {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    MeromorphicOn.divisor (fun w => f w - a) U u
      ≤ 2 * MeromorphicOn.divisor (deriv f) U u := by
  have hga : ∀ z : ℂ, AnalyticAt ℂ (fun w => f w - a) z :=
    fun z => (hf.analyticAt z).sub analyticAt_const
  have hgd : ∀ z : ℂ, AnalyticAt ℂ (deriv f) z := fun z => (hf.deriv).analyticAt z
  rw [divisor_eq_analyticOrder_toNat hga hfa hu, divisor_eq_analyticOrder_toNat hgd hfd hu]
  set m : ℕ := (analyticOrderAt (fun w => f w - a) u).toNat with hm
  set k : ℕ := (analyticOrderAt (deriv f) u).toNat with hk
  have hmord : analyticOrderAt (fun w => f w - a) u = (m : ℕ∞) := by
    have hfin : analyticOrderAt (fun w => f w - a) u ≠ ⊤ := by
      intro h
      apply hfa u
      rw [(hga u).meromorphicOrderAt_eq, h]
      rfl
    rw [hm]
    exact (ENat.coe_toNat hfin).symm
  have hkord : analyticOrderAt (deriv f) u = (k : ℕ∞) := by
    have hfin : analyticOrderAt (deriv f) u ≠ ⊤ := by
      intro h
      apply hfd u
      rw [(hgd u).meromorphicOrderAt_eq, h]
      rfl
    rw [hk]
    exact (ENat.coe_toNat hfin).symm
  by_cases hz : f u = a
  · have hle := order_le_two_mul_order_deriv hf hram hz hmord hkord
    exact_mod_cast hle
  · have hzero : m = 0 := by
      have hne : (fun w => f w - a) u ≠ 0 := by
        simp only [ne_eq, sub_eq_zero]
        exact hz
      have h0 : analyticOrderAt (fun w => f w - a) u = 0 :=
        (AnalyticAt.analyticOrderAt_eq_zero (hga u)).mpr hne
      rw [hm, h0]
      rfl
    rw [hzero]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    omega


/-- Away from an `a`-point the shifted divisor vanishes. -/
theorem divisor_sub_eq_zero_of_ne {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a u : ℂ}
    (hfa : ∀ z, meromorphicOrderAt (fun w => f w - a) z ≠ ⊤) {U : Set ℂ} (hu : u ∈ U)
    (hne : f u ≠ a) : MeromorphicOn.divisor (fun w => f w - a) U u = 0 := by
  have hga : ∀ z : ℂ, AnalyticAt ℂ (fun w => f w - a) z :=
    fun z => (hf.analyticAt z).sub analyticAt_const
  rw [divisor_eq_analyticOrder_toNat hga hfa hu]
  have hval : (fun w => f w - a) u ≠ 0 := by
    simp only [ne_eq, sub_eq_zero]
    exact hne
  have h0 : analyticOrderAt (fun w => f w - a) u = 0 :=
    (AnalyticAt.analyticOrderAt_eq_zero (hga u)).mpr hval
  rw [h0]
  rfl

/-- The divisor of the derivative of an entire function is nonnegative. -/
theorem divisor_deriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfd : ∀ z, meromorphicOrderAt (deriv f) z ≠ ⊤) {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    0 ≤ MeromorphicOn.divisor (deriv f) U u := by
  have hgd : ∀ z : ℂ, AnalyticAt ℂ (deriv f) z := fun z => (hf.deriv).analyticAt z
  rw [divisor_eq_analyticOrder_toNat hgd hfd hu]
  exact Int.natCast_nonneg _

/-- **The summed pointwise divisor inequality.**  For finitely many distinct totally ramified values
the shifted divisors together are dominated by twice the divisor of the derivative, because at any
point at most one of the values is attained. -/
theorem sum_divisor_sub_le_two_mul_divisor_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {q : ℕ} (A : Fin q → ℂ) (hinj : Function.Injective A)
    (hram : ∀ j, ∀ z, f z = A j → deriv f z = 0)
    (hfa : ∀ j, ∀ z, meromorphicOrderAt (fun w => f w - A j) z ≠ ⊤)
    (hfd : ∀ z, meromorphicOrderAt (deriv f) z ≠ ⊤)
    {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    (∑ j, MeromorphicOn.divisor (fun w => f w - A j) U u)
      ≤ 2 * MeromorphicOn.divisor (deriv f) U u := by
  classical
  by_cases hex : ∃ j : Fin q, f u = A j
  · obtain ⟨j₀, hj₀⟩ := hex
    have hother : ∀ j ∈ (Finset.univ : Finset (Fin q)), j ≠ j₀ →
        MeromorphicOn.divisor (fun w => f w - A j) U u = 0 := by
      intro j _ hj
      refine divisor_sub_eq_zero_of_ne hf (hfa j) hu ?_
      intro hval
      exact hj (hinj (by rw [← hval, hj₀]))
    rw [Finset.sum_eq_single j₀ hother (fun h => absurd (Finset.mem_univ j₀) h)]
    exact divisor_sub_le_two_mul_divisor_deriv hf (hram j₀) (hfa j₀) hfd hu
  · push_neg at hex
    have hzero : ∀ j ∈ (Finset.univ : Finset (Fin q)),
        MeromorphicOn.divisor (fun w => f w - A j) U u = 0 :=
      fun j _ => divisor_sub_eq_zero_of_ne hf (hfa j) hu (hex j)
    rw [Finset.sum_eq_zero hzero]
    have := divisor_deriv_nonneg hf hfd hu
    omega


/-! ## Integrating the divisor inequality -/

/-- **The counting inequality for totally ramified values.**  Integrating the summed pointwise
divisor inequality: the counting functions of finitely many distinct totally ramified values are
together at most twice the zero-counting function of the derivative. -/
theorem sum_logCounting_le_two_mul_logCounting_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {q : ℕ} (A : Fin q → ℂ) (hinj : Function.Injective A)
    (hram : ∀ j, ∀ z, f z = A j → deriv f z = 0)
    (hfa : ∀ j, ∀ z, meromorphicOrderAt (fun w => f w - A j) z ≠ ⊤)
    (hfd : ∀ z, meromorphicOrderAt (deriv f) z ≠ ⊤)
    {r : ℝ} (hr : 1 ≤ r) :
    (∑ j, Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor (fun w => f w - A j) Set.univ) r)
      ≤ 2 * Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor (deriv f) Set.univ) r := by
  classical
  set D : Fin q → Function.locallyFinsupp ℂ ℤ :=
    fun j => MeromorphicOn.divisor (fun w => f w - A j) Set.univ with hD
  set E : Function.locallyFinsupp ℂ ℤ := MeromorphicOn.divisor (deriv f) Set.univ with hE
  have hle : (∑ j, D j) ≤ (2 : ℕ) • E := by
    intro u
    have hsum : (∑ j, D j) u = ∑ j, (D j) u := by
      simp [hD]
    rw [hsum]
    have hpt := sum_divisor_sub_le_two_mul_divisor_deriv hf A hinj hram hfa hfd
      (U := Set.univ) (u := u) (Set.mem_univ u)
    have hsmul : ((2 : ℕ) • E) u = 2 * E u := by
      simp [two_smul, two_mul]
    rw [hsmul]
    exact hpt
  have hmono := smallGrowth_locallyFinsupp_logCounting_mono hle hr
  have hsumc : Function.locallyFinsuppWithin.logCounting (∑ j, D j) r
      = ∑ j, Function.locallyFinsuppWithin.logCounting (D j) r := by
    rw [map_sum, Finset.sum_apply]
  have hsmulc : Function.locallyFinsuppWithin.logCounting ((2 : ℕ) • E) r
      = 2 * Function.locallyFinsuppWithin.logCounting E r := by
    rw [map_nsmul]
    simp [two_smul, two_mul]
  rw [hsumc, hsmulc] at hmono
  exact hmono


/-- For an entire function of finite order everywhere the divisor is its own positive part. -/
theorem divisor_posPart_eq_self {g : ℂ → ℂ} (hg : ∀ z, AnalyticAt ℂ g z)
    (hne : ∀ z, meromorphicOrderAt g z ≠ ⊤) :
    (MeromorphicOn.divisor g Set.univ)⁺ = MeromorphicOn.divisor g Set.univ := by
  refine posPart_eq_self.mpr ?_
  intro u
  rw [divisor_eq_analyticOrder_toNat hg hne (Set.mem_univ u)]
  exact Int.natCast_nonneg _

/-- **The counting inequality in value-distribution form.**  Finitely many distinct totally ramified
values of an entire function have counting functions summing to at most twice the zero-counting
function of the derivative. -/
theorem sum_logCounting_value_le_two_mul_logCounting_deriv_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {q : ℕ} (A : Fin q → ℂ) (hinj : Function.Injective A)
    (hram : ∀ j, ∀ z, f z = A j → deriv f z = 0)
    (hfa : ∀ j, ∀ z, meromorphicOrderAt (fun w => f w - A j) z ≠ ⊤)
    (hfd : ∀ z, meromorphicOrderAt (deriv f) z ≠ ⊤)
    {r : ℝ} (hr : 1 ≤ r) :
    (∑ j, ValueDistribution.logCounting f (A j : WithTop ℂ) r)
      ≤ 2 * ValueDistribution.logCounting (deriv f) 0 r := by
  have hga : ∀ (j : Fin q) (z : ℂ), AnalyticAt ℂ (fun w => f w - A j) z :=
    fun j z => (hf.analyticAt z).sub analyticAt_const
  have hgd : ∀ z : ℂ, AnalyticAt ℂ (deriv f) z := fun z => (hf.deriv).analyticAt z
  have hval : ∀ j : Fin q, ValueDistribution.logCounting f (A j : WithTop ℂ) r
      = Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor (fun w => f w - A j) Set.univ) r := by
    intro j
    rw [ValueDistribution.logCounting_coe, divisor_posPart_eq_self (hga j) (hfa j)]
  have hderiv : ValueDistribution.logCounting (deriv f) 0 r
      = Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor (deriv f) Set.univ) r := by
    rw [ValueDistribution.logCounting_zero, divisor_posPart_eq_self hgd hfd]
  simp only [hval, hderiv]
  exact sum_logCounting_le_two_mul_logCounting_deriv hf A hinj hram hfa hfd hr

end GaloisForLFunctions.HTGeometry
