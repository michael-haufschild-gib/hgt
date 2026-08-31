import GaloisForLFunctions.HTGeometry.JensenProximityReciprocal
import GaloisForLFunctions.HTGeometry.ProximityFirstOrderAutonomous
import GaloisForLFunctions.HTGeometry.SecondMainTheoremEntire
import GaloisForLFunctions.HTGeometry.AlgebraicProximityBound
import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic

/-!
# The second main theorem for a function omitting two values

For an entire `F` omitting two values with a nowhere-vanishing derivative both counting terms of the
second main theorem vanish, and the ramification term `m(r, 1/F')` is discharged by Jensen rather
than by a ramification count: `F'` is zero-free, so `m(r,1/F') = m(r,F') − log‖F'(0)‖`, and
`m(r,F') ≤ m(r,F) + m(r,F'/F)`.  Since `m(r,F) = T(r,F)` for an entire function, one power of the
characteristic cancels and

```text
T(r,F) ≤ m(r, F'/(F−a₁)) + m(r, F'/(F−a₂)) + m(r, F'/F) + O(1).
```

Each term on the right is an `S(r,F)`, so the inequality reads `T ≤ S` — the contradiction that
forbids a nonconstant entire solution of `F' = c(F)` from omitting two roots of `c`.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Filter

/-- An entire function that omits a value has no counting function there. -/
theorem logCounting_eq_zero_of_omits {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℂ}
    (hne : ∀ z, f z ≠ a) : ValueDistribution.logCounting f (a : WithTop ℂ) = 0 := by
  rw [ValueDistribution.logCounting_coe]
  have hmero : MeromorphicOn (fun x => f x - a) Set.univ :=
    fun w _ => (((hf.sub_const a)).analyticAt w).meromorphicAt
  have hdiv : MeromorphicOn.divisor (fun x => f x - a) Set.univ = 0 := by
    ext z
    rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ z)]
    have hA : AnalyticAt ℂ (fun x => f x - a) z := (hf.sub_const a).analyticAt z
    have hz : (fun x => f x - a) z ≠ 0 := sub_ne_zero.mpr (hne z)
    rw [hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_zero.mpr hz]
    simp
  rw [hdiv]
  simp

/-- An entire function with a nowhere-vanishing derivative is not identically zero near any
point. -/
theorem meromorphicOrderAt_ne_top_of_deriv_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF' : ∀ z, deriv F z ≠ 0) (u : ℂ) : meromorphicOrderAt F u ≠ ⊤ := by
  intro htop
  have hA : AnalyticAt ℂ F u := hF.analyticAt u
  rw [hA.meromorphicOrderAt_eq] at htop
  have hord : analyticOrderAt F u = ⊤ := by
    by_contra hc
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hc
    rw [← hn] at htop
    exact absurd htop (by exact_mod_cast WithTop.coe_ne_top)
  have hnhds : F =ᶠ[nhds u] 0 := analyticOrderAt_eq_top.mp hord
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hall := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ u) hnhds
  have hFzero : F = fun _ => (0 : ℂ) := by
    funext z
    exact hall (Set.mem_univ z)
  have : deriv F 0 = 0 := by rw [hFzero]; simp
  exact hF' 0 this

/-- **The second main theorem for a function omitting two values with a zero-free derivative.**
Both counting terms vanish, and the ramification term is discharged by Jensen, leaving the
characteristic bounded by three logarithmic-derivative proximities. -/
theorem characteristic_le_of_omits_two {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂)
    (hF' : ∀ z, deriv F z ≠ 0) {r K : ℝ} (hr : r ≠ 0)
    (hfmt : ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + K) :
    characteristic F ⊤ r
      ≤ proximity (fun z => deriv F z / (F z - a₁)) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₂)) ⊤ r
        + proximity (fun z => deriv F z / F z) ⊤ r
        + ((2 * K + 2 * Real.posLog (2 / ‖a₁ - a₂‖)
            + Real.posLog (2 * (2 / ‖a₁ - a₂‖)) + Real.log 2 + Real.log 2)
          - Real.log ‖deriv F 0‖) := by
  classical
  have hδ : 0 < ‖a₁ - a₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hane)
  have hsep : ∀ i j : Fin 2, i ≠ j → ‖a₁ - a₂‖ ≤ ‖(![a₁, a₂] i) - (![a₁, a₂] j)‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [norm_sub_rev]
  have hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv F z ≠ 0 :=
    Filter.Eventually.of_forall hF'
  have hsmt := mul_characteristic_le_of_separated_entire (f := F) ![a₁, a₂] hδ hr hsep hF hfmt hcod
  -- the counting terms vanish
  have hcount : ∑ j : Fin 2, logCounting F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r = 0 := by
    have hz1 : logCounting F ((a₁ : ℂ) : WithTop ℂ) r = 0 := by
      rw [logCounting_eq_zero_of_omits hF h₁]; rfl
    have hz2 : logCounting F ((a₂ : ℂ) : WithTop ℂ) r = 0 := by
      rw [logCounting_eq_zero_of_omits hF h₂]; rfl
    rw [Fin.sum_univ_two]
    show logCounting F ((a₁ : ℂ) : WithTop ℂ) r + logCounting F ((a₂ : ℂ) : WithTop ℂ) r = 0
    rw [hz1, hz2, add_zero]
  -- the proximity sum
  have hprox : ∑ j : Fin 2, proximity (fun z => deriv F z / (F z - ![a₁, a₂] j)) ⊤ r
      = proximity (fun z => deriv F z / (F z - a₁)) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₂)) ⊤ r := by
    rw [Fin.sum_univ_two]
    rfl
  -- the ramification term
  have hderivdiff : Differentiable ℂ (deriv F) := hF.deriv
  have hram : proximity (fun z => (deriv F z)⁻¹) ⊤ r
      = proximity (deriv F) ⊤ r - Real.log ‖deriv F 0‖ :=
    proximity_inv_eq_sub hderivdiff hF' hr
  have hsplit : proximity (deriv F) ⊤ r
      ≤ proximity F ⊤ r + proximity (fun z => deriv F z / F z) ⊤ r :=
    proximity_deriv_le_add_logDeriv hF hr
      (fun u _ => meromorphicOrderAt_ne_top_of_deriv_ne_zero hF hF' u)
  have hchar : proximity F ⊤ r = characteristic F ⊤ r := by
    rw [characteristic_top_eq_proximity_of_analyticOnNhd (fun z _ => hF.analyticAt z)]
  rw [hcount, hprox, hram, zero_add] at hsmt
  push_cast at hsmt
  linarith [hsmt, hsplit, hchar]

/-- **The omitting second main theorem with every denominator zero-free.**  Splitting
`F' = (F − a₁)·(F'/(F − a₁))` rather than `F·(F'/F)` keeps every logarithmic derivative taken at an
omitted value, so every divisor in the logarithmic-derivative estimate vanishes. -/
theorem characteristic_le_of_omits_two_shifted {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂)
    (hF' : ∀ z, deriv F z ≠ 0) {r K : ℝ} (hr : r ≠ 0)
    (hfmt : ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + K) :
    characteristic F ⊤ r
      ≤ 2 * proximity (fun z => deriv F z / (F z - a₁)) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₂)) ⊤ r
        + ((2 * K + 2 * Real.posLog (2 / ‖a₁ - a₂‖)
            + Real.posLog (2 * (2 / ‖a₁ - a₂‖)) + Real.log 2 + Real.log 2)
          - Real.log ‖deriv F 0‖ + (Real.posLog ‖a₁‖ + Real.log 2)) := by
  classical
  have hδ : 0 < ‖a₁ - a₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hane)
  have hsep : ∀ i j : Fin 2, i ≠ j → ‖a₁ - a₂‖ ≤ ‖(![a₁, a₂] i) - (![a₁, a₂] j)‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [norm_sub_rev]
  have hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv F z ≠ 0 :=
    Filter.Eventually.of_forall hF'
  have hsmt := mul_characteristic_le_of_separated_entire (f := F) ![a₁, a₂] hδ hr hsep hF hfmt hcod
  have hcount : ∑ j : Fin 2, logCounting F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r = 0 := by
    have hz1 : logCounting F ((a₁ : ℂ) : WithTop ℂ) r = 0 := by
      rw [logCounting_eq_zero_of_omits hF h₁]; rfl
    have hz2 : logCounting F ((a₂ : ℂ) : WithTop ℂ) r = 0 := by
      rw [logCounting_eq_zero_of_omits hF h₂]; rfl
    rw [Fin.sum_univ_two]
    show logCounting F ((a₁ : ℂ) : WithTop ℂ) r + logCounting F ((a₂ : ℂ) : WithTop ℂ) r = 0
    rw [hz1, hz2, add_zero]
  have hprox : ∑ j : Fin 2, proximity (fun z => deriv F z / (F z - ![a₁, a₂] j)) ⊤ r
      = proximity (fun z => deriv F z / (F z - a₁)) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₂)) ⊤ r := by
    rw [Fin.sum_univ_two]
    rfl
  have hderivdiff : Differentiable ℂ (deriv F) := hF.deriv
  have hram : proximity (fun z => (deriv F z)⁻¹) ⊤ r
      = proximity (deriv F) ⊤ r - Real.log ‖deriv F 0‖ :=
    proximity_inv_eq_sub hderivdiff hF' hr
  -- split the derivative against the shifted function
  have hshiftne : ∀ z, F z - a₁ ≠ 0 := fun z h => h₁ z (by linear_combination h)
  have hmshift : Meromorphic (fun z => F z - a₁) :=
    fun z => (((hF.sub_const a₁)).analyticAt z).meromorphicAt
  have hmquot : Meromorphic (fun z => deriv F z / (F z - a₁)) :=
    fun z => ((hderivdiff.analyticAt z).meromorphicAt).div (hmshift z)
  have heqfac : deriv F =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
      (fun z => F z - a₁) * fun z => deriv F z / (F z - a₁) := by
    filter_upwards with z
    show deriv F z = (F z - a₁) * (deriv F z / (F z - a₁))
    field_simp
    rw [mul_div_assoc, div_self (hshiftne z), mul_one]
  have hsplit : proximity (deriv F) ⊤ r
      ≤ proximity (fun z => F z - a₁) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₁)) ⊤ r :=
    proximity_top_le_of_codiscrete_mul hr heqfac hmshift hmquot
  -- the shift costs a constant
  have hAF : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hAc : AnalyticOnNhd ℂ (fun _ : ℂ => -a₁) Set.univ := fun z _ => analyticAt_const
  have hAs : AnalyticOnNhd ℂ (fun z => F z - a₁) Set.univ :=
    fun z _ => ((hF.sub_const a₁)).analyticAt z
  have hshiftle : proximity (fun z => F z - a₁) ⊤ r
      ≤ proximity F ⊤ r + (Real.posLog ‖a₁‖ + Real.log 2) := by
    have hadd := GaloisForLFunctions.Nevanlinna.characteristic_add_le hAF hAc r
    have hconst := GaloisForLFunctions.Nevanlinna.characteristic_const_eq (-a₁) r
    have hfun : (fun z => F z + -a₁) = fun z => F z - a₁ := by funext z; ring
    rw [hfun, hconst, norm_neg] at hadd
    rw [← GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd hAs,
      ← GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd hAF]
    linarith
  have hchar : proximity F ⊤ r = characteristic F ⊤ r := by
    rw [characteristic_top_eq_proximity_of_analyticOnNhd hAF]
  rw [hcount, hprox, hram, zero_add] at hsmt
  push_cast at hsmt
  linarith [hsmt, hsplit, hshiftle, hchar]

end GaloisForLFunctions.HTGeometry
