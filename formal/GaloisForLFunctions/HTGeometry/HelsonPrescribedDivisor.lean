import GaloisForLFunctions.HTGeometry.PrescribedDivisorRealization
import GaloisForLFunctions.HTGeometry.HelsonZetaAnalytic

/-!
# Divisor surjectivity of the Helson continuation stratum, reduced to Andersson's factorization

Andersson's Theorem 2 (arXiv:2408.15713) says that a function analytic and zero free on
`Re s > 1`, whose logarithmic derivative extends continuously to `Re s ≥ 1`, factors as a Helson
zeta function times an entire zero-free function.  This module records that property as
`HelsonFactorizationProperty` and derives from it the divisor statement the seam card consumes:

```text
every locally finite signed divisor supported in Re s < 1 is the divisor of the meromorphic
continuation of some Helson zeta function.
```

The consumer end is unconditional: the realization of an arbitrary divisor by a quotient of
Weierstrass products is already formal in `PrescribedDivisorRealization`, the resulting function is
analytic and zero free on the closed half plane `Re s ≥ 1` because the divisor lives strictly to the
left of it, and dividing by the entire zero-free factor changes no order.  So the only remaining
content of the divisor half of the card is Andersson's factorization itself.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- **Andersson's Helson factorization property** (arXiv:2408.15713, Theorem 2): a function
analytic and zero free on a neighbourhood of the closed half plane `Re s ≥ 1` is a Helson zeta
function times an entire zero-free function, on `Re s > 1`. -/
def HelsonFactorizationProperty : Prop :=
  ∀ F : ℂ → ℂ, (∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ F z) → (∀ z : ℂ, 1 ≤ z.re → F z ≠ 0) →
    ∃ (χ : PhaseTorus) (g : ℂ → ℂ), Differentiable ℂ g ∧ (∀ z : ℂ, g z ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → F s = helsonZetaValue s χ * g s

/-- The realized divisor function is analytic and nonvanishing on the closed half plane, when the
divisor lives strictly to the left of it. -/
theorem divisorFunction_analyticAt_of_re_le {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hbre : ∀ n, (b n).re < 1) {z : ℂ} (hz : 1 ≤ z.re) :
    AnalyticAt ℂ (divisorFunction a b) z := by
  have hden : GaloisForLFunctions.weierstrassGenusProduct b z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (GaloisForLFunctions.weierstrassGenusProduct_eq_zero_iff hb hbne z).mp h
    have := hbre n
    rw [← hn] at this
    linarith
  exact ((GaloisForLFunctions.differentiable_weierstrassGenusProduct ha hane).analyticAt z).div
    ((GaloisForLFunctions.differentiable_weierstrassGenusProduct hb hbne).analyticAt z) hden

theorem divisorFunction_ne_zero_of_re_le {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) {z : ℂ} (hz : 1 ≤ z.re) :
    divisorFunction a b z ≠ 0 := by
  have hnum : GaloisForLFunctions.weierstrassGenusProduct a z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (GaloisForLFunctions.weierstrassGenusProduct_eq_zero_iff ha hane z).mp h
    have := hare n
    rw [← hn] at this
    linarith
  have hden : GaloisForLFunctions.weierstrassGenusProduct b z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (GaloisForLFunctions.weierstrassGenusProduct_eq_zero_iff hb hbne z).mp h
    have := hbre n
    rw [← hn] at this
    linarith
  rw [GaloisForLFunctions.divisorFunction]
  exact div_ne_zero hnum hden

/-- Implementation of divisor surjectivity from Andersson's factorization input. -/
private theorem exists_continuable_phase_with_prescribed_divisor_of_factorization
    (hA : HelsonFactorizationProperty) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) :
    ∃ χ : PhaseTorus, χ ∈ continuableStratum ∧
      ∃ F : ℂ → ℂ, MeromorphicOn F Set.univ ∧
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (F s)) ∧
        ∀ z : ℂ, meromorphicOrderAt F z
          = meromorphicOrderAt (GaloisForLFunctions.divisorFunction a b) z := by
  classical
  obtain ⟨χ, g, hgdiff, hgne, hfact⟩ := hA (GaloisForLFunctions.divisorFunction a b)
    (fun z hz => divisorFunction_analyticAt_of_re_le ha hane hb hbne hbre hz)
    (fun z hz => divisorFunction_ne_zero_of_re_le ha hane hb hbne hare hbre hz)
  refine ⟨χ, ?_, fun s => GaloisForLFunctions.divisorFunction a b s / g s, ?_, ?_, ?_⟩
  · refine ⟨fun s => GaloisForLFunctions.divisorFunction a b s / g s, ?_, ?_⟩
    · intro z _
      exact ((GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z
        (Set.mem_univ z)).div ((hgdiff.analyticAt z).meromorphicAt)
    · intro s hs
      have hval : GaloisForLFunctions.divisorFunction a b s / g s = helsonZetaValue s χ := by
        rw [hfact s hs, mul_div_assoc, div_self (hgne s), mul_one]
      show HasProd _ (GaloisForLFunctions.divisorFunction a b s / g s)
      rw [hval]
      exact (multipliable_helsonEuler (fun p => le_of_eq (χ p).2) hs).hasProd
  · intro z _
    exact ((GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z
      (Set.mem_univ z)).div ((hgdiff.analyticAt z).meromorphicAt)
  · intro s hs
    have hval : GaloisForLFunctions.divisorFunction a b s / g s = helsonZetaValue s χ := by
      rw [hfact s hs, mul_div_assoc, div_self (hgne s), mul_one]
    show HasProd _ (GaloisForLFunctions.divisorFunction a b s / g s)
    rw [hval]
    exact (multipliable_helsonEuler (fun p => le_of_eq (χ p).2) hs).hasProd
  · intro z
    have hgorder : meromorphicOrderAt g z = 0 := by
      rw [(hgdiff.analyticAt z).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr (hgne z))]
      rfl
    have hdiv := meromorphicOrderAt_div
      ((GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z (Set.mem_univ z))
      ((hgdiff.analyticAt z).meromorphicAt)
    have hfun : (fun s => GaloisForLFunctions.divisorFunction a b s / g s)
        = GaloisForLFunctions.divisorFunction a b / g := rfl
    rw [hfun, hdiv, hgorder, sub_zero]

/-- **Exact Andersson absorption law.**  Adjoining the complete prescribed-divisor realization to
the factorization property does not strengthen it.  The theorem is closed while retaining the
entire conditional divisor-surjectivity content. -/
theorem helsonFactorizationProperty_iff_and_exists_continuable_phase_with_prescribed_divisor
    {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) :
    HelsonFactorizationProperty ↔
      HelsonFactorizationProperty ∧
        ∃ χ : PhaseTorus, χ ∈ continuableStratum ∧
          ∃ F : ℂ → ℂ, MeromorphicOn F Set.univ ∧
            (∀ s : ℂ, 1 < s.re →
              HasProd
                (fun p : Nat.Primes =>
                  (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
                (F s)) ∧
            ∀ z : ℂ, meromorphicOrderAt F z =
              meromorphicOrderAt (GaloisForLFunctions.divisorFunction a b) z := by
  constructor
  · intro hA
    exact ⟨hA,
      exists_continuable_phase_with_prescribed_divisor_of_factorization
        hA ha hane hb hbne hare hbre⟩
  · exact And.left

end GaloisForLFunctions.HTGeometry

end
