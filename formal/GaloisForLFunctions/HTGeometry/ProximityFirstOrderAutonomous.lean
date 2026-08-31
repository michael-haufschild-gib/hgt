import GaloisForLFunctions.HTGeometry.ProximityPolynomialComposition
import GaloisForLFunctions.HTGeometry.SecondMainTheoremChain

/-!
# The proximity inequality of an autonomous first-order equation

An entire solution of `F' = c(F)` with `c` a polynomial of degree `d` satisfies

```text
(d − 1) · m(r, F) ≤ m(r, F'/F) + O(1).
```

Both halves are elementary once the proximity of a polynomial composition is known: the left side is
`m(r, c ∘ F) = m(r, F')` from below, and the right side is `m(r, F·(F'/F))` split by
subadditivity of the proximity under products, valid off the codiscrete zero set of `F`.

For `d ≥ 2` the logarithmic-derivative estimate makes the right-hand side an error term, forcing `F`
to be a polynomial; and a polynomial cannot solve such an equation, because `deg F − 1 = d · deg F`
has no solution with `deg F ≥ 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial ValueDistribution Metric Filter

/-- For an entire `F` whose germ is nowhere identically zero on the circle,
`m(r, F') ≤ m(r, F) + m(r, F'/F)`. -/
theorem proximity_deriv_le_add_logDeriv {F : ℂ → ℂ} (hF : Differentiable ℂ F) {r : ℝ} (hr : r ≠ 0)
    (h₂ : ∀ u ∈ sphere (0 : ℂ) |r|, meromorphicOrderAt F u ≠ ⊤) :
    proximity (deriv F) ⊤ r
      ≤ proximity F ⊤ r + proximity (fun z => deriv F z / F z) ⊤ r := by
  have hmF : Meromorphic F := fun z => (hF.analyticAt z).meromorphicAt
  have hmF' : Meromorphic (deriv F) := fun z => ((hF.deriv).analyticAt z).meromorphicAt
  have hmOn : MeromorphicOn F (sphere (0 : ℂ) |r|) := fun z _ => hmF z
  have hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), F z ≠ 0 :=
    MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hmOn h₂
  have heq : deriv F =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
      F * fun z => deriv F z / F z := by
    filter_upwards [hcod] with z hz
    show deriv F z = F z * (deriv F z / F z)
    field_simp
  exact proximity_top_le_of_codiscrete_mul hr heq hmF (hmF'.div hmF)

/-- **The proximity inequality for an autonomous first-order equation.**  If `F' = c(F)` with `c` a
nonzero polynomial of degree `d`, then `(d − 1) m(r,F) ≤ m(r, F'/F) + C` with `C` independent of the
radius. -/
theorem exists_proximity_autonomous_bound {c : ℂ[X]} (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : ℂ → ℂ}, Differentiable ℂ F →
      (∀ z, deriv F z = c.eval (F z)) → ∀ {r : ℝ}, r ≠ 0 →
        (∀ u ∈ sphere (0 : ℂ) |r|, meromorphicOrderAt F u ≠ ⊤) →
        ((c.natDegree : ℝ) - 1) * proximity F ⊤ r
          ≤ proximity (fun z => deriv F z / F z) ⊤ r + C := by
  obtain ⟨C, hC0, hC⟩ := exists_le_proximity_comp_polynomial c hc
  refine ⟨C, hC0, ?_⟩
  intro F hF hrel r hr h₂
  have hcont : Continuous F := hF.continuous
  have hfun : (fun z => c.eval (F z)) = deriv F := by
    funext z
    exact (hrel z).symm
  have hlow := hC hcont r
  rw [hfun] at hlow
  have hup := proximity_deriv_le_add_logDeriv hF hr h₂
  have : (c.natDegree : ℝ) * proximity F ⊤ r - C
      ≤ proximity F ⊤ r + proximity (fun z => deriv F z / F z) ⊤ r := le_trans hlow hup
  linarith

/-- **A polynomial cannot solve an autonomous equation of degree at least two.**  Comparing degrees,
`deg q − 1 = deg c · deg q` is impossible unless `q` is constant. -/
theorem natDegree_eq_zero_of_derivative_eq_comp {q c : ℂ[X]} (hc : 2 ≤ c.natDegree)
    (h : derivative q = c.comp q) : q.natDegree = 0 := by
  by_contra hn
  have hn1 : 1 ≤ q.natDegree := Nat.one_le_iff_ne_zero.mpr hn
  have hcomp : (c.comp q).natDegree = c.natDegree * q.natDegree := Polynomial.natDegree_comp
  have hder : (derivative q).natDegree ≤ q.natDegree - 1 := Polynomial.natDegree_derivative_le q
  rw [h, hcomp] at hder
  have hmul : 2 * q.natDegree ≤ c.natDegree * q.natDegree :=
    Nat.mul_le_mul_right _ hc
  omega

end GaloisForLFunctions.HTGeometry
