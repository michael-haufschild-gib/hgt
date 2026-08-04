import GaloisForLFunctions.HTGeometry.SecondMainTheoremSeparation
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
# Assembling the second main theorem

The separation estimate turns the sum of proximities to several values into a single proximity term.
The first main theorem replaces each value-characteristic by the characteristic at infinity.  What
comes out is the second main theorem with the single term `m(r, ∑ (f - a_j)⁻¹)` still to be
estimated — and that term is where the logarithmic-derivative estimate enters.

The first main theorem is taken as an explicit hypothesis rather than invoked, so the statement is
unconditional and the caller can supply mathlib's quantitative version.
-/

open Metric ValueDistribution Filter

namespace GaloisForLFunctions.HTGeometry

/-- The characteristic splits into proximity and counting. -/
theorem characteristic_apply (f : ℂ → ℂ) (a : WithTop ℂ) (r : ℝ) :
    characteristic f a r = proximity f a r + logCounting f a r := rfl

/-- **The second main theorem, up to the residual proximity term.**  With `K` bounding the
first-main-theorem defect at each value,

  `q · T(r,f) ≤ ∑_j N(r, a_j) + m(r, ∑_j (f - a_j)⁻¹) + (qK + separation constant)`.

The residual proximity term is what the logarithmic-derivative estimate bounds by `S(r,f)`. -/
theorem mul_characteristic_le_sum_logCounting_add_proximity
    {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {δ r K : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hmero : ∀ j : Fin q, MeromorphicOn (fun z => (f z - A j)⁻¹) (sphere (0 : ℂ) |r|))
    (hfmt : ∀ j : Fin q, characteristic f ⊤ r ≤ characteristic f (A j : WithTop ℂ) r + K) :
    (q : ℝ) * characteristic f ⊤ r
      ≤ (∑ j, logCounting f (A j : WithTop ℂ) r)
        + proximity (fun z => ∑ j, (f z - A j)⁻¹) ⊤ r
        + ((q : ℝ) * K + (q : ℝ) * Real.posLog (2 / δ)
            + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2) := by
  classical
  have hsep' := sum_proximity_le_of_meromorphic A hδ hsep hmero
  -- sum the first main theorem over the values
  have hsumfmt : (q : ℝ) * characteristic f ⊤ r
      ≤ ∑ j, (characteristic f (A j : WithTop ℂ) r + K) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => hfmt j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  have hexpand : ∑ j, (characteristic f (A j : WithTop ℂ) r + K)
      = (∑ j, proximity f (A j : WithTop ℂ) r)
        + (∑ j, logCounting f (A j : WithTop ℂ) r) + (q : ℝ) * K := by
    have h₁ : ∀ j : Fin q, characteristic f (A j : WithTop ℂ) r + K
        = proximity f (A j : WithTop ℂ) r + logCounting f (A j : WithTop ℂ) r + K := by
      intro j
      rw [characteristic_apply]
    simp only [h₁]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hexpand] at hsumfmt
  linarith

/-! ## Moving the residual term

The residual proximity term factors as `∑ (f - a_j)⁻¹ = (∑ f'/(f - a_j)) · (1/f')`, but only away
from the critical points of `f`, where the junk value `0⁻¹ = 0` breaks the identity.  Proximity is a
circle average, so it only sees the identity up to a codiscrete set — which is exactly the tolerance
`proximity_congr_codiscreteWithin` provides. -/

/-- **Proximity of a product, up to a codiscrete set.** -/
theorem proximity_top_le_of_codiscrete_mul {F G H : ℂ → ℂ} {r : ℝ} (hr : r ≠ 0)
    (heq : F =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] G * H)
    (hG : Meromorphic G) (hH : Meromorphic H) :
    proximity F ⊤ r ≤ proximity G ⊤ r + proximity H ⊤ r := by
  rw [proximity_congr_codiscreteWithin heq hr]
  exact proximity_mul_top_le hG hH r

/-- **Proximity of a sum, up to a codiscrete set.** -/
theorem proximity_top_sum_le_of_codiscrete {F : ℂ → ℂ} {q : ℕ} {G : Fin q → ℂ → ℂ} {r : ℝ}
    (hr : r ≠ 0)
    (heq : F =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] ∑ j, G j)
    (hG : ∀ j : Fin q, Meromorphic (G j)) :
    proximity F ⊤ r ≤ (∑ j, proximity (G j) ⊤ r) + Real.log (q : ℝ) := by
  rw [proximity_congr_codiscreteWithin heq hr]
  have h := proximity_sum_top_le (Finset.univ : Finset (Fin q)) G (fun j _ => hG j) r
  simpa [Finset.card_univ] using h

/-! ## The residual factorization -/

/-- **The residual identity, away from the critical points.**  Where `f' ≠ 0`,
`∑ (f - a_j)⁻¹ = (∑ f'/(f - a_j))·(1/f')`.  No condition on `f - a_j` is needed: both sides vanish
where it does. -/
theorem sum_inv_eq_mul_of_deriv_ne {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {z : ℂ}
    (hz : deriv f z ≠ 0) :
    (∑ j, (f z - A j)⁻¹) = (∑ j, deriv f z / (f z - A j)) * (deriv f z)⁻¹ := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  field_simp

/-- The residual identity holds codiscretely as soon as the critical points are codiscretely
avoided. -/
theorem sum_inv_eventuallyEq_mul {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {r : ℝ}
    (hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0) :
    (fun z => ∑ j, (f z - A j)⁻¹)
      =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
        (fun z => ∑ j, deriv f z / (f z - A j)) * fun z => (deriv f z)⁻¹ := by
  filter_upwards [hcod] with z hz
  exact sum_inv_eq_mul_of_deriv_ne A hz

/-- The critical points are codiscretely avoided when `f'` is meromorphic and nowhere locally
zero. -/
theorem eventually_deriv_ne_zero {f : ℂ → ℂ} {r : ℝ}
    (h₁ : MeromorphicOn (deriv f) (sphere (0 : ℂ) |r|))
    (h₂ : ∀ u ∈ sphere (0 : ℂ) |r|, meromorphicOrderAt (deriv f) u ≠ ⊤) :
    ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0 :=
  MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero h₁ h₂

/-- **The residual proximity term, split.**  `m(r, ∑ (f - a_j)⁻¹)` is bounded by the sum of the
proximities of the logarithmic derivatives `f'/(f - a_j)`, plus `log q`, plus the ramification term
`m(r, 1/f')`. -/
theorem proximity_sum_inv_le {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {r : ℝ} (hr : r ≠ 0)
    (hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0)
    (hG : Meromorphic (fun z => ∑ j, deriv f z / (f z - A j)))
    (hH : Meromorphic (fun z => (deriv f z)⁻¹))
    (hGj : ∀ j : Fin q, Meromorphic (fun z => deriv f z / (f z - A j))) :
    proximity (fun z => ∑ j, (f z - A j)⁻¹) ⊤ r
      ≤ (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r) + Real.log (q : ℝ)
        + proximity (fun z => (deriv f z)⁻¹) ⊤ r := by
  have hstep₁ := proximity_top_le_of_codiscrete_mul hr (sum_inv_eventuallyEq_mul A hcod) hG hH
  have heq2 : (fun z : ℂ => ∑ j, deriv f z / (f z - A j))
      =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] ∑ j, fun z : ℂ => deriv f z / (f z - A j) := by
    filter_upwards with z
    simp [Finset.sum_apply]
  have hstep₂ := proximity_top_sum_le_of_codiscrete hr heq2 hGj
  linarith

/-! ## The assembled inequality -/

/-- The proximity at infinity of a logarithmic derivative is the circle average the estimate of
`LogDerivativeProximity` bounds. -/
theorem proximity_top_logDeriv_eq {f : ℂ → ℂ} {a : ℂ} {r : ℝ} :
    proximity (fun z => deriv f z / (f z - a)) ⊤ r
      = Real.circleAverage (fun z => Real.posLog ‖deriv f z / (f z - a)‖) 0 r := by
  rw [proximity_top]

/-- **The second main theorem.**  For pairwise separated values,

  `q·T(r,f) ≤ ∑_j N(r, a_j) + ∑_j m(r, f'/(f − a_j)) + m(r, 1/f') + constants`.

The middle group is bounded by the logarithmic-derivative estimate and the last term is the
ramification term.  The first main theorem enters only through the hypothesis `hfmt`. -/
theorem mul_characteristic_le_of_separated
    {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {δ r K : ℝ} (hδ : 0 < δ) (hr : r ≠ 0)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hmero : ∀ j : Fin q, MeromorphicOn (fun z => (f z - A j)⁻¹) (sphere (0 : ℂ) |r|))
    (hfmt : ∀ j : Fin q, characteristic f ⊤ r ≤ characteristic f (A j : WithTop ℂ) r + K)
    (hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0)
    (hG : Meromorphic (fun z => ∑ j, deriv f z / (f z - A j)))
    (hH : Meromorphic (fun z => (deriv f z)⁻¹))
    (hGj : ∀ j : Fin q, Meromorphic (fun z => deriv f z / (f z - A j))) :
    (q : ℝ) * characteristic f ⊤ r
      ≤ (∑ j, logCounting f (A j : WithTop ℂ) r)
        + (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r)
        + proximity (fun z => (deriv f z)⁻¹) ⊤ r
        + ((q : ℝ) * K + (q : ℝ) * Real.posLog (2 / δ)
            + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2 + Real.log (q : ℝ)) := by
  have h₁ := mul_characteristic_le_sum_logCounting_add_proximity A hδ hsep hmero hfmt
  have h₂ := proximity_sum_inv_le A hr hcod hG hH hGj
  linarith

/-! ## Discharging the first-main-theorem hypothesis -/

/-- The value characteristic is the characteristic of the shift at zero. -/
theorem characteristic_coe_eq (f : ℂ → ℂ) (a₀ : ℂ) :
    characteristic f (a₀ : WithTop ℂ) = characteristic (f - fun _ => a₀) 0 := by
  rw [characteristic, characteristic, proximity_coe_eq_proximity_sub_const_zero,
    logCounting_coe_eq_logCounting_sub_const_zero]

/-- The characteristic at zero is the characteristic of the reciprocal at infinity. -/
theorem characteristic_zero_eq_inv_top (g : ℂ → ℂ) :
    characteristic g 0 = characteristic g⁻¹ ⊤ := by
  rw [characteristic, characteristic, proximity_inv, logCounting_inv]

/-- **The first-main-theorem defect at a finite value.**  Combining the two quantitative halves of
the first main theorem: the shift `f ↦ f - a₀` and the inversion. -/
theorem characteristic_top_le_characteristic_coe {f : ℂ → ℂ} {a₀ : ℂ} {r : ℝ}
    (hf : Meromorphic f) (hg : Meromorphic (f - fun _ => a₀)) :
    characteristic f ⊤ r
      ≤ characteristic f (a₀ : WithTop ℂ) r
        + ((Real.posLog ‖a₀‖ + Real.log 2)
          + max |Real.log ‖((f - fun _ : ℂ => a₀) : ℂ → ℂ) 0‖|
              |Real.log ‖meromorphicTrailingCoeffAt ((f - fun _ : ℂ => a₀) : ℂ → ℂ) 0‖|) := by
  have hshift := abs_characteristic_sub_characteristic_shift_le (f := f) (a₀ := a₀) (r := r) hf
  have hinv := characteristic_sub_characteristic_inv_le (f := f - fun _ => a₀) (R := r) hg
  have hfun : (fun z => f z - a₀) = (f - fun _ => a₀) := rfl
  rw [hfun] at hshift
  have hval : characteristic f (a₀ : WithTop ℂ) r = characteristic (f - fun _ => a₀)⁻¹ ⊤ r := by
    rw [characteristic_coe_eq, characteristic_zero_eq_inv_top]
  rw [hval]
  have h₁ := (abs_le.mp hshift).1
  have h₂ := (abs_le.mp hshift).2
  have h₃ := (abs_le.mp hinv).1
  have h₄ := (abs_le.mp hinv).2
  linarith

/-! ## At least one value is taken often -/

/-- **Pigeonhole on the second main theorem.**  If `q·T(r,f) ≤ ∑_j N(r, a_j) + S`, then some value
is attained with counting function at least `T(r,f) - S/q`.

This is the form the composition-growth argument consumes: a *lower* bound on the number of
`a`-points for at least one value, which is exactly what a zero-free outer function fails to provide
on its own. -/
theorem exists_logCounting_ge {f : ℂ → ℂ} {q : ℕ} (hq : 0 < q) (A : Fin q → ℂ) {r S : ℝ}
    (hsmt : (q : ℝ) * characteristic f ⊤ r
      ≤ (∑ j, logCounting f (A j : WithTop ℂ) r) + S) :
    ∃ j : Fin q, characteristic f ⊤ r - S / (q : ℝ)
      ≤ logCounting f (A j : WithTop ℂ) r := by
  classical
  by_contra hcon
  have hall : ∀ j : Fin q,
      logCounting f (A j : WithTop ℂ) r < characteristic f ⊤ r - S / (q : ℝ) := by
    intro j
    by_contra h
    exact hcon ⟨j, not_lt.mp h⟩
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have hsum : ∑ j, logCounting f (A j : WithTop ℂ) r
      < ∑ _j : Fin q, (characteristic f ⊤ r - S / (q : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty hne (fun j _ => hall j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hval : (q : ℝ) * (characteristic f ⊤ r - S / (q : ℝ))
      = (q : ℝ) * characteristic f ⊤ r - S := by
    field_simp
  rw [hval] at hsum
  linarith

end GaloisForLFunctions.HTGeometry
