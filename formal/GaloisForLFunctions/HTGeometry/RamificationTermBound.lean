import GaloisForLFunctions.HTGeometry.SecondMainTheoremEntire
import GaloisForLFunctions.HTGeometry.TotallyRamifiedOrder
import GaloisForLFunctions.HTGeometry.SmallGrowthDerivative

/-!
# The ramification term of the second main theorem

The term `m(r, 1/f')` left over by the second main theorem is converted, through the first main
theorem applied to `f'`, into

```text
m(r, 1/f') ≤ T(r, f') + C - N(r, 1/f').
```

The counting function `N(r, 1/f')` is the one that absorbs the value-counting functions of totally
ramified values, and `T(r, f')` is bounded by the characteristic of `f` together with the proximity
of the logarithmic derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution

/-- **The ramification term through the first main theorem.**  The proximity of `1/g` at infinity is
the characteristic of `g` minus the zero-counting function, up to the first-main-theorem defect. -/
theorem proximity_inv_top_le {g : ℂ → ℂ} (hg : Meromorphic g) {r : ℝ} :
    proximity (fun z => (g z)⁻¹) ⊤ r
      ≤ characteristic g ⊤ r
        + max |Real.log ‖g 0‖| |Real.log ‖meromorphicTrailingCoeffAt g 0‖|
        - logCounting g 0 r := by
  have hfun : (fun z => (g z)⁻¹) = g⁻¹ := rfl
  rw [hfun, ValueDistribution.proximity_inv]
  have hchar0 : characteristic g 0 r = proximity g 0 r + logCounting g 0 r := rfl
  have hinv : characteristic g 0 = characteristic g⁻¹ ⊤ := by
    rw [ValueDistribution.characteristic, ValueDistribution.characteristic,
      ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]
  have hfmt := ValueDistribution.characteristic_sub_characteristic_inv_le (f := g) (R := r) hg
  have h1 := (abs_le.mp hfmt).1
  have h3 : characteristic g 0 r = characteristic g⁻¹ ⊤ r := by rw [hinv]
  linarith [hchar0, h1, h3]


/-- **The first main theorem, the direction bounding a value characteristic by the characteristic at
infinity.**  The corpus's `characteristic_top_le_characteristic_coe` is the opposite inequality; both
come from the same two absolute-value estimates. -/
theorem characteristic_coe_le_characteristic_top {f : ℂ → ℂ} {a₀ : ℂ} {r : ℝ}
    (hf : Meromorphic f) (hg : Meromorphic ((f - fun _ : ℂ => a₀) : ℂ → ℂ)) :
    characteristic f (a₀ : WithTop ℂ) r
      ≤ characteristic f ⊤ r
        + ((Real.posLog ‖a₀‖ + Real.log 2)
          + max |Real.log ‖((f - fun _ : ℂ => a₀) : ℂ → ℂ) 0‖|
              |Real.log ‖meromorphicTrailingCoeffAt ((f - fun _ : ℂ => a₀) : ℂ → ℂ) 0‖|) := by
  have hshift := ValueDistribution.abs_characteristic_sub_characteristic_shift_le
    (f := f) (a₀ := a₀) (r := r) hf
  have hinv := ValueDistribution.characteristic_sub_characteristic_inv_le
    (f := (f - fun _ : ℂ => a₀)) (R := r) hg
  have hfun : (fun x => f x - a₀) = ((f - fun _ : ℂ => a₀) : ℂ → ℂ) := rfl
  rw [hfun] at hshift
  have hval : characteristic f (a₀ : WithTop ℂ) r
      = characteristic ((f - fun _ : ℂ => a₀) : ℂ → ℂ)⁻¹ ⊤ r := by
    rw [characteristic_coe_eq, characteristic_zero_eq_inv_top]
  rw [hval]
  have h₁ := (abs_le.mp hshift).1
  have h₂ := (abs_le.mp hinv).1
  linarith


open Metric Filter in
/-- **The totally ramified value bound.**  For an entire function with `q` pairwise separated
totally ramified values,

```text
(q/2 − 2) · T(r,f) ≤ ∑_j m(r, f'/(f − a_j)) + m(r, f'/f) + C.
```

The right-hand side is the Nevanlinna error term `S(r,f)`, so the number of totally ramified values
is bounded as soon as `S(r,f) = o(T(r,f))`. -/
theorem totallyRamified_characteristic_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {q : ℕ} (A : Fin q → ℂ) {δ r : ℝ} (hδ : 0 < δ) (hr : 1 ≤ r)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hram : ∀ j, ∀ z, f z = A j → deriv f z = 0)
    (hfa : ∀ j, ∀ z, meromorphicOrderAt (fun w => f w - A j) z ≠ ⊤)
    (hfd : ∀ z, meromorphicOrderAt (deriv f) z ≠ ⊤)
    (hforder : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0) :
    ∃ C : ℝ, ((q : ℝ) / 2 - 2) * characteristic f ⊤ r
      ≤ (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r)
        + proximity (fun z => deriv f z / f z) ⊤ r + C := by
  classical
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    linarith
  have hmf : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  have hinj : Function.Injective A := by
    intro i j hij
    by_contra hne
    have := hsep i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  -- the second main theorem
  obtain ⟨K, hK0, hsmt⟩ :=
    exists_mul_characteristic_le_of_separated_entire A hδ hr0 hsep hf hcod
  -- inequality 1
  have hineq1 := sum_logCounting_value_le_two_mul_logCounting_deriv_zero hf A hinj hram hfa hfd hr
  -- inequality 2
  have hineq2 := proximity_inv_top_le (g := deriv f) (fun z => ((hf.deriv).analyticAt z).meromorphicAt) (r := r)
  -- inequality 3
  have hineq3 := smallGrowth_characteristic_deriv_le hmf hforder hr
  -- each value characteristic is bounded by the characteristic at infinity
  have hNj : ∀ j : Fin q, logCounting f (A j : WithTop ℂ) r
      ≤ characteristic f ⊤ r
        + ((Real.posLog ‖A j‖ + Real.log 2)
          + max |Real.log ‖((f - fun _ : ℂ => A j) : ℂ → ℂ) 0‖|
              |Real.log ‖meromorphicTrailingCoeffAt ((f - fun _ : ℂ => A j) : ℂ → ℂ) 0‖|) := by
    intro j
    have hg : Meromorphic ((f - fun _ : ℂ => A j) : ℂ → ℂ) := by
      intro z
      exact (hmf z).sub (analyticAt_const.meromorphicAt)
    have hbase := characteristic_coe_le_characteristic_top (f := f) (a₀ := A j) (r := r) hmf hg
    have hprox : (0 : ℝ) ≤ proximity f (A j : WithTop ℂ) r := proximity_nonneg r
    have hsplit : characteristic f (A j : WithTop ℂ) r
        = proximity f (A j : WithTop ℂ) r + logCounting f (A j : WithTop ℂ) r := rfl
    linarith
  set Kv : ℝ := ∑ j, ((Real.posLog ‖A j‖ + Real.log 2)
      + max |Real.log ‖((f - fun _ : ℂ => A j) : ℂ → ℂ) 0‖|
          |Real.log ‖meromorphicTrailingCoeffAt ((f - fun _ : ℂ => A j) : ℂ → ℂ) 0‖|) with hKv
  have hsumN : (∑ j, logCounting f (A j : WithTop ℂ) r)
      ≤ (q : ℝ) * characteristic f ⊤ r + Kv := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => hNj j)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    rw [hKv]
    exact h
  refine ⟨K * (q : ℝ) + (q : ℝ) * Real.posLog (2 / δ)
      + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2 + Real.log (q : ℝ)
      + max |Real.log ‖deriv f 0‖| |Real.log ‖meromorphicTrailingCoeffAt (deriv f) 0‖|
      + Kv / 2, ?_⟩
  linarith [hsmt, hineq1, hineq2, hineq3, hsumN]

end GaloisForLFunctions.HTGeometry
