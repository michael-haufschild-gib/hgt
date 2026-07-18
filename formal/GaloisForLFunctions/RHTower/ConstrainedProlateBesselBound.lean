import GaloisForLFunctions.RHTower.ConstrainedProlateSignedSpectrum

/-!
# The true-operator Bessel bound for the constraint coordinates

The constraint coordinates of the concrete prolate problem are the pairings

```text
ℓ_n(a) = ⟨1_{[-a,a]}, e_n⟩ = ∫_{-a}^{a} e_n(x) dx,
```

of the central-interval indicator against the signed prolate modes of the actual compressed
Fourier block `Pₐ F Pₐ`.  The signed modes are pairwise orthogonal with norm zero or one, so the
subfamily of nonzero modes is orthonormal and Bessel's inequality applies to the indicator; the
zero modes pair to zero and contribute nothing.  Since the indicator has squared norm exactly
`2a`, the total squared constraint mass obeys the aperture bound

```text
Σ_n ‖ℓ_n(a)‖² ≤ 2a,
```

unconditionally — this is the Bessel-side hypothesis of the exact secular transfer theorems,
discharged for the true operator rather than assumed.
-/

noncomputable section

open MeasureTheory
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The squared norm of the central indicator is exactly the aperture length `2a`. -/
theorem norm_evenCentralIndicator_sq {a : ℝ} (ha : 0 ≤ a) :
    ‖evenCentralIndicator a‖ ^ 2 = 2 * a := by
  have hnorm : ‖evenCentralIndicator a‖
      = ‖indicatorConstLp 2 (measurableSet_centralInterval a)
          measure_Icc_lt_top.ne (1 : ℂ)‖ := rfl
  rw [hnorm, norm_indicatorConstLp (by norm_num) (by norm_num)]
  have hvol : (volume : Measure ℝ).real (centralInterval a) = 2 * a := by
    have h1 : (volume : Measure ℝ) (centralInterval a) = ENNReal.ofReal (2 * a) := by
      rw [show centralInterval a = Set.Icc (-a) a from rfl, Real.volume_Icc]
      congr 1
      ring
    rw [measureReal_def, h1, ENNReal.toReal_ofReal (by linarith)]
  have h2 : (1 : ℝ) / (2 : ENNReal).toReal = 1 / 2 := by simp
  rw [hvol, norm_one, one_mul, h2, ← Real.rpow_natCast ((2 * a) ^ ((1 : ℝ) / 2)) 2,
    ← Real.rpow_mul (by linarith)]
  norm_num

/-- The `n`-th true constraint coordinate: the central indicator paired against the `n`-th
signed prolate mode. -/
def evenProlateConstraintCoord (a : ℝ) (n : ℕ) : ℂ :=
  inner ℂ (evenCentralIndicator a) (evenProlateSignedMode a n)

/-- The constraint coordinate is exactly the integral of the mode over the aperture. -/
theorem evenProlateConstraintCoord_eq_integral (a : ℝ) (n : ℕ) :
    evenProlateConstraintCoord a n
      = ∫ x in centralInterval a, ((evenProlateSignedMode a n : evenSubspace) : SoninL2) x := by
  unfold evenProlateConstraintCoord
  rw [Submodule.coe_inner]
  exact MeasureTheory.L2.inner_indicatorConstLp_one
    (measurableSet_centralInterval a) measure_Icc_lt_top.ne _

/-- The coordinate against a vanishing mode vanishes. -/
theorem evenProlateConstraintCoord_eq_zero_of_mode_eq_zero {a : ℝ} {n : ℕ}
    (h : evenProlateSignedMode a n = 0) : evenProlateConstraintCoord a n = 0 := by
  unfold evenProlateConstraintCoord
  rw [h, inner_zero_right]

/-- The nonzero signed prolate modes form an orthonormal family. -/
theorem orthonormal_nonzero_evenProlateSignedModes (a : ℝ) :
    Orthonormal ℂ (fun i : {n : ℕ | evenProlateSignedMode a n ≠ 0} =>
      evenProlateSignedMode a i) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
    rcases evenProlateSignedMode_norm_zero_or_one a i with h0 | h1
    · exact absurd h0 i.2
    · rw [h1]
      norm_num
  · rw [if_neg hij]
    exact evenProlateSignedMode_orthogonal_of_ne a fun h => hij (Subtype.ext h)

/-- **The true-operator Bessel bound.**  The total squared constraint mass of the signed
prolate modes against the central indicator is at most the aperture length `2a`. -/
theorem tsum_evenProlateConstraintCoord_sq_le {a : ℝ} (ha : 0 ≤ a) :
    (∑' n : ℕ, ‖evenProlateConstraintCoord a n‖ ^ 2) ≤ 2 * a := by
  have horth := orthonormal_nonzero_evenProlateSignedModes a
  have hbessel := horth.tsum_inner_products_le (evenCentralIndicator a)
  have hsupp : Function.support (fun n : ℕ => ‖evenProlateConstraintCoord a n‖ ^ 2)
      ⊆ {n : ℕ | evenProlateSignedMode a n ≠ 0} := by
    intro n hn
    simp only [Function.mem_support] at hn
    intro h0
    apply hn
    rw [evenProlateConstraintCoord_eq_zero_of_mode_eq_zero h0]
    norm_num
  calc (∑' n : ℕ, ‖evenProlateConstraintCoord a n‖ ^ 2)
      = ∑' i : {n : ℕ | evenProlateSignedMode a n ≠ 0},
          ‖evenProlateConstraintCoord a ↑i‖ ^ 2 :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' i : {n : ℕ | evenProlateSignedMode a n ≠ 0},
          ‖inner ℂ (evenProlateSignedMode a ↑i) (evenCentralIndicator a)‖ ^ 2 := by
        refine tsum_congr fun i => ?_
        unfold evenProlateConstraintCoord
        rw [norm_inner_symm]
    _ ≤ ‖evenCentralIndicator a‖ ^ 2 := hbessel
    _ = 2 * a := norm_evenCentralIndicator_sq ha

/-- The squared constraint coordinates are summable. -/
theorem summable_evenProlateConstraintCoord_sq (a : ℝ) :
    Summable fun n : ℕ => ‖evenProlateConstraintCoord a n‖ ^ 2 := by
  have horth := orthonormal_nonzero_evenProlateSignedModes a
  have hsub := horth.inner_products_summable (evenCentralIndicator a)
  have hzero : ∀ n : ℕ,
      n ∉ Set.range (fun i : {n : ℕ | evenProlateSignedMode a n ≠ 0} => (i : ℕ)) →
      ‖evenProlateConstraintCoord a n‖ ^ 2 = 0 := by
    intro n hn
    have hnot : evenProlateSignedMode a n = 0 := by
      by_contra hne
      exact hn ⟨⟨n, hne⟩, rfl⟩
    rw [evenProlateConstraintCoord_eq_zero_of_mode_eq_zero hnot]
    norm_num
  refine (Function.Injective.summable_iff Subtype.coe_injective hzero).mp ?_
  refine hsub.congr fun i => ?_
  unfold evenProlateConstraintCoord
  rw [norm_inner_symm]
  rfl

/-- The Bessel-side hypotheses of the exact secular transfer theorems, discharged for the true
operator: summability holds at every aperture and the `2λ` bound holds for all nonnegative
apertures. -/
theorem evenProlate_bessel_eventually :
    ∀ᶠ lam : ℝ in Filter.atTop,
      (∑' n : ℕ, ‖evenProlateConstraintCoord lam n‖ ^ 2) ≤ 2 * lam := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam
  exact tsum_evenProlateConstraintCoord_sq_le hlam

theorem evenProlate_summable_eventually :
    ∀ᶠ lam : ℝ in Filter.atTop,
      Summable fun n : ℕ => ‖evenProlateConstraintCoord lam n‖ ^ 2 :=
  Filter.Eventually.of_forall fun lam => summable_evenProlateConstraintCoord_sq lam

end RHTower
