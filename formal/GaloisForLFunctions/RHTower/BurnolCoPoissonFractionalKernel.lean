import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorReciprocal

/-!
# The fractional-part form of the reciprocal-indicator co-Poisson value

The number of integers in the multiplicative window `[t b, t / b]` is its length `t (1/b - b)`
corrected by the two fractional parts of the endpoints.  Dividing by `t` and subtracting the window
mass leaves exactly

`(fract (t b) - fract (t / b)) / t`.

This is the classical fractional-part kernel: its Mellin transform on the positive ray is
`-zeta(w) / w` on each dilated copy, so the co-Poisson vector of the indicator seed is the
elementary bridge between the Sonine space and the zeta function inside the critical strip.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem natCeil_le_natFloor_add_one {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (ht : 0 < t) :
    ⌈t * b⌉₊ ≤ ⌊t / b⌋₊ + 1 := by
  refine Nat.ceil_le.mpr ?_
  have h1 : t * b ≤ t / b := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (le_inv_self_of_le_one hb hb1) ht.le
  have h2 : t / b < ((⌊t / b⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  push_cast
  linarith

theorem natFloor_cast_eq_sub_fract {x : ℝ} (hx : 0 ≤ x) :
    ((⌊x⌋₊ : ℕ) : ℝ) = x - Int.fract x := by
  have h : ((⌊x⌋₊ : ℕ) : ℤ) = ⌊x⌋ := Int.natCast_floor_eq_floor hx
  have h2 : ((⌊x⌋₊ : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h
  rw [h2, Int.self_sub_fract]

theorem natCeil_cast_eq_add_sub_fract {x : ℝ} (hx : 0 ≤ x) (hfr : Int.fract x ≠ 0) :
    ((⌈x⌉₊ : ℕ) : ℝ) = x + 1 - Int.fract x := by
  have h : ((⌈x⌉₊ : ℕ) : ℤ) = ⌈x⌉ := Int.natCast_ceil_eq_ceil hx
  have h2 : ((⌈x⌉₊ : ℕ) : ℝ) = ((⌈x⌉ : ℤ) : ℝ) := by exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h
  have hneg : (⌊-x⌋ : ℤ) = -⌈x⌉ := Int.floor_neg
  have h3 : ((⌊-x⌋ : ℤ) : ℝ) = -x - Int.fract (-x) := (Int.self_sub_fract (-x)).symm
  rw [hneg, Int.fract_neg hfr] at h3
  push_cast at h3
  rw [h2]
  linarith

/-- **The window index count in fractional-part form.** -/
theorem windowCard_eq_fract {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (ht : 0 < t)
    (hfr : Int.fract (t * b) ≠ 0) :
    ((Finset.Icc ⌈t * b⌉₊ ⌊t / b⌋₊).card : ℝ) =
      t * (b⁻¹ - b) + Int.fract (t * b) - Int.fract (t / b) := by
  have hle := natCeil_le_natFloor_add_one hb hb1 ht
  have hcard : ((Finset.Icc ⌈t * b⌉₊ ⌊t / b⌋₊).card : ℝ) =
      ((⌊t / b⌋₊ : ℕ) : ℝ) + 1 - ((⌈t * b⌉₊ : ℕ) : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub hle]
    push_cast
    ring
  rw [hcard, natFloor_cast_eq_sub_fract (by positivity : (0 : ℝ) ≤ t / b),
    natCeil_cast_eq_add_sub_fract (by positivity : (0 : ℝ) ≤ t * b) hfr]
  have hexp : t * (b⁻¹ - b) = t / b - t * b := by
    rw [mul_sub, div_eq_mul_inv]
  rw [hexp]
  ring

/-- **The reciprocal-indicator co-Poisson value is the fractional-part kernel.** -/
theorem burnolCoPoissonRightSum_reciprocalIndicator_eq_fract {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 0 < t) (hfr : Int.fract (t * b) ≠ 0) :
    burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t =
      (((Int.fract (t * b) - Int.fract (t / b)) / t : ℝ) : ℂ) := by
  rw [burnolCoPoissonRightSum_reciprocalIndicator_eq_card hb hb1 ht]
  congr 1
  rw [windowCard_eq_fract hb hb1 ht hfr]
  field_simp
  ring

/-- The scales at which the window endpoint is an integer form a null set. -/
theorem measure_zero_fract_eq_zero {b : ℝ} (hb : 0 < b) :
    volume {t : ℝ | Int.fract (t * b) = 0} = 0 := by
  have hsub : {t : ℝ | Int.fract (t * b) = 0} ⊆ Set.range fun n : ℤ => (n : ℝ) / b := by
    intro t ht
    refine ⟨⌊t * b⌋, ?_⟩
    have h : ((⌊t * b⌋ : ℤ) : ℝ) = t * b := by
      have h0 := Int.self_sub_fract (t * b)
      rw [(by exact ht : Int.fract (t * b) = 0), sub_zero] at h0
      exact h0.symm
    dsimp only
    rw [h, mul_div_assoc, div_self (ne_of_gt hb), mul_one]
  exact measure_mono_null hsub
    ((Set.countable_range fun n : ℤ => (n : ℝ) / b).measure_zero volume)

/-- **The fractional-part form holds almost everywhere on the positive ray.** -/
theorem burnolCoPoissonRightSum_reciprocalIndicator_ae_fract {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonIndicatorSeed b))
      =ᵐ[volume.restrict (Ioi 0)]
      fun t : ℝ => (((Int.fract (t * b) - Int.fract (t / b)) / t : ℝ) : ℂ) := by
  have hcompl : ∀ᵐ t ∂(volume : Measure ℝ), Int.fract (t * b) ≠ 0 := by
    rw [Filter.eventually_iff, mem_ae_iff]
    convert measure_zero_fract_eq_zero hb using 2
    ext t
    simp
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcompl] with t ht hfr
  exact burnolCoPoissonRightSum_reciprocalIndicator_eq_fract hb hb1 (mem_Ioi.mp ht) hfr

end RHTower
