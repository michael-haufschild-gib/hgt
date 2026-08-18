import GaloisForLFunctions.RHTower.PrimeWeylSamplingIdealizerAnalytic
import GaloisForLFunctions.RHTower.XiRealDivisorSampling

/-!
# The collapse on the full real Xi sampling quotient, and its sharpness

`prime-modulated-weyl-idealizer-collapse-on-xi-sampling`, equations `(23)` and section 7.

The real Xi divisor is locally finite and symmetric — both unconditional theorems of this tree — so
Theorem A applies to it as soon as its counting function is superlinear.  Superlinearity of
`Z_Xi^R` is exactly the positive-proportion theorem of Selberg (equivalently Conrey's `2/5`)
combined with Riemann–von Mangoldt, and it is the single named literature input of section 4; it
enters here as the explicit hypothesis `SuperlinearSamples xiRealDivisor`.

Sections 7.1 and 7.2 are the sharpness of the two hypotheses, and both are constructed here:

* a **finite** sampling set does not collapse — a polynomial coefficient may vanish on it without
  being the zero polynomial;
* a **linear-density lattice** does not collapse — the shift by the lattice period preserves the
  sampling ideal exactly.
-/

open Set

namespace RHTower

/-! ## `(23)`: the Xi instance -/

/-- **`(23)`: the sampling idealizer collapses on the full real Xi divisor.**  Every coefficient of
a finite shift–Weyl operator descending to the real-Xi sampling quotient vanishes, except the
zero-shift zero-order polynomial multiplier. -/
theorem xiSamplingIdealizer_collapse {m : ℕ} {F : Finset ℝ} {a : ℝ → ℕ → Polynomial ℂ}
    (hsuper : SuperlinearSamples xiRealDivisor) (h0 : (0 : ℝ) ∈ F)
    (hpres : PreservesSamplingIdeal m xiRealDivisor F a) :
    ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → a h j = 0 :=
  samplingIdealizer_collapse locallyFiniteSamples_xiRealDivisor symmetric_xiRealDivisor
    hsuper h0 hpres

/-- **`(23)` in operator form.**  On the real-Xi sampling quotient the operator acts as
multiplication by a polynomial in the spectral variable. -/
theorem xiSamplingIdealizer_eq_polynomial_multiplier {m : ℕ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ}
    (hsuper : SuperlinearSamples xiRealDivisor) (h0 : (0 : ℝ) ∈ F)
    (hpres : PreservesSamplingIdeal m xiRealDivisor F a) (φ : ℝ → ℂ) (x : ℝ) :
    shiftWeylEval m F a φ x = (a 0 0).eval (x : ℂ) * φ x :=
  shiftWeylEval_eq_polynomial_multiplier h0
    (xiSamplingIdealizer_collapse hsuper h0 hpres) φ x

/-! ## Section 7.1: a finite sampling set does not collapse -/

/-- The first-order operator `x ∂_x`. -/
noncomputable def firstOrderPositionCoeff : ℝ → ℕ → Polynomial ℂ :=
  fun _ j => if j = 1 then Polynomial.X else 0

/-- **Section 7.1.**  On the one-point sampling set the operator `x ∂_x` preserves the sampling
ideal even though its first-order coefficient is a nonzero polynomial: superlinearity cannot be
dropped in favour of mere nonemptiness. -/
theorem preservesSamplingIdeal_singleton_firstOrder :
    PreservesSamplingIdeal 1 ({0} : Set ℝ) ({0} : Finset ℝ) firstOrderPositionCoeff := by
  intro φ _ γ hγ
  have hγ0 : γ = 0 := hγ
  subst hγ0
  rw [shiftWeylEval]
  simp only [Finset.sum_singleton, Finset.sum_range_succ, Finset.range_one,
    firstOrderPositionCoeff]
  norm_num

theorem firstOrderPositionCoeff_ne_zero : firstOrderPositionCoeff 0 1 ≠ 0 := by
  rw [firstOrderPositionCoeff]
  simp

/-! ## Section 7.2: a linear-density lattice does not collapse -/

/-- The lattice sampling set `h ℤ`. -/
def latticeSamples (h : ℝ) : Set ℝ := {x : ℝ | ∃ n : ℤ, x = (n : ℝ) * h}

theorem latticeSamples_symm {h : ℝ} : ∀ x, x ∈ latticeSamples h → -x ∈ latticeSamples h := by
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact ⟨-n, by push_cast; ring⟩

theorem locallyFiniteSamples_lattice {h : ℝ} (hh : 0 < h) :
    LocallyFiniteSamples (latticeSamples h) := by
  intro T
  have hsub : latticeSamples h ∩ Set.Icc (-T) T
      ⊆ (fun n : ℤ => (n : ℝ) * h) '' (Set.Icc (-⌈|T| / h⌉) ⌈|T| / h⌉ : Set ℤ) := by
    rintro x ⟨⟨n, rfl⟩, hx⟩
    refine ⟨n, ⟨?_, ?_⟩, rfl⟩
    · have hle : -|T| ≤ (n : ℝ) * h := le_trans (neg_le_neg (le_abs_self T)) hx.1
      have hdiv : -(|T| / h) ≤ (n : ℝ) := by
        rw [← neg_div]
        exact (div_le_iff₀ hh).mpr hle
      have : (-⌈|T| / h⌉ : ℝ) ≤ (n : ℝ) := by
        have := Int.le_ceil (|T| / h)
        linarith
      exact_mod_cast this
    · have hle : (n : ℝ) * h ≤ |T| := le_trans hx.2 (le_abs_self T)
      have hdiv : (n : ℝ) ≤ |T| / h := (le_div_iff₀ hh).mpr hle
      have : (n : ℝ) ≤ (⌈|T| / h⌉ : ℝ) := le_trans hdiv (Int.le_ceil _)
      exact_mod_cast this
  exact Set.Finite.subset (Set.Finite.image _ (Set.finite_Icc _ _)) hsub

theorem shiftFailure_lattice_eq_empty {h : ℝ} : shiftFailure (latticeSamples h) h = ∅ := by
  ext x
  simp only [shiftFailure, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨n, rfl⟩
  intro hcon
  exact hcon ⟨n + 1, by push_cast; ring⟩

/-- **Section 7.2: superlinear density is the sharp mechanism.**  A linear-density lattice is
locally finite and symmetric but not superlinear. -/
theorem not_superlinearSamples_lattice {h : ℝ} (hh : 0 < h) :
    ¬ SuperlinearSamples (latticeSamples h) := by
  intro hsuper
  have hinf := infinite_shiftFailure_of_superlinear (locallyFiniteSamples_lattice hh)
    latticeSamples_symm hsuper (ne_of_gt hh)
  rw [shiftFailure_lattice_eq_empty] at hinf
  exact absurd hinf (by simp)

/-- The pure shift by the lattice period. -/
noncomputable def latticeShiftCoeff : ℝ → ℕ → Polynomial ℂ := fun _ _ => 1

/-- **Section 7.2.**  On the lattice `h ℤ` the shift by `h` preserves the sampling ideal, so the
collapse fails: the nonzero coefficient sits at a nonzero shift. -/
theorem preservesSamplingIdeal_lattice_shift {h : ℝ} :
    PreservesSamplingIdeal 0 (latticeSamples h) ({h} : Finset ℝ) latticeShiftCoeff := by
  intro φ hφ γ hγ
  obtain ⟨n, rfl⟩ := hγ
  rw [shiftWeylEval]
  simp only [Finset.sum_singleton, latticeShiftCoeff, Polynomial.eval_one, one_mul, zero_add,
    Finset.sum_range_one, iteratedDeriv_zero]
  exact hφ ((n : ℝ) * h + h) ⟨n + 1, by push_cast; ring⟩

theorem latticeShiftCoeff_ne_zero {h : ℝ} : latticeShiftCoeff h 0 ≠ 0 := by
  rw [latticeShiftCoeff]
  exact one_ne_zero

end RHTower
