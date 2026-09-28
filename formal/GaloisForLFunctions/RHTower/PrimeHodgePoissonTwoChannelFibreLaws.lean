import GaloisForLFunctions.RHTower.PrimeHodgePoissonTwoChannelIntegralSplit
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CompactObserverHorizon

/-!
# Two-channel prime--Hodge split: exact trace preservation and fibre laws

Companion to `PrimeHodgePoissonTwoChannelIntegralSplit` (ULF-PHPTCIS-001):

* the two-Kraus instrument `X ↦ V_a X V_a ⊕ C_a X C_a` preserves the (complex) trace of **every**
  trace-class input, not only of states;
* for `a ≠ 0` the prime visibility `sech(a log p / 2)` tends to zero along the primes while the
  contrast `|tanh(a log p / 2)|` tends to one;
* on the prime fibre `ℓ²(Primes)` the visibility multiplier is compact for `a ≠ 0`, whereas its lift
  to the history--prime carrier `ℓ²(ℕ × Primes)` is never compact (infinite history multiplicity).
-/

open Filter Topology ContinuousLinearMap

namespace RHTower

noncomputable section

/-- **(PTC.5) trace preservation on arbitrary trace-class inputs.** -/
theorem primeHodgeTwoChannelInstrument_opTrace (a : ℝ)
    (ρ : GaloisForLFunctions.HTGeometry.TraceClassOperator PrimeHodgeHistoryHilbert) :
    opTrace ((primeHodgeTwoChannelInstrument a ρ :
        GaloisForLFunctions.HTGeometry.TraceClassOperator
          (WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert))) :
        WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert) →L[ℂ]
          WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert)) =
      opTrace (ρ : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) := by
  change opTrace ((primeHodgeSplitDilation a ∘L
      (ρ : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)) ∘L
        adjoint (primeHodgeSplitDilation a)) = _
  rw [GaloisForLFunctions.HTGeometry.opTrace_sandwich _ _ ρ.property,
    adjoint_primeHodgeSplitDilation_comp_self, ContinuousLinearMap.comp_id]

theorem tendsto_natCast_primes_cofinite :
    Tendsto (fun p : Nat.Primes => ((p : ℕ) : ℝ)) cofinite atTop := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have h1 : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hinj.tendsto_cofinite
  exact tendsto_natCast_atTop_atTop.comp h1

theorem tendsto_abs_primeHodgeRapidity {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun p : Nat.Primes => |primeHodgeRapidity a p|) cofinite atTop := by
  have hlog : Tendsto (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) cofinite atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_primes_cofinite
  have hpos : 0 < |a| / 2 := by positivity
  have hscaled := hlog.const_mul_atTop hpos
  refine hscaled.congr' ?_
  filter_upwards with p
  have hlp : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_natCast_nonneg _
  rw [primeHodgeRapidity, abs_div, abs_mul, abs_of_nonneg hlp, abs_two]
  ring

/-- For `a ≠ 0` the prime visibility `sech(a log p / 2)` tends to zero along the primes. -/
theorem tendsto_primeHodgeVisibility_zero {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun p : Nat.Primes => primeHodgeVisibility a p) cofinite (𝓝 0) := by
  have hbound : ∀ p : Nat.Primes,
      (1 + |primeHodgeRapidity a p|) / 2 ≤ Real.cosh (primeHodgeRapidity a p) := by
    intro p
    rw [← Real.cosh_abs, Real.cosh_eq]
    have h1 := Real.add_one_le_exp |primeHodgeRapidity a p|
    have h2 := Real.exp_pos (-|primeHodgeRapidity a p|)
    linarith
  have hlin : Tendsto (fun p : Nat.Primes => (1 + |primeHodgeRapidity a p|) / 2)
      cofinite atTop :=
    (tendsto_atTop_add_const_left _ 1 (tendsto_abs_primeHodgeRapidity ha)).atTop_div_const
      two_pos
  have hcosh : Tendsto (fun p : Nat.Primes => Real.cosh (primeHodgeRapidity a p))
      cofinite atTop := tendsto_atTop_mono hbound hlin
  refine hcosh.inv_tendsto_atTop.congr fun p => ?_
  simp [primeHodgeVisibility]

/-- For `a ≠ 0` the prime contrast tends in modulus to one along the primes. -/
theorem tendsto_abs_primeHodgeContrast_one {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun p : Nat.Primes => |primeHodgeContrast a p|) cofinite (𝓝 1) := by
  have hsq : Tendsto (fun p : Nat.Primes => primeHodgeContrast a p ^ 2) cofinite (𝓝 1) := by
    have hv := (tendsto_primeHodgeVisibility_zero ha).pow 2
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at hv
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hv
    rw [sub_zero] at h1
    refine h1.congr fun p => ?_
    have := primeHodgeVisibility_sq_add_contrast_sq a p
    linarith
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hsq
  rw [Real.sqrt_one] at hsqrt
  refine hsqrt.congr fun p => ?_
  simp [Function.comp, Real.sqrt_sq_eq_abs]

theorem norm_primeHodgeVisibility_prime_le_one (a : ℝ) (p : Nat.Primes) :
    ‖((primeHodgeVisibility a p : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeHodgeVisibility_pos a p)]
  exact primeHodgeVisibility_le_one a p

/-- Visibility multiplier on the prime fibre `ℓ²(Primes)`. -/
def primeHodgePrimeFibreVisibilityOp (a : ℝ) :
    HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ] HTGeometry.IndexedEllTwo Nat.Primes :=
  HTGeometry.ellTwoDiagonal (fun p : Nat.Primes => (primeHodgeVisibility a p : ℂ))
    (norm_primeHodgeVisibility_prime_le_one a)

/-- **Prime-fibre compactness.**  For `a ≠ 0` the visibility multiplier on `ℓ²(Primes)` is a
compact operator. -/
theorem isCompactOperator_primeHodgePrimeFibreVisibilityOp {a : ℝ} (ha : a ≠ 0) :
    IsCompactOperator (primeHodgePrimeFibreVisibilityOp a) := by
  apply GaloisForLFunctions.HTGeometry.isCompactOperator_of_diag_tendsto_cofinite
    (HTGeometry.ellTwoCoordinateBasis Nat.Primes)
    (c := fun p : Nat.Primes => (primeHodgeVisibility a p : ℂ))
  · intro p
    exact HTGeometry.ellTwoDiagonal_coordinateBasis _ _ p
  · have h := (tendsto_primeHodgeVisibility_zero ha).norm
    rw [norm_zero] at h
    refine h.congr fun p => ?_
    rw [Complex.norm_real]

/-- **Infinite history multiplicity.**  The lift of the visibility multiplier to the
history--prime carrier `ℓ²(ℕ × Primes)` is never compact: along the orthonormal history column of
any prime it acts by the fixed positive scalar `sech(a log p / 2)`. -/
theorem not_isCompactOperator_primeHodgeVisibilityOp (a : ℝ) :
    ¬ IsCompactOperator (primeHodgeVisibilityOp a) := by
  intro hK
  classical
  let p₀ : Nat.Primes := ⟨2, Nat.prime_two⟩
  let e : ℕ → PrimeHodgeHistoryHilbert := fun n =>
    HTGeometry.ellTwoCoordinateBasis PrimeHodgeHistoryIndex (n, p₀)
  have he : Orthonormal ℂ e :=
    (HTGeometry.ellTwoCoordinateBasis PrimeHodgeHistoryIndex).orthonormal.comp _
      (fun m n h => congrArg Prod.fst h)
  have htend := HTGeometry.ConstraintMotiveRelativity.tendsto_norm_image_orthonormal
    (primeHodgeVisibilityOp a) hK he
  have hconst : ∀ n, ‖primeHodgeVisibilityOp a (e n)‖ = primeHodgeVisibility a p₀ := by
    intro n
    have hdiag : primeHodgeVisibilityOp a (e n) =
        ((primeHodgeVisibility a p₀ : ℝ) : ℂ) • e n :=
      HTGeometry.ellTwoDiagonal_coordinateBasis
        (fun np : PrimeHodgeHistoryIndex => (primeHodgeVisibility a np.2 : ℂ))
        (norm_primeHodgeVisibility_le_one a) (n, p₀)
    rw [hdiag, norm_smul, he.1 n, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (primeHodgeVisibility_pos a p₀)]
  simp only [hconst] at htend
  exact (primeHodgeVisibility_pos a p₀).ne' (tendsto_nhds_unique tendsto_const_nhds htend)

end

end RHTower
