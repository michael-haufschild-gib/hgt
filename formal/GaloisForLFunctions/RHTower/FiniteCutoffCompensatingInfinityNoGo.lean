import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder
import GaloisForLFunctions.RHTower.FiniteMobiusRecoveryGluingNoGo

/-!
# Compensating finite-cutoff infinities are universal on the open strip

The constant-coefficient Dirichlet head and the explicit continuation correction both escape at
every point of the open critical strip.  After the canonical complex-power normalization their
limits are respectively `1` and `-1`, while their exact sum converges to zeta.  At a nontrivial
zeta zero that finite sum darkens.

This supplies a literal two-process infinity, but closes it as a first-boundary zero detector: the
same antidiagonal leading boundary occurs at every open-strip point.  Any information-geometric
route using these two processes must retain a finer compensated finite part; ordinary boundary
completion loses the zero datum.
-/

noncomputable section

open Complex Filter Set
open scoped Topology BigOperators

namespace RHTower.DeletionMixedRefinement

/-- A point of the open critical strip, with both analytic-domain inequalities internalized. -/
abbrev FiniteCutoffOpenStripPoint := {s : ℂ // 0 < s.re ∧ s.re < 1}

/-- No open-strip point is the pole. -/
theorem finiteCutoffOpenStripPoint_ne_one (s : FiniteCutoffOpenStripPoint) :
    (s : ℂ) ≠ 1 := by
  intro h
  have := s.2.2
  rw [h, Complex.one_re] at this
  exact lt_irrefl 1 this

/-- Literal constant-coefficient Dirichlet head. -/
def finiteZetaFormationHead (N : ℕ) (s : ℂ) : ℂ :=
  finiteDirichletHead
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℂ) N s

/-- The coefficient head is the expected finite complex-power sum. -/
theorem finiteZetaFormationHead_eq_sum (N : ℕ) (s : ℂ) :
    finiteZetaFormationHead N s =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
  rw [finiteZetaFormationHead, finiteDirichletHead_eq_sum_mul_cpow]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  simp [hn0]

/-- Exact two-process decomposition before passage to cutoff infinity. -/
theorem finiteZetaFormationHead_add_continuationCorrection
    (N : ℕ) (s : ℂ) :
    finiteZetaFormationHead N s + finiteCutoffContinuationCorrection N s =
      finiteCutoffZeta N s := by
  simp [finiteZetaFormationHead, finiteCutoffContinuationCorrection]

/-- Canonical scale that removes the divergent complex-power head. -/
def finiteCutoffNormalizer (s : FiniteCutoffOpenStripPoint) (N : ℕ) : ℂ :=
  (1 - (s : ℂ)) * (N : ℂ) ^ ((s : ℂ) - 1)

/-- The canonical normalization vanishes throughout the open strip. -/
theorem tendsto_finiteCutoffNormalizer_zero (s : FiniteCutoffOpenStripPoint) :
    Tendsto (finiteCutoffNormalizer s) atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℂ) ^ ((s : ℂ) - 1)) atTop (nhds 0) :=
    tendsto_nat_cpow_zero (by
      simp only [Complex.sub_re, Complex.one_re]
      exact sub_neg.mpr s.2.2)
  change Tendsto (fun N : ℕ =>
    (1 - (s : ℂ)) * (N : ℂ) ^ ((s : ℂ) - 1)) atTop (nhds 0)
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := (1 - (s : ℂ))).mul hpow)

/-- The normalizer is nonzero at every nonempty cutoff. -/
theorem eventually_finiteCutoffNormalizer_ne_zero (s : FiniteCutoffOpenStripPoint) :
    ∀ᶠ N : ℕ in atTop, finiteCutoffNormalizer s N ≠ 0 := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  apply mul_ne_zero
  · intro h
    apply finiteCutoffOpenStripPoint_ne_one s
    linear_combination -h
  · apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (by exact_mod_cast (Nat.ne_zero_of_lt hN))

/-- Reciprocal normalizer magnitude escapes to infinity. -/
theorem tendsto_inv_norm_finiteCutoffNormalizer_atTop
    (s : FiniteCutoffOpenStripPoint) :
    Tendsto (fun N : ℕ => ‖finiteCutoffNormalizer s N‖⁻¹) atTop atTop := by
  have hnorm : Tendsto (fun N : ℕ => ‖finiteCutoffNormalizer s N‖)
      atTop (nhds 0) := by
    simpa using (tendsto_finiteCutoffNormalizer_zero s).norm
  have hwithin : Tendsto (fun N : ℕ => ‖finiteCutoffNormalizer s N‖)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hnorm, (eventually_finiteCutoffNormalizer_ne_zero s).mono fun N hN =>
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hN))⟩
  exact hwithin.inv_tendsto_nhdsGT_zero

/-- The finite continuation converges pointwise to zeta throughout the open strip. -/
theorem tendsto_finiteCutoffZeta_at_openStrip (s : FiniteCutoffOpenStripPoint) :
    Tendsto (fun N : ℕ => finiteCutoffZeta N s.1) atTop (nhds (riemannZeta s.1)) := by
  have h := tendstoUniformlyOn_finiteCutoffZeta
    (Bornology.isBounded_singleton : Bornology.IsBounded ({s.1} : Set ℂ))
    (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨s.2.1, finiteCutoffOpenStripPoint_ne_one s⟩)
  exact h.tendsto_at (show s.1 ∈ ({s.1} : Set ℂ) by simp)

/-- The normalized coefficient head converges to `1` at every open-strip point. -/
theorem tendsto_normalized_finiteZetaFormationHead
    (s : FiniteCutoffOpenStripPoint) :
    Tendsto (fun N : ℕ =>
      finiteCutoffNormalizer s N * finiteZetaFormationHead N s.1)
      atTop (nhds 1) := by
  have hpartial := tendsto_sum_cpow_sub_pow s.2.1
    (finiteCutoffOpenStripPoint_ne_one s)
  have hpow : Tendsto (fun N : ℕ => (N : ℂ) ^ (s.1 - 1)) atTop (nhds 0) :=
    tendsto_nat_cpow_zero (by
      simp only [Complex.sub_re, Complex.one_re]
      exact sub_neg.mpr s.2.2)
  have hzero := hpow.mul hpartial
  have hscaled : Tendsto (fun N : ℕ =>
      (1 - s.1) * ((N : ℂ) ^ (s.1 - 1) *
        ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s.1)) -
          (N : ℂ) ^ (1 - s.1) / (1 - s.1))) + 1) atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds (x := (1 - s.1))).mul hzero).add_const (1 : ℂ)
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [finiteCutoffNormalizer, finiteZetaFormationHead_eq_sum]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hcancel : (N : ℂ) ^ (s.1 - 1) * (N : ℂ) ^ (1 - s.1) = 1 := by
    rw [← Complex.cpow_add _ _ hN0]
    simp
  have hden : (1 : ℂ) - s.1 ≠ 0 := by
    intro h
    apply finiteCutoffOpenStripPoint_ne_one s
    linear_combination -h
  rw [show (1 - s.1) * (N : ℂ) ^ (s.1 - 1) *
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s.1) =
      1 + (1 - s.1) * ((N : ℂ) ^ (s.1 - 1) *
        ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s.1)) -
          (N : ℂ) ^ (1 - s.1) / (1 - s.1))) by
        field_simp [hden]
        linear_combination hcancel]
  ring

/-- The normalized continuation correction converges to `-1` everywhere on the open strip. -/
theorem tendsto_normalized_finiteCutoffContinuationCorrection
    (s : FiniteCutoffOpenStripPoint) :
    Tendsto (fun N : ℕ =>
      finiteCutoffNormalizer s N * finiteCutoffContinuationCorrection N s.1)
      atTop (nhds (-1)) := by
  have hscaledFormation :=
    (tendsto_finiteCutoffNormalizer_zero s).mul (tendsto_finiteCutoffZeta_at_openStrip s)
  have hscaledHead := tendsto_normalized_finiteZetaFormationHead s
  have h := hscaledFormation.sub hscaledHead
  simpa [finiteCutoffContinuationCorrection, finiteZetaFormationHead, mul_sub] using h

/-- The coefficient head leaves every norm-bounded set throughout the open strip. -/
theorem tendsto_norm_finiteZetaFormationHead_atTop
    (s : FiniteCutoffOpenStripPoint) :
    Tendsto (fun N : ℕ => ‖finiteZetaFormationHead N s.1‖) atTop atTop := by
  have hscaled := (tendsto_normalized_finiteZetaFormationHead s).norm
  rw [norm_one] at hscaled
  have hproduct := hscaled.pos_mul_atTop zero_lt_one
    (tendsto_inv_norm_finiteCutoffNormalizer_atTop s)
  refine hproduct.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hnormalizerNe : ‖finiteCutoffNormalizer s N‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    apply mul_ne_zero
    · intro h
      apply finiteCutoffOpenStripPoint_ne_one s
      linear_combination -h
    · apply Complex.cpow_ne_zero_iff.mpr
      exact Or.inl (by exact_mod_cast (Nat.ne_zero_of_lt hN))
  rw [norm_mul]
  field_simp

/-- The continuation correction leaves every norm-bounded set throughout the open strip. -/
theorem tendsto_norm_finiteCutoffContinuationCorrection_atTop
    (s : FiniteCutoffOpenStripPoint) :
    Tendsto (fun N : ℕ => ‖finiteCutoffContinuationCorrection N s.1‖) atTop atTop := by
  have hscaled := (tendsto_normalized_finiteCutoffContinuationCorrection s).norm
  rw [norm_neg, norm_one] at hscaled
  have hproduct := hscaled.pos_mul_atTop zero_lt_one
    (tendsto_inv_norm_finiteCutoffNormalizer_atTop s)
  refine hproduct.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hnormalizerNe : ‖finiteCutoffNormalizer s N‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    apply mul_ne_zero
    · intro h
      apply finiteCutoffOpenStripPoint_ne_one s
      linear_combination -h
    · apply Complex.cpow_ne_zero_iff.mpr
      exact Or.inl (by exact_mod_cast (Nat.ne_zero_of_lt hN))
  rw [norm_mul]
  field_simp

/-- Every nontrivial zero determines an open-strip point without an added premise. -/
def finiteCutoffOpenStripPointOfZero
    (rho : RiemannGaussian.NontrivialZetaZero) : FiniteCutoffOpenStripPoint :=
  ⟨rho.1, RiemannGaussian.NontrivialZetaZero.zero_lt_re rho,
    RiemannGaussian.NontrivialZetaZero.re_lt_one rho⟩

/-- At a nontrivial zero, the finite sum of the two escaping processes darkens. -/
theorem tendsto_finiteZetaFormationHead_add_continuationCorrection_at_zero
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      finiteZetaFormationHead N rho.1 + finiteCutoffContinuationCorrection N rho.1)
      atTop (nhds 0) := by
  have h := tendsto_finiteCutoffZeta_at_openStrip (finiteCutoffOpenStripPointOfZero rho)
  have h' : Tendsto (fun N : ℕ => finiteCutoffZeta N rho.1)
      atTop (nhds (riemannZeta rho.1)) := by
    simpa [finiteCutoffOpenStripPointOfZero] using h
  rw [rho.2.1] at h'
  exact h'.congr
    (fun N => (finiteZetaFormationHead_add_continuationCorrection N rho.1).symm)

/-- Closed package: two separately defined processes escape in opposite normalized directions,
while their exact sum darkens at every nontrivial zero. -/
theorem finiteCutoffCompensatingInfinityAtZero_closed
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N : ℕ => ‖finiteZetaFormationHead N rho.1‖) atTop atTop ∧
      Tendsto (fun N : ℕ => ‖finiteCutoffContinuationCorrection N rho.1‖) atTop atTop ∧
      Tendsto (fun N : ℕ =>
        finiteCutoffNormalizer (finiteCutoffOpenStripPointOfZero rho) N *
          finiteZetaFormationHead N rho.1) atTop (nhds 1) ∧
      Tendsto (fun N : ℕ =>
        finiteCutoffNormalizer (finiteCutoffOpenStripPointOfZero rho) N *
          finiteCutoffContinuationCorrection N rho.1) atTop (nhds (-1)) ∧
      Tendsto (fun N : ℕ =>
        finiteZetaFormationHead N rho.1 + finiteCutoffContinuationCorrection N rho.1)
        atTop (nhds 0) := by
  exact ⟨tendsto_norm_finiteZetaFormationHead_atTop (finiteCutoffOpenStripPointOfZero rho),
    tendsto_norm_finiteCutoffContinuationCorrection_atTop
      (finiteCutoffOpenStripPointOfZero rho),
    tendsto_normalized_finiteZetaFormationHead (finiteCutoffOpenStripPointOfZero rho),
    tendsto_normalized_finiteCutoffContinuationCorrection
      (finiteCutoffOpenStripPointOfZero rho),
    tendsto_finiteZetaFormationHead_add_continuationCorrection_at_zero rho⟩

end RHTower.DeletionMixedRefinement
