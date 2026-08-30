import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZParityLocalTemperedFEReflectionNoGo
import GaloisForLFunctions.RHTower.XiShiftedArcsineCenteredSourceWallNonintegrability

/-!
# No uniformly finite counterterm depth for all-grade FZZ parity reflection

The local FZZ parity functional-equation data already forces every natural Mellin grade.  Written
only in terms of the literal Fermi source, its grade-`n` reflected density is

`R_n(t) = t⁻¹^(n+1) / (exp t + 1)`.

This module classifies the exact counterterm depth at the ultraviolet endpoint.  If subtracting a
counterterm `C` makes grade `n` locally `L¹`, then `t^n C(t)` cannot have a finite right limit at
zero: the uncancelled density has the positive residue

`t^(n+1) (R_n(t) - C(t)) → 1/2`.

The bound is sharp.  A canonical analytic-coefficient counterterm has pole depth exactly `n+1`
and leaves the regular Fermi kernel.  Hence the required depth grows without bound with Mellin
grade.  No single finite pole bound can renormalize the full all-grade local reflection.

This kills the finite-renormalizable local-action branch of the FZZ-P chain

`literal parity source → all-grade reflection → finite local action → Ward equivariance → RH`.

It does not kill grade-dependent unbounded counterterm towers, distributional/Hadamard
completions, or genuinely nonlocal and channel-coupled dynamics.

`[FZZ-P ROUTE KILL] [SOURCE-PURE] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-- Literal FZZ parity functional-equation density at natural Mellin grade `n`. -/
def fzzCigarParityReflectedGradeDensity (n : ℕ) (t : ℝ) : ℝ :=
  t⁻¹ ^ (n + 1) * (Real.exp t + 1)⁻¹

/-- A counterterm has pole order at most `N` when multiplication by `t^N` has a finite right
limit at the ultraviolet endpoint.  The limit may depend on the counterterm and may vanish. -/
def FZZCigarParityFinitePoleOrderAtMost (C : ℝ → ℝ) (N : ℕ) : Prop :=
  ∃ L : ℝ, Tendsto (fun t : ℝ => t ^ N * C t) (𝓝[>] (0 : ℝ)) (𝓝 L)

/-- Local `L¹` renormalization of one reflected grade on some right neighborhood of zero. -/
def FZZCigarParityLocallyL1RenormalizesGrade (n : ℕ) (C : ℝ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    IntegrableOn (fun t => fzzCigarParityReflectedGradeDensity n t - C t) (Ioo 0 ε)

/-- A proposed all-grade local reflection action with one finite pole bound for every counterterm. -/
def FZZCigarParityUniformFiniteCountertermProducer : Prop :=
  ∃ (N : ℕ) (C : ℕ → ℝ → ℝ),
    (∀ n, FZZCigarParityFinitePoleOrderAtMost (C n) N) ∧
    ∀ n, FZZCigarParityLocallyL1RenormalizesGrade n (C n)

/-- The density used here is exactly the all-grade output forced by any local two-grade FZZ
functional-equation realization. -/
theorem FZZCigarParityLocalFEReflectionData.all_nat_grades_eq_reflectedGradeDensity
    (D : FZZCigarParityLocalFEReflectionData) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    D.weight t * D.energyMap t ^ n * fzzCigarParityDelay (D.energyMap t) =
      fzzCigarParityReflectedGradeDensity n t := by
  rw [D.all_nat_grades ht n, fzzCigarParityReflectedGradeDensity,
    fzzCigarParityDelay_eq_fermi ht]

/-- The regular Fermi germ has ultraviolet value `1/2`. -/
private theorem tendsto_fzzCigarFermi_nhdsGT_zero :
    Tendsto (fun t : ℝ => (Real.exp t + 1)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have h : Tendsto (fun t : ℝ => (Real.exp t + 1)⁻¹)
      (𝓝 (0 : ℝ)) (𝓝 ((Real.exp 0 + 1)⁻¹)) :=
    ((Real.continuous_exp.add continuous_const).inv₀ (fun x => by
      change Real.exp x + 1 ≠ 0
      positivity)).continuousAt
  simpa only [Real.exp_zero, one_add_one_eq_two, inv_eq_one_div] using
    tendsto_nhdsWithin_of_tendsto_nhds h

/-- **Uncancelled residue law.**  A counterterm of order at most `N` leaves the strictly positive
order-`N+1` residue `1/2` in grade `N`. -/
theorem tendsto_fzzCigarParityReflectedGradeDensity_sub_counterterm_scaled
    (N : ℕ) (C : ℝ → ℝ) (hC : FZZCigarParityFinitePoleOrderAtMost C N) :
    Tendsto (fun t : ℝ => t ^ (N + 1) *
      (fzzCigarParityReflectedGradeDensity N t - C t))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  obtain ⟨L, hL⟩ := hC
  have hzero : Tendsto (fun t : ℝ => t * (t ^ N * C t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul hL
  have heq :
      (fun t : ℝ => t ^ (N + 1) *
          (fzzCigarParityReflectedGradeDensity N t - C t)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => (Real.exp t + 1)⁻¹ - t * (t ^ N * C t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hp : t ^ (N + 1) * t⁻¹ ^ (N + 1) = 1 := by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ ht0)]
    rw [fzzCigarParityReflectedGradeDensity]
    calc
      t ^ (N + 1) *
          (t⁻¹ ^ (N + 1) * (Real.exp t + 1)⁻¹ - C t) =
          (t ^ (N + 1) * t⁻¹ ^ (N + 1)) * (Real.exp t + 1)⁻¹ -
            t ^ (N + 1) * C t := by ring
      _ = (Real.exp t + 1)⁻¹ - t * (t ^ N * C t) := by
        rw [hp, one_mul, pow_succ]
        ring
  simpa using (tendsto_fzzCigarFermi_nhdsGT_zero.sub hzero).congr' heq.symm

/-- **Exact per-grade lower bound.**  Any counterterm that makes grade `n` locally `L¹` has pole
depth strictly greater than `n`. -/
theorem not_fzzCigarParityFinitePoleOrderAtMost_of_locallyL1RenormalizesGrade
    (n : ℕ) (C : ℝ → ℝ) (hI : FZZCigarParityLocallyL1RenormalizesGrade n C) :
    ¬ FZZCigarParityFinitePoleOrderAtMost C n := by
  intro hC
  obtain ⟨ε, hε, hI⟩ := hI
  exact not_integrableOn_Ioo_of_tendsto_natPow_mul_pos (Nat.succ_pos n)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (tendsto_fzzCigarParityReflectedGradeDensity_sub_counterterm_scaled n C hC) hε hI

/-- Canonical source-local subtraction: it removes exactly the grade pole and leaves the regular
Fermi kernel. -/
def fzzCigarParityCanonicalGradeCounterterm (n : ℕ) (t : ℝ) : ℝ :=
  (t⁻¹ ^ (n + 1) - 1) * (Real.exp t + 1)⁻¹

/-- Canonical subtraction leaves the regular Fermi density pointwise. -/
theorem fzzCigarParityCanonicalGradeCounterterm_residual (n : ℕ) (t : ℝ) :
    fzzCigarParityReflectedGradeDensity n t -
      fzzCigarParityCanonicalGradeCounterterm n t = (Real.exp t + 1)⁻¹ := by
  simp only [fzzCigarParityReflectedGradeDensity, fzzCigarParityCanonicalGradeCounterterm]
  ring

/-- The canonical grade counterterm really gives a local `L¹` remainder. -/
theorem fzzCigarParityCanonicalGradeCounterterm_locallyL1 (n : ℕ) :
    FZZCigarParityLocallyL1RenormalizesGrade n
      (fzzCigarParityCanonicalGradeCounterterm n) := by
  refine ⟨1, zero_lt_one, ?_⟩
  have hcont : Continuous (fun t : ℝ => (Real.exp t + 1)⁻¹) :=
    (Real.continuous_exp.add continuous_const).inv₀ (fun x => by
      change Real.exp x + 1 ≠ 0
      positivity)
  have hint : IntegrableOn (fun t : ℝ => (Real.exp t + 1)⁻¹) (Icc 0 1) :=
    hcont.integrableOn_Icc
  refine (hint.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
  intro t _
  exact (fzzCigarParityCanonicalGradeCounterterm_residual n t).symm

/-- The canonical grade-`n` counterterm has pole order at most `n+1`, with nonzero scaled limit
`1/2`. -/
theorem fzzCigarParityCanonicalGradeCounterterm_order_succ (n : ℕ) :
    FZZCigarParityFinitePoleOrderAtMost
      (fzzCigarParityCanonicalGradeCounterterm n) (n + 1) := by
  refine ⟨1 / 2, ?_⟩
  have hone : Tendsto (fun t : ℝ => 1 - t ^ (n + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
      tendsto_const_nhds
    have hp : Tendsto (fun t : ℝ => t ^ (n + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ (n + 1))) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).pow (n + 1)
    simpa using hc.sub hp
  have heq :
      (fun t : ℝ => t ^ (n + 1) *
          fzzCigarParityCanonicalGradeCounterterm n t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => (1 - t ^ (n + 1)) * (Real.exp t + 1)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hp : t ^ (n + 1) * t⁻¹ ^ (n + 1) = 1 := by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ ht0)]
    rw [fzzCigarParityCanonicalGradeCounterterm]
    calc
      t ^ (n + 1) * ((t⁻¹ ^ (n + 1) - 1) * (Real.exp t + 1)⁻¹) =
          (t ^ (n + 1) * t⁻¹ ^ (n + 1) - t ^ (n + 1)) *
            (Real.exp t + 1)⁻¹ := by ring
      _ = (1 - t ^ (n + 1)) * (Real.exp t + 1)⁻¹ := by rw [hp]
  simpa using (hone.mul tendsto_fzzCigarFermi_nhdsGT_zero).congr' heq.symm

/-- **Sharp per-grade classification.**  At every grade `n`, depth `n+1` is attainable and depth
`n` is impossible for a locally `L¹` subtraction. -/
theorem exists_fzzCigarParity_exactCountertermDepth_everyGrade :
    ∀ n : ℕ, ∃ C : ℝ → ℝ,
      FZZCigarParityLocallyL1RenormalizesGrade n C ∧
      FZZCigarParityFinitePoleOrderAtMost C (n + 1) ∧
      ¬ FZZCigarParityFinitePoleOrderAtMost C n := by
  intro n
  refine ⟨fzzCigarParityCanonicalGradeCounterterm n,
    fzzCigarParityCanonicalGradeCounterterm_locallyL1 n,
    fzzCigarParityCanonicalGradeCounterterm_order_succ n, ?_⟩
  exact not_fzzCigarParityFinitePoleOrderAtMost_of_locallyL1RenormalizesGrade n _
    (fzzCigarParityCanonicalGradeCounterterm_locallyL1 n)

/-- **Unbounded-depth law.**  Every all-grade locally `L¹` counterterm family escapes each proposed
finite common pole bound, already at the grade equal to that bound. -/
theorem fzzCigarParity_countertermPoleDepth_unbounded
    (C : ℕ → ℝ → ℝ)
    (hlocal : ∀ n, FZZCigarParityLocallyL1RenormalizesGrade n (C n)) (N : ℕ) :
    ∃ n : ℕ, ¬ FZZCigarParityFinitePoleOrderAtMost (C n) N := by
  exact ⟨N, not_fzzCigarParityFinitePoleOrderAtMost_of_locallyL1RenormalizesGrade N (C N)
    (hlocal N)⟩

/-- **FZZ-P finite-action route kill.**  No all-grade local reflection producer can have one
uniformly finite counterterm pole bound. -/
theorem not_fzzCigarParityUniformFiniteCountertermProducer :
    ¬ FZZCigarParityUniformFiniteCountertermProducer := by
  rintro ⟨N, C, hfinite, hlocal⟩
  exact not_fzzCigarParityFinitePoleOrderAtMost_of_locallyL1RenormalizesGrade N (C N)
    (hlocal N) (hfinite N)

end

end RHTower
