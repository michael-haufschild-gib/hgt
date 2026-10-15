import GaloisForLFunctions.RHTower.PrimeAlgebraicTranslationWeylPhase
import Mathlib.Analysis.Meromorphic.Order

/-!
# Xi-corrected transport at the prime rotation clock

Holomorphic scalar corrections of spectral translation preserve the principal Xi ideal at an
isolated zero only by annihilating its entire local quotient. The exact meromorphic correction
retains the prime Weyl relation, satisfies the source cocycle, and carries the signed difference
of Xi divisors. At a small native prime clock step this difference is an exact zero/pole dipole
with the original analytic multiplicity. The scalar correction therefore supplies meromorphic
transport, not a holomorphic automorphism of the local divisor quotient.
-/

open Filter Topology
namespace RHTower
noncomputable section

/-- Membership in the principal Xi ideal of holomorphic germs at `rho`. -/
def xiLocalMultiple (rho : ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧ f =ᶠ[𝓝 rho] (fun z => xi z * g z)

private theorem xiShift_analyticAt (t rho : ℂ) :
    AnalyticAt ℂ (fun z => xi (z + t)) rho :=
  (xi_analyticOnNhd_univ (rho + t) (Set.mem_univ _)).comp (f := fun z : ℂ => z + t)
    (analyticAt_id.add analyticAt_const)

/-- Away from the translated divisor, the conductor of scalar translation is exactly
    the original Xi ideal. -/
theorem xiScalarShift_conductor_iff (rho t : ℂ) (w : ℂ → ℂ)
    (ht : xi (rho + t) ≠ 0) :
    xiLocalMultiple rho (fun z => w z * xi (z + t)) ↔ xiLocalMultiple rho w := by
  constructor
  · rintro ⟨g, hg, he⟩
    refine ⟨fun z => g z / xi (z + t), hg.div (xiShift_analyticAt t rho) ht, ?_⟩
    have hn : ∀ᶠ z in 𝓝 rho, xi (z + t) ≠ 0 :=
      (xiShift_analyticAt t rho).continuousAt.eventually_ne ht
    filter_upwards [he, hn] with z hz hnz
    exact (eq_div_iff hnz).mpr hz |>.trans (mul_div_assoc _ _ _)
  · rintro ⟨g, hg, he⟩
    refine ⟨fun z => g z * xi (z + t), hg.mul (xiShift_analyticAt t rho), ?_⟩
    filter_upwards [he] with z hz
    rw [hz, mul_assoc]

/-- Every scalar correction that preserves the Xi ideal kills the entire local quotient. -/
theorem xiScalarShift_preserving_iff_annihilating (rho t : ℂ) (w : ℂ → ℂ)
    (ht : xi (rho + t) ≠ 0) :
    xiLocalMultiple rho (fun z => w z * xi (z + t)) ↔
      ∀ f : ℂ → ℂ, AnalyticAt ℂ f (rho + t) →
        xiLocalMultiple rho (fun z => w z * f (z + t)) := by
  constructor
  · intro h f hf
    obtain ⟨g, hg, he⟩ := (xiScalarShift_conductor_iff rho t w ht).mp h
    refine ⟨fun z => g z * f (z + t), hg.mul (hf.comp (f := fun z : ℂ => z + t) (analyticAt_id.add analyticAt_const)), ?_⟩
    filter_upwards [he] with z hz
    rw [hz, mul_assoc]
  · intro h
    exact h xi (xi_analyticOnNhd_univ _ (Set.mem_univ _))

/-- At a zero, the unit germ survives in the Xi quotient. -/
theorem not_xiLocalMultiple_one {rho : ℂ} (hrho : xi rho = 0) :
    ¬ xiLocalMultiple rho (fun _ => 1) := by
  rintro ⟨g, _, hg⟩
  have h := hg.self_of_nhds
  simp [hrho] at h

/-- A source-preserving scalar translation cannot recover even the unit class at a Xi zero. -/
theorem xiScalarShift_no_local_right_inverse {rho t : ℂ} (w : ℂ → ℂ)
    (hrho : xi rho = 0) (ht : xi (rho + t) ≠ 0)
    (hw : xiLocalMultiple rho (fun z => w z * xi (z + t))) :
    ¬ ∃ f : ℂ → ℂ, AnalyticAt ℂ f (rho + t) ∧
      xiLocalMultiple rho (fun z => w z * f (z + t) - 1) := by
  rintro ⟨f, hf, hunit⟩
  obtain ⟨g, _, hg⟩ := (xiScalarShift_preserving_iff_annihilating rho t w ht).mp hw f hf
  obtain ⟨h, _, hh⟩ := hunit
  have hz := hg.eq_of_nhds
  have hu := hh.eq_of_nhds
  simp only [hrho, zero_mul] at hz hu
  rw [hz] at hu
  norm_num at hu

/-- The meromorphic correction that transports the principal Xi factor. -/
def xiTranslationGauge (t : ℂ) (z : ℂ) : ℂ := xi z / xi (z + t)

private theorem meromorphicOrderAt_xi_nat (z : ℂ) :
    meromorphicOrderAt xi z = ((analyticOrderAt xi z).toNat : ℤ) := by
  rw [(xi_analyticOnNhd_univ z (Set.mem_univ _)).meromorphicOrderAt_eq,
    ← ENat.coe_toNat (xi_order_ne_top z)]
  rfl

private theorem xiShift_order (t z : ℂ) :
    meromorphicOrderAt (fun w => xi (w + t)) z = meromorphicOrderAt xi (z + t) := by
  have hd : deriv (fun w : ℂ => w + t) z = 1 := (hasDerivAt_id z |>.add_const t).deriv
  exact meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := xi) (g := fun w : ℂ => w + t) (x := z)
    (analyticAt_id.add analyticAt_const) (by rw [hd]; exact one_ne_zero)

private theorem xiShift_eventually_ne_zero (t z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, xi (w + t) ≠ 0 := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (xiShift_analyticAt t z).meromorphicAt).mp
  rw [xiShift_order, meromorphicOrderAt_xi_nat]
  exact WithTop.coe_ne_top

/-- The correction carries the exact signed difference of the two Xi divisors. -/
theorem xiTranslationGauge_order (t z : ℂ) :
    meromorphicOrderAt (xiTranslationGauge t) z =
      (((analyticOrderAt xi z).toNat : ℤ) -
        ((analyticOrderAt xi (z + t)).toNat : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt (xi / (fun w => xi (w + t))) z = _
  rw [meromorphicOrderAt_div
    (xi_analyticOnNhd_univ z (Set.mem_univ _)).meromorphicAt
    (xiShift_analyticAt t z).meromorphicAt, xiShift_order,
    meromorphicOrderAt_xi_nat, meromorphicOrderAt_xi_nat]

/-- The Xi gauge is meromorphic at every spectral point. -/
theorem xiTranslationGauge_meromorphicAt (t z : ℂ) :
    MeromorphicAt (xiTranslationGauge t) z :=
  (xi_analyticOnNhd_univ z (Set.mem_univ _)).meromorphicAt.div
    (xiShift_analyticAt t z).meromorphicAt

/-- Scalar Xi-corrected spectral transport. -/
def xiCorrectedTranslate (t : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  xiTranslationGauge t z * f (z + t)

/-- Meromorphic correction preserves the original prime Weyl multiplier exactly. -/
theorem xiCorrectedTranslate_primeEulerExpMultiply (p : ℕ) (t z : ℂ) (f : ℂ → ℂ) :
    xiCorrectedTranslate t (primeEulerExpMultiply p f) z =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * t) *
        primeEulerExpMultiply p (xiCorrectedTranslate t f) z := by
  have h := spectralTranslate_primeEulerExpMultiply p t z f
  change primeEulerExpMultiply p f (z + t) = _ at h
  unfold xiCorrectedTranslate
  rw [h]
  unfold primeEulerExpMultiply spectralTranslate
  ring

/-- The scalar transitions satisfy the cocycle identity off the intermediate divisor. -/
theorem xiTranslationGauge_cocycle (t u z : ℂ) (hz : xi (z + t) ≠ 0) :
    xiTranslationGauge t z * xiTranslationGauge u (z + t) =
      xiTranslationGauge (t + u) z := by
  unfold xiTranslationGauge
  rw [add_assoc]
  field_simp

/-- The Xi transitions obey the cocycle law as meromorphic germs at every point. -/
theorem xiTranslationGauge_cocycle_germ (t u z : ℂ) :
    (fun w => xiTranslationGauge t w * xiTranslationGauge u (w + t))
      =ᶠ[𝓝[≠] z] xiTranslationGauge (t + u) := by
  filter_upwards [xiShift_eventually_ne_zero t z] with w hw
  exact xiTranslationGauge_cocycle t u w hw

/-- Corrected transport carries the entire principal Xi factor without losing multiplicity. -/
theorem xiCorrectedTranslate_source_germ (t z : ℂ) (f : ℂ → ℂ) :
    xiCorrectedTranslate t (fun w => xi w * f w) =ᶠ[𝓝[≠] z]
      (fun w => xi w * f (w + t)) := by
  filter_upwards [xiShift_eventually_ne_zero t z] with w hw
  unfold xiCorrectedTranslate xiTranslationGauge
  field_simp

/-- Exact composition of meromorphic source transports. -/
theorem xiCorrectedTranslate_comp_germ (t u z : ℂ) (f : ℂ → ℂ) :
    xiCorrectedTranslate t (xiCorrectedTranslate u f) =ᶠ[𝓝[≠] z]
      xiCorrectedTranslate (t + u) f := by
  filter_upwards [xiTranslationGauge_cocycle_germ t u z] with w hw
  change xiTranslationGauge t w * (xiTranslationGauge u (w + t) * f (w + t + u)) = _
  rw [← mul_assoc, hw, add_assoc]
  rfl

/-- Every isolated Xi zero supplies an exact zero/pole dipole for small translations. -/
theorem xiTranslationGauge_isolated_dipole (rho : ℂ) :
    ∃ epsilon > 0, ∀ t : ℂ, t ≠ 0 → ‖t‖ < epsilon →
      xi (rho + t) ≠ 0 ∧ xi (rho - t) ≠ 0 ∧
      meromorphicOrderAt (xiTranslationGauge t) rho =
        ((analyticOrderAt xi rho).toNat : ℤ) ∧
      meromorphicOrderAt (xiTranslationGauge t) (rho - t) =
        (-((analyticOrderAt xi rho).toNat : ℤ) : WithTop ℤ) := by
  have hne : ∀ᶠ z in 𝓝[≠] rho, xi z ≠ 0 :=
    (xi_analyticOnNhd_univ rho (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => xi_order_ne_top rho (analyticOrderAt_eq_top.mpr h))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
  obtain ⟨epsilon, hepsilon, hne⟩ := hne
  refine ⟨epsilon, hepsilon, fun t ht hnorm => ?_⟩
  have hp : xi (rho + t) ≠ 0 := hne (by simpa [dist_eq_norm] using hnorm)
    (by simpa using ht)
  have hm : xi (rho - t) ≠ 0 := hne (by simpa [dist_eq_norm] using hnorm)
    (by simpa using ht)
  refine ⟨hp, hm, ?_, ?_⟩
  · rw [xiTranslationGauge_order, analyticOrderAt_eq_zero.mpr (Or.inr hp)]
    simp
  · rw [xiTranslationGauge_order, sub_add_cancel,
      analyticOrderAt_eq_zero.mpr (Or.inr hm)]
    simp

/-- At a genuine zero the transported pole has no holomorphic extension. -/
theorem xiTranslationGauge_no_holomorphic_extension {rho t : ℂ}
    (hrho : xi rho = 0) (ht : xi (rho - t) ≠ 0) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g (rho - t) ∧
      xiTranslationGauge t =ᶠ[𝓝[≠] (rho - t)] g := by
  rintro ⟨g, hg, he⟩
  have hord : meromorphicOrderAt (xiTranslationGauge t) (rho - t) =
      (-((analyticOrderAt xi rho).toNat : ℤ) : WithTop ℤ) := by
    rw [xiTranslationGauge_order, sub_add_cancel,
      analyticOrderAt_eq_zero.mpr (Or.inr ht)]
    simp
  have hnonneg := hg.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr he, hord] at hnonneg
  have hle : (0 : ℤ) ≤ -((analyticOrderAt xi rho).toNat : ℤ) := by
    exact_mod_cast hnonneg
  have hm := xi_order_toNat_ne_zero hrho
  omega

/-- A native rational-imaginary prime clock retains the exact Xi zero/pole charge,
    while every holomorphic scalar correction preserving the divisor has no local right inverse. -/
theorem xiPrimeClock_scalarRepairClassification {rho : ℂ} (hrho : xi rho = 0) :
    ∃ q : ℕ, 0 < q ∧
      (∀ w : ℂ → ℂ,
        xiLocalMultiple rho (fun z => w z * xi (z + primeAlgebraicClockStep q)) →
          ¬ ∃ f : ℂ → ℂ, AnalyticAt ℂ f (rho + primeAlgebraicClockStep q) ∧
            xiLocalMultiple rho (fun z => w z * f (z + primeAlgebraicClockStep q) - 1)) ∧
      meromorphicOrderAt (xiTranslationGauge (primeAlgebraicClockStep q)) rho =
        ((analyticOrderAt xi rho).toNat : ℤ) ∧
      meromorphicOrderAt (xiTranslationGauge (primeAlgebraicClockStep q))
        (rho - primeAlgebraicClockStep q) =
          (-((analyticOrderAt xi rho).toNat : ℤ) : WithTop ℤ) ∧
      ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g (rho - primeAlgebraicClockStep q) ∧
        xiTranslationGauge (primeAlgebraicClockStep q) =ᶠ[𝓝[≠] (rho - primeAlgebraicClockStep q)] g := by
  obtain ⟨epsilon, hepsilon, he⟩ := xiTranslationGauge_isolated_dipole rho
  obtain ⟨q, hq, hnorm⟩ := exists_primeAlgebraicClockStep_norm_lt hepsilon
  have hstep : primeAlgebraicClockStep q ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_primeAlgebraicClockStep]
    exact one_div_pos.mpr (by exact_mod_cast hq)
  obtain ⟨hp, hm, hzero, hpole⟩ := he (primeAlgebraicClockStep q) hstep hnorm
  exact ⟨q, hq, fun w hw => xiScalarShift_no_local_right_inverse w hrho hp hw,
    hzero, hpole, xiTranslationGauge_no_holomorphic_extension hrho hm⟩

end
end RHTower
