import GaloisForLFunctions.RHTower.XiThermalProjectiveMomentSpectrum

/-!
# Cofinal cooling sections of the Xi thermal projective system

Finite KMS positivity and pointwise thermodynamic convergence leave a two-parameter cold/system-size
bound as an exact RH criterion.  Positivity also makes the finite partition values monotone in both
coordinates.  Consequently any one cofinal section through the product of system size and inverse
temperature detects the same critical value: boundedness along that single section is equivalent
to RH.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Enlarging the finite thermal system can only increase its positive cold partition value. -/
theorem xiThermalProjectiveColdTruncation_mono_size
    {N M k : ℕ} (hNM : N ≤ M) :
    xiThermalProjectiveColdTruncation N k ≤
      xiThermalProjectiveColdTruncation M k := by
  rw [xiThermalProjectiveColdTruncation, xiThermalProjectiveColdTruncation]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hNM) (fun j _ _ =>
      mul_nonneg (xiThermalNode_pos _).le (Real.exp_pos _).le)

/-- Cooling a fixed finite system can only increase the projective partition value. -/
theorem xiThermalProjectiveColdTruncation_mono_cold
    {N k l : ℕ} (hkl : k ≤ l) :
    xiThermalProjectiveColdTruncation N k ≤
      xiThermalProjectiveColdTruncation N l := by
  rw [xiThermalProjectiveColdTruncation, xiThermalProjectiveColdTruncation]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (xiThermalNode_pos _).le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hkl)
    (xiEndpointProjectiveReflectionDisplacement_nonneg _)

/-- Product-order monotonicity of the finite projective cold system. -/
theorem xiThermalProjectiveColdTruncation_mono
    {N M k l : ℕ} (hNM : N ≤ M) (hkl : k ≤ l) :
    xiThermalProjectiveColdTruncation N k ≤
      xiThermalProjectiveColdTruncation M l :=
  (xiThermalProjectiveColdTruncation_mono_size hNM).trans
    (xiThermalProjectiveColdTruncation_mono_cold hkl)

/-- **Cofinal cooling-section RH law.**  Let both the finite-system size and integer inverse
temperature tend to infinity along an arbitrary common schedule.  Eventual boundedness of the one
resulting scalar sequence is equivalent to RH. -/
theorem riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveCofinalSection
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤ C := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ :=
      riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition.mp
        hRH
    refine ⟨C, ?_⟩
    filter_upwards [hcold.eventually hC] with j hj
    exact
      (xiThermalProjectiveColdTruncation_le_partition (size j) (cold j)).trans hj
  · rintro ⟨C, hC⟩
    apply
      riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition.mpr
    refine ⟨C, Filter.Eventually.of_forall fun k => ?_⟩
    have ht := (tendsto_pi_nhds.mp
      tendsto_xiThermalProjectiveColdTruncation) k
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall fun N => by
      have hevent : ∀ᶠ j : ℕ in atTop,
          xiThermalProjectiveColdTruncation (size j) (cold j) ≤ C ∧
            N ≤ size j ∧ k ≤ cold j :=
        hC.and ((hsize.eventually_ge_atTop N).and
          (hcold.eventually_ge_atTop k))
      obtain ⟨j, hjC, hNj, hkj⟩ := hevent.exists
      exact (xiThermalProjectiveColdTruncation_mono hNj hkj).trans hjC

/-- **Off-line cofinal divergence law.**  If RH is false, every simultaneous thermodynamic and
zero-temperature section diverges to `+infinity`.  One off-line Xi atom is eventually present in
the finite system and its positive Boltzmann factor then grows exponentially along the cold
coordinate. -/
theorem thermalProjectiveCofinalSection_tendsto_atTop_of_not_riemannHypothesis
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop)
    (hnot : ¬ RiemannHypothesis) :
    Tendsto
      (fun j => xiThermalProjectiveColdTruncation (size j) (cold j))
      atTop atTop := by
  have hexists : ∃ q : XiZeroCopy,
      0 < xiEndpointProjectiveReflectionDisplacement q := by
    by_contra h
    push Not at h
    have hzero : xiThermalProjectiveMoment 1 = 0 := by
      rw [xiThermalProjectiveMoment]
      have hfun : (fun q : XiZeroCopy => xiThermalNode q *
          xiEndpointProjectiveReflectionDisplacement q ^ 1) = 0 := by
        funext q
        have hd : xiEndpointProjectiveReflectionDisplacement q = 0 :=
          le_antisymm (h q) (xiEndpointProjectiveReflectionDisplacement_nonneg q)
        simp [hd]
      rw [hfun]
      exact tsum_zero
    exact hnot (xiThermalProjectiveMoment_one_eq_zero_iff_rh.mp hzero)
  obtain ⟨q, hq⟩ := hexists
  obtain ⟨i, hi⟩ := xiThermalEnumeration_bijective.2 q
  let atom : ℕ → ℝ := fun j =>
    xiThermalNode q * Real.exp
      ((cold j : ℝ) * xiEndpointProjectiveReflectionDisplacement q)
  have hatom : Tendsto atom atTop atTop := by
    have hcast : Tendsto (fun j => (cold j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hcold
    have hscaled : Tendsto
        (fun j => (cold j : ℝ) * xiEndpointProjectiveReflectionDisplacement q)
        atTop atTop :=
      hcast.atTop_mul_const hq
    have hexp : Tendsto
        (fun j => Real.exp
          ((cold j : ℝ) * xiEndpointProjectiveReflectionDisplacement q))
        atTop atTop := by
      exact (Real.tendsto_exp_atTop.comp hscaled).congr'
        (Eventually.of_forall fun _ => rfl)
    simpa only [atom] using hexp.const_mul_atTop (xiThermalNode_pos q)
  have hatom_le : ∀ᶠ j : ℕ in atTop,
      atom j ≤ xiThermalProjectiveColdTruncation (size j) (cold j) := by
    filter_upwards [hsize.eventually_ge_atTop (i + 1)] with j hj
    rw [xiThermalProjectiveColdTruncation]
    have himem : i ∈ Finset.range (size j) := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum
      (f := fun m => xiThermalNode (xiThermalEnumeration m) *
        Real.exp ((cold j : ℝ) *
          xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration m)))
      (fun m _ => mul_nonneg (xiThermalNode_pos _).le (Real.exp_pos _).le)
      himem
    simpa only [atom, hi] using hsingle
  exact Filter.tendsto_atTop_mono' atTop hatom_le hatom

/-- Along any cofinal cooling section, divergence to `+infinity` is exactly the positive
alternative to RH. -/
theorem thermalProjectiveCofinalSection_tendsto_atTop_iff_not_riemannHypothesis
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    Tendsto
        (fun j => xiThermalProjectiveColdTruncation (size j) (cold j))
        atTop atTop ↔
      ¬ RiemannHypothesis := by
  constructor
  · intro hdiv hRH
    obtain ⟨C, hC⟩ :=
      (riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveCofinalSection
        size cold hsize hcold).mp hRH
    obtain ⟨j, hjle, hjgt⟩ :=
      (hC.and (hdiv.eventually_gt_atTop C)).exists
    exact (not_lt_of_ge hjle) hjgt
  · exact thermalProjectiveCofinalSection_tendsto_atTop_of_not_riemannHypothesis
      size cold hsize hcold

/-- **Frequently bounded cofinal-section RH law.**  Eventual uniformity is unnecessary.  It is
enough that one finite bound recurs cofinally often along any simultaneous thermodynamic/cold
schedule.  Under false RH the same sequence diverges, so no such recurrent bound can survive. -/
theorem riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveCofinalSection
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤ C := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ :=
      (riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveCofinalSection
        size cold hsize hcold).mp hRH
    exact ⟨C, hC.frequently⟩
  · rintro ⟨C, hC⟩
    by_contra hnot
    have hdiv :=
      thermalProjectiveCofinalSection_tendsto_atTop_of_not_riemannHypothesis
        size cold hsize hcold hnot
    obtain ⟨j, hjle, hjgt⟩ :=
      (hC.and_eventually (hdiv.eventually_gt_atTop C)).exists
    exact (not_lt_of_ge hjle) hjgt

/-- The simplest cofinal section is the diagonal: system size and inverse temperature both equal
the same integer.  One eventual bound on this single explicit sequence is already equivalent to
RH. -/
theorem riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveDiagonal :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation j j ≤ C := by
  simpa using
    (riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveCofinalSection
      id id tendsto_id tendsto_id)

/-- On the diagonal, a fixed upper bound need only recur cofinally often.  Equivalently, one
bounded subsequence of simultaneous finite-volume/zero-temperature values proves RH. -/
theorem riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveDiagonal :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation j j ≤ C := by
  simpa using
    (riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveCofinalSection
      id id tendsto_id tendsto_id)

/-- The exact Gamma-free fixed-window negative-source target is equivalent to boundedness along
the single diagonal sequence of finite projective thermal systems. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_eventually_bounded_thermalProjectiveDiagonal
    {L : ℝ} (hL : 0 < L) {N₀ : ℕ}
    (hN₀ : ∀ n : ℕ, N₀ ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N₀) ≤
        ((1 : ℝ) : EReal) ↔
      ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation j j ≤ C := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN₀).symm.trans
        riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveDiagonal

/-- **Weak diagonal finite-physics discharge.**  The critical Gamma-free source abscissa follows
as soon as one fixed bound recurs cofinally often along the diagonal finite thermal systems. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_frequently_bounded_thermalProjectiveDiagonal
    {L : ℝ} (hL : 0 < L) {N₀ : ℕ}
    (hN₀ : ∀ n : ℕ, N₀ ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N₀) ≤
        ((1 : ℝ) : EReal) ↔
      ∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation j j ≤ C := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN₀).symm.trans
        riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveDiagonal

end

end RHTower
