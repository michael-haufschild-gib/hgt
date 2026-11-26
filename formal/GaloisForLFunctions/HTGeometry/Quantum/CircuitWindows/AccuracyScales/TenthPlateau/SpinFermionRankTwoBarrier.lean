import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HiddenRotatedIsingTube
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations

/-! # `U(2)^⊗N`-invariant bond rank-`2` conditioning and `Spin(N)` free-fermion synthesis

This module resolves the gauge-invariant post-`(N - 1)` complexity hierarchy beyond locally rotated
Ising chains on the `1`D `N = n + 2` qubit Pauli chain, abstracting all skew-pair rotations,
adjacent Givens `SO(m)` factorizations, and Clifford even-subspace commutant rigidity over general
dimension `m` and `C*`-algebras `{A : Type*} [CStarAlgebra A]`:

1. **`U(2)^⊗N`-gauge-invariant bond rank-`2` conditioning `Ω_rank2(n, η)`:**
   - `bondRankTwoEvent_compl_prob_le`: pivot-conditioned product-Gaussian failure bound
     `ℙ(Ω_rank2(n, η)ᶜ) ≤ (n + 1) * (r ^ 9 + 9 * (η ^ 2 / r) ^ 4)` for all `r > 0`, specializing
     at `r = √η` (`η ∈ [0, 1]`) to `≤ 10 * (n + 1) * (√η) ^ 9`.
   - `locallyRotatedIsing_operator_dist_ge_of_bondMinor`: `bondMinorInvariant (bondMatrix u e)`
     lower-bounds `9 * frobSq3 (bondMatrix u e) * ‖H(u) - W H_diag W*‖²` uniformly across **every**
     local unitary product `W = prodLocalMatrix R ∈ U(2)^⊗N` and **every** diagonal chain `v`.
2. **Abstract `SO(m)` adjacent-Givens synthesis and Clifford even-subspace commutant rigidity:**
   - `exists_adjGivens_prod_eq_of_specialOrthogonal`: every `O ∈ SO(m)` factors into at most
     `m * (m - 1) / 2` elementary adjacent Givens rotations `adjGivens m e φ` (`e + 1 < m`).
   - `eq_scalar_one_of_mem_evenClifford_commutant`: over any nontrivial `C*`-algebra `A`, every
     unitary `W ∈ evenCliffordSubspace γ` commuting with all Clifford generators `γ_c` is a
     unit-modulus scalar `z • 1`.
3. **Exact `choose(N, 2)`-gate `Spin(N)` compilation and Jordan-Wigner survival tube:**
   - `realizes_choose_two_of_alternatingJWChain`: every alternating `ZZ / XX` chain Hamiltonian on
     `n + 2` qubits is compiled **exactly** for all `t ∈ ℝ` in `(n + 2) * (n + 1) / 2` two-qubit
     gates via the `Spin(n + 2) → SO(n + 2)` Majorana representation.
   - `gaussian_alternatingJW_tube_tail`: inside `nonCommutingBondEvent (k + 1) η`, an event of
     probability `≥ c_JW(k, η) * T ^ -(11 * k + 25)` simultaneously exhibits maximally projective
     simple spectrum, full `2^N` Vandermonde rank on `[0, 1]`, and `√2` scalar-return excision
     while surviving `T < tenthPlateauOnset H s` for all `(k + 3) * (k + 2) / 2 ≤ s ≤ P`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev Realizes {n : ℕ} := @DiagonalSynthesis.Realizes n

/-! ## Section 1: `U(2)^⊗N`-invariant bond rank-`2` conditioning `Ω_rank2(n, η)` -/

/-- `3 × 3` bond coupling matrix `B_e(u)` of a chain shell `u : PathShell n` on bond `e`. -/
def bondMatrix {n : ℕ} (u : PathShell n) (e : Fin (n + 1)) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun p q => u (.inr (e, (p, q)))

/-- `3 × 3` bond coupling matrix read from `x : PrefixIndex n → ℝ` on bond `e`. -/
def bondMatrixOfPrefix (n : ℕ) (x : PrefixIndex n → ℝ) (e : Fin (n + 1)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun p q => x ((pathCoeffEquiv n).symm (.inr (e, (p, q))))

/-- `U(2)^⊗N`-gauge-invariant bond rank-`2` bulk event `Ω_rank2(n, η)`: every bond `e` has
`η ^ 4 ≤ bondMinorInvariant (bondMatrixOfPrefix n x e)`. -/
def bondRankTwoEvent (n : ℕ) (η : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | ∀ e : Fin (n + 1), η ^ 4 ≤ bondMinorInvariant (bondMatrixOfPrefix n x e)}

private theorem gaussianReal_Icc_shifted_le (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussianReal 0 1).real (Icc (c - δ) (c + δ)) ≤ δ := by
  have h1 : (gaussianReal 0 1) (Icc (c - δ) (c + δ)) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume (Icc (c - δ) (c + δ)) := by
    rw [gaussianReal_apply 0 (by norm_num) _, ← setLIntegral_const]
    refine setLIntegral_mono_ae (by fun_prop) ?_
    filter_upwards with t _
    rw [gaussianPDF]
    apply ENNReal.ofReal_le_ofReal
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))
  have hlen : c + δ - (c - δ) = 2 * δ := by ring
  rw [Real.volume_Icc, hlen, ← ENNReal.ofReal_mul (by positivity)] at h1
  have hsqrt_ge2 : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    Real.le_sqrt_of_sq_le (by linarith only [Real.pi_gt_three])
  have hinv_le : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 / 2 :=
    one_div (Real.sqrt (2 * Real.pi)) ▸ one_div_le_one_div_of_le two_pos hsqrt_ge2
  have hprod_le : (Real.sqrt (2 * Real.pi))⁻¹ * (2 * δ) ≤ δ := by
    nlinarith only [hinv_le, hδ]
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal hδ (h1.trans (ENNReal.ofReal_le_ofReal hprod_le))

private theorem nine_gaussian_bondMinor_lt_prob_le {η r : ℝ} (_hη : 0 ≤ η) (hr : 0 < r) :
    (Measure.pi fun _ : Fin 3 × Fin 3 => gaussianReal 0 1).real
      {b : Fin 3 × Fin 3 → ℝ | bondMinorInvariant (fun p q => b (p, q)) < η ^ 4} ≤
      r ^ 9 + 9 * (η ^ 2 / r) ^ 4 := by
  let γ := gaussianReal 0 1
  let μ₉ := Measure.pi fun _ : Fin 3 × Fin 3 => γ
  haveI : IsProbabilityMeasure μ₉ := by dsimp only [μ₉]; infer_instance
  let Small9 : Set (Fin 3 × Fin 3 → ℝ) := {b | ∀ pq : Fin 3 × Fin 3, |b pq| < r}
  have hSmall_prob : μ₉.real Small9 ≤ r ^ 9 := by
    have hsub : Small9 ⊆ {b : Fin 3 × Fin 3 → ℝ |
        ∃ u ∈ ({()} : Finset Unit), ∀ pq ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), |b pq| < r} :=
      fun b hb => ⟨(), Finset.mem_singleton_self (), fun pq _ => hb pq⟩
    have hb := (pi_smallCube_union_prob_le ({()} : Finset Unit)
      (fun _ => (Finset.univ : Finset (Fin 3 × Fin 3))) 9 (fun _ _ => by decide) hr.le).2
    simp only [Finset.card_singleton, Nat.cast_one, one_mul] at hb
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans hb
  let PivSet (pq₀ : Fin 3 × Fin 3) : Set (Fin 3 × Fin 3 → ℝ) :=
    {b | r ≤ |b pq₀| ∧ ∀ p q : Fin 3, p ≠ pq₀.1 → q ≠ pq₀.2 →
      |b pq₀ * b (p, q) - b (pq₀.1, q) * b (p, pq₀.2)| ≤ η ^ 2}
  have hcov : {b : Fin 3 × Fin 3 → ℝ | bondMinorInvariant (fun p q => b (p, q)) < η ^ 4} ⊆
      Small9 ∪ ⋃ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), PivSet pq₀ := by
    intro b hlt
    by_cases hall_lt : ∀ pq : Fin 3 × Fin 3, |b pq| < r
    · exact Or.inl hall_lt
    · right
      push Not at hall_lt
      obtain ⟨pq₀, hpq₀⟩ := hall_lt
      refine mem_iUnion₂.mpr ⟨pq₀, Finset.mem_univ pq₀, hpq₀, fun p q hp hq => ?_⟩
      let p₁ := min p pq₀.1
      let p₂ := max p pq₀.1
      let q₁ := min q pq₀.2
      let q₂ := max q pq₀.2
      have hp_lt : p₁ < p₂ := by
        rcases lt_or_gt_of_ne hp with h | h
        · simp [p₁, p₂, min_eq_left h.le, max_eq_right h.le, h]
        · simp [p₁, p₂, min_eq_right h.le, max_eq_left h.le, h]
      have hq_lt : q₁ < q₂ := by
        rcases lt_or_gt_of_ne hq with h | h
        · simp [q₁, q₂, min_eq_left h.le, max_eq_right h.le, h]
        · simp [q₁, q₂, min_eq_right h.le, max_eq_left h.le, h]
      have hsq_eq : (b (p₁, q₁) * b (p₂, q₂) - b (p₁, q₂) * b (p₂, q₁)) ^ 2 =
          (b pq₀ * b (p, q) - b (pq₀.1, q) * b (p, pq₀.2)) ^ 2 := by
        rcases lt_or_gt_of_ne hp with hp1 | hp2 <;> rcases lt_or_gt_of_ne hq with hq1 | hq2
        · simp only [p₁, p₂, q₁, q₂, min_eq_left hp1.le, max_eq_right hp1.le,
            min_eq_left hq1.le, max_eq_right hq1.le]; ring
        · simp only [p₁, p₂, q₁, q₂, min_eq_left hp1.le, max_eq_right hp1.le,
            min_eq_right hq2.le, max_eq_left hq2.le]; ring
        · simp only [p₁, p₂, q₁, q₂, min_eq_right hp2.le, max_eq_left hp2.le,
            min_eq_left hq1.le, max_eq_right hq1.le]; ring
        · simp only [p₁, p₂, q₁, q₂, min_eq_right hp2.le, max_eq_left hp2.le,
            min_eq_right hq2.le, max_eq_left hq2.le]
      have hsingle_le : (b (p₁, q₁) * b (p₂, q₂) - b (p₁, q₂) * b (p₂, q₁)) ^ 2 ≤
          bondMinorInvariant (fun p' q' => b (p', q')) := by
        unfold bondMinorInvariant
        have h1 : (if p₁ < p₂ ∧ q₁ < q₂ then
            (b (p₁, q₁) * b (p₂, q₂) - b (p₁, q₂) * b (p₂, q₁)) ^ 2 else 0) ≤
            ∑ q' : Fin 3 × Fin 3, if p₁ < p₂ ∧ q'.1 < q'.2 then
              (b (p₁, q'.1) * b (p₂, q'.2) - b (p₁, q'.2) * b (p₂, q'.1)) ^ 2 else 0 :=
          Finset.single_le_sum
            (f := fun q' : Fin 3 × Fin 3 => if p₁ < p₂ ∧ q'.1 < q'.2 then
              (b (p₁, q'.1) * b (p₂, q'.2) - b (p₁, q'.2) * b (p₂, q'.1)) ^ 2 else 0)
            (fun q' _ => by split_ifs; exact sq_nonneg _; exact le_rfl)
            (Finset.mem_univ (q₁, q₂))
        have h2 : (∑ q' : Fin 3 × Fin 3, if p₁ < p₂ ∧ q'.1 < q'.2 then
            (b (p₁, q'.1) * b (p₂, q'.2) - b (p₁, q'.2) * b (p₂, q'.1)) ^ 2 else 0) ≤
            bondMinorInvariant (fun p' q' => b (p', q')) :=
          Finset.single_le_sum
            (f := fun p' : Fin 3 × Fin 3 => ∑ q' : Fin 3 × Fin 3, if p'.1 < p'.2 ∧ q'.1 < q'.2 then
              (b (p'.1, q'.1) * b (p'.2, q'.2) - b (p'.1, q'.2) * b (p'.2, q'.1)) ^ 2 else 0)
            (fun p' _ => Finset.sum_nonneg fun q' _ => by split_ifs; exact sq_nonneg _; exact le_rfl)
            (Finset.mem_univ (p₁, p₂))
        rw [if_pos ⟨hp_lt, hq_lt⟩] at h1
        exact h1.trans h2
      have hsq_lt : |b pq₀ * b (p, q) - b (pq₀.1, q) * b (p, pq₀.2)| ^ 2 ≤ (η ^ 2) ^ 2 := by
        rw [sq_abs, ← hsq_eq]
        exact (hsingle_le.trans hlt.le).trans_eq (by ring)
      exact (sq_le_sq₀ (abs_nonneg _) (sq_nonneg η)).mp hsq_lt
  have hpiv_prob (pq₀ : Fin 3 × Fin 3) : μ₉.real (PivSet pq₀) ≤ (η ^ 2 / r) ^ 4 := by
    let Comp : Fin 3 × Fin 3 → Prop := fun pq => pq.1 ≠ pq₀.1 ∧ pq.2 ≠ pq₀.2
    have hcard_comp : @Fintype.card (Subtype Comp) (Subtype.fintype Comp) = 4 := by
      rcases pq₀ with ⟨p₀, q₀⟩
      fin_cases p₀ <;> fin_cases q₀ <;> decide
    have hPiv_meas : MeasurableSet (PivSet pq₀) := by
      have hm1 : MeasurableSet {b : Fin 3 × Fin 3 → ℝ | r ≤ |b pq₀|} :=
        measurableSet_le measurable_const (continuous_abs.measurable.comp (measurable_pi_apply pq₀))
      let S_comp : Finset (Fin 3 × Fin 3) :=
        Finset.univ.filter fun pq : Fin 3 × Fin 3 => pq.1 ≠ pq₀.1 ∧ pq.2 ≠ pq₀.2
      have heq2 : {b : Fin 3 × Fin 3 → ℝ | ∀ p q : Fin 3, p ≠ pq₀.1 → q ≠ pq₀.2 →
          |b pq₀ * b (p, q) - b (pq₀.1, q) * b (p, pq₀.2)| ≤ η ^ 2} =
          ⋂ pq ∈ S_comp, {b : Fin 3 × Fin 3 → ℝ |
            |b pq₀ * b pq - b (pq₀.1, pq.2) * b (pq.1, pq₀.2)| ≤ η ^ 2} := by
        ext b
        simp only [mem_setOf_eq, mem_iInter, S_comp, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.forall, and_imp]
      change MeasurableSet ({b | r ≤ |b pq₀|} ∩ {b : Fin 3 × Fin 3 → ℝ |
        ∀ p q : Fin 3, p ≠ pq₀.1 → q ≠ pq₀.2 →
          |b pq₀ * b (p, q) - b (pq₀.1, q) * b (p, pq₀.2)| ≤ η ^ 2})
      refine hm1.inter ?_
      rw [heq2]
      refine MeasurableSet.biInter S_comp.countable_toSet fun pq _ => ?_
      exact measurableSet_le
        (continuous_abs.measurable.comp
          (((measurable_pi_apply pq₀).mul (measurable_pi_apply pq)).sub
            ((measurable_pi_apply (pq₀.1, pq.2)).mul (measurable_pi_apply (pq.1, pq₀.2)))))
        measurable_const
    let e_sp := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin 3 × Fin 3 => ℝ) Comp
    have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin 3 × Fin 3 => γ) Comp
    let μ_c := @Measure.pi (Subtype Comp) (fun _ => ℝ) (Subtype.fintype Comp) _ (fun _ => γ)
    let μ_r := @Measure.pi {pq : Fin 3 × Fin 3 // ¬ Comp pq} (fun _ => ℝ)
      (Subtype.fintype fun pq => ¬ Comp pq) _ (fun _ => γ)
    have hmeas_eq : μ₉ (PivSet pq₀) = (μ_c.prod μ_r) (e_sp.symm ⁻¹' PivSet pq₀) := by
      rw [← hmp.measure_preimage (e_sp.symm.measurable hPiv_meas).nullMeasurableSet]
      congr 1; ext b; change b ∈ PivSet pq₀ ↔ e_sp.symm (e_sp b) ∈ PivSet pq₀
      rw [e_sp.symm_apply_apply]
    have hprod_eval : (μ_c.prod μ_r) (e_sp.symm ⁻¹' PivSet pq₀) =
        ∫⁻ z, μ_c {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ PivSet pq₀} ∂μ_r :=
      Measure.prod_apply_symm (e_sp.symm.measurable hPiv_meas)
    let δ' := η ^ 2 / r
    have hδ'_nn : 0 ≤ δ' := div_nonneg (sq_nonneg η) hr.le
    have hsec_le (z : {pq : Fin 3 × Fin 3 // ¬ Comp pq} → ℝ) :
        μ_c {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ PivSet pq₀} ≤
          ENNReal.ofReal (δ' ^ 4) := by
      have hpiv_not : ¬ Comp pq₀ := fun h => h.1 rfl
      let z₀ := z ⟨pq₀, hpiv_not⟩
      by_cases hz₀ : r ≤ |z₀|
      · have hz₀_abs_pos : 0 < |z₀| := hr.trans_le hz₀
        have hz₀_ne : z₀ ≠ 0 := abs_pos.mp hz₀_abs_pos
        let center (u : Subtype Comp) : ℝ :=
          (z ⟨(pq₀.1, u.1.2), fun h => h.1 rfl⟩ * z ⟨(u.1.1, pq₀.2), fun h => h.2 rfl⟩) / z₀
        have hsub_box : {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ PivSet pq₀} ⊆
            Set.univ.pi fun u : Subtype Comp => Icc (center u - δ') (center u + δ') := by
          intro w ⟨_, hcond⟩ u _
          have h1 := hcond u.1.1 u.1.2 u.2.1 u.2.2
          have heval_piv : e_sp.symm (w, z) pq₀ = z₀ := by
            simp [e_sp, z₀, hpiv_not, MeasurableEquiv.piEquivPiSubtypeProd]
          have heval_u : e_sp.symm (w, z) u.1 = w u := by
            simp [e_sp, u.2, MeasurableEquiv.piEquivPiSubtypeProd]
          have hnot_row : ¬ Comp (pq₀.1, u.1.2) := fun h => h.1 rfl
          have hnot_col : ¬ Comp (u.1.1, pq₀.2) := fun h => h.2 rfl
          have heval_row : e_sp.symm (w, z) (pq₀.1, u.1.2) = z ⟨(pq₀.1, u.1.2), hnot_row⟩ := by
            simp [e_sp, hnot_row, MeasurableEquiv.piEquivPiSubtypeProd]
          have heval_col : e_sp.symm (w, z) (u.1.1, pq₀.2) = z ⟨(u.1.1, pq₀.2), hnot_col⟩ := by
            simp [e_sp, hnot_col, MeasurableEquiv.piEquivPiSubtypeProd]
          rw [heval_piv, heval_u, heval_row, heval_col] at h1
          have hdiff : |w u - center u| ≤ δ' := by
            have hid : w u - center u =
                (z₀ * w u - z ⟨(pq₀.1, u.1.2), hnot_row⟩ * z ⟨(u.1.1, pq₀.2), hnot_col⟩) / z₀ := by
              dsimp [center]; field_simp [hz₀_ne]
            rw [hid, abs_div]
            exact (div_le_div_of_nonneg_right h1 hz₀_abs_pos.le).trans
              (div_le_div_of_nonneg_left (sq_nonneg η) hr hz₀)
          have hbd := abs_le.mp hdiff
          exact ⟨by linarith only [hbd.1], by linarith only [hbd.2]⟩
        calc μ_c {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ PivSet pq₀}
            ≤ μ_c (Set.univ.pi fun u : Subtype Comp => Icc (center u - δ') (center u + δ')) :=
              measure_mono hsub_box
          _ = ∏ u : Subtype Comp, γ (Icc (center u - δ') (center u + δ')) := by
              dsimp only [μ_c]
              exact @Measure.pi_pi (Subtype Comp) (fun _ => ℝ) (Subtype.fintype Comp) _ (fun _ => γ) _ _
          _ ≤ ∏ _u : Subtype Comp, ENNReal.ofReal δ' := by
              refine Finset.prod_le_prod' fun u _ => ?_
              rw [← ENNReal.ofReal_toReal (measure_ne_top γ _)]
              exact ENNReal.ofReal_le_ofReal (gaussianReal_Icc_shifted_le (center u) hδ'_nn)
          _ = ENNReal.ofReal (δ' ^ 4) := by
              rw [Finset.prod_const, Finset.card_univ, hcard_comp, ENNReal.ofReal_pow hδ'_nn]
      · have hemp : {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ PivSet pq₀} = ∅ := by
          ext w; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
          rintro ⟨h1, _⟩
          have heval_piv : e_sp.symm (w, z) pq₀ = z₀ := by
            simp [e_sp, z₀, hpiv_not, MeasurableEquiv.piEquivPiSubtypeProd]
          rw [heval_piv] at h1
          exact hz₀ h1
        rw [hemp, measure_empty]; simp
    have htot : μ₉ (PivSet pq₀) ≤ ENNReal.ofReal (δ' ^ 4) := by
      rw [hmeas_eq, hprod_eval]
      refine (lintegral_mono hsec_le).trans ?_
      haveI : IsProbabilityMeasure μ_r := by dsimp only [μ_r]; infer_instance
      rw [lintegral_const, measure_univ, mul_one]
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (pow_nonneg hδ'_nn 4) htot
  calc μ₉.real {b : Fin 3 × Fin 3 → ℝ | bondMinorInvariant (fun p q => b (p, q)) < η ^ 4}
      ≤ μ₉.real (Small9 ∪ ⋃ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), PivSet pq₀) :=
          measureReal_mono hcov (measure_ne_top _ _)
    _ ≤ μ₉.real Small9 +
          μ₉.real (⋃ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), PivSet pq₀) :=
          measureReal_union_le _ _
    _ ≤ r ^ 9 + ∑ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), μ₉.real (PivSet pq₀) :=
          add_le_add hSmall_prob (measureReal_biUnion_finset_le _ _)
    _ ≤ r ^ 9 + ∑ _pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), (η ^ 2 / r) ^ 4 :=
          add_le_add le_rfl (Finset.sum_le_sum fun pq₀ _ => hpiv_prob pq₀)
    _ = r ^ 9 + 9 * (η ^ 2 / r) ^ 4 := by
          have hc9 : (Finset.univ : Finset (Fin 3 × Fin 3)).card = 9 := by decide
          rw [Finset.sum_const, hc9, nsmul_eq_mul]; norm_num

/-- Sharp product-Gaussian failure bound for the `U(2)^⊗N`-invariant bond rank-`2` event
`bondRankTwoEvent n η`:
1. For every `η ≥ 0` and pivot scale `r > 0`,
   `ℙ(Ω_rank2(n, η)ᶜ) ≤ (n + 1) * (r ^ 9 + 9 * (η ^ 2 / r) ^ 4)`.
2. For every `η ∈ [0, 1]`, setting `r = √η` gives
   `ℙ(Ω_rank2(n, η)ᶜ) ≤ 10 * (n + 1) * (√η) ^ 9`. -/
theorem bondRankTwoEvent_compl_prob_le (n : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (∀ r > 0,
      (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real (bondRankTwoEvent n η)ᶜ ≤
        ((n + 1 : ℕ) : ℝ) * (r ^ 9 + 9 * (η ^ 2 / r) ^ 4)) ∧
    (η ≤ 1 →
      (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real (bondRankTwoEvent n η)ᶜ ≤
        (10 * (n + 1 : ℕ) : ℝ) * (Real.sqrt η) ^ 9) := by
  let γ := gaussianReal 0 1
  let μ := Measure.pi fun _ : PrefixIndex n => γ
  haveI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hmeas_lt : MeasurableSet {b : Fin 3 × Fin 3 → ℝ |
      bondMinorInvariant (fun p q => b (p, q)) < η ^ 4} := by
    have hcont : Continuous fun b : Fin 3 × Fin 3 → ℝ =>
        bondMinorInvariant (fun p q => b (p, q)) := by
      unfold bondMinorInvariant
      refine continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_
      by_cases h : p.1 < p.2 ∧ q.1 < q.2
      · simp only [if_pos h]
        exact (((continuous_apply (p.1, q.1)).mul (continuous_apply (p.2, q.2))).sub
          ((continuous_apply (p.1, q.2)).mul (continuous_apply (p.2, q.1)))).pow 2
      · simp only [if_neg h]; exact continuous_const
    exact measurableSet_lt hcont.measurable measurable_const
  have hmp_bond (e : Fin (n + 1)) :
      MeasurePreserving
        (fun (x : PrefixIndex n → ℝ) (pq : Fin 3 × Fin 3) =>
          x ((pathCoeffEquiv n).symm (.inr (e, pq))))
        μ (Measure.pi fun _ : Fin 3 × Fin 3 => γ) := by
    let emb : Fin 3 × Fin 3 → PrefixIndex n := fun pq => (pathCoeffEquiv n).symm (.inr (e, pq))
    have hemb_inj : Function.Injective emb :=
      fun _ _ h => (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv n).symm.injective h))).2
    have hi := ProbabilityTheory.iIndepFun_pi (μ := fun _ : PrefixIndex n => γ)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
    refine ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _), ?_⟩
    have h := (hi.precomp hemb_inj).map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)
    have hmap (pq : Fin 3 × Fin 3) :
        Measure.map (fun x : PrefixIndex n → ℝ => x (emb pq)) μ = γ :=
      (measurePreserving_eval (fun _ : PrefixIndex n => γ) (emb pq)).map_eq
    exact h.trans (congrArg Measure.pi (funext hmap))
  have hgen : ∀ r > 0,
      μ.real (bondRankTwoEvent n η)ᶜ ≤ ((n + 1 : ℕ) : ℝ) * (r ^ 9 + 9 * (η ^ 2 / r) ^ 4) := by
    intro r hr
    have hsub : (bondRankTwoEvent n η)ᶜ ⊆
        ⋃ e ∈ (Finset.univ : Finset (Fin (n + 1))),
          {x : PrefixIndex n → ℝ | bondMinorInvariant (bondMatrixOfPrefix n x e) < η ^ 4} := by
      intro x hx
      rw [mem_compl_iff, bondRankTwoEvent, mem_setOf_eq] at hx
      push Not at hx
      obtain ⟨e, he⟩ := hx
      exact mem_iUnion₂.mpr ⟨e, Finset.mem_univ e, he⟩
    have hbond_le (e : Fin (n + 1)) :
        μ.real {x : PrefixIndex n → ℝ | bondMinorInvariant (bondMatrixOfPrefix n x e) < η ^ 4} ≤
          r ^ 9 + 9 * (η ^ 2 / r) ^ 4 := by
      have hpre := congrArg ENNReal.toReal
        ((hmp_bond e).measure_preimage hmeas_lt.nullMeasurableSet)
      exact hpre.trans_le (nine_gaussian_bondMinor_lt_prob_le hη hr)
    calc μ.real (bondRankTwoEvent n η)ᶜ
        ≤ μ.real (⋃ e ∈ (Finset.univ : Finset (Fin (n + 1))),
            {x : PrefixIndex n → ℝ | bondMinorInvariant (bondMatrixOfPrefix n x e) < η ^ 4}) :=
            measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ e ∈ (Finset.univ : Finset (Fin (n + 1))),
            μ.real {x : PrefixIndex n → ℝ | bondMinorInvariant (bondMatrixOfPrefix n x e) < η ^ 4} :=
            measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _e ∈ (Finset.univ : Finset (Fin (n + 1))), (r ^ 9 + 9 * (η ^ 2 / r) ^ 4) :=
            Finset.sum_le_sum fun e _ => hbond_le e
      _ = ((n + 1 : ℕ) : ℝ) * (r ^ 9 + 9 * (η ^ 2 / r) ^ 4) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨hgen, fun hη1 => ?_⟩
  rcases eq_or_lt_of_le hη with rfl | hη_pos
  · have hemp : (bondRankTwoEvent n 0)ᶜ = ∅ := by
      ext x; simp only [mem_compl_iff, bondRankTwoEvent, mem_setOf_eq, mem_empty_iff_false,
        iff_false, not_forall, not_le]
      rintro ⟨e, hlt⟩
      have hnn := bondMinorInvariant_nonneg (bondMatrixOfPrefix n x e)
      norm_num at hlt
      linarith only [hlt, hnn]
    rw [hemp, measureReal_empty, Real.sqrt_zero, zero_pow (by omega), mul_zero]
  · let r := Real.sqrt η
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hη_pos
    have hr_le1 : r ≤ 1 := Real.sqrt_le_one.mpr hη1
    have hr_sq : r ^ 2 = η := Real.sq_sqrt hη_pos.le
    have hdiv_eq : (η ^ 2 / r) ^ 4 = r ^ 12 := by
      rw [← hr_sq]
      field_simp [hr_pos.ne']
    have hr12_le : r ^ 12 ≤ r ^ 9 := pow_le_pow_of_le_one hr_pos.le hr_le1 (by omega)
    calc μ.real (bondRankTwoEvent n η)ᶜ
        ≤ ((n + 1 : ℕ) : ℝ) * (r ^ 9 + 9 * (η ^ 2 / r) ^ 4) := hgen r hr_pos
      _ = ((n + 1 : ℕ) : ℝ) * (r ^ 9 + 9 * r ^ 12) := by rw [hdiv_eq]
      _ ≤ ((n + 1 : ℕ) : ℝ) * (r ^ 9 + 9 * r ^ 9) :=
            mul_le_mul_of_nonneg_left (by linarith only [hr12_le]) (Nat.cast_nonneg _)
      _ = (10 * (n + 1 : ℕ) : ℝ) * r ^ 9 := by ring

private theorem twoByTwo_pauli_decomp (M : Matrix Bool Bool ℂ) :
    M = (Matrix.trace M / 2) • (1 : Matrix Bool Bool ℂ) +
      ∑ a : Fin 3, (Matrix.trace (finiteQubitPauli a * M) / 2) • finiteQubitPauli a := by
  ext x y
  fin_cases x <;> fin_cases y
  all_goals simp [finiteQubitPauli, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
  · ring
  · ring_nf; rw [Complex.I_sq]; ring
  · ring_nf; rw [Complex.I_sq]; ring
  · ring

private theorem conj_pauliZ_eq_real_pauli_comb (R₀ : Matrix Bool Bool ℂ)
    (hR₀ : star R₀ * R₀ = 1 ∧ R₀ * star R₀ = 1) :
    let M := R₀ * finiteQubitPauli 2 * star R₀
    let w : Fin 3 → ℝ := fun a => (Matrix.trace (finiteQubitPauli a * M)).re / 2
    Matrix.trace M = 0 ∧
    M = ∑ a : Fin 3, ((w a : ℝ) : ℂ) • finiteQubitPauli a := by
  intro M w
  have hP_sa (a : Fin 3) : star (finiteQubitPauli a) = finiteQubitPauli a := by
    rw [Matrix.star_eq_conjTranspose, (finiteQubitPauli_isHermitian a).eq]
  have htr_star (X : Matrix Bool Bool ℂ) : star (Matrix.trace X) = Matrix.trace (star X) := by
    simp [Matrix.trace]
  have htr0 : Matrix.trace M = 0 := by
    dsimp only [M]
    rw [Matrix.trace_mul_comm, ← mul_assoc, hR₀.1, one_mul]
    simp [Matrix.trace, finiteQubitPauli]
  have hM_sa : star M = M := by
    dsimp only [M]
    rw [star_mul, star_mul, star_star, hP_sa 2, mul_assoc]
  have hreal_tr (a : Fin 3) :
      Matrix.trace (finiteQubitPauli a * M) / 2 = ((w a : ℝ) : ℂ) := by
    have hst : star (Matrix.trace (finiteQubitPauli a * M)) =
        Matrix.trace (finiteQubitPauli a * M) := by
      rw [htr_star, star_mul, hM_sa, hP_sa a, Matrix.trace_mul_comm]
    have him0 : (Matrix.trace (finiteQubitPauli a * M)).im = 0 := by
      have h := congrArg Complex.im hst
      simp only [Complex.star_def, Complex.conj_im] at h
      linarith only [h]
    dsimp only [w]
    apply Complex.ext
    · simp
    · simp [him0]
  refine ⟨htr0, ?_⟩
  have hdec := twoByTwo_pauli_decomp M
  rw [htr0, zero_div, zero_smul, zero_add] at hdec
  rw [hdec]
  exact Finset.sum_congr rfl fun a _ => by rw [hreal_tr a]

private theorem bessel_bond_pauli_le_opNorm_sq {n : ℕ} (e : Fin (n + 1)) (Δ : Register (n + 2)) :
    let N := n + 2
    (∑ p : Fin 3, ∑ q : Fin 3,
      ‖((2 : ℂ) ^ N)⁻¹ * Matrix.trace (star (finitePauliMatrix (couplingWord e (p, q))) * Δ)‖ ^ 2) ≤
      ‖Δ‖ ^ 2 := by
  intro N
  let α : Fin 3 × Fin 3 → ℂ := fun pq =>
    ((2 : ℂ) ^ N)⁻¹ * Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Δ)
  let Δ_proj : Register N := ∑ pq : Fin 3 × Fin 3, α pq • finitePauliMatrix (couplingWord e pq)
  let Rem : Register N := Δ - Δ_proj
  have horth_pq (pq₁ pq₂ : Fin 3 × Fin 3) :
      Matrix.trace (star (finitePauliMatrix (couplingWord e pq₁)) *
        finitePauliMatrix (couplingWord e pq₂)) =
        if pq₁ = pq₂ then (2 : ℂ) ^ N else 0 := by
    rw [trace_star_finitePauliMatrix_mul, Fintype.card_fin]
    by_cases h : pq₁ = pq₂
    · subst h; simp [N]
    · have hc_ne : couplingWord e pq₁ ≠ couplingWord e pq₂ := fun hw =>
        h ((Prod.mk.inj (Sum.inr.inj (@pathWord_injective n (.inr (e, pq₁)) (.inr (e, pq₂)) hw))).2)
      rw [if_neg hc_ne, if_neg h]
  have htr_proj_eq (pq : Fin 3 × Fin 3) :
      Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Δ_proj) =
        (2 : ℂ) ^ N * α pq := by
    dsimp only [Δ_proj]
    rw [Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single pq]
    · rw [Matrix.mul_smul, Matrix.trace_smul, horth_pq pq pq, if_pos rfl, smul_eq_mul, mul_comm]
    · intro rs _ hrs
      rw [Matrix.mul_smul, Matrix.trace_smul, horth_pq pq rs, if_neg hrs.symm, smul_zero]
    · simp
  have htr_rem_zero (pq : Fin 3 × Fin 3) :
      Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Rem) = 0 := by
    dsimp only [Rem]
    rw [Matrix.mul_sub, Matrix.trace_sub, htr_proj_eq pq]
    dsimp only [α]
    have h2ne : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
    rw [← mul_assoc, mul_inv_cancel₀ h2ne, one_mul, sub_self]
  have hhs_eq (M : Register N) :
      (Matrix.trace (star M * M)).re = ∑ b : Config N, ∑ a : Config N, ‖M a b‖ ^ 2 := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.star_def]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hcross1 : Matrix.trace (star Δ_proj * Rem) = 0 := by
    dsimp only [Δ_proj]
    rw [star_sum, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun pq _ => ?_
    rw [star_smul, Matrix.smul_mul, Matrix.trace_smul, htr_rem_zero pq, smul_zero]
  have hcross2 : (Matrix.trace (star Rem * Δ_proj)).re = 0 := by
    have htr_star (X : Register N) : star (Matrix.trace X) = Matrix.trace (star X) := by
      simp [Matrix.trace, star_sum]
    have hst : star (Matrix.trace (star Δ_proj * Rem)) = Matrix.trace (star Rem * Δ_proj) := by
      rw [htr_star, star_mul, star_star]
    rw [hcross1, star_zero] at hst
    rw [← hst, Complex.zero_re]
  have hproj_hs : (Matrix.trace (star Δ_proj * Δ_proj)).re =
      (2 : ℝ) ^ N * ∑ pq : Fin 3 × Fin 3, ‖α pq‖ ^ 2 := by
    have hc : Matrix.trace (star Δ_proj * Δ_proj) =
        (2 : ℂ) ^ N * ∑ pq : Fin 3 × Fin 3, (star (α pq) * α pq) := by
      conv_lhs => arg 1; arg 1; dsimp only [Δ_proj]
      rw [star_sum, Matrix.sum_mul, Matrix.trace_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun pq _ => ?_
      rw [star_smul, Matrix.smul_mul, Matrix.trace_smul, htr_proj_eq pq, smul_eq_mul]
      ring
    rw [hc]
    have hsum_real : (∑ pq : Fin 3 × Fin 3, star (α pq) * α pq) =
        ((∑ pq : Fin 3 × Fin 3, ‖α pq‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun pq _ => ?_
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [hsum_real, show ((2 : ℂ) ^ N) = (((2 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpyth : (2 : ℝ) ^ N * (∑ pq : Fin 3 × Fin 3, ‖α pq‖ ^ 2) ≤
      ∑ b : Config N, ∑ a : Config N, ‖Δ a b‖ ^ 2 := by
    have hΔ_split : Δ = Rem + Δ_proj := by dsimp [Rem]; abel
    have htr_split : (Matrix.trace (star Δ * Δ)).re =
        (Matrix.trace (star Rem * Rem)).re + (Matrix.trace (star Δ_proj * Δ_proj)).re := by
      conv_lhs => rw [hΔ_split]
      rw [star_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
      simp only [Complex.add_re, hcross1, hcross2, add_zero, zero_add]
    have hrem_nn : 0 ≤ (Matrix.trace (star Rem * Rem)).re := by
      rw [hhs_eq]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [← hhs_eq Δ, htr_split, ← hproj_hs]
    linarith only [hrem_nn]
  have hΔ_hs_le : (∑ b : Config N, ∑ a : Config N, ‖Δ a b‖ ^ 2) ≤ (2 : ℝ) ^ N * ‖Δ‖ ^ 2 := by
    have hcol (b : Config N) : (∑ a : Config N, ‖Δ a b‖ ^ 2) ≤ ‖Δ‖ ^ 2 := by
      let e_b : EuclideanSpace ℂ (Config N) := EuclideanSpace.single b 1
      have he_n : ‖e_b‖ = 1 := by simp [e_b]
      have hle := pow_le_pow_left₀ (norm_nonneg _)
        ((Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) Δ).le_opNorm e_b) 2
      rw [Matrix.l2_opNorm_toEuclideanCLM, he_n, mul_one, EuclideanSpace.norm_sq_eq] at hle
      refine (le_of_eq ?_).trans hle
      refine Finset.sum_congr rfl fun a _ => ?_
      have happ : (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) Δ e_b).ofLp a = Δ a b := by
        rw [Matrix.ofLp_toEuclideanCLM]; simp [e_b]
      rw [happ]
    calc (∑ b : Config N, ∑ a : Config N, ‖Δ a b‖ ^ 2)
        ≤ ∑ _b : Config N, ‖Δ‖ ^ 2 := Finset.sum_le_sum fun b _ => hcol b
      _ = (2 : ℝ) ^ N * ‖Δ‖ ^ 2 := by simp [Config, Finset.sum_const, nsmul_eq_mul]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos two_pos N
  rw [← Fintype.sum_prod_type
    (f := fun pq : Fin 3 × Fin 3 =>
      ‖((2 : ℂ) ^ N)⁻¹ * Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Δ)‖ ^ 2)]
  exact le_of_mul_le_mul_left (hpyth.trans hΔ_hs_le) h2pos

/-- `U(2)^⊗N`-gauge-invariant operator-norm lower bound against **all** locally rotated Ising
Hamiltonians: for every local unitary tuple `R : Fin (n + 2) → Matrix Bool Bool ℂ`
(`∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1`), every diagonal shell `v : PathShell n`
(`∀ l, ¬ IsDiagLabel l → v l = 0`), and every bond `e : Fin (n + 1)`,
`bondMinorInvariant (bondMatrix u e) ≤ 9 * frobSq3 (bondMatrix u e) *
  ‖pathHamiltonian u - prodLocalMatrix R * pathHamiltonian v * star (prodLocalMatrix R)‖ ^ 2`. -/
theorem locallyRotatedIsing_operator_dist_ge_of_bondMinor {n : ℕ}
    (u v : PathShell n) (hv : ∀ l : PathLabel n, ¬ IsDiagLabel l → v l = 0)
    (R : Fin (n + 2) → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (e : Fin (n + 1)) :
    let W := prodLocalMatrix R
    bondMinorInvariant (bondMatrix u e) ≤
      9 * frobSq3 (bondMatrix u e) *
        ‖pathHamiltonian u - W * pathHamiltonian v * star W‖ ^ 2 := by
  intro W
  let N := n + 2
  let M_s : Fin N → Matrix Bool Bool ℂ := fun s => R s * finiteQubitPauli 2 * star (R s)
  let w_R : Fin N → Fin 3 → ℝ := fun s a => (Matrix.trace (finiteQubitPauli a * M_s s)).re / 2
  have hMs (s : Fin N) := conj_pauliZ_eq_real_pauli_comb (R s) (hR s)
  have hR_one (s : Fin N) : R s * (1 : Matrix Bool Bool ℂ) * star (R s) = 1 := by
    rw [mul_one, (hR s).2]
  have htrace_prodLocal (A B : Fin N → Matrix Bool Bool ℂ) :
      Matrix.trace (prodLocalMatrix A * prodLocalMatrix B) =
        ∏ s : Fin N, Matrix.trace (A s * B s) := by
    rw [prodLocalMatrix_mul, Matrix.trace]
    simp only [Matrix.diag_apply, prodLocalMatrix]
    rw [← Fintype.prod_sum (fun s (b : Bool) => (A s * B s) b b)]
    rfl
  have hpauli_tr_one (a b : Fin 3) :
      Matrix.trace (star (finiteQubitPauli a) * finiteQubitPauli b) =
        if a = b then 2 else 0 := by
    fin_cases a <;> fin_cases b <;>
      simp [finiteQubitPauli, Matrix.trace, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply] <;>
      norm_num
  have hpauli_tr_zero (a : Fin 3) : Matrix.trace (star (finiteQubitPauli a)) = 0 := by
    rw [Matrix.star_eq_conjTranspose, (finiteQubitPauli_isHermitian a).eq]
    fin_cases a <;> simp [finiteQubitPauli, Matrix.trace]
  have htr_diag_label (pq : Fin 3 × Fin 3) (l : PathLabel n) (hl_diag : IsDiagLabel l) :
      Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) *
        (W * finitePauliMatrix (pathWord l) * star W)) =
        if l = .inr (e, (2, 2)) then
          (2 : ℂ) ^ N * ((w_R e.castSucc pq.1 * w_R e.succ pq.2 : ℝ) : ℂ)
        else 0 := by
    rw [prodLocalMatrix_conj_pauli]
    have hP_st : star (finitePauliMatrix (couplingWord e pq)) =
        prodLocalMatrix (fun s => star (boolPauliOption (couplingWord e pq s))) := by
      rw [← prodLocalMatrix_star]; rfl
    rw [hP_st, htrace_prodLocal]
    rcases l with ⟨s₀, q₀⟩ | ⟨e', pq'⟩
    · have hq₀ : q₀ = 2 := hl_diag
      subst hq₀
      rw [if_neg (by simp)]
      have hex_end : ∃ t : Fin N, (t = e.castSucc ∨ t = e.succ) ∧ t ≠ s₀ := by
        by_cases h1 : e.castSucc = s₀
        · exact ⟨e.succ, Or.inr rfl, fun h2 => e.castSucc_lt_succ.ne (h1.trans h2.symm)⟩
        · exact ⟨e.castSucc, Or.inl rfl, h1⟩
      obtain ⟨t, ht_end, ht_ne⟩ := hex_end
      refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
      have hnone : pathWord (.inl (s₀, 2)) t = none := by simp [pathWord, onsiteWord, ht_ne]
      rw [hnone, show boolPauliOption none = 1 from rfl, hR_one t]
      rcases ht_end with rfl | rfl
      · simp [couplingWord, boolPauliOption, hpauli_tr_zero]
      · simp [couplingWord, e.castSucc_lt_succ.ne', boolPauliOption, hpauli_tr_zero]
    · have hpq' : pq' = (2, 2) := hl_diag
      subst hpq'
      by_cases hee' : e' = e
      · subst e'
        rw [if_pos rfl]
        let pairSet : Finset (Fin N) := {e.castSucc, e.succ}
        have hne_cs : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
        rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hne_cs]
        have hrest_prod : (∏ s ∈ pairSetᶜ,
            Matrix.trace (star (boolPauliOption (couplingWord e pq s)) *
              (R s * boolPauliOption (pathWord (.inr (e, (2, 2))) s) * star (R s)))) =
            (2 : ℂ) ^ n := by
          have hc_card : pairSetᶜ.card = n := by
            have h1 := Finset.card_compl_add_card pairSet
            rw [Finset.card_pair hne_cs, Fintype.card_fin] at h1
            dsimp [N] at h1; omega
          have h1 : ∀ s ∈ pairSetᶜ,
              Matrix.trace (star (boolPauliOption (couplingWord e pq s)) *
                (R s * boolPauliOption (pathWord (.inr (e, (2, 2))) s) * star (R s))) = 2 := by
            intro s hs
            simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
            have hs1 : couplingWord e pq s = none := by simp [couplingWord, hs.1, hs.2]
            have hs2 : pathWord (.inr (e, (2, 2))) s = none := by simp [pathWord, couplingWord, hs.1, hs.2]
            rw [hs1, hs2, show boolPauliOption none = 1 from rfl, star_one, one_mul, hR_one s,
              Matrix.trace_one, Fintype.card_bool, Nat.cast_ofNat]
          rw [Finset.prod_congr rfl h1, Finset.prod_const, hc_card]
        have hend1 : Matrix.trace (star (boolPauliOption (couplingWord e pq e.castSucc)) *
            (R e.castSucc * boolPauliOption (pathWord (.inr (e, (2, 2))) e.castSucc) * star (R e.castSucc))) =
            2 * ((w_R e.castSucc pq.1 : ℝ) : ℂ) := by
          have hc1 : boolPauliOption (couplingWord e pq e.castSucc) = finiteQubitPauli pq.1 := by
            simp [couplingWord, boolPauliOption]
          have hc2 : R e.castSucc * boolPauliOption (pathWord (.inr (e, (2, 2))) e.castSucc) *
              star (R e.castSucc) = M_s e.castSucc := by
            simp [pathWord, couplingWord, boolPauliOption, M_s]
          rw [hc1, hc2]
          dsimp only [M_s]
          rw [(hMs e.castSucc).2, Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single pq.1]
          · rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.1 pq.1, if_pos rfl, smul_eq_mul, mul_comm]
          · intro a _ ha; rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.1 a, if_neg ha.symm, smul_zero]
          · simp
        have hend2 : Matrix.trace (star (boolPauliOption (couplingWord e pq e.succ)) *
            (R e.succ * boolPauliOption (pathWord (.inr (e, (2, 2))) e.succ) * star (R e.succ))) =
            2 * ((w_R e.succ pq.2 : ℝ) : ℂ) := by
          have hc1 : boolPauliOption (couplingWord e pq e.succ) = finiteQubitPauli pq.2 := by
            simp [couplingWord, hne_cs.symm, boolPauliOption]
          have hc2 : R e.succ * boolPauliOption (pathWord (.inr (e, (2, 2))) e.succ) *
              star (R e.succ) = M_s e.succ := by
            simp [pathWord, couplingWord, hne_cs.symm, boolPauliOption, M_s]
          rw [hc1, hc2]
          dsimp only [M_s]
          rw [(hMs e.succ).2, Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single pq.2]
          · rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.2 pq.2, if_pos rfl, smul_eq_mul, mul_comm]
          · intro a _ ha; rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.2 a, if_neg ha.symm, smul_zero]
          · simp
        rw [hend1, hend2, hrest_prod, Complex.ofReal_mul]
        have hpowN : (2 : ℂ) ^ N = (2 : ℂ) * (2 : ℂ) * (2 : ℂ) ^ n := by
          dsimp [N]; rw [pow_add]; ring
        rw [hpowN]; ring
      · rw [if_neg (by simp [hee'])]
        have hex_out : ∃ t : Fin N, (t = e'.castSucc ∨ t = e'.succ) ∧
            t ≠ e.castSucc ∧ t ≠ e.succ := by
          rcases lt_or_gt_of_ne hee' with hlt | hgt
          · refine ⟨e'.castSucc, Or.inl rfl, fun h => ?_, fun h => ?_⟩
            · exact hlt.ne (Fin.castSucc_injective _ h)
            · have hv := congrArg Fin.val h; simp at hv; have : e'.val < e.val := hlt; omega
          · refine ⟨e'.succ, Or.inr rfl, fun h => ?_, fun h => ?_⟩
            · have hv := congrArg Fin.val h; simp at hv; have : e.val < e'.val := hgt; omega
            · exact hgt.ne' (Fin.succ_injective _ h)
        obtain ⟨t, ht_e', ht_ne1, ht_ne2⟩ := hex_out
        refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
        have hnone_e : couplingWord e pq t = none := by simp [couplingWord, ht_ne1, ht_ne2]
        have hsome_e' : R t * boolPauliOption (pathWord (.inr (e', (2, 2))) t) * star (R t) = M_s t := by
          rcases ht_e' with rfl | rfl
          · simp [pathWord, couplingWord, boolPauliOption, M_s]
          · simp [pathWord, couplingWord, e'.castSucc_lt_succ.ne', boolPauliOption, M_s]
        rw [hnone_e, show boolPauliOption none = 1 from rfl, star_one, one_mul, hsome_e']
        exact (hMs t).1
  let Δ := pathHamiltonian u - W * pathHamiltonian v * star W
  have htr_Δ (pq : Fin 3 × Fin 3) :
      ((2 : ℂ) ^ N)⁻¹ * Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Δ) =
        ((u (.inr (e, pq)) - (v (.inr (e, (2, 2))) * w_R e.castSucc pq.1) * w_R e.succ pq.2 : ℝ) : ℂ) := by
    have htr_u : Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * pathHamiltonian u) =
        (2 : ℂ) ^ N * ((u (.inr (e, pq)) : ℝ) : ℂ) := by
      rw [pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.trace_sum,
        Finset.sum_eq_single (.inr (e, pq))]
      · rw [Matrix.mul_smul, Matrix.trace_smul]
        have hu := finitePauliMatrix_mem_unitary (couplingWord e pq)
        change _ • Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) *
          finitePauliMatrix (couplingWord e pq)) = _
        rw [(Unitary.mem_iff.mp hu).1, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_bool, smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
      · intro l _ hne
        rw [Matrix.mul_smul, Matrix.trace_smul, trace_star_finitePauliMatrix_mul]
        have hword_ne : couplingWord e pq ≠ pathWord l := fun hw =>
          hne (@pathWord_injective n (.inr (e, pq)) l hw).symm
        rw [if_neg hword_ne, smul_zero]
      · simp
    have htr_v : Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) *
        (W * pathHamiltonian v * star W)) =
        (2 : ℂ) ^ N * (((v (.inr (e, (2, 2))) * w_R e.castSucc pq.1) * w_R e.succ pq.2 : ℝ) : ℂ) := by
      rw [pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
        Finset.sum_eq_single (.inr (e, (2, 2)))]
      · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
          htr_diag_label pq (.inr (e, (2, 2))) rfl, if_pos rfl, smul_eq_mul]
        push_cast; ring
      · intro l _ hne
        by_cases hld : IsDiagLabel l
        · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
            htr_diag_label pq l hld, if_neg hne, smul_zero]
        · rw [hv l hld, Complex.ofReal_zero, zero_smul, Matrix.mul_zero, Matrix.zero_mul,
            Matrix.mul_zero, Matrix.trace_zero]
      · simp
    dsimp only [Δ]
    rw [Matrix.mul_sub, Matrix.trace_sub, htr_u, htr_v]
    have h2ne : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
    push_cast
    field_simp [h2ne]
  have hbessel := bessel_bond_pauli_le_opNorm_sq e Δ
  have herr_sum : (∑ p : Fin 3, ∑ q : Fin 3,
      (bondMatrix u e p q - (v (.inr (e, (2, 2))) * w_R e.castSucc p) * w_R e.succ q) ^ 2) ≤
      ‖Δ‖ ^ 2 := by
    refine (le_of_eq ?_).trans hbessel
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [htr_Δ (p, q), Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rfl
  have hmin := bondMinorInvariant_le_rankOne_dist (bondMatrix u e)
    (fun p => v (.inr (e, (2, 2))) * w_R e.castSucc p) (w_R e.succ)
  exact hmin.trans (mul_le_mul_of_nonneg_left herr_sum
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)))

/-! ## Section 2: Abstract `C*`-algebra skew-pair rotations, `SO(m)` adjacent Givens synthesis,
and Clifford even-subspace commutant rigidity -/

private theorem skew_square_exp {A : Type*} [CStarAlgebra A] {X : A} (hX : X * X = -1) (θ : ℝ) :
    NormedSpace.exp ((θ : ℂ) • X) =
      (Real.cos θ : ℂ) • (1 : A) + (Real.sin θ : ℂ) • X := by
  have hsq : ((θ : ℂ) • X) * ((θ : ℂ) • X) = (-((θ : ℂ) ^ (2 : ℕ))) • (1 : A) := by
    rw [smul_mul_smul_comm, hX, smul_neg, ← neg_smul, pow_two]
  rw [_root_.HTGeometry.exp_of_mul_self_eq_neg_sq_smul_one _ θ hsq, smul_smul]
  have hsin : Real.sinc θ * θ = Real.sin θ := by
    by_cases h : θ = 0
    · simp only [h, mul_zero, Real.sin_zero]
    · rw [Real.sinc_of_ne_zero h, div_mul_cancel₀ _ h]
  rw [← Complex.ofReal_mul, hsin]

private theorem exp_skewPair_star_eq {A : Type*} [CStarAlgebra A] {γ₁ γ₂ : A}
    (hst₁ : star γ₁ = γ₁) (hst₂ : star γ₂ = γ₂) (hanti : γ₁ * γ₂ = -(γ₂ * γ₁)) (θ : ℝ) :
    star (NormedSpace.exp ((θ : ℂ) • (γ₁ * γ₂))) =
      NormedSpace.exp (((-θ : ℝ) : ℂ) • (γ₁ * γ₂)) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  rw [NormedSpace.star_exp, star_smul, star_mul, hst₂, hst₁]
  have hst_prod : γ₂ * γ₁ = -(γ₁ * γ₂) := by
    rw [← neg_neg (γ₂ * γ₁), ← hanti]
  rw [hst_prod, Complex.star_def, Complex.conj_ofReal, smul_neg, Complex.ofReal_neg, neg_smul]

private theorem exp_skewPair_conj {A : Type*} [CStarAlgebra A] {γ₁ γ₂ : A}
    (h₁ : γ₁ * γ₁ = 1) (h₂ : γ₂ * γ₂ = 1)
    (hst₁ : star γ₁ = γ₁) (hst₂ : star γ₂ = γ₂) (hanti : γ₁ * γ₂ = -(γ₂ * γ₁)) (φ : ℝ) :
    let U := NormedSpace.exp (((φ / 2 : ℝ) : ℂ) • (γ₁ * γ₂))
    U * γ₁ * star U = (Real.cos φ : ℂ) • γ₁ + ((-Real.sin φ : ℝ) : ℂ) • γ₂ ∧
    U * γ₂ * star U = (Real.sin φ : ℂ) • γ₁ + (Real.cos φ : ℂ) • γ₂ ∧
    ∀ γ₃ : A, γ₁ * γ₃ = -(γ₃ * γ₁) → γ₂ * γ₃ = -(γ₃ * γ₂) → U * γ₃ * star U = γ₃ := by
  intro U
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let X := γ₁ * γ₂
  have hX₁ : X * γ₁ = -γ₂ := by dsimp [X]; rw [hanti, neg_mul, mul_assoc, h₁, mul_one]
  have h₁X : γ₁ * X = γ₂ := by dsimp [X]; rw [← mul_assoc, h₁, one_mul]
  have hX₂ : X * γ₂ = γ₁ := by dsimp [X]; rw [mul_assoc, h₂, mul_one]
  have h₂X : γ₂ * X = -γ₁ := by
    dsimp [X]; rw [← mul_assoc]
    have h21 : γ₂ * γ₁ = -(γ₁ * γ₂) := by rw [← neg_neg (γ₂ * γ₁), ← hanti]
    rw [h21, neg_mul, mul_assoc, h₂, mul_one]
  have hX_sq : X * X = -1 := by dsimp [X]; rw [← mul_assoc, hX₁, neg_mul, h₂]
  have hU_exp : U = (Real.cos (φ / 2) : ℂ) • (1 : A) + (Real.sin (φ / 2) : ℂ) • X :=
    skew_square_exp hX_sq (φ / 2)
  have hstU : star U = NormedSpace.exp (((-(φ / 2) : ℝ) : ℂ) • X) :=
    exp_skewPair_star_eq hst₁ hst₂ hanti (φ / 2)
  have hstU_exp : star U =
      (Real.cos (φ / 2) : ℂ) • (1 : A) + (-(Real.sin (φ / 2) : ℂ)) • X := by
    rw [hstU, skew_square_exp hX_sq (-(φ / 2)), Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  have hc_double : Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2 = Real.cos φ := by
    have h2 : φ = 2 * (φ / 2) := by ring
    conv_rhs => rw [h2, Real.cos_two_mul]
    linarith only [Real.sin_sq_add_cos_sq (φ / 2)]
  have hs_double : 2 * Real.sin (φ / 2) * Real.cos (φ / 2) = Real.sin φ := by
    rw [← Real.sin_two_mul, show 2 * (φ / 2) = φ by ring]
  let c : ℂ := (Real.cos (φ / 2) : ℂ)
  let s : ℂ := (Real.sin (φ / 2) : ℂ)
  have hc_c : c * c - s * s = (Real.cos φ : ℂ) := by
    dsimp [c, s]; exact_mod_cast (by simpa [pow_two] using hc_double)
  have hs_c : 2 * s * c = (Real.sin φ : ℂ) := by
    dsimp [c, s]; exact_mod_cast hs_double
  refine ⟨?_, ?_, ?_⟩
  · rw [hstU_exp, hU_exp]
    change (c • (1 : A) + s • X) * γ₁ * (c • (1 : A) + (-s) • X) = _
    have hL : (c • (1 : A) + s • X) * γ₁ = c • γ₁ + (-s) • γ₂ := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hX₁, smul_neg, neg_smul]
    rw [hL, add_mul, mul_add, mul_add]
    simp only [smul_mul_smul_comm, mul_one, h₁X, h₂X, smul_neg]
    have hs1 : c * -s = -(s * c) := by ring
    have hs2 : -s * c = -(s * c) := by ring
    have hs3 : -s * -s = s * s := by ring
    have hs4 : -(2 * s * c) = -(s * c) + -(s * c) := by ring
    rw [Complex.ofReal_neg, ← hc_c, ← hs_c, hs1, hs2, hs3, hs4, sub_smul, add_smul, neg_smul]
    abel
  · rw [hstU_exp, hU_exp]
    change (c • (1 : A) + s • X) * γ₂ * (c • (1 : A) + (-s) • X) = _
    have hL : (c • (1 : A) + s • X) * γ₂ = c • γ₂ + s • γ₁ := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hX₂]
    rw [hL, add_mul, mul_add, mul_add]
    simp only [smul_mul_smul_comm, mul_one, h₁X, h₂X, smul_neg]
    have hs1 : c * -s = -(s * c) := by ring
    have hs2 : s * -s = -(s * s) := by ring
    have hs3 : 2 * s * c = s * c + s * c := by ring
    rw [← hc_c, ← hs_c, hs1, hs2, hs3]
    simp only [sub_smul, add_smul, neg_smul, neg_neg]
    abel
  · intro γ₃ ha₁ ha₂
    have hcommX : Commute X γ₃ := by
      change (γ₁ * γ₂) * γ₃ = γ₃ * (γ₁ * γ₂)
      rw [mul_assoc, ha₂, mul_neg, ← mul_assoc, ha₁, neg_mul, neg_neg, mul_assoc]
    have hcommU : U * γ₃ = γ₃ * U :=
      ((hcommX.smul_left ((φ / 2 : ℝ) : ℂ)).exp_left).eq
    have hU_unit : U * star U = 1 := by
      rw [hstU, ← NormedSpace.exp_add_of_commute
        (((Commute.refl X).smul_left _).smul_right _)]
      have h0 : ((φ / 2 : ℝ) : ℂ) • X + ((-(φ / 2) : ℝ) : ℂ) • X = 0 := by
        rw [← add_smul, Complex.ofReal_neg, add_neg_cancel, zero_smul]
      rw [h0, NormedSpace.exp_zero]
    rw [hcommU, mul_assoc, hU_unit, mul_one]

/-- Elementary adjacent Givens rotation `G_{e, e + 1}(φ) ∈ SO(m)` acting in rows/columns
`(e, e + 1)` when `e + 1 < m` (and fixing all other indices). -/
def adjGivens (m e : ℕ) (φ : ℝ) : Matrix (Fin m) (Fin m) ℝ := fun i j =>
  if i.val = e ∧ j.val = e then Real.cos φ
  else if i.val = e ∧ j.val = e + 1 then Real.sin φ
  else if i.val = e + 1 ∧ j.val = e then -Real.sin φ
  else if i.val = e + 1 ∧ j.val = e + 1 then Real.cos φ
  else if i = j then 1 else 0

private theorem adjGivens_zero (m e : ℕ) : adjGivens m e 0 = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have hne1 : ¬ (i.val = e ∧ i.val = e + 1) := by omega
    have hne2 : ¬ (i.val = e + 1 ∧ i.val = e) := by omega
    simp only [adjGivens, Real.cos_zero, Matrix.one_apply_eq,
      hne1, hne2, ↓reduceIte]
    split_ifs <;> rfl
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h1 : ¬ (i.val = e ∧ j.val = e) := by omega
    have h4 : ¬ (i.val = e + 1 ∧ j.val = e + 1) := by omega
    simp only [adjGivens, Real.sin_zero, neg_zero, Matrix.one_apply_ne hij,
      h1, h4, hij, ↓reduceIte]
    split_ifs <;> rfl

private theorem adjGivens_transpose (m e : ℕ) (φ : ℝ) :
    (adjGivens m e φ)ᵀ = adjGivens m e (-φ) := by
  ext i j
  simp only [Matrix.transpose_apply, adjGivens, Real.cos_neg, Real.sin_neg, neg_neg, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem adjGivens_mul_same {m e : ℕ} (he : e + 1 < m) (φ ψ : ℝ) :
    adjGivens m e φ * adjGivens m e ψ = adjGivens m e (φ + ψ) := by
  let i₀ : Fin m := ⟨e, by omega⟩
  let i₁ : Fin m := ⟨e + 1, he⟩
  have hi₀₁ : i₀ ≠ i₁ := fun h => by have hv := congrArg Fin.val h; dsimp [i₀, i₁] at hv; omega
  let P : Finset (Fin m) := {i₀, i₁}
  have hmem_P (k : Fin m) : k ∈ P ↔ k.val = e ∨ k.val = e + 1 := by
    simp only [P, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, i₀, i₁]
  have hrow_out {i k : Fin m} (hi : i ∉ P) (θ : ℝ) :
      adjGivens m e θ i k = if i = k then 1 else 0 := by
    rw [hmem_P, not_or] at hi
    simp [adjGivens, hi.1, hi.2]
  have hcol_out {k j : Fin m} (hj : j ∉ P) (θ : ℝ) :
      adjGivens m e θ k j = if k = j then 1 else 0 := by
    rw [hmem_P, not_or] at hj
    simp only [adjGivens, hj.1, hj.2, and_false, ↓reduceIte]
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ P
  · by_cases hj : j ∈ P
    · have hzero_out : ∀ k ∈ Finset.univ, k ∉ P →
          adjGivens m e φ i k * adjGivens m e ψ k j = 0 := by
        intro k _ hk
        rw [hcol_out hk φ, if_neg (fun hik : i = k => hk (hik ▸ hi)), zero_mul]
      rw [← Finset.sum_subset P.subset_univ hzero_out, Finset.sum_pair hi₀₁]
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
        simp only [adjGivens, i₀, i₁, Nat.add_eq_left, one_ne_zero, and_self, and_false,
          false_and, ↓reduceIte]
      · rw [Real.cos_add]; ring
      · rw [Real.sin_add]; ring
      · rw [Real.sin_add]; ring
      · rw [Real.cos_add]; ring
    · simp_rw [hcol_out hj ψ, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j), hcol_out hj (φ + ψ),
        hcol_out hj φ]
  · simp_rw [hrow_out hi φ, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i), hrow_out hi (φ + ψ), hrow_out hi ψ]

private theorem adjGivens_orthog {m e : ℕ} (he : e + 1 < m) (φ : ℝ) :
    (adjGivens m e φ)ᵀ * adjGivens m e φ = 1 ∧
    adjGivens m e φ * (adjGivens m e φ)ᵀ = 1 ∧
    (adjGivens m e φ).det = 1 := by
  have hL : ∀ θ : ℝ, (adjGivens m e θ)ᵀ * adjGivens m e θ = 1 := fun θ => by
    rw [adjGivens_transpose, adjGivens_mul_same he, neg_add_cancel, adjGivens_zero]
  have hR : ∀ θ : ℝ, adjGivens m e θ * (adjGivens m e θ)ᵀ = 1 := fun θ => by
    rw [adjGivens_transpose, adjGivens_mul_same he, add_neg_cancel, adjGivens_zero]
  refine ⟨hL φ, hR φ, ?_⟩
  have hhalf : adjGivens m e (φ / 2) * adjGivens m e (φ / 2) = adjGivens m e φ := by
    rw [adjGivens_mul_same he, add_halves]
  have hd_one : ((adjGivens m e (φ / 2))ᵀ * adjGivens m e (φ / 2)).det = 1 := by
    rw [hL (φ / 2), Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_transpose] at hd_one
  rw [← hhalf, Matrix.det_mul, hd_one]

private theorem adjGivens_plane_elim (a b : ℝ) :
    let φ := Complex.arg ((a : ℂ) + (b : ℂ) * Complex.I)
    0 ≤ Real.cos φ * a + Real.sin φ * b ∧
    -Real.sin φ * a + Real.cos φ * b = 0 := by
  let z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hre : z.re = a := by simp [z]
  have him : z.im = b := by simp [z]
  let φ := Complex.arg z
  change 0 ≤ Real.cos φ * a + Real.sin φ * b ∧ -Real.sin φ * a + Real.cos φ * b = 0
  by_cases hz : z = 0
  · have ha : a = 0 := by rw [← hre, hz, Complex.zero_re]
    have hb : b = 0 := by rw [← him, hz, Complex.zero_im]
    simp [ha, hb]
  · have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hcos := Complex.norm_mul_cos_arg z
    have hsin := Complex.norm_mul_sin_arg z
    rw [hre] at hcos
    rw [him] at hsin
    have hmul1 : ‖z‖ * (Real.cos φ * a + Real.sin φ * b) = a ^ 2 + b ^ 2 := by
      dsimp [φ]; linear_combination a * hcos + b * hsin
    have hmul2 : ‖z‖ * (-Real.sin φ * a + Real.cos φ * b) = 0 := by
      dsimp [φ]; linear_combination -a * hsin + b * hcos
    have hnn : 0 ≤ ‖z‖ * (Real.cos φ * a + Real.sin φ * b) := by rw [hmul1]; positivity
    refine ⟨by by_contra hlt; push Not at hlt; nlinarith only [hnn, hnorm_pos, hlt], ?_⟩
    exact (mul_eq_zero.mp hmul2).resolve_left hnorm_pos.ne'

private theorem adjGivens_succ_lift {m e : ℕ} (_he : e + 1 < m + 1) (φ : ℝ) :
    let G := adjGivens (m + 2) (e + 1) φ
    G 0 0 = 1 ∧
    (∀ i : Fin (m + 1), G i.succ 0 = 0) ∧
    (∀ j : Fin (m + 1), G 0 j.succ = 0) ∧
    G.submatrix Fin.succ Fin.succ = adjGivens (m + 1) e φ := by
  intro G
  refine ⟨?_, fun i => ?_, fun j => ?_, ?_⟩
  · simp [G, adjGivens]
  · simp [G, adjGivens, Fin.succ_ne_zero]
  · simp [G, adjGivens, (Fin.succ_ne_zero j).symm]
  · ext i j
    simp only [G, Matrix.submatrix_apply, adjGivens, Fin.val_succ, add_left_inj,
      Fin.succ_inj]

private theorem isOneDirectSum_mul {m : ℕ}
    {A B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}
    (hA00 : A 0 0 = 1) (hAi0 : ∀ i : Fin (m + 1), A i.succ 0 = 0)
    (hA0j : ∀ j : Fin (m + 1), A 0 j.succ = 0)
    (hB00 : B 0 0 = 1) (hBi0 : ∀ i : Fin (m + 1), B i.succ 0 = 0)
    (hB0j : ∀ j : Fin (m + 1), B 0 j.succ = 0) :
    (A * B) 0 0 = 1 ∧
    (∀ i : Fin (m + 1), (A * B) i.succ 0 = 0) ∧
    (∀ j : Fin (m + 1), (A * B) 0 j.succ = 0) ∧
    (A * B).submatrix Fin.succ Fin.succ =
      A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
  refine ⟨?_, fun i => ?_, fun j => ?_, ?_⟩
  · rw [Matrix.mul_apply, Fin.sum_univ_succ, hA00, hB00, one_mul,
      Finset.sum_eq_zero (fun k _ => by rw [hA0j k, zero_mul]), add_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ, hAi0 i, zero_mul, zero_add]
    exact Finset.sum_eq_zero fun k _ => by rw [hBi0 k, mul_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ, hB0j j, mul_zero, zero_add]
    exact Finset.sum_eq_zero fun k _ => by rw [hA0j k, zero_mul]
  · ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, hAi0 i, zero_mul, zero_add,
      Matrix.mul_apply]
    rfl

private theorem choose2_step_eq (m : ℕ) :
    (m + 1) + (m + 1) * m / 2 = (m + 2) * (m + 1) / 2 := by
  have heven : ∀ k : ℕ, 2 * ((k + 1) * k / 2) = (k + 1) * k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h1 : (k + 2) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
        rw [h1, Nat.add_mul_div_left _ _ two_pos, mul_add, ih]
  have h1 := heven m
  have h2 := heven (m + 1)
  have h3 : 2 * (m + 1) + (m + 1) * m = (m + 2) * (m + 1) := by ring
  omega

private theorem elim_col_zero_bottom (m : ℕ)
    (O : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
    (hL : Oᵀ * O = 1) (hR : O * Oᵀ = 1) (hdet : O.det = 1) :
    ∀ r : ℕ, r ≤ m →
      ∃ (L : List (ℕ × ℝ)) (O_r : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ),
        L.length = r ∧
        (∀ p ∈ L, p.1 + 1 < m + 2) ∧
        O_rᵀ * O_r = 1 ∧ O_r * O_rᵀ = 1 ∧ O_r.det = 1 ∧
        (∀ i : Fin (m + 2), m + 1 - r < i.val → O_r i 0 = 0) ∧
        O = (L.map fun p => adjGivens (m + 2) p.1 p.2).prod * O_r := by
  intro r hr
  induction r with
  | zero =>
      refine ⟨[], O, rfl, by simp, hL, hR, hdet, fun i hi => by omega, by simp⟩
  | succ r ih =>
      obtain ⟨L, O_r, hlen, hpL, hLr, hRr, hdetr, hzero, hO_eq⟩ := ih (by omega)
      let e := m - r
      have he : e + 1 < m + 2 := by dsimp [e]; omega
      let i₀ : Fin (m + 2) := ⟨e, by omega⟩
      let i₁ : Fin (m + 2) := ⟨e + 1, he⟩
      let φ := Complex.arg ((O_r i₀ 0 : ℂ) + (O_r i₁ 0 : ℂ) * Complex.I)
      let G := adjGivens (m + 2) e φ
      let G_inv := adjGivens (m + 2) e (-φ)
      obtain ⟨hGL, hGR, hGdet⟩ := adjGivens_orthog he φ
      let O_next := G * O_r
      have hGinv_G : G_inv * G = 1 := by
        dsimp [G_inv, G]; rw [← adjGivens_transpose]; exact hGL
      have hOr_eq : O_r = G_inv * O_next := by
        dsimp [O_next]; rw [← mul_assoc, hGinv_G, one_mul]
      have hLn : O_nextᵀ * O_next = 1 := by
        dsimp [O_next]; rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc Gᵀ, hGL, one_mul, hLr]
      have hRn : O_next * O_nextᵀ = 1 := by
        dsimp [O_next]; rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc O_r, hRr, one_mul, hGR]
      have hdetn : O_next.det = 1 := by
        dsimp [O_next]; rw [Matrix.det_mul, hGdet, hdetr, mul_one]
      have hzero_next : ∀ i : Fin (m + 2), m + 1 - (r + 1) < i.val → O_next i 0 = 0 := by
        intro i hi
        have he1 : m + 1 - (r + 1) = e := by dsimp [e]; omega
        rw [he1] at hi
        by_cases hi_eq : i.val = e + 1
        · have hi_i₁ : i = i₁ := Fin.ext hi_eq
          subst hi_i₁
          dsimp only [O_next, G]
          rw [Matrix.mul_apply]
          have hpair : i₀ ≠ i₁ := fun h => by have hv := congrArg Fin.val h; dsimp [i₀, i₁] at hv; omega
          let P : Finset (Fin (m + 2)) := {i₀, i₁}
          have hout : ∀ k ∈ Finset.univ, k ∉ P → adjGivens (m + 2) e φ i₁ k * O_r k 0 = 0 := by
            intro k _ hk
            simp only [P, Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, i₀, i₁] at hk
            have hg0 : adjGivens (m + 2) e φ i₁ k = 0 := by
              simp [adjGivens, i₁, hk.1, hk.2, show i₁ ≠ k from fun h => hk.2 (congrArg Fin.val h.symm)]
            rw [hg0, zero_mul]
          rw [← Finset.sum_subset P.subset_univ hout, Finset.sum_pair hpair]
          simp only [adjGivens, i₀, i₁, Nat.add_eq_left, one_ne_zero, and_self, and_false,
            false_and, ↓reduceIte]
          exact (adjGivens_plane_elim (O_r i₀ 0) (O_r i₁ 0)).2
        · have hi_gt : e + 1 < i.val := by omega
          have hi_gt_old : m + 1 - r < i.val := by dsimp [e] at hi_gt; omega
          dsimp only [O_next, G]
          rw [Matrix.mul_apply]
          have hrow : ∀ k : Fin (m + 2), adjGivens (m + 2) e φ i k = if i = k then 1 else 0 := by
            intro k
            have h1 : i.val ≠ e := by omega
            have h2 : i.val ≠ e + 1 := by omega
            simp [adjGivens, h1, h2]
          simp_rw [hrow, ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
          exact hzero i hi_gt_old
      refine ⟨L ++ [(e, -φ)], O_next, by simp [hlen], ?_, hLn, hRn, hdetn, hzero_next, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · exact hpL p hp1
        · simp only [List.mem_singleton] at hp2; subst hp2; exact he
      · rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          mul_assoc, ← hOr_eq, ← hO_eq]

/-- Exact adjacent-Givens synthesis of `SO(m)`: every special orthogonal matrix
`O : Matrix (Fin m) (Fin m) ℝ` (`Oᵀ * O = 1`, `O * Oᵀ = 1`, `O.det = 1`) factors into at most
`m * (m - 1) / 2` elementary adjacent Givens rotations `adjGivens m e φ` (`e + 1 < m`). -/
theorem exists_adjGivens_prod_eq_of_specialOrthogonal :
    ∀ (m : ℕ) (O : Matrix (Fin m) (Fin m) ℝ),
      Oᵀ * O = 1 → O * Oᵀ = 1 → O.det = 1 →
      ∃ L : List (ℕ × ℝ),
        L.length ≤ m * (m - 1) / 2 ∧
        (∀ p ∈ L, p.1 + 1 < m) ∧
        O = (L.map fun p => adjGivens m p.1 p.2).prod
  | 0, O, _, _, _ => by
      refine ⟨[], by simp, by simp, ?_⟩
      ext i; exact Fin.elim0 i
  | 1, O, _, _, hdet => by
      refine ⟨[], by simp, by simp, ?_⟩
      rw [Matrix.det_fin_one] at hdet
      ext i j; fin_cases i; fin_cases j; simpa using hdet
  | m + 2, O, hL, hR, hdet => by
      obtain ⟨L_bot, O_m, hlen_bot, hp_bot, hLm, hRm, hdetm, hzero_m, hO_bot⟩ :=
        elim_col_zero_bottom m O hL hR hdet m le_rfl
      have he0 : 0 + 1 < m + 2 := by omega
      let i₀ : Fin (m + 2) := 0
      let i₁ : Fin (m + 2) := ⟨1, by omega⟩
      let φ₀ := Complex.arg ((O_m i₀ 0 : ℂ) + (O_m i₁ 0 : ℂ) * Complex.I)
      let G₀ := adjGivens (m + 2) 0 φ₀
      let G₀_inv := adjGivens (m + 2) 0 (-φ₀)
      obtain ⟨hG0L, hG0R, hG0det⟩ := adjGivens_orthog he0 φ₀
      let O' := G₀ * O_m
      have hG0_canc : G₀_inv * G₀ = 1 := by
        dsimp [G₀_inv, G₀]; rw [← adjGivens_transpose]; exact hG0L
      have hOm_eq : O_m = G₀_inv * O' := by
        dsimp [O']; rw [← mul_assoc, hG0_canc, one_mul]
      have hL' : O'ᵀ * O' = 1 := by
        dsimp [O']; rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc G₀ᵀ, hG0L, one_mul, hLm]
      have hR' : O' * O'ᵀ = 1 := by
        dsimp [O']; rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc O_m, hRm, one_mul, hG0R]
      have hdet' : O'.det = 1 := by
        dsimp [O']; rw [Matrix.det_mul, hG0det, hdetm, mul_one]
      have hpair01 : i₀ ≠ i₁ := fun h => by
        have hv := congrArg Fin.val h; simp [i₀, i₁] at hv
      let P01 : Finset (Fin (m + 2)) := {i₀, i₁}
      have hout01 (i : Fin (m + 2)) : ∀ k ∈ Finset.univ, k ∉ P01 →
          adjGivens (m + 2) 0 φ₀ i k * O_m k 0 = 0 := by
        intro k _ hk
        have hk_not : k ∉ P01 := hk
        by_cases hiP : i ∈ P01
        · simp only [P01, Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, i₀, i₁,
            Fin.val_zero] at hk
          have hg0 : adjGivens (m + 2) 0 φ₀ i k = 0 := by
            simp only [adjGivens, Nat.zero_add, hk.1, hk.2, and_false, ↓reduceIte]
            exact if_neg fun hik : i = k => hk_not (hik ▸ hiP)
          rw [hg0, zero_mul]
        · simp only [P01, Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, i₀, i₁,
            Fin.val_zero] at hiP hk
          by_cases hik : i = k
          · subst hik
            have hgt1 : m + 1 - m < i.val := by omega
            rw [hzero_m i hgt1, mul_zero]
          · simp [adjGivens, hiP.1, hiP.2, hik]
      have hO'_00_nn : 0 ≤ O' 0 0 := by
        dsimp only [O', G₀]
        rw [Matrix.mul_apply, ← Finset.sum_subset P01.subset_univ (hout01 0),
          Finset.sum_pair hpair01]
        simp only [adjGivens, i₀, i₁, Fin.val_zero, Nat.zero_add, one_ne_zero, and_self,
          and_false, ↓reduceIte]
        exact (adjGivens_plane_elim (O_m i₀ 0) (O_m i₁ 0)).1
      have hO'_i0 : ∀ i : Fin (m + 1), O' i.succ 0 = 0 := by
        intro i
        dsimp only [O', G₀]
        rw [Matrix.mul_apply, ← Finset.sum_subset P01.subset_univ (hout01 i.succ),
          Finset.sum_pair hpair01]
        by_cases hi1 : i.succ = i₁
        · rw [hi1]
          simp only [adjGivens, i₀, i₁, Fin.val_zero, Nat.zero_add, one_ne_zero, and_self,
            and_false, false_and, ↓reduceIte]
          exact (adjGivens_plane_elim (O_m i₀ 0) (O_m i₁ 0)).2
        · have hi_ne0 : i.val ≠ 0 := fun h0 => hi1 (Fin.ext (by simp [i₁, h0]))
          have hg1 : adjGivens (m + 2) 0 φ₀ i.succ i₀ = 0 := by
            dsimp only [adjGivens, i₀, Fin.val_succ, Fin.val_zero]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg (Fin.succ_ne_zero i)]
          have hg2 : adjGivens (m + 2) 0 φ₀ i.succ i₁ = 0 := by
            dsimp only [adjGivens, i₁, Fin.val_succ]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg hi1]
          rw [hg1, hg2, zero_mul, zero_mul, add_zero]
      have hO'_00_eq1 : O' 0 0 = 1 := by
        have hcol0 := congrFun (congrFun hL' 0) 0
        rw [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply_eq] at hcol0
        simp only [Matrix.transpose_apply] at hcol0
        have htail0 : (∑ i : Fin (m + 1), O' i.succ 0 * O' i.succ 0) = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hO'_i0 i, zero_mul]
        rw [htail0, add_zero] at hcol0
        nlinarith only [hcol0, hO'_00_nn, sq_nonneg (O' 0 0 - 1)]
      have hO'_0j : ∀ j : Fin (m + 1), O' 0 j.succ = 0 := by
        have hrow0 := congrFun (congrFun hR' 0) 0
        rw [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply_eq] at hrow0
        simp only [Matrix.transpose_apply, hO'_00_eq1, mul_one] at hrow0
        have hsum0 : (∑ j : Fin (m + 1), O' 0 j.succ ^ 2) = 0 := by
          have hs : (∑ j : Fin (m + 1), O' 0 j.succ ^ 2) =
              ∑ j : Fin (m + 1), O' 0 j.succ * O' 0 j.succ :=
            Finset.sum_congr rfl fun _ _ => sq _
          linarith only [hrow0, hs]
        intro j
        have hle := Finset.single_le_sum (f := fun k : Fin (m + 1) => O' 0 k.succ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
        rw [hsum0] at hle
        exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
      let O'' := O'.submatrix Fin.succ Fin.succ
      have hL'' : O''ᵀ * O'' = 1 := by
        ext i j
        have h := congrFun (congrFun hL' i.succ) j.succ
        rw [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, hO'_0j i, zero_mul,
          zero_add] at h
        rw [Matrix.mul_apply]
        have hsum : (∑ x : Fin (m + 1), O''ᵀ i x * O'' x j) =
            ∑ x : Fin (m + 1), O'ᵀ i.succ x.succ * O' x.succ j.succ :=
          Finset.sum_congr rfl fun _ _ => rfl
        rw [hsum, h]
        simp only [Matrix.one_apply, Fin.succ_inj]
      have hR'' : O'' * O''ᵀ = 1 := by
        ext i j
        have h := congrFun (congrFun hR' i.succ) j.succ
        rw [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, hO'_i0 i, zero_mul,
          zero_add] at h
        rw [Matrix.mul_apply]
        have hsum : (∑ x : Fin (m + 1), O'' i x * O''ᵀ x j) =
            ∑ x : Fin (m + 1), O' i.succ x.succ * O'ᵀ x.succ j.succ :=
          Finset.sum_congr rfl fun _ _ => rfl
        rw [hsum, h]
        simp only [Matrix.one_apply, Fin.succ_inj]
      have hdet'' : O''.det = 1 := by
        have hd := Matrix.det_succ_row_zero O'
        have h0sa : Fin.succAbove (0 : Fin (m + 2)) = Fin.succ := funext Fin.zero_succAbove
        rw [hdet', Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, hO'_00_eq1, one_mul,
          h0sa, Finset.sum_eq_zero (fun j _ => by rw [hO'_0j j, mul_zero, zero_mul]),
          add_zero] at hd
        exact hd.symm
      obtain ⟨L_sub, hlen_sub, hp_sub, hO''_eq⟩ :=
        exists_adjGivens_prod_eq_of_specialOrthogonal (m + 1) O'' hL'' hR'' hdet''
      have hlift_prod : ∀ (L : List (ℕ × ℝ)), (∀ p ∈ L, p.1 + 1 < m + 1) →
          let P := (L.map fun p => adjGivens (m + 2) (p.1 + 1) p.2).prod
          P 0 0 = 1 ∧
          (∀ i : Fin (m + 1), P i.succ 0 = 0) ∧
          (∀ j : Fin (m + 1), P 0 j.succ = 0) ∧
          P.submatrix Fin.succ Fin.succ = (L.map fun p => adjGivens (m + 1) p.1 p.2).prod := by
        intro L
        induction L with
        | nil =>
            intro _
            simp only [List.map_nil, List.prod_nil, Matrix.one_apply_eq, true_and]
            refine ⟨fun i => Matrix.one_apply_ne (Fin.succ_ne_zero i),
              fun j => Matrix.one_apply_ne (Fin.succ_ne_zero j).symm, ?_⟩
            ext i j; simp [Matrix.one_apply, Fin.succ_inj]
        | cons p tail ih =>
            intro hp
            have hp0 : p.1 + 1 < m + 1 := hp p (List.mem_cons.mpr (Or.inl rfl))
            have hpt : ∀ q ∈ tail, q.1 + 1 < m + 1 :=
              fun q hq => hp q (List.mem_cons.mpr (Or.inr hq))
            obtain ⟨h1, h2, h3, h4⟩ := adjGivens_succ_lift hp0 p.2
            obtain ⟨t1, t2, t3, t4⟩ := ih hpt
            obtain ⟨m1, m2, m3, m4⟩ := isOneDirectSum_mul h1 h2 h3 t1 t2 t3
            simp only [List.map_cons, List.prod_cons]
            exact ⟨m1, m2, m3, m4.trans (by rw [h4, t4])⟩
      obtain ⟨hP00, hPi0, hP0j, hPsub⟩ := hlift_prod L_sub hp_sub
      have hO'_eq_lift : O' = (L_sub.map fun p => adjGivens (m + 2) (p.1 + 1) p.2).prod := by
        ext i j
        refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
        · rw [hO'_00_eq1, hP00]
        · rw [hO'_0j j', hP0j j']
        · rw [hO'_i0 i', hPi0 i']
        · change O'' i' j' = ((L_sub.map fun p => adjGivens (m + 2) (p.1 + 1) p.2).prod).submatrix
            Fin.succ Fin.succ i' j'
          rw [hPsub, ← hO''_eq]
      let L_tot : List (ℕ × ℝ) :=
        L_bot ++ [(0, -φ₀)] ++ L_sub.map (fun p => (p.1 + 1, p.2))
      refine ⟨L_tot, ?_, ?_, ?_⟩
      · simp only [L_tot, List.length_append, List.length_singleton, List.length_map, hlen_bot]
        have hstep := choose2_step_eq m
        rw [show m + 1 - 1 = m by omega] at hlen_sub
        rw [show m + 2 - 1 = m + 1 by omega]
        omega
      · intro p hp
        simp only [L_tot, List.mem_append, List.mem_singleton, List.mem_map] at hp
        rcases hp with (hp1 | rfl) | ⟨q, hq, rfl⟩
        · exact hp_bot p hp1
        · omega
        · have := hp_sub q hq; omega
      · simp only [L_tot, List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton, List.map_map, Function.comp_def]
        rw [← hO'_eq_lift, mul_assoc, ← hOm_eq, ← hO_bot]

/-! ### Abstract Clifford even-subspace commutant rigidity -/

/-- Ordered product of Clifford generators over a list `L : List (Fin m)` masked by `f`. -/
def cliffordListProd {A : Type*} [Ring A] {m : ℕ} (γ : Fin m → A)
    (L : List (Fin m)) (f : Fin m → Bool) : A :=
  (L.map fun a => if f a then γ a else 1).prod

/-- Canonical Clifford monomial `∏_{a : Fin m} γ_a^{f(a)}`. -/
def cliffordMonomial {A : Type*} [Ring A] {m : ℕ} (γ : Fin m → A) (f : Fin m → Bool) : A :=
  cliffordListProd γ (List.finRange m) f

/-- Even Clifford `ℂ`-subspace spanned by all even-weight Clifford monomials. -/
def evenCliffordSubspace {A : Type*} [CStarAlgebra A] {m : ℕ} (γ : Fin m → A) : Submodule ℂ A :=
  Submodule.span ℂ {M : A | ∃ f : Fin m → Bool,
    Even (Finset.univ.filter fun a => f a = true).card ∧ M = cliffordMonomial γ f}

/-- `ℂ`-subalgebra generated by quadratic Clifford elements `{γ_a γ_b : a ≠ b}`. -/
def evenCliffordAdjoin {A : Type*} [CStarAlgebra A] {m : ℕ} (γ : Fin m → A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ {X : A | ∃ a b : Fin m, a ≠ b ∧ X = γ a * γ b}

private theorem mul_cliffordListProd_toggle {A : Type*} [CStarAlgebra A] {m : ℕ}
    {γ : Fin m → A} (hsq : ∀ a, γ a * γ a = 1)
    (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a))
    (c : Fin m) :
    ∀ (L : List (Fin m)), L.Nodup → c ∈ L → ∀ (f : Fin m → Bool),
      ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        γ c * cliffordListProd γ L f = ε • cliffordListProd γ L (Function.update f c (!f c))
  | [], _, hc, _ => (List.not_mem_nil hc).elim
  | d :: tail, hnd, hc, f => by
      obtain ⟨hd_not, hnd_tail⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hc with rfl | hc_tail
      · have htail_eq : cliffordListProd γ tail (Function.update f c (!f c)) =
            cliffordListProd γ tail f := by
          unfold cliffordListProd
          congr 1
          refine List.map_congr_left fun a ha => ?_
          have hac : a ≠ c := fun h => hd_not (h ▸ ha)
          rw [Function.update_of_ne hac]
        refine ⟨1, Or.inl rfl, ?_⟩
        rw [one_smul]
        change γ c * ((if f c then γ c else 1) * cliffordListProd γ tail f) =
          (if Function.update f c (!f c) c then γ c else 1) *
            cliffordListProd γ tail (Function.update f c (!f c))
        rw [Function.update_self, htail_eq]
        cases hfc : f c
        · simp
        · simp [← mul_assoc, hsq c]
      · have hcd : c ≠ d := fun h => hd_not (h ▸ hc_tail)
        obtain ⟨ε, hε, ih⟩ := mul_cliffordListProd_toggle hsq hanti c tail hnd_tail hc_tail f
        simp only [cliffordListProd, List.map_cons, List.prod_cons, Function.update_of_ne hcd.symm]
        cases hfd : f d
        · refine ⟨ε, hε, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
          exact ih
        · refine ⟨-ε, ?_, ?_⟩
          · rcases hε with rfl | rfl <;> [exact Or.inr rfl; exact Or.inl (by norm_num)]
          · simp only [↓reduceIte]
            calc γ c * (γ d * cliffordListProd γ tail f)
                = (γ c * γ d) * cliffordListProd γ tail f := (mul_assoc _ _ _).symm
              _ = -(γ d * (γ c * cliffordListProd γ tail f)) := by
                  rw [hanti c d hcd, neg_mul, mul_assoc]
              _ = (-ε) • (γ d * cliffordListProd γ tail (Function.update f c (!f c))) := by
                  rw [ih, mul_smul_comm, neg_smul]

private theorem filter_update_not_even_iff {m : ℕ} (f : Fin m → Bool) (c : Fin m) :
    Even (Finset.univ.filter fun a => Function.update f c (!f c) a = true).card ↔
      ¬ Even (Finset.univ.filter fun a => f a = true).card := by
  let S := Finset.univ.filter fun a => f a = true
  let S' := Finset.univ.filter fun a => Function.update f c (!f c) a = true
  change Even S'.card ↔ ¬ Even S.card
  cases hfc : f c
  · have hc_not : c ∉ S := by simp [S, hfc]
    have hS' : S' = insert c S := by
      ext a; by_cases hac : a = c
      · subst hac; simp [S', hfc]
      · simp [S', S, hac]
    rw [hS', Finset.card_insert_of_notMem hc_not, Nat.even_add_one]
  · have hc_in : c ∈ S := by simp [S, hfc]
    have hS' : S = insert c S' := by
      ext a; by_cases hac : a = c
      · subst hac; simp [S, S', hfc]
      · simp [S, S', hac]
    have hc_not' : c ∉ S' := by simp [S', hfc]
    have hcard : S.card = S'.card + 1 := by rw [hS', Finset.card_insert_of_notMem hc_not']
    rw [hcard, Nat.even_add_one, not_not]

private theorem evenCliffordAdjoin_le_subspace {A : Type*} [CStarAlgebra A] {m : ℕ}
    {γ : Fin m → A} (hsq : ∀ a, γ a * γ a = 1)
    (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a)) :
    (evenCliffordAdjoin γ).toSubmodule ≤ evenCliffordSubspace γ := by
  have hone_mem : (1 : A) ∈ evenCliffordSubspace γ := by
    refine Submodule.subset_span ⟨fun _ => false, by simp, ?_⟩
    simp [cliffordMonomial, cliffordListProd]
  have hmul_two (a b : Fin m) : ∀ y ∈ evenCliffordSubspace γ,
      (γ a * γ b) * y ∈ evenCliffordSubspace γ := by
    intro y hy
    refine Submodule.span_induction ?_ (by simp)
      (fun u v _ _ hu hv => by rw [mul_add]; exact Submodule.add_mem _ hu hv)
      (fun r u _ hu => by rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu) hy
    rintro _ ⟨f, heven, rfl⟩
    obtain ⟨ε₁, _, h₁⟩ := mul_cliffordListProd_toggle hsq hanti b (List.finRange m)
      (List.nodup_finRange m) (List.mem_finRange b) f
    let f₁ := Function.update f b (!f b)
    obtain ⟨ε₂, _, h₂⟩ := mul_cliffordListProd_toggle hsq hanti a (List.finRange m)
      (List.nodup_finRange m) (List.mem_finRange a) f₁
    let f₂ := Function.update f₁ a (!f₁ a)
    have heven₂ : Even (Finset.univ.filter fun x => f₂ x = true).card := by
      dsimp [f₂, f₁]
      rw [filter_update_not_even_iff, filter_update_not_even_iff, not_not]
      exact heven
    have hprod_eq : (γ a * γ b) * cliffordMonomial γ f = (ε₁ * ε₂) • cliffordMonomial γ f₂ := by
      calc (γ a * γ b) * cliffordMonomial γ f
          = γ a * (γ b * cliffordListProd γ (List.finRange m) f) := mul_assoc _ _ _
        _ = (ε₁ * ε₂) • cliffordMonomial γ f₂ := by
            rw [h₁, mul_smul_comm, h₂, smul_smul]; rfl
    rw [hprod_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f₂, heven₂, rfl⟩)
  intro w hw
  have hact : ∀ y ∈ evenCliffordSubspace γ, w * y ∈ evenCliffordSubspace γ := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hw
    · rintro x ⟨a, b, _, rfl⟩ y hy
      exact hmul_two a b y hy
    · intro r y hy
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact Submodule.smul_mem _ r hy
    · intro x₁ x₂ _ _ hx₁ hx₂ y hy
      rw [add_mul]; exact Submodule.add_mem _ (hx₁ y hy) (hx₂ y hy)
    · intro x₁ x₂ _ _ hx₁ hx₂ y hy
      rw [mul_assoc]; exact hx₁ _ (hx₂ y hy)
  simpa only [mul_one] using hact 1 hone_mem

private theorem isClosed_evenCliffordAdjoin {A : Type*} [CStarAlgebra A] {m : ℕ}
    {γ : Fin m → A} (hsq : ∀ a, γ a * γ a = 1)
    (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a)) :
    IsClosed (evenCliffordAdjoin γ : Set A) := by
  have hfin_set : {M : A | ∃ f : Fin m → Bool,
      Even (Finset.univ.filter fun a => f a = true).card ∧ M = cliffordMonomial γ f}.Finite := by
    refine ((Set.finite_univ : (Set.univ : Set (Fin m → Bool)).Finite).image
      (cliffordMonomial γ)).subset ?_
    rintro _ ⟨f, _, rfl⟩
    exact ⟨f, Set.mem_univ f, rfl⟩
  haveI : FiniteDimensional ℂ (evenCliffordSubspace γ) :=
    FiniteDimensional.span_of_finite ℂ hfin_set
  have hle := evenCliffordAdjoin_le_subspace hsq hanti
  haveI : FiniteDimensional ℂ (evenCliffordAdjoin γ).toSubmodule :=
    Submodule.finiteDimensional_of_le hle
  exact (evenCliffordAdjoin γ).toSubmodule.closed_of_finiteDimensional

private theorem conj_cliffordListProd_eq_pow {A : Type*} [CStarAlgebra A] {m : ℕ}
    {γ : Fin m → A} (hsq : ∀ a, γ a * γ a = 1)
    (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a))
    (c : Fin m) (f : Fin m → Bool) :
    ∀ L : List (Fin m),
      γ c * cliffordListProd γ L f * γ c =
        ((-1 : ℂ) ^ (L.filter fun a => decide (f a = true ∧ a ≠ c)).length) •
          cliffordListProd γ L f
  | [] => by simp [cliffordListProd, hsq c]
  | a :: tail => by
      have ih := conj_cliffordListProd_eq_pow hsq hanti c f tail
      have hcons : cliffordListProd γ (a :: tail) f =
          (if f a = true then γ a else 1) * cliffordListProd γ tail f := rfl
      have hsplit : γ c * ((if f a = true then γ a else 1) * cliffordListProd γ tail f) * γ c =
          (γ c * (if f a = true then γ a else 1) * γ c) *
            (γ c * cliffordListProd γ tail f * γ c) := by
        calc γ c * ((if f a = true then γ a else 1) * cliffordListProd γ tail f) * γ c
            = γ c * (if f a = true then γ a else 1) * (γ c * γ c) *
                cliffordListProd γ tail f * γ c := by rw [hsq c, mul_one]; simp only [mul_assoc]
          _ = _ := by simp only [mul_assoc]
      rw [hcons, List.filter_cons, hsplit, ih]
      by_cases hfa : f a = true
      · by_cases hac : a = c
        · subst hac
          simp [hfa, hsq a]
        · have hneg : γ c * γ a * γ c = (-1 : ℂ) • γ a := by
            rw [hanti c a (Ne.symm hac), neg_mul, mul_assoc, hsq c, mul_one, neg_one_smul]
          simp [hfa, hac, hneg, pow_succ]
      · simp [hfa, hsq c]

/-- Abstract Clifford even-subspace commutant rigidity: over any nontrivial `C*`-algebra `A`, if
`γ : Fin m → A` satisfies `γ_a² = 1` and `γ_a γ_b = -γ_b γ_a` (`a ≠ b`), then every unitary
`W ∈ evenCliffordSubspace γ` commuting with all `γ_c` is a unit-modulus scalar `z • 1`. -/
theorem eq_scalar_one_of_mem_evenClifford_commutant {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {m : ℕ} {γ : Fin m → A}
    (hsq : ∀ a, γ a * γ a = 1) (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a))
    {W : A} (hW_even : W ∈ evenCliffordSubspace γ) (hW_unit : W ∈ unitary A)
    (hW_comm : ∀ c : Fin m, W * γ c = γ c * W) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ W = z • (1 : A) := by
  let twirl (c : Fin m) : A →ₗ[ℂ] A :=
    { toFun := fun X => (1 / 2 : ℂ) • (X + γ c * X * γ c)
      map_add' := fun X Y => by
        rw [← smul_add]
        refine congrArg ((1 / 2 : ℂ) • ·) ?_
        rw [mul_add, add_mul]; abel
      map_smul' := fun r X => by
        simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul,
          mul_comm (1 / 2 : ℂ) r] }
  let foldTwirl : List (Fin m) → A →ₗ[ℂ] A := fun L =>
    L.foldr (fun c acc => (twirl c).comp acc) LinearMap.id
  have htwirl_fix_W : ∀ L : List (Fin m), foldTwirl L W = W := by
    intro L
    induction L with
    | nil => rfl
    | cons c tail ih =>
        change twirl c (foldTwirl tail W) = W
        rw [ih]
        dsimp [twirl]
        rw [← hW_comm c, mul_assoc, hsq c, mul_one, ← two_smul ℂ W, smul_smul]
        norm_num
  have htwirl_one : ∀ c : Fin m, twirl c 1 = 1 := fun c => by
    dsimp [twirl]; rw [mul_one, hsq c, ← two_smul ℂ (1 : A), smul_smul]; norm_num
  have hfold_one : ∀ L : List (Fin m), foldTwirl L 1 = 1 := by
    intro L; induction L with
    | nil => rfl
    | cons c tail ih => change twirl c (foldTwirl tail 1) = 1; rw [ih, htwirl_one]
  have hmon_twirl (f : Fin m → Bool)
      (heven : Even (Finset.univ.filter fun a => f a = true).card) :
      foldTwirl (List.finRange m) (cliffordMonomial γ f) ∈ Submodule.span ℂ {(1 : A)} := by
    by_cases hex : ∃ c : Fin m, f c = true
    · obtain ⟨c₀, hc₀⟩ := hex
      have hanti_c₀ : γ c₀ * cliffordMonomial γ f * γ c₀ = -cliffordMonomial γ f := by
        unfold cliffordMonomial
        rw [conj_cliffordListProd_eq_pow hsq hanti c₀ f (List.finRange m)]
        let S_f := Finset.univ.filter fun a => f a = true
        have hc₀_mem : c₀ ∈ S_f := Finset.mem_filter.mpr ⟨Finset.mem_univ c₀, hc₀⟩
        have hlen_eq : ((List.finRange m).filter fun a => decide (f a = true ∧ a ≠ c₀)).length =
            (S_f.erase c₀).card := by
          have hcard_nodup : ∀ (L : List (Fin m)), L.Nodup → L.toFinset.card = L.length := by
            intro L hnd
            induction L with
            | nil => simp
            | cons x xs ih =>
                obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
                have hx' : x ∉ xs.toFinset := by simpa using hx
                rw [List.toFinset_cons, Finset.card_insert_of_notMem hx', ih hxs, List.length_cons]
          have hnodup := (List.nodup_finRange m).filter (fun a => decide (f a = true ∧ a ≠ c₀))
          rw [← hcard_nodup _ hnodup]
          congr 1; ext a
          simp [S_f, and_comm]
        have hodd : ¬ Even (S_f.erase c₀).card := by
          have hcard : (S_f.erase c₀).card + 1 = S_f.card := Finset.card_erase_add_one hc₀_mem
          intro hev_er
          rw [← hcard, Nat.even_add_one] at heven
          exact heven hev_er
        rw [hlen_eq, (Nat.not_even_iff_odd.mp hodd).neg_one_pow, neg_one_smul]
      have hstep_dich (d : Fin m) :
          twirl d (cliffordMonomial γ f) = cliffordMonomial γ f ∨
          twirl d (cliffordMonomial γ f) = 0 := by
        have hpow := conj_cliffordListProd_eq_pow hsq hanti d f (List.finRange m)
        rcases neg_one_pow_eq_or ℂ
          ((List.finRange m).filter fun a => decide (f a = true ∧ a ≠ d)).length with hp1 | hm1
        · left; dsimp [twirl]
          rw [cliffordMonomial, hpow, hp1, one_smul, ← two_smul ℂ, smul_smul]; norm_num
        · right; dsimp [twirl]
          rw [cliffordMonomial, hpow, hm1, neg_one_smul, add_neg_cancel, smul_zero]
      have hkill_c₀ : twirl c₀ (cliffordMonomial γ f) = 0 := by
        dsimp [twirl]; rw [hanti_c₀, add_neg_cancel, smul_zero]
      have hfold_kill : ∀ L : List (Fin m), c₀ ∈ L →
          foldTwirl L (cliffordMonomial γ f) = 0 := by
        intro L
        induction L with
        | nil => intro h; exact (List.not_mem_nil h).elim
        | cons d tail ih =>
            intro hmem
            change twirl d (foldTwirl tail (cliffordMonomial γ f)) = 0
            by_cases hc_tail : c₀ ∈ tail
            · rw [ih hc_tail, map_zero]
            · have hdc : d = c₀ := ((List.mem_cons.mp hmem).resolve_right hc_tail).symm
              subst hdc
              have hdich_tail : ∀ K : List (Fin m),
                  foldTwirl K (cliffordMonomial γ f) = cliffordMonomial γ f ∨
                  foldTwirl K (cliffordMonomial γ f) = 0 := by
                intro K; induction K with
                | nil => exact Or.inl rfl
                | cons e K' ihK =>
                    have hfe : foldTwirl (e :: K') (cliffordMonomial γ f) =
                        twirl e (foldTwirl K' (cliffordMonomial γ f)) := rfl
                    rw [hfe]
                    rcases ihK with heq | hz
                    · rw [heq]; exact hstep_dich e
                    · rw [hz, map_zero]; exact Or.inr rfl
              rcases hdich_tail tail with heq | hz
              · rw [heq, hkill_c₀]
              · rw [hz, map_zero]
      rw [hfold_kill (List.finRange m) (List.mem_finRange c₀)]
      exact Submodule.zero_mem _
    · push Not at hex
      have hf0 : f = fun _ => false := funext fun c => Bool.eq_false_iff.mpr (hex c)
      have hm1 : cliffordMonomial γ f = 1 := by
        rw [hf0]; simp [cliffordMonomial, cliffordListProd]
      rw [hm1, hfold_one]
      exact Submodule.subset_span rfl
  have hW_span : foldTwirl (List.finRange m) W ∈ Submodule.span ℂ {(1 : A)} := by
    refine Submodule.span_induction ?_ (by simp)
      (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
      (fun r x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ r hx) hW_even
    rintro _ ⟨f, heven, rfl⟩
    exact hmon_twirl f heven
  rw [htwirl_fix_W] at hW_span
  obtain ⟨z, hz_eq⟩ := Submodule.mem_span_singleton.mp hW_span
  refine ⟨z, ?_, hz_eq.symm⟩
  have h1 : ‖W‖ = 1 := CStarRing.norm_of_mem_unitary hW_unit
  rw [← hz_eq, norm_smul, norm_one, mul_one] at h1
  exact h1

/-! ## Section 3: Explicit Jordan-Wigner chain realization and `choose(N, 2)` survival tube -/

/-- Alternating `ZZ / XX` bond Pauli word on `n + 2` qubits: `(2, 2)` on even bonds,
`(0, 0)` on odd bonds. -/
def jwBondWord (n : ℕ) (e : Fin (n + 1)) : Fin (n + 2) → Option (Fin 3) :=
  couplingWord e (if Even e.val then (2, 2) else (0, 0))

/-- Predicate identifying the `n + 1` alternating `ZZ / XX` Jordan-Wigner bond labels in
`PathLabel n`. -/
def isJWChainLabel {n : ℕ} : PathLabel n → Prop
  | .inl _ => False
  | .inr (e, pq) => pq = if Even e.val then (2, 2) else (0, 0)

instance {n : ℕ} (l : PathLabel n) : Decidable (isJWChainLabel l) := by
  cases l with
  | inl _ => exact isFalse id
  | inr epq => dsimp [isJWChainLabel]; infer_instance

/-- Jordan-Wigner `1`-Majorana-per-site Pauli string `γ_a = Y_0 ⋯ Y_{a-1} (X_a or Z_a)` on
`n + 2` qubits (`X_a` for `Even a.val`, `Z_a` for odd `a.val`). -/
def jwMajoranaWord (n : ℕ) (a : Fin (n + 2)) (s : Fin (n + 2)) : Option (Fin 3) :=
  if s.val < a.val then some 1
  else if s.val = a.val then (if Even a.val then some 0 else some 2)
  else none

/-- Matrix realization `γ_a = finitePauliMatrix (jwMajoranaWord n a) : Register (n + 2)`. -/
def jwMajorana (n : ℕ) (a : Fin (n + 2)) : Register (n + 2) :=
  finitePauliMatrix (jwMajoranaWord n a)

private theorem jwMajoranaWord_injective (n : ℕ) : Function.Injective (jwMajoranaWord n) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := congrFun hab a
    have ha_lt : a.val < b.val := hlt
    simp only [jwMajoranaWord, lt_irrefl, ↓reduceIte, ha_lt] at h
    split_ifs at h <;> simp at h
  · have h := congrFun hab b
    have hb_lt : b.val < a.val := hgt
    simp only [jwMajoranaWord, lt_irrefl, ↓reduceIte, hb_lt] at h
    split_ifs at h <;> simp at h

private theorem jwMajorana_sq (n : ℕ) (a : Fin (n + 2)) :
    jwMajorana n a * jwMajorana n a = 1 :=
  finitePauliMatrix_mul_self _

private theorem jwMajorana_star (n : ℕ) (a : Fin (n + 2)) :
    star (jwMajorana n a) = jwMajorana n a :=
  finitePauliMatrix_isHermitian _

private theorem jwMajorana_anticommute (n : ℕ) {a b : Fin (n + 2)} (hab : a ≠ b) :
    jwMajorana n a * jwMajorana n b = -(jwMajorana n b * jwMajorana n a) := by
  have hlt_anti : ∀ {x y : Fin (n + 2)}, x < y →
      jwMajorana n x * jwMajorana n y = -(jwMajorana n y * jwMajorana n x) := by
    intro x y hxy
    unfold jwMajorana
    rw [finitePauliMatrix_mul, finitePauliMatrix_mul]
    have hlbl : (fun s => optMul (jwMajoranaWord n x s) (jwMajoranaWord n y s)) =
        fun s => optMul (jwMajoranaWord n y s) (jwMajoranaWord n x s) :=
      funext fun s => optMul_comm _ _
    have hph : (∏ s : Fin (n + 2), optPhase (jwMajoranaWord n x s) (jwMajoranaWord n y s)) =
        -(∏ s : Fin (n + 2), optPhase (jwMajoranaWord n y s) (jwMajoranaWord n x s)) := by
      have hout1 : ∀ s ∈ ({x} : Finset (Fin (n + 2)))ᶜ,
          optPhase (jwMajoranaWord n x s) (jwMajoranaWord n y s) = 1 := by
        intro s hs
        have hsx : s.val ≠ x.val := fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
        rcases lt_or_gt_of_ne hsx with hslt | hsgt
        · have hsy : s.val < y.val := hslt.trans hxy
          simp [jwMajoranaWord, hslt, hsy, optPhase]
        · have h1 : ¬ s.val < x.val := not_lt.mpr hsgt.le
          simp [jwMajoranaWord, h1, hsx, optPhase]
      have hout2 : ∀ s ∈ ({x} : Finset (Fin (n + 2)))ᶜ,
          optPhase (jwMajoranaWord n y s) (jwMajoranaWord n x s) = 1 := by
        intro s hs
        have hsx : s.val ≠ x.val := fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
        rcases lt_or_gt_of_ne hsx with hslt | hsgt
        · have hsy : s.val < y.val := hslt.trans hxy
          simp [jwMajoranaWord, hslt, hsy, optPhase]
        · have h1 : ¬ s.val < x.val := not_lt.mpr hsgt.le
          simp [jwMajoranaWord, h1, hsx, optPhase_none_right]
      rw [← Finset.prod_mul_prod_compl ({x} : Finset (Fin (n + 2))),
        ← Finset.prod_mul_prod_compl ({x} : Finset (Fin (n + 2))),
        Finset.prod_singleton, Finset.prod_singleton,
        Finset.prod_eq_one hout1, Finset.prod_eq_one hout2, mul_one, mul_one]
      have hx_lt_y : x.val < y.val := hxy
      simp only [jwMajoranaWord, lt_irrefl, ↓reduceIte, hx_lt_y]
      by_cases hev : Even x.val <;> simp [hev, optPhase]
    rw [hlbl, hph, neg_smul]
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact hlt_anti hlt
  · rw [hlt_anti hgt, neg_neg]

private def jwSign {n : ℕ} (e : Fin (n + 1)) : ℝ :=
  if Even e.val then -1 else 1

private theorem jwSign_sq {n : ℕ} (e : Fin (n + 1)) : jwSign e * jwSign e = 1 := by
  unfold jwSign; split_ifs <;> norm_num

private theorem jwBond_skew_eq_majorana_pair (n : ℕ) (e : Fin (n + 1)) :
    (-Complex.I) • finitePauliMatrix (jwBondWord n e) =
      ((jwSign e : ℝ) : ℂ) • (jwMajorana n e.castSucc * jwMajorana n e.succ) := by
  unfold jwMajorana
  rw [finitePauliMatrix_mul]
  have hlbl : (fun s : Fin (n + 2) =>
      optMul (jwMajoranaWord n e.castSucc s) (jwMajoranaWord n e.succ s)) =
      jwBondWord n e := by
    funext s
    by_cases hs1 : s = e.castSucc
    · subst hs1
      have hlt_v : e.val < e.val + 1 := Nat.lt_succ_self e.val
      simp only [jwMajoranaWord, couplingWord, jwBondWord, Fin.val_castSucc, Fin.val_succ,
        lt_irrefl, hlt_v, ↓reduceIte]
      by_cases hev : Even e.val <;> simp only [hev, ↓reduceIte, optMul] <;> decide
    · by_cases hs2 : s = e.succ
      · subst hs2
        have h1 : ¬ (e.val + 1 < e.val) := by omega
        have h2 : e.val + 1 ≠ e.val := by omega
        simp only [jwMajoranaWord, couplingWord, jwBondWord, Fin.val_castSucc, Fin.val_succ,
          h1, h2, lt_irrefl, hs1, ↓reduceIte, optMul]
        by_cases hev : Even e.val
        · have hne1 : ¬ Even (e.val + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hev
          simp only [hev, hne1, ↓reduceIte]
        · have he1 : Even (e.val + 1) := (Nat.even_add_one).mpr hev
          simp only [hev, he1, ↓reduceIte]
      · have hv1 : s.val ≠ e.val := fun h => hs1 (Fin.ext h)
        have hv2 : s.val ≠ e.val + 1 := fun h => hs2 (Fin.ext h)
        rcases lt_or_gt_of_ne hv1 with hslt | hsgt
        · have hslt2 : s.val < e.val + 1 := by omega
          simp only [jwMajoranaWord, Fin.val_castSucc, Fin.val_succ, hslt, hslt2, ↓reduceIte,
            optMul, jwBondWord, couplingWord, hs1, hs2]
        · have hn1 : ¬ s.val < e.val := by omega
          have hn2 : ¬ s.val < e.val + 1 := by omega
          simp only [jwMajoranaWord, Fin.val_castSucc, Fin.val_succ, hn1, hn2, hv1, hv2,
            ↓reduceIte, optMul, jwBondWord, couplingWord, hs1, hs2]
  have hph : (∏ s : Fin (n + 2),
      optPhase (jwMajoranaWord n e.castSucc s) (jwMajoranaWord n e.succ s)) =
      if Even e.val then Complex.I else -Complex.I := by
    have hout : ∀ s ∈ ({e.castSucc} : Finset (Fin (n + 2)))ᶜ,
        optPhase (jwMajoranaWord n e.castSucc s) (jwMajoranaWord n e.succ s) = 1 := by
      intro s hs
      have hs1 : s.val ≠ e.val :=
        fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
      rcases lt_or_gt_of_ne hs1 with hslt | hsgt
      · have hslt2 : s.val < e.val + 1 := by omega
        simp only [jwMajoranaWord, Fin.val_castSucc, Fin.val_succ, hslt, hslt2, ↓reduceIte,
          optPhase]
      · have hn1 : ¬ s.val < e.val := by omega
        simp only [jwMajoranaWord, Fin.val_castSucc, Fin.val_succ, hn1, hs1, ↓reduceIte, optPhase]
    rw [← Finset.prod_mul_prod_compl ({e.castSucc} : Finset (Fin (n + 2))),
      Finset.prod_singleton, Finset.prod_eq_one hout, mul_one]
    have hlt_v : e.val < e.val + 1 := Nat.lt_succ_self e.val
    simp only [jwMajoranaWord, Fin.val_castSucc, Fin.val_succ, lt_irrefl, hlt_v, ↓reduceIte]
    by_cases hev : Even e.val <;> simp [hev, optPhase]
  rw [hlbl, hph, smul_smul]
  congr 1
  unfold jwSign
  by_cases hev : Even e.val <;> simp [hev]

/-- Real linear subspace of `Register (n + 2)` spanned by the `n + 2` Majorana operators. -/
def realMajoranaSubspace (n : ℕ) : Submodule ℝ (Register (n + 2)) :=
  Submodule.span ℝ (Set.range (jwMajorana n))

/-- Real Majorana coordinate `majCoeff n M a = Re(Tr(γ_a M)) / 2^{n + 2}`. -/
def majCoeff (n : ℕ) (M : Register (n + 2)) (a : Fin (n + 2)) : ℝ :=
  (Matrix.trace (jwMajorana n a * M)).re / (2 ^ (n + 2) : ℝ)

/-- Induced `(n + 2) × (n + 2)` Majorana action matrix `(majMat n U)_{a, c}` of `U`. -/
def majMat (n : ℕ) (U : Register (n + 2)) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  fun a c => majCoeff n (U * jwMajorana n c * star U) a

private theorem majCoeff_majorana (n : ℕ) (a b : Fin (n + 2)) :
    majCoeff n (jwMajorana n b) a = if a = b then 1 else 0 := by
  unfold majCoeff jwMajorana
  rw [trace_pauli_mul, Fintype.card_fin]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl,
      show ((2 : ℂ) ^ (n + 2)).re = (2 : ℝ) ^ (n + 2) by
        rw [show ((2 : ℂ) ^ (n + 2)) = (((2 : ℝ) ^ (n + 2) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_re]]
    exact div_self (pow_ne_zero _ two_ne_zero)
  · rw [if_neg (fun h => hab (jwMajoranaWord_injective n h)), if_neg hab, Complex.zero_re, zero_div]

private theorem majCoeff_add (n : ℕ) (M₁ M₂ : Register (n + 2)) (a : Fin (n + 2)) :
    majCoeff n (M₁ + M₂) a = majCoeff n M₁ a + majCoeff n M₂ a := by
  unfold majCoeff
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, add_div]

private theorem majCoeff_real_smul (n : ℕ) (r : ℝ) (M : Register (n + 2)) (a : Fin (n + 2)) :
    majCoeff n (r • M) a = r * majCoeff n M a := by
  unfold majCoeff
  have h1 : jwMajorana n a * (r • M) = (r : ℂ) • (jwMajorana n a * M) := by
    rw [← Complex.coe_smul, Matrix.mul_smul]
  rw [h1, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_div_assoc]

private theorem eq_sum_majCoeff_of_mem_realMajoranaSubspace {n : ℕ} {M : Register (n + 2)}
    (hM : M ∈ realMajoranaSubspace n) :
    M = ∑ a : Fin (n + 2), ((majCoeff n M a : ℝ) : ℂ) • jwMajorana n a := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hM
  · rintro _ ⟨b, rfl⟩
    simp_rw [majCoeff_majorana]
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab; simp [hab]
    · simp
  · unfold majCoeff
    simp [Matrix.trace_zero, zero_div]
  · intro x y _ _ hx hy
    simp_rw [majCoeff_add, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  · intro r x _ hx
    simp_rw [majCoeff_real_smul, Complex.ofReal_mul, ← smul_smul, ← Finset.smul_sum, ← Complex.coe_smul]
    rw [Complex.coe_smul, ← hx]
    exact (Complex.coe_smul r x).symm

private theorem majMat_one (n : ℕ) : majMat n 1 = 1 := by
  ext a c
  simp [majMat, majCoeff_majorana, Matrix.one_apply]

private theorem majMat_mul {n : ℕ} {U₁ U₂ : Register (n + 2)}
    (hU₂ : ∀ c : Fin (n + 2), U₂ * jwMajorana n c * star U₂ ∈ realMajoranaSubspace n) :
    majMat n (U₁ * U₂) = majMat n U₁ * majMat n U₂ := by
  ext a c
  rw [Matrix.mul_apply]
  have hexp := eq_sum_majCoeff_of_mem_realMajoranaSubspace (hU₂ c)
  have hconj : (U₁ * U₂) * jwMajorana n c * star (U₁ * U₂) =
      ∑ b : Fin (n + 2), (majMat n U₂ b c) • (U₁ * jwMajorana n b * star U₁) := by
    calc (U₁ * U₂) * jwMajorana n c * star (U₁ * U₂)
        = U₁ * (U₂ * jwMajorana n c * star U₂) * star U₁ := by
            rw [star_mul]; simp only [mul_assoc]
      _ = U₁ * (∑ b : Fin (n + 2), ((majMat n U₂ b c : ℝ) : ℂ) • jwMajorana n b) * star U₁ := by
            rw [hexp]; rfl
      _ = ∑ b : Fin (n + 2), (majMat n U₂ b c) • (U₁ * jwMajorana n b * star U₁) := by
            rw [Matrix.mul_sum, Matrix.sum_mul]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
  dsimp only [majMat]
  rw [hconj]
  have hsum_lin : ∀ (S : Finset (Fin (n + 2))) (f : Fin (n + 2) → ℝ)
      (g : Fin (n + 2) → Register (n + 2)),
      majCoeff n (∑ b ∈ S, f b • g b) a = ∑ b ∈ S, f b * majCoeff n (g b) a := by
    intro S f g
    induction S using Finset.induction_on with
    | empty => simp [majCoeff]
    | @insert b S hb ih =>
        rw [Finset.sum_insert hb, majCoeff_add, majCoeff_real_smul, ih, Finset.sum_insert hb]
  rw [hsum_lin]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

private theorem majMat_star_eq_transpose {n : ℕ} (U : Register (n + 2)) :
    majMat n (star U) = (majMat n U)ᵀ := by
  ext a c
  simp only [majMat, Matrix.transpose_apply, majCoeff, star_star]
  refine congrArg (· / (2 ^ (n + 2) : ℝ)) ?_
  have htr_star (X : Register (n + 2)) : star (Matrix.trace X) = Matrix.trace (star X) := by
    simp [Matrix.trace, star_sum]
  have hst_tr : star (Matrix.trace (jwMajorana n a * (star U * jwMajorana n c * U))) =
      Matrix.trace (jwMajorana n c * (U * jwMajorana n a * star U)) := by
    rw [htr_star, star_mul, star_mul, star_mul, star_star, jwMajorana_star, jwMajorana_star]
    calc Matrix.trace ((star U * (jwMajorana n c * U)) * jwMajorana n a)
        = Matrix.trace (star U * (jwMajorana n c * (U * jwMajorana n a))) := by
            simp only [mul_assoc]
      _ = Matrix.trace ((jwMajorana n c * (U * jwMajorana n a)) * star U) :=
            Matrix.trace_mul_comm (star U) _
      _ = Matrix.trace (jwMajorana n c * (U * jwMajorana n a * star U)) := by
            simp only [mul_assoc]
  have hre := congrArg Complex.re hst_tr
  simpa only [Complex.star_def, Complex.conj_re] using hre

private theorem jwBondGate_preserves_and_majMat (n : ℕ) (e : Fin (n + 1)) (φ : ℝ) :
    let θ := jwSign e * (φ / 2)
    let U := unitaryEvolution (finitePauliMatrix (jwBondWord n e)) θ
    U ∈ unitary (Register (n + 2)) ∧
    U ∈ evenCliffordAdjoin (jwMajorana n) ∧
    star U ∈ evenCliffordAdjoin (jwMajorana n) ∧
    (∀ c : Fin (n + 2), U * jwMajorana n c * star U ∈ realMajoranaSubspace n) ∧
    majMat n U = adjGivens (n + 2) e.val φ ∧
    Realizes 1 U := by
  intro θ U
  let _ : NormedAlgebra ℚ (Register (n + 2)) := .restrictScalars ℚ ℂ (Register (n + 2))
  have hU_exp_eq : U = NormedSpace.exp (((φ / 2 : ℝ) : ℂ) •
      (jwMajorana n e.castSucc * jwMajorana n e.succ)) := by
    dsimp only [U, unitaryEvolution, θ]
    rw [jwBond_skew_eq_majorana_pair, ← Complex.coe_smul, smul_smul]
    refine congrArg NormedSpace.exp
      (congrArg (· • (jwMajorana n e.castSucc * jwMajorana n e.succ)) ?_)
    have hsq : (jwSign e : ℂ) * (jwSign e : ℂ) = 1 := by exact_mod_cast jwSign_sq e
    push_cast
    linear_combination (φ / 2 : ℂ) * hsq
  have hne_end : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
  have hgen_adjoin : jwMajorana n e.castSucc * jwMajorana n e.succ ∈
      evenCliffordAdjoin (jwMajorana n) :=
    Algebra.subset_adjoin ⟨e.castSucc, e.succ, hne_end, rfl⟩
  have hclosed := isClosed_evenCliffordAdjoin (jwMajorana_sq n) (fun _ _ h => jwMajorana_anticommute n h)
  have hU_adj : U ∈ evenCliffordAdjoin (jwMajorana n) := by
    rw [hU_exp_eq]
    exact NormedSpace.exp_mem (R := ℂ) hclosed (Subalgebra.smul_mem _ hgen_adjoin _)
  have hstU_adj : star U ∈ evenCliffordAdjoin (jwMajorana n) := by
    rw [hU_exp_eq, exp_skewPair_star_eq (jwMajorana_star n _) (jwMajorana_star n _)
      (jwMajorana_anticommute n hne_end)]
    exact NormedSpace.exp_mem (R := ℂ) hclosed (Subalgebra.smul_mem _ hgen_adjoin _)
  have hU_unit : U ∈ unitary (Register (n + 2)) :=
    unitaryEvolution_mem_unitary (finitePauliMatrix_isHermitian _) θ
  obtain ⟨hc1, hc2, hco⟩ := exp_skewPair_conj (jwMajorana_sq n e.castSucc) (jwMajorana_sq n e.succ)
    (jwMajorana_star n e.castSucc) (jwMajorana_star n e.succ)
    (jwMajorana_anticommute n hne_end) φ
  rw [← hU_exp_eq] at hc1 hc2 hco
  have hpres (c : Fin (n + 2)) : U * jwMajorana n c * star U ∈ realMajoranaSubspace n := by
    by_cases h1 : c = e.castSucc
    · subst h1; rw [hc1, Complex.coe_smul, Complex.coe_smul]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · by_cases h2 : c = e.succ
      · subst h2; rw [hc2, Complex.coe_smul, Complex.coe_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      · rw [hco (jwMajorana n c) (jwMajorana_anticommute n (Ne.symm h1))
          (jwMajorana_anticommute n (Ne.symm h2))]
        exact Submodule.subset_span ⟨c, rfl⟩
  have hmaj : majMat n U = adjGivens (n + 2) e.val φ := by
    ext a c
    dsimp only [majMat]
    by_cases h1 : c = e.castSucc
    · subst h1
      rw [hc1, Complex.coe_smul, Complex.coe_smul, majCoeff_add, majCoeff_real_smul, majCoeff_real_smul,
        majCoeff_majorana, majCoeff_majorana]
      by_cases ha1 : a = e.castSucc
      · subst ha1; simp [adjGivens, hne_end]
      · by_cases ha2 : a = e.succ
        · subst ha2; simp [adjGivens, hne_end.symm]
        · have hv1 : a.val ≠ e.val := fun h => ha1 (Fin.ext h)
          have hv2 : a.val ≠ e.val + 1 := fun h => ha2 (Fin.ext h)
          simp [adjGivens, ha1, ha2, hv1, hv2]
    · by_cases h2 : c = e.succ
      · subst h2
        rw [hc2, Complex.coe_smul, Complex.coe_smul, majCoeff_add, majCoeff_real_smul, majCoeff_real_smul,
          majCoeff_majorana, majCoeff_majorana]
        by_cases ha1 : a = e.castSucc
        · subst ha1; simp [adjGivens, hne_end]
        · by_cases ha2 : a = e.succ
          · subst ha2; simp [adjGivens, hne_end.symm]
          · have hv1 : a.val ≠ e.val := fun h => ha1 (Fin.ext h)
            have hv2 : a.val ≠ e.val + 1 := fun h => ha2 (Fin.ext h)
            simp [adjGivens, ha1, ha2, hv1, hv2]
      · rw [hco (jwMajorana n c) (jwMajorana_anticommute n (Ne.symm h1))
          (jwMajorana_anticommute n (Ne.symm h2)), majCoeff_majorana]
        have hc1v : c.val ≠ e.val := fun h => h1 (Fin.ext h)
        have hc2v : c.val ≠ e.val + 1 := fun h => h2 (Fin.ext h)
        simp [adjGivens, hc1v, hc2v]
  have hreal1 : Realizes 1 U := by
    have hn2 : 2 ≤ n + 2 := by omega
    have hw_le2 : pauliWeight (jwBondWord n e) ≤ 2 := by
      unfold pauliWeight jwBondWord
      have hsub : (Finset.univ.filter fun s =>
          couplingWord e (if Even e.val then (2, 2) else (0, 0)) s ≠ none) ⊆
          ({e.castSucc, e.succ} : Finset (Fin (n + 2))) := by
        intro s hs
        have hne := (Finset.mem_filter.mp hs).2
        by_contra hout
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
        exact hne (by simp [couplingWord, hout.1, hout.2])
      exact (Finset.card_le_card hsub).trans (Finset.card_pair hne_end).le
    have hnot_id : jwBondWord n e ≠ pauliIdentityLabel (n + 2) := by
      intro hid
      have h := congrFun hid e.castSucc
      simp only [jwBondWord, couplingWord, ↓reduceIte, pauliIdentityLabel] at h
      split_ifs at h
    let Q : PauliTracelessLabel (n + 2) 2 := ⟨jwBondWord n e, hw_le2, hnot_id⟩
    let H_b := finitePauliSelfAdjointBasis (Fin (n + 2)) (jwBondWord n e)
    have hc : realPauliCoefficient H_b Q.val = 1 := by
      change (finitePauliSelfAdjointBasis (Fin (n + 2))).repr
        ((finitePauliSelfAdjointBasis (Fin (n + 2))) (jwBondWord n e)) (jwBondWord n e) = 1
      rw [Module.Basis.repr_self, Finsupp.single_eq_same]
    obtain ⟨z, hz, G, hG⟩ := exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn2 H_b Q θ
    refine ⟨z, hz, TwoQubitCircuit.singleOn _ _ (Q.coveringPair_distinct hn2) G, le_rfl, ?_⟩
    rw [TwoQubitCircuit.singleOn_eval]
    simpa only [twoLocalSkewGenerator, hc, Complex.ofReal_one, one_smul, unitaryEvolution, U] using hG
  exact ⟨hU_unit, hU_adj, hstU_adj, hpres, hmaj, hreal1⟩

/-- Exact `choose(n + 2, 2) = (n + 2) * (n + 1) / 2`-gate `Spin(n + 2)` compilation of every
alternating `ZZ / XX` Jordan-Wigner chain Hamiltonian on `n + 2` qubits for **all** `t ∈ ℝ`. -/
theorem realizes_choose_two_of_alternatingJWChain {n : ℕ} (u : PathShell n)
    (hu : ∀ l : PathLabel n, ¬ isJWChainLabel l → u l = 0) (t : ℝ) :
    Realizes ((n + 2) * (n + 1) / 2) (unitaryEvolution (pathHamiltonian u) t) := by
  let _ : NormedAlgebra ℚ (Register (n + 2)) := .restrictScalars ℚ ℂ (Register (n + 2))
  let H := pathHamiltonian u
  have hH_sa : IsSelfAdjoint H := isSelfAdjoint_pathHamiltonian u
  let J : Fin (n + 1) → ℝ := fun e =>
    u (.inr (e, if Even e.val then (2, 2) else (0, 0)))
  have hH_eq : H = ∑ e : Fin (n + 1), ((J e : ℝ) : ℂ) • finitePauliMatrix (jwBondWord n e) := by
    dsimp only [H]
    rw [pathHamiltonian_eq_sum, Fintype.sum_sum_type]
    have hinl : (∑ x : Fin (n + 2) × Fin 3,
        ((u (.inl x) : ℝ) : ℂ) • finitePauliMatrix (pathWord (.inl x))) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        rw [hu (.inl x) id, Complex.ofReal_zero, zero_smul]
    rw [hinl, zero_add, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    let pq_e : Fin 3 × Fin 3 := if Even e.val then (2, 2) else (0, 0)
    rw [Finset.sum_eq_single pq_e]
    · rfl
    · intro pq _ hpq
      have hnot : ¬ isJWChainLabel (.inr (e, pq)) := hpq
      rw [hu (.inr (e, pq)) hnot, Complex.ofReal_zero, zero_smul]
    · simp
  have hclosed_adj := isClosed_evenCliffordAdjoin (jwMajorana_sq n)
    (fun _ _ h => jwMajorana_anticommute n h)
  have hskew_adjoin (s : ℝ) : s • ((-Complex.I) • H) ∈ evenCliffordAdjoin (jwMajorana n) := by
    rw [hH_eq, Finset.smul_sum, Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun e _ => ?_
    have h1 : s • ((-Complex.I) • (((J e : ℝ) : ℂ) • finitePauliMatrix (jwBondWord n e))) =
        ((s * J e * jwSign e : ℝ) : ℂ) • (jwMajorana n e.castSucc * jwMajorana n e.succ) := by
      rw [smul_comm (-Complex.I), jwBond_skew_eq_majorana_pair, ← Complex.coe_smul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    rw [h1]
    have hmem_e : jwMajorana n e.castSucc * jwMajorana n e.succ ∈
        evenCliffordAdjoin (jwMajorana n) :=
      Algebra.subset_adjoin ⟨e.castSucc, e.succ, e.castSucc_lt_succ.ne, rfl⟩
    exact Subalgebra.smul_mem _ hmem_e _
  have hUt_adjoin (s : ℝ) : unitaryEvolution H s ∈ evenCliffordAdjoin (jwMajorana n) :=
    NormedSpace.exp_mem (R := ℂ) hclosed_adj (hskew_adjoin s)
  have had_mem : ∀ M ∈ realMajoranaSubspace n,
      Complex.I • (H * M - M * H) ∈ realMajoranaSubspace n := by
    intro M hM
    refine Submodule.span_induction ?_ (by simp)
      (fun x y _ _ hx hy => by
        have h : H * (x + y) - (x + y) * H = (H * x - x * H) + (H * y - y * H) := by
          rw [mul_add, add_mul]; abel
        rw [h, smul_add]; exact Submodule.add_mem _ hx hy)
      (fun r x _ hx => by
        have h : Complex.I • (H * (r • x) - (r • x) * H) =
            r • (Complex.I • (H * x - x * H)) := by
          rw [← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_comm Complex.I,
            Complex.coe_smul]
        rw [h]; exact Submodule.smul_mem _ r hx) hM
    rintro _ ⟨c, rfl⟩
    rw [hH_eq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    have hPe : Complex.I • finitePauliMatrix (jwBondWord n e) =
        ((-jwSign e : ℝ) : ℂ) • (jwMajorana n e.castSucc * jwMajorana n e.succ) := by
      have h := congrArg Neg.neg (jwBond_skew_eq_majorana_pair n e)
      simpa only [neg_smul, neg_neg, Complex.ofReal_neg] using h
    have hterm_eq : Complex.I • ((((J e : ℝ) : ℂ) • finitePauliMatrix (jwBondWord n e)) *
          jwMajorana n c -
        jwMajorana n c * (((J e : ℝ) : ℂ) • finitePauliMatrix (jwBondWord n e))) =
        ((-J e * jwSign e : ℝ) : ℂ) •
          ((jwMajorana n e.castSucc * jwMajorana n e.succ) * jwMajorana n c -
            jwMajorana n c * (jwMajorana n e.castSucc * jwMajorana n e.succ)) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_comm Complex.I, smul_sub,
        ← Matrix.smul_mul, ← Matrix.mul_smul, hPe, Matrix.smul_mul, Matrix.mul_smul,
        ← smul_sub, smul_smul]
      refine congrArg (· • _) ?_
      push_cast; ring
    rw [hterm_eq]
    by_cases h1 : c = e.castSucc
    · subst h1
      have hcomm1 : (jwMajorana n e.castSucc * jwMajorana n e.succ) * jwMajorana n e.castSucc -
          jwMajorana n e.castSucc * (jwMajorana n e.castSucc * jwMajorana n e.succ) =
          ((-2 : ℝ) : ℂ) • jwMajorana n e.succ := by
        have ha := jwMajorana_anticommute n e.castSucc_lt_succ.ne
        have hL : (jwMajorana n e.castSucc * jwMajorana n e.succ) * jwMajorana n e.castSucc =
            -jwMajorana n e.succ := by
          rw [ha, neg_mul, mul_assoc, jwMajorana_sq, mul_one]
        have hR : jwMajorana n e.castSucc * (jwMajorana n e.castSucc * jwMajorana n e.succ) =
            jwMajorana n e.succ := by
          rw [← mul_assoc, jwMajorana_sq, one_mul]
        rw [hL, hR]
        calc -jwMajorana n e.succ - jwMajorana n e.succ
            = (-1 : ℂ) • jwMajorana n e.succ + (-1 : ℂ) • jwMajorana n e.succ := by simp [sub_eq_add_neg]
          _ = ((-2 : ℝ) : ℂ) • jwMajorana n e.succ := by rw [← add_smul]; norm_num
      rw [hcomm1, smul_smul, ← Complex.ofReal_mul, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · by_cases h2 : c = e.succ
      · subst h2
        have hcomm2 : (jwMajorana n e.castSucc * jwMajorana n e.succ) * jwMajorana n e.succ -
            jwMajorana n e.succ * (jwMajorana n e.castSucc * jwMajorana n e.succ) =
            ((2 : ℝ) : ℂ) • jwMajorana n e.castSucc := by
          have ha := jwMajorana_anticommute n e.castSucc_lt_succ.ne'
          have hL : (jwMajorana n e.castSucc * jwMajorana n e.succ) * jwMajorana n e.succ =
              jwMajorana n e.castSucc := by
            rw [mul_assoc, jwMajorana_sq, mul_one]
          have hR : jwMajorana n e.succ * (jwMajorana n e.castSucc * jwMajorana n e.succ) =
              -jwMajorana n e.castSucc := by
            rw [← mul_assoc, ha, neg_mul, mul_assoc, jwMajorana_sq, mul_one]
          rw [hL, hR, sub_neg_eq_add, ← two_smul ℂ]
          norm_num
        rw [hcomm2, smul_smul, ← Complex.ofReal_mul, Complex.coe_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · have ha1 := jwMajorana_anticommute n (Ne.symm h1)
        have ha2 := jwMajorana_anticommute n (Ne.symm h2)
        have hcomm0 : (jwMajorana n e.castSucc * jwMajorana n e.succ) * jwMajorana n c -
            jwMajorana n c * (jwMajorana n e.castSucc * jwMajorana n e.succ) = 0 := by
          rw [mul_assoc, ha2, mul_neg, ← mul_assoc, ha1, neg_mul, neg_neg, mul_assoc, sub_self]
        rw [hcomm0, smul_zero]; exact Submodule.zero_mem _
  have hiter_mem : ∀ k : ℕ, ∀ M ∈ realMajoranaSubspace n,
      (Complex.I ^ k) • iteratedCommutator H k M ∈ realMajoranaSubspace n := by
    intro k
    induction k with
    | zero => intro M hM; simpa only [pow_zero, one_smul, iteratedCommutator] using hM
    | succ k ih =>
        intro M hM
        have hsmul_iter : ∀ (m : ℕ) (z : ℂ) (X : Register (n + 2)),
            z • iteratedCommutator H m X = iteratedCommutator H m (z • X) := by
          intro m z
          induction m with
          | zero => intro X; rfl
          | succ m ihm =>
              intro X
              dsimp only [iteratedCommutator]
              rw [ihm, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
        have hstep : (Complex.I ^ (k + 1)) • iteratedCommutator H (k + 1) M =
            (Complex.I ^ k) • iteratedCommutator H k (Complex.I • (H * M - M * H)) := by
          dsimp only [iteratedCommutator]
          rw [pow_succ, mul_smul, hsmul_iter k Complex.I]
        rw [hstep]
        exact ih _ (had_mem M hM)
  have hclosed_real : IsClosed (realMajoranaSubspace n : Set (Register (n + 2))) := by
    haveI : FiniteDimensional ℝ (realMajoranaSubspace n) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    exact (realMajoranaSubspace n).closed_of_finiteDimensional
  have hUt_pres (s : ℝ) (c : Fin (n + 2)) :
      unitaryEvolution H s * jwMajorana n c * star (unitaryEvolution H s) ∈
        realMajoranaSubspace n := by
    have horb_eq : unitaryEvolution H s * jwMajorana n c * star (unitaryEvolution H s) =
        heisenbergOrbit H (jwMajorana n c) (-s) := by
      unfold heisenbergOrbit unitaryEvolution
      have hst (u_s : ℝ) : star (NormedSpace.exp (u_s • ((-Complex.I) • H))) =
          NormedSpace.exp ((-u_s) • ((-Complex.I) • H)) := by
        rw [NormedSpace.star_exp, star_smul, star_smul, hH_sa.star_eq]
        simp [neg_smul, smul_neg]
      rw [hst s, hst (-s), neg_neg]
    rw [horb_eq]
    have htay_mem (K : ℕ) :
        heisenbergCommutatorTaylor H (jwMajorana n c) K (-s) ∈ realMajoranaSubspace n := by
      unfold heisenbergCommutatorTaylor
      refine Submodule.sum_mem _ fun k _ => ?_
      have h1 : ((((-s) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * Complex.I ^ k) •
          iteratedCommutator H k (jwMajorana n c) =
          ((-s) ^ k / (k.factorial : ℝ)) •
            ((Complex.I ^ k) • iteratedCommutator H k (jwMajorana n c)) := by
        rw [← Complex.coe_smul, smul_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (hiter_mem k _ (Submodule.subset_span ⟨c, rfl⟩))
    let R := 2 * ‖H‖ * |-s|
    have hsum_R : Summable (fun k : ℕ => R ^ k / (k.factorial : ℝ)) := by
      have hs := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) R).summable
      rwa [NormedSpace.expSeries_apply_eq_div' (𝕂 := ℝ) R] at hs
    have htend0 : Tendsto
        (fun K : ℕ => R ^ (K + 1) / ((K + 1).factorial : ℝ) * ‖jwMajorana n c‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_mul] using
        (hsum_R.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)).mul_const ‖jwMajorana n c‖
    have htend_tay : Tendsto
        (fun K : ℕ => heisenbergCommutatorTaylor H (jwMajorana n c) K (-s)) atTop
        (𝓝 (heisenbergOrbit H (jwMajorana n c) (-s))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun K => ?_) htend0
      rw [norm_sub_rev]
      exact norm_heisenbergOrbit_sub_commutatorTaylor_le hH_sa (jwMajorana n c) K (-s)
    exact hclosed_real.mem_of_tendsto htend_tay (Eventually.of_forall htay_mem)
  let U_t := unitaryEvolution H t
  let O_t := majMat n U_t
  have hUt_unit : ∀ s : ℝ, unitaryEvolution H s ∈ unitary (Register (n + 2)) :=
    fun s => unitaryEvolution_mem_unitary hH_sa s
  have hUt_inv (s : ℝ) : star (unitaryEvolution H s) = unitaryEvolution H (-s) := by
    unfold unitaryEvolution
    rw [NormedSpace.star_exp, star_smul, star_smul, hH_sa.star_eq]
    simp [neg_smul, smul_neg]
  have hOt_orthL : O_tᵀ * O_t = 1 := by
    dsimp [O_t]
    rw [← majMat_star_eq_transpose, ← majMat_mul (hUt_pres t),
      (Unitary.mem_iff.mp (hUt_unit t)).1, majMat_one]
  have hOt_orthR : O_t * O_tᵀ = 1 := by
    dsimp [O_t]
    rw [← majMat_star_eq_transpose]
    have hpres_st : ∀ c, star U_t * jwMajorana n c * star (star U_t) ∈ realMajoranaSubspace n := by
      intro c; dsimp [U_t]; rw [hUt_inv t]; exact hUt_pres (-t) c
    rw [← majMat_mul hpres_st, (Unitary.mem_iff.mp (hUt_unit t)).2, majMat_one]
  have hOt_det : O_t.det = 1 := by
    have hhalf : U_t = unitaryEvolution H (t / 2) * unitaryEvolution H (t / 2) := by
      dsimp [U_t]; unfold unitaryEvolution
      rw [← NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _),
        ← add_smul, add_halves]
    have hOmul : O_t = majMat n (unitaryEvolution H (t / 2)) *
        majMat n (unitaryEvolution H (t / 2)) := by
      dsimp [O_t]; rw [hhalf, majMat_mul (hUt_pres (t / 2))]
    have hdet_nn : 0 ≤ O_t.det := by
      rw [hOmul, Matrix.det_mul, ← sq]; exact sq_nonneg _
    have hdet_sq : O_t.det ^ 2 = 1 := by
      have hd := congrArg Matrix.det hOt_orthL
      rwa [Matrix.det_mul, Matrix.det_transpose, ← sq, Matrix.det_one] at hd
    nlinarith only [hdet_nn, hdet_sq, sq_nonneg (O_t.det - 1)]
  obtain ⟨L_giv, hlen_giv, hp_giv, hOt_prod⟩ :=
    exists_adjGivens_prod_eq_of_specialOrthogonal (n + 2) O_t hOt_orthL hOt_orthR hOt_det
  have hcompile : ∀ (L : List (ℕ × ℝ)), (∀ p ∈ L, p.1 + 1 < n + 2) →
      ∃ U_c : Register (n + 2),
        U_c ∈ unitary (Register (n + 2)) ∧
        star U_c ∈ evenCliffordAdjoin (jwMajorana n) ∧
        (∀ c : Fin (n + 2), U_c * jwMajorana n c * star U_c ∈ realMajoranaSubspace n) ∧
        majMat n U_c = (L.map fun p => adjGivens (n + 2) p.1 p.2).prod ∧
        Realizes L.length U_c := by
    intro L
    induction L with
    | nil =>
        intro _
        refine ⟨1, OneMemClass.one_mem _, by rw [star_one]; exact OneMemClass.one_mem _,
          fun c => by simp only [one_mul, star_one, mul_one]; exact Submodule.subset_span ⟨c, rfl⟩,
          by simp [majMat_one], DiagonalSynthesis.Realizes.one (n + 2)⟩
    | cons p tail ih =>
        intro hp
        have hp0 : p.1 < n + 1 := by have := hp p (List.mem_cons.mpr (Or.inl rfl)); omega
        let e : Fin (n + 1) := ⟨p.1, hp0⟩
        obtain ⟨hG_u, _, hstG_adj, hG_pres, hG_maj, hG_real⟩ :=
          jwBondGate_preserves_and_majMat n e p.2
        obtain ⟨U_tail, hUtl_u, hstUtl_adj, hUtl_pres, hUtl_maj, hUtl_real⟩ :=
          ih (fun q hq => hp q (List.mem_cons.mpr (Or.inr hq)))
        let G := unitaryEvolution (finitePauliMatrix (jwBondWord n e)) (jwSign e * (p.2 / 2))
        refine ⟨G * U_tail, mul_mem hG_u hUtl_u, ?_, ?_, ?_, ?_⟩
        · rw [star_mul]; exact Subalgebra.mul_mem _ hstUtl_adj hstG_adj
        · intro c
          have hexp := eq_sum_majCoeff_of_mem_realMajoranaSubspace (hUtl_pres c)
          have h1 : (G * U_tail) * jwMajorana n c * star (G * U_tail) =
              ∑ b : Fin (n + 2), (majCoeff n (U_tail * jwMajorana n c * star U_tail) b) •
                (G * jwMajorana n b * star G) := by
            rw [star_mul]
            calc (G * U_tail) * jwMajorana n c * (star U_tail * star G)
                = G * (U_tail * jwMajorana n c * star U_tail) * star G := by simp only [mul_assoc]
              _ = G * (∑ b, ((majCoeff n (U_tail * jwMajorana n c * star U_tail) b : ℝ) : ℂ) •
                    jwMajorana n b) * star G := by rw [← hexp]
              _ = _ := by
                    rw [Matrix.mul_sum, Matrix.sum_mul]
                    refine Finset.sum_congr rfl fun b _ => ?_
                    rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
          rw [h1]
          exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hG_pres b)
        · rw [majMat_mul hUtl_pres, hG_maj, hUtl_maj, List.map_cons, List.prod_cons]
        · simpa only [List.length_cons, Nat.add_comm] using
            DiagonalSynthesis.Realizes.mul hG_real hUtl_real
  obtain ⟨U_c, hUc_u, hstUc_adj, hUc_pres, hUc_maj, hUc_real⟩ := hcompile L_giv hp_giv
  let W := U_t * star U_c
  have hW_unit : W ∈ unitary (Register (n + 2)) := mul_mem (hUt_unit t) (Unitary.star_mem hUc_u)
  have hW_even : W ∈ evenCliffordSubspace (jwMajorana n) :=
    evenCliffordAdjoin_le_subspace (jwMajorana_sq n) (fun _ _ h => jwMajorana_anticommute n h)
      (Subalgebra.mul_mem _ (hUt_adjoin t) hstUc_adj)
  have hstUc_pres : ∀ c : Fin (n + 2),
      star U_c * jwMajorana n c * star (star U_c) ∈ realMajoranaSubspace n := by
    intro c
    have hOt_eq_Uc : majMat n U_c = O_t := hUc_maj.trans hOt_prod.symm
    have hlin_comb : jwMajorana n c =
        ∑ b : Fin (n + 2), (O_t c b) • (U_c * jwMajorana n b * star U_c) := by
      have hterm (b : Fin (n + 2)) := eq_sum_majCoeff_of_mem_realMajoranaSubspace (hUc_pres b)
      trans (∑ b : Fin (n + 2), (O_t c b) •
        ∑ a : Fin (n + 2), (majMat n U_c a b) • jwMajorana n a)
      · symm
        calc ∑ b : Fin (n + 2), (O_t c b) • ∑ a : Fin (n + 2), (majMat n U_c a b) • jwMajorana n a
            = ∑ a : Fin (n + 2), (∑ b : Fin (n + 2), O_t c b * majMat n U_c a b) • jwMajorana n a := by
                simp_rw [Finset.smul_sum, smul_smul]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun a _ => (Finset.sum_smul ..).symm
          _ = ∑ a : Fin (n + 2), ((O_t * O_tᵀ) c a) • jwMajorana n a := by
                rw [hOt_eq_Uc]; rfl
          _ = jwMajorana n c := by
                rw [hOt_orthR]; simp [Matrix.one_apply]
      · refine Finset.sum_congr rfl fun b _ => ?_
        congr 1
        rw [hterm b]
        exact Finset.sum_congr rfl fun a _ => by rw [Complex.coe_smul]; rfl
    have hconj_st : star U_c * jwMajorana n c * star (star U_c) =
        ∑ b : Fin (n + 2), (O_t c b) • jwMajorana n b := by
      conv_lhs => arg 1; arg 2; rw [hlin_comb]
      rw [star_star, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc star U_c * (U_c * jwMajorana n b * star U_c) * U_c
          = (star U_c * U_c) * jwMajorana n b * (star U_c * U_c) := by simp only [mul_assoc]
        _ = jwMajorana n b := by
              rw [(Unitary.mem_iff.mp hUc_u).1, one_mul, mul_one]
    rw [hconj_st]
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hW_pres (c : Fin (n + 2)) : W * jwMajorana n c * star W ∈ realMajoranaSubspace n := by
    dsimp [W]
    have hexp := eq_sum_majCoeff_of_mem_realMajoranaSubspace (hstUc_pres c)
    have h1 : (U_t * star U_c) * jwMajorana n c * star (U_t * star U_c) =
        ∑ b : Fin (n + 2), (majCoeff n (star U_c * jwMajorana n c * star (star U_c)) b) •
          (U_t * jwMajorana n b * star U_t) := by
      rw [star_mul]
      calc (U_t * star U_c) * jwMajorana n c * (star (star U_c) * star U_t)
          = U_t * (star U_c * jwMajorana n c * star (star U_c)) * star U_t := by simp only [mul_assoc]
        _ = U_t * (∑ b, ((majCoeff n (star U_c * jwMajorana n c * star (star U_c)) b : ℝ) : ℂ) •
              jwMajorana n b) * star U_t := by rw [← hexp]
        _ = _ := by
              rw [Matrix.mul_sum, Matrix.sum_mul]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
    rw [h1]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hUt_pres t b)
  have hW_maj : majMat n W = 1 := by
    dsimp [W]
    rw [majMat_mul hstUc_pres, majMat_star_eq_transpose, hUc_maj, ← hOt_prod]
    exact hOt_orthR
  have hW_comm (c : Fin (n + 2)) : W * jwMajorana n c = jwMajorana n c * W := by
    have hexp := eq_sum_majCoeff_of_mem_realMajoranaSubspace (hW_pres c)
    change W * jwMajorana n c * star W = ∑ a, ((majMat n W a c : ℝ) : ℂ) • jwMajorana n a at hexp
    rw [hW_maj] at hexp
    have hconj1 : W * jwMajorana n c * star W = jwMajorana n c := by
      rw [hexp, Finset.sum_eq_single c]
      · simp
      · intro a _ hac; simp [Matrix.one_apply_ne hac]
      · simp
    calc W * jwMajorana n c
        = (W * jwMajorana n c * star W) * W := by
            rw [mul_assoc _ (star W) W, (Unitary.mem_iff.mp hW_unit).1, mul_one]
      _ = jwMajorana n c * W := by rw [hconj1]
  haveI : Nontrivial (Register (n + 2)) := by
    refine ⟨⟨0, 1, fun h => (zero_ne_one : (0 : ℂ) ≠ 1) ?_⟩⟩
    simpa using congrFun (congrFun h (fun _ => false)) (fun _ => false)
  obtain ⟨z, hz, hW_eq⟩ := eq_scalar_one_of_mem_evenClifford_commutant (jwMajorana_sq n)
    (fun _ _ h => jwMajorana_anticommute n h) hW_even hW_unit hW_comm
  have hUt_eq_zUc : U_t = z • U_c := by
    calc U_t = U_t * (star U_c * U_c) := by rw [(Unitary.mem_iff.mp hUc_u).1, mul_one]
      _ = W * U_c := (mul_assoc _ _ _).symm
      _ = z • U_c := by rw [hW_eq, Matrix.smul_mul, one_mul]
  obtain ⟨z', hz', C, hC, hUc_eq⟩ := hUc_real
  refine ⟨z * z', by rw [norm_mul, hz, hz', mul_one], C, hC.trans hlen_giv, ?_⟩
  change U_t = (z * z') • C.eval.val
  rw [hUt_eq_zUc, hUc_eq, smul_smul]

/-- Alternating `ZZ / XX` Jordan-Wigner free-fermion survival tube inside
`nonCommutingBondEvent (k + 1) η`: for every `η : ℝ` and all sufficiently large `k` (`N = k + 3`),
there is `c > 0` such that for every `T ≥ 2`, an event of `pathPauliDisorderLaw` probability
`≥ c * T ^ -(11 * k + 25)` simultaneously satisfies:
1. `x ∈ nonCommutingBondEvent (k + 1) η`,
2. maximally projective simple spectrum, full `2^N` Vandermonde rank on `[0, 1]`, and `√2`
   scalar-return excision, yet
3. `T < tenthPlateauOnset H s` for **every** budget `(k + 3) * (k + 2) / 2 ≤ s ≤ P`
   (`choose(N, 2) ≤ s ≤ P`). -/
theorem gaussian_alternatingJW_tube_tail (η : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let P := nearHilbertContinuousCircuitBudget N
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T →
        c ≤ T ^ (11 * k + 25) * pathPauliDisorderLaw.real {ω : PathPauliDisorder |
          let u := pathPauliDisorderShell ω (k + 1)
          let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
          let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
          x ∈ nonCommutingBondEvent (k + 1) η ∧
          MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
          (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
            Module.finrank ℂ (Submodule.span ℂ
              (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
          (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
            Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
          (∀ s : ℕ, (k + 3) * (k + 2) / 2 ≤ s → s ≤ P → T < tenthPlateauOnset H s)} := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let γ := gaussianReal 0 1
  have hent := (tendsto_add_atTop_nat 3).eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hent, eventually_ge_atTop 20] with k hentropy hklarge
  intro N P
  let s_jw : ℕ := (k + 3) * (k + 2) / 2
  have hP_ge : 2 * s_jw ≤ P := by
    dsimp only [P, N, s_jw, nearHilbertContinuousCircuitBudget]
    have h2div : 2 * ((k + 3) * (k + 2) / 2) ≤ (k + 3) * (k + 2) := Nat.mul_div_le _ 2
    have hind : ∀ m : ℕ, 20 ≤ m → 64 * (m + 4) * ((m + 3) * (m + 2)) ≤ 2 ^ (m + 3) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
          have hstep_m : 64 * (m + 5) * ((m + 4) * (m + 3)) ≤
              2 * (64 * (m + 4) * ((m + 3) * (m + 2))) := by
            have hlin : m + 5 ≤ 2 * (m + 2) := by omega
            calc 64 * (m + 5) * ((m + 4) * (m + 3))
                = (64 * (m + 4) * (m + 3)) * (m + 5) := by ring
              _ ≤ (64 * (m + 4) * (m + 3)) * (2 * (m + 2)) := Nat.mul_le_mul_left _ hlin
              _ = 2 * (64 * (m + 4) * ((m + 3) * (m + 2))) := by ring
          calc 64 * (m + 5) * ((m + 4) * (m + 3))
              ≤ 2 * (64 * (m + 4) * ((m + 3) * (m + 2))) := hstep_m
            _ ≤ 2 * 2 ^ (m + 3) := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (m + 4) := by rw [← pow_succ']
    refine (Nat.mul_le_mul_left (64 * (k + 4)) h2div).trans (hind k hklarge) |> fun h => ?_
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact h)
  let M_η : ℝ := max |η| 3
  have hM_ge3 : 3 ≤ M_η := le_max_right |η| 3
  have hM_ge_eta : η ≤ M_η := (le_abs_self η).trans (le_max_left |η| 3)
  let S_jw : Finset (PathLabel (k + 1)) :=
    Finset.univ.filter fun l : PathLabel (k + 1) => isJWChainLabel l
  let S_weak : Finset (PathLabel (k + 1)) := Finset.univ \ S_jw
  have hcard_jw : S_jw.card = k + 2 := by
    let emb : Fin (k + 2) ↪ PathLabel (k + 1) :=
      ⟨fun e => .inr (e, if Even e.val then (2, 2) else (0, 0)),
       fun _ _ h => (Prod.mk.inj (Sum.inr.inj h)).1⟩
    have heq : S_jw = Finset.univ.map emb := by
      ext l
      simp only [S_jw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, emb,
        Function.Embedding.coeFn_mk]
      rcases l with ⟨v, a⟩ | ⟨e, pq⟩
      · simp [isJWChainLabel]
      · simp only [isJWChainLabel]
        exact ⟨fun h => ⟨e, h ▸ rfl⟩, fun ⟨e', h⟩ => by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inr.inj h); rfl⟩
    rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcard_tot : Fintype.card (PathLabel (k + 1)) = 12 * k + 27 := by
    simp only [PathLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega
  have hcard_weak : S_weak.card = 11 * k + 25 := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S_jw)
    rw [Finset.card_univ, hcard_tot, hcard_jw] at h1
    dsimp only [S_weak]
    omega
  have hdisj : Disjoint S_jw S_weak := disjoint_sdiff_self_right
  have hunion_univ : S_jw ∪ S_weak = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hp_jw : 0 < γ.real (Icc M_η (M_η + 1)) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by linarith)).ne' (measure_ne_top _ _)
  let W_num : ℝ := 100 * ((11 * k + 25 : ℕ) : ℝ)
  have hW_pos : 0 < W_num := by dsimp only [W_num]; positivity
  let c : ℝ := (γ.real (Icc M_η (M_η + 1))) ^ (k + 2) *
    (2 * gaussianDensityFloor / W_num) ^ (11 * k + 25)
  have hc_pos : 0 < c :=
    mul_pos (pow_pos hp_jw _)
      (pow_pos (div_pos (mul_pos two_pos gaussianDensityFloor_pos) hW_pos) _)
  refine ⟨c, hc_pos, fun T hT2 => ?_⟩
  have hT_pos : 0 < T := by linarith only [hT2]
  let δ : ℝ := 1 / (W_num * T)
  have hδ_pos : 0 < δ := div_pos zero_lt_one (mul_pos hW_pos hT_pos)
  have hδ_le1 : δ ≤ 1 := by
    have hW1 : 1 ≤ W_num := by
      dsimp only [W_num]
      have : (1 : ℝ) ≤ ((11 * k + 25 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 11 * k + 25 by omega)
      linarith only [this]
    exact div_le_one_of_le₀ (by nlinarith only [hW1, hT2]) (mul_pos hW_pos hT_pos).le
  let F_coord : PathLabel (k + 1) → Set ℝ := fun l =>
    if l ∈ S_jw then Icc M_η (M_η + 1) else Icc (-δ) δ
  let JWBox : Set (PathLabel (k + 1) → ℝ) := Set.univ.pi F_coord
  have hJWBox_meas : MeasurableSet JWBox :=
    MeasurableSet.pi (Set.to_countable _) fun l _ => by
      dsimp only [F_coord]; split_ifs <;> exact measurableSet_Icc
  have hJWBox_mass : (γ.real (Icc M_η (M_η + 1))) ^ (k + 2) *
      (2 * gaussianDensityFloor * δ) ^ (11 * k + 25) ≤
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real JWBox := by
    have hprod_eq : (Measure.pi fun _ : PathLabel (k + 1) => γ).real JWBox =
        (∏ l ∈ S_jw, γ.real (F_coord l)) * (∏ l ∈ S_weak, γ.real (F_coord l)) := by
      rw [Measure.real_def, Measure.pi_pi, ENNReal.toReal_prod, ← hunion_univ,
        Finset.prod_union hdisj]; rfl
    have hpj : (∏ l ∈ S_jw, γ.real (F_coord l)) = (γ.real (Icc M_η (M_η + 1))) ^ (k + 2) := by
      have h1 : (∏ l ∈ S_jw, γ.real (F_coord l)) = ∏ _l ∈ S_jw, γ.real (Icc M_η (M_η + 1)) :=
        Finset.prod_congr rfl fun l hl => by simp [F_coord, hl]
      rw [h1, Finset.prod_const, hcard_jw]
    have hpw : (∏ l ∈ S_weak, γ.real (F_coord l)) = (γ.real (Icc (-δ) δ)) ^ (11 * k + 25) := by
      have h1 (l : PathLabel (k + 1)) (hl : l ∈ S_weak) : l ∉ S_jw := (Finset.mem_sdiff.mp hl).2
      have h2 : (∏ l ∈ S_weak, γ.real (F_coord l)) = ∏ _l ∈ S_weak, γ.real (Icc (-δ) δ) :=
        Finset.prod_congr rfl fun l hl => by simp [F_coord, h1 l hl]
      rw [h2, Finset.prod_const, hcard_weak]
    have hlow_enn := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ)) (gaussianReal_Icc_lower hδ_le1)
    rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (by linarith only [hδ_pos])),
      ← Measure.real_def] at hlow_enn
    have h1d : 2 * gaussianDensityFloor * δ ≤ γ.real (Icc (-δ) δ) := by linarith only [hlow_enn]
    rw [hprod_eq, hpj, hpw]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (mul_nonneg two_pos.le gaussianDensityFloor_pos.le) hδ_pos.le) h1d _)
      (pow_nonneg measureReal_nonneg _)
  let u_map : PathPauliDisorder → PathLabel (k + 1) → ℝ :=
    fun ω l => pathPauliDisorderShell ω (k + 1) l
  have hmp_lbl := measurePreserving_pathDisorder_labels (k + 1)
  have hpre_mass : pathPauliDisorderLaw.real (u_map ⁻¹' JWBox) =
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real JWBox :=
    congrArg ENNReal.toReal (hmp_lbl.measure_preimage hJWBox_meas.nullMeasurableSet)
  let TargetEvent : Set PathPauliDisorder := {ω : PathPauliDisorder |
    let u := pathPauliDisorderShell ω (k + 1)
    let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    x ∈ nonCommutingBondEvent (k + 1) η ∧
    MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
    (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
      Module.finrank ℂ (Submodule.span ℂ
        (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
    (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
    (∀ s : ℕ, s_jw ≤ s → s ≤ P → T < tenthPlateauOnset H s)}
  have hae_sub : u_map ⁻¹' JWBox ≤ᵐ[pathPauliDisorderLaw] TargetEvent := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hmax_all hω_in
    let u := pathPauliDisorderShell ω (k + 1)
    have hu_box : ∀ l : PathLabel (k + 1), u l ∈ F_coord l := fun l => hω_in l (mem_univ l)
    let pq_jw (e : Fin (k + 2)) : Fin 3 × Fin 3 := if Even e.val then (2, 2) else (0, 0)
    have hpq_mem (e : Fin (k + 2)) : Sum.inr (e, pq_jw e) ∈ S_jw :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hu_jw_ge (e : Fin (k + 2)) : M_η ≤ u (.inr (e, pq_jw e)) := by
      have h := hu_box (.inr (e, pq_jw e))
      rw [show F_coord (.inr (e, pq_jw e)) = Icc M_η (M_η + 1) from if_pos (hpq_mem e)] at h
      exact h.1
    have hnc_bond : (fun i => u (pathCoeffEquiv (k + 1) i)) ∈ nonCommutingBondEvent (k + 1) η := by
      refine ⟨fun e => ⟨pq_jw e, ?_⟩, fun e f hef => ⟨pq_jw e, pq_jw f, ?_, ?_, ?_⟩⟩
      · simpa only [Equiv.apply_symm_apply] using
          (hM_ge_eta.trans (hu_jw_ge e)).trans (le_abs_self _)
      · have hval : e.val + 1 = f.val := by
          have hv := congrArg Fin.val hef
          simpa only [Fin.val_succ, Fin.val_castSucc] using hv
        have hev_iff : Even f.val ↔ ¬ Even e.val := by rw [← hval, Nat.even_add_one]
        dsimp only [pq_jw]
        by_cases hev : Even e.val
        · have hnf : ¬ Even f.val := fun hf => (hev_iff.mp hf) hev
          simp only [hev, hnf, ↓reduceIte]; decide
        · have hfv : Even f.val := hev_iff.mpr hev
          simp only [hev, hfv, ↓reduceIte]; decide
      · simpa only [Equiv.apply_symm_apply] using
          (hM_ge_eta.trans (hu_jw_ge e)).trans (le_abs_self _)
      · simpa only [Equiv.apply_symm_apply] using
          (hM_ge_eta.trans (hu_jw_ge f)).trans (le_abs_self _)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    have hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := hmax_all k
    have hvand := vandermonde_full_rank_unit_interval H hmax.injective
    have hb0_ge3 : 3 ≤ |u (.inr (0, (2, 2)))| := by
      have h := hu_jw_ge 0
      simp only [pq_jw, Fin.val_zero, Even.zero, ↓reduceIte] at h
      exact (hM_ge3.trans h).trans (le_abs_self _)
    have hexc := exists_antipodal_return_excision_of_shell_coeff u (.inr (0, (2, 2))) hb0_ge3 hT2
    let u_jw : PathShell (k + 1) :=
      WithLp.toLp 2 fun l => if isJWChainLabel l then u l else 0
    have hujw_off : ∀ l : PathLabel (k + 1), ¬ isJWChainLabel l → u_jw l = 0 :=
      fun l hl => if_neg hl
    have hdiff_jw : ‖pathHamiltonian u - pathHamiltonian u_jw‖ ≤
        ((11 * k + 25 : ℕ) : ℝ) * δ := by
      have hsub_sum : pathHamiltonian u - pathHamiltonian u_jw =
          ∑ l ∈ S_weak, ((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l) := by
        rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, ← Finset.sum_sub_distrib,
          ← hunion_univ, Finset.sum_union hdisj]
        have hjw0 : (∑ l ∈ S_jw, (((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l) -
            ((u_jw l : ℝ) : ℂ) • finitePauliMatrix (pathWord l))) = 0 := by
          refine Finset.sum_eq_zero fun l hl => ?_
          have h1 : u_jw l = u l := if_pos (Finset.mem_filter.mp hl).2
          rw [h1, sub_self]
        rw [hjw0, zero_add]
        refine Finset.sum_congr rfl fun l hl => ?_
        have hnot : ¬ isJWChainLabel l := fun h => (Finset.mem_sdiff.mp hl).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩)
        have h0 : u_jw l = 0 := if_neg hnot
        rw [h0, Complex.ofReal_zero, zero_smul, sub_zero]
      rw [hsub_sum]
      refine (norm_sum_le _ _).trans ?_
      have hterm (l : PathLabel (k + 1)) (hl : l ∈ S_weak) :
          ‖((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)‖ ≤ δ := by
        rw [norm_smul, norm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]
        have hnot : l ∉ S_jw := (Finset.mem_sdiff.mp hl).2
        exact abs_le.mpr (by simpa only [F_coord, if_neg hnot, Set.mem_Icc] using hu_box l)
      calc ∑ l ∈ S_weak, ‖((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)‖
          ≤ ∑ _l ∈ S_weak, δ := Finset.sum_le_sum hterm
        _ = ((11 * k + 25 : ℕ) : ℝ) * δ := by
            rw [Finset.sum_const, hcard_weak, nsmul_eq_mul]
    have hearly_inc (t : ℝ) (ht : |t| ≤ T) :
        HasProjectiveCircuitApproximation N (1 / 100 : ℝ) s_jw (unitaryEvolution H.val t) := by
      obtain ⟨z, hz, C, hC, hU_jw⟩ := realizes_choose_two_of_alternatingJWChain u_jw hujw_off t
      refine ⟨z, hz, C, hC, ?_⟩
      rw [← hU_jw]
      calc ‖unitaryEvolution (pathHamiltonian u) t - unitaryEvolution (pathHamiltonian u_jw) t‖
          ≤ |t| * ‖pathHamiltonian u - pathHamiltonian u_jw‖ :=
            norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u)
              (isSelfAdjoint_pathHamiltonian u_jw) t
        _ ≤ T * (((11 * k + 25 : ℕ) : ℝ) * δ) :=
            mul_le_mul ht hdiff_jw (norm_nonneg _) hT_pos.le
        _ = 1 / 100 := by dsimp only [δ, W_num]; field_simp [hT_pos.ne', hW_pos.ne']
    let d := 2 ^ N - 1
    let e_fin : Config N ≃ Fin (d + 1) := (Fintype.equivFin _).trans
      (finCongr (by
        simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        have hd : 0 < 2 ^ N := Nat.two_pow_pos N
        dsimp [d]; omega))
    obtain ⟨σ, hσ_gt, hσ_eq, _, _, _⟩ := first_circuit_threshold_of_increment e_fin H
      (hmax.comp_equiv e_fin.symm) hentropy T hT_pos.le hP_ge hearly_inc
    have honset_gt (s : ℕ) (hs_lo : s_jw ≤ s) (hs_hi : s ≤ P) :
        T < tenthPlateauOnset H s := by
      have hearly (t : ℝ) (ht : t ∈ Icc 0 T) : orbitCircuitDistance H s t < 1 / 10 := by
        have habs : |t| ≤ T := by rw [abs_of_nonneg ht.1]; exact ht.2
        obtain ⟨z, hz, C, hC, herr⟩ := hearly_inc t habs
        have hd := (hasProjectiveCircuitApproximation_iff_infDist _ s (1 / 100 : ℝ)).mp
          ⟨z, hz, C, hC.trans hs_lo, herr⟩
        change orbitCircuitDistance H s t ≤ 1 / 100 at hd
        linarith only [hd]
      have hB_gt : 1 / 10 < orbitCircuitDistance H s σ := by
        have hmono : orbitCircuitDistance H P σ ≤ orbitCircuitDistance H s σ := by
          apply (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
          obtain ⟨z, hz, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr
            (le_rfl : orbitCircuitDistance H s σ ≤ _)
          exact ⟨z, hz, C, hC.trans hs_hi, herr⟩
        rw [hσ_eq] at hmono
        linarith only [hmono]
      exact (tenthPlateauOnset_spec H hT_pos (hT_pos.trans hσ_gt).le hearly hB_gt).1
    exact ⟨hnc_bond, hmax, hvand, hexc, honset_gt⟩
  have hmeas_le : (Measure.pi fun _ : PathLabel (k + 1) => γ).real JWBox ≤
      pathPauliDisorderLaw.real TargetEvent := by
    rw [← hpre_mass]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae_sub)
  have hc_eq : c = T ^ (11 * k + 25) *
      ((γ.real (Icc M_η (M_η + 1))) ^ (k + 2) *
        (2 * gaussianDensityFloor * δ) ^ (11 * k + 25)) := by
    dsimp only [c, δ]
    have hpow_T : T ^ (11 * k + 25) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (11 * k + 25) =
        (2 * gaussianDensityFloor / W_num) ^ (11 * k + 25) := by
      rw [← mul_pow]; congr 1; field_simp [hT_pos.ne', hW_pos.ne']
    calc c = (γ.real (Icc M_η (M_η + 1))) ^ (k + 2) *
            (T ^ (11 * k + 25) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (11 * k + 25)) := by
              dsimp only [c]; rw [hpow_T]
      _ = _ := by ring
  rw [hc_eq]
  exact mul_le_mul_of_nonneg_left (hJWBox_mass.trans hmeas_le) (pow_nonneg hT_pos.le _)

#print axioms bondRankTwoEvent_compl_prob_le
#print axioms locallyRotatedIsing_operator_dist_ge_of_bondMinor
#print axioms exists_adjGivens_prod_eq_of_specialOrthogonal
#print axioms eq_scalar_one_of_mem_evenClifford_commutant
#print axioms realizes_choose_two_of_alternatingJWChain
#print axioms gaussian_alternatingJW_tube_tail

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
