import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalTerminalWallEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergySquares

/-!
# Strict energy positivity for distinct positive causal delays

Endpoint mass detects the first coefficient of an ordered causal sum before
the next translate starts. Repetition proves independence modulo almost-
everywhere equality. The sharp wall floor then makes the energy matrix
positive definite for distinct positive delays.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

/-- Strictly increasing absolute delays have strictly positive consecutive increments. -/
theorem exists_strict_criticalCausalCumulativeDelays_from
    (l : List (ℝ≥0 × ℝ)) (p : ℝ≥0) (hp : ∀ q ∈ l, p < q.1)
    (hord : l.Pairwise (fun q r => q.1 < r.1)) :
    ∃ k : List (ℝ≥0 × ℝ),
      (criticalCausalCumulativeDelays k).map (fun q => (p + q.1, q.2)) = l ∧
        ∀ q ∈ k, 0 < (q.1 : ℝ) := by
  induction l generalizing p with
  | nil => exact ⟨[], rfl, by simp only [List.not_mem_nil, false_implies, implies_true]⟩
  | cons q l ih =>
    rcases q with ⟨s, c⟩
    rcases List.pairwise_cons.mp hord with ⟨hs, htail⟩
    obtain ⟨k, hk, hkpos⟩ := ih s hs htail
    have hps : p < s := hp (s, c) List.mem_cons_self
    let h : ℝ≥0 := ⟨(s : ℝ) - p, sub_nonneg.mpr hps.le⟩
    have hph : p + h = s := by
      apply Subtype.ext
      change (p : ℝ) + ((s : ℝ) - p) = s
      ring
    refine ⟨(h, c) :: k, ?_, ?_⟩
    · simp only [criticalCausalCumulativeDelays, List.map_cons, List.map_map,
        Function.comp_def, ← add_assoc, hph]
      rw [hk]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact sub_pos.mpr hps
      · exact hkpos q hq

private theorem coefficients_zero_shift_map_iff (l : List (ℝ≥0 × ℝ)) (h : ℝ≥0) :
    (∀ q ∈ l.map (fun p => (h + p.1, p.2)), q.2 = 0) ↔ ∀ q ∈ l, q.2 = 0 := by
  constructor
  · intro hz q hq
    exact hz (h + q.1, q.2) (List.mem_map.mpr ⟨q, hq, rfl⟩)
  · intro hz q hq
    rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
    exact hz r hr

theorem criticalCausalCumulativeDelays_coefficients_zero_iff (l : List (ℝ≥0 × ℝ)) :
    (∀ q ∈ criticalCausalCumulativeDelays l, q.2 = 0) ↔ ∀ q ∈ l, q.2 = 0 := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rcases q with ⟨h, c⟩
    rw [criticalCausalCumulativeDelays, List.forall_mem_cons, List.forall_mem_cons,
      coefficients_zero_shift_map_iff, ih]

/-- The first cumulative delay is a literal terminal support wall. -/
theorem criticalCausalPolynomial_terminal_wall {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (h : ℝ≥0) (c : ℝ)
    (l : List (ℝ≥0 × ℝ)) (u : ℝ) (hu : -(h : ℝ) ≤ u) :
    criticalCausalPolynomial F ((h, c) :: l) u = 0 := by
  have hn : 0 ≤ u + (h : ℝ) := by linarith only [hu]
  simp only [criticalCausalPolynomial, (hF.causalPolynomial l).support _ hn,
    hF.support _ hn, mul_zero, add_zero]

/-- A delayed profile cannot cancel a nonzero multiple of the endpoint ground state. -/
theorem criticalHalfLineGroundState_coeff_zero_of_gap_cancellation
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {G : ℝ → ℝ} {c d : ℝ} (hd : 0 < d)
    (hgap : ∀ u, -d ≤ u → G u = 0)
    (hz : (fun u => G u + c * F u) =ᵐ[volume] fun _ => 0) : c = 0 := by
  by_contra hc
  have hae : F =ᵐ[volume.restrict (Ioo (-d) 0)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioo] with u hu hum
    change G u + c * F u = 0 at hu
    rw [hgap u hum.1.le, zero_add] at hu
    exact (mul_eq_zero.mp hu).resolve_left hc
  have hs : (∫ u in Ioo (-d) 0, F u ^ 2) = 0 := by
    calc
      _ = ∫ _u in Ioo (-d) 0, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hae] with u hu
        rw [hu, zero_pow (by decide : 2 ≠ 0)]
      _ = 0 := by simp only [integral_zero]
  exact (ne_of_gt (criticalHalfLineGroundState_endpoint_mass_pos hW hthreshold hF hd)) hs

/-- Positive successive increments give independent causal translates, modulo null sets. -/
theorem criticalCausalPolynomial_coefficients_zero_of_ae_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) :
    (∀ p ∈ l, 0 < (p.1 : ℝ)) →
    (criticalCausalPolynomial F l =ᵐ[volume] fun _ => 0) → ∀ p ∈ l, p.2 = 0 := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons p l ih =>
    rcases p with ⟨h, c⟩
    intro hpos hz
    have hposl : ∀ p ∈ l, 0 < (p.1 : ℝ) :=
      fun p hp => hpos p (List.mem_cons_of_mem _ hp)
    have hpre : (fun u => criticalCausalPolynomial F l u + c * F u) =ᵐ[volume]
        fun _ => 0 := by
      have hat := hz.comp_tendsto
        (measurePreserving_add_right volume (-(h : ℝ))).quasiMeasurePreserving.tendsto_ae
      filter_upwards [hat] with u hu
      simpa only [Function.comp_apply, criticalCausalPolynomial,
        add_assoc, neg_add_cancel, add_zero] using hu
    obtain ⟨d, hd, hgap⟩ : ∃ d : ℝ, 0 < d ∧
        ∀ u, -d ≤ u → criticalCausalPolynomial F l u = 0 := by
      cases l with
      | nil => exact ⟨1, zero_lt_one, fun _ _ => rfl⟩
      | cons q l' =>
        exact ⟨q.1, hposl q (List.mem_cons_self),
          criticalCausalPolynomial_terminal_wall hdF q.1 q.2 l'⟩
    have hc := criticalHalfLineGroundState_coeff_zero_of_gap_cancellation
      hW hthreshold hF hd hgap hpre
    have htail : criticalCausalPolynomial F l =ᵐ[volume] fun _ => 0 := by
      simpa only [hc, zero_mul, add_zero] using hpre
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hc
    · exact ih hposl htail p hp

theorem criticalCausalPolynomial_eq_zero_of_coefficients (F : ℝ → ℝ)
    (l : List (ℝ≥0 × ℝ)) :
    (∀ p ∈ l, p.2 = 0) → criticalCausalPolynomial F l = fun _ => 0 := by
  induction l with
  | nil => intro _; rfl
  | cons p l ih =>
    rcases p with ⟨h, c⟩
    intro hc
    have hh : c = 0 := hc (h, c) List.mem_cons_self
    have ht := ih (fun p hp => hc p (List.mem_cons_of_mem _ hp))
    simp only [criticalCausalPolynomial, hh, ht, zero_mul, add_zero]

/-- The energy matrix of distinct strictly positive cumulative delays is positive definite. -/
theorem criticalHalfLineFullEnergy_causalPolynomial_eq_zero_iff
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) (hpos : ∀ p ∈ l, 0 < (p.1 : ℝ)) :
    criticalHalfLineFullEnergy W₀ (criticalCausalPolynomial F l) = 0 ↔
      ∀ p ∈ l, p.2 = 0 := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  constructor
  · intro he
    apply criticalCausalPolynomial_coefficients_zero_of_ae_zero hW hthreshold hF l hpos
    cases l with
    | nil => exact Eventually.of_forall fun _ => rfl
    | cons p l =>
      rcases p with ⟨h, c⟩
      by_contra hne
      have hp := criticalHalfLineFullEnergy_pos_of_terminal_wall hW hthreshold
        (hdF.causalPolynomial ((h, c) :: l)) (hpos (h, c) List.mem_cons_self)
        (criticalCausalPolynomial_terminal_wall hdF h c l) hne
      exact (ne_of_gt hp) he
  · intro hc
    rw [criticalCausalPolynomial_eq_zero_of_coefficients F l hc]
    have hz := criticalHalfLineFullEnergy_const_mul W₀ F 0
    simpa only [zero_mul, zero_pow (by decide : 2 ≠ 0)] using hz

/-- Adjoining delay zero adds exactly the critical-state null direction. -/
theorem criticalHalfLineFullEnergy_causalPolynomial_zero_head_eq_zero_iff
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) (hpos : ∀ p ∈ l, 0 < (p.1 : ℝ)) (c : ℝ) :
    criticalHalfLineFullEnergy W₀ (criticalCausalPolynomial F ((0, c) :: l)) = 0 ↔
      ∀ p ∈ l, p.2 = 0 := by
  have he := criticalHalfLineFullEnergy_causal_ground_shear hW hthreshold hF
    ((criticalHalfLineEnergyDomain_of_groundState hF).causalPolynomial l)
    (h := 0) le_rfl c
  simp only [add_zero, mul_zero, Real.exp_zero, sub_self, zero_mul] at he
  simp only [criticalCausalPolynomial, NNReal.coe_zero, add_zero]
  rw [he]
  exact criticalHalfLineFullEnergy_causalPolynomial_eq_zero_iff hW hthreshold hF l hpos

/-- Every strictly ordered positive absolute-delay family has a positive definite energy matrix. -/
theorem criticalHalfLineFullEnergy_strict_ordered_sum_eq_zero_iff
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) (hpos : ∀ q ∈ l, 0 < q.1)
    (hord : l.Pairwise (fun q r => q.1 < r.1)) :
    criticalHalfLineFullEnergy W₀
      (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) = 0 ↔
        ∀ q ∈ l, q.2 = 0 := by
  obtain ⟨k, hk, hkpos⟩ := exists_strict_criticalCausalCumulativeDelays_from l 0 hpos hord
  have hcum : criticalCausalCumulativeDelays k = l := by
    simp only [zero_add, Prod.mk.eta] at hk
    change (criticalCausalCumulativeDelays k).map id = l at hk
    simpa only [List.map_id] using hk
  have hfun : (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) =
      criticalCausalPolynomial F k := by
    funext u
    rw [criticalCausalPolynomial_eq_sum, hcum]
  rw [hfun, criticalHalfLineFullEnergy_causalPolynomial_eq_zero_iff hW hthreshold hF k hkpos,
    ← hcum]
  exact (criticalCausalCumulativeDelays_coefficients_zero_iff k).symm

/-- Every nontrivial real combination of distinct positive causal translates has positive energy. -/
theorem criticalHalfLineFullEnergy_strict_ordered_sum_pos
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) (hpos : ∀ q ∈ l, 0 < q.1)
    (hord : l.Pairwise (fun q r => q.1 < r.1))
    (hne : ∃ q ∈ l, q.2 ≠ 0) :
    0 < criticalHalfLineFullEnergy W₀
      (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) := by
  obtain ⟨k, hk, _⟩ := exists_strict_criticalCausalCumulativeDelays_from l 0 hpos hord
  simp only [zero_add, Prod.mk.eta] at hk
  change (criticalCausalCumulativeDelays k).map id = l at hk
  rw [List.map_id] at hk
  have hfun : (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) =
      criticalCausalPolynomial F k := by
    funext u
    rw [criticalCausalPolynomial_eq_sum, hk]
  have hn := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold
    ((criticalHalfLineEnergyDomain_of_groundState hF).causalPolynomial k)
  rw [← hfun] at hn
  refine lt_of_le_of_ne hn ?_
  intro he
  obtain ⟨q, hq, hqne⟩ := hne
  exact hqne ((criticalHalfLineFullEnergy_strict_ordered_sum_eq_zero_iff
    hW hthreshold hF l hpos hord).mp he.symm q hq)

/-- The actual finite causal energy matrices are strictly positive away from delay zero. -/
theorem riemannHypothesis_or_exists_strict_causal_energy_matrices :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ),
      0 < W₀ ∧ (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ l : List (ℝ≥0 × ℝ), (∀ p ∈ l, 0 < (p.1 : ℝ)) →
        (criticalHalfLineFullEnergy W₀ (criticalCausalPolynomial F l) = 0 ↔
          ∀ p ∈ l, p.2 = 0) ∧
        (∀ c : ℝ,
          criticalHalfLineFullEnergy W₀ (criticalCausalPolynomial F ((0, c) :: l)) = 0 ↔
            ∀ p ∈ l, p.2 = 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨W₀, F, hW, ht, hF, ?_⟩
    intro l hpos
    exact ⟨criticalHalfLineFullEnergy_causalPolynomial_eq_zero_iff hW ht hF l hpos,
      criticalHalfLineFullEnergy_causalPolynomial_zero_head_eq_zero_iff hW ht hF l hpos⟩

/-- Failure of RH supplies strict positivity for every ordered positive causal-delay matrix. -/
theorem riemannHypothesis_or_exists_strict_ordered_causal_energy_matrices :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ),
      0 < W₀ ∧ (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ l : List (ℝ≥0 × ℝ), (∀ q ∈ l, 0 < q.1) →
        l.Pairwise (fun q r => q.1 < r.1) →
        (criticalHalfLineFullEnergy W₀
          (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) = 0 ↔
            ∀ q ∈ l, q.2 = 0) ∧
        ((∃ q ∈ l, q.2 ≠ 0) → 0 < criticalHalfLineFullEnergy W₀
          (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨W₀, F, hW, ht, hF, ?_⟩
    intro l hpos hord
    exact ⟨criticalHalfLineFullEnergy_strict_ordered_sum_eq_zero_iff hW ht hF l hpos hord,
      criticalHalfLineFullEnergy_strict_ordered_sum_pos hW ht hF l hpos hord⟩

#print axioms criticalCausalPolynomial_coefficients_zero_of_ae_zero
#print axioms criticalHalfLineFullEnergy_causalPolynomial_eq_zero_iff
#print axioms riemannHypothesis_or_exists_strict_causal_energy_matrices
#print axioms riemannHypothesis_or_exists_strict_ordered_causal_energy_matrices

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
