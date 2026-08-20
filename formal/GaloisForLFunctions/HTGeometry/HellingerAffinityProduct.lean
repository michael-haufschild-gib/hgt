import GaloisForLFunctions.HTGeometry.PoissonIntensityMarkingIsometry

/-!
# Hellinger affinity is multiplicative over independent packets

On a countable space the Hellinger affinity of two laws is the atom series `∑ √(P{a}Q{a})`.  It is
invariant under relabelling by a measurable equivalence and multiplicative over independent
products, hence equal to the product of the coordinate affinities for a finite labelled packet.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

theorem sqrt_mul_le_add_div_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 := by
  rw [show (x + y) / 2 = Real.sqrt (((x + y) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (x - y)]

theorem summable_hellingerTerm {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    Summable fun a : α => Real.sqrt ((P {a}).toReal * (Q {a}).toReal) := by
  have hmaj : Summable fun a : α => ((P {a}).toReal + (Q {a}).toReal) / 2 :=
    (((hasSum_measure_singleton_toReal P).add
      (hasSum_measure_singleton_toReal Q)).div_const 2).summable
  refine Summable.of_nonneg_of_le (fun a => Real.sqrt_nonneg _) (fun a => ?_) hmaj
  exact sqrt_mul_le_add_div_two ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem hellingerAffinity_nonneg {α : Type*} [MeasurableSpace α] (P Q : Measure α) :
    0 ≤ hellingerAffinity P Q :=
  tsum_nonneg fun _ => Real.sqrt_nonneg _

/-- Hellinger affinity is invariant under relabelling. -/
theorem hellingerAffinity_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (e : α ≃ᵐ β) (P Q : Measure α) :
    hellingerAffinity (P.map e) (Q.map e) = hellingerAffinity P Q := by
  have hpre : ∀ b : β, (e : α → β) ⁻¹' {b} = {e.symm b} := by
    intro b
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  have hatom : ∀ b : β, (P.map e) {b} = P {e.symm b} := by
    intro b
    rw [MeasurableEquiv.map_apply, hpre b]
  have hatomQ : ∀ b : β, (Q.map e) {b} = Q {e.symm b} := by
    intro b
    rw [MeasurableEquiv.map_apply, hpre b]
  rw [hellingerAffinity, hellingerAffinity,
    tsum_congr (fun b => by rw [hatom b, hatomQ b])]
  exact e.toEquiv.symm.tsum_eq fun a => Real.sqrt ((P {a}).toReal * (Q {a}).toReal)

/-- **Hellinger affinity is multiplicative over independent products.** -/
theorem hellingerAffinity_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    hellingerAffinity (P₁.prod P₂) (Q₁.prod Q₂)
      = hellingerAffinity P₁ Q₁ * hellingerAffinity P₂ Q₂ := by
  have hs1 := summable_hellingerTerm P₁ Q₁
  have hs2 := summable_hellingerTerm P₂ Q₂
  have hmul := hs1.mul_of_nonneg hs2 (fun a => Real.sqrt_nonneg _) (fun b => Real.sqrt_nonneg _)
  rw [hellingerAffinity, hellingerAffinity, hellingerAffinity, hs1.tsum_mul_tsum hs2 hmul]
  refine tsum_congr fun p => ?_
  obtain ⟨a, b⟩ := p
  have h1 : (P₁.prod P₂) {(a, b)} = P₁ {a} * P₂ {b} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  have h2 : (Q₁.prod Q₂) {(a, b)} = Q₁ {a} * Q₂ {b} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [h1, h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    show (P₁ {a}).toReal * (P₂ {b}).toReal * ((Q₁ {a}).toReal * (Q₂ {b}).toReal)
      = ((P₁ {a}).toReal * (Q₁ {a}).toReal) * ((P₂ {b}).toReal * (Q₂ {b}).toReal) from by ring,
    Real.sqrt_mul (by positivity)]

/-- **Hellinger affinity of a finite labelled packet.** -/
theorem hellingerAffinity_pi {n : ℕ} {Z : Type*} [MeasurableSpace Z] [Countable Z]
    [MeasurableSingletonClass Z] (P Q : Fin n → Measure Z)
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)] :
    hellingerAffinity (Measure.pi P) (Measure.pi Q) = ∏ i, hellingerAffinity (P i) (Q i) := by
  induction n with
  | zero =>
      have hsub : Subsingleton (Fin 0 → Z) := inferInstance
      have hpi : Measure.pi P = Measure.pi Q := by
        refine Measure.ext fun s _ => ?_
        rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
        · simp
        · have hs : s = Set.univ := by
            ext y
            simp [Subsingleton.elim y x, hx]
          rw [hs, measure_univ, measure_univ]
      have hone : hellingerAffinity (Measure.pi Q) (Measure.pi Q) = 1 := by
        rw [hellingerAffinity]
        have hterm : ∀ f : Fin 0 → Z,
            Real.sqrt (((Measure.pi Q) {f}).toReal * ((Measure.pi Q) {f}).toReal)
              = ((Measure.pi Q) {f}).toReal := by
          intro f
          rw [Real.sqrt_mul_self ENNReal.toReal_nonneg]
        rw [tsum_congr hterm]
        exact (hasSum_measure_singleton_toReal (Measure.pi Q)).tsum_eq
      rw [hpi, hone]
      simp
  | succ k ih =>
      have hmp := measurePreserving_piFinSuccAbove P 0
      have hnp := measurePreserving_piFinSuccAbove Q 0
      rw [← hellingerAffinity_map_measurableEquiv
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Z) 0) (Measure.pi P)
        (Measure.pi Q), hmp.map_eq, hnp.map_eq, hellingerAffinity_prod,
        ih (fun j => P ((0 : Fin (k + 1)).succAbove j))
          (fun j => Q ((0 : Fin (k + 1)).succAbove j)), Fin.prod_univ_succ]
      simp

theorem hellingerAffinity_pi_const {n : ℕ} {Z : Type*} [MeasurableSpace Z] [Countable Z]
    [MeasurableSingletonClass Z] (P Q : Measure Z) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    hellingerAffinity (Measure.pi fun _ : Fin n => P) (Measure.pi fun _ : Fin n => Q)
      = hellingerAffinity P Q ^ n := by
  rw [hellingerAffinity_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The Gamma-six labelled packet -/

/-- **Poisson relative entropy of the Gamma-six labelled packet**, forward direction. -/
theorem gammaSix_packet_klDiv (m : ℕ) (δ : ℝ) (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b)
    (hav : (a : ℝ) = gammaSixForward m δ) (hbv : (b : ℝ) = gammaSixReflected m δ) :
    (klDiv (Measure.pi fun _ : Fin (gammaSixCount m) => Po(a))
        (Measure.pi fun _ : Fin (gammaSixCount m) => Po(b))).toReal
      = 2 * gammaSixClock m δ * (5 * Real.exp (gammaSixClock m δ))
        - 5 * Real.exp (gammaSixClock m δ) + 5 * Real.exp (-gammaSixClock m δ) := by
  rw [toReal_klDiv_poissonPacket (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)]
  simp only [hav, hbv]
  exact gammaSix_forward_div m δ

/-- **Poisson relative entropy of the Gamma-six labelled packet**, reflected direction. -/
theorem gammaSix_packet_klDiv_reflected (m : ℕ) (δ : ℝ) (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b)
    (hav : (a : ℝ) = gammaSixForward m δ) (hbv : (b : ℝ) = gammaSixReflected m δ) :
    (klDiv (Measure.pi fun _ : Fin (gammaSixCount m) => Po(b))
        (Measure.pi fun _ : Fin (gammaSixCount m) => Po(a))).toReal
      = -(2 * gammaSixClock m δ) * (5 * Real.exp (-gammaSixClock m δ))
        - 5 * Real.exp (-gammaSixClock m δ) + 5 * Real.exp (gammaSixClock m δ) := by
  rw [toReal_klDiv_poissonPacket (fun _ => b) (fun _ => a) (fun _ => hb) (fun _ => ha)]
  simp only [hav, hbv]
  exact gammaSix_reflected_div m δ

/-- **Poisson Hellinger affinity of the Gamma-six labelled packet.** -/
theorem gammaSix_packet_affinity (m : ℕ) (δ : ℝ) (a b : ℝ≥0)
    (hav : (a : ℝ) = gammaSixForward m δ) (hbv : (b : ℝ) = gammaSixReflected m δ) :
    hellingerAffinity (Measure.pi fun _ : Fin (gammaSixCount m) => Po(a))
        (Measure.pi fun _ : Fin (gammaSixCount m) => Po(b))
      = Real.exp (-5 * (Real.cosh (gammaSixClock m δ) - 1)) := by
  rw [hellingerAffinity_pi_const]
  exact gammaSix_affinity m δ a b hav hbv

end

end GaloisForLFunctions.HTGeometry
