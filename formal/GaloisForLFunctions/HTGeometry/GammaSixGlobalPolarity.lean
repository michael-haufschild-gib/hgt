import GaloisForLFunctions.HTGeometry.HellingerAffinityProduct
import GaloisForLFunctions.HTGeometry.ProductOccupancyDichotomy

/-!
# Global polarity of the infinite Gamma-six formation

The forward and reflected labelled Gamma-six formations are the Kolmogorov products of their shell
packets over all shells.  Off the functional-equation centre their occupancy masses are summable in
one direction and divergent in the other, so the first and second Borel--Cantelli lemmas separate
them by the finite-occupancy event: the two laws are mutually singular.  At the centre they are
identical.  Fixed-label functional-equation quasi-invariance therefore forces neutrality.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal

noncomputable section

/-! ## The labelled shell index -/

/-- The label set of the Gamma-six formation: one label per coordinate of every shell `m ≥ 3`. -/
abbrev GammaSixLabel := Σ _k : ℕ, Fin (gammaSixCount (_k + 3))

theorem gammaSixCount_pos (m : ℕ) : 0 < gammaSixCount m := by
  rw [gammaSixCount]
  positivity

instance : Infinite GammaSixLabel := by
  refine Infinite.of_injective (fun k : ℕ => (⟨k, ⟨0, gammaSixCount_pos (k + 3)⟩⟩ :
    GammaSixLabel)) ?_
  intro k l h
  simpa using congrArg Sigma.fst h

/-- Forward coordinate intensity as a nonnegative rate. -/
def gammaSixForwardNN (m : ℕ) (δ : ℝ) : ℝ≥0 :=
  ⟨gammaSixForward m δ, (gammaSixForward_pos m δ).le⟩

@[simp] theorem coe_gammaSixForwardNN (m : ℕ) (δ : ℝ) :
    (gammaSixForwardNN m δ : ℝ) = gammaSixForward m δ := rfl

/-- The infinite labelled Gamma-six formation at displacement `δ`. -/
def gammaSixLaw (δ : ℝ) : Measure (GammaSixLabel → ℕ) :=
  Measure.infinitePi fun l : GammaSixLabel => Po(gammaSixForwardNN (l.1 + 3) δ)

instance isProbabilityMeasure_gammaSixLaw (δ : ℝ) : IsProbabilityMeasure (gammaSixLaw δ) := by
  rw [gammaSixLaw]
  infer_instance

/-! ## Occupancy masses -/

theorem poissonMeasure_compl_zero (r : ℝ≥0) :
    Po(r) ({0}ᶜ : Set ℕ) = ENNReal.ofReal (1 - Real.exp (-(r : ℝ))) := by
  have hle : Real.exp (-(r : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
  rw [prob_compl_eq_one_sub (MeasurableSet.singleton 0), poissonMeasure_singleton]
  norm_num
  rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  simp

theorem one_sub_exp_neg_ge {a : ℝ} (ha : 0 ≤ a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by
  have h1 : (0 : ℝ) < 1 + a := by linarith
  have hexp : 1 + a ≤ Real.exp a := by
    simpa [add_comm] using Real.add_one_le_exp a
  have hpos : (0 : ℝ) < Real.exp a := Real.exp_pos a
  have hinv : Real.exp (-a) ≤ 1 / (1 + a) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos h1]
    linarith
  have heq : 1 - 1 / (1 + a) = a / (1 + a) := by
    field_simp
    ring
  linarith

theorem one_sub_exp_neg_ge_min {a : ℝ} (ha : 0 ≤ a) : min a 1 / 2 ≤ 1 - Real.exp (-a) := by
  refine le_trans ?_ (one_sub_exp_neg_ge ha)
  have h1 : (0 : ℝ) < 1 + a := by linarith
  rw [div_le_div_iff₀ (by norm_num) h1]
  rcases le_total a 1 with h | h
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right h]
    nlinarith

theorem one_sub_exp_neg_le {a : ℝ} : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

/-! ## The occupancy dichotomy for the Gamma-six formation -/

/-- An enumeration of the Gamma-six label set. -/
def gammaSixLabelEquiv : ℕ ≃ GammaSixLabel :=
  (@Denumerable.eqv GammaSixLabel (Classical.choice (nonempty_denumerable GammaSixLabel))).symm

theorem gammaSix_occupancyMass (δ : ℝ) (l : GammaSixLabel) :
    Po(gammaSixForwardNN (l.1 + 3) δ) ({0}ᶜ : Set ℕ)
      = ENNReal.ofReal (1 - Real.exp (-gammaSixForward (l.1 + 3) δ)) := by
  rw [poissonMeasure_compl_zero, coe_gammaSixForwardNN]

theorem gammaSix_occupancy_nonneg (δ : ℝ) (l : GammaSixLabel) :
    0 ≤ 1 - Real.exp (-gammaSixForward (l.1 + 3) δ) := by
  have : Real.exp (-gammaSixForward (l.1 + 3) δ) ≤ 1 :=
    Real.exp_le_one_iff.2 (by simpa using (gammaSixForward_pos (l.1 + 3) δ).le)
  linarith

/-- Below the centre the occupancy masses of the reflected formation are summable. -/
theorem summable_gammaSix_occupancy_neg {δ : ℝ} (hδ : 0 < δ) :
    Summable fun l : GammaSixLabel => 1 - Real.exp (-gammaSixForward (l.1 + 3) (-δ)) := by
  set ρ : ℝ := Real.exp (-(Real.log 6 * δ)) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hlog6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (by nlinarith [hlog6, hδ])
  have hgeo : Summable fun k : ℕ => 5 * ρ ^ (k + 3) :=
    Summable.mul_left 5 ((summable_nat_add_iff 3).2 (summable_geometric_of_lt_one hρ0.le hρ1))
  refine (summable_sigma_of_nonneg (fun l => gammaSix_occupancy_nonneg (-δ) l)).2 ⟨?_, ?_⟩
  · intro k
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun i =>
      gammaSix_occupancy_nonneg (-δ) ⟨k, i⟩) (fun k => ?_) hgeo
    have hfin : ∑' _i : Fin (gammaSixCount (k + 3)),
        (1 - Real.exp (-gammaSixForward (k + 3) (-δ)))
        = (gammaSixCount (k + 3) : ℝ) * (1 - Real.exp (-gammaSixForward (k + 3) (-δ))) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hfin]
    calc (gammaSixCount (k + 3) : ℝ) * (1 - Real.exp (-gammaSixForward (k + 3) (-δ)))
        ≤ (gammaSixCount (k + 3) : ℝ) * gammaSixForward (k + 3) (-δ) :=
          mul_le_mul_of_nonneg_left one_sub_exp_neg_le (by positivity)
      _ = 5 * ρ ^ (k + 3) := by
          rw [gammaSixForward_neg, gammaSixReflected_total, gammaSixClock, hρdef,
            ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring

/-- Above the centre the occupancy masses of the forward formation diverge. -/
theorem not_summable_gammaSix_occupancy {δ : ℝ} (hδ : 0 < δ) :
    ¬ Summable fun l : GammaSixLabel => 1 - Real.exp (-gammaSixForward (l.1 + 3) δ) := by
  intro hsum
  have hshell := ((summable_sigma_of_nonneg
    (fun l => gammaSix_occupancy_nonneg δ l)).1 hsum).2
  have hzero := hshell.tendsto_atTop_zero
  have hlow : ∀ k : ℕ, (5 : ℝ) / 2 ≤ ∑' _i : Fin (gammaSixCount (k + 3)),
      (1 - Real.exp (-gammaSixForward (k + 3) δ)) := by
    intro k
    have hfin : ∑' _i : Fin (gammaSixCount (k + 3)),
        (1 - Real.exp (-gammaSixForward (k + 3) δ))
        = (gammaSixCount (k + 3) : ℝ) * (1 - Real.exp (-gammaSixForward (k + 3) δ)) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hfin]
    have hNpos : (0 : ℝ) < (gammaSixCount (k + 3) : ℝ) := by
      exact_mod_cast gammaSixCount_pos (k + 3)
    have hmin := one_sub_exp_neg_ge_min (gammaSixForward_pos (k + 3) δ).le
    have hstep : (gammaSixCount (k + 3) : ℝ) * (min (gammaSixForward (k + 3) δ) 1 / 2)
        ≤ (gammaSixCount (k + 3) : ℝ) * (1 - Real.exp (-gammaSixForward (k + 3) δ)) :=
      mul_le_mul_of_nonneg_left hmin hNpos.le
    have hA : (5 : ℝ) ≤ (gammaSixCount (k + 3) : ℝ) * gammaSixForward (k + 3) δ := by
      rw [gammaSixForward_total, gammaSixClock]
      have hx : (0 : ℝ) ≤ ((k : ℝ) + 3) * Real.log 6 * δ := by
        have hlog6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
        positivity
      have hexp : (1 : ℝ) ≤ Real.exp (((k + 3 : ℕ) : ℝ) * Real.log 6 * δ) := by
        rw [Real.one_le_exp_iff]
        push_cast
        exact hx
      linarith
    have hN : (5 : ℝ) ≤ (gammaSixCount (k + 3) : ℝ) := by
      rw [gammaSixCount]
      have : (1 : ℝ) ≤ (6 : ℝ) ^ (k + 3) := one_le_pow₀ (by norm_num)
      push_cast
      linarith
    have hmul : (5 : ℝ) / 2
        ≤ (gammaSixCount (k + 3) : ℝ) * (min (gammaSixForward (k + 3) δ) 1 / 2) := by
      rcases le_total (gammaSixForward (k + 3) δ) 1 with h | h
      · rw [min_eq_left h]
        nlinarith [hA]
      · rw [min_eq_right h]
        nlinarith [hN]
    linarith
  have hcontra := hzero.eventually (gt_mem_nhds (show (0 : ℝ) < 5 / 2 by norm_num))
  obtain ⟨k, hk⟩ := hcontra.exists
  exact absurd (hlow k) (not_le.2 hk)

/-! ## Global polarity -/

theorem tsum_gammaSix_occupancy_ne_top {δ : ℝ} (hδ : 0 < δ) :
    (∑' l : GammaSixLabel,
      Po(gammaSixForwardNN (l.1 + 3) (-δ)) ({0}ᶜ : Set ℕ)) ≠ ∞ := by
  rw [tsum_congr fun l => gammaSix_occupancyMass (-δ) l]
  exact (tsum_ofReal_ne_top_iff_summable _ (fun l => gammaSix_occupancy_nonneg (-δ) l)).2
    (summable_gammaSix_occupancy_neg hδ)

theorem tsum_gammaSix_occupancy_eq_top {δ : ℝ} (hδ : 0 < δ) :
    (∑' l : GammaSixLabel, Po(gammaSixForwardNN (l.1 + 3) δ) ({0}ᶜ : Set ℕ)) = ∞ := by
  rw [tsum_congr fun l => gammaSix_occupancyMass δ l]
  by_contra h
  exact not_summable_gammaSix_occupancy hδ
    ((tsum_ofReal_ne_top_iff_summable _ (fun l => gammaSix_occupancy_nonneg δ l)).1 h)

/-- **Global polarity, positive displacement.**  Off the centre the forward and reflected labelled
Gamma-six formations are mutually singular, separated by the finite-occupancy event. -/
theorem gammaSixLaw_mutuallySingular_of_pos {δ : ℝ} (hδ : 0 < δ) :
    (gammaSixLaw δ).MutuallySingular (gammaSixLaw (-δ)) := by
  refine ⟨{k : GammaSixLabel → ℕ | (occupiedSet k).Finite},
    measurableSet_finiteOccupancy gammaSixLabelEquiv, ?_, ?_⟩
  · rw [gammaSixLaw, finiteOccupancy_eq_compl,
      MeasureTheory.prob_compl_eq_zero_iff (measurableSet_infiniteOccupancy gammaSixLabelEquiv)]
    exact measure_infiniteOccupancy_eq_one _ gammaSixLabelEquiv
      (tsum_gammaSix_occupancy_eq_top hδ)
  · rw [gammaSixLaw, show ({k : GammaSixLabel → ℕ | (occupiedSet k).Finite}ᶜ)
        = {k : GammaSixLabel → ℕ | (occupiedSet k).Infinite} from by
      rw [finiteOccupancy_eq_compl, compl_compl]]
    exact measure_infiniteOccupancy_eq_zero _ gammaSixLabelEquiv
      (tsum_gammaSix_occupancy_ne_top hδ)

/-- **Global polarity.** -/
theorem gammaSixLaw_mutuallySingular {δ : ℝ} (hδ : δ ≠ 0) :
    (gammaSixLaw δ).MutuallySingular (gammaSixLaw (-δ)) := by
  rcases lt_or_gt_of_ne hδ with h | h
  · have h' : 0 < -δ := by linarith
    have := gammaSixLaw_mutuallySingular_of_pos h'
    rw [neg_neg] at this
    exact this.symm
  · exact gammaSixLaw_mutuallySingular_of_pos h

/-- **Fixed-label functional-equation quasi-invariance forces neutrality.** -/
theorem gammaSixLaw_absolutelyContinuous_iff (δ : ℝ) :
    gammaSixLaw δ ≪ gammaSixLaw (-δ) ↔ δ = 0 := by
  constructor
  · intro hac
    by_contra hδ
    obtain ⟨S, -, hS1, hS2⟩ := gammaSixLaw_mutuallySingular hδ
    have hSc : gammaSixLaw δ Sᶜ = 0 := hac hS2
    have hzero : gammaSixLaw δ Set.univ = 0 := by
      have hle := measure_union_le (μ := gammaSixLaw δ) S Sᶜ
      rw [Set.union_compl_self, hS1, hSc, add_zero] at hle
      exact nonpos_iff_eq_zero.1 hle
    rw [measure_univ] at hzero
    exact one_ne_zero hzero
  · rintro rfl
    rw [neg_zero]

/-- **Global polarity as an equality criterion.** -/
theorem gammaSixLaw_eq_iff (δ : ℝ) : gammaSixLaw δ = gammaSixLaw (-δ) ↔ δ = 0 := by
  constructor
  · intro h
    exact (gammaSixLaw_absolutelyContinuous_iff δ).1 (h ▸ Measure.AbsolutelyContinuous.rfl)
  · rintro rfl
    rw [neg_zero]

end

end GaloisForLFunctions.HTGeometry
