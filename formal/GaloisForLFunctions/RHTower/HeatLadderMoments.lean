import GaloisForLFunctions.RHTower.HeatLadderExpand
import GaloisForLFunctions.RHTower.HeatEnergyAsymptotic

/-!
# The all-order principal energy as a finite sum of window moments

Integrating the all-order squared principal part against the heat multiplier turns every
two-sided power test into an averaged coefficient times a window moment.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The `K`-th order principal energy, as a finite sum of window moments. -/
noncomputable def heatLadderMoments (s : ℂ) (K : ℕ) (x : ℝ) : ℂ :=
  ((((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ) + ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ)) / 2)
      * heatMoment x (((2 * s.re - 2 : ℝ)) : ℂ)
    + ∑ k ∈ Finset.range (K + 1),
        ((jonquiereLead s * (starRingEnd ℂ) (jonquiereRegCoeff s k)
            + (-1 : ℂ) ^ k * (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereRegCoeff s k))) / 2)
          * heatMoment x (s - 1 + ((k : ℕ) : ℂ))
    + ∑ k ∈ Finset.range (K + 1),
        (((starRingEnd ℂ) (jonquiereLead s) * jonquiereRegCoeff s k
            + (-1 : ℂ) ^ k
              * ((starRingEnd ℂ) (jonquiereLeadNeg s) * jonquiereRegCoeff s k)) / 2)
          * heatMoment x ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ))
    + ∑ k ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
        ((jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
            + (-1 : ℂ) ^ (k + l)
              * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l))) / 2)
          * heatMoment x (((k + l : ℕ) : ℂ))

/-- The two-sided power test integral, unnormalised. -/
theorem integral_halfSplit_eq {x : ℝ} (hx : 0 < x) {lam : ℂ} (hlam : -1 < lam.re) (cp cm : ℂ) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      = (2 * (Real.pi : ℂ)) * (((cp + cm) / 2) * heatMoment x lam) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push Not
    exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr hpi.ne'⟩
  have h := heatMoment_halfSplit hx hlam cp cm
  rw [← h, ← mul_assoc, mul_one_div, div_self hne, one_mul]

/-- The all-order squared principal part is integrable against the multiplier. -/
theorem integrableOn_principalOrderSq_mul_heatMultiplier {s : ℂ} (h0 : 1 / 2 < s.re)
    (h1 : s.re < 1) {x : ℝ} (hx : 0 < x) (K : ℕ) :
    IntegrableOn (fun θ : ℝ =>
        (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ))
          * heatMultiplier x θ) (Ioc (-Real.pi) Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hl1 : (-1 : ℝ) < (((2 * s.re - 2 : ℝ)) : ℂ).re := by simp; linarith
  have hl2 : ∀ k : ℕ, (-1 : ℝ) < (s - 1 + ((k : ℕ) : ℂ)).re := by
    intro k
    simp
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hl3 : ∀ k : ℕ, (-1 : ℝ) < ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ)).re := by
    intro k
    simp
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hl4 : ∀ m : ℕ, (-1 : ℝ) < (((m : ℕ) : ℂ)).re := by
    intro m
    simp
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hi1 : IntegrableOn (fun θ : ℝ => ((if 0 < θ then ((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ)
      else ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ))
      * ((|θ| : ℝ) : ℂ) ^ (((2 * s.re - 2 : ℝ)) : ℂ)) * heatMultiplier x θ)
      (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx hl1 _ _
  have hi2 : ∀ k ∈ Finset.range (K + 1), IntegrableOn (fun θ : ℝ =>
      ((if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (jonquiereRegCoeff s k)
          else (-1 : ℂ) ^ k * (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereRegCoeff s k)))
        * ((|θ| : ℝ) : ℂ) ^ (s - 1 + ((k : ℕ) : ℂ))) * heatMultiplier x θ)
      (Ioc (-Real.pi) Real.pi) := fun k _ => integrableOn_halfSplit hx (hl2 k) _ _
  have hi3 : ∀ k ∈ Finset.range (K + 1), IntegrableOn (fun θ : ℝ =>
      ((if 0 < θ then (starRingEnd ℂ) (jonquiereLead s) * jonquiereRegCoeff s k
          else (-1 : ℂ) ^ k * ((starRingEnd ℂ) (jonquiereLeadNeg s) * jonquiereRegCoeff s k))
        * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ))) * heatMultiplier x θ)
      (Ioc (-Real.pi) Real.pi) := fun k _ => integrableOn_halfSplit hx (hl3 k) _ _
  have hi4 : ∀ k ∈ Finset.range (K + 1), IntegrableOn (fun θ : ℝ =>
      ∑ l ∈ Finset.range (K + 1),
        ((if 0 < θ then jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
            else (-1 : ℂ) ^ (k + l)
              * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)))
          * ((|θ| : ℝ) : ℂ) ^ (((k + l : ℕ) : ℂ))) * heatMultiplier x θ)
      (Ioc (-Real.pi) Real.pi) := fun k _ =>
    MeasureTheory.integrable_finsetSum _ (fun l _ => integrableOn_halfSplit hx (hl4 (k + l)) _ _)
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  refine (((hi1.add (MeasureTheory.integrable_finsetSum _ hi2)).add
    (MeasureTheory.integrable_finsetSum _ hi3)).add
      (MeasureTheory.integrable_finsetSum _ hi4)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_of_ae hne0] with θ hne
  simp only [Pi.add_apply]
  rw [germPrincipalOrder_mul_conj s K hne, add_mul, add_mul, add_mul]
  simp only [Finset.sum_mul]

/-- **The all-order principal energy is the finite moment sum.** -/
theorem heatLadderMoments_eq {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) {x : ℝ} (hx : 0 < x)
    (K : ℕ) :
    (1 / (2 * (Real.pi : ℂ)))
      * (∫ θ in Ioc (-Real.pi) Real.pi,
          (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ))
            * heatMultiplier x θ)
      = heatLadderMoments s K x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push Not
    exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr hpi.ne'⟩
  have hl1 : (-1 : ℝ) < (((2 * s.re - 2 : ℝ)) : ℂ).re := by simp; linarith
  have hl2 : ∀ k : ℕ, (-1 : ℝ) < (s - 1 + ((k : ℕ) : ℂ)).re := by
    intro k
    simp
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hl3 : ∀ k : ℕ, (-1 : ℝ) < ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ)).re := by
    intro k
    simp
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hl4 : ∀ m : ℕ, (-1 : ℝ) < (((m : ℕ) : ℂ)).re := by
    intro m
    simp
    linarith [Nat.cast_nonneg (α := ℝ) m]
  set g1 : ℝ → ℂ := fun θ => ((if 0 < θ then ((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ)
      else ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ))
    * ((|θ| : ℝ) : ℂ) ^ (((2 * s.re - 2 : ℝ)) : ℂ)) * heatMultiplier x θ with hg1
  set g2 : ℕ → ℝ → ℂ := fun k θ =>
    ((if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (jonquiereRegCoeff s k)
        else (-1 : ℂ) ^ k * (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereRegCoeff s k)))
      * ((|θ| : ℝ) : ℂ) ^ (s - 1 + ((k : ℕ) : ℂ))) * heatMultiplier x θ with hg2
  set g3 : ℕ → ℝ → ℂ := fun k θ =>
    ((if 0 < θ then (starRingEnd ℂ) (jonquiereLead s) * jonquiereRegCoeff s k
        else (-1 : ℂ) ^ k * ((starRingEnd ℂ) (jonquiereLeadNeg s) * jonquiereRegCoeff s k))
      * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ))) * heatMultiplier x θ with hg3
  set g4 : ℕ → ℕ → ℝ → ℂ := fun k l θ =>
    ((if 0 < θ then jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
        else (-1 : ℂ) ^ (k + l)
          * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)))
      * ((|θ| : ℝ) : ℂ) ^ (((k + l : ℕ) : ℂ))) * heatMultiplier x θ with hg4
  have hi1 : IntegrableOn g1 (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx hl1 _ _
  have hi2 : ∀ k ∈ Finset.range (K + 1), IntegrableOn (g2 k) (Ioc (-Real.pi) Real.pi) :=
    fun k _ => integrableOn_halfSplit hx (hl2 k) _ _
  have hi3 : ∀ k ∈ Finset.range (K + 1), IntegrableOn (g3 k) (Ioc (-Real.pi) Real.pi) :=
    fun k _ => integrableOn_halfSplit hx (hl3 k) _ _
  have hi4 : ∀ k ∈ Finset.range (K + 1), ∀ l ∈ Finset.range (K + 1),
      IntegrableOn (g4 k l) (Ioc (-Real.pi) Real.pi) :=
    fun k _ l _ => integrableOn_halfSplit hx (hl4 (k + l)) _ _
  have hi4' : ∀ k ∈ Finset.range (K + 1),
      IntegrableOn (fun θ => ∑ l ∈ Finset.range (K + 1), g4 k l θ) (Ioc (-Real.pi) Real.pi) :=
    fun k hk => MeasureTheory.integrable_finsetSum _ (fun l hl => hi4 k hk l hl)
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hpt : (fun θ : ℝ =>
      (germPrincipalOrder s K θ * (starRingEnd ℂ) (germPrincipalOrder s K θ))
        * heatMultiplier x θ)
      =ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)]
      fun θ => g1 θ + (∑ k ∈ Finset.range (K + 1), g2 k θ)
        + (∑ k ∈ Finset.range (K + 1), g3 k θ)
        + (∑ k ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1), g4 k l θ) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne0] with θ hne
    rw [germPrincipalOrder_mul_conj s K hne, hg1, hg2, hg3, hg4, add_mul, add_mul, add_mul]
    simp only [Finset.sum_mul]
  have hS2 : IntegrableOn (fun θ => ∑ k ∈ Finset.range (K + 1), g2 k θ)
      (Ioc (-Real.pi) Real.pi) := MeasureTheory.integrable_finsetSum _ hi2
  have hS3 : IntegrableOn (fun θ => ∑ k ∈ Finset.range (K + 1), g3 k θ)
      (Ioc (-Real.pi) Real.pi) := MeasureTheory.integrable_finsetSum _ hi3
  have hS4 : IntegrableOn
      (fun θ => ∑ k ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1), g4 k l θ)
      (Ioc (-Real.pi) Real.pi) := MeasureTheory.integrable_finsetSum _ hi4'
  have hA : IntegrableOn (fun θ => g1 θ + ∑ k ∈ Finset.range (K + 1), g2 k θ)
      (Ioc (-Real.pi) Real.pi) := hi1.add hS2
  have hB : IntegrableOn
      (fun θ => g1 θ + (∑ k ∈ Finset.range (K + 1), g2 k θ)
        + ∑ k ∈ Finset.range (K + 1), g3 k θ) (Ioc (-Real.pi) Real.pi) := hA.add hS3
  rw [MeasureTheory.integral_congr_ae hpt]
  rw [MeasureTheory.integral_add hB hS4, MeasureTheory.integral_add hA hS3,
    MeasureTheory.integral_add hi1 hS2,
    MeasureTheory.integral_finsetSum _ hi2, MeasureTheory.integral_finsetSum _ hi3,
    MeasureTheory.integral_finsetSum _ hi4']
  have e1 := integral_halfSplit_eq hx hl1 ((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ)
    ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ)
  have e2 : ∀ k : ℕ, (∫ θ in Ioc (-Real.pi) Real.pi, g2 k θ)
      = (2 * (Real.pi : ℂ)) * (((jonquiereLead s * (starRingEnd ℂ) (jonquiereRegCoeff s k)
          + (-1 : ℂ) ^ k * (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereRegCoeff s k))) / 2)
        * heatMoment x (s - 1 + ((k : ℕ) : ℂ))) := fun k =>
    integral_halfSplit_eq hx (hl2 k) _ _
  have e3 : ∀ k : ℕ, (∫ θ in Ioc (-Real.pi) Real.pi, g3 k θ)
      = (2 * (Real.pi : ℂ)) * ((((starRingEnd ℂ) (jonquiereLead s) * jonquiereRegCoeff s k
          + (-1 : ℂ) ^ k
            * ((starRingEnd ℂ) (jonquiereLeadNeg s) * jonquiereRegCoeff s k)) / 2)
        * heatMoment x ((starRingEnd ℂ) s - 1 + ((k : ℕ) : ℂ))) := fun k =>
    integral_halfSplit_eq hx (hl3 k) _ _
  have e4 : ∀ k l : ℕ, (∫ θ in Ioc (-Real.pi) Real.pi, g4 k l θ)
      = (2 * (Real.pi : ℂ)) * (((jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
          + (-1 : ℂ) ^ (k + l)
            * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l))) / 2)
        * heatMoment x (((k + l : ℕ) : ℂ))) := fun k l =>
    integral_halfSplit_eq hx (hl4 (k + l)) _ _
  have e4' : ∀ k ∈ Finset.range (K + 1),
      (∫ θ in Ioc (-Real.pi) Real.pi, ∑ l ∈ Finset.range (K + 1), g4 k l θ)
      = (2 * (Real.pi : ℂ)) * ∑ l ∈ Finset.range (K + 1),
          (((jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l)
            + (-1 : ℂ) ^ (k + l)
              * (jonquiereRegCoeff s k * (starRingEnd ℂ) (jonquiereRegCoeff s l))) / 2)
            * heatMoment x (((k + l : ℕ) : ℂ))) := by
    intro k hk
    rw [MeasureTheory.integral_finsetSum _ (fun l hl => hi4 k hk l hl), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => e4 k l
  rw [e1, Finset.sum_congr rfl (fun k _ => e2 k), Finset.sum_congr rfl (fun k _ => e3 k),
    Finset.sum_congr rfl e4', heatLadderMoments,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← mul_add, ← mul_add, ← mul_add, ← mul_assoc, one_div_mul_cancel h2pi, one_mul]

end RHTower
