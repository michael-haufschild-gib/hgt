import GaloisForLFunctions.RHTower.SoninPrimeArchAdjacentNormTomography
import GaloisForLFunctions.RHTower.SoninPrimeArchMomentBarycenter

/-!
# Adjacent-norm tomography for Sonin aperture barycenters

The Sonin moment barycenter ranges over every energy moment.  This module proves that the same
measure-valued condition can be tested using only two explicit Hilbert-norm families: monomials
and adjacent binomials.  Monomials recover even moments; polarization of adjacent binomials
recovers odd moments, including integrability.  Thus these sparse norm probes are a complete
tomography of positive aperture barycenters and retain the existing implication to RH.
-/

open MeasureTheory Polynomial

namespace RHTower

noncomputable section

/-- A positive aperture measure whose monomial and adjacent-binomial norm integrals equal the
corresponding prime--Gamma targets. -/
def SoninPrimeArchAdjacentNormBarycenter (nu : Measure ℝ) : Prop :=
  (∀ᵐ a ∂nu, 0 < a) ∧
    (∀ n, Integrable (fun a => soninAllPrimeTraceHankel a (X ^ n)) nu ∧
      (∫ a, soninAllPrimeTraceHankel a (X ^ n) ∂nu) =
        ((normalizedPrimeArchMoment (2 * n) : ℝ) : ℂ)) ∧
    ∀ n, Integrable (fun a =>
        soninAllPrimeTraceHankel a (X ^ n + X ^ (n + 1))) nu ∧
      (∫ a, soninAllPrimeTraceHankel a (X ^ n + X ^ (n + 1)) ∂nu) =
        ((normalizedPrimeArchMoment (2 * n) : ℝ) : ℂ) +
          2 * ((normalizedPrimeArchMoment (2 * n + 1) : ℝ) : ℂ) +
          ((normalizedPrimeArchMoment (2 * n + 2) : ℝ) : ℂ)

/-- Every all-moment barycenter satisfies the two sparse norm-probe families. -/
theorem soninPrimeArchAdjacentNormBarycenter_of_momentBarycenter
    {nu : Measure ℝ} (h : SoninPrimeArchMomentBarycenter nu) :
    SoninPrimeArchAdjacentNormBarycenter nu := by
  refine ⟨h.1, ?_, ?_⟩
  · intro n
    have heq : (fun a => soninAllPrimeTraceHankel a (X ^ n)) =ᵐ[nu]
        fun a => soninAllPrimeEnergyMoment a (2 * n) :=
      h.1.mono fun a ha => soninAllPrimeTraceHankel_monomial_eq_energyMoment a ha n
    refine ⟨(h.2.1 (2 * n)).congr heq.symm, ?_⟩
    rw [integral_congr_ae heq]
    exact (h.2.2 (2 * n)).symm
  · intro n
    have heq :
        (fun a => soninAllPrimeTraceHankel a (X ^ n + X ^ (n + 1))) =ᵐ[nu]
          fun a => soninAllPrimeEnergyMoment a (2 * n) +
            2 * soninAllPrimeEnergyMoment a (2 * n + 1) +
            soninAllPrimeEnergyMoment a (2 * n + 2) :=
      h.1.mono fun a ha => soninAllPrimeTraceHankel_adjacent_eq_energyMoments a ha n
    have h0 := h.2.1 (2 * n)
    have h1 := h.2.1 (2 * n + 1)
    have h2 := h.2.1 (2 * n + 2)
    refine ⟨(h0.add (h1.const_mul 2) |>.add h2).congr heq.symm, ?_⟩
    rw [integral_congr_ae heq]
    have hsum0 := integral_add h0 (h1.const_mul 2)
    change (∫ a, soninAllPrimeEnergyMoment a (2 * n) +
        2 * soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) =
      (∫ a, soninAllPrimeEnergyMoment a (2 * n) ∂nu) +
        (∫ a, 2 * soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) at hsum0
    have hsum2 := integral_add (h0.add (h1.const_mul 2)) h2
    change (∫ a, (soninAllPrimeEnergyMoment a (2 * n) +
        2 * soninAllPrimeEnergyMoment a (2 * n + 1)) +
        soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) =
      (∫ a, soninAllPrimeEnergyMoment a (2 * n) +
        2 * soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) +
      (∫ a, soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) at hsum2
    have hmul := integral_const_mul (μ := nu) (2 : ℂ)
      (fun a => soninAllPrimeEnergyMoment a (2 * n + 1))
    calc
      (∫ a, soninAllPrimeEnergyMoment a (2 * n) +
          2 * soninAllPrimeEnergyMoment a (2 * n + 1) +
          soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) =
          (∫ a, soninAllPrimeEnergyMoment a (2 * n) ∂nu) +
            2 * (∫ a, soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) +
            (∫ a, soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) := by
            rw [hsum2, hsum0, hmul]
      _ = _ := by
        rw [← h.2.2 (2 * n), ← h.2.2 (2 * n + 1), ← h.2.2 (2 * n + 2)]

/-- Sparse monomial and adjacent-binomial norm data reconstruct all Sonin moments, including
integrability of every odd moment. -/
theorem soninPrimeArchMomentBarycenter_of_adjacentNormBarycenter
    {nu : Measure ℝ} (h : SoninPrimeArchAdjacentNormBarycenter nu) :
    SoninPrimeArchMomentBarycenter nu := by
  have heven (n : ℕ) :
      (fun a => soninAllPrimeTraceHankel a (X ^ n)) =ᵐ[nu]
        fun a => soninAllPrimeEnergyMoment a (2 * n) :=
    h.1.mono fun a ha => soninAllPrimeTraceHankel_monomial_eq_energyMoment a ha n
  have hadj (n : ℕ) :
      (fun a => soninAllPrimeTraceHankel a (X ^ n + X ^ (n + 1))) =ᵐ[nu]
        fun a => soninAllPrimeEnergyMoment a (2 * n) +
          2 * soninAllPrimeEnergyMoment a (2 * n + 1) +
          soninAllPrimeEnergyMoment a (2 * n + 2) :=
    h.1.mono fun a ha => soninAllPrimeTraceHankel_adjacent_eq_energyMoments a ha n
  have hIntEven (n : ℕ) : Integrable (fun a => soninAllPrimeEnergyMoment a (2 * n)) nu :=
    (h.2.1 n).1.congr (heven n)
  have hIntOdd (n : ℕ) : Integrable (fun a => soninAllPrimeEnergyMoment a (2 * n + 1)) nu := by
    have hrewrite :
        (fun a => soninAllPrimeEnergyMoment a (2 * n + 1)) =ᵐ[nu]
          fun a => (soninAllPrimeTraceHankel a (X ^ n + X ^ (n + 1)) -
            soninAllPrimeTraceHankel a (X ^ n) -
            soninAllPrimeTraceHankel a (X ^ (n + 1))) / 2 := by
      filter_upwards [heven n, heven (n + 1), hadj n] with a h0 h2 ha
      rw [h0, h2, ha]
      ring_nf
    exact ((((h.2.2 n).1.sub (h.2.1 n).1).sub (h.2.1 (n + 1)).1).div_const 2).congr
      hrewrite.symm
  refine ⟨h.1, ?_, ?_⟩
  · intro r
    rcases Nat.even_or_odd r with hr | hr
    · obtain ⟨n, rfl⟩ := hr
      simpa [two_mul] using hIntEven n
    · obtain ⟨n, rfl⟩ := hr
      exact hIntOdd n
  · intro r
    rcases Nat.even_or_odd r with hr | hr
    · obtain ⟨n, rfl⟩ := hr
      simpa [two_mul, integral_congr_ae (heven n)] using (h.2.1 n).2.symm
    · obtain ⟨n, rfl⟩ := hr
      have h0 := hIntEven n
      have h1 := hIntOdd n
      have h2 : Integrable (fun a => soninAllPrimeEnergyMoment a (2 * n + 2)) nu := by
        simpa [Nat.mul_add] using hIntEven (n + 1)
      have htarget := (h.2.2 n).2
      rw [integral_congr_ae (hadj n)] at htarget
      have hsum0 := integral_add h0 (h1.const_mul 2)
      change (∫ a, soninAllPrimeEnergyMoment a (2 * n) +
          2 * soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) =
        (∫ a, soninAllPrimeEnergyMoment a (2 * n) ∂nu) +
          (∫ a, 2 * soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) at hsum0
      have hsum2 := integral_add (h0.add (h1.const_mul 2)) h2
      change (∫ a, (soninAllPrimeEnergyMoment a (2 * n) +
          2 * soninAllPrimeEnergyMoment a (2 * n + 1)) +
          soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) =
        (∫ a, soninAllPrimeEnergyMoment a (2 * n) +
          2 * soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) +
        (∫ a, soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) at hsum2
      have hmul := integral_const_mul (μ := nu) (2 : ℂ)
        (fun a => soninAllPrimeEnergyMoment a (2 * n + 1))
      have hsum :
          (∫ a, soninAllPrimeEnergyMoment a (2 * n) +
            2 * soninAllPrimeEnergyMoment a (2 * n + 1) +
            soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) =
          (∫ a, soninAllPrimeEnergyMoment a (2 * n) ∂nu) +
            2 * (∫ a, soninAllPrimeEnergyMoment a (2 * n + 1) ∂nu) +
            (∫ a, soninAllPrimeEnergyMoment a (2 * n + 2) ∂nu) := by
        rw [hsum2, hsum0, hmul]
      rw [hsum] at htarget
      have heven2 :
          (fun a => soninAllPrimeTraceHankel a (X ^ (n + 1))) =ᵐ[nu]
            fun a => soninAllPrimeEnergyMoment a (2 * n + 2) := by
        simpa [Nat.mul_add] using heven (n + 1)
      rw [← integral_congr_ae (heven n),
        ← integral_congr_ae heven2] at htarget
      have hm0 := (h.2.1 n).2
      have hm2 := (h.2.1 (n + 1)).2
      linear_combination (-1 / 2 : ℂ) * htarget +
        (1 / 2 : ℂ) * hm0 + (1 / 2 : ℂ) * hm2

/-- **Adjacent-norm barycenter universality.**  Two sparse norm-probe families carry exactly the
same measure-valued information as the complete Sonin prime--archimedean moment barycenter. -/
theorem soninPrimeArchAdjacentNormBarycenter_iff_momentBarycenter
    {nu : Measure ℝ} :
    SoninPrimeArchAdjacentNormBarycenter nu ↔ SoninPrimeArchMomentBarycenter nu :=
  ⟨soninPrimeArchMomentBarycenter_of_adjacentNormBarycenter,
    soninPrimeArchAdjacentNormBarycenter_of_momentBarycenter⟩

/-- The sparse adjacent-norm barycenter condition retains the established implication to RH. -/
theorem riemannHypothesis_of_soninPrimeArchAdjacentNormBarycenter
    {nu : Measure ℝ} (h : SoninPrimeArchAdjacentNormBarycenter nu) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninPrimeArchMomentBarycenter
    (soninPrimeArchMomentBarycenter_of_adjacentNormBarycenter h)

end

end RHTower
