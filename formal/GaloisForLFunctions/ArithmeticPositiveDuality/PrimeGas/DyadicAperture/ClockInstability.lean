import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.ExceptionalTimes
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection

/-!
# Instability at maximal angular aperture

The prime–vacuum pair alone produces a full projection jump in every
sampling-time neighborhood. Its positive Gibbs weight gives a uniform
lower bound on the oscillation of the actual thermal trace.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary

open SampledClocks CopyExchange Set
open scoped Classical

/-- Every sampling-time neighborhood contains readings separated by at least B. -/
def Oscillation (f : ℝ → ℝ) (B : ℝ) := ∀ t : ℝ, ∀ ε > 0, ∃ u v : ℝ,
  dist u t < ε ∧ dist v t < ε ∧ B ≤ f v-f u

private theorem dense_oscillation {f : ℝ → ℝ} {B : ℝ}
    (zero : ∀ u ∉ exceptional, f u = 0) (hit : ∀ v, rejected v primeVacuum → B ≤ f v) :
    Oscillation f B := by
  intro t ε hε
  obtain ⟨u,hu,hout⟩ := Metric.dense_iff.mp (exceptional_countable.dense_compl ℝ) t ε hε
  obtain ⟨v,hv,hin⟩ := Metric.dense_iff.mp prime_vacuum_dense t ε hε
  exact ⟨u,v,hu,hv,by rw [zero u hout,sub_zero]; exact hit v hin⟩

theorem Oscillation.discontinuous {f : ℝ → ℝ} {B : ℝ} (h : Oscillation f B) (hp : 0 < B) (t : ℝ) :
    ¬ContinuousAt f t := by
  intro hc
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc (B/2) (half_pos hp)
  obtain ⟨u,v,hu,hv,hgap⟩ := h t δ hδ
  have h₁ := hclose hu
  have h₂ := hclose hv
  rw [Real.dist_eq,abs_lt] at h₁ h₂
  linarith only [h₁.1,h₂.2,hgap]

/-- Rejection projection measured in the normalized one-quantum state at prime two. -/
def primeReading (t : ℝ) : ℝ :=
  (HTGeometry.lpCoordinateProjection {x | rejected t x} (lp.single 2 primeVacuum (1:ℂ)) primeVacuum).re

private theorem prime_reading_eq (t : ℝ) : primeReading t = if rejected t primeVacuum then 1 else 0 := by
  by_cases hx : rejected t primeVacuum <;> simp [primeReading,hx]

theorem prime_reading_oscillation : Oscillation primeReading 1 := by
  apply dense_oscillation
  · intro u hu
    exact (prime_reading_eq u).trans (if_neg fun h => hu ⟨primeVacuum,h⟩)
  · intro v hv
    rw [prime_reading_eq,if_pos hv]

private theorem real_weight (β : ℝ) (x : Word) : (wordHeat (β:ℂ) x).re =
    Real.exp (-β*energy (∏ b, x b)) := by
  rw [wordHeat_total,heat,← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp,Complex.ofReal_re]

/-- Gibbs weight of the pair (2,1) bounds the rejected operator trace on a dense set. -/
theorem loss_oscillation (β : {β : ℝ // 1/2 < β}) :
    Oscillation (fun t => (correction t (β.val:ℂ)).re) (Real.exp (-β.val*Real.log 2)) := by
  apply dense_oscillation
  · intro u hu
    letI : IsEmpty {x // rejected u x} := ⟨fun x => hu ⟨x.val,x.property⟩⟩
    simp [correction,partition]
  · intro v hv
    have hs := (sectorHeat_iff _ _).mp ((rejected_heat_iff v (β.val:ℂ)).mpr fun _ => β.property)
    have hr : HasSum (fun i : {x // rejected v x} => (wordHeat (β.val:ℂ) i.val).re)
        (correction v (β.val:ℂ)).re := Complex.hasSum_re hs.of_norm.hasSum
    have hw := hr.summable.le_tsum (⟨primeVacuum,hv⟩ : {x // rejected v x})
      (fun i _ => (Real.exp_pos _).le.trans_eq (real_weight β.val i.val).symm)
    have he : energy (∏ b : Bool, primeVacuum b) = Real.log 2 := by norm_num [Fintype.prod_bool,primeVacuum,energy]
    rw [hr.tsum_eq] at hw
    exact (show Real.exp (-β.val*Real.log 2) = (wordHeat (β.val:ℂ) primeVacuum).re by rw [real_weight,he]).trans_le hw

/-- Real reading of the accepted trace-class heat operator. -/
def thermalReading (β : {β : ℝ // 1 < β}) (t : ℝ) : ℝ :=
  (ContinuousLinearMap.opTrace (sectorHeat (measured t Real.pi)
    ⟨(β.val:ℂ),(sectorHeat_iff _ _).mp ((maximal_heat_iff t _).mpr β.property)⟩)).re

private theorem thermal_reading_eq (β : {β : ℝ // 1 < β}) (t : ℝ) :
    thermalReading β t = (riemannZeta (β.val:ℂ)^2).re-(correction t (β.val:ℂ)).re :=
  congrArg Complex.re (maximal_trace t ⟨(β.val:ℂ),(sectorHeat_iff _ _).mp ((maximal_heat_iff t _).mpr β.property)⟩)

/-- The accepted thermal trace retains at least the prime weight of oscillation in every neighborhood. -/
theorem thermal_oscillation (β : {β : ℝ // 1 < β}) :
    Oscillation (thermalReading β) (Real.exp (-β.val*Real.log 2)) := by
  intro t ε hε
  obtain ⟨u,v,hu,hv,h⟩ := loss_oscillation ⟨β.val,by linarith only [β.property]⟩ t ε hε
  refine ⟨v,u,hv,hu,?_⟩
  change Real.exp (-β.val*Real.log 2) ≤ (correction v (β.val:ℂ)).re - (correction u (β.val:ℂ)).re at h
  rw [thermal_reading_eq,thermal_reading_eq]
  linarith only [h]

theorem thermal_nowhere_continuous (β : {β : ℝ // 1 < β}) (t : ℝ) : ¬ContinuousAt (thermalReading β) t :=
  (thermal_oscillation β).discontinuous (Real.exp_pos _) t

#print axioms prime_reading_oscillation
#print axioms loss_oscillation
#print axioms thermal_oscillation
#print axioms thermal_nowhere_continuous

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary
