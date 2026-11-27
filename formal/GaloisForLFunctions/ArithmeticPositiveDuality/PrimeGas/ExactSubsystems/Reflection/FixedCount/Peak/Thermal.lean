import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-! # Largest Gibbs weights under reflection of inverse temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak

open Finset Real _root_.HTGeometry

variable {X : Type*} [Fintype X]

/-- Largest normalized weight, independent of the names of the energy levels. -/
def largest (E : X → ℝ) (b : ℝ) := sSup (Set.range (finiteGibbsStateWeight b E))

/-- Partition measured from the energy of one specified state. -/
def relativeZ (E : X → ℝ) (b : ℝ) (u : X) := ∑ x, exp (-b*(E x-E u))

theorem relativeZ_pos (E : X → ℝ) (b : ℝ) (u : X) : 0 < relativeZ E b u :=
  sum_pos (fun _ _ => exp_pos _) ⟨u, mem_univ u⟩

theorem weight_eq_inv (E : X → ℝ) (b : ℝ) (u : X) :
    finiteGibbsStateWeight b E u = (relativeZ E b u)⁻¹ := by
  have h : relativeZ E b u = finiteGibbsPartition b E / exp (-b*E u) := by
    rw [relativeZ, finiteGibbsPartition, sum_div]
    exact sum_congr rfl fun x _ => by rw [← exp_sub]; congr 1; ring
  rw [h, finiteGibbsStateWeight, inv_div]

theorem largest_at {E : X → ℝ} {b : ℝ} (u : X) (h : ∀ x, b*E u ≤ b*E x) :
    largest E b = (relativeZ E b u)⁻¹ := by
  letI : Nonempty X := ⟨u⟩
  have hg : IsGreatest (Set.range (finiteGibbsStateWeight b E)) (finiteGibbsStateWeight b E u) := by
    refine ⟨⟨u, rfl⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact div_le_div_of_nonneg_right (exp_le_exp.mpr (by linarith only [h x] : -b*E x ≤ -b*E u))
      (finiteGibbsPartition_pos b E).le
  exact hg.csSup_eq.trans (weight_eq_inv E b u)

theorem largest_neg_energy (E : X → ℝ) (b : ℝ) : largest (fun x => -E x) b = largest E (-b) := by
  apply congrArg (fun f : X → ℝ => sSup (Set.range f))
  funext x
  simp only [finiteGibbsStateWeight, finiteGibbsPartition, mul_neg, neg_mul, neg_neg]

/-- A one-sided pairing, strict at one state, orders the two largest probabilities. -/
theorem strict_peak_above {E : X → ℝ} {b : ℝ} (hb : 0 < b) (u v : X)
    (hu : ∀ x, E u ≤ E x) (hv : ∀ x, E x ≤ E v) (R : Equiv.Perm X)
    (h : ∀ x, E u + E v ≤ E x + E (R x)) (hstrict : ∃ x, E u + E v < E x + E (R x)) :
    largest E (-b) < largest E b := by
  have lew (x : X) : exp (-b*(E x-E u)) ≤ exp (-(-b)*(E (R x)-E v)) := by
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr (h x))]
  obtain ⟨x, hx⟩ := hstrict
  have ltw : exp (-b*(E x-E u)) < exp (-(-b)*(E (R x)-E v)) := by
    apply exp_lt_exp.mpr
    nlinarith only [mul_pos hb (sub_pos.mpr hx)]
  have cmp : relativeZ E b u < relativeZ E (-b) v := by
    calc _ < ∑ y, exp (-(-b)*(E (R y)-E v)) := sum_lt_sum (fun y _ => lew y) ⟨x, mem_univ x, ltw⟩
         _ = _ := Equiv.sum_comp R (fun y => exp (-(-b)*(E y-E v)))
  rw [largest_at v (fun y => mul_le_mul_of_nonpos_left (hv y) (neg_nonpos.mpr hb.le)),
    largest_at u (fun y => mul_le_mul_of_nonneg_left (hu y) hb.le)]
  exact (inv_lt_inv₀ (relativeZ_pos E (-b) v) (relativeZ_pos E b u)).mpr cmp

theorem strict_peak_below {E : X → ℝ} {b : ℝ} (hb : 0 < b) (u v : X)
    (hu : ∀ x, E u ≤ E x) (hv : ∀ x, E x ≤ E v) (R : Equiv.Perm X)
    (h : ∀ x, E x + E (R x) ≤ E u + E v) (hstrict : ∃ x, E x + E (R x) < E u + E v) :
    largest E b < largest E (-b) := by
  obtain ⟨z,hz⟩ := hstrict
  have hh := strict_peak_above (E := fun x => -E x) hb v u (fun x => neg_le_neg (hv x))
    (fun x => neg_le_neg (hu x)) R (fun x => by linarith only [h x])
    ⟨z, by linarith only [hz]⟩
  simpa only [largest_neg_energy, neg_neg] using hh

#print axioms largest_at
#print axioms strict_peak_above
#print axioms strict_peak_below

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak
