import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheThresholdIsThePriceOfTheArchimedeanLine

/-!
# Near-incidences of products are successor correlations

The elementary relations of the field are `ab = cd` and `ab − cd = h`. For a box `s` of integers
with weights `α`, the **fourfold incidence** `I_h = Σ_{ab = cd + h} α_a α_b \overline{α_c α_d}`
(`fourfoldIncidence`) is the shift-`h` successor correlation of the product source
`r(N) = Σ_{ab = N} α_a α_b` (`fourfoldIncidence_eq`). So the relation `ab − cd = h` is read by
the gauge calculus of `SuccessorCorrelationsArePureGaugeCharge` applied to `r`:

* at `h = 0` it is the multiplicative energy `Σ_N |r(N)|²`, gauge invariant
  (`fourfoldIncidence_zero`);
* for `h ≠ 0` the twisted incidence has gauge mean zero (`integral_fourfoldIncidence_twisted`) and
  gauge mean square `Σ_N |r(N)|² |r(N+h)|²` (`integral_normSq_fourfoldIncidence_twisted`).

The multiplicative energy is the gauge-invariant shadow of the family `{I_h}`; every near-incidence
`h ≠ 0` is gauge charge, with square-root-size fluctuation over the orbit. Bounding `I_h` for the
actual weights (divisor, Möbius, von Mangoldt) is an additive-divisor problem: arithmetic of one
gauge point.
-/

open MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry ArithmeticKunnethTheory

/-- The pairs `(a, b)` of the box, as functions `Fin 2 → ℕ`. -/
abbrev boxPairs (s : Finset ℕ) : Finset (Fin 2 → ℕ) := Fintype.piFinset fun _ : Fin 2 => s

/-- **The fourfold incidence** `Σ_{ab = cd + h} α_a α_b \overline{α_c α_d}` over the box. -/
def fourfoldIncidence (s : Finset ℕ) (α : ℕ → ℂ) (h : ℕ) : ℂ :=
  ∑ t ∈ boxPairs s, ∑ u ∈ boxPairs s,
    if t 0 * t 1 = u 0 * u 1 + h then α (t 0) * α (t 1) * conj (α (u 0) * α (u 1)) else 0

theorem powCoeff_two_eq (s : Finset ℕ) (α : ℕ → ℂ) (N : ℕ) :
    powCoeff s α 2 N = ∑ t ∈ boxPairs s, if t 0 * t 1 = N then α (t 0) * α (t 1) else 0 := by
  rw [powCoeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Fin.prod_univ_two]

theorem powCoeff_eq_zero_of_not_mem {s : Finset ℕ} {α : ℕ → ℂ} {k N : ℕ}
    (hN : N ∉ ArithmeticKunnethTheory.powSupport s k) : powCoeff s α k N = 0 := by
  rw [powCoeff]
  refine Finset.sum_eq_zero fun t ht => absurd ?_ hN
  obtain ⟨ht, hprod⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_image.mpr ⟨t, ht, hprod⟩

/-- **The fourfold incidence is a successor correlation of the product source.** -/
theorem fourfoldIncidence_eq (s : Finset ℕ) (α : ℕ → ℂ) (h : ℕ) :
    fourfoldIncidence s α h =
      ∑ N ∈ ArithmeticKunnethTheory.powSupport s 2, powCoeff s α 2 (N + h) * conj (powCoeff s α 2 N) := by
  classical
  have hfib : ∀ u ∈ boxPairs s, ∀ t : Fin 2 → ℕ,
      (∑ N ∈ ArithmeticKunnethTheory.powSupport s 2,
        (if t 0 * t 1 = N + h then α (t 0) * α (t 1) else 0) *
          conj (if u 0 * u 1 = N then α (u 0) * α (u 1) else 0)) =
      if t 0 * t 1 = u 0 * u 1 + h then α (t 0) * α (t 1) * conj (α (u 0) * α (u 1)) else 0 := by
    intro u hu t
    have hmem : u 0 * u 1 ∈ ArithmeticKunnethTheory.powSupport s 2 :=
      Finset.mem_image.mpr ⟨u, hu, by simp [Fin.prod_univ_two]⟩
    rw [Finset.sum_eq_single (u 0 * u 1)]
    · rw [if_pos rfl]
      split_ifs <;> simp
    · intro N _ hN
      rw [if_neg (fun e => hN e.symm), map_zero, mul_zero]
    · exact fun h' => absurd hmem h'
  rw [fourfoldIncidence]
  simp_rw [powCoeff_two_eq, map_sum, Finset.sum_mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u hu => hfib u hu t

/-- At `h = 0` the fourfold incidence is the multiplicative energy. -/
theorem fourfoldIncidence_zero (s : Finset ℕ) (α : ℕ → ℂ) :
    fourfoldIncidence s α 0 =
      ∑ N ∈ ArithmeticKunnethTheory.powSupport s 2, ((‖powCoeff s α 2 N‖ ^ 2 : ℝ) : ℂ) := by
  rw [fourfoldIncidence_eq]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [add_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- The fourfold incidence written as a conjugated successor correlation. -/
theorem fourfoldIncidence_eq_conj_succCorr (s : Finset ℕ) (α : ℕ → ℂ) (h : ℕ) :
    fourfoldIncidence s α h =
      conj (succCorr (ArithmeticKunnethTheory.powSupport s 2) h (powCoeff s α 2)) := by
  rw [fourfoldIncidence_eq, succCorr, map_sum]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- **The near-incidence `ab − cd = h ≠ 0` is gauge charged.** -/
theorem integral_fourfoldIncidence_twisted {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {h : ℕ}
    (hh : h ≠ 0) (α : ℕ → ℂ) :
    ∫ y, fourfoldIncidence s (twisted y α) h ∂gaugeHaar = 0 := by
  have htw : ∀ y, powCoeff s (twisted y α) 2 = twisted y (powCoeff s α 2) := fun y =>
    funext fun N => powCoeff_twisted hs y α 2 N
  simp_rw [fourfoldIncidence_eq_conj_succCorr, htw]
  rw [integral_conj, integral_succCorr_twisted (fun N hN => ne_zero_of_mem_powSupport hs hN) hh,
    map_zero]

/-- **Its gauge mean square is `Σ_N |r(N)|² |r(N+h)|²`.** -/
theorem integral_normSq_fourfoldIncidence_twisted {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {h : ℕ}
    (hh : h ≠ 0) (α : ℕ → ℂ) :
    ∫ y, ‖fourfoldIncidence s (twisted y α) h‖ ^ 2 ∂gaugeHaar =
      ∑ N ∈ ArithmeticKunnethTheory.powSupport s 2,
        ‖powCoeff s α 2 N‖ ^ 2 * ‖powCoeff s α 2 (N + h)‖ ^ 2 := by
  have htw : ∀ y, powCoeff s (twisted y α) 2 = twisted y (powCoeff s α 2) := fun y =>
    funext fun N => powCoeff_twisted hs y α 2 N
  simp_rw [fourfoldIncidence_eq_conj_succCorr, htw, RCLike.norm_conj]
  exact integral_normSq_succCorr_twisted (fun N hN => ne_zero_of_mem_powSupport hs hN) hh _

end GaloisForLFunctions.ArithmeticCorrelationGeometry
