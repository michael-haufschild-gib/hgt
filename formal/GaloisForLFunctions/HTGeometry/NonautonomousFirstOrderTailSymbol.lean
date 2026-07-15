import GaloisForLFunctions.HTGeometry.NonautonomousStableCore
import Mathlib.Data.Nat.Log

/-!
# Tensor symbols and finite defect budgets for first-order tails

A rational `k`-differential evaluated on a scalar jet has the form `q(y) (δy)^k`.  The first
theorems certify that pullback of the tensor coefficient and the first-jet chain rule transport
this observable exactly, including negative tensor weights.

The remaining theorems isolate the multiplicity mechanism behind the finite-transient law.  A
terminal zero of multiplicity `m` pulls back over a degree-`D` fiber with total multiplicity at
least `D m`.  Hence a fixed initial zero budget forces every sufficiently deep defect count to
vanish when prefix degrees grow at least exponentially.  These are static constraint depths, not
times of a continuous evolution.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Evaluation of a rational tensor coefficient on a scalar first jet.  Integer powers allow
covariant tensors and their contravariant reciprocals in one definition. -/
def tensorJetObservable {K : Type*} [Field K]
    (q : K → K) (weight : ℤ) (y dy : K) : K :=
  q y * dy ^ weight

/-- Exact first-jet transport of a tensor observable. -/
theorem tensorJetObservable_transport {K : Type*} [Field K]
    (q₀ q₁ R dR : K → K) (weight : ℤ) (y dy : K)
    (hsymbol : q₀ y = q₁ (R y) * dR y ^ weight) :
    tensorJetObservable q₁ weight (R y) (dR y * dy) =
      tensorJetObservable q₀ weight y dy := by
  simp only [tensorJetObservable, mul_zpow]
  rw [← mul_assoc, hsymbol]

/-- Tensor-symbol transport composes exactly through two constraint layers. -/
theorem tensorSymbol_transport_comp {K : Type*} [Field K]
    (q₀ q₁ q₂ R S dR dS : K → K) (weight : ℤ) (y : K)
    (h₀₁ : q₀ y = q₁ (R y) * dR y ^ weight)
    (h₁₂ : q₁ (R y) = q₂ (S (R y)) * dS (R y) ^ weight) :
    q₀ y = q₂ (S (R y)) * (dS (R y) * dR y) ^ weight := by
  rw [h₀₁, h₁₂, mul_zpow]
  ring

/-- A zero of multiplicity `m` on a terminal tensor contributes at least `e*m` at a point of
ramification index `e` in the pullback fiber.  Summed over a degree-`D` fiber, its contribution is
at least `D*m`. -/
theorem pullbackZeroMultiplicity_fiber
    {α : Type*} (fiber : Finset α) (ramification sourceMultiplicity : α → ℕ)
    (terminalMultiplicity degree : ℕ)
    (hdegree : ∑ x ∈ fiber, ramification x = degree)
    (hlocal : ∀ x ∈ fiber,
      ramification x * terminalMultiplicity ≤ sourceMultiplicity x) :
    degree * terminalMultiplicity ≤
      ∑ x ∈ fiber, sourceMultiplicity x := by
  calc
    degree * terminalMultiplicity =
        (∑ x ∈ fiber, ramification x) * terminalMultiplicity := by rw [hdegree]
    _ = ∑ x ∈ fiber, ramification x * terminalMultiplicity := by
      rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ fiber, sourceMultiplicity x := by
      exact Finset.sum_le_sum fun x hx => hlocal x hx

/-- If a degree-amplified future defect fits inside the initial budget and the degree already
exceeds that budget, the future defect is zero. -/
theorem futureTensorDefect_eq_zero_of_degree_gt
    (initialDefect futureDefect degree : ℕ)
    (hamplified : degree * futureDefect ≤ initialDefect)
    (hdegree : initialDefect < degree) :
    futureDefect = 0 := by
  by_contra hfuture
  have hpos : 0 < futureDefect := Nat.pos_of_ne_zero hfuture
  have hle : degree ≤ degree * futureDefect :=
    Nat.le_mul_of_pos_right degree hpos
  exact (Nat.not_le_of_lt hdegree) (hle.trans hamplified)

/-- Quantitative finite-transient law: if prefix degree dominates `2^n`, every defect after the
binary logarithmic budget is zero. -/
theorem tensorDefect_eq_zero_after_log
    (defect prefixDegree : ℕ → ℕ)
    (hamplified : ∀ n, prefixDegree n * defect n ≤ defect 0)
    (hdegree : ∀ n, 2 ^ n ≤ prefixDegree n)
    {n : ℕ} (hn : Nat.log 2 (defect 0) < n) :
    defect n = 0 := by
  apply futureTensorDefect_eq_zero_of_degree_gt
    (defect 0) (defect n) (prefixDegree n) (hamplified n)
  exact (Nat.lt_pow_of_log_lt Nat.one_lt_two hn).trans_le (hdegree n)

/-- Exponential prefix degree and multiplicative pullback of defects force the defect sequence to
vanish eventually. -/
theorem tensorDefect_eventually_zero
    (defect prefixDegree : ℕ → ℕ)
    (hamplified : ∀ n, prefixDegree n * defect n ≤ defect 0)
    (hdegree : ∀ n, 2 ^ n ≤ prefixDegree n) :
    ∀ᶠ n in Filter.atTop, defect n = 0 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (defect 0) Nat.one_lt_two
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  apply futureTensorDefect_eq_zero_of_degree_gt
    (defect 0) (defect n) (prefixDegree n) (hamplified n)
  exact hN.trans_le <| (Nat.pow_le_pow_right (by omega) hn).trans (hdegree n)

/-- If a terminal shifted tensor order does not divide the regular source order, none of its
preimages can be a regular source point.  The whole fiber is forced into the finite exceptional
divisor. -/
theorem tensorFiber_subset_exceptional_of_not_dvd
    {α : Type*} (fiber exceptional : Finset α)
    (ramification sourceAngle : α → ℕ) (regularAngle terminalAngle : ℕ)
    (hregular : ∀ x ∈ fiber, x ∉ exceptional → sourceAngle x = regularAngle)
    (htransport : ∀ x ∈ fiber,
      sourceAngle x = ramification x * terminalAngle)
    (hnotdvd : ¬ terminalAngle ∣ regularAngle) :
    fiber ⊆ exceptional := by
  intro x hx
  by_contra hxe
  apply hnotdvd
  refine ⟨ramification x, ?_⟩
  calc
    regularAngle = sourceAngle x := (hregular x hx hxe).symm
    _ = ramification x * terminalAngle := htransport x hx
    _ = terminalAngle * ramification x := Nat.mul_comm _ _

/-- If a full degree fiber is trapped in a finite exceptional divisor and shifted tensor orders
multiply by ramification, the covering degree is bounded by the exceptional angle budget. -/
theorem tensorFiber_degree_le_exceptionalBudget
    {α : Type*} (fiber exceptional : Finset α)
    (ramification sourceAngle : α → ℕ) (terminalAngle degree budget : ℕ)
    (hsubset : fiber ⊆ exceptional)
    (hdegree : ∑ x ∈ fiber, ramification x = degree)
    (htransport : ∀ x ∈ fiber,
      sourceAngle x = ramification x * terminalAngle)
    (hbudget : ∑ x ∈ exceptional, sourceAngle x ≤ budget)
    (hterminal : 0 < terminalAngle) :
    degree ≤ budget := by
  have hsum : ∑ x ∈ fiber, sourceAngle x ≤
      ∑ x ∈ exceptional, sourceAngle x :=
    Finset.sum_le_sum_of_subset hsubset
  have hdegreeAngle : degree * terminalAngle =
      ∑ x ∈ fiber, sourceAngle x := by
    calc
      degree * terminalAngle =
          (∑ x ∈ fiber, ramification x) * terminalAngle := by rw [hdegree]
      _ = ∑ x ∈ fiber, ramification x * terminalAngle := by
        rw [Finset.sum_mul]
      _ = ∑ x ∈ fiber, sourceAngle x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (htransport x hx).symm
  have hamplified : degree * terminalAngle ≤ budget := by
    rw [hdegreeAngle]
    exact hsum.trans hbudget
  exact (Nat.le_mul_of_pos_right degree hterminal).trans hamplified

/-- **Angle quantization by expansion.**  Once the covering degree exceeds the entire exceptional
source-angle budget, every positive terminal angle must divide the regular angle.  This is the
finite combinatorial core that turns rational cone weights into integral orbifold weights. -/
theorem terminalTensorAngle_dvd_of_exceptionalBudget_lt_degree
    {α : Type*} (fiber exceptional : Finset α)
    (ramification sourceAngle : α → ℕ) (regularAngle terminalAngle degree budget : ℕ)
    (hregular : ∀ x ∈ fiber, x ∉ exceptional → sourceAngle x = regularAngle)
    (hdegree : ∑ x ∈ fiber, ramification x = degree)
    (htransport : ∀ x ∈ fiber,
      sourceAngle x = ramification x * terminalAngle)
    (hbudget : ∑ x ∈ exceptional, sourceAngle x ≤ budget)
    (hterminal : 0 < terminalAngle)
    (hexpanding : budget < degree) :
    terminalAngle ∣ regularAngle := by
  by_contra hnotdvd
  have hsubset : fiber ⊆ exceptional :=
    tensorFiber_subset_exceptional_of_not_dvd fiber exceptional
      ramification sourceAngle regularAngle terminalAngle hregular htransport hnotdvd
  have hdegree_le : degree ≤ budget :=
    tensorFiber_degree_le_exceptionalBudget fiber exceptional
      ramification sourceAngle terminalAngle degree budget hsubset hdegree
      htransport hbudget hterminal
  exact (Nat.not_le_of_lt hexpanding) hdegree_le

end GaloisForLFunctions.HTGeometry
