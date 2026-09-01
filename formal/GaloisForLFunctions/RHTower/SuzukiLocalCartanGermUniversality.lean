import GaloisForLFunctions.RHTower.SuzukiNonabelianCartanWardCofinalEquivalence

/-!
# Universality of fixed local Suzuki Cartan germs

The literal opposite-root `SL₂` construction uses `log (1+x)` in each source-labelled Levi
coordinate.  This module classifies every fixed replacement with the same forced first two jets:

`phi(x) = x - x^2/2 + O(x^3)`.

The assembled cubic remainder is at most `O(log(A)^3/sqrt(A))`, hence vanishes cofinally.  After
the forced quadratic counterterm, every such completed observable is Suzuki Green plus `o(1)`.
Its uniform boundedness is therefore equivalent to RH.  This kills the whole fixed local analytic
Cartan/Stokes-fusion producer class: any surviving coercive mechanism must couple source labels
nonlocally or depend genuinely on the cutoff before scalar/cofinal passage.
-/

open Complex Filter Function Set Topology
open scoped Topology BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

/-- Remainder after the forced coefficient-faithful linear and quadratic Cartan jets. -/
def suzukiLocalCartanGermRemainder (phi : ℝ → ℝ) (x : ℝ) : ℝ :=
  phi x - x + x ^ 2 / 2

/-- A fixed local Cartan germ agrees with `x - x²/2` through second order and has a
uniform cubic remainder on the positive source cone. -/
def SuzukiLocalCartanGermCubicControlled (phi : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
    |suzukiLocalCartanGermRemainder phi x| ≤ C * x ^ 3

/-- Aggregate local-germ remainder over one natural Suzuki source aperture. -/
def suzukiLocalCartanGermRemainderMass (phi : ℝ → ℝ) (A : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 A,
    suzukiLocalCartanGermRemainder phi (suzukiCenterStokesCartanCell A n)

/-- Completed local-germ observable with forced quadratic counterterm and literal regular-screw
subtraction. -/
def suzukiLocalCartanGermWardObservable (phi : ℝ → ℝ) (A : ℕ) : ℝ :=
  2 * (∑ n ∈ Finset.Icc 2 A, phi (suzukiCenterStokesCartanCell A n)) +
    suzukiStokesCartanQuadraticCounterterm A -
      suzukiUnitRieszRegularWardMass (Real.log A)

/-- Uniform boundedness of a fixed local-germ completed observable. -/
def SuzukiLocalCartanGermWardObservableBounded (phi : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
    |suzukiLocalCartanGermWardObservable phi (N + 2)| ≤ B

/-- Exact endpoint identity: every local-germ observable is Suzuki Green plus its aggregate
third-order remainder. -/
theorem suzukiLocalCartanGermWardObservable_eq_green_add_remainder
    (phi : ℝ → ℝ) (N : ℕ) :
    suzukiLocalCartanGermWardObservable phi (N + 2) =
      unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) +
        2 * suzukiLocalCartanGermRemainderMass phi (N + 2) := by
  rw [suzukiLocalCartanGermWardObservable,
    suzukiLocalCartanGermRemainderMass,
    unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
  have hlinear :=
    suzukiStokesCartanLinearMass_eq_primeOutgoingCharge_half
      (by omega : 2 ≤ N + 2)
  have hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 2) =
      2 * suzukiStokesCartanLinearMass (N + 2) := by
    linarith
  rw [hcharge]
  unfold suzukiStokesCartanLinearMass suzukiStokesCartanQuadraticCounterterm
    suzukiLocalCartanGermRemainder
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

/-- Cubic mass of all source-labelled Cartan cells has the sharp aperture scale needed for
cofinal vanishing. -/
theorem sum_suzukiCenterStokesCartanCell_cube_le
    {A : ℕ} (hA : 2 ≤ A) :
    (∑ n ∈ Finset.Icc 2 A, suzukiCenterStokesCartanCell A n ^ 3) ≤
      Real.log A ^ 3 / (8 * Real.sqrt A) := by
  have hA0 : (0 : ℝ) < A := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
  have hsqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.2 hA0
  have hlog : 0 ≤ Real.log A := Real.log_nonneg (by
    exact_mod_cast (by omega : 1 ≤ A))
  have hcard : (Finset.Icc 2 A).card ≤ A := by
    simp only [Nat.card_Icc]
    omega
  calc
    (∑ n ∈ Finset.Icc 2 A, suzukiCenterStokesCartanCell A n ^ 3) ≤
        ∑ _n ∈ Finset.Icc 2 A,
          (Real.log A / (2 * Real.sqrt A)) ^ 3 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (suzukiCenterStokesCartanCell_nonneg hA hn)
        (suzukiCenterStokesCartanCell_le hA hn) 3
    _ = ((Finset.Icc 2 A).card : ℝ) *
        (Real.log A / (2 * Real.sqrt A)) ^ 3 := by simp
    _ ≤ (A : ℝ) * (Real.log A / (2 * Real.sqrt A)) ^ 3 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = Real.log A ^ 3 / (8 * Real.sqrt A) := by
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hA0.le]
      ring

/-- Aggregate remainder bound for every cubic-controlled fixed local germ. -/
theorem abs_suzukiLocalCartanGermRemainderMass_le
    {phi : ℝ → ℝ} (hphi : SuzukiLocalCartanGermCubicControlled phi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, 2 ≤ A →
      |suzukiLocalCartanGermRemainderMass phi A| ≤
        C * (Real.log A ^ 3 / (8 * Real.sqrt A)) := by
  obtain ⟨C, hC, hbound⟩ := hphi
  refine ⟨C, hC, ?_⟩
  intro A hA
  calc
    |suzukiLocalCartanGermRemainderMass phi A| ≤
        ∑ n ∈ Finset.Icc 2 A,
          |suzukiLocalCartanGermRemainder phi
            (suzukiCenterStokesCartanCell A n)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 A,
        C * suzukiCenterStokesCartanCell A n ^ 3 := by
      apply Finset.sum_le_sum
      intro n hn
      exact hbound _ (suzukiCenterStokesCartanCell_nonneg hA hn)
    _ = C * (∑ n ∈ Finset.Icc 2 A,
        suzukiCenterStokesCartanCell A n ^ 3) := by
      rw [Finset.mul_sum]
    _ ≤ C * (Real.log A ^ 3 / (8 * Real.sqrt A)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_suzukiCenterStokesCartanCell_cube_le hA) hC

/-- Every cubic-controlled local Cartan correction vanishes after cofinal source assembly. -/
theorem tendsto_suzukiLocalCartanGermRemainderMass
    {phi : ℝ → ℝ} (hphi : SuzukiLocalCartanGermCubicControlled phi) :
    Tendsto (fun N : ℕ => suzukiLocalCartanGermRemainderMass phi (N + 2))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := abs_suzukiLocalCartanGermRemainderMass_le hphi
  have hbase : Tendsto
      (fun N : ℕ => Real.log ((N + 2 : ℕ) : ℝ) ^ 3 /
        (24 * Real.sqrt ((N + 2 : ℕ) : ℝ))) atTop (𝓝 0) :=
    tendsto_suzukiStokesCartanCubicMajorant.comp (tendsto_add_atTop_nat 2)
  have hmajor : Tendsto
      (fun N : ℕ => C * (Real.log ((N + 2 : ℕ) : ℝ) ^ 3 /
        (8 * Real.sqrt ((N + 2 : ℕ) : ℝ)))) atTop (𝓝 0) := by
    have hscaled := hbase.const_mul (3 * C)
    convert hscaled using 1
    · funext N
      ring
    · norm_num
  have hneg : Tendsto
      (fun N : ℕ => -(C * (Real.log ((N + 2 : ℕ) : ℝ) ^ 3 /
        (8 * Real.sqrt ((N + 2 : ℕ) : ℝ))))) atTop (𝓝 0) := by
    simpa using hmajor.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg hmajor
    (fun N => neg_le_of_abs_le (hbound (N + 2) (by omega)))
    (fun N => le_of_abs_le (hbound (N + 2) (by omega)))

/-- Cubic control gives a uniform aperture bound, not merely a cofinal limit. -/
theorem exists_uniform_bound_abs_suzukiLocalCartanGermRemainderMass
    {phi : ℝ → ℝ} (hphi : SuzukiLocalCartanGermCubicControlled phi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℕ, 2 ≤ A →
      |suzukiLocalCartanGermRemainderMass phi A| ≤ K := by
  obtain ⟨C, hC, hbound⟩ := abs_suzukiLocalCartanGermRemainderMass_le hphi
  obtain ⟨D, hD, hlogD⟩ :=
    exists_const_log_pow_le_rpow 3 (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨C * D / 8, by positivity, ?_⟩
  intro A hA
  have hA0 : (0 : ℝ) < A := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
  have hsqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.2 hA0
  have hpow := hlogD A (by omega : 1 ≤ A)
  have hrpow : (A : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt A := by
    rw [Real.sqrt_eq_rpow]
  rw [hrpow] at hpow
  have hratio : Real.log A ^ 3 / Real.sqrt A ≤ D := by
    exact (div_le_iff₀ hsqrt).2 (by simpa [mul_comm] using hpow)
  calc
    |suzukiLocalCartanGermRemainderMass phi A| ≤
        C * (Real.log A ^ 3 / (8 * Real.sqrt A)) := hbound A hA
    _ = (C / 8) * (Real.log A ^ 3 / Real.sqrt A) := by ring
    _ ≤ (C / 8) * D := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = C * D / 8 := by ring

/-- Uniform boundedness of any fixed cubic-controlled local Cartan germ is exactly boundedness of
the literal atomic--continuous Suzuki endpoint. -/
theorem suzukiLocalCartanGermWardObservableBounded_iff_atomicContinuous
    {phi : ℝ → ℝ} (hphi : SuzukiLocalCartanGermCubicControlled phi) :
    SuzukiLocalCartanGermWardObservableBounded phi ↔
      SuzukiWardAtomicContinuousImbalanceBounded := by
  obtain ⟨K, hK, hrem⟩ :=
    exists_uniform_bound_abs_suzukiLocalCartanGermRemainderMass hphi
  constructor
  · rintro ⟨B, hB, hobs⟩
    refine ⟨B + 2 * K, by positivity, fun N => ?_⟩
    rw [← unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
    have hid := suzukiLocalCartanGermWardObservable_eq_green_add_remainder phi N
    have hrewrite : unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) =
        suzukiLocalCartanGermWardObservable phi (N + 2) -
          2 * suzukiLocalCartanGermRemainderMass phi (N + 2) := by
      linarith
    rw [hrewrite]
    calc
      |suzukiLocalCartanGermWardObservable phi (N + 2) -
          2 * suzukiLocalCartanGermRemainderMass phi (N + 2)| ≤
          |suzukiLocalCartanGermWardObservable phi (N + 2)| +
            |2 * suzukiLocalCartanGermRemainderMass phi (N + 2)| := abs_sub _ _
      _ ≤ B + 2 * K := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [hobs N, hrem (N + 2) (by omega : 2 ≤ N + 2)]
  · rintro ⟨B, hB, hgreen⟩
    refine ⟨B + 2 * K, by positivity, fun N => ?_⟩
    rw [suzukiLocalCartanGermWardObservable_eq_green_add_remainder]
    calc
      |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) +
          2 * suzukiLocalCartanGermRemainderMass phi (N + 2)| ≤
          |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ))| +
            |2 * suzukiLocalCartanGermRemainderMass phi (N + 2)| := abs_add_le _ _
      _ ≤ B + 2 * K := by
        have hgreen' :
            |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ))| ≤ B := by
          rw [unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
          exact hgreen N
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [hgreen', hrem (N + 2) (by omega : 2 ≤ N + 2)]

/-- Local Cartan-germ universality: every fixed coefficient-faithful cubic-controlled Stokes germ
has bounded completed observable exactly under RH. -/
theorem riemannHypothesis_iff_suzukiLocalCartanGermWardObservableBounded
    {phi : ℝ → ℝ} (hphi : SuzukiLocalCartanGermCubicControlled phi) :
    RiemannHypothesis ↔ SuzukiLocalCartanGermWardObservableBounded phi := by
  rw [riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded]
  exact (suzukiLocalCartanGermWardObservableBounded_iff_atomicContinuous hphi).symm

/-- Closed producer-class kill: no cubic-controlled fixed local Cartan germ can make boundedness
easier than the original RH-equivalent Suzuki Green endpoint. -/
theorem all_suzukiLocalCartanGermWardObservables_bounded_iff_riemannHypothesis :
    (∀ phi : ℝ → ℝ, SuzukiLocalCartanGermCubicControlled phi →
      SuzukiLocalCartanGermWardObservableBounded phi) ↔ RiemannHypothesis := by
  constructor
  · intro hall
    let phi : ℝ → ℝ := fun x => x - x ^ 2 / 2
    have hphi : SuzukiLocalCartanGermCubicControlled phi := by
      refine ⟨0, le_rfl, ?_⟩
      intro x hx
      simp [phi, suzukiLocalCartanGermRemainder]
    exact (riemannHypothesis_iff_suzukiLocalCartanGermWardObservableBounded hphi).mpr
      (hall phi hphi)
  · intro hRH phi hphi
    exact (riemannHypothesis_iff_suzukiLocalCartanGermWardObservableBounded hphi).mp hRH

/-- The literal opposite-root `SL₂` Levi logarithm belongs to the classified class. -/
theorem suzukiLogOneAddCartanGerm_cubicControlled :
    SuzukiLocalCartanGermCubicControlled (fun x : ℝ => Real.log (1 + x)) := by
  refine ⟨1 / 3, by norm_num, ?_⟩
  intro x hx
  have hnonneg := suzukiStokesCartanCubicRemainder_nonneg hx
  have hupper := suzukiStokesCartanCubicRemainder_le hx
  rw [abs_of_nonneg]
  · change Real.log (1 + x) - x + x ^ 2 / 2 ≤ (1 / 3) * x ^ 3
    unfold suzukiStokesCartanCubicRemainder at hupper
    ring_nf at hupper ⊢
    exact hupper
  · simpa [suzukiLocalCartanGermRemainder,
      suzukiStokesCartanCubicRemainder] using hnonneg

/-- Every fixed cubic deformation has the same forced first two jets and is covered by the
universality theorem, regardless of its third-order coefficient. -/
theorem suzukiCubicPolynomialCartanGerm_cubicControlled (c : ℝ) :
    SuzukiLocalCartanGermCubicControlled
      (fun x : ℝ => x - x ^ 2 / 2 + c * x ^ 3) := by
  refine ⟨|c|, abs_nonneg c, ?_⟩
  intro x hx
  have hx3 : 0 ≤ x ^ 3 := by positivity
  unfold suzukiLocalCartanGermRemainder
  have heq : x - x ^ 2 / 2 + c * x ^ 3 - x + x ^ 2 / 2 = c * x ^ 3 := by ring
  rw [heq, abs_mul, abs_of_nonneg hx3]

end

end GaloisForLFunctions.RHTower
