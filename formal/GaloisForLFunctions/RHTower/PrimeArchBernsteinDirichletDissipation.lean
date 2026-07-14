import GaloisForLFunctions.RHTower.PrimeArchBernsteinPurityDivergence

/-!
# Dirichlet dissipation under Bernstein degree elevation

Bernstein degree elevation is a fixed barycentric coarse-graining.  Its exact squared-energy
loss is a weighted nearest-neighbour Dirichlet form.  Consequently the scaled coefficient purity
`(n + 1) * Pi n` is monotone and equals its initial value plus cumulative dissipation.

For the endpoint prime--archimedean source, RH is equivalent to a linear cumulative-dissipation
bound recurring at cofinally many degrees.  Under failure of RH the cumulative mean dissipation
tends to positive infinity.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

open HTGeometry

/-- Weighted nearest-neighbour energy of the degree-`n+1` Bernstein coefficient packet. -/
def bernsteinCoefficientDirichletDissipation (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((((n + 1 - i) * (i + 1) : ℕ) : ℝ) / (n + 1 : ℝ)) *
      (bernsteinCoefficient m (n + 1) i -
        bernsteinCoefficient m (n + 1) (i + 1)) ^ 2

theorem bernsteinCoefficientDirichletDissipation_nonneg
    (m : ℕ → ℝ) (n : ℕ) :
    0 ≤ bernsteinCoefficientDirichletDissipation m n := by
  rw [bernsteinCoefficientDirichletDissipation]
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) (sq_nonneg _)

/-- Moment evaluation transports Bernstein degree elevation to the coefficient packets. -/
lemma bernsteinCoefficient_degree_elevation
    (m : ℕ → ℝ) (n i : ℕ) (hi : i ≤ n) :
    bernsteinCoefficient m n i =
      (((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) *
          bernsteinCoefficient m (n + 1) i +
        (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) *
          bernsteinCoefficient m (n + 1) (i + 1) := by
  rw [bernsteinCoefficient, bernsteinPolynomial_degree_elevation n i hi,
    momentFunctional_add, momentFunctional_smul, momentFunctional_smul]
  rfl

private lemma two_point_barycentric_energy_identity
    {A B D x y : ℝ} (hD : D ≠ 0) (hsum : A + B = D + 1) :
    D * (A / D * x + B / D * y) ^ 2 +
        (A * B / D) * (x - y) ^ 2 =
      (D + 1) * (A / D * x ^ 2 + B / D * y ^ 2) := by
  field_simp [hD]
  linear_combination (A * x ^ 2 + B * y ^ 2) * hsum

/-- **Exact degree-elevation dissipation law.**  The increase of scaled purity is precisely the
weighted adjacent Dirichlet energy of the finer packet. -/
theorem scaled_bernsteinCoefficientPurity_succ_eq_add_dirichletDissipation
    (m : ℕ → ℝ) (n : ℕ) :
    (n + 2 : ℝ) * bernsteinCoefficientPurity m (n + 1) =
      (n + 1 : ℝ) * bernsteinCoefficientPurity m n +
        bernsteinCoefficientDirichletDissipation m n := by
  let x : ℕ → ℝ := fun i => bernsteinCoefficient m (n + 1) i
  have hrow (i : ℕ) (hi : i ≤ n) :
      (n + 1 : ℝ) * (bernsteinCoefficient m n i) ^ 2 +
          ((((n + 1 - i) * (i + 1) : ℕ) : ℝ) / (n + 1 : ℝ)) *
            (x i - x (i + 1)) ^ 2 =
        (n + 2 : ℝ) *
          ((((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) * (x i) ^ 2 +
            (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) * (x (i + 1)) ^ 2) := by
    rw [bernsteinCoefficient_degree_elevation m n i hi]
    have hden : (n + 1 : ℝ) ≠ 0 := by positivity
    have hsum :
        ((n + 1 - i : ℕ) : ℝ) + ((i + 1 : ℕ) : ℝ) =
          (n + 1 : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega : i ≤ n + 1)]
      push_cast
      ring
    have hident := two_point_barycentric_energy_identity
      (A := ((n + 1 - i : ℕ) : ℝ)) (B := ((i + 1 : ℕ) : ℝ))
      (D := (n + 1 : ℝ)) (x := x i) (y := x (i + 1)) hden hsum
    dsimp only [x] at hident ⊢
    convert hident using 1 <;> push_cast <;> ring
  rw [bernsteinCoefficientPurity, bernsteinCoefficientPurity,
    bernsteinCoefficientDirichletDissipation]
  calc
    (n + 2 : ℝ) *
        (∑ i ∈ Finset.range (n + 1 + 1),
          (bernsteinCoefficient m (n + 1) i) ^ 2) =
      (n + 2 : ℝ) *
        (∑ i ∈ Finset.range (n + 1),
          ((((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) * (x i) ^ 2 +
            (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) * (x (i + 1)) ^ 2)) := by
        rw [show n + 1 + 1 = n + 2 by omega]
        rw [bernstein_elevation_weighted_sum n (fun i => (x i) ^ 2)]
    _ = ∑ i ∈ Finset.range (n + 1),
        ((n + 2 : ℝ) *
          ((((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) * (x i) ^ 2 +
            (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) * (x (i + 1)) ^ 2)) := by
        rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1),
        ((n + 1 : ℝ) * (bernsteinCoefficient m n i) ^ 2 +
          ((((n + 1 - i) * (i + 1) : ℕ) : ℝ) / (n + 1 : ℝ)) *
            (x i - x (i + 1)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hil : i < n + 1 := by simpa only [Finset.mem_range] using hi
        exact (hrow i (by omega)).symm
    _ = (n + 1 : ℝ) *
          (∑ i ∈ Finset.range (n + 1),
            (bernsteinCoefficient m n i) ^ 2) +
        ∑ i ∈ Finset.range (n + 1),
          ((((n + 1 - i) * (i + 1) : ℕ) : ℝ) / (n + 1 : ℝ)) *
            (x i - x (i + 1)) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := rfl

/-- Scaled Bernstein purity is nondecreasing under degree elevation. -/
theorem scaled_bernsteinCoefficientPurity_monotone (m : ℕ → ℝ) :
    Monotone (fun n : ℕ => (n + 1 : ℝ) * bernsteinCoefficientPurity m n) := by
  apply monotone_nat_of_le_succ
  intro n
  calc
    (n + 1 : ℝ) * bernsteinCoefficientPurity m n ≤
        (n + 1 : ℝ) * bernsteinCoefficientPurity m n +
          bernsteinCoefficientDirichletDissipation m n :=
      le_add_of_nonneg_right (bernsteinCoefficientDirichletDissipation_nonneg m n)
    _ = (n + 2 : ℝ) * bernsteinCoefficientPurity m (n + 1) :=
      (scaled_bernsteinCoefficientPurity_succ_eq_add_dirichletDissipation m n).symm
    _ = ((n + 1 : ℕ) + 1 : ℝ) * bernsteinCoefficientPurity m (n + 1) := by
      push_cast
      ring

/-- The scaled purity is the initial purity plus total accumulated Dirichlet dissipation. -/
theorem scaled_bernsteinCoefficientPurity_eq_initial_add_sum_dirichletDissipation
    (m : ℕ → ℝ) (n : ℕ) :
    (n + 1 : ℝ) * bernsteinCoefficientPurity m n =
      bernsteinCoefficientPurity m 0 +
        ∑ k ∈ Finset.range n, bernsteinCoefficientDirichletDissipation m k := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ((n + 1 : ℕ) + 1 : ℝ) * bernsteinCoefficientPurity m (n + 1) =
            (n + 2 : ℝ) * bernsteinCoefficientPurity m (n + 1) := by
              push_cast
              ring
        _ = (n + 1 : ℝ) * bernsteinCoefficientPurity m n +
              bernsteinCoefficientDirichletDissipation m n :=
          scaled_bernsteinCoefficientPurity_succ_eq_add_dirichletDissipation m n
        _ = bernsteinCoefficientPurity m 0 +
              ∑ k ∈ Finset.range (n + 1),
                bernsteinCoefficientDirichletDissipation m k := by
          rw [ih, Finset.sum_range_succ]
          ring

/-- Endpoint source Dirichlet dissipation. -/
def primeArchEndpointBernsteinDirichletDissipation (n : ℕ) : ℝ :=
  bernsteinCoefficientDirichletDissipation
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n

theorem primeArchEndpointBernstein_scaledPurity_eq_initial_add_sum_dissipation
    (n : ℕ) :
    (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n =
      primeArchEndpointBernsteinPurity 0 +
        ∑ k ∈ Finset.range n, primeArchEndpointBernsteinDirichletDissipation k := by
  exact scaled_bernsteinCoefficientPurity_eq_initial_add_sum_dirichletDissipation _ n

/-- Initial endpoint energy plus all Dirichlet dissipation accumulated before degree `n`. -/
def primeArchEndpointBernsteinCumulativeDissipationEnergy (n : ℕ) : ℝ :=
  primeArchEndpointBernsteinPurity 0 +
    ∑ k ∈ Finset.range n, primeArchEndpointBernsteinDirichletDissipation k

/-- The cumulative dissipation energy is exactly the linearly scaled endpoint purity. -/
theorem primeArchEndpointBernsteinCumulativeDissipationEnergy_eq_scaledPurity
    (n : ℕ) :
    primeArchEndpointBernsteinCumulativeDissipationEnergy n =
      (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n := by
  exact (primeArchEndpointBernstein_scaledPurity_eq_initial_add_sum_dissipation n).symm

/-- A cofinal linear bound for cumulative endpoint Dirichlet dissipation. -/
def PrimeArchEndpointBernsteinCofinalLinearDissipation : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    (∑ k ∈ Finset.range n, primeArchEndpointBernsteinDirichletDissipation k) ≤
      C * (n + 1 : ℝ)

/-- **Cofinal dissipation criterion.** RH is equivalent to one fixed linear cumulative-energy
bound recurring at arbitrarily large Bernstein degrees. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinCofinalLinearDissipation :
    RiemannHypothesis ↔ PrimeArchEndpointBernsteinCofinalLinearDissipation := by
  constructor
  · intro hRH
    refine ⟨normalizedPrimeArchMoment 0 ^ 2, fun N => ⟨N, le_rfl, ?_⟩⟩
    have hbalance :=
      primeArchEndpointBernstein_scaledPurity_eq_initial_add_sum_dissipation N
    have hupper := primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH N
    have hzero : 0 ≤ primeArchEndpointBernsteinPurity 0 :=
      bernsteinCoefficientPurity_nonneg _ 0
    nlinarith
  · rintro ⟨C, hC⟩
    apply riemannHypothesis_iff_primeArchEndpointBernsteinPurity_cofinallyBounded.mpr
    refine ⟨primeArchEndpointBernsteinPurity 0 + C, fun N => ?_⟩
    obtain ⟨n, hn, hsum⟩ := hC N
    refine ⟨n, hn, ?_⟩
    have hbalance :=
      primeArchEndpointBernstein_scaledPurity_eq_initial_add_sum_dissipation n
    have hzero : 0 ≤ primeArchEndpointBernsteinPurity 0 :=
      bernsteinCoefficientPurity_nonneg _ 0
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmul :
        (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n ≤
          (n + 1 : ℝ) * (primeArchEndpointBernsteinPurity 0 + C) := by
      nlinarith [mul_nonneg hn0 hzero]
    exact le_of_mul_le_mul_left hmul (by positivity : (0 : ℝ) < n + 1)

/-- The cumulative mean endpoint dissipation. -/
def primeArchEndpointBernsteinMeanDissipation (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, primeArchEndpointBernsteinDirichletDissipation k) /
    (n + 1 : ℝ)

/-- Failure of RH forces the cumulative mean dissipation to positive infinity. -/
theorem tendsto_primeArchEndpointBernsteinMeanDissipation_atTop_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    Tendsto primeArchEndpointBernsteinMeanDissipation atTop atTop := by
  have hp := tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis hRH
  have hshift : Tendsto
      (fun n : ℕ => primeArchEndpointBernsteinPurity n -
        primeArchEndpointBernsteinPurity 0) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    exact (hp.eventually_ge_atTop
      (b + primeArchEndpointBernsteinPurity 0)).mono (fun n hn => by linarith)
  apply tendsto_atTop_mono' atTop (Eventually.of_forall fun n => ?_) hshift
  rw [primeArchEndpointBernsteinMeanDissipation]
  have hbalance :=
    primeArchEndpointBernstein_scaledPurity_eq_initial_add_sum_dissipation n
  have hzero : 0 ≤ primeArchEndpointBernsteinPurity 0 :=
    bernsteinCoefficientPurity_nonneg _ 0
  have hden : 0 < (n + 1 : ℝ) := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The endpoint source has a sharp dissipation dichotomy: RH gives a cofinal linear phase,
whereas false RH gives divergent cumulative mean dissipation. -/
theorem primeArchEndpointBernsteinDirichletDissipation_dichotomy :
    (RiemannHypothesis ∧ PrimeArchEndpointBernsteinCofinalLinearDissipation) ∨
    (¬ RiemannHypothesis ∧
      Tendsto primeArchEndpointBernsteinMeanDissipation atTop atTop) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ⟨hRH,
      riemannHypothesis_iff_primeArchEndpointBernsteinCofinalLinearDissipation.mp hRH⟩
  · exact Or.inr ⟨hRH,
      tendsto_primeArchEndpointBernsteinMeanDissipation_atTop_of_not_rh hRH⟩

end

end RHTower
