import GaloisForLFunctions.HTGeometry.PolynomialTorsionLanguageDefectLimit
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability

/-!
# Gaussian torsion-language tail lock

At the quadratic Taylor scale the dominant ADE face is not confined to a fixed finite
offset window.  Its complete offset lattice is nevertheless absolutely summable: a grouped
weight has only polynomial growth in the offsets, while the exact residual valuation is a
positive Gaussian quadratic form.  This file develops the two analytic exactification tools
which are special to that critical scale:

* exact expansion of a translated quadratic lattice energy;
* domination of a max-polynomial constrained Gaussian by the coordinatewise ambient Gaussian;
* vanishing of the corresponding finite-box tails;
* approximate finite Fourier inversion.  Unlike the finite-face zero theorem, this last result
  retains a uniform error `epsilon`; it is the step which permits the window radius to tend to
  infinity only after torsion recurrence has exposed a chosen Fourier coefficient.

No bounded-confinement assertion is made: offsets of every fixed size remain on the quadratic
face.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open Filter Finset Topology

noncomputable section

/-! ## Exact quadratic offset energy -/

/-- The largest absolute coordinate of an integer lattice point, measured in `ℕ`. -/
def integerLatticeMaxNatAbs {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℕ :=
  Finset.univ.sup fun i => (z i).natAbs

/-- Quadratic energy of an integer offset tuple. -/
def gaussianOffsetEnergy {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℝ :=
  ∑ i, (z i : ℝ) ^ 2

/-- Translating every coordinate by the same real center splits the quadratic energy into its
center, source-sum, and transverse-offset terms. -/
theorem sum_sq_add_eq_center_source_offset
    {ι : Type*} [Fintype ι] (q : ℝ) (z : ι → ℤ) :
    (∑ i, (q + (z i : ℝ)) ^ 2) =
      (Fintype.card ι : ℝ) * q ^ 2 +
        2 * q * (∑ i, (z i : ℝ)) + gaussianOffsetEnergy z := by
  simp only [gaussianOffsetEnergy]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (∑ i, q * (z i : ℝ) * 2) =
      (q * ∑ i, (z i : ℝ)) * 2 by
    rw [← Finset.sum_mul, ← Finset.mul_sum]]
  ring

/-- Exact quadratic expansion for a bounded multiplicity pattern. -/
theorem polynomialPatternPowerValuation_two
    {M D : ℕ} (p : Fin M → Fin (D + 1)) (t : ℝ)
    (hcount : (∑ r, (p r : ℕ)) = D) :
    polynomialPatternPowerValuation 2 p t =
      (D : ℝ) * t ^ 2 +
        2 * t * (polynomialPatternMoment p 1 : ℝ) +
          (polynomialPatternMoment p 2 : ℝ) := by
  rw [polynomialPatternPowerValuation]
  simp_rw [Real.rpow_two, add_sq, mul_add, Finset.sum_add_distrib]
  have hcountR : (∑ x, ((p x : ℕ) : ℝ)) = D := by
    exact_mod_cast hcount
  have hm1 : (∑ x, ((p x : ℕ) : ℝ) * (x : ℝ)) =
      (polynomialPatternMoment p 1 : ℝ) := by
    rw [polynomialPatternMoment]
    push_cast
    simp only [pow_one]
  have hm2 : (∑ x, ((p x : ℕ) : ℝ) * (x : ℝ) ^ 2) =
      (polynomialPatternMoment p 2 : ℝ) := by
    rw [polynomialPatternMoment]
    push_cast
  have hfirst : (∑ x, ((p x : ℕ) : ℝ) * t ^ 2) = (D : ℝ) * t ^ 2 := by
    rw [← Finset.sum_mul, hcountR]
  have hmiddle : (∑ x, ((p x : ℕ) : ℝ) * (2 * t * (x : ℝ))) =
      2 * t * (polynomialPatternMoment p 1 : ℝ) := by
    rw [← hm1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hfirst, hmiddle, hm2]
  ring

/-- Equal count and equal source sum make the quadratic valuation difference independent of the
translated center. -/
theorem polynomialPatternPowerValuation_two_sub_of_moment_one_eq
    {M D : ℕ} (p r : Fin M → Fin (D + 1)) (t : ℝ)
    (hpcount : (∑ j, (p j : ℕ)) = D)
    (hrcount : (∑ j, (r j : ℕ)) = D)
    (hmoment : polynomialPatternMoment p 1 = polynomialPatternMoment r 1) :
    polynomialPatternPowerValuation 2 p t -
        polynomialPatternPowerValuation 2 r t =
      (polynomialPatternMoment p 2 : ℝ) -
        (polynomialPatternMoment r 2 : ℝ) := by
  rw [polynomialPatternPowerValuation_two p t hpcount,
    polynomialPatternPowerValuation_two r t hrcount, hmoment]
  ring

/-! ## Ambient Gaussian majorant -/

/-- The coordinatewise polynomial-Gaussian majorant supplied by
`summable_fintype_pi_polynomialGaussian`. -/
def gaussianCoordinateMajorant
    {ι : Type*} [Fintype ι] (J : ℕ) (B : ℝ) (z : ι → ℤ) : ℝ :=
  ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J *
    Real.exp (-B * (z i : ℝ) ^ 2)

theorem gaussianCoordinateMajorant_nonneg
    {ι : Type*} [Fintype ι] (J : ℕ) (B : ℝ) (z : ι → ℤ) :
    0 ≤ gaussianCoordinateMajorant J B z := by
  unfold gaussianCoordinateMajorant
  positivity

/-- The maximum-coordinate polynomial weight is bounded by the product of the coordinatewise
weights.  Positivity of the dimension is essential only to choose a coordinate attaining the
finite maximum. -/
theorem one_add_latticeMax_pow_le_prod
    {ι : Type*} [Fintype ι] [Nonempty ι] (J : ℕ) (z : ι → ℤ) :
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J ≤
      ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J := by
  classical
  obtain ⟨i, _hi, hiMax⟩ := Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset ι)) (f := fun i => (z i).natAbs)
    (Finset.univ_nonempty)
  have hfactor : (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J =
      (1 + ((z i).natAbs : ℝ)) ^ J := by
    simp only [integerLatticeMaxNatAbs]
    rw [hiMax]
  rw [hfactor]
  exact Finset.single_le_prod'
    (fun j _ => by
      have : (1 : ℝ) ≤ 1 + ((z j).natAbs : ℝ) := by positivity
      exact one_le_pow₀ this)
    (Finset.mem_univ i)

/-- Exact product factorization of the coordinatewise Gaussian. -/
theorem prod_exp_neg_sq
    {ι : Type*} [Fintype ι] (B : ℝ) (z : ι → ℤ) :
    (∏ i, Real.exp (-B * (z i : ℝ) ^ 2)) =
      Real.exp (-B * gaussianOffsetEnergy z) := by
  rw [← Real.exp_sum]
  simp only [gaussianOffsetEnergy]
  congr 1
  rw [← Finset.mul_sum]
  ring

/-- A polynomial in the largest offset times the constrained Gaussian energy is bounded by a
constant multiple of the coordinatewise ambient Gaussian. -/
theorem maxPolynomial_gaussian_le_coordinateMajorant
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (_hB : 0 ≤ B) (Q₀ : ℝ) (z : ι → ℤ) :
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z - Q₀)) ≤
      Real.exp (B * Q₀) * gaussianCoordinateMajorant J B z := by
  have hpoly := one_add_latticeMax_pow_le_prod J z
  have hexp : Real.exp (-B * (gaussianOffsetEnergy z - Q₀)) =
      Real.exp (B * Q₀) *
        ∏ i, Real.exp (-B * (z i : ℝ) ^ 2) := by
    rw [prod_exp_neg_sq]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, gaussianCoordinateMajorant, Finset.prod_mul_distrib]
  have hnonneg : 0 ≤ Real.exp (B * Q₀) *
      ∏ i, Real.exp (-B * (z i : ℝ) ^ 2) := by positivity
  nlinarith

/-- Coordinatewise polynomial-Gaussian weights are summable on every finite integer lattice. -/
theorem summable_gaussianCoordinateMajorant
    (ι : Type) [Fintype ι] (J : ℕ) {B : ℝ} (hB : 0 < B) :
    Summable (gaussianCoordinateMajorant (ι := ι) J B) := by
  simpa [gaussianCoordinateMajorant] using
    (summable_fintype_pi_polynomialGaussian ι (fun _ => J) (fun _ => B)
      (fun _ => hB))

/-- The max-polynomial Gaussian itself is summable, by comparison with the ambient product. -/
theorem summable_maxPolynomial_gaussian
    (ι : Type) [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (hB : 0 < B) (Q₀ : ℝ) :
    Summable (fun z : ι → ℤ =>
      (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z - Q₀))) := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((summable_gaussianCoordinateMajorant ι J hB).mul_left (Real.exp (B * Q₀)))
  exact maxPolynomial_gaussian_le_coordinateMajorant J hB.le Q₀ z

/-- The ambient product majorant outside growing integer boxes tends to zero. -/
theorem tendsto_gaussianCoordinateMajorant_tsum_outside_box_zero
    (ι : Type) [Fintype ι] (J : ℕ) (B : ℝ) :
    Tendsto (fun R =>
      ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
        gaussianCoordinateMajorant J B z.1)
      atTop (nhds 0) := by
  simpa [gaussianCoordinateMajorant] using
    (tendsto_polynomialGaussian_tsum_outside_box_zero
      ι (fun _ => J) (fun _ => B))

/-- The complete max-polynomial Gaussian face has vanishing mass outside growing finite boxes. -/
theorem tendsto_maxPolynomial_gaussian_tsum_outside_box_zero
    (ι : Type) [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (hB : 0 < B) (Q₀ : ℝ) :
    Tendsto (fun R =>
      ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
        (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
          Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀)))
      atTop (nhds 0) := by
  let f : (ι → ℤ) → ℝ := fun z =>
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
      Real.exp (-B * (gaussianOffsetEnergy z - Q₀))
  have hsum : Summable f := summable_maxPolynomial_gaussian ι J hB Q₀
  exact (tendsto_tsum_compl_atTop_zero f).comp (integerLatticeBox_tendsto_atTop ι)

/-! ## Approximate finite Fourier inversion -/

/-- Approximate torsion Fourier inversion: if a finite multiplicity face is uniformly bounded by
`epsilon` on the full `(D+1)`-torsion state space, then each individual Fourier coefficient has
norm at most `epsilon`.  This is the quantitative replacement for
`face_fin_weights_eq_zero` needed before sending a Gaussian window radius to infinity. -/
theorem norm_face_fin_weight_le_of_uniform_torsion_bound
    {M D : ℕ} (F : Finset (Fin M → Fin (D + 1)))
    (ell : (Fin M → Fin (D + 1)) → ℂ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ s : Fin M → ℂ, (∀ r, s r ^ (D + 1) = 1) →
      ‖∑ p ∈ F, ell p * ∏ r, s r ^ (p r : ℕ)‖ ≤ epsilon) :
    ∀ p ∈ F, ‖ell p‖ ≤ epsilon := by
  classical
  intro p₀ hp₀
  let m := D + 1
  have hm0 : m ≠ 0 := by omega
  set zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hzetaDef
  have hzeta : IsPrimitiveRoot zeta m := Complex.isPrimitiveRoot_exp m hm0
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero hm0
  let states : Finset (Fin M → ℕ) :=
    Fintype.piFinset (fun _ : Fin M => Finset.range m)
  let faceValue : (Fin M → ℕ) → ℂ := fun x =>
    ∑ p ∈ F, ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))
  have hstateBound : ∀ x ∈ states, ‖faceValue x‖ ≤ epsilon := by
    intro x hx
    have hxmem : ∀ i, x i ∈ Finset.range m := by
      simpa [states, Fintype.mem_piFinset] using hx
    let s : Fin M → ℂ := fun i => zeta ^ x i
    have hs : ∀ i, s i ^ (D + 1) = 1 := by
      intro i
      dsimp [s, m]
      rw [← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    have hb := hbound s hs
    have heq : faceValue x =
        ∑ p ∈ F, ell p * ∏ i, s i ^ (p i : ℕ) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      dsimp [s]
      rw [← pow_mul, ← zpow_natCast zeta (x i * (p i : ℕ))]
      congr 1
      push_cast
      ring
    rwa [heq]
  have hoff : ∀ p ∈ F, p ≠ p₀ →
      ∏ i, (∑ j ∈ Finset.range m,
        (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) = 0 := by
    intro p hp hne
    obtain ⟨i₀, hi₀⟩ : ∃ i, p i ≠ p₀ i := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    refine Finset.prod_eq_zero (Finset.mem_univ i₀)
      (sum_pow_zpow_eq_zero hzeta ?_)
    intro hdvd
    have habs : |(p i₀ : ℤ) - (p₀ i₀ : ℤ)| < (m : ℤ) := by
      rw [abs_lt]
      change -((D : ℤ) + 1) < (p i₀ : ℤ) - (p₀ i₀ : ℤ) ∧
        (p i₀ : ℤ) - (p₀ i₀ : ℤ) < (D : ℤ) + 1
      constructor <;> omega
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
    apply hi₀
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp hz
  have hdiag :
      ∏ i : Fin M, (∑ j ∈ Finset.range m,
        (zeta ^ ((p₀ i : ℤ) - (p₀ i : ℤ))) ^ j) =
        (m : ℂ) ^ M := by
    simp [Finset.prod_const, m]
  have hfourier :
      ell p₀ * (m : ℂ) ^ M =
        ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x := by
    have hrw : ∀ p ∈ F,
        ell p * ∏ i, (∑ j ∈ Finset.range m,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) =
          ∑ x ∈ states,
            (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) *
              (ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))) := by
      intro p hp
      rw [Finset.prod_univ_sum, Finset.mul_sum]
      apply Finset.sum_congr
      · ext x
        simp only [states, Fintype.mem_piFinset]
      · intro x hx
        have hsplit : ∀ i : Fin M,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ x i =
              zeta ^ (-((p₀ i : ℤ) * (x i : ℤ))) *
                zeta ^ ((p i : ℤ) * (x i : ℤ)) := by
          intro i
          rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hzeta0]
          congr 1
          push_cast
          ring
        rw [Finset.prod_congr rfl (fun i _ => hsplit i),
          Finset.prod_mul_distrib]
        ring
    calc
      ell p₀ * (m : ℂ) ^ M =
          ∑ p ∈ F, ell p * ∏ i, (∑ j ∈ Finset.range m,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) := by
        rw [Finset.sum_eq_single p₀]
        · rw [hdiag]
        · intro p hp hne
          rw [hoff p hp hne, mul_zero]
        · exact fun h => (h hp₀).elim
      _ = ∑ p ∈ F, ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) *
            (ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))) :=
        Finset.sum_congr rfl hrw
      _ = ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
  have hcharNorm : ∀ x : Fin M → ℕ, ‖(∏ i : Fin M,
      zeta ^ (-((p₀ i : ℤ) * (x i : ℤ))))‖ = 1 := by
    intro x
    rw [norm_prod]
    have hzetaNorm : ‖zeta‖ = 1 := hzeta.norm'_eq_one hm0
    simp [norm_zpow, hzetaNorm]
  have hrhs :
      ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ ≤
        (m : ℝ) ^ M * epsilon := by
    calc
      ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ ≤
          ∑ x ∈ states,
            ‖(∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _x ∈ states, epsilon := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul, hcharNorm]
        simpa using hstateBound x hx
      _ = (m : ℝ) ^ M * epsilon := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        simp [states, m]
  have hmul : ‖ell p₀‖ * (m : ℝ) ^ M ≤ (m : ℝ) ^ M * epsilon := by
    rw [← hfourier, norm_mul, norm_pow]
    have hmnorm : ‖(m : ℂ)‖ = (m : ℝ) := by simp
    rwa [hmnorm] at hrhs
  have hmpos : 0 < (m : ℝ) ^ M := by positivity
  nlinarith

end

end GaloisForLFunctions
