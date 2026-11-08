import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitMassBoundaryOfPositiveAnnihilators

/-!
# The hyperbolic cost of a reflected zero pair

The two zero equations at equal height give an exact hyperbolic moment.
Its endpoint-normalized test yields the central positive-mass cost of the pair.
Positive trinomials with two opposite endpoint phases attain this cost.
The reflection excess is strict, but tends to zero as bandwidth grows.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Filter Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem sinh_test_identity (δ c L : ℝ) :
    Real.sinh (δ * (c - L)) =
      (Real.exp (δ * c) * Real.exp (-δ * L) -
        Real.exp (-δ * c) * Real.exp (δ * L)) / 2 := by
  have hp : δ * c + -δ * L = δ * (c - L) := by ring
  have hm : -δ * c + δ * L = -(δ * (c - L)) := by ring
  rw [← Real.exp_add, ← Real.exp_add, hp, hm, Real.sinh_eq]

private theorem shifted_frequency_sum {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (ρ : ℂ) (t : ℝ) :
    (∑ d ∈ P.support.erase 0, (Real.exp (-t * monomialLog d) : ℂ) *
      ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) =
        dirichletEval (ρ + (t : ℂ)) P - 1 := by
  rw [dirichletEval_eq_one_add_tail hP, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro d _
  rw [Complex.ofReal_exp]
  calc
    _ = (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
        (Complex.exp ((-t * monomialLog d : ℝ) : ℂ) *
          Complex.exp (-(monomialLog d : ℂ) * ρ)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- The two reflected zeros prescribe a nonzero hyperbolic frequency moment. -/
theorem reflected_pair_hyperbolic_moment {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {δ : ℝ}
    (hplus : dirichletEval (ρ + (δ : ℂ)) P = 0)
    (hminus : dirichletEval (ρ - (δ : ℂ)) P = 0) (c : ℝ) :
    (∑ d ∈ P.support.erase 0, (Real.sinh (δ * (c - monomialLog d)) : ℂ) *
      ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) =
        -(Real.sinh (δ * c) : ℂ) := by
  have hp := shifted_frequency_sum hP ρ δ
  have hm := shifted_frequency_sum hP ρ (-δ)
  rw [hplus, zero_sub] at hp
  simp only [neg_neg, Complex.ofReal_neg, ← sub_eq_add_neg, hminus, zero_sub] at hm
  have he : (∑ d ∈ P.support.erase 0, (Real.sinh (δ * (c - monomialLog d)) : ℂ) *
      ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) =
      ((Real.exp (δ * c) : ℂ) * (∑ d ∈ P.support.erase 0,
        (Real.exp (-δ * monomialLog d) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) -
       (Real.exp (-δ * c) : ℂ) * (∑ d ∈ P.support.erase 0,
        (Real.exp (δ * monomialLog d) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)))) / 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [sinh_test_identity]
    push_cast
    ring
  rw [he, hp, hm, Real.sinh_eq]
  push_cast
  ring_nf

/-- Equal-height reflected zeros force the sharp central-mass bound associated
with the available logarithmic frequency interval. -/
theorem reflected_pair_forces_hyperbolic_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hplus : dirichletEval (ρ + (δ : ℂ)) P = 0)
    (hminus : dirichletEval (ρ - (δ : ℂ)) P = 0)
    {a B : ℝ} (ha : 0 < a) (hB : a < B)
    (hfreq : ∀ d ∈ P.support.erase 0, a ≤ monomialLog d ∧ monomialLog d ≤ B) :
    Real.sinh (δ * ((B + a) / 2)) / Real.sinh (δ * ((B - a) / 2)) ≤
      dirichletTailMass P ρ.re := by
  let c := (B + a) / 2
  let h := (B - a) / 2
  have hh : 0 < h := by dsimp only [h]; positivity
  have hc : 0 < c := by dsimp only [c]; linarith only [ha, hB]
  have hden : 0 < Real.sinh (δ * h) := Real.sinh_pos_iff.mpr (mul_pos hδ hh)
  have hmoment := reflected_pair_hyperbolic_moment hP hplus hminus c
  have htest (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      |Real.sinh (δ * (c - monomialLog d))| ≤ Real.sinh (δ * h) := by
    rw [Real.abs_sinh]
    apply Real.sinh_le_sinh.mpr
    rw [abs_mul, abs_of_pos hδ]
    apply mul_le_mul_of_nonneg_left _ hδ.le
    apply abs_le.mpr
    dsimp only [c, h]
    constructor <;> linarith only [(hfreq d hd).1, (hfreq d hd).2]
  have hcost : Real.sinh (δ * c) ≤ Real.sinh (δ * h) * dirichletTailMass P ρ.re := by
    calc
      _ = ‖∑ d ∈ P.support.erase 0, (Real.sinh (δ * (c - monomialLog d)) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))‖ := by
        rw [hmoment, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos hδ hc))]
      _ ≤ ∑ d ∈ P.support.erase 0, ‖(Real.sinh (δ * (c - monomialLog d)) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ d ∈ P.support.erase 0, Real.sinh (δ * h) *
          (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) := by
        apply Finset.sum_le_sum
        intro d hd
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (P.coeff d).coe_nonneg, Complex.norm_exp, Complex.mul_re,
          Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
          neg_zero, zero_mul, sub_zero]
        exact mul_le_mul_of_nonneg_right (htest d hd)
          (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)
      _ = _ := by rw [dirichletTailMass, Finset.mul_sum]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcost)

private theorem sinh_exp_cancel_plus (u v : ℝ) :
    Real.sinh v * Real.exp u - Real.sinh u * Real.exp v = Real.sinh (v - u) := by
  rw [Real.sinh_sub]
  simp only [Real.sinh_eq, Real.cosh_eq]
  ring

private theorem sinh_exp_cancel_minus (u v : ℝ) :
    Real.sinh v * Real.exp (-u) - Real.sinh u * Real.exp (-v) = Real.sinh (v - u) := by
  rw [Real.sinh_sub]
  simp only [Real.sinh_eq, Real.cosh_eq]
  ring

private theorem sinh_ratio_split {u v : ℝ} (h : u < v) :
    (Real.sinh v + Real.sinh u) / Real.sinh (v - u) =
      Real.sinh ((v + u) / 2) / Real.sinh ((v - u) / 2) := by
  have hh : 0 < Real.sinh ((v - u) / 2) :=
    Real.sinh_pos_iff.mpr (by linarith only [h])
  have hc : 0 < Real.cosh ((v - u) / 2) := Real.cosh_pos _
  have hv := Real.sinh_add ((v + u) / 2) ((v - u) / 2)
  have hu := Real.sinh_sub ((v + u) / 2) ((v - u) / 2)
  rw [show (v + u) / 2 + (v - u) / 2 = v by ring] at hv
  rw [show (v + u) / 2 - (v - u) / 2 = u by ring] at hu
  have hsum : Real.sinh v + Real.sinh u =
      2 * Real.sinh ((v + u) / 2) * Real.cosh ((v - u) / 2) := by
    rw [hv, hu]
    ring
  have hden : Real.sinh (v - u) =
      2 * Real.sinh ((v - u) / 2) * Real.cosh ((v - u) / 2) := by
    rw [← Real.sinh_two_mul]
    congr 1
    ring
  rw [hsum, hden]
  field_simp [hh.ne', hc.ne']

/-- The upper endpoint of the two-frequency prime-two support. -/
def reflectedPairFrequency (m : ℕ) : ℝ := ((2 * m + 2 : ℕ) : ℝ) * Real.log 2

private theorem reflectedPairFrequency_gt (m : ℕ) :
    Real.log 2 < reflectedPairFrequency m := by
  have hn : (1 : ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 * m + 2 by omega)
  simpa only [reflectedPairFrequency, one_mul] using
    mul_lt_mul_of_pos_right hn (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- Positive weight of the lower frequency in the sharp reflected-pair trinomial. -/
def reflectedPairLowCoefficient (δ : ℝ) (m : ℕ) : ℝ≥0 :=
  Real.toNNReal (Real.sinh (δ * reflectedPairFrequency m) /
    Real.sinh (δ * (reflectedPairFrequency m - Real.log 2)))

/-- Positive weight of the upper frequency in the sharp reflected-pair trinomial. -/
def reflectedPairHighCoefficient (δ : ℝ) (m : ℕ) : ℝ≥0 :=
  Real.toNNReal (Real.sinh (δ * Real.log 2) /
    Real.sinh (δ * (reflectedPairFrequency m - Real.log 2)))

private theorem pair_den_pos {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    0 < Real.sinh (δ * (reflectedPairFrequency m - Real.log 2)) :=
  Real.sinh_pos_iff.mpr (mul_pos hδ (sub_pos.mpr (reflectedPairFrequency_gt m)))

private theorem coe_pair_low {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ((reflectedPairLowCoefficient δ m : ℝ≥0) : ℝ) =
      Real.sinh (δ * reflectedPairFrequency m) /
        Real.sinh (δ * (reflectedPairFrequency m - Real.log 2)) := by
  apply Real.coe_toNNReal
  exact (div_pos (Real.sinh_pos_iff.mpr (mul_pos hδ
    ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans (reflectedPairFrequency_gt m))))
      (pair_den_pos hδ m)).le

private theorem coe_pair_high {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ((reflectedPairHighCoefficient δ m : ℝ≥0) : ℝ) =
      Real.sinh (δ * Real.log 2) /
        Real.sinh (δ * (reflectedPairFrequency m - Real.log 2)) := by
  apply Real.coe_toNNReal
  exact (div_pos (Real.sinh_pos_iff.mpr
    (mul_pos hδ (Real.log_pos (by norm_num : (1 : ℝ) < 2)))) (pair_den_pos hδ m)).le

/-- The endpoint phases are minus one and plus one at the marked ordinate. -/
def reflectedPairAnnihilator (σ δ : ℝ) (m : ℕ) : MvPolynomial (Fin 2) ℝ≥0 :=
  1 + MvPolynomial.C (reflectedPairLowCoefficient δ m) * scaledTwoMonomial σ +
    MvPolynomial.C (reflectedPairHighCoefficient δ m) * scaledTwoMonomial σ ^ (2 * m + 2)

theorem reflectedPairAnnihilator_constantCoeff (σ δ : ℝ) (m : ℕ) :
    MvPolynomial.constantCoeff (reflectedPairAnnihilator σ δ m) = 1 := by
  simp [reflectedPairAnnihilator, scaledTwoMonomial, pow_add]

private theorem pair_eval (σ δ : ℝ) (m : ℕ) (s : ℂ) :
    dirichletEval s (reflectedPairAnnihilator σ δ m) =
      1 + (((reflectedPairLowCoefficient δ m : ℝ≥0) : ℝ) : ℂ) *
        dirichletEval s (scaledTwoMonomial σ) +
      (((reflectedPairHighCoefficient δ m : ℝ≥0) : ℝ) : ℂ) *
        dirichletEval s (scaledTwoMonomial σ) ^ (2 * m + 2) := by
  simp only [reflectedPairAnnihilator, map_add, map_one, map_mul, map_pow,
    dirichletEval, MvPolynomial.eval₂Hom_C]
  rfl

private theorem scaledTwoMonomial_shift_root (σ t : ℝ) :
    dirichletEval (sharpBinomialRoot σ + (t : ℂ)) (scaledTwoMonomial σ) =
      -(Real.exp (-Real.log 2 * t) : ℂ) := by
  rw [dirichletEval_scaledTwoMonomial]
  have he : (Real.log 2 : ℂ) * ((σ : ℂ) - (sharpBinomialRoot σ + (t : ℂ))) =
      (Real.log 2 : ℂ) * ((σ : ℂ) - sharpBinomialRoot σ) + ((-Real.log 2 * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← dirichletEval_scaledTwoMonomial,
    scaledTwoMonomial_at_root, ← Complex.ofReal_exp, neg_one_mul]

private theorem pair_eval_shift_root (σ δ t : ℝ) (m : ℕ) :
    dirichletEval (sharpBinomialRoot σ + (t : ℂ)) (reflectedPairAnnihilator σ δ m) =
      ((1 - ((reflectedPairLowCoefficient δ m : ℝ≥0) : ℝ) * Real.exp (-Real.log 2 * t) +
        ((reflectedPairHighCoefficient δ m : ℝ≥0) : ℝ) *
          Real.exp (-reflectedPairFrequency m * t) : ℝ) : ℂ) := by
  rw [pair_eval, scaledTwoMonomial_shift_root]
  have hp : (-(Real.exp (-Real.log 2 * t) : ℂ)) ^ (2 * m + 2) =
      (Real.exp (-reflectedPairFrequency m * t) : ℂ) := by
    rw [neg_pow]
    have hs : (-1 : ℂ) ^ (2 * m + 2) = 1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hs, one_mul, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    dsimp only [reflectedPairFrequency]
    ring
  rw [hp]
  push_cast
  ring

/-- The explicit positive trinomial vanishes at both members of the reflected pair. -/
theorem reflectedPairAnnihilator_zeros (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    dirichletEval (sharpBinomialRoot σ + (δ : ℂ)) (reflectedPairAnnihilator σ δ m) = 0 ∧
      dirichletEval (sharpBinomialRoot σ - (δ : ℂ)) (reflectedPairAnnihilator σ δ m) = 0 := by
  have hd := (pair_den_pos hδ m).ne'
  have hp := sinh_exp_cancel_minus (δ * Real.log 2) (δ * reflectedPairFrequency m)
  have hm := sinh_exp_cancel_plus (δ * Real.log 2) (δ * reflectedPairFrequency m)
  have he : δ * reflectedPairFrequency m - δ * Real.log 2 =
      δ * (reflectedPairFrequency m - Real.log 2) := by ring
  rw [he] at hp hm
  constructor
  · rw [pair_eval_shift_root, coe_pair_low hδ, coe_pair_high hδ]
    apply Complex.ofReal_eq_zero.mpr
    have heq : -Real.log 2 * δ = -(δ * Real.log 2) := by ring
    have heqB : -reflectedPairFrequency m * δ = -(δ * reflectedPairFrequency m) := by ring
    rw [heq, heqB]
    field_simp [hd]
    linarith only [hp]
  · rw [sub_eq_add_neg, ← Complex.ofReal_neg, pair_eval_shift_root,
      coe_pair_low hδ, coe_pair_high hδ]
    apply Complex.ofReal_eq_zero.mpr
    have heq : -Real.log 2 * -δ = δ * Real.log 2 := by ring
    have heqB : -reflectedPairFrequency m * -δ = δ * reflectedPairFrequency m := by ring
    rw [heq, heqB]
    field_simp [hd]
    linarith only [hm]

/-- The central tail mass is exactly the universal hyperbolic lower bound. -/
theorem reflectedPairAnnihilator_mass (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    dirichletTailMass (reflectedPairAnnihilator σ δ m) σ =
      Real.sinh (δ * ((reflectedPairFrequency m + Real.log 2) / 2)) /
        Real.sinh (δ * ((reflectedPairFrequency m - Real.log 2) / 2)) := by
  have he := dirichletEval_ofReal_eq_one_add_tail
    (reflectedPairAnnihilator_constantCoeff σ δ m) σ
  rw [pair_eval, scaledTwoMonomial_at_real, one_pow, mul_one, mul_one] at he
  have hm : dirichletTailMass (reflectedPairAnnihilator σ δ m) σ =
      ((reflectedPairLowCoefficient δ m : ℝ≥0) : ℝ) +
        ((reflectedPairHighCoefficient δ m : ℝ≥0) : ℝ) := by
    have hc := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hc
    linarith only [hc]
  rw [hm, coe_pair_low hδ, coe_pair_high hδ, ← add_div]
  have hs := sinh_ratio_split (mul_lt_mul_of_pos_left (reflectedPairFrequency_gt m) hδ)
  rw [show δ * reflectedPairFrequency m - δ * Real.log 2 =
    δ * (reflectedPairFrequency m - Real.log 2) by ring,
    show δ * reflectedPairFrequency m + δ * Real.log 2 =
    δ * (reflectedPairFrequency m + Real.log 2) by ring] at hs
  simpa only [mul_div_assoc] using hs

/-- Only the first and the prescribed even prime-two frequency are present. -/
theorem reflectedPairAnnihilator_frequency_bound (σ δ : ℝ) (m : ℕ) :
    ∀ d ∈ (reflectedPairAnnihilator σ δ m).support.erase 0,
      monomialLog d ≤ reflectedPairFrequency m := by
  intro d hd
  have hraw := Finset.mem_of_mem_erase hd
  have h1 : MvPolynomial.C (reflectedPairLowCoefficient δ m) * scaledTwoMonomial σ =
      MvPolynomial.monomial (Finsupp.single 0 1)
        (reflectedPairLowCoefficient δ m * sharpBinomialCoefficient σ) := by
    rw [scaledTwoMonomial, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_X_eq_monomial]
  have h2 : MvPolynomial.C (reflectedPairHighCoefficient δ m) *
      scaledTwoMonomial σ ^ (2 * m + 2) =
      MvPolynomial.monomial (Finsupp.single 0 (2 * m + 2))
        (reflectedPairHighCoefficient δ m * sharpBinomialCoefficient σ ^ (2 * m + 2)) := by
    rw [scaledTwoMonomial, mul_pow, ← map_pow, ← mul_assoc, ← map_mul,
      MvPolynomial.C_mul_X_pow_eq_monomial]
  change d ∈ (1 + MvPolynomial.C (reflectedPairLowCoefficient δ m) * scaledTwoMonomial σ +
    MvPolynomial.C (reflectedPairHighCoefficient δ m) *
      scaledTwoMonomial σ ^ (2 * m + 2)).support at hraw
  rw [h1, h2] at hraw
  have hs : d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 0 (2 * m + 2) := by
    rcases Finset.mem_union.mp (MvPolynomial.support_add hraw) with hd' | hd'
    · rcases Finset.mem_union.mp (MvPolynomial.support_add hd') with hd' | hd'
      · exact Or.inl (by simpa only [MvPolynomial.support_one, Finset.mem_singleton] using hd')
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd')))
    · exact Or.inr (Or.inr (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd')))
  rcases hs with hz | hl | hu
  · exact ((Finset.mem_erase.mp hd).1 hz).elim
  · rw [hl]
    simpa [monomialLog, primeBase] using (reflectedPairFrequency_gt m).le
  · rw [hu]
    simp [monomialLog, primeBase, reflectedPairFrequency]

/-- Every even prime-two bandwidth admits a positive polynomial attaining the
reflected-pair mass bound, at every center and every positive separation. -/
theorem exists_sharp_reflected_pair_annihilator (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ∃ (P : MvPolynomial (Fin 2) ℝ≥0) (ρ : ℂ),
      MvPolynomial.constantCoeff P = 1 ∧ ρ.re = σ ∧
      dirichletEval (ρ + (δ : ℂ)) P = 0 ∧ dirichletEval (ρ - (δ : ℂ)) P = 0 ∧
      (∀ d ∈ P.support.erase 0, monomialLog d ≤ reflectedPairFrequency m) ∧
      dirichletTailMass P σ =
        Real.sinh (δ * ((reflectedPairFrequency m + Real.log 2) / 2)) /
          Real.sinh (δ * ((reflectedPairFrequency m - Real.log 2) / 2)) :=
  ⟨reflectedPairAnnihilator σ δ m, sharpBinomialRoot σ,
    reflectedPairAnnihilator_constantCoeff σ δ m, sharpBinomialRoot_re σ,
    (reflectedPairAnnihilator_zeros σ hδ m).1, (reflectedPairAnnihilator_zeros σ hδ m).2,
    reflectedPairAnnihilator_frequency_bound σ δ m, reflectedPairAnnihilator_mass σ hδ m⟩

private theorem sinh_ratio_excess {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Real.sinh (x + u) / Real.sinh x =
      Real.exp u + 2 * Real.sinh u / (Real.exp (2 * x) - 1) := by
  have hs := (Real.sinh_pos_iff.mpr hx).ne'
  have he := (Real.exp_pos x).ne'
  have hnum : Real.sinh (x + u) =
      Real.exp u * Real.sinh x + Real.exp (-x) * Real.sinh u := by
    rw [Real.sinh_add]
    simp only [Real.sinh_eq, Real.cosh_eq]
    ring
  have hden : Real.exp (2 * x) - 1 = 2 * Real.exp x * Real.sinh x := by
    rw [Real.sinh_eq, show 2 * x = x + x by ring, Real.exp_add, Real.exp_neg]
    field_simp
  rw [hnum, hden, Real.exp_neg]
  field_simp


private theorem hyperbolic_cost_excess {δ a B : ℝ} (hδ : 0 < δ) (hB : a < B) :
    Real.sinh (δ * ((B + a) / 2)) / Real.sinh (δ * ((B - a) / 2)) =
      Real.exp (δ * a) + 2 * Real.sinh (δ * a) / (Real.exp (δ * (B - a)) - 1) := by
  have h := sinh_ratio_excess (mul_pos hδ (div_pos (sub_pos.mpr hB) two_pos)) (δ * a)
  rw [show δ * ((B - a) / 2) + δ * a = δ * ((B + a) / 2) by ring,
    show 2 * (δ * ((B - a) / 2)) = δ * (B - a) by ring] at h
  exact h

/-- Reflection imposes a strict mass excess over the one-root frequency floor. -/
theorem reflected_pair_mass_gt_single_root_floor {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hplus : dirichletEval (ρ + (δ : ℂ)) P = 0)
    (hminus : dirichletEval (ρ - (δ : ℂ)) P = 0) :
    Real.exp (δ * Real.log 2) < dirichletTailMass P ρ.re := by
  have hS : (P.support.erase 0).Nonempty := by
    have hm := one_le_dirichletTailMass_of_zero hP hplus
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp only [dirichletTailMass, hn, Finset.sum_empty] at hm
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hm
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (P.support.erase 0) monomialLog hS
  have hlo := log_two_le_monomialLog d (Finset.mem_erase.mp hd).1
  have hB : Real.log 2 < monomialLog d + 1 := by linarith only [hlo]
  have hc := reflected_pair_forces_hyperbolic_mass hP hδ hplus hminus
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hB (fun e he =>
      ⟨log_two_le_monomialLog e (Finset.mem_erase.mp he).1,
        (hmax e he).trans (by linarith)⟩)
  rw [hyperbolic_cost_excess hδ hB] at hc
  have hnum : 0 < 2 * Real.sinh (δ * Real.log 2) :=
    mul_pos two_pos (Real.sinh_pos_iff.mpr
      (mul_pos hδ (Real.log_pos (by norm_num : (1 : ℝ) < 2))))
  have hden : 0 < Real.exp (δ * (monomialLog d + 1 - Real.log 2)) - 1 := by
    have h := Real.exp_lt_exp.mpr (mul_pos hδ (sub_pos.mpr hB))
    simpa only [Real.exp_zero, sub_pos] using h
  exact (lt_add_of_pos_right _ (div_pos hnum hden)).trans_le hc

/-- The strict reflection excess has no uniform positive gap: explicit positive
one-prime polynomials approach the single-root floor at every separation. -/
theorem exists_reflected_pair_mass_near_single_root_floor
    (σ : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (P : MvPolynomial (Fin 2) ℝ≥0) (ρ : ℂ),
      MvPolynomial.constantCoeff P = 1 ∧ ρ.re = σ ∧
      dirichletEval (ρ + (δ : ℂ)) P = 0 ∧ dirichletEval (ρ - (δ : ℂ)) P = 0 ∧
      Real.exp (δ * Real.log 2) < dirichletTailMass P σ ∧
      dirichletTailMass P σ < Real.exp (δ * Real.log 2) + ε := by
  have hu : 0 < δ * Real.log 2 :=
    mul_pos hδ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * Real.sinh (δ * Real.log 2) / (ε * (δ * Real.log 2)))
  have hm' := (div_lt_iff₀ (mul_pos hε hu)).mp hm
  have hD : 0 < δ * (reflectedPairFrequency m - Real.log 2) :=
    mul_pos hδ (sub_pos.mpr (reflectedPairFrequency_gt m))
  have hE : 0 < Real.exp (δ * (reflectedPairFrequency m - Real.log 2)) - 1 := by
    have h := Real.exp_lt_exp.mpr hD
    simpa only [Real.exp_zero, sub_pos] using h
  have hfreq : (δ * Real.log 2) * (m : ℝ) ≤
      δ * (reflectedPairFrequency m - Real.log 2) := by
    have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    dsimp only [reflectedPairFrequency]
    push_cast
    nlinarith only [hu, mul_nonneg hu.le hn]
  have hexp := Real.add_one_le_exp (δ * (reflectedPairFrequency m - Real.log 2))
  have hbound : (δ * Real.log 2) * (m : ℝ) ≤
      Real.exp (δ * (reflectedPairFrequency m - Real.log 2)) - 1 := by
    linarith only [hfreq, hexp]
  have hsmall : 2 * Real.sinh (δ * Real.log 2) /
      (Real.exp (δ * (reflectedPairFrequency m - Real.log 2)) - 1) < ε := by
    apply (div_lt_iff₀ hE).mpr
    have hw := mul_le_mul_of_nonneg_left hbound hε.le
    nlinarith only [hm', hw]
  let P := reflectedPairAnnihilator σ δ m
  have hz := reflectedPairAnnihilator_zeros σ hδ m
  refine ⟨P, sharpBinomialRoot σ, reflectedPairAnnihilator_constantCoeff σ δ m,
    sharpBinomialRoot_re σ, hz.1, hz.2, ?_, ?_⟩
  · simpa only [sharpBinomialRoot_re] using reflected_pair_mass_gt_single_root_floor
      (reflectedPairAnnihilator_constantCoeff σ δ m) hδ hz.1 hz.2
  · change dirichletTailMass (reflectedPairAnnihilator σ δ m) σ < _
    rw [reflectedPairAnnihilator_mass σ hδ m,
      hyperbolic_cost_excess hδ (reflectedPairFrequency_gt m)]
    linarith only [hsmall]

private theorem scaled_sinh_slope (c : ℝ) :
    Tendsto (fun t : ℝ => Real.sinh (t * c) / t) (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  have hd : HasDerivAt (fun t : ℝ => Real.sinh (t * c)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).sinh
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine hd.congr fun t => ?_
  rw [slope_def_field]
  simp only [zero_mul, Real.sinh_zero, sub_zero, div_eq_inv_mul]

/-- Coalescing reflected zeros recover the double-zero frequency-span cost. -/
theorem tendsto_reflected_pair_cost_at_zero {a B : ℝ} (hB : a < B) :
    Tendsto (fun δ : ℝ => Real.sinh (δ * ((B + a) / 2)) /
      Real.sinh (δ * ((B - a) / 2))) (𝓝[≠] (0 : ℝ)) (𝓝 ((B + a) / (B - a))) := by
  have hh : (B - a) / 2 ≠ 0 := (div_pos (sub_pos.mpr hB) two_pos).ne'
  have hd := (scaled_sinh_slope ((B + a) / 2)).div (scaled_sinh_slope ((B - a) / 2)) hh
  rw [div_div_div_cancel_right₀ (two_ne_zero : (2 : ℝ) ≠ 0)] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact div_div_div_cancel_right₀ hδ _ _
private theorem exp_den_atTop {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    Tendsto (fun B : ℝ => Real.exp (δ * (B - a)) - 1) atTop atTop := by
  have hD : Tendsto (fun B : ℝ => δ * (B - a)) atTop atTop := by
    apply tendsto_atTop.2
    intro y
    filter_upwards [eventually_ge_atTop (a + y / δ)] with B hB
    have hd : y / δ ≤ B - a := by linarith only [hB]
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hd
  apply tendsto_atTop_mono _ hD
  intro B
  linarith only [Real.add_one_le_exp (δ * (B - a))]

private theorem excess_tendsto_zero {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    Tendsto (fun B : ℝ => Real.exp (δ * a) +
      2 * Real.sinh (δ * a) / (Real.exp (δ * (B - a)) - 1)) atTop (𝓝 (Real.exp (δ * a))) := by
  have h := (tendsto_inv_atTop_zero.comp (exp_den_atTop hδ a)).const_mul
    (2 * Real.sinh (δ * a))
  simpa only [Function.comp_def, mul_zero, add_zero, div_eq_mul_inv] using
    h.const_add (Real.exp (δ * a))

/-- The finite-bandwidth reflection cost approaches the one-root floor at infinite bandwidth. -/
theorem tendsto_reflected_pair_cost_atTop {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    Tendsto (fun B : ℝ => Real.sinh (δ * ((B + a) / 2)) /
      Real.sinh (δ * ((B - a) / 2))) atTop (𝓝 (Real.exp (δ * a))) := by
  refine (excess_tendsto_zero hδ a).congr' ?_
  filter_upwards [eventually_gt_atTop a] with B hB
  exact (hyperbolic_cost_excess hδ hB).symm

#print axioms tendsto_reflected_pair_cost_at_zero
#print axioms tendsto_reflected_pair_cost_atTop

#print axioms reflected_pair_mass_gt_single_root_floor
#print axioms exists_reflected_pair_mass_near_single_root_floor

#print axioms reflectedPairAnnihilator_zeros
#print axioms reflectedPairAnnihilator_mass
#print axioms exists_sharp_reflected_pair_annihilator

#print axioms reflected_pair_hyperbolic_moment
#print axioms reflected_pair_forces_hyperbolic_mass

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
