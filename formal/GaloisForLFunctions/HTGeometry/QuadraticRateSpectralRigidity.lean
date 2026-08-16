import GaloisForLFunctions.HTGeometry.SpectralRelationOrbitPolynomial
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Quadratic-rate rigidity of a spectral action

A *quadratic-rate identity* asserts that the square of a fixed linear spectral action equals a
multiple of the Hilbert--Schmidt rate `D⁻¹Tr(H²) = D⁻¹∑E_j²`.  On the traceless hyperplane the
left side is a rank-one quadratic form and the right side is a multiple of the Euclidean form, so
for at least three levels the identity forces both the multiple and the action to vanish.

The identity is only ever available on an open patch, so the localisation step is done first:
along every hyperplane direction the defect is a quadratic polynomial in the line parameter, and
three points of a line kill its leading coefficient.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I]

/-- The quadratic-rate defect of a spectral action: the square of the action minus the given
multiple of the Hilbert--Schmidt rate. -/
def quadraticRateDefect (c : I → ℝ) (κ : ℝ) (E : I → ℝ) : ℝ :=
  (∑ i, c i * E i) ^ 2 - κ * ∑ i, E i ^ 2

/-! ## Localisation along a line -/

/-- The defect along a line is a quadratic polynomial whose leading coefficient is the defect of
the direction. -/
theorem quadraticRateDefect_affine (c : I → ℝ) (κ : ℝ) (p E : I → ℝ) (s : ℝ) :
    quadraticRateDefect c κ (fun i => p i + s * E i)
      = quadraticRateDefect c κ p
        + s * (2 * (∑ i, c i * p i) * (∑ i, c i * E i) - 2 * κ * ∑ i, p i * E i)
        + s ^ 2 * quadraticRateDefect c κ E := by
  have h1 : (∑ i, c i * (p i + s * E i)) = (∑ i, c i * p i) + s * ∑ i, c i * E i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i, (p i + s * E i) ^ 2)
      = (∑ i, p i ^ 2) + 2 * s * (∑ i, p i * E i) + s ^ 2 * ∑ i, E i ^ 2 := by
    rw [show (∑ i, p i ^ 2) + 2 * s * (∑ i, p i * E i) + s ^ 2 * ∑ i, E i ^ 2
        = ∑ i, (p i ^ 2 + 2 * s * (p i * E i) + s ^ 2 * E i ^ 2) from by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [quadraticRateDefect]
  rw [h1, h2]
  ring

/-- Three points of one line kill the leading coefficient. -/
theorem quadraticRateDefect_eq_zero_of_symmetric_pair (c : I → ℝ) (κ : ℝ) (p E : I → ℝ)
    {s : ℝ} (hs : s ≠ 0) (h0 : quadraticRateDefect c κ p = 0)
    (hplus : quadraticRateDefect c κ (fun i => p i + s * E i) = 0)
    (hminus : quadraticRateDefect c κ (fun i => p i + (-s) * E i) = 0) :
    quadraticRateDefect c κ E = 0 := by
  rw [quadraticRateDefect_affine c κ p E s, h0, zero_add] at hplus
  rw [quadraticRateDefect_affine c κ p E (-s), h0, zero_add] at hminus
  have hsum : 2 * s ^ 2 * quadraticRateDefect c κ E = 0 := by
    have : (-s) ^ 2 = s ^ 2 := by ring
    rw [this] at hminus
    linarith
  have hs2 : (s : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  rcases mul_eq_zero.mp hsum with h | h
  · exact absurd h (by positivity)
  · exact h

omit [Fintype I] in
/-- Every direction is reachable symmetrically inside a neighbourhood. -/
theorem exists_symmetric_pair_of_mem_nhds (p E : I → ℝ) {S : Set (I → ℝ)} (hS : S ∈ nhds p) :
    ∃ s : ℝ, s ≠ 0 ∧ (fun i => p i + s * E i) ∈ S ∧ (fun i => p i + (-s) * E i) ∈ S := by
  have hcont : Continuous fun t : ℝ => (fun i => p i + t * E i) :=
    continuous_pi fun i => continuous_const.add (continuous_id.mul continuous_const)
  have hzero : (fun i => p i + (0 : ℝ) * E i) = p := by
    funext i; ring
  have hpre : (fun t : ℝ => (fun i => p i + t * E i)) ⁻¹' S ∈ nhds (0 : ℝ) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rwa [hzero]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε / 2, by positivity, hball ?_, hball ?_⟩
  · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0:ℝ) < ε / 2)]
    linarith
  · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg,
      abs_of_pos (by positivity : (0:ℝ) < ε / 2)]
    linarith

/-- **Localisation.**  A quadratic-rate identity on a neighbourhood of one traceless point holds
on the whole traceless hyperplane. -/
theorem quadraticRateDefect_eq_zero_of_nhds (c : I → ℝ) (κ : ℝ) (p : I → ℝ)
    {S : Set (I → ℝ)} (hS : S ∈ nhds p) (hzero : ∀ q ∈ S, quadraticRateDefect c κ q = 0) :
    ∀ E : I → ℝ, quadraticRateDefect c κ E = 0 := by
  intro E
  obtain ⟨s, hs, hp, hm⟩ := exists_symmetric_pair_of_mem_nhds p E hS
  exact quadraticRateDefect_eq_zero_of_symmetric_pair c κ p E hs
    (hzero p (mem_of_mem_nhds hS)) (hzero _ hp) (hzero _ hm)

/-! ## The two-level test directions -/

variable [DecidableEq I]

/-- The traceless direction supported on one pair of levels. -/
def levelPairDirection (i j : I) : I → ℝ :=
  fun x => (if x = i then 1 else 0) - (if x = j then 1 else 0)

theorem sum_levelPairDirection (i j : I) : ∑ x, levelPairDirection (I := I) i j x = 0 := by
  simp [levelPairDirection, Finset.sum_sub_distrib]

theorem sum_mul_levelPairDirection (c : I → ℝ) (i j : I) :
    ∑ x, c x * levelPairDirection (I := I) i j x = c i - c j := by
  simp only [levelPairDirection, mul_sub, Finset.sum_sub_distrib]
  simp

theorem sum_sq_levelPairDirection {i j : I} (hij : i ≠ j) :
    ∑ x, levelPairDirection (I := I) i j x ^ 2 = 2 := by
  have hval : ∀ x : I, levelPairDirection (I := I) i j x ^ 2
      = (if x = i then (1:ℝ) else 0) + (if x = j then (1:ℝ) else 0) := by
    intro x
    have hji : ¬ (j = i) := fun hh => hij hh.symm
    by_cases hx : x = i
    · simp [levelPairDirection, hx, hij]
    · by_cases hy : x = j
      · simp [levelPairDirection, hy, hji]
      · simp [levelPairDirection, hx, hy]
  rw [Finset.sum_congr rfl fun x _ => hval x, Finset.sum_add_distrib]
  simp
  norm_num

/-- The quadratic-rate defect on a two-level direction. -/
theorem quadraticRateDefect_levelPairDirection (c : I → ℝ) (κ : ℝ) {i j : I} (hij : i ≠ j) :
    quadraticRateDefect c κ (levelPairDirection (I := I) i j) = (c i - c j) ^ 2 - 2 * κ := by
  rw [quadraticRateDefect, sum_mul_levelPairDirection c i j, sum_sq_levelPairDirection hij]
  ring

/-! ## Rigidity -/

/-- **Quadratic-rate rigidity.**  For a spectral packet of at least three levels, no square of a
zero-sum spectral action is a multiple of the Hilbert--Schmidt rate. -/
theorem quadraticRate_traceless_rigidity (hcard : 3 ≤ Fintype.card I) (c : I → ℝ) (κ : ℝ)
    (hsum : ∑ i, c i = 0)
    (h : ∀ E : I → ℝ, ∑ i, E i = 0 → quadraticRateDefect c κ E = 0) :
    κ = 0 ∧ c = 0 := by
  obtain ⟨t, -, ht3⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I)) (n := 3)
    (by simpa using hcard)
  obtain ⟨i, j, l, hij, hil, hjl, -⟩ := Finset.card_eq_three.mp ht3
  have hpair : ∀ x y : I, x ≠ y → (c x - c y) ^ 2 = 2 * κ := by
    intro x y hxy
    have := h (levelPairDirection (I := I) x y) (sum_levelPairDirection x y)
    rw [quadraticRateDefect_levelPairDirection c κ hxy] at this
    linarith
  -- three pairwise differences of one triple force the multiple to vanish
  have hu : (c i - c j) ^ 2 = 2 * κ := hpair i j hij
  have hv : (c i - c l) ^ 2 = 2 * κ := hpair i l hil
  have hw : (c j - c l) ^ 2 = 2 * κ := hpair j l hjl
  have hprod : (c i - c l) * (c j - c l) = κ := by nlinarith [hu, hv, hw]
  have hkappa : κ = 0 := by nlinarith [hv, hw, hprod]
  refine ⟨hkappa, ?_⟩
  -- with a vanishing multiple every level difference vanishes
  have hconst : ∀ x y : I, c x = c y := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy]
    · have := hpair x y hxy
      rw [hkappa] at this
      have hzero : (c x - c y) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
      linarith
  have hne : Nonempty I := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨i₀⟩ := hne
  have hsum' : (Fintype.card I : ℝ) * c i₀ = 0 := by
    rw [← hsum]
    rw [Finset.sum_congr rfl fun x _ => hconst x i₀]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcardne : (Fintype.card I : ℝ) ≠ 0 := by
    have : 0 < Fintype.card I := by omega
    positivity
  have hi₀ : c i₀ = 0 := by
    rcases mul_eq_zero.mp hsum' with h' | h'
    · exact absurd h' hcardne
    · exact h'
  funext x
  rw [hconst x i₀, hi₀]
  rfl

/-- **Quadratic-rate rigidity, local form.**  A quadratic-rate identity valid only near one
traceless point already forces the multiple and the action to vanish. -/
theorem quadraticRate_traceless_rigidity_of_nhds (hcard : 3 ≤ Fintype.card I) (c : I → ℝ) (κ : ℝ)
    (hsum : ∑ i, c i = 0) (p : I → ℝ) {S : Set (I → ℝ)} (hS : S ∈ nhds p)
    (hzero : ∀ q ∈ S, quadraticRateDefect c κ q = 0) :
    κ = 0 ∧ c = 0 :=
  quadraticRate_traceless_rigidity hcard c κ hsum
    fun E _ => quadraticRateDefect_eq_zero_of_nhds c κ p hS hzero E

end GaloisForLFunctions.HTGeometry

end
