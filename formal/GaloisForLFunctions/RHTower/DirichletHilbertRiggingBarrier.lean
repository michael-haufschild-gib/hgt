import Mathlib.Analysis.PSeries
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The diagonal Hilbert-rigging barrier for Dirichlet superpositions

Suppose the coefficient state with magnitudes `(n+1)^(-sigma)` is placed in a weighted coefficient
Hilbert space with squared basis norms `w n`.  The formal summation vector `(1,1,...)` is a bounded
dual vector exactly when `sum (w n)^(-1)` converges, while the Dirichlet state belongs to the
Hilbert space exactly when `sum w n * (n+1)^(-2 sigma)` converges.

This file proves that some positive diagonal weight can satisfy both requirements if and only if
`sigma > 1`.  Thus no choice of positive diagonal rigging turns analytic continuation in the
critical strip into a normal Hilbert-space matrix coefficient.  Changing finitely many signs, as
in a diagonal Pontryagin/Krein superspace, does not alter this underlying Hilbert-topology barrier.
-/

noncomputable section

namespace GaloisForLFunctions

open Filter

/-- Magnitude of the `n`th Dirichlet coefficient, indexed from `n+1`. -/
def dirichletMagnitude (sigma : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ (-sigma)

/-- Existence of a positive diagonal Hilbert rigging in which both the Dirichlet coefficient state
and the all-ones summation covector are normal. -/
def AdmitsDiagonalHilbertRigging (sigma : ℝ) : Prop :=
  ∃ w : ℕ → ℝ,
    (∀ n, 0 < w n) ∧
    Summable (fun n => (w n)⁻¹) ∧
    Summable (fun n => w n * dirichletMagnitude sigma n ^ 2)

private theorem two_mul_le_weighted_sq_add_inv
    {w a : ℝ} (hw : 0 < w) :
    2 * a ≤ w * a ^ 2 + w⁻¹ := by
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  have hsquare := sq_nonneg (w * a - 1)
  apply (mul_le_mul_iff_of_pos_right hw).1
  nlinarith

/-- Weighted `ℓ²` membership of a state and its all-ones dual forces the coefficient sequence into
`ℓ¹`.  This is the exact Cauchy--Schwarz obstruction behind the rigging barrier. -/
theorem summable_of_weighted_rigging
    (a w : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hw : ∀ n, 0 < w n)
    (hdual : Summable fun n => (w n)⁻¹)
    (hstate : Summable fun n => w n * a n ^ 2) :
    Summable a := by
  have hmajor : Summable (fun n => w n * a n ^ 2 + (w n)⁻¹) := hstate.add hdual
  have htwo : Summable (fun n => 2 * a n) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (by norm_num) (ha n)
    · intro n
      exact two_mul_le_weighted_sq_add_inv (hw n)
    · exact hmajor
  exact (summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).mp htwo

/-- The coefficient magnitudes themselves are summable exactly to the right of the classical
Dirichlet abscissa `sigma = 1`. -/
theorem summable_dirichletMagnitude_iff (sigma : ℝ) :
    Summable (dirichletMagnitude sigma) ↔ 1 < sigma := by
  have heq : dirichletMagnitude sigma =
      fun n : ℕ => 1 / |(n : ℝ) + 1| ^ sigma := by
    funext n
    change ((n : ℝ) + 1) ^ (-sigma) = 1 / |(n : ℝ) + 1| ^ sigma
    rw [Real.rpow_neg (by positivity)]
    rw [abs_of_pos (by positivity)]
    simp [one_div]
  rw [heq]
  exact Real.summable_one_div_nat_add_rpow 1 sigma

/-- The all-ones summation source has infinite Sobolev order relative to the arithmetic clock
`H e_n = log n e_n`: no finite power of the clock supplies a square-summable dual weight. -/
theorem nat_log_pow_recip_not_summable (k : ℕ) :
    ¬ Summable (fun n : ℕ => (1 / (Real.log (n : ℝ)) ^ k : ℝ)) := by
  intro hlog
  have hgrowth : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ k‖ ≤ 1 * ‖x‖ :=
    Real.isLittleO_pow_log_id_atTop.bound one_pos
  have hnat : ∀ᶠ n : ℕ in atTop, ‖Real.log (n : ℝ) ^ k‖ ≤ 1 * ‖(n : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hgrowth
  have hharm : Summable (fun n : ℕ => (1 / (n : ℝ) : ℝ)) := by
    apply Summable.of_norm_bounded_eventually hlog
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hnat, eventually_gt_atTop 1] with n hn hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn1)
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    have hpowpos : 0 < Real.log (n : ℝ) ^ k := pow_pos hlogpos _
    have hle : Real.log (n : ℝ) ^ k ≤ (n : ℝ) := by
      simpa [Real.norm_of_nonneg (pow_nonneg hlogpos.le k), Real.norm_of_nonneg hnpos.le] using hn
    rw [Real.norm_of_nonneg (one_div_nonneg.mpr hnpos.le)]
    exact one_div_le_one_div_of_le hpowpos hle
  exact Real.not_summable_one_div_natCast hharm

/-- **Sharp rigging barrier.** A positive diagonal Hilbert scale can make both the Dirichlet state
and the all-ones summation covector normal if and only if `sigma > 1`. -/
theorem admitsDiagonalHilbertRigging_iff (sigma : ℝ) :
    AdmitsDiagonalHilbertRigging sigma ↔ 1 < sigma := by
  constructor
  · rintro ⟨w, hw, hdual, hstate⟩
    apply (summable_dirichletMagnitude_iff sigma).mp
    exact summable_of_weighted_rigging (dirichletMagnitude sigma) w
      (fun n => by unfold dirichletMagnitude; positivity) hw hdual hstate
  · intro hsigma
    let w : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ sigma
    refine ⟨w, ?_, ?_, ?_⟩
    · intro n
      dsimp [w]
      positivity
    · have hsum := (summable_dirichletMagnitude_iff sigma).2 hsigma
      apply hsum.congr
      intro n
      dsimp [w, dirichletMagnitude]
      rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))]
    · have hsum := (summable_dirichletMagnitude_iff sigma).2 hsigma
      apply hsum.congr
      intro n
      dsimp [w, dirichletMagnitude]
      have hn : 0 < (n + 1 : ℝ) := by positivity
      rw [← Real.rpow_mul_natCast hn.le]
      rw [← Real.rpow_add hn]
      congr 1
      ring

section Bessel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A uniform Bessel bound for a countable family of Hilbert-space modes. -/
def HasBesselBound (u : ℕ → E) (B : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : E),
    ∑ i ∈ s, ‖inner ℂ (u i) x‖ ^ 2 ≤ B * ‖x‖ ^ 2

/-- A Bessel family can have unit response against one vector on only finitely much total mass. -/
theorem card_le_of_bessel_unit_response
    (u : ℕ → E) (B : ℝ) (hB : HasBesselBound u B)
    (s : Finset ℕ) (y : E) (hy : ∀ i ∈ s, inner ℂ (u i) y = 1) :
    (s.card : ℝ) ≤ B * ‖y‖ ^ 2 := by
  calc
    (s.card : ℝ) = ∑ i ∈ s, (1 : ℝ) := by simp
    _ = ∑ i ∈ s, ‖inner ℂ (u i) y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hy i hi]
      norm_num
    _ ≤ B * ‖y‖ ^ 2 := hB s y

/-- **Non-diagonal normality barrier.** No infinite Bessel family admits a bounded Hilbert vector
whose inner product with every mode is one. Hence abandoning diagonal weights is insufficient if
the coefficient modes must still form a stably synthesizable quantum frame. -/
theorem no_bessel_family_with_unit_response
    (u : ℕ → E) (B : ℝ) (hB : HasBesselBound u B) :
    ¬ ∃ y : E, ∀ i, inner ℂ (u i) y = 1 := by
  rintro ⟨y, hy⟩
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (B * ‖y‖ ^ 2)
  have hle := card_le_of_bessel_unit_response u B hB (Finset.range N) y
    (fun i _hi => hy i)
  simp only [Finset.card_range] at hle
  exact (not_le_of_gt hN) hle

/-- A Bessel family cannot have the same nonzero matrix coefficient against every mode. This is
the orthogonal-complement engine behind density of the graph of the unbounded summation relation. -/
theorem bessel_constant_response_eq_zero
    (u : ℕ → E) (B : ℝ) (hB : HasBesselBound u B)
    (y : E) (c : ℂ) (hy : ∀ i, inner ℂ (u i) y = c) :
    c = 0 := by
  by_contra hc
  apply no_bessel_family_with_unit_response u B hB
  refine ⟨c⁻¹ • y, ?_⟩
  intro i
  rw [inner_smul_right, hy i]
  exact inv_mul_cancel₀ hc

end Bessel

end GaloisForLFunctions
