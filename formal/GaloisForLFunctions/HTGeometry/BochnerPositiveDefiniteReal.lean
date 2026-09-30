import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Bochner's theorem on the real line

A continuous positive-definite function `φ : ℝ → ℂ` (in the finite-matrix sense
`PositiveDefiniteOnReal`) is the characteristic function of a finite positive measure:
`φ t = ∫ e^{itx} dμ(x)` (`exists_charFun_eq_of_positiveDefinite`).

**Construction.**  For a mesh `h > 0` and a window length `N`, the lattice Fejér density
`g(x) = h/(2π(N+1)) · Σ_{j,k ≤ N} e^{ijhx} φ((k-j)h) e^{-ikhx}` on `[-π/h, π/h]` is a value of the
positive-definite quadratic form at the vectors `(e^{-ijhx})_j`, hence nonnegative.  Its moments at
the lattice frequencies are the Fejér means `(1 - |m|/(N+1)) φ(mh)`.  With `h = 2^{-n}` and
`N = 4^n` these measures are tight: the Fejér kernel `|Σ_{a ≤ K} e^{iaθ}|² ≤ π²/θ²` converts
continuity of `φ` at `0` into a uniform bound on the mass outside `[-R, R]`.  Prokhorov's theorem
gives a limit measure, whose characteristic function agrees with `φ` at every dyadic point, and
hence everywhere by continuity.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate BigOperators Real ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {φ : ℝ → ℂ}

/-! ### Positive-definite basics -/

theorem PositiveDefiniteOnReal.re_nonneg_im_eq_zero (hφ : PositiveDefiniteOnReal φ) {N : ℕ}
    (t : Fin N → ℝ) (c : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j, star (c i) * φ (t j - t i) * c j).re ∧
      (∑ i, ∑ j, star (c i) * φ (t j - t i) * c j).im = 0 := by
  obtain ⟨r, hr, hsum⟩ := hφ N t c
  rw [hsum]
  simp [hr]

/-- A positive-definite quadratic form over `range (N+1)` is real and nonnegative. -/
theorem PositiveDefiniteOnReal.range_form (hφ : PositiveDefiniteOnReal φ) (N : ℕ) (t : ℕ → ℝ)
    (c : ℕ → ℂ) :
    0 ≤ (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        star (c i) * φ (t j - t i) * c j).re ∧
      (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        star (c i) * φ (t j - t i) * c j).im = 0 := by
  have h := hφ.re_nonneg_im_eq_zero (N := N + 1) (fun i => t i) (fun i => c i)
  simpa only [Finset.sum_range] using h

theorem PositiveDefiniteOnReal.zero (hφ : PositiveDefiniteOnReal φ) :
    0 ≤ (φ 0).re ∧ (φ 0).im = 0 := by
  have h := hφ.re_nonneg_im_eq_zero (N := 1) (fun _ => 0) (fun _ => 1)
  simpa using h

/-- The `2 × 2` form at the points `0, s`. -/
theorem PositiveDefiniteOnReal.two_form (hφ : PositiveDefiniteOnReal φ) (s : ℝ) (a b : ℂ) :
    0 ≤ (star a * φ 0 * a + star a * φ s * b + star b * φ (-s) * a + star b * φ 0 * b).re ∧
      (star a * φ 0 * a + star a * φ s * b + star b * φ (-s) * a + star b * φ 0 * b).im = 0 := by
  have h := hφ.re_nonneg_im_eq_zero (N := 2) ![0, s] ![a, b]
  simpa [Fin.sum_univ_two, add_assoc] using h

/-- Hermitian symmetry `φ(-s) = conj φ(s)`. -/
theorem PositiveDefiniteOnReal.neg (hφ : PositiveDefiniteOnReal φ) (s : ℝ) :
    φ (-s) = conj (φ s) := by
  have h1 := (hφ.two_form s 1 1).2
  have h2 := (hφ.two_form s 1 I).2
  have h0 := hφ.zero.2
  simp only [star_one, one_mul, mul_one, Complex.add_im] at h1
  simp [Complex.mul_im, Complex.mul_re] at h2
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

/-- `|φ(s)| ≤ φ(0)`. -/
theorem PositiveDefiniteOnReal.norm_le (hφ : PositiveDefiniteOnReal φ) (s : ℝ) :
    ‖φ s‖ ≤ (φ 0).re := by
  have hneg := hφ.neg s
  have h00 := hφ.zero
  set p : ℝ := (φ 0).re with hp
  have hφ0 : φ 0 = (p : ℂ) := Complex.ext (by simp [hp]) (by simp [h00.2])
  -- the form at `(1, b)` with `b = -r conj φ(s)`
  have key : ∀ r : ℝ, 0 ≤ r → 0 ≤ p * (1 + r ^ 2 * ‖φ s‖ ^ 2) - 2 * r * ‖φ s‖ ^ 2 := by
    intro r hr
    have h := (hφ.two_form s 1 (-(r : ℂ) * conj (φ s))).1
    rw [hneg, hφ0] at h
    have hmul : φ s * conj (φ s) = (‖φ s‖ : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have hmul' : conj (φ s) * φ s = (‖φ s‖ : ℂ) ^ 2 := by rw [mul_comm, hmul]
    have e : (star (1 : ℂ) * (p : ℂ) * 1 + star 1 * φ s * (-(r : ℂ) * conj (φ s)) +
        star (-(r : ℂ) * conj (φ s)) * conj (φ s) * 1 +
        star (-(r : ℂ) * conj (φ s)) * (p : ℂ) * (-(r : ℂ) * conj (φ s))) =
        ((p * (1 + r ^ 2 * ‖φ s‖ ^ 2) - 2 * r * ‖φ s‖ ^ 2 : ℝ) : ℂ) := by
      simp only [star_one, one_mul, mul_one, star_mul', star_neg, Complex.star_def,
        Complex.conj_ofReal, Complex.conj_conj]
      push_cast
      linear_combination (-(r : ℂ)) * hmul - (r : ℂ) * hmul' + ((p : ℂ) * r ^ 2) * hmul'
    rw [e, Complex.ofReal_re] at h
    exact h
  rcases eq_or_lt_of_le h00.1 with hp0 | hp0
  · -- `φ(0) = 0` forces `φ(s) = 0`
    have := key 1 zero_le_one
    rw [← hp0] at this
    have hn : ‖φ s‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖φ s‖ = 0 := by nlinarith [norm_nonneg (φ s)]
    rw [this, ← hp0]
  · have := key (1 / p) (by positivity)
    have hp' : p ≠ 0 := hp0.ne'
    have h2 : ‖φ s‖ ^ 2 ≤ p ^ 2 := by
      have e : p * (1 + (1 / p) ^ 2 * ‖φ s‖ ^ 2) - 2 * (1 / p) * ‖φ s‖ ^ 2 =
          (p ^ 2 - ‖φ s‖ ^ 2) / p := by field_simp; ring
      rw [e] at this
      have := (div_nonneg_iff.mp this)
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · linarith
    nlinarith [norm_nonneg (φ s)]

namespace Bochner

/-! ### Exponential integrals over one lattice period -/

/-- `∫_{-π/h}^{π/h} e^{imhx} dx = 2π/h · [m = 0]` for an integer `m`. -/
theorem integral_exp_lattice (h : ℝ) (hh : 0 < h) (m : ℤ) :
    ∫ x in (-π / h)..(π / h), cexp (I * (((m : ℝ) * h * x : ℝ) : ℂ)) =
      if m = 0 then ((2 * π / h : ℝ) : ℂ) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      intervalIntegral.integral_const]
    rw [Complex.real_smul, mul_one]
    push_cast
    ring
  · have hc : I * ((m : ℂ) * h) ≠ 0 := by
      refine mul_ne_zero I_ne_zero (mul_ne_zero ?_ ?_)
      · exact_mod_cast hm
      · exact_mod_cast hh.ne'
    have e : ∀ x : ℝ, cexp (I * (((m : ℝ) * h * x : ℝ) : ℂ)) = cexp (I * ((m : ℂ) * h) * x) := by
      intro x; congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have h1 : I * ((m : ℂ) * h) * ((π / h : ℝ) : ℂ) = ((m * π : ℝ) : ℂ) * I := by
      push_cast; field_simp
    have h2 : I * ((m : ℂ) * h) * ((-π / h : ℝ) : ℂ) = ((-(m * π) : ℝ) : ℂ) * I := by
      push_cast; field_simp
    rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.sin_int_mul_pi m]
    simp

/-! ### The lattice Fejér density -/

variable (φ) in
/-- The lattice Fejér density `h/(2π(N+1)) Σ_{j,k ≤ N} e^{ijhx} φ((k-j)h) e^{-ikhx}`. -/
def fejerDensity (h : ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  ((h / (2 * π * (N + 1)) : ℝ) : ℂ) *
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      star (cexp (-(I * (((j : ℝ) * h * x : ℝ) : ℂ)))) * φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (-(I * (((k : ℝ) * h * x : ℝ) : ℂ)))

/-- The Fejér density is real and nonnegative. -/
theorem fejerDensity_nonneg (hφ : PositiveDefiniteOnReal φ) {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    (x : ℝ) : 0 ≤ (fejerDensity φ h N x).re ∧ (fejerDensity φ h N x).im = 0 := by
  obtain ⟨h1, h2⟩ := hφ.range_form N (fun j => (j : ℝ) * h)
    (fun j => cexp (-(I * (((j : ℝ) * h * x : ℝ) : ℂ))))
  set S := ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      star (cexp (-(I * (((j : ℝ) * h * x : ℝ) : ℂ)))) * φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (-(I * (((k : ℝ) * h * x : ℝ) : ℂ))) with hS
  have hc : 0 ≤ h / (2 * π * (N + 1)) := by positivity
  rw [fejerDensity, ← hS, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  exact ⟨mul_nonneg hc h1, by rw [h2, mul_zero]⟩

/-- Summing an integer-indexed Kronecker delta over `range (N+1)`. -/
theorem sum_range_ite_intCast_eq (N : ℕ) (a : ℤ) (c : ℂ) :
    ∑ k ∈ Finset.range (N + 1), (if (k : ℤ) = a then c else 0) =
      if 0 ≤ a ∧ a ≤ N then c else 0 := by
  split_ifs with ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha.1
    have hn : n ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]; have := ha.2; omega
    simp only [Nat.cast_inj]
    rw [Finset.sum_ite_eq' (Finset.range (N + 1)) n (fun _ => c), if_pos hn]
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg]
    rintro rfl
    rw [Finset.mem_range] at hk
    exact ha ⟨by positivity, by omega⟩

/-- The number of lattice pairs `(j, j + l)` in `[0, N]²`. -/
def pairCount (N : ℕ) (l : ℤ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun j : ℕ => 0 ≤ (j : ℤ) + l ∧ (j : ℤ) + l ≤ N)).card

theorem pairCount_le (N : ℕ) (l : ℤ) : pairCount N l ≤ N + 1 := by
  rw [pairCount]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem pairCount_ge (N : ℕ) (l : ℤ) : (N : ℝ) + 1 - |(l : ℝ)| ≤ pairCount N l := by
  rcases le_or_gt 0 l with hl | hl
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hl
    have hsub : Finset.range (N + 1 - a) ⊆
        (Finset.range (N + 1)).filter (fun j : ℕ => 0 ≤ (j : ℤ) + a ∧ (j : ℤ) + a ≤ N) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by positivity, by omega⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    rw [pairCount]
    push_cast
    rw [abs_of_nonneg (by positivity)]
    have : ((N + 1 - a : ℕ) : ℝ) ≥ (N : ℝ) + 1 - a := by
      rcases le_or_gt a (N + 1) with h | h
      · rw [Nat.cast_sub h]; push_cast; linarith
      · have : ((N + 1 - a : ℕ) : ℝ) ≥ 0 := Nat.cast_nonneg _
        have h' : (N : ℝ) + 1 < a := by exact_mod_cast h
        linarith
    exact le_trans this (by exact_mod_cast hc)
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, l = -(a : ℤ) := ⟨(-l).toNat, by omega⟩
    subst ha
    have hsub : (Finset.range (N + 1 - a)).image (fun j => j + a) ⊆
        (Finset.range (N + 1)).filter (fun j : ℕ => 0 ≤ (j : ℤ) + -(a : ℤ) ∧
          (j : ℤ) + -(a : ℤ) ≤ N) := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [Finset.mem_range] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by push_cast; omega, by push_cast; omega⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (add_left_injective a), Finset.card_range] at hc
    rw [pairCount]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have : ((N + 1 - a : ℕ) : ℝ) ≥ (N : ℝ) + 1 - a := by
      rcases le_or_gt a (N + 1) with h | h
      · rw [Nat.cast_sub h]; push_cast; linarith
      · have : ((N + 1 - a : ℕ) : ℝ) ≥ 0 := Nat.cast_nonneg _
        have h' : (N : ℝ) + 1 < a := by exact_mod_cast h
        linarith
    exact le_trans this (by exact_mod_cast hc)

/-- One term of the Fejér density times a lattice character. -/
theorem fejer_term_mul_exp (h x : ℝ) (j k : ℕ) (l : ℤ) :
    star (cexp (-(I * (((j : ℝ) * h * x : ℝ) : ℂ)))) * φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (-(I * (((k : ℝ) * h * x : ℝ) : ℂ))) * cexp (I * (((l : ℝ) * h * x : ℝ) : ℂ)) =
      φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (I * (((((j : ℤ) - k + l : ℤ) : ℝ) * h * x : ℝ) : ℂ)) := by
  have hstar : star (cexp (-(I * (((j : ℝ) * h * x : ℝ) : ℂ)))) =
      cexp (I * (((j : ℝ) * h * x : ℝ) : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [hstar]
  calc cexp (I * (((j : ℝ) * h * x : ℝ) : ℂ)) * φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (-(I * (((k : ℝ) * h * x : ℝ) : ℂ))) * cexp (I * (((l : ℝ) * h * x : ℝ) : ℂ))
      = φ ((k : ℝ) * h - (j : ℝ) * h) * (cexp (I * (((j : ℝ) * h * x : ℝ) : ℂ)) *
        cexp (-(I * (((k : ℝ) * h * x : ℝ) : ℂ))) * cexp (I * (((l : ℝ) * h * x : ℝ) : ℂ))) := by
        ring
    _ = _ := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 2
        push_cast
        ring

/-- **Lattice moments of the Fejér density** are the Fejér means `(pairs/(N+1)) φ(lh)`. -/
theorem integral_fejerDensity_mul_exp {h : ℝ} (hh : 0 < h) (N : ℕ) (l : ℤ) :
    ∫ x in (-π / h)..(π / h), fejerDensity φ h N x * cexp (I * (((l : ℝ) * h * x : ℝ) : ℂ)) =
      (((pairCount N l : ℝ) / (N + 1) : ℝ) : ℂ) * φ ((l : ℝ) * h) := by
  have hcont : ∀ j k : ℕ, IntervalIntegrable (fun x : ℝ =>
      φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (I * (((((j : ℤ) - k + l : ℤ) : ℝ) * h * x : ℝ) : ℂ))) volume (-π / h) (π / h) := by
    intro j k
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  simp_rw [fejerDensity, mul_assoc (((h / (2 * π * (N + 1)) : ℝ) : ℂ)), Finset.sum_mul,
    fejer_term_mul_exp h _ _ _ l]
  rw [intervalIntegral.integral_const_mul]
  have hswap : ∫ x in (-π / h)..(π / h), ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (I * (((((j : ℤ) - k + l : ℤ) : ℝ) * h * x : ℝ) : ℂ)) =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∫ x in (-π / h)..(π / h), φ ((k : ℝ) * h - (j : ℝ) * h) *
          cexp (I * (((((j : ℤ) - k + l : ℤ) : ℝ) * h * x : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_finsetSum (f := fun (j : ℕ) (x : ℝ) => ∑ k ∈ Finset.range (N + 1),
      φ ((k : ℝ) * h - (j : ℝ) * h) *
        cexp (I * (((((j : ℤ) - k + l : ℤ) : ℝ) * h * x : ℝ) : ℂ)))
      (fun j _ => Continuous.intervalIntegrable
        (continuous_finsetSum _ fun k _ => by fun_prop) _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact intervalIntegral.integral_finsetSum (fun k _ => hcont j k)
  rw [hswap]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_lattice h hh]
  -- collapse the Kronecker deltas
  have hinner : ∀ j : ℕ, (∑ k ∈ Finset.range (N + 1), φ ((k : ℝ) * h - (j : ℝ) * h) *
      (if (j : ℤ) - k + l = 0 then ((2 * π / h : ℝ) : ℂ) else 0)) =
      if 0 ≤ (j : ℤ) + l ∧ (j : ℤ) + l ≤ N then φ ((l : ℝ) * h) * ((2 * π / h : ℝ) : ℂ) else 0 := by
    intro j
    rw [← sum_range_ite_intCast_eq N ((j : ℤ) + l) (φ ((l : ℝ) * h) * ((2 * π / h : ℝ) : ℂ))]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (j : ℤ) - k + l = 0
    · have hk' : (k : ℤ) = j + l := by omega
      rw [if_pos hk, if_pos hk']
      congr 2
      have : (k : ℝ) = (j : ℝ) + l := by exact_mod_cast hk'
      rw [this]; ring
    · have hk' : ¬ (k : ℤ) = j + l := by omega
      rw [if_neg hk, if_neg hk', mul_zero]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  rw [show ((Finset.range (N + 1)).filter
      (fun j : ℕ => 0 ≤ (j : ℤ) + l ∧ (j : ℤ) + l ≤ N)).card = pairCount N l from rfl]
  push_cast
  field_simp

theorem pairCount_zero (N : ℕ) : pairCount N 0 = N + 1 := by
  rw [pairCount, Finset.filter_true_of_mem, Finset.card_range]
  intro j hj
  rw [Finset.mem_range] at hj
  exact ⟨by positivity, by omega⟩

theorem continuous_fejerDensity (h : ℝ) (N : ℕ) : Continuous (fejerDensity φ h N) := by
  unfold fejerDensity
  refine continuous_const.mul (continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => ?_)
  fun_prop

/-! ### The lattice Fejér measure -/

variable (φ) in
/-- The lattice Fejér measure: the Fejér density on `(-π/h, π/h]`. -/
def fejerMeasure (h : ℝ) (N : ℕ) : Measure ℝ :=
  (volume.restrict (Ioc (-π / h) (π / h))).withDensity
    (fun x => ((fejerDensity φ h N x).re.toNNReal : ℝ≥0∞))

theorem integral_fejerMeasure (hφ : PositiveDefiniteOnReal φ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    (g : ℝ → ℂ) :
    ∫ x, g x ∂fejerMeasure φ h N = ∫ x in (-π / h)..(π / h), fejerDensity φ h N x * g x := by
  have hmeas : Measurable fun x => (fejerDensity φ h N x).re.toNNReal :=
    (Complex.continuous_re.comp (continuous_fejerDensity h N)).measurable.real_toNNReal
  rw [fejerMeasure, integral_withDensity_eq_integral_smul hmeas,
    intervalIntegral.integral_of_le (by
      have : 0 < π / h := by positivity
      rw [neg_div]; linarith)]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  obtain ⟨h1, h2⟩ := fejerDensity_nonneg hφ hh.le N x
  have e : fejerDensity φ h N x = (((fejerDensity φ h N x).re.toNNReal : ℝ) : ℂ) := by
    rw [Real.coe_toNNReal _ h1]
    exact Complex.ext (by simp) (by simp [h2])
  rw [NNReal.smul_def, Complex.real_smul, ← e]

/-- **Lattice values of the characteristic function** are the Fejér means. -/
theorem charFun_fejerMeasure (hφ : PositiveDefiniteOnReal φ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    (l : ℤ) :
    charFun (fejerMeasure φ h N) ((l : ℝ) * h) =
      (((pairCount N l : ℝ) / (N + 1) : ℝ) : ℂ) * φ ((l : ℝ) * h) := by
  rw [charFun_apply_real, integral_fejerMeasure hφ hh, ← integral_fejerDensity_mul_exp hh N l]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show fejerDensity φ h N x * cexp (((l : ℝ) * h : ℝ) * (x : ℂ) * I) =
    fejerDensity φ h N x * cexp (I * (((l : ℝ) * h * x : ℝ) : ℂ))
  congr 2
  push_cast
  ring

/-! ### The Fejér kernel -/

/-- The normalized Fejér kernel `|Σ_{a ≤ K} e^{iaθ}|²/(K+1)²`. -/
def fejerKernel (K : ℕ) (θ : ℝ) : ℝ :=
  ‖∑ a ∈ Finset.range (K + 1), cexp (I * (((a : ℝ) * θ : ℝ) : ℂ))‖ ^ 2 / ((K : ℝ) + 1) ^ 2

theorem fejerKernel_nonneg (K : ℕ) (θ : ℝ) : 0 ≤ fejerKernel K θ := by
  unfold fejerKernel; positivity

theorem fejerKernel_le_one (K : ℕ) (θ : ℝ) : fejerKernel K θ ≤ 1 := by
  unfold fejerKernel
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  rw [div_le_one (by positivity)]
  have hn : ‖∑ a ∈ Finset.range (K + 1), cexp (I * (((a : ℝ) * θ : ℝ) : ℂ))‖ ≤ (K : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    simp only [Complex.norm_exp_I_mul_ofReal, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    push_cast; rfl
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- Jordan's inequality in the form `|θ|/π ≤ |sin(θ/2)|` on `[-π, π]`. -/
theorem abs_div_pi_le_abs_sin_half {θ : ℝ} (hθ : |θ| ≤ π) : |θ| / π ≤ |Real.sin (θ / 2)| := by
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ π → x / π ≤ Real.sin (x / 2) := by
    intro x hx0 hxπ
    have := Real.mul_le_sin (x := x / 2) (by positivity) (by linarith)
    calc x / π = 2 / π * (x / 2) := by ring
      _ ≤ _ := this
  rcases le_or_gt 0 θ with h | h
  · rw [abs_of_nonneg h] at hθ ⊢
    exact (key θ h hθ).trans (le_abs_self _)
  · rw [abs_of_neg h] at hθ ⊢
    have := key (-θ) (by linarith) hθ
    rw [show -θ / 2 = -(θ / 2) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

/-- **Fejér decay:** `|Σ_{a ≤ K} e^{iaθ}| ≤ π/|θ|` for `0 < |θ| ≤ π`. -/
theorem norm_sum_exp_le {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : |θ| ≤ π) (K : ℕ) :
    ‖∑ a ∈ Finset.range (K + 1), cexp (I * (((a : ℝ) * θ : ℝ) : ℂ))‖ ≤ π / |θ| := by
  set z : ℂ := cexp (I * (θ : ℂ)) with hz
  have hsin : 0 < |Real.sin (θ / 2)| :=
    lt_of_lt_of_le (div_pos (abs_pos.mpr hθ0) Real.pi_pos) (abs_div_pi_le_abs_sin_half hθ)
  have hz1 : ‖z - 1‖ = 2 * |Real.sin (θ / 2)| := by
    rw [hz, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have hzne : z ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hz1; linarith
  have hpow : ∀ a : ℕ, cexp (I * (((a : ℝ) * θ : ℝ) : ℂ)) = z ^ a := by
    intro a; rw [hz, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  simp_rw [hpow]
  rw [geom_sum_eq hzne, norm_div, hz1]
  have hnum : ‖z ^ (K + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hz, Complex.norm_exp_I_mul_ofReal, one_pow, norm_one]; norm_num
  have hden : 2 * |θ| / π ≤ 2 * |Real.sin (θ / 2)| := by
    have := abs_div_pi_le_abs_sin_half hθ; rw [mul_div_assoc]; linarith
  calc ‖z ^ (K + 1) - 1‖ / (2 * |Real.sin (θ / 2)|) ≤ 2 / (2 * |θ| / π) := by
        gcongr
    _ = π / |θ| := by field_simp

theorem fejerKernel_le {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : |θ| ≤ π) (K : ℕ) :
    fejerKernel K θ ≤ π ^ 2 / (((K : ℝ) + 1) ^ 2 * θ ^ 2) := by
  unfold fejerKernel
  have hn := norm_sum_exp_le hθ0 hθ K
  have h2 : ‖∑ a ∈ Finset.range (K + 1), cexp (I * (((a : ℝ) * θ : ℝ) : ℂ))‖ ^ 2 ≤
      (π / |θ|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [div_pow, sq_abs] at h2
  calc _ ≤ π ^ 2 / θ ^ 2 / ((K : ℝ) + 1) ^ 2 := by gcongr
    _ = _ := by rw [div_div, mul_comm]

/-- The Fejér kernel as a double exponential sum. -/
theorem fejerKernel_eq_sum (K : ℕ) (θ : ℝ) :
    ((fejerKernel K θ : ℝ) : ℂ) = (1 / ((K : ℂ) + 1) ^ 2) *
      ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        cexp (I * (((((a : ℤ) - b : ℤ) : ℝ) * θ : ℝ) : ℂ)) := by
  set S := ∑ a ∈ Finset.range (K + 1), cexp (I * (((a : ℝ) * θ : ℝ) : ℂ)) with hS
  have hconj : conj S = ∑ b ∈ Finset.range (K + 1), cexp (-(I * (((b : ℝ) * θ : ℝ) : ℂ))) := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have hsq : ((‖S‖ ^ 2 : ℝ) : ℂ) = S * conj S := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold fejerKernel
  rw [← hS]
  push_cast
  rw [show ((‖S‖ : ℂ)) ^ 2 = ((‖S‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, hsq, hconj,
    Finset.sum_mul_sum, div_eq_mul_one_div, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem isFiniteMeasure_fejerMeasure (h : ℝ) (N : ℕ) : IsFiniteMeasure (fejerMeasure φ h N) := by
  have hc : Continuous fun x => (fejerDensity φ h N x).re :=
    Complex.continuous_re.comp (continuous_fejerDensity h N)
  have hint : IntegrableOn (fun x => (fejerDensity φ h N x).re) (Icc (-π / h) (π / h)) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have hint' : Integrable (fun x => (fejerDensity φ h N x).re)
      (volume.restrict (Ioc (-π / h) (π / h))) := hint.mono_set Ioc_subset_Icc_self
  exact isFiniteMeasure_withDensity_ofReal hint'.hasFiniteIntegral

theorem fejerMeasure_real_univ (hφ : PositiveDefiniteOnReal φ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    (fejerMeasure φ h N).real univ = (φ 0).re := by
  have := charFun_fejerMeasure hφ hh N 0
  rw [Int.cast_zero, zero_mul, charFun_zero, pairCount_zero] at this
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  rw [show ((N + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) = 1 by push_cast; field_simp, Complex.ofReal_one,
    one_mul] at this
  have := congrArg Complex.re this
  simpa using this

/-- **Integral of the Fejér kernel** against the Fejér measure. -/
theorem integral_fejerKernel_fejerMeasure (hφ : PositiveDefiniteOnReal φ) {h : ℝ} (hh : 0 < h)
    (N K : ℕ) :
    ∫ x, fejerKernel K (h * x) ∂fejerMeasure φ h N = (1 / ((K : ℝ) + 1) ^ 2) *
      ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        (pairCount N ((a : ℤ) - b) : ℝ) / (N + 1) * (φ ((((a : ℤ) - b : ℤ) : ℝ) * h)).re := by
  haveI := isFiniteMeasure_fejerMeasure (φ := φ) h N
  have hint : ∀ a b : ℕ, Integrable (fun x : ℝ =>
      cexp (I * (((((a : ℤ) - b : ℤ) : ℝ) * (h * x) : ℝ) : ℂ))) (fejerMeasure φ h N) := by
    intro a b
    refine Integrable.of_bound (C := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_I_mul_ofReal]
  have hcf : ∀ a b : ℕ, ∫ x, cexp (I * (((((a : ℤ) - b : ℤ) : ℝ) * (h * x) : ℝ) : ℂ))
      ∂fejerMeasure φ h N = (((pairCount N ((a : ℤ) - b) : ℝ) / (N + 1) : ℝ) : ℂ) *
        φ ((((a : ℤ) - b : ℤ) : ℝ) * h) := by
    intro a b
    rw [← charFun_fejerMeasure hφ hh N ((a : ℤ) - b), charFun_apply_real]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    congr 1; push_cast; ring
  have hc : ∫ x, ((fejerKernel K (h * x) : ℝ) : ℂ) ∂fejerMeasure φ h N =
      (1 / ((K : ℂ) + 1) ^ 2) * ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        (((pairCount N ((a : ℤ) - b) : ℝ) / (N + 1) : ℝ) : ℂ) *
          φ ((((a : ℤ) - b : ℤ) : ℝ) * h) := by
    simp_rw [fejerKernel_eq_sum]
    rw [integral_const_mul, integral_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ => hint a b]
    simp_rw [integral_finsetSum _ fun b _ => hint _ b, hcf]
  have hre := congrArg Complex.re hc
  rw [integral_complex_ofReal, Complex.ofReal_re] at hre
  rw [hre, show (1 / ((K : ℂ) + 1) ^ 2) = ((1 / ((K : ℝ) + 1) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.re_ofReal_mul]

theorem ae_mem_fejerMeasure (h : ℝ) (N : ℕ) :
    ∀ᵐ x ∂fejerMeasure φ h N, x ∈ Ioc (-π / h) (π / h) :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

/-- The Fejér mean bracket: `1 - (pairs/(N+1)) Re φ(mh) ≤ (1 - Re φ(mh)) + |m|/(N+1)`. -/
theorem fejer_bracket_le (hφ : PositiveDefiniteOnReal φ) (hφ0 : φ 0 = 1) (N : ℕ) (m : ℤ)
    (t : ℝ) :
    1 - (pairCount N m : ℝ) / (N + 1) * (φ t).re ≤ (1 - (φ t).re) + |(m : ℝ)| / (N + 1) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hr : (φ t).re ≤ 1 := by
    have := hφ.norm_le t
    rw [hφ0, Complex.one_re] at this
    exact (Complex.re_le_norm _).trans this
  have hr' : -1 ≤ (φ t).re := by
    have := hφ.norm_le t
    rw [hφ0, Complex.one_re] at this
    have := Complex.abs_re_le_norm (φ t)
    linarith [neg_abs_le (φ t).re]
  have hc1 : (pairCount N m : ℝ) / (N + 1) ≤ 1 := by
    rw [div_le_one hN]; exact_mod_cast pairCount_le N m
  have hc0 : 1 - |(m : ℝ)| / (N + 1) ≤ (pairCount N m : ℝ) / (N + 1) := by
    rw [le_div_iff₀ hN, sub_mul, div_mul_cancel₀ _ hN.ne', one_mul]
    exact pairCount_ge N m
  nlinarith

/-- **Tightness of the Fejér measures.**  If `φ(0) = 1` and `(K+1) h R ≥ 2π`, the mass outside
`[-R, R]` is at most `4/3` of the average Fejér bracket over `|a - b| ≤ K`. -/
theorem fejerMeasure_tail_le (hφ : PositiveDefiniteOnReal φ) (hφ0 : φ 0 = 1) {h : ℝ}
    (hh : 0 < h) (N K : ℕ) {R : ℝ} (hR : 0 < R) (hKR : 2 * π ≤ ((K : ℝ) + 1) * h * R) :
    3 / 4 * (fejerMeasure φ h N).real {x | R < |x|} ≤ (1 / ((K : ℝ) + 1) ^ 2) *
      ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        ((1 - (φ ((((a : ℤ) - b : ℤ) : ℝ) * h)).re) + |(((a : ℤ) - b : ℤ) : ℝ)| / (N + 1)) := by
  haveI := isFiniteMeasure_fejerMeasure (φ := φ) h N
  set ν := fejerMeasure φ h N with hν
  have hmass : ν.real univ = 1 := by rw [hν, fejerMeasure_real_univ hφ hh, hφ0, Complex.one_re]
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hFc : Continuous fun x : ℝ => fejerKernel K (h * x) := by
    unfold fejerKernel; fun_prop
  have hFint : Integrable (fun x : ℝ => fejerKernel K (h * x)) ν :=
    Integrable.of_bound (C := 1) hFc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (fejerKernel_nonneg K _)]; exact fejerKernel_le_one K _)
  have hSmeas : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const measurable_norm
  -- lower bound by the indicator
  have hlow : 3 / 4 * ν.real {x | R < |x|} ≤ ∫ x, (1 - fejerKernel K (h * x)) ∂ν := by
    rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const _ hSmeas]
    refine integral_mono_ae ((integrable_const _).indicator hSmeas)
      ((integrable_const 1).sub hFint) ?_
    filter_upwards [ae_mem_fejerMeasure (φ := φ) h N] with x hx
    by_cases hxS : x ∈ {x : ℝ | R < |x|}
    · rw [Set.indicator_of_mem hxS]
      have hxR : R < |x| := hxS
      have hθ0 : h * x ≠ 0 := mul_ne_zero hh.ne' (by intro h0; rw [h0, abs_zero] at hxR; linarith)
      have hθ : |h * x| ≤ π := by
        have hxa : |x| ≤ π / h := abs_le.mpr ⟨by rw [← neg_div]; exact hx.1.le, hx.2⟩
        rw [abs_mul, abs_of_pos hh]
        calc h * |x| ≤ h * (π / h) := by gcongr
          _ = π := by field_simp
      have hF := fejerKernel_le hθ0 hθ K
      have hbig : π ^ 2 / (((K : ℝ) + 1) ^ 2 * (h * x) ^ 2) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : (2 * π) ^ 2 ≤ (((K : ℝ) + 1) * h * R) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hKR 2
        have h2 : R ^ 2 ≤ x ^ 2 := by
          rw [← sq_abs x]; exact pow_le_pow_left₀ hR.le hxR.le 2
        have h3 : (((K : ℝ) + 1) * h * R) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 * (h * x) ^ 2 := by
          rw [show (((K : ℝ) + 1) * h * R) ^ 2 = (((K : ℝ) + 1) ^ 2 * h ^ 2) * R ^ 2 by ring,
            show ((K : ℝ) + 1) ^ 2 * (h * x) ^ 2 = (((K : ℝ) + 1) ^ 2 * h ^ 2) * x ^ 2 by ring]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        nlinarith
      linarith
    · rw [Set.indicator_of_notMem hxS]
      linarith [fejerKernel_le_one K (h * x)]
  have heq : ∫ x, (1 - fejerKernel K (h * x)) ∂ν = (1 / ((K : ℝ) + 1) ^ 2) *
      ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        (1 - (pairCount N ((a : ℤ) - b) : ℝ) / (N + 1) *
          (φ ((((a : ℤ) - b : ℤ) : ℝ) * h)).re) := by
    rw [integral_sub (integrable_const 1) hFint, integral_const, hmass, one_smul,
      integral_fejerKernel_fejerMeasure hφ hh N K]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, mul_sub]
    field_simp
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring_nf
  rw [heq] at hlow
  refine hlow.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
    Finset.sum_le_sum fun b _ => fejer_bracket_le hφ hφ0 N _ _) (by positivity))

/-! ### The dyadic Fejér sequence -/

theorem isProbabilityMeasure_fejerMeasure (hφ : PositiveDefiniteOnReal φ) (hφ0 : φ 0 = 1) {h : ℝ}
    (hh : 0 < h) (N : ℕ) : IsProbabilityMeasure (fejerMeasure φ h N) := by
  haveI := isFiniteMeasure_fejerMeasure (φ := φ) h N
  constructor
  have h1 := fejerMeasure_real_univ hφ hh N
  rw [hφ0, Complex.one_re] at h1
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ univ)]
  simp only [Measure.real] at h1
  rw [h1, ENNReal.ofReal_one]

/-- Outside `[-π/h, π/h]` the Fejér measure vanishes. -/
theorem fejerMeasure_tail_eq_zero {h : ℝ} (N : ℕ) {R : ℝ} (hR : π / h ≤ R) :
    fejerMeasure φ h N {x | R < |x|} = 0 := by
  rw [← compl_compl {x : ℝ | R < |x|}]
  refine measure_mono_null (fun x hx => ?_) (ae_mem_fejerMeasure (φ := φ) h N)
  simp only [mem_compl_iff, mem_setOf_eq, not_lt] at hx ⊢
  intro hmem
  have : |x| ≤ π / h := abs_le.mpr ⟨by rw [← neg_div]; exact hmem.1.le, hmem.2⟩
  exact hx (this.trans hR)

theorem dyadic_pos (n : ℕ) : (0 : ℝ) < 1 / 2 ^ n := by positivity

variable (φ) in
/-- The dyadic Fejér sequence: mesh `2^{-n}`, window `4^n`. -/
def fejerSeq (hφ : PositiveDefiniteOnReal φ) (hφ0 : φ 0 = 1) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨fejerMeasure φ (1 / 2 ^ n) (4 ^ n),
    isProbabilityMeasure_fejerMeasure hφ hφ0 (dyadic_pos n) _⟩

/-- **Uniform tightness of the dyadic Fejér sequence.** -/
theorem isTight_fejerSeq (hφ : PositiveDefiniteOnReal φ) (hφ0 : φ 0 = 1) (hc : Continuous φ) :
    IsTightMeasureSet {x | ∃ μ ∈ range (fejerSeq φ hφ hφ0), (μ : Measure ℝ) = x} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he0, hepos', he⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hepos : 0 < e := by
    by_contra h; push Not at h
    rw [ENNReal.ofReal_of_nonpos h] at hepos'; exact lt_irrefl _ hepos'
  -- continuity at `0`
  obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.mp hc.continuousAt (e / 4) (by positivity)
  have hbr : ∀ t : ℝ, |t| < δ → 1 - (φ t).re ≤ e / 4 := by
    intro t ht
    have := hδφ (x := t) (by rw [Real.dist_eq, sub_zero]; exact ht)
    rw [hφ0, dist_eq_norm] at this
    have h2 : 1 - (φ t).re = (1 - φ t).re := by simp
    rw [h2]
    exact ((Complex.re_le_norm _).trans (by rw [norm_sub_rev]; exact this.le))
  -- a dyadic threshold
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (1 / 2 : ℝ) ^ n₀ < min (δ / 4) (e / 8) :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  set R : ℝ := 4 * π / δ + 16 * π / e + π * 2 ^ n₀ with hRdef
  have hR0 : 0 < R := by positivity
  refine ⟨Icc (-R) R, isCompact_Icc, ?_⟩
  rintro μ ⟨ν, ⟨n, rfl⟩, rfl⟩
  have hcompl : (Icc (-R) R)ᶜ = {x : ℝ | R < |x|} := by
    ext x; simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, not_and_or, not_le, lt_abs]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; exact h
    · rintro (h | h)
      · right; exact h
      · left; linarith
  rw [hcompl]
  change fejerMeasure φ (1 / 2 ^ n) (4 ^ n) {x | R < |x|} ≤ ε
  rcases lt_or_ge n n₀ with hn | hn
  · -- small `n`: the measure lives inside `[-R, R]`
    rw [fejerMeasure_tail_eq_zero]
    · exact bot_le
    · have : π / (1 / 2 ^ n) = π * 2 ^ n := by field_simp
      rw [this]
      have h2 : (2 : ℝ) ^ n ≤ 2 ^ n₀ := pow_le_pow_right₀ (by norm_num) hn.le
      have : π * 2 ^ n ≤ π * 2 ^ n₀ := by gcongr
      rw [hRdef]; linarith [div_pos (mul_pos four_pos Real.pi_pos) hδ,
        div_pos (mul_pos (by norm_num : (0 : ℝ) < 16) Real.pi_pos) hepos]
  · -- large `n`: the Fejér tail bound
    set h : ℝ := 1 / 2 ^ n with hhdef
    have hh : 0 < h := dyadic_pos n
    haveI := isFiniteMeasure_fejerMeasure (φ := φ) h (4 ^ n)
    have hhle : h < δ / 4 ∧ h < e / 8 := by
      have h1 : h = (1 / 2 : ℝ) ^ n := by rw [hhdef, one_div_pow]
      have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ n₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      rw [h1]
      exact ⟨lt_of_le_of_lt h2 (lt_of_lt_of_le hn₀ (min_le_left _ _)),
        lt_of_le_of_lt h2 (lt_of_lt_of_le hn₀ (min_le_right _ _))⟩
    have hp1 : 0 ≤ 4 * π / δ := by positivity
    have hp2 : 0 ≤ 16 * π / e := by positivity
    have hp3 : 0 ≤ π * 2 ^ n₀ := by positivity
    have hRδ : 4 * π / δ ≤ R := by rw [hRdef]; linarith
    have hRe : 16 * π / e ≤ R := by rw [hRdef]; linarith
    set K : ℕ := ⌈2 * π / (h * R)⌉₊ with hKdef
    have hKge : 2 * π / (h * R) ≤ K := Nat.le_ceil _
    have hKlt : (K : ℝ) < 2 * π / (h * R) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hKR : 2 * π ≤ ((K : ℝ) + 1) * h * R := by
      have : 2 * π = 2 * π / (h * R) * (h * R) := by field_simp
      rw [this, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hKh : (K : ℝ) * h < δ := by
      have h1 : (K : ℝ) * h < (2 * π / (h * R) + 1) * h :=
        mul_lt_mul_of_pos_right hKlt hh
      have h2 : (2 * π / (h * R) + 1) * h = 2 * π / R + h := by field_simp
      have h3 : 2 * π / R ≤ δ / 2 := by
        rw [div_le_iff₀ hR0]
        have := (div_le_iff₀ hδ).mp hRδ
        nlinarith
      linarith [hhle.1]
    have hKN : (K : ℝ) / ((4 ^ n : ℕ) + 1) < e / 4 := by
      have h4 : (0 : ℝ) < ((4 ^ n : ℕ) : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ h4]
      have h5 : (K : ℝ) < 2 * π / (h * R) + 1 := hKlt
      have h6 : 2 * π / (h * R) = 2 * π * 2 ^ n / R := by rw [hhdef]; field_simp
      have h7 : ((4 ^ n : ℕ) : ℝ) = 2 ^ n * 2 ^ n := by push_cast; rw [← mul_pow]; norm_num
      have h8 : 2 * π / R ≤ e / 8 := by
        rw [div_le_iff₀ hR0]
        have := (div_le_iff₀ hepos).mp hRe
        nlinarith
      have h9 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have h10 : (1 : ℝ) / 2 ^ n < e / 8 := hhle.2
      have h11 : 1 < e / 8 * 2 ^ n := by
        rw [div_lt_iff₀ (by positivity)] at h10; linarith
      rw [h6] at h5
      have h12 : 2 * π * 2 ^ n / R ≤ e / 8 * 2 ^ n := by
        rw [show 2 * π * 2 ^ n / R = 2 * π / R * 2 ^ n by ring]
        exact mul_le_mul_of_nonneg_right h8 (by positivity)
      rw [h7]
      nlinarith
    have htail := fejerMeasure_tail_le hφ hφ0 hh (4 ^ n) K hR0 hKR
    have hbrk : ∀ a ∈ Finset.range (K + 1), ∀ b ∈ Finset.range (K + 1),
        (1 - (φ ((((a : ℤ) - b : ℤ) : ℝ) * h)).re) + |(((a : ℤ) - b : ℤ) : ℝ)| / ((4 ^ n : ℕ) + 1)
          ≤ e / 2 := by
      intro a ha b hb
      rw [Finset.mem_range] at ha hb
      have hab : |(((a : ℤ) - b : ℤ) : ℝ)| ≤ K := by
        push_cast
        rw [abs_le]
        constructor
        · have : (b : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.mp hb
          linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
        · have : (a : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.mp ha
          linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
      have h1 : 1 - (φ ((((a : ℤ) - b : ℤ) : ℝ) * h)).re ≤ e / 4 := by
        apply hbr
        rw [abs_mul, abs_of_pos hh]
        calc |(((a : ℤ) - b : ℤ) : ℝ)| * h ≤ K * h := by gcongr
          _ < δ := hKh
      have h2 : |(((a : ℤ) - b : ℤ) : ℝ)| / ((4 ^ n : ℕ) + 1) < e / 4 :=
        lt_of_le_of_lt (div_le_div_of_nonneg_right hab (by positivity)) hKN
      linarith
    have hsum : (1 / ((K : ℝ) + 1) ^ 2) *
        ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
          ((1 - (φ ((((a : ℤ) - b : ℤ) : ℝ) * h)).re) +
            |(((a : ℤ) - b : ℤ) : ℝ)| / ((4 ^ n : ℕ) + 1)) ≤ e / 2 := by
      have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hbrk a ha b hb
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      calc _ ≤ (1 / ((K : ℝ) + 1) ^ 2) * (((K + 1 : ℕ) : ℝ) * (((K + 1 : ℕ) : ℝ) * (e / 2))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = e / 2 := by push_cast; field_simp
    have hreal : (fejerMeasure φ h (4 ^ n)).real {x | R < |x|} ≤ e := by
      linarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact (ENNReal.ofReal_le_ofReal hreal).trans he.le

/-- At a dyadic point the characteristic functions of the Fejér sequence converge to `φ`. -/
theorem tendsto_charFun_fejerSeq_dyadic (hφ : PositiveDefiniteOnReal φ) (hφ0 : φ 0 = 1) (j : ℤ)
    (m : ℕ) :
    Tendsto (fun n => charFun (fejerSeq φ hφ hφ0 n : Measure ℝ) ((j : ℝ) / 2 ^ m)) atTop
      (𝓝 (φ ((j : ℝ) / 2 ^ m))) := by
  set c : ℕ → ℝ := fun n => (pairCount (4 ^ n) (j * 2 ^ (n - m)) : ℝ) / ((4 ^ n : ℕ) + 1) with hc
  have hev : ∀ n, m ≤ n → charFun (fejerSeq φ hφ hφ0 n : Measure ℝ) ((j : ℝ) / 2 ^ m) =
      ((c n : ℝ) : ℂ) * φ ((j : ℝ) / 2 ^ m) := by
    intro n hn
    have ht : (j : ℝ) / 2 ^ m = (((j * 2 ^ (n - m) : ℤ) : ℝ)) * (1 / 2 ^ n) := by
      push_cast
      rw [show (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m by rw [← pow_add, Nat.sub_add_cancel hn]]
      field_simp
    change charFun (fejerMeasure φ (1 / 2 ^ n) (4 ^ n)) _ = _
    rw [ht, charFun_fejerMeasure hφ (dyadic_pos n)]
  have hlim : Tendsto c atTop (𝓝 1) := by
    have hlow : ∀ n, m ≤ n → 1 - |(j : ℝ)| / 2 ^ m * (1 / 2) ^ n ≤ c n := by
      intro n hmn
      have h4 : (0 : ℝ) < ((4 ^ n : ℕ) : ℝ) + 1 := by positivity
      have hge := pairCount_ge (4 ^ n) (j * 2 ^ (n - m))
      rw [hc]
      simp only
      rw [le_div_iff₀ h4]
      have e1 : |(((j * 2 ^ (n - m) : ℤ)) : ℝ)| ≤ |(j : ℝ)| / 2 ^ m * (1 / 2) ^ n *
          (((4 ^ n : ℕ) : ℝ) + 1) := by
        push_cast
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n - m))]
        rw [show (2 : ℝ) ^ (n - m) = 2 ^ n / 2 ^ m by
          rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel hmn]]
        rw [show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        have : |(j : ℝ)| * (2 ^ n / 2 ^ m) = |(j : ℝ)| / 2 ^ m * (1 / 2) ^ n * (2 ^ n * 2 ^ n) := by
          rw [one_div_pow]; field_simp
        rw [this]
        have hpos : 0 ≤ |(j : ℝ)| / 2 ^ m * (1 / 2) ^ n := by positivity
        nlinarith
      nlinarith
    have hup : ∀ n, c n ≤ 1 := by
      intro n
      rw [hc]; simp only
      rw [div_le_one (by positivity)]
      exact_mod_cast pairCount_le _ _
    have hz : Tendsto (fun n : ℕ => 1 - |(j : ℝ)| / 2 ^ m * (1 / 2) ^ n) atTop (𝓝 1) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (|(j : ℝ)| / 2 ^ m)
      simpa using this.const_sub 1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hz tendsto_const_nhds
      (Filter.eventually_atTop.mpr ⟨m, hlow⟩) (Eventually.of_forall hup)
  have hlim' : Tendsto (fun n => ((c n : ℝ) : ℂ) * φ ((j : ℝ) / 2 ^ m)) atTop
      (𝓝 (φ ((j : ℝ) / 2 ^ m))) := by
    have := (Complex.continuous_ofReal.tendsto 1).comp hlim
    simpa using this.mul_const (φ ((j : ℝ) / 2 ^ m))
  exact hlim'.congr' (Filter.eventually_atTop.mpr ⟨m, fun n hn => (hev n hn).symm⟩)

end Bochner

open Bochner

/-- **Bochner, normalized.**  A continuous positive-definite `φ` with `φ(0) = 1` is the
characteristic function of a probability measure. -/
theorem exists_probabilityMeasure_charFun_eq (hφ : PositiveDefiniteOnReal φ) (hφ0 : φ 0 = 1)
    (hc : Continuous φ) : ∃ μ : ProbabilityMeasure ℝ, ∀ t, charFun (μ : Measure ℝ) t = φ t := by
  have hcomp := isCompact_closure_of_isTightMeasureSet (isTight_fejerSeq hφ hφ0 hc)
  obtain ⟨μ₀, -, σ, hσ, hlim⟩ := hcomp.tendsto_subseq
    (x := fejerSeq φ hφ hφ0) (fun n => subset_closure (mem_range_self n))
  refine ⟨μ₀, ?_⟩
  have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim
  -- agreement at dyadic points
  have hdy : ∀ (j : ℤ) (m : ℕ), charFun (μ₀ : Measure ℝ) ((j : ℝ) / 2 ^ m) = φ ((j : ℝ) / 2 ^ m) :=
    fun j m => tendsto_nhds_unique (hcf _)
      ((tendsto_charFun_fejerSeq_dyadic hφ hφ0 j m).comp hσ.tendsto_atTop)
  -- density of the dyadics
  intro t
  set tm : ℕ → ℝ := fun m => (⌊t * 2 ^ m⌋ : ℝ) / 2 ^ m with htm
  have htend : Tendsto tm atTop (𝓝 t) := by
    have hb : ∀ m : ℕ, |tm m - t| ≤ (1 / 2) ^ m := by
      intro m
      have h2 : (0 : ℝ) < 2 ^ m := by positivity
      have h1 := Int.floor_le (t * 2 ^ m)
      have h3 := Int.lt_floor_add_one (t * 2 ^ m)
      rw [htm]; simp only
      rw [abs_le, one_div_pow]
      constructor
      · have h4 : (⌊t * 2 ^ m⌋ : ℝ) / 2 ^ m + 1 / 2 ^ m = (⌊t * 2 ^ m⌋ + 1) / 2 ^ m := by
          rw [← add_div]
        rw [neg_le_sub_iff_le_add, h4, le_div_iff₀ h2]
        linarith
      · rw [sub_le_iff_le_add, div_le_iff₀ h2, add_mul, div_mul_cancel₀ _ h2.ne']
        linarith
    have hz := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m => norm_nonneg _) (fun m => by rw [Real.norm_eq_abs]; exact hb m) hz
  have h1 : Tendsto (fun m => charFun (μ₀ : Measure ℝ) (tm m)) atTop
      (𝓝 (charFun (μ₀ : Measure ℝ) t)) := (continuous_charFun.tendsto t).comp htend
  have h2 : Tendsto (fun m => φ (tm m)) atTop (𝓝 (φ t)) := (hc.tendsto t).comp htend
  refine tendsto_nhds_unique h1 ?_
  refine h2.congr fun m => ?_
  exact (hdy _ m).symm

theorem PositiveDefiniteOnReal.const_mul (hφ : PositiveDefiniteOnReal φ) {c : ℝ} (hc : 0 ≤ c) :
    PositiveDefiniteOnReal fun t => (c : ℂ) * φ t := by
  intro N t v
  obtain ⟨r, hr, hsum⟩ := hφ N t v
  refine ⟨c * r, mul_nonneg hc hr, ?_⟩
  have : ∑ i, ∑ j, star (v i) * ((c : ℂ) * φ (t j - t i)) * v j =
      (c : ℂ) * ∑ i, ∑ j, star (v i) * φ (t j - t i) * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, hsum]; push_cast; ring

/-- **Bochner's theorem on the real line.**  A continuous positive-definite function is the
characteristic function of a finite positive measure. -/
theorem exists_charFun_eq_of_positiveDefinite (hφ : PositiveDefiniteOnReal φ)
    (hc : Continuous φ) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ t, charFun μ t = φ t := by
  obtain ⟨hp0, hpim⟩ := hφ.zero
  set p : ℝ := (φ 0).re with hp
  rcases eq_or_lt_of_le hp0 with hp00 | hppos
  · refine ⟨0, inferInstance, fun t => ?_⟩
    have := hφ.norm_le t
    rw [← hp, ← hp00] at this
    have h0 : φ t = 0 := norm_le_zero_iff.mp this
    rw [h0, charFun_apply_real, integral_zero_measure]
  · set ψ : ℝ → ℂ := fun t => ((1 / p : ℝ) : ℂ) * φ t with hψ
    have hψpd : PositiveDefiniteOnReal ψ := hφ.const_mul (by positivity)
    have hψ0 : ψ 0 = 1 := by
      have hφ0 : φ 0 = (p : ℂ) := Complex.ext (by simp [hp]) (by simp [hpim])
      have hpc : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hppos.ne'
      rw [hψ]; simp only; rw [hφ0]; push_cast; exact one_div_mul_cancel hpc
    have hψc : Continuous ψ := continuous_const.mul hc
    obtain ⟨μ₀, hμ₀⟩ := exists_probabilityMeasure_charFun_eq hψpd hψ0 hψc
    have hpc : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hppos.ne'
    refine ⟨(ENNReal.ofReal p) • (μ₀ : Measure ℝ),
      Measure.smul_finite _ ENNReal.ofReal_ne_top, fun t => ?_⟩
    rw [charFun_apply_real, integral_smul_measure, ← charFun_apply_real, hμ₀, hψ]
    simp only
    rw [ENNReal.toReal_ofReal hppos.le, Complex.real_smul, ← mul_assoc]
    push_cast
    rw [mul_one_div_cancel hpc, one_mul]

end GaloisForLFunctions.HTGeometry
