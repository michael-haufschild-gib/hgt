import GaloisForLFunctions.RHTower.ZetaDiscUniformCarlsonTail
import GaloisForLFunctions.RHTower.ZetaFiniteMeanSquare
import GaloisForLFunctions.RHTower.ThetaEulerTwoPortJetPole
import GaloisForLFunctions.RHTower.SteinhausEulerLocalMeanSq
import GaloisForLFunctions.RHTower.SteinhausEulerSmoothSeries
import GaloisForLFunctions.RHTower.FiniteEulerProductUniversalityOnDiscs

/-!
# The disc-uniform Carlson tail law for the finite Euler product

Let `E_y(s) = ∏_{p ≤ y} (1 − p^{−s})^{−1}` be the finite Euler product and let `closedBall c (2r)`
lie in `1/2 < Re s < 1`.  Then for all large `y` the heights `τ ∈ [0, T]` at which
`|ζ(z + iτ) − E_y(z + iτ)| ≥ ε` for some `z ∈ closedBall c r` have measure at most `δ T` for all
large `T` (`eventually_eventually_volume_eulerDiscTailBadSet_le`).  This is the Euler-product
analogue of the Carlson tail law for the Dirichlet heads, and it is what transfers the
Kronecker–Weyl density of Euler-product approximations to `ζ` itself.

**The vertical-line mean square.**  `E_y` is the Dirichlet series of the `(y+1)`-smooth numbers,
so on a vertical line

  `ζ − E_y = (ζ − head_M) + (non-smooth part of head_M) − (smooth tail beyond M)`.

The first term is the Carlson tail of the Dirichlet head; the second is a Dirichlet polynomial
with `0/1` coefficients supported on `n > y`, whose window mean square is at most
`(7V/4)·tailMass(y, σ₀)` plus a fixed off-diagonal constant (the Dirichlet mean value theorem);
the third is bounded pointwise by the tail of the convergent smooth-number series, which is small
for `M` large.  Hence the window mean square of `ζ − E_y` is at most `(7V/4)` times a quantity that
tends to zero with `y` (`eventually_uniform_window_eulerTail_meanSquare_le`).

**From lines to the disc.**  Since the closed disc `closedBall c (2r)` avoids the pole, no pole
weight is needed: the local planar mean-square inequality bounds `|ζ − E_y|²` at a point of the
disc by the planar energy on the doubled disc, Tonelli and Markov give the window density of the
bad heights, and the dyadic-to-prefix lemma gives the prefix density.
-/

open Complex Filter Topology MeasureTheory Set Finset Metric
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## 1. The finite Euler product and its smooth-number expansion -/

/-- The finite Euler product over the primes `≤ y`, indexed by `ℕ`. -/
def eulerHead (y : ℕ) (s : ℂ) : ℂ :=
  ∏ n ∈ (range (y + 1)).filter Nat.Prime, (1 - (n : ℂ) ^ (-s))⁻¹

theorem eulerHead_eq_eulerPhaseProduct_one (y : ℕ) (s : ℂ) :
    eulerHead y s = eulerPhaseProduct y 1 s := by
  rw [eulerPhaseProduct_one, eulerHead, ← map_val_primesLE, Finset.prod_map]
  rfl

theorem eulerHead_eq_thetaEulerStageZeta (y : ℕ) (s : ℂ) :
    eulerHead y s = thetaEulerStageZeta (Nat.primesBelow (y + 1)) s := by
  unfold eulerHead thetaEulerStageZeta Nat.primesBelow
  rfl

/-- **The smooth-number expansion** `E_y(s) = Σ_{n (y+1)-smooth} n^{−s}` for `Re s > 0`. -/
theorem hasSum_smooth_eulerHead (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℂ) ^ (-s)) n)
      (eulerHead y s) := by
  have h := (hasSum_factoredNumbers_cpow (Nat.primesBelow (y + 1))
    (fun p hp => Nat.prime_of_mem_primesBelow hp) hs).2
  rw [← eulerHead_eq_thetaEulerStageZeta] at h
  have h2 := (hasSum_subtype_iff_indicator (f := fun n : ℕ => (n : ℂ) ^ (-s))
    (s := Nat.factoredNumbers (Nat.primesBelow (y + 1)))).mp h
  rwa [← Nat.smoothNumbers_eq_factoredNumbers_primesBelow] at h2

theorem zero_notMem_smoothNumbers (y : ℕ) : (0 : ℕ) ∉ Nat.smoothNumbers (y + 1) :=
  fun h => (Nat.mem_smoothNumbers.mp h).1 rfl

/-- A positive integer that is not `(y+1)`-smooth exceeds `y`. -/
theorem lt_of_not_mem_smoothNumbers {y n : ℕ} (hn : n ≠ 0) (h : n ∉ Nat.smoothNumbers (y + 1)) :
    y < n := by
  rw [Nat.mem_smoothNumbers, not_and] at h
  have h' := h hn
  push_neg at h'
  obtain ⟨p, hp, hpy⟩ := h'
  have hdvd := Nat.dvd_of_mem_primeFactorsList hp
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  omega

/-! ## 2. Smooth and non-smooth parts of the Dirichlet head -/

/-- `Σ_{n ≤ M, n (y+1)-smooth} n^{−s}`. -/
def smoothHead (y M : ℕ) (s : ℂ) : ℂ :=
  edPoly (fun n => if n ∈ Nat.smoothNumbers (y + 1) then 1 else 0) (Finset.Icc 1 M) s

/-- `Σ_{n ≤ M, n not (y+1)-smooth} n^{−s}`. -/
def nonSmoothHead (y M : ℕ) (s : ℂ) : ℂ :=
  edPoly (fun n => if n ∈ Nat.smoothNumbers (y + 1) then 0 else 1) (Finset.Icc 1 M) s

theorem head_eq_smoothHead_add_nonSmoothHead (y M : ℕ) (s : ℂ) :
    edPoly (fun _ => 1) (Finset.Icc 1 M) s = smoothHead y M s + nonSmoothHead y M s := by
  unfold smoothHead nonSmoothHead edPoly
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-- The smooth tail `E_y − Σ_{n ≤ M, smooth} n^{−s}`. -/
def smoothTail (y M : ℕ) (s : ℂ) : ℂ := eulerHead y s - smoothHead y M s

/-- The head of the smooth series up to `M` is `smoothHead`. -/
theorem sum_range_indicator_smooth_eq_smoothHead (y M : ℕ) (s : ℂ) :
    ∑ i ∈ range (M + 1), (Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℂ) ^ (-s)) i
      = smoothHead y M s := by
  classical
  rw [sum_range_succ', Set.indicator_of_notMem (zero_notMem_smoothNumbers y), add_zero]
  unfold smoothHead edPoly
  rw [← Sieve.image_succ_univ M, Finset.sum_image (Sieve.succ_injOn M),
    Fin.sum_univ_eq_sum_range (fun i => (if i + 1 ∈ Nat.smoothNumbers (y + 1) then (1 : ℂ) else 0)
      * (((i + 1 : ℕ) : ℝ) : ℂ) ^ (-s)) M]
  refine sum_congr rfl fun i _ => ?_
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- The smooth tail is the tail of the smooth-number series beyond `M`. -/
theorem smoothTail_eq_tsum (y M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    smoothTail y M s = ∑' i : ℕ,
      (Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℂ) ^ (-s)) (i + (M + 1)) := by
  have hsum := (hasSum_smooth_eulerHead y hs).summable
  have hsplit := hsum.sum_add_tsum_nat_add (M + 1)
  rw [(hasSum_smooth_eulerHead y hs).tsum_eq, sum_range_indicator_smooth_eq_smoothHead] at hsplit
  rw [smoothTail, ← hsplit]
  ring

/-! ## 3. The smooth tail is uniformly small for `M` large -/

/-- The majorant `Σ_{i} 1_{smooth}(i + M + 1) (i + M + 1)^{−σ}` of the smooth tail. -/
def smoothTailMass (y M : ℕ) (σ : ℝ) : ℝ :=
  ∑' i : ℕ, (Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) (i + (M + 1))

theorem summable_indicator_smooth_rpow (y : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable ((Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℝ) ^ (-σ))) :=
  summable_subtype_iff_indicator.mp (summable_smoothNumbers_neg_rpow (y + 1) hσ)

theorem smoothTailMass_nonneg (y M : ℕ) (σ : ℝ) : 0 ≤ smoothTailMass y M σ :=
  tsum_nonneg fun i => Set.indicator_nonneg (fun n _ => by positivity) _

/-- The smooth tail mass tends to zero with `M`. -/
theorem tendsto_smoothTailMass (y : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun M => smoothTailMass y M σ) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add
    (fun n : ℕ => (Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n)
  exact h.comp (tendsto_add_atTop_nat 1)

/-- **The smooth tail is bounded by its mass** for `Re s ≥ σ > 0`. -/
theorem norm_smoothTail_le (y M : ℕ) {s : ℂ} {σ : ℝ} (hσ : 0 < σ) (hs : σ ≤ s.re) :
    ‖smoothTail y M s‖ ≤ smoothTailMass y M σ := by
  rw [smoothTail_eq_tsum y M (by linarith)]
  have hnorm : ∀ n : ℕ,
      ‖(Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℂ) ^ (-s)) n‖
        ≤ (Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n := by
    intro n
    by_cases hn : n ∈ Nat.smoothNumbers (y + 1)
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
      have hn0 : 0 < n := Nat.pos_of_ne_zero (Nat.mem_smoothNumbers.mp hn).1
      rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn0) (by linarith)
    · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, norm_zero]
  have hsumm : Summable (fun i : ℕ =>
      (Nat.smoothNumbers (y + 1)).indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) (i + (M + 1))) :=
    (summable_nat_add_iff (M + 1)).mpr (summable_indicator_smooth_rpow y hσ)
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun i => hnorm _) ?_ hsumm)
  · exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hnorm _) hsumm
  · exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hnorm _) hsumm

/-! ## 4. The non-smooth head: a Dirichlet polynomial supported above `y` -/

/-- A Dirichlet polynomial over `[1, M]` on a vertical line, as a `dirPoly` at `−t`. -/
theorem edPoly_Icc_line_eq_dirPoly_neg (a : ℕ → ℂ) (M : ℕ) (σ t : ℝ) :
    edPoly a (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)
      = Sieve.dirPoly M
          (fun n : Fin M => a ((n : ℕ) + 1) * ((((n : ℕ) : ℝ) + 1) ^ (-σ) : ℝ)) (-t) := by
  classical
  rw [edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1)]
  unfold cdpoly cdterm Sieve.dirPoly
  rw [← Sieve.image_succ_univ M, Finset.sum_image (Sieve.succ_injOn M)]
  refine sum_congr rfl fun n _ => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2
  push_cast
  ring

/-- The off-diagonal constant of the Dirichlet mean value theorem for the head up to `M`. -/
def nonSmoothOffDiagonal (M : ℕ) (σ : ℝ) : ℝ :=
  208 * ∑ n ∈ range M, ((n : ℝ) + 1) ^ (1 - 2 * σ)

theorem nonSmoothOffDiagonal_nonneg (M : ℕ) (σ : ℝ) : 0 ≤ nonSmoothOffDiagonal M σ := by
  unfold nonSmoothOffDiagonal
  positivity

theorem norm_real_rpow_sq' (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖((x ^ (-σ) : ℝ) : ℂ)‖ ^ 2 = x ^ (-(2 * σ)) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

/-- The tail mass of the Dirichlet coefficients is antitone in the cutoff. -/
theorem zetaCoefficientTailMass_antitone {y M : ℕ} (hyM : y ≤ M) {σ : ℝ} (hσ : 1 / 2 < σ) :
    zetaCoefficientTailMass M σ ≤ zetaCoefficientTailMass y σ := by
  unfold zetaCoefficientTailMass
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsum : ∀ k : ℕ, Summable (fun n : ℕ => if n ≤ k then (0 : ℝ) else (n : ℝ) ^ (-2 * σ)) :=
    fun k => Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> simp [Real.rpow_nonneg]) hs
  refine Summable.tsum_le_tsum (fun n => ?_) (hsum M) (hsum y)
  split_ifs with h1 h2
  · exact le_rfl
  · positivity
  · omega
  · exact le_rfl

/-- **Window mean square of the non-smooth head.**  Its diagonal is at most the tail mass beyond
`y`, and the off-diagonal is a constant depending on `M` only. -/
theorem nonSmoothHead_meanSquare_window_le (y M : ℕ) {σ₀ σ : ℝ} (h0 : 1 / 2 < σ₀)
    (hσ : σ₀ ≤ σ) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫ t in T₁..T₂, ‖nonSmoothHead y M ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ (T₂ - T₁) * zetaCoefficientTailMass y σ₀ + nonSmoothOffDiagonal M σ₀ := by
  classical
  set b : Fin M → ℂ := fun n =>
    (if (n : ℕ) + 1 ∈ Nat.smoothNumbers (y + 1) then (0 : ℂ) else 1)
      * ((((n : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) with hb
  have hconv : ∀ t : ℝ, nonSmoothHead y M ((σ : ℂ) + (t : ℂ) * I) = Sieve.dirPoly M b (-t) :=
    fun t => edPoly_Icc_line_eq_dirPoly_neg _ M σ t
  simp_rw [hconv]
  have h := (abs_le.mp (Sieve.dirichlet_meanValue_sharp_window_neg M b T₁ T₂)).2
  -- the coefficient squares
  have hpos : ∀ n : Fin M, (0 : ℝ) < ((n : ℕ) : ℝ) + 1 := fun n => by positivity
  have hone : ∀ n : Fin M, (1 : ℝ) ≤ ((n : ℕ) : ℝ) + 1 := fun n => by
    have := (n : ℕ).cast_nonneg (α := ℝ)
    linarith
  have hb_sq : ∀ n : Fin M, ‖b n‖ ^ 2
      = if (n : ℕ) + 1 ∈ Nat.smoothNumbers (y + 1) then 0
        else (((n : ℕ) : ℝ) + 1) ^ (-(2 * σ)) := by
    intro n
    rw [hb]
    split_ifs with hn
    · simp
    · rw [one_mul, norm_real_rpow_sq' σ (hpos n)]
  -- diagonal: each term is at most the corresponding term of the tail mass beyond `y`
  have hdiag : ∑ n : Fin M, ‖b n‖ ^ 2 ≤ zetaCoefficientTailMass y σ₀ := by
    have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ₀)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hsum : Summable (fun n : ℕ => if n ≤ y then (0 : ℝ) else (n : ℝ) ^ (-2 * σ₀)) :=
      Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by split_ifs <;> simp [Real.rpow_nonneg]) hs
    have hterm : ∀ n : Fin M, ‖b n‖ ^ 2
        ≤ (fun m : ℕ => if m ≤ y then (0 : ℝ) else (m : ℝ) ^ (-2 * σ₀)) ((n : ℕ) + 1) := by
      intro n
      rw [hb_sq]
      simp only
      split_ifs with h1 h2 h2
      · exact le_rfl
      · positivity
      · exfalso
        have := lt_of_not_mem_smoothNumbers (by omega) h1
        omega
      · push_cast
        exact Real.rpow_le_rpow_of_exponent_le (hone n) (by linarith)
    calc ∑ n : Fin M, ‖b n‖ ^ 2
        ≤ ∑ n : Fin M, (fun m : ℕ => if m ≤ y then (0 : ℝ) else (m : ℝ) ^ (-2 * σ₀)) ((n : ℕ) + 1) :=
          sum_le_sum fun n _ => hterm n
      _ = ∑ n ∈ range M, (fun m : ℕ => if m ≤ y then (0 : ℝ) else (m : ℝ) ^ (-2 * σ₀)) (n + 1) :=
          Fin.sum_univ_eq_sum_range _ M
      _ ≤ ∑' n : ℕ, (fun m : ℕ => if m ≤ y then (0 : ℝ) else (m : ℝ) ^ (-2 * σ₀)) (n + 1) :=
          ((summable_nat_add_iff 1).mpr hsum).sum_le_tsum _
            (fun n _ => by simp only; split_ifs <;> positivity)
      _ = zetaCoefficientTailMass y σ₀ := by
          unfold zetaCoefficientTailMass
          rw [hsum.tsum_eq_zero_add]
          simp
  -- off-diagonal: a constant depending on `M` only
  have hoff : 208 * ∑ n : Fin M, (((n : ℕ) : ℝ) + 1) * ‖b n‖ ^ 2 ≤ nonSmoothOffDiagonal M σ₀ := by
    unfold nonSmoothOffDiagonal
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Fin.sum_univ_eq_sum_range (fun n => ((n : ℝ) + 1) ^ (1 - 2 * σ₀)) M]
    refine sum_le_sum fun n _ => ?_
    rw [hb_sq]
    split_ifs
    · rw [mul_zero]
      positivity
    · rw [← Real.rpow_one (((n : ℕ) : ℝ) + 1)]
      nth_rewrite 2 [Real.rpow_one]
      rw [← Real.rpow_add (hpos n)]
      exact Real.rpow_le_rpow_of_exponent_le (hone n) (by linarith)
  have hT' : 0 ≤ T₂ - T₁ := by linarith
  calc (∫ t in T₁..T₂, ‖Sieve.dirPoly M b (-t)‖ ^ 2)
      ≤ (T₂ - T₁) * ∑ n : Fin M, ‖b n‖ ^ 2 + 208 * ∑ n : Fin M, (((n : ℕ) : ℝ) + 1) * ‖b n‖ ^ 2 := by
        linarith
    _ ≤ (T₂ - T₁) * zetaCoefficientTailMass y σ₀ + nonSmoothOffDiagonal M σ₀ := by
        gcongr

/-! ## 5. The Euler tail on a vertical line and its window mean square -/

/-- `ζ − E_y` on the vertical line `Re s = σ`, as a function of the height. -/
def eulerLineTail (y : ℕ) (σ t : ℝ) : ℂ :=
  riemannZeta ((σ : ℂ) + (t : ℂ) * I) - eulerHead y ((σ : ℂ) + (t : ℂ) * I)

/-- The Euler tail is the Carlson tail plus the non-smooth head minus the smooth tail. -/
theorem eulerLineTail_decomposition (y M : ℕ) (σ t : ℝ) :
    eulerLineTail y σ t = zetaDirichletTail M σ t
      + nonSmoothHead y M ((σ : ℂ) + (t : ℂ) * I) - smoothTail y M ((σ : ℂ) + (t : ℂ) * I) := by
  unfold eulerLineTail zetaDirichletTail zetaDirichletHead smoothTail
  rw [head_eq_smoothHead_add_nonSmoothHead y M]
  ring

theorem continuousOn_eulerHead (y : ℕ) :
    ContinuousOn (eulerHead y) {s : ℂ | 0 < s.re} := by
  unfold eulerHead
  refine continuousOn_finset_prod _ fun n hn => ?_
  have hn2 : 2 ≤ n := (mem_filter.mp hn).2.two_le
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  refine ContinuousOn.inv₀ ?_ fun s hs => ?_
  · exact (continuous_const.sub (continuous_neg.const_cpow (Or.inl hn0))).continuousOn
  · have := one_sub_phase_cpow_ne_zero_nat (ω := 1) (by simp) hn2 (hs : 0 < s.re) le_rfl
    simpa using this

theorem differentiableOn_eulerHead (y : ℕ) :
    DifferentiableOn ℂ (eulerHead y) {s : ℂ | 0 < s.re} := by
  unfold eulerHead
  refine DifferentiableOn.finsetProd fun n hn => ?_
  have hn2 : 2 ≤ n := (mem_filter.mp hn).2.two_le
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  refine DifferentiableOn.inv ?_ fun s hs => ?_
  · exact (differentiableOn_const _).sub (differentiableOn_neg.const_cpow (Or.inl hn0))
  · have := one_sub_phase_cpow_ne_zero_nat (ω := 1) (by simp) hn2 (hs : 0 < s.re) le_rfl
    simpa using this

theorem measurable_eulerHead (y : ℕ) : Measurable (eulerHead y) := by
  unfold eulerHead
  refine Finset.measurable_prod _ fun n hn => ?_
  have hn2 : 2 ≤ n := (mem_filter.mp hn).2.two_le
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact (continuous_const.sub (continuous_neg.const_cpow (Or.inl hn0))).measurable.inv

theorem continuous_eulerLineTail (y : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≠ 1) :
    Continuous (eulerLineTail y σ) := by
  unfold eulerLineTail
  refine (continuous_riemannZeta_vertical_line hσ1).sub ?_
  refine (continuousOn_eulerHead y).comp_continuous
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t => ?_
  simp [hσ0]

/-- **Uniform window mean square of the Euler tail.**  For `y ≤ M` and `[σ₀, σ₁] ⊂ (1/2, 1)`, the
window mean square of `ζ − E_y` on `[V/4, 2V]` is eventually at most
`(7V/4)(9·tailMass(y, σ₀) + 4η + 3·smoothTailMass(y, M, σ₀)²)`, uniformly in the abscissa. -/
theorem eventually_uniform_window_eulerLineTail_meanSquare_le (y M : ℕ) (hyM : y ≤ M)
    {σ₀ σ₁ : ℝ} (h0 : 1 / 2 < σ₀) (h01 : σ₀ ≤ σ₁) (h1 : σ₁ < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ V : ℝ in atTop, ∀ σ ∈ Icc σ₀ σ₁,
      (∫ t in V / 4..2 * V, ‖eulerLineTail y σ t‖ ^ 2)
        ≤ 7 * V / 4 * (9 * zetaCoefficientTailMass y σ₀ + 4 * η
            + 3 * smoothTailMass y M σ₀ ^ 2) := by
  have hσ₀0 : 0 < σ₀ := by linarith
  filter_upwards [eventually_uniform_window_zetaDirichletTail_meanSquare_le M h0 h01 h1 hη,
    eventually_ge_atTop (12 * nonSmoothOffDiagonal M σ₀ / (7 * η)),
    eventually_ge_atTop (0 : ℝ)] with V hcarlson hVoff hV0
  intro σ hσ
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hσ1 : σ ≠ 1 := ne_of_lt (lt_of_le_of_lt hσ.2 h1)
  have hVle : V / 4 ≤ 2 * V := by linarith
  -- the three pieces
  set T : ℝ → ℂ := zetaDirichletTail M σ with hTdef
  set P : ℝ → ℂ := fun t => nonSmoothHead y M ((σ : ℂ) + (t : ℂ) * I) with hPdef
  set R : ℝ → ℂ := fun t => smoothTail y M ((σ : ℂ) + (t : ℂ) * I) with hRdef
  have hTc : Continuous T := continuous_zetaDirichletTail M hσ1
  have hPc : Continuous P := by
    rw [hPdef]
    exact (differentiable_edPoly _ fun n hn => (Finset.mem_Icc.mp hn).1).continuous.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hRc : Continuous R := by
    rw [hRdef]
    unfold smoothTail
    refine Continuous.sub ?_ ?_
    · refine (continuousOn_eulerHead y).comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun t => ?_
      simp [hσ0]
    · exact (differentiable_edPoly _ fun n hn => (Finset.mem_Icc.mp hn).1).continuous.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  -- pointwise: `‖T + P − R‖² ≤ 3(‖T‖² + ‖P‖² + ‖R‖²)`
  have hpt : ∀ t, ‖eulerLineTail y σ t‖ ^ 2
      ≤ 3 * ‖T t‖ ^ 2 + 3 * ‖P t‖ ^ 2 + 3 * ‖R t‖ ^ 2 := by
    intro t
    rw [eulerLineTail_decomposition y M]
    have h3 : ‖T t + P t - R t‖ ≤ ‖T t‖ + ‖P t‖ + ‖R t‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    have h0' : 0 ≤ ‖T t + P t - R t‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖T t‖ - ‖P t‖), sq_nonneg (‖T t‖ - ‖R t‖), sq_nonneg (‖P t‖ - ‖R t‖),
      norm_nonneg (T t), norm_nonneg (P t), norm_nonneg (R t)]
  have hii : ∀ f : ℝ → ℂ, Continuous f →
      IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume (V / 4) (2 * V) :=
    fun f hf => (hf.norm.pow 2).intervalIntegrable _ _
  have hint : (∫ t in V / 4..2 * V, ‖eulerLineTail y σ t‖ ^ 2)
      ≤ 3 * (∫ t in V / 4..2 * V, ‖T t‖ ^ 2) + 3 * (∫ t in V / 4..2 * V, ‖P t‖ ^ 2)
        + 3 * (∫ t in V / 4..2 * V, ‖R t‖ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hii T hTc).const_mul 3) ((hii P hPc).const_mul 3),
      ← intervalIntegral.integral_add (((hii T hTc).const_mul 3).add ((hii P hPc).const_mul 3))
        ((hii R hRc).const_mul 3)]
    exact intervalIntegral.integral_mono_on hVle
      (hii _ (continuous_eulerLineTail y hσ0 hσ1)) ((((hii T hTc).const_mul 3).add
        ((hii P hPc).const_mul 3)).add ((hii R hRc).const_mul 3)) fun t _ => hpt t
  -- the Carlson piece
  have hT : (∫ t in V / 4..2 * V, ‖T t‖ ^ 2)
      ≤ 7 * V / 4 * (2 * zetaCoefficientTailMass y σ₀ + η) := by
    refine (hcarlson σ hσ).trans ?_
    gcongr
    exact zetaCoefficientTailMass_antitone hyM h0
  -- the non-smooth head
  have hP : (∫ t in V / 4..2 * V, ‖P t‖ ^ 2)
      ≤ 7 * V / 4 * (zetaCoefficientTailMass y σ₀ + η / 3) := by
    refine (nonSmoothHead_meanSquare_window_le y M h0 hσ.1 hVle).trans ?_
    have hoff : nonSmoothOffDiagonal M σ₀ ≤ 7 * V / 4 * (η / 3) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)] at hVoff
      linarith
    have : 2 * V - V / 4 = 7 * V / 4 := by ring
    rw [this]
    linarith
  -- the smooth tail
  have hR : (∫ t in V / 4..2 * V, ‖R t‖ ^ 2) ≤ 7 * V / 4 * smoothTailMass y M σ₀ ^ 2 := by
    have hbound : ∀ t ∈ Icc (V / 4) (2 * V), ‖R t‖ ^ 2 ≤ smoothTailMass y M σ₀ ^ 2 := by
      intro t _
      have h := norm_smoothTail_le y M (s := (σ : ℂ) + (t : ℂ) * I) hσ₀0 (by simp [hσ.1])
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    calc (∫ t in V / 4..2 * V, ‖R t‖ ^ 2)
        ≤ ∫ _t in V / 4..2 * V, smoothTailMass y M σ₀ ^ 2 :=
          intervalIntegral.integral_mono_on hVle (hii R hRc)
            intervalIntegrable_const hbound
      _ = 7 * V / 4 * smoothTailMass y M σ₀ ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  calc (∫ t in V / 4..2 * V, ‖eulerLineTail y σ t‖ ^ 2)
      ≤ 3 * (∫ t in V / 4..2 * V, ‖T t‖ ^ 2) + 3 * (∫ t in V / 4..2 * V, ‖P t‖ ^ 2)
          + 3 * (∫ t in V / 4..2 * V, ‖R t‖ ^ 2) := hint
    _ ≤ 3 * (7 * V / 4 * (2 * zetaCoefficientTailMass y σ₀ + η))
          + 3 * (7 * V / 4 * (zetaCoefficientTailMass y σ₀ + η / 3))
          + 3 * (7 * V / 4 * smoothTailMass y M σ₀ ^ 2) := by gcongr
    _ = 7 * V / 4 * (9 * zetaCoefficientTailMass y σ₀ + 4 * η
          + 3 * smoothTailMass y M σ₀ ^ 2) := by ring

/-! ## 6. The Euler tail as a function of the complex variable -/

/-- `ζ(s) − E_y(s)`, with the Euler product in its phased form with all phases one. -/
def eulerTailFun (y : ℕ) (s : ℂ) : ℂ := riemannZeta s - eulerPhaseProduct y 1 s

theorem eulerTailFun_eq (y : ℕ) (s : ℂ) : eulerTailFun y s = riemannZeta s - eulerHead y s := by
  rw [eulerTailFun, eulerHead_eq_eulerPhaseProduct_one]

theorem eulerTailFun_add_mul_I (y : ℕ) (z : ℂ) (τ : ℝ) :
    eulerTailFun y (z + τ * I) = eulerLineTail y z.re (z.im + τ) := by
  rw [eulerTailFun_eq, eulerLineTail]
  have : z + τ * I = (z.re : ℂ) + ((z.im + τ : ℝ) : ℂ) * I := by
    push_cast
    rw [add_mul]
    nth_rewrite 1 [← Complex.re_add_im z]
    ring
  rw [this]

/-- The region `0 < Re s < 1`, on which `ζ − E_y` is holomorphic. -/
theorem differentiableOn_eulerTailFun (y : ℕ) :
    DifferentiableOn ℂ (eulerTailFun y) {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  have hfun : eulerTailFun y = fun s => riemannZeta s - eulerHead y s :=
    funext fun s => eulerTailFun_eq y s
  rw [hfun]
  refine DifferentiableOn.sub (fun s hs => ?_) ((differentiableOn_eulerHead y).mono fun s hs => hs.1)
  have hs1 : s ≠ 1 := fun h => by
    have := hs.2
    rw [h, Complex.one_re] at this
    exact lt_irrefl _ this
  exact (differentiableAt_riemannZeta hs1).differentiableWithinAt

theorem measurable_eulerTailFun (y : ℕ) : Measurable (eulerTailFun y) := by
  have hfun : eulerTailFun y = fun s => riemannZeta s - eulerHead y s :=
    funext fun s => eulerTailFun_eq y s
  rw [hfun]
  refine Measurable.sub ?_ (measurable_eulerHead y)
  exact measurable_of_continuousOn_compl_singleton 1 fun s hs =>
    (differentiableAt_riemannZeta (hs : s ≠ 1)).continuousAt.continuousWithinAt

/-- The closed disc of radius `2r + ρ` about `c + iτ` lies in `0 < Re < 1` when
`1/2 < Re c − 2r` and `Re c + 2r < 1`. -/
theorem closedBall_subset_strip {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : 1 / 2 < c.re - 2 * r)
    (h1 : c.re + 2 * r < 1) (τ : ℝ) :
    closedBall (c + τ * I) (2 * r) ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have h2 := re_le_of_mem_closedBall hs
  have h3 : (c + τ * I).re - 2 * r ≤ s.re := re_ge_of_mem_closedBall hs
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at h2 h3
  constructor <;> linarith

theorem integrableOn_normSq_eulerTailFun_shift_ball (y : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) (τ : ℝ) :
    IntegrableOn (fun w => ‖eulerTailFun y (w + τ * I)‖ ^ 2) (ball c (2 * r)) := by
  have hcont : ContinuousOn (fun w => ‖eulerTailFun y (w + τ * I)‖ ^ 2) (closedBall c (2 * r)) := by
    refine (((differentiableOn_eulerTailFun y).continuousOn).comp
      (continuous_id.add continuous_const).continuousOn ?_).norm.pow 2
    intro w hw
    have hw' : w + τ * I ∈ closedBall (c + τ * I) (2 * r) := by
      rwa [mem_closedBall, dist_add_right]
    exact closedBall_subset_strip hr h0 h1 τ hw'
  exact (hcont.integrableOn_compact (isCompact_closedBall c (2 * r))).mono_set ball_subset_closedBall

/-- Translation of the planar integral along the imaginary axis. -/
theorem integral_ball_normSq_shift (G : ℂ → ℂ) (c : ℂ) (ρ : ℝ) (τ : ℝ) :
    (∫ w in ball (c + τ * I) ρ, ‖G w‖ ^ 2) = ∫ w in ball c ρ, ‖G (w + τ * I)‖ ^ 2 := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  calc (∫ w, (ball (c + τ * I) ρ).indicator (fun w => ‖G w‖ ^ 2) w)
      = ∫ w, (ball (c + τ * I) ρ).indicator (fun w => ‖G w‖ ^ 2) (w + τ * I) :=
        (MeasureTheory.integral_add_right_eq_self _ _).symm
    _ = ∫ w, (ball c ρ).indicator (fun w => ‖G (w + τ * I)‖ ^ 2) w := by
        congr 1
        funext w
        by_cases hw : w ∈ ball c ρ
        · have hw' : w + τ * I ∈ ball (c + τ * I) ρ := by rwa [mem_ball, dist_add_right]
          rw [indicator_of_mem hw', indicator_of_mem hw]
        · have hw' : w + τ * I ∉ ball (c + τ * I) ρ := by rwa [mem_ball, dist_add_right]
          rw [indicator_of_notMem hw', indicator_of_notMem hw]

/-- **Pointwise control on the disc.**  For `z ∈ closedBall c r` and any height `τ`, the Euler
tail at `z + iτ` is bounded by its planar mean square on `ball c (2r) + iτ`. -/
theorem normSq_eulerTailFun_le_integral_ball (y : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {z : ℂ} (hz : z ∈ closedBall c r)
    (τ : ℝ) :
    ‖eulerTailFun y (z + τ * I)‖ ^ 2 ≤
      1 / (Real.pi * r ^ 2) * ∫ w in ball c (2 * r), ‖eulerTailFun y (w + τ * I)‖ ^ 2 := by
  set w₀ : ℂ := z + τ * I with hw₀
  have hsub : closedBall w₀ r ⊆ closedBall (c + τ * I) (2 * r) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    have hd : dist w₀ (c + τ * I) ≤ r := by
      rw [hw₀, dist_add_right]
      exact mem_closedBall.mp hz
    calc dist w (c + τ * I) ≤ dist w w₀ + dist w₀ (c + τ * I) := dist_triangle _ _ _
      _ ≤ r + r := by linarith
      _ = 2 * r := by ring
  have hstrip := (closedBall_subset_strip hr h0 h1 τ).trans' hsub
  have hdiff : DifferentiableOn ℂ (eulerTailFun y) (ball w₀ r) :=
    (differentiableOn_eulerTailFun y).mono (ball_subset_closedBall.trans hstrip)
  have hcont : ContinuousOn (eulerTailFun y) (closedBall w₀ r) :=
    (differentiableOn_eulerTailFun y).continuousOn.mono hstrip
  have hmvi := norm_sq_value_mul_area_le_integral_ball_local (eulerTailFun y) w₀ hr hdiff hcont
  have hball : ball w₀ r ⊆ ball (c + τ * I) (2 * r) := by
    intro w hw
    rw [mem_ball] at hw ⊢
    have hd : dist w₀ (c + τ * I) ≤ r := by
      rw [hw₀, dist_add_right]
      exact mem_closedBall.mp hz
    calc dist w (c + τ * I) ≤ dist w w₀ + dist w₀ (c + τ * I) := dist_triangle _ _ _
      _ < r + r := by linarith
      _ = 2 * r := by ring
  have hiF2 : IntegrableOn (fun w => ‖eulerTailFun y w‖ ^ 2) (ball (c + τ * I) (2 * r)) := by
    have hcont' : ContinuousOn (fun w => ‖eulerTailFun y w‖ ^ 2) (closedBall (c + τ * I) (2 * r)) :=
      ((differentiableOn_eulerTailFun y).continuousOn.mono
        (closedBall_subset_strip hr h0 h1 τ)).norm.pow 2
    exact (hcont'.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hint2 : (∫ w in ball w₀ r, ‖eulerTailFun y w‖ ^ 2)
      ≤ ∫ w in ball (c + τ * I) (2 * r), ‖eulerTailFun y w‖ ^ 2 :=
    setIntegral_mono_set hiF2 (Eventually.of_forall fun w => by positivity)
      (Eventually.of_forall hball)
  rw [integral_ball_normSq_shift (eulerTailFun y) c (2 * r) τ] at hint2
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  calc ‖eulerTailFun y (z + τ * I)‖ ^ 2 * (Real.pi * r ^ 2)
      = Real.pi * r ^ 2 * ‖eulerTailFun y w₀‖ ^ 2 := by rw [hw₀]; ring
    _ ≤ ∫ w in ball w₀ r, ‖eulerTailFun y w‖ ^ 2 := hmvi
    _ ≤ ∫ w in ball c (2 * r), ‖eulerTailFun y (w + τ * I)‖ ^ 2 := hint2

/-! ## 7. Planar energy, bad heights, and the Markov bound on dyadic windows -/

/-- Planar mean square of `ζ − E_y` on `ball c (2r) + iτ`, as a function of the height. -/
def eulerDiscTailEnergy (y : ℕ) (c : ℂ) (r : ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in ball c (2 * r), ENNReal.ofReal (‖eulerTailFun y (w + τ * I)‖ ^ 2)

/-- Heights at which `|ζ − E_y| ≥ ε` somewhere on `closedBall c r + iτ`. -/
def eulerDiscTailBadSet (y : ℕ) (c : ℂ) (r ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∃ z ∈ closedBall c r, ε ≤ ‖eulerTailFun y (z + τ * I)‖}

theorem measurable_shiftedEulerTailEnergyIntegrand (y : ℕ) :
    Measurable (fun p : ℝ × ℂ => ENNReal.ofReal (‖eulerTailFun y (p.2 + p.1 * I)‖ ^ 2)) := by
  have hm : Measurable (fun p : ℝ × ℂ => p.2 + (p.1 : ℂ) * I) :=
    (continuous_snd.add ((Complex.continuous_ofReal.comp continuous_fst).mul
      continuous_const)).measurable
  exact (((measurable_eulerTailFun y).comp hm).norm.pow_const 2).ennreal_ofReal

theorem measurable_eulerDiscTailEnergy (y : ℕ) (c : ℂ) (r : ℝ) :
    Measurable (eulerDiscTailEnergy y c r) :=
  (measurable_shiftedEulerTailEnergyIntegrand y).lintegral_prod_right'

/-- The bad heights are those of large planar energy. -/
theorem eulerDiscTailBadSet_subset_energy_ge (y : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε : ℝ} (hε : 0 < ε) :
    eulerDiscTailBadSet y c r ε ⊆
      {τ : ℝ | ENNReal.ofReal (ε ^ 2 * (Real.pi * r ^ 2)) ≤ eulerDiscTailEnergy y c r τ} := by
  rintro τ ⟨z, hz, hε'⟩
  have hmvi := normSq_eulerTailFun_le_integral_ball y hr h0 h1 hz τ
  have hX : ε ^ 2 ≤ ‖eulerTailFun y (z + τ * I)‖ ^ 2 := pow_le_pow_left₀ hε.le hε' 2
  have hJ : ε ^ 2 * (Real.pi * r ^ 2) ≤
      ∫ w in ball c (2 * r), ‖eulerTailFun y (w + τ * I)‖ ^ 2 := by
    have h := hX.trans hmvi
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h
    linarith
  show ENNReal.ofReal _ ≤ eulerDiscTailEnergy y c r τ
  unfold eulerDiscTailEnergy
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_normSq_eulerTailFun_shift_ball y hr h0 h1 τ)
    (Eventually.of_forall fun w => by
      show (0 : ℝ) ≤ ‖eulerTailFun y (w + τ * I)‖ ^ 2
      positivity)]
  exact ENNReal.ofReal_le_ofReal hJ

/-- Vertical window integral of the shifted Euler tail at one point `w` of the doubled disc,
bounded by the uniform window bound at the abscissa `Re w`. -/
theorem lintegral_window_shiftedEulerTail_le (y : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {V B : ℝ}
    (hV : 4 * (|c.im| + 2 * r) ≤ V)
    (hB : ∀ σ ∈ Icc (c.re - 2 * r) (c.re + 2 * r),
      (∫ t in V / 4..2 * V, ‖eulerLineTail y σ t‖ ^ 2) ≤ B)
    {w : ℂ} (hw : w ∈ ball c (2 * r)) :
    (∫⁻ τ in Icc (V / 2) V, ENNReal.ofReal (‖eulerTailFun y (w + τ * I)‖ ^ 2)) ≤
      ENNReal.ofReal B := by
  have hK0 : 0 ≤ |c.im| + 2 * r := by positivity
  have hV0 : 0 ≤ V := by linarith
  have hwre : w.re ∈ Icc (c.re - 2 * r) (c.re + 2 * r) :=
    ⟨(re_gt_of_mem_ball hw).le, (re_lt_of_mem_ball hw).le⟩
  have hwim : |w.im| ≤ |c.im| + 2 * r := by
    have h := im_sub_abs_lt_of_mem_ball hw
    have h2 := abs_sub_abs_le_abs_sub w.im c.im
    linarith
  have hne : w.re ≠ 1 := ne_of_lt (by linarith [re_lt_of_mem_ball hw])
  have hpos : 0 < w.re := by linarith [re_gt_of_mem_ball hw]
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖eulerLineTail y w.re t‖ ^ 2) with hg
  have hshift : ∀ τ : ℝ, ENNReal.ofReal (‖eulerTailFun y (w + τ * I)‖ ^ 2) = g (τ + w.im) := by
    intro τ
    rw [eulerTailFun_add_mul_I, add_comm]
  have htrans : (∫⁻ τ in Icc (V / 2) V, g (τ + w.im)) =
      ∫⁻ t in Icc (V / 2 + w.im) (V + w.im), g t := by
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
    calc (∫⁻ τ, (Icc (V / 2) V).indicator (fun τ => g (τ + w.im)) τ)
        = ∫⁻ τ, (Icc (V / 2 + w.im) (V + w.im)).indicator g (τ + w.im) := by
          congr 1
          funext τ
          by_cases hτ : τ ∈ Icc (V / 2) V
          · have hτ' : τ + w.im ∈ Icc (V / 2 + w.im) (V + w.im) :=
              ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
            rw [indicator_of_mem hτ, indicator_of_mem hτ']
          · have hτ' : τ + w.im ∉ Icc (V / 2 + w.im) (V + w.im) := by
              intro h
              exact hτ ⟨by linarith [h.1], by linarith [h.2]⟩
            rw [indicator_of_notMem hτ, indicator_of_notMem hτ']
      _ = ∫⁻ t, (Icc (V / 2 + w.im) (V + w.im)).indicator g t :=
          lintegral_add_right_eq_self _ _
  simp_rw [hshift]
  rw [htrans]
  have hsub : Icc (V / 2 + w.im) (V + w.im) ⊆ Icc (V / 4) (2 * V) := by
    intro t ht
    have ha := abs_le.mp hwim
    constructor <;> linarith [ht.1, ht.2, ha.1, ha.2]
  have hint : IntegrableOn (fun t => ‖eulerLineTail y w.re t‖ ^ 2) (Icc (V / 4) (2 * V)) :=
    ((continuous_eulerLineTail y hpos hne).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  calc (∫⁻ t in Icc (V / 2 + w.im) (V + w.im), g t)
      ≤ ∫⁻ t in Icc (V / 4) (2 * V), g t := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ t in Icc (V / 4) (2 * V), ‖eulerLineTail y w.re t‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => by
          show (0 : ℝ) ≤ ‖eulerLineTail y w.re t‖ ^ 2
          positivity)).symm
    _ = ENNReal.ofReal (∫ t in V / 4..2 * V, ‖eulerLineTail y w.re t‖ ^ 2) := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hB w.re hwre)

/-- **Markov bound on a dyadic window.**  If the window mean squares on `[V/4, 2V]` are at most
`B` for every abscissa of the doubled disc, the bad heights in `[V/2, V]` have measure at most
`4B/ε²`. -/
theorem volume_eulerDiscTailBadSet_window_le (y : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε : ℝ} (hε : 0 < ε) {V B : ℝ}
    (hV : 4 * (|c.im| + 2 * r) ≤ V) (hB0 : 0 ≤ B)
    (hB : ∀ σ ∈ Icc (c.re - 2 * r) (c.re + 2 * r),
      (∫ t in V / 4..2 * V, ‖eulerLineTail y σ t‖ ^ 2) ≤ B) :
    volume (eulerDiscTailBadSet y c r ε ∩ Icc (V / 2) V) ≤ ENNReal.ofReal (4 / ε ^ 2 * B) := by
  set a : ℝ := ε ^ 2 * (Real.pi * r ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have hmarkov : volume ({τ : ℝ | ENNReal.ofReal a ≤ eulerDiscTailEnergy y c r τ} ∩ Icc (V / 2) V)
      ≤ (∫⁻ τ in Icc (V / 2) V, eulerDiscTailEnergy y c r τ) / ENNReal.ofReal a := by
    rw [← Measure.restrict_apply' measurableSet_Icc,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr ha0).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact mul_meas_ge_le_lintegral₀ (measurable_eulerDiscTailEnergy y c r).aemeasurable _
  have hton : (∫⁻ τ in Icc (V / 2) V, eulerDiscTailEnergy y c r τ) =
      ∫⁻ w in ball c (2 * r), ∫⁻ τ in Icc (V / 2) V,
        ENNReal.ofReal (‖eulerTailFun y (w + τ * I)‖ ^ 2) := by
    unfold eulerDiscTailEnergy
    exact lintegral_lintegral_swap (measurable_shiftedEulerTailEnergyIntegrand y).aemeasurable
  have hinner : (∫⁻ w in ball c (2 * r), ∫⁻ τ in Icc (V / 2) V,
      ENNReal.ofReal (‖eulerTailFun y (w + τ * I)‖ ^ 2)) ≤
      ENNReal.ofReal B * volume (ball c (2 * r)) := by
    calc (∫⁻ w in ball c (2 * r), ∫⁻ τ in Icc (V / 2) V,
          ENNReal.ofReal (‖eulerTailFun y (w + τ * I)‖ ^ 2))
        ≤ ∫⁻ w in ball c (2 * r), ENNReal.ofReal B :=
          setLIntegral_mono' measurableSet_ball fun w hw =>
            lintegral_window_shiftedEulerTail_le y hr h0 h1 hV hB hw
      _ = ENNReal.ofReal B * volume (ball c (2 * r)) := setLIntegral_const _ _
  have hvol : volume (ball c (2 * r)) = ENNReal.ofReal (Real.pi * (2 * r) ^ 2) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow (by positivity),
      mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  calc volume (eulerDiscTailBadSet y c r ε ∩ Icc (V / 2) V)
      ≤ volume ({τ : ℝ | ENNReal.ofReal a ≤ eulerDiscTailEnergy y c r τ} ∩ Icc (V / 2) V) :=
        measure_mono (inter_subset_inter_left _ (eulerDiscTailBadSet_subset_energy_ge y hr h0 h1 hε))
    _ ≤ (∫⁻ τ in Icc (V / 2) V, eulerDiscTailEnergy y c r τ) / ENNReal.ofReal a := hmarkov
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (Real.pi * (2 * r) ^ 2) / ENNReal.ofReal a := by
        rw [hton, ← hvol]
        exact ENNReal.div_le_div_right hinner _
    _ = ENNReal.ofReal (4 / ε ^ 2 * B) := by
        rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_div_of_pos ha0]
        congr 1
        rw [ha]
        field_simp
        ring

/-! ## 8. The disc-uniform Carlson law for the Euler product -/

/-- **Disc-uniform Carlson tail law for the finite Euler product.**  Let `closedBall c (2r)` lie in
`1/2 < Re s < 1`.  For all large `y`, the heights `τ ∈ [0, T]` at which
`|ζ(z + iτ) − E_y(z + iτ)| ≥ ε` for some `z ∈ closedBall c r` have measure at most `δ T` for all
large `T`. -/
theorem eventually_eventually_volume_eulerDiscTailBadSet_le {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ y : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (eulerDiscTailBadSet y c r ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  set σ₀ : ℝ := c.re - 2 * r with hσ₀
  have hσ₀pos : 0 < σ₀ := by rw [hσ₀]; linarith
  set η : ℝ := δ * ε ^ 2 / 448 with hη
  have hη0 : 0 < η := by positivity
  filter_upwards [(tendsto_zetaCoefficientTailMass h0).eventually (gt_mem_nhds hη0)] with y hy
  -- a cutoff `M ≥ y` with small smooth tail mass
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((tendsto_smoothTailMass y hσ₀pos).eventually (gt_mem_nhds (Real.sqrt_pos.mpr hη0)))
  set M : ℕ := max y M₀ with hM
  have hmass : smoothTailMass y M σ₀ ^ 2 ≤ η := by
    have h := hM₀ M (le_max_right _ _)
    calc smoothTailMass y M σ₀ ^ 2 ≤ Real.sqrt η ^ 2 :=
          pow_le_pow_left₀ (smoothTailMass_nonneg y M σ₀) h.le 2
      _ = η := Real.sq_sqrt hη0.le
  have hτ0 := zetaCoefficientTailMass_nonneg y σ₀
  set θ : ℝ := 9 * zetaCoefficientTailMass y σ₀ + 4 * η + 3 * smoothTailMass y M σ₀ ^ 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθle : θ ≤ 16 * η := by rw [hθ]; linarith
  set β : ℝ := 7 * θ / ε ^ 2 with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβle : β ≤ δ / 4 := by
    rw [hβ, hη]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hwin : ∀ᶠ V : ℝ in atTop,
      volume (eulerDiscTailBadSet y c r ε ∩ Icc (V / 2) V) ≤ ENNReal.ofReal (β * V) := by
    filter_upwards [eventually_uniform_window_eulerLineTail_meanSquare_le y M (le_max_left _ _)
      h0 (by linarith) h1 hη0, eventually_ge_atTop (4 * (|c.im| + 2 * r)),
      eventually_ge_atTop (0 : ℝ)] with V hVwin hV4 hV0
    have hB0 : 0 ≤ 7 * V / 4 * θ := by positivity
    refine (volume_eulerDiscTailBadSet_window_le y hr h0 h1 hε hV4 hB0 hVwin).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hβ]
    ring
  filter_upwards [eventually_volume_inter_Icc_le_of_dyadic_window hβ0 hwin (half_pos hδ),
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have := mul_le_mul_of_nonneg_right (show 2 * β + δ / 2 ≤ δ by linarith) hT0
  linarith

end RHTower
