import GaloisForLFunctions.SuccessorShellArithmetic.TheShellsAloneCostTheSquareOfTheOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompletedShellEnergyIsAPositiveFourierIntegral
import GaloisForLFunctions.RHTower.LogWindowPrimeNumberTheorem

/-!
# The shells and the pole cancel on the top band

The separate payment of the shells costs `c²/ε` (`TheShellsAloneCostTheSquareOfTheOverlap`): along
the witness `x_η = b + η b1_T` the shells move by `2η Σ_T b_n R(n) ≍ ηGcq log N` while the defect
moves by `η² log N`. This file proves the positive survivor: the pole moments move by the same
amount, so the joint block `2·Pole − NR` has an `η`-coefficient of order `G(log N + c)` only.

* **The pole on the witness** (`poleMoments_topWitnessVector`): with `a_∓ = ∫ g e^{∓u/2}`,
  `(∫ f_η e^{−u/2})(∫ f_η e^{u/2}) = a₋a₊(H_N + ηS_T)(N + η|T|)`.
* **The pole row is a lattice sum of the pole moments** (`abs_poleRow_sub_le`): by a first-order
  cell comparison and the substitution `t = n e^u`,
  `∫ (log t/√t) β(log t − log n) dt = √n(a₋a₊ log n + ∫ u e^{u/2}β)`, because
  `∫ e^{u/2} β = a₋a₊` is the factorization of the autocorrelation's Laplace transform at `½`.
* **Cancellation** (`exists_abs_jointWitnessCoefficient_le`): the `η`-coefficient
  `a₋a₊(H_N|T| + N S_T) − Σ_T b_n R(n)` is `O(G(log N + c + 1))`, uniformly in `N`, while each of
  its two terms is `≍ Gcq log N`.

So the obstruction of the separate payment is removed by paying the shells together with the pole:
the `c`-linear parts are the same lattice-free quantity on both sides.
-/

noncomputable section

open MeasureTheory Finset Filter Topology intervalIntegral
open scoped Real

namespace GaloisForLFunctions.SuccessorShellArithmetic

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-! ### A first-order cell comparison -/

/-- **Cell comparison.** If `|F'| ≤ K` on `[a, a + m]`, the lattice sum of `F` and its integral
differ by at most `mK`. -/
theorem abs_sum_sub_integral_le_of_deriv {F F' : ℝ → ℝ} {a K : ℝ} {m : ℕ}
    (hd : ∀ t ∈ Set.Icc a (a + m), HasDerivAt F (F' t) t)
    (hb : ∀ t ∈ Set.Icc a (a + m), |F' t| ≤ K) :
    |∑ k ∈ range m, F (a + k) - ∫ t in a..a + m, F t| ≤ m * K := by
  have hcell : ∀ k < m, Set.Icc (a + k) (a + (k + 1 : ℕ)) ⊆ Set.Icc a (a + m) := by
    intro k hk t ht
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact ⟨by linarith only [ht.1, hk0], by linarith only [ht.2, hk']⟩
  have hint : ∀ k < m, IntervalIntegrable F volume (a + k) (a + (k + 1 : ℕ)) := by
    intro k hk
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by push_cast; linarith only)]
    exact fun t ht => (hd t (hcell k hk ht)).continuousAt.continuousWithinAt
  have hsum := sum_integral_adjacent_intervals (a := fun k : ℕ => a + k) hint
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum, ← sum_sub_distrib]
  have hK : ∀ k < m, |F (a + k) - ∫ t in a + k..a + (k + 1 : ℕ), F t| ≤ K := by
    intro k hk
    have hderiv : ∀ t ∈ Set.Icc (a + k) (a + (k + 1 : ℕ)),
        HasDerivWithinAt F (F' t) (Set.Icc (a + k) (a + (k + 1 : ℕ))) t :=
      fun t ht => (hd t (hcell k hk ht)).hasDerivWithinAt
    have hbd : ∀ t ∈ Set.Icc (a + k) (a + (k + 1 : ℕ)), ‖F' t‖ ≤ K :=
      fun t ht => hb t (hcell k hk ht)
    have hlo : a + k ∈ Set.Icc (a + k) (a + (k + 1 : ℕ)) :=
      ⟨le_rfl, by push_cast; linarith only⟩
    have hconst : F (a + k) = ∫ _t in a + k..a + (k + 1 : ℕ), F (a + k) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint k hk)]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a + k) (b := a + (k + 1 : ℕ)) (C := K) (f := fun t => F (a + k) - F t) (by
        intro t ht
        rw [Set.uIoc_of_le (by push_cast; linarith only)] at ht
        have htI : t ∈ Set.Icc (a + k) (a + (k + 1 : ℕ)) := ⟨ht.1.le, ht.2⟩
        have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd (convex_Icc _ _)
          hlo htI
        rw [norm_sub_rev] at h
        refine h.trans ?_
        have hK0 : 0 ≤ K := (abs_nonneg _).trans (hb _ (hcell k hk hlo))
        have ht1 : ‖t - (a + k)‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [ht.1])]
          have := ht.2; push_cast at this; linarith only [this]
        nlinarith only [ht1, hK0])
    have hlen : |a + ((k + 1 : ℕ) : ℝ) - (a + k)| = 1 := by push_cast; ring_nf; simp
    rw [hlen, mul_one] at hle
    exact hle
  calc
    _ ≤ ∑ k ∈ range m, |F (a + k) - ∫ t in a + k..a + (k + 1 : ℕ), F t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range m, K := sum_le_sum fun k hk => hK k (mem_range.mp hk)
    _ = m * K := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### The atom autocorrelation -/

section Autocorrelation

variable {φ : ℝ → ℝ}

/-- At width `w` the atom autocorrelation is the dilated profile autocorrelation. -/
theorem bumpCorr_atomDilate_eq {w : ℝ} (hw : 0 < w) (s : ℝ) :
    bumpCorr (atomDilate φ w) s = w * shellAutocorr φ (s / w) := by
  have h := Measure.integral_comp_div (fun y => φ y * φ (y + s / w)) w
  simp only [smul_eq_mul, abs_of_pos hw] at h
  unfold bumpCorr atomDilate
  rw [show (fun v => φ (v / w) * φ ((v + s) / w)) = fun v => φ (v / w) * φ (v / w + s / w) from
    funext fun v => by rw [add_div], h]
  rfl

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- The atom autocorrelation has derivative `A'(s/w)`, `A` the profile autocorrelation. -/
theorem hasDerivAt_bumpCorr_atomDilate {w : ℝ} (hw : 0 < w) (s : ℝ) :
    HasDerivAt (bumpCorr (atomDilate φ w)) (deriv (shellAutocorr φ) (s / w)) s := by
  have hA : HasDerivAt (shellAutocorr φ) (deriv (shellAutocorr φ) (s / w)) (s / w) :=
    ((contDiff_shellAutocorr hφ hsupp).differentiable (by norm_num) _).hasDerivAt
  have h := (hA.comp s ((hasDerivAt_id s).div_const w)).const_mul w
  rw [show (fun s => bumpCorr (atomDilate φ w) s) = fun s => w * (shellAutocorr φ ∘ fun x => x / w) s
    from funext fun s => bumpCorr_atomDilate_eq hw s] at *
  convert h using 1
  field_simp

/-- The profile autocorrelation has a bounded derivative. -/
theorem exists_abs_deriv_shellAutocorr_le :
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁ := by
  have hcs : HasCompactSupport (shellAutocorr φ) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => by
      apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨C, hC⟩ := hcs.deriv.exists_bound_of_continuous
    ((contDiff_shellAutocorr hφ hsupp).continuous_deriv (by norm_num))
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

end Autocorrelation

/-- **The Laplace factorization at `½`**: `∫ e^{u/2} β(u) du = a₋a₊`. -/
theorem integral_exp_half_mul_bumpCorr {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∫ u, Real.exp (u / 2) * bumpCorr g u =
      (∫ u, g u * Real.exp (-u / 2)) * ∫ u, g u * Real.exp (u / 2) := by
  rw [← RHTower.WeilOneSided.integral_autoCorr_mul_exp_half hg hgc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  change Real.exp (v / 2) * bumpCorr g v = RHTower.WeilOneSided.autoCorr g v * Real.exp (v / 2)
  rw [mul_comm, ← bumpCorr_neg (g := g) v]
  unfold bumpCorr RHTower.WeilOneSided.autoCorr
  simp only [sub_eq_add_neg]

end GaloisForLFunctions.SuccessorShellArithmetic
