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
  have hf : bumpCorr (atomDilate φ w) = fun y => w * (shellAutocorr φ ∘ fun x => id x / w) y :=
    funext fun y => bumpCorr_atomDilate_eq hw y
  have h2 : w * (deriv (shellAutocorr φ) (s / w) * (1 / w)) = deriv (shellAutocorr φ) (s / w) := by
    rw [one_div, mul_left_comm, mul_inv_cancel₀ hw.ne', mul_one]
  rw [hf, ← h2]
  exact h

/-- The profile autocorrelation has a bounded derivative. -/
theorem exists_abs_deriv_shellAutocorr_le :
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁ := by
  have hcs : HasCompactSupport (shellAutocorr φ) :=
    HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)) fun x hx => by
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

/-! ### The pole on the witness -/

/-- The pole weights of the atom: `a₋ = ∫ g e^{−u/2}`, `a₊ = ∫ g e^{u/2}`. -/
def poleWeightMinus (g : ℝ → ℝ) : ℝ := ∫ u, g u * Real.exp (-u / 2)

/-- The pole weight `a₊ = ∫ g e^{u/2}`. -/
def poleWeightPlus (g : ℝ → ℝ) : ℝ := ∫ u, g u * Real.exp (u / 2)

theorem exp_neg_half_log {n : ℕ} (hn : 1 ≤ n) : Real.exp (-(Real.log n / 2)) = poleVector n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [poleVector, Real.sqrt_eq_rpow, Real.exp_neg, ← Real.rpow_natCast, one_div,
    ← Real.exp_log (Real.rpow_pos_of_pos hn0 _), Real.log_rpow hn0]
  congr 2
  ring

theorem exp_half_log {n : ℕ} (hn : 1 ≤ n) : Real.exp (Real.log n / 2) = Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.exp_log (Real.rpow_pos_of_pos hn0 _), Real.log_rpow hn0]
  congr 1
  ring

/-- The moments of an atomic test against `e^{∓u/2}` are its pole sums times the atom's weights. -/
theorem poleMoments_atomicTest {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) :
    (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N x g u * Real.exp (u / 2)) =
      poleWeightMinus g * poleWeightPlus g *
        ((∑ n ∈ Icc 1 N, x n * poleVector n) * ∑ n ∈ Icc 1 N, x n * Real.sqrt n) := by
  have hm := ArithmeticLorentzianGeometry.integral_atomicTest_mul (g := g)
    (Real.continuous_exp.comp (continuous_id.div_const 2).neg) hg hgsupp N x
  have hp := ArithmeticLorentzianGeometry.integral_atomicTest_mul (g := g)
    (Real.continuous_exp.comp (continuous_id.div_const 2)) hg hgsupp N x
  have hshift : ∀ (n : ℕ) (s : ℝ), ∫ u, g (u - Real.log n) * Real.exp (s * (u / 2)) =
      Real.exp (s * (Real.log n / 2)) * ∫ u, g u * Real.exp (s * (u / 2)) := by
    intro n s
    have h := integral_sub_right_eq_self (μ := volume)
      (fun u => g u * Real.exp (s * ((u + Real.log n) / 2))) (Real.log n)
    simp only [sub_add_cancel] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [show s * ((u + Real.log n) / 2) = s * (u / 2) + s * (Real.log n / 2) by ring,
      Real.exp_add]
    ring
  have hm' : ∫ u, atomicTest N x g u * Real.exp (-(u / 2)) =
      (∑ n ∈ Icc 1 N, x n * poleVector n) * poleWeightMinus g := by
    rw [show (fun u => atomicTest N x g u * Real.exp (-(u / 2))) =
      fun u => atomicTest N x g u * (Real.exp ∘ fun u => -(u / 2)) u from rfl, hm, sum_mul]
    refine sum_congr rfl fun n hn => ?_
    have h := hshift n (-1)
    simp only [neg_one_mul] at h
    simp only [Function.comp]
    rw [h, exp_neg_half_log (mem_Icc.mp hn).1, poleWeightMinus]
    rw [show (fun u => g u * Real.exp (-(u / 2))) = fun u => g u * Real.exp (-u / 2) from
      funext fun u => by rw [neg_div]]
    ring
  have hp' : ∫ u, atomicTest N x g u * Real.exp (u / 2) =
      (∑ n ∈ Icc 1 N, x n * Real.sqrt n) * poleWeightPlus g := by
    rw [show (fun u => atomicTest N x g u * Real.exp (u / 2)) =
      fun u => atomicTest N x g u * (Real.exp ∘ fun u => u / 2) u from rfl, hp, sum_mul]
    refine sum_congr rfl fun n hn => ?_
    have h := hshift n 1
    simp only [one_mul] at h
    simp only [Function.comp]
    rw [h, exp_half_log (mem_Icc.mp hn).1, poleWeightPlus]
    ring
  rw [hm', hp']
  ring

/-- **The pole on the witness**: `Pole(x_η) = a₋a₊(H_N + ηS_T)(N + η|T|)`. -/
theorem poleMoments_topWitnessVector {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (η : ℝ) :
    (∫ u, atomicTest N (topWitnessVector N w η) g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N (topWitnessVector N w η) g u * Real.exp (u / 2)) =
      poleWeightMinus g * poleWeightPlus g *
        ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) + η * ∑ n ∈ topBand N w, 1 / (n : ℝ)) *
          ((N : ℝ) + η * (topBand N w).card) := by
  rw [poleMoments_atomicTest hg hgsupp]
  have hT : ∀ F : ℕ → ℝ, ∑ n ∈ Icc 1 N, (if n ∈ topBand N w then F n else 0) =
      ∑ n ∈ topBand N w, F n := by
    intro F
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(mem_topBand.mp h).1, h⟩⟩
  have h1 : ∑ n ∈ Icc 1 N, topWitnessVector N w η n * poleVector n =
      (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) + η * ∑ n ∈ topBand N w, 1 / (n : ℝ) := by
    rw [← hT, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [topWitnessVector, topWitness]
    split_ifs <;> simp [add_mul, ← sq, poleVector_sq]
  have h2 : ∑ n ∈ Icc 1 N, topWitnessVector N w η n * Real.sqrt n =
      (N : ℝ) + η * (topBand N w).card := by
    have hone : ∀ n ∈ Icc 1 N, poleVector n * Real.sqrt n = 1 := by
      intro n hn
      have hn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)
      rw [poleVector]; field_simp
    have hcardT : ((topBand N w).card : ℝ) = ∑ n ∈ topBand N w, (1 : ℝ) := by simp
    have hcardN : (N : ℝ) = ∑ n ∈ Icc 1 N, (1 : ℝ) := by simp
    rw [hcardT, hcardN, ← hT, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    simp only [topWitnessVector, topWitness]
    split_ifs
    · rw [add_mul, mul_assoc, hone n hn]; ring
    · rw [add_mul, hone n hn]; ring
  rw [h1, h2]
  ring

end GaloisForLFunctions.SuccessorShellArithmetic
