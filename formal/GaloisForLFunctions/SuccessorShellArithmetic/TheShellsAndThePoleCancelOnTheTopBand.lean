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

theorem exp_half_log {n : ℕ} (hn : 1 ≤ n) : Real.exp (Real.log n / 2) = Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add, add_halves, Real.exp_log hn0]

theorem exp_neg_half_log {n : ℕ} (hn : 1 ≤ n) : Real.exp (-(Real.log n / 2)) = poleVector n := by
  rw [Real.exp_neg, exp_half_log hn, poleVector, one_div]

/-- The moments of an atomic test against `e^{∓u/2}` are its pole sums times the atom's weights. -/
theorem poleMoments_atomicTest {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) :
    (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N x g u * Real.exp (u / 2)) =
      poleWeightMinus g * poleWeightPlus g *
        ((∑ n ∈ Icc 1 N, x n * poleVector n) * ∑ n ∈ Icc 1 N, x n * Real.sqrt n) := by
  have hm := ArithmeticLorentzianGeometry.integral_atomicTest_mul (g := g)
    (φ := fun u => Real.exp (-(u / 2)))
    (Real.continuous_exp.comp (continuous_id.div_const 2).neg) hg hgsupp N x
  have hp := ArithmeticLorentzianGeometry.integral_atomicTest_mul (g := g)
    (φ := fun u => Real.exp (u / 2))
    (Real.continuous_exp.comp (continuous_id.div_const 2)) hg hgsupp N x
  have hshift : ∀ (n : ℕ) (s : ℝ), ∫ u, g (u - Real.log n) * Real.exp (s * (u / 2)) =
      Real.exp (s * (Real.log n / 2)) * ∫ u, g u * Real.exp (s * (u / 2)) := by
    intro n s
    have h := integral_sub_right_eq_self (μ := volume)
      (fun u => g u * Real.exp (s * ((u + Real.log n) / 2))) (Real.log n)
    simp only [sub_add_cancel] at h
    rw [h, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [show s * ((u + Real.log n) / 2) = s * (u / 2) + s * (Real.log n / 2) by ring,
      Real.exp_add]
    ring
  have hm' : ∫ u, atomicTest N x g u * Real.exp (-(u / 2)) =
      (∑ n ∈ Icc 1 N, x n * poleVector n) * poleWeightMinus g := by
    rw [hm, sum_mul]
    refine sum_congr rfl fun n hn => ?_
    have h := hshift n (-1)
    simp only [neg_one_mul] at h
    rw [h, exp_neg_half_log (mem_Icc.mp hn).1, poleWeightMinus]
    rw [show (fun u => g u * Real.exp (-(u / 2))) = fun u => g u * Real.exp (-u / 2) from
      funext fun u => by rw [neg_div]]
    ring
  have hp' : ∫ u, atomicTest N x g u * Real.exp (u / 2) =
      (∑ n ∈ Icc 1 N, x n * Real.sqrt n) * poleWeightPlus g := by
    rw [hp, sum_mul]
    refine sum_congr rfl fun n hn => ?_
    have h := hshift n 1
    simp only [one_mul] at h
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
    have hb2 := poleVector_sq n
    split_ifs
    · rw [add_mul, mul_assoc, ← sq, hb2]
    · rw [mul_zero, add_zero, add_zero, ← sq, hb2]
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
    · rw [add_mul, mul_assoc, hone n hn]
    · rw [add_mul, hone n hn]; ring
  rw [h1, h2]
  ring

/-! ### The row integrand -/

/-- The pole row as a function of a continuous partner `t`: `(log t/√t) β(log t − log n)`. -/
def rowIntegrand (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.log t * (Real.sqrt t)⁻¹ * bumpCorr g (Real.log t - Real.log n)

theorem rowIntegrand_natCast (g : ℝ → ℝ) (n ℓ : ℕ) :
    rowIntegrand g n ℓ = poleVector ℓ * Real.log ℓ * bumpCorr g (Real.log ℓ - Real.log n) := by
  rw [rowIntegrand, poleVector, one_div]; ring

section Row

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- The derivative of the row integrand:
`(t√t)⁻¹((1 − log t/2) β(u) + log t · A'(u/w))`, `u = log t − log n`. -/
theorem hasDerivAt_rowIntegrand {w : ℝ} (hw : 0 < w) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (rowIntegrand (atomDilate φ w) n)
      ((t * Real.sqrt t)⁻¹ * ((1 - Real.log t / 2) *
          bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
        Real.log t * deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hlog := Real.hasDerivAt_log ht.ne'
  have hinv := (Real.hasDerivAt_sqrt ht.ne').inv hs.ne'
  have hβ := (hasDerivAt_bumpCorr_atomDilate hφ hsupp hw (Real.log t - Real.log n)).comp t
    (hlog.sub_const (Real.log n))
  have h := (hlog.mul hinv).mul hβ
  have hf : rowIntegrand (atomDilate φ w) n = Real.log * (fun x => Real.sqrt x)⁻¹ *
      (bumpCorr (atomDilate φ w) ∘ fun x => Real.log x - Real.log n) := by
    funext x; simp only [rowIntegrand, Pi.mul_apply, Pi.inv_apply, Function.comp]
  rw [hf]
  refine h.congr_deriv ?_
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  simp only [Pi.mul_apply, Pi.inv_apply, Function.comp]
  field_simp
  rw [hsq]
  ring

/-- **The row integrand has derivative `O((1 + log 2n)(G + A₁)/n^{3/2})` on `[n/2, 2n]`.** -/
theorem abs_deriv_rowIntegrand_le {w A₁ : ℝ} (hw : 0 < w)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁) {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Set.Icc ((n : ℝ) / 2) (2 * n)) :
    |(t * Real.sqrt t)⁻¹ * ((1 - Real.log t / 2) *
          bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
        Real.log t * deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))| ≤
      ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * ((1 + Real.log (2 * n)) *
        ((∫ u, atomDilate φ w u ^ 2) + A₁)) := by
  have hn2 : (1 : ℝ) ≤ n / 2 := by
    rw [le_div_iff₀ two_pos]; exact_mod_cast (by omega : 1 * 2 ≤ n)
  have ht1 : 1 ≤ t := hn2.trans ht.1
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogle : Real.log t ≤ Real.log (2 * n) := Real.log_le_log ht0 ht.2
  have hgc : Continuous (atomDilate φ w) := hφ.continuous.comp (continuous_id.div_const w)
  have hgcs : HasCompactSupport (atomDilate φ w) := by
    refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc 0 w)) fun u hu => ?_
    apply hsupp
    intro h
    apply hu
    rw [Set.mem_Icc, le_div_iff₀ hw, div_le_iff₀ hw] at h
    constructor <;> nlinarith only [h.1, h.2, hw]
  have hβ := abs_bumpCorr_le hgc hgcs (Real.log t - Real.log n)
  have hA := hA₁ ((Real.log t - Real.log n) / w)
  have hA₀ : 0 ≤ A₁ := (abs_nonneg _).trans hA
  have hG : 0 ≤ ∫ u, atomDilate φ w u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hpos : 0 < t * Real.sqrt t := mul_pos ht0 (Real.sqrt_pos.mpr ht0)
  have hden : ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2)) ≤ t * Real.sqrt t :=
    mul_le_mul ht.1 (Real.sqrt_le_sqrt ht.1) (Real.sqrt_nonneg _) ht0.le
  have hinv : (t * Real.sqrt t)⁻¹ ≤ ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ :=
    inv_anti₀ (mul_pos (by positivity) (Real.sqrt_pos.mpr (by positivity))) hden
  have hbracket : |(1 - Real.log t / 2) * bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
      Real.log t * deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w)| ≤
      (1 + Real.log (2 * n)) * ((∫ u, atomDilate φ w u ^ 2) + A₁) := by
    have h1 : |1 - Real.log t / 2| ≤ 1 + Real.log (2 * n) := by
      rw [abs_le]; constructor <;> linarith only [hlog0, hlogle]
    have h2 : |Real.log t| ≤ 1 + Real.log (2 * n) := by
      rw [abs_of_nonneg hlog0]; linarith only [hlogle]
    calc
      _ ≤ |1 - Real.log t / 2| * |bumpCorr (atomDilate φ w) (Real.log t - Real.log n)| +
          |Real.log t| * |deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (1 + Real.log (2 * n)) * (∫ u, atomDilate φ w u ^ 2) +
          (1 + Real.log (2 * n)) * A₁ :=
        add_le_add (mul_le_mul h1 hβ (abs_nonneg _) (by linarith only [h2, abs_nonneg (Real.log t)]))
          (mul_le_mul h2 hA (abs_nonneg _) (by linarith only [h2, abs_nonneg (Real.log t)]))
      _ = _ := by ring
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  exact mul_le_mul hinv hbracket (abs_nonneg _) (inv_nonneg.mpr (by positivity))

/-- The atom vanishes at both ends of its support, so its autocorrelation vanishes for `|t| ≥ w`. -/
theorem bumpCorr_atomDilate_eq_zero_of_le {w t : ℝ} (hw : 0 < w) (ht : w ≤ |t|) :
    bumpCorr (atomDilate φ w) t = 0 := by
  have hopen : ∀ v, atomDilate φ w v ≠ 0 → 0 < v ∧ v < w := by
    intro v hv
    have hmem : v / w ∈ Set.Icc (0 : ℝ) 1 := by
      by_contra h; exact hv (hsupp _ h)
    have h0 : v / w ≠ 0 := fun h => hv (by simp only [atomDilate, h, profile_zero hφ hsupp])
    have h1 : v / w ≠ 1 := fun h => hv (by simp only [atomDilate, h, profile_one hφ hsupp])
    have hlo : 0 < v / w := lt_of_le_of_ne hmem.1 (Ne.symm h0)
    have hhi : v / w < 1 := lt_of_le_of_ne hmem.2 h1
    exact ⟨(div_pos_iff_of_pos_right hw).mp hlo, (div_lt_one hw).mp hhi⟩
  unfold bumpCorr
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)
  change atomDilate φ w v * atomDilate φ w (v + t) = 0
  by_contra hne
  obtain ⟨h1, h2⟩ := hopen v (left_ne_zero_of_mul hne)
  obtain ⟨h3, h4⟩ := hopen (v + t) (right_ne_zero_of_mul hne)
  have : |t| < w := abs_lt.mpr ⟨by linarith only [h2, h3], by linarith only [h1, h4]⟩
  linarith only [this, ht]

/-- The atom autocorrelation is continuous. -/
theorem continuous_bumpCorr_atomDilate {w : ℝ} (hw : 0 < w) :
    Continuous (bumpCorr (atomDilate φ w)) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_bumpCorr_atomDilate hφ hsupp hw s).continuousAt

/-- **The substitution `t = n e^u`.** Over any interval containing the support of the row,
`∫ (log t/√t) β(log t − log n) dt = √n(log n ∫ e^{u/2}β + ∫ u e^{u/2}β)`. -/
theorem integral_rowIntegrand {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ n * Real.exp (-w)) (hb : n * Real.exp w ≤ b) :
    ∫ t in a..b, rowIntegrand (atomDilate φ w) n t =
      Real.sqrt n * (Real.log n * (∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u) +
        ∫ u, u * Real.exp (u / 2) * bumpCorr (atomDilate φ w) u) := by
  set β := bumpCorr (atomDilate φ w) with hβdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβc : Continuous β := continuous_bumpCorr_atomDilate hφ hsupp hw
  have hβ0 : ∀ u, w ≤ |u| → β u = 0 := fun u hu => bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw hu
  set a' := Real.log (a / n)
  set b' := Real.log (b / n)
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have ha' : a' ≤ -w := by
    rw [← Real.log_exp (-w)]
    exact Real.log_le_log (div_pos ha hn0) (by rw [div_le_iff₀ hn0]; linarith only [hab])
  have hb' : w ≤ b' := by
    rw [← Real.log_exp w]
    exact Real.log_le_log (Real.exp_pos w) (by rw [le_div_iff₀ hn0]; linarith only [hb])
  have hab' : a' ≤ b' := by linarith only [ha', hb', hw]
  -- the substitution
  have hsub := integral_comp_mul_deriv' (a := a') (b := b') (f := fun u => n * Real.exp u)
    (f' := fun u => n * Real.exp u) (g := rowIntegrand (atomDilate φ w) n)
    (fun u _ => (Real.hasDerivAt_exp u).const_mul _) (by fun_prop) (by
      rintro t ⟨u, -, rfl⟩
      have ht : (0 : ℝ) < n * Real.exp u := by positivity
      refine ContinuousAt.continuousWithinAt ?_
      unfold rowIntegrand
      exact ((Real.continuousAt_log ht.ne').mul (Real.continuous_sqrt.continuousAt.inv₀
        (Real.sqrt_pos.mpr ht).ne')).mul
        (hβc.continuousAt.comp ((Real.continuousAt_log ht.ne').sub continuousAt_const)))
  have hfa : (n : ℝ) * Real.exp a' = a := by
    simp only [a']; rw [Real.exp_log (div_pos ha hn0)]; field_simp
  have hfb : (n : ℝ) * Real.exp b' = b := by
    simp only [b']; rw [Real.exp_log (div_pos hb0 hn0)]; field_simp
  rw [hfa, hfb] at hsub
  rw [← hsub]
  -- the transformed integrand
  have hpt : ∀ u, (rowIntegrand (atomDilate φ w) n ∘ fun u => (n : ℝ) * Real.exp u) u *
      ((n : ℝ) * Real.exp u) =
      Real.sqrt n * ((Real.log n * (Real.exp (u / 2) * β u)) + u * Real.exp (u / 2) * β u) := by
    intro u
    have he : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
      rw [← Real.sqrt_sq (Real.exp_pos (u / 2)).le, sq, ← Real.exp_add, add_halves]
    have hlog : Real.log ((n : ℝ) * Real.exp u) = Real.log n + u := by
      rw [Real.log_mul hn0.ne' (Real.exp_pos u).ne', Real.log_exp]
    have hsq : Real.sqrt ((n : ℝ) * Real.exp u) = Real.sqrt n * Real.exp (u / 2) := by
      rw [Real.sqrt_mul hn0.le, he]
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hex : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
      rw [← Real.exp_add, add_halves]
    simp only [Function.comp, rowIntegrand, hlog, hsq, add_sub_cancel_left]
    rw [← hβdef, hex]
    field_simp
    rw [Real.sq_sqrt hn0.le]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  -- the support of `β` lies inside `[a', b']`
  have hint1 : Integrable (fun u => Real.exp (u / 2) * β u) := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_)
    exact HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-w) w)) fun u hu =>
      by rw [hβ0 u (by
        simp only [Set.mem_Icc, not_and_or, not_le] at hu
        rcases hu with hu | hu
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  have hint2 : Integrable (fun u => u * Real.exp (u / 2) * β u) := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_)
    exact HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-w) w)) fun u hu =>
      by rw [hβ0 u (by
        simp only [Set.mem_Icc, not_and_or, not_le] at hu
        rcases hu with hu | hu
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  rw [intervalIntegral.integral_of_le hab', ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_add (hint1.const_mul _) hint2]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
  have hu' : w ≤ |u| := by
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hβ0 u hu']
  ring

/-- **The pole row is a lattice sum of the pole moments.** For `n` in the top band,
`b_n R(n) = log n · ∫e^{u/2}β + ∫ u e^{u/2}β − G log n/n + O(b_n (n(e^w − e^{−w}) + 2) K_n)`,
`K_n = ((n/2)√(n/2))⁻¹(1 + log 2n)(G + A₁)`. -/
theorem abs_poleRow_sub_le {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁) {N n : ℕ} (hN : 8 ≤ N)
    (hnT : n ∈ topBand N w) :
    |poleVector n * shellPoleRow (atomDilate φ w) N w n -
        (Real.log n * (∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u) +
          ∫ u, u * Real.exp (u / 2) * bumpCorr (atomDilate φ w) u) +
        (∫ u, atomDilate φ w u ^ 2) * Real.log n / n| ≤
      poleVector n * ((n * (Real.exp w - Real.exp (-w)) + 2) *
        (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * ((1 + Real.log (2 * n)) *
          ((∫ u, atomDilate φ w u ^ 2) + A₁)))) := by
  set g := atomDilate φ w with hgdef
  set β := bumpCorr g with hβdef
  set G := ∫ u, g u ^ 2 with hGdef
  set P := ∫ u, Real.exp (u / 2) * β u
  set I₁ := ∫ u, u * Real.exp (u / 2) * β u
  set K := ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * ((1 + Real.log (2 * n)) * (G + A₁))
  set L := ⌈(N : ℝ) * Real.exp w⌉₊
  obtain ⟨hnI, hn2⟩ := mem_topBand.mp hnT
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hNR : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hNn : (N : ℝ) < 2 * n := by
    have := Real.add_one_le_exp w
    nlinarith only [hn2, this, hw, hNR]
  have hn4 : (4 : ℝ) ≤ n := by linarith only [hNn, hNR]
  -- the exponentials are close to one
  have hem : 3 / 4 ≤ Real.exp (-w) := by
    have := Real.add_one_le_exp (-w); linarith only [this, hw4]
  have hep : Real.exp w ≤ 4 / 3 := by
    have h1 : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith only [h1, hem, Real.exp_pos w]
  have hew2 : Real.exp w < 2 := by linarith only [hep]
  -- the cells
  set A := ⌊(n : ℝ) * Real.exp (-w)⌋₊ with hAdef
  set B := ⌊(n : ℝ) * Real.exp w⌋₊ with hBdef
  have hAle : (A : ℝ) ≤ n * Real.exp (-w) := Nat.floor_le (by positivity)
  have hAgt : (n : ℝ) * Real.exp (-w) < A + 1 := Nat.lt_floor_add_one _
  have hBle : (B : ℝ) ≤ n * Real.exp w := Nat.floor_le (by positivity)
  have hBgt : (n : ℝ) * Real.exp w < B + 1 := Nat.lt_floor_add_one _
  have hAn : (n : ℝ) / 2 ≤ A := by nlinarith only [hAgt, hem, hn4]
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ A := by linarith only [hAn, hn4]
    exact_mod_cast this
  have hAB : A ≤ B + 1 := by
    have e1 : (n : ℝ) * Real.exp (-w) ≤ n :=
      mul_le_of_le_one_right hn0.le (Real.exp_le_one_iff.mpr (by linarith only [hw]))
    have e2 : (n : ℝ) ≤ n * Real.exp w :=
      le_mul_of_one_le_right hn0.le (Real.one_le_exp_iff.mpr hw.le)
    have : (A : ℝ) ≤ B + 1 := by linarith only [hAle, e1, e2, hBgt]
    exact_mod_cast this
  have hB2n : (B : ℝ) + 1 ≤ 2 * n := by nlinarith only [hBle, hep, hn4]
  have hBL : B ≤ L := by
    have h1 : (B : ℝ) ≤ N * Real.exp w :=
      hBle.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) (Real.exp_pos w).le)
    exact_mod_cast h1.trans (Nat.le_ceil _)
  set m := B + 1 - A with hmdef
  have hmR : (m : ℝ) = B + 1 - A := by rw [hmdef, Nat.cast_sub hAB]; push_cast; ring
  -- the prime-free row as a lattice sum
  have hrow : shellPoleRow g N w n =
      ∑ k ∈ range m, rowIntegrand g n ((A : ℝ) + k) - poleVector n * Real.log n * G := by
    rw [shellPoleRow_eq_log hew2]
    have hsplit : ∀ ℓ ∈ Icc 1 L, poleVector ℓ * Real.log ℓ *
        (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) =
        rowIntegrand g n ℓ - if ℓ = n then poleVector n * Real.log n * G else 0 := by
      intro ℓ _
      rw [rowIntegrand_natCast]
      split_ifs with h
      · subst h; rw [sub_self, bumpCorr_zero]; ring
      · ring
    have hnL : n ∈ Icc 1 L := mem_Icc.mpr ⟨hn1, (by
      have : (n : ℝ) ≤ N * Real.exp w := (by exact_mod_cast hnN : (n : ℝ) ≤ N).trans
        (le_mul_of_one_le_right (Nat.cast_nonneg N) (Real.one_le_exp_iff.mpr hw.le))
      exact_mod_cast this.trans (Nat.le_ceil _))⟩
    rw [sum_congr rfl hsplit, sum_sub_distrib, sum_ite_eq' (Icc 1 L) n, if_pos hnL]
    congr 1
    -- only the cells `A ≤ ℓ ≤ B` carry the row
    have hsub : Icc A B ⊆ Icc 1 L := fun ℓ hℓ =>
      mem_Icc.mpr ⟨hA1.trans (mem_Icc.mp hℓ).1, (mem_Icc.mp hℓ).2.trans hBL⟩
    rw [← sum_subset hsub fun ℓ hℓL hℓ => ?_]
    · rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      rfl
    · have hℓ1 := (mem_Icc.mp hℓL).1
      have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
      rw [rowIntegrand_natCast, bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw, mul_zero]
      simp only [mem_Icc, not_and_or, not_le] at hℓ
      rcases hℓ with hℓ | hℓ
      · have hlt : (ℓ : ℝ) < n * Real.exp (-w) := by
          have : ℓ + 1 ≤ A := hℓ
          have : (ℓ : ℝ) + 1 ≤ A := by exact_mod_cast this
          linarith only [this, hAle]
        have := Real.log_lt_log hℓ0 hlt
        rw [Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
        rw [abs_of_neg (by linarith only [this, hw])]
        linarith only [this]
      · have hlt : (n : ℝ) * Real.exp w < ℓ := by
          have : B + 1 ≤ ℓ := hℓ
          have : (B : ℝ) + 1 ≤ ℓ := by exact_mod_cast this
          linarith only [this, hBgt]
        have := Real.log_lt_log (by positivity) hlt
        rw [Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
        rw [abs_of_pos (by linarith only [this, hw])]
        linarith only [this]
  -- the cell comparison
  have hcells : (A : ℝ) + m = B + 1 := by rw [hmR]; ring
  have hderiv : ∀ t ∈ Set.Icc (A : ℝ) (A + m), HasDerivAt (rowIntegrand g n)
      ((t * Real.sqrt t)⁻¹ * ((1 - Real.log t / 2) * bumpCorr g (Real.log t - Real.log n) +
        Real.log t * deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))) t := by
    intro t ht
    exact hasDerivAt_rowIntegrand hφ hsupp hw n (by linarith only [ht.1, hAn, hn4])
  have hbound : ∀ t ∈ Set.Icc (A : ℝ) (A + m),
      |(t * Real.sqrt t)⁻¹ * ((1 - Real.log t / 2) * bumpCorr g (Real.log t - Real.log n) +
        Real.log t * deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))| ≤ K := by
    intro t ht
    refine abs_deriv_rowIntegrand_le hφ hsupp hw hA₁ (by exact_mod_cast (by
      have : (2 : ℝ) ≤ n := by linarith only [hn4]
      exact_mod_cast this : 2 ≤ n)) ⟨hAn.trans ht.1, ?_⟩
    rw [hcells] at ht; linarith only [ht.2, hB2n]
  have hcmp := abs_sum_sub_integral_le_of_deriv hderiv hbound
  have hint := integral_rowIntegrand hφ hsupp hw hn1 (a := A) (b := A + m)
    (by linarith only [hAn, hn4]) hAle (by rw [hcells]; exact hBgt.le)
  rw [hint] at hcmp
  -- assemble with the weight `b_n = 1/√n`
  have hbn : poleVector n * Real.sqrt n = 1 := by
    rw [poleVector]; field_simp
  have hbn2 : poleVector n * (poleVector n * Real.log n * G) = G * Real.log n / n := by
    rw [← mul_assoc, ← mul_assoc, ← sq, poleVector_sq]; ring
  have hb0 : 0 ≤ poleVector n := by unfold poleVector; positivity
  have hm : (m : ℝ) ≤ n * (Real.exp w - Real.exp (-w)) + 2 := by
    rw [hmR]; nlinarith only [hBle, hAgt]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hbound A ⟨le_rfl, by
    have := Nat.cast_nonneg (α := ℝ) m; linarith only [this]⟩)
  rw [hrow, mul_sub, hbn2]
  calc
    _ = |poleVector n * (∑ k ∈ range m, rowIntegrand g n ((A : ℝ) + k) -
          Real.sqrt n * (Real.log n * P + I₁))| := by
      congr 1
      rw [mul_sub, ← mul_assoc (poleVector n) (Real.sqrt n), hbn, one_mul]
      ring
    _ ≤ poleVector n * (m * K) := by
      rw [abs_mul, abs_of_nonneg hb0]
      exact mul_le_mul_of_nonneg_left hcmp hb0
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hK0) hb0

end Row

end GaloisForLFunctions.SuccessorShellArithmetic
