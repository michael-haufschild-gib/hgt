import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailWindowRieszCoercivity
import GaloisForLFunctions.RHTower.PoissonSummationPiecewise
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanIntervalMeanSquare

/-! Bernoulli harmonic expansion of the factorial phase profiles and Montgomery–Vaughan bounds
for each harmonic layer.

The periodic clamped kernel `C(u) = {u}(1 - {u})/2` has the absolutely convergent cosine series
`C(u) = 1/12 - (1/(2π²)) ∑_{k ≥ 1} cos(2πku)/k²`. Reading it on the multiples of `1, 2, 4` and
combining with the dyadic stencil `P(u) = C(4u)/4 - 2C(2u) + 4C(u)` gives
`P(u) - 3/16 = -(2/π²) ∑_{k ≥ 1} χ(k) cos(2πku)/k²` with `χ(k) = 1 - 2[2 ∣ k] + [4 ∣ k]`.
For a finite complex family `b`, the combination `B_b(v) = ∑_{n ∈ S} b_n Φ_{n+1}(v)` of the phase
profiles `Φ_N(v) = P(λ_N v) - P(N v)` therefore expands as
`B_b = -(2/π²) ∑_k w_k H_k` with `w_k = χ(k)/k²` and harmonic layers
`H_k(v) = ∑_n b_n (cos(2πkλ_{n+1}v) - cos(2πk(n+1)v))`.

Each dilated layer `H_k(r v)`, `r ≥ 1`, is an exponential sum over the four signed branches
`± k r (n + 1)`, `± k r λ_{n+1}` with coefficients `∓ b_n / 2`; the collar bounds separate these
frequencies by `k / 15`, so the Montgomery–Vaughan interval inequalities give
`(ℓ - K/k) ∑‖b_n‖² ≤ ∫_a^{a+ℓ} ‖H_k(r v)‖² dv ≤ (ℓ + K/k) ∑‖b_n‖²` with `K = 390/π`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- Transport of a sum along pointwise and value equalities. -/
theorem hasSum_of_eq_of_eq {α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f g : ℕ → α}
    {a c : α} (h : HasSum f a) (hfg : ∀ k, g k = f k) (hac : a = c) : HasSum g c :=
  hac ▸ h.congr_fun hfg

/-- Bernoulli cosine series of the periodic clamped kernel:
`∑_{k ≥ 1} cos(2πku) / k² = 2π² (1/12 - C(u))`. -/
theorem periodicClampedKernel_hasSum_cos (u : ℝ) :
    HasSum (fun k : ℕ => Real.cos (2 * Real.pi * k * u) / (k : ℝ) ^ 2)
      (2 * Real.pi ^ 2 * (1 / 12 - periodicClampedKernel u)) := by
  have h := GaloisForLFunctions.RHTower.hasSum_cos_div_sq u
  have he : GaloisForLFunctions.RHTower.sawPrimitive u = periodicClampedKernel u := by
    rw [periodicClampedKernel_eq_fract, GaloisForLFunctions.RHTower.sawPrimitive]
    ring
  rwa [he] at h

/-- The cosine series of `C(d u)` read on the multiples of `d`. -/
theorem periodicClampedKernel_mul_hasSum_cos {d : ℕ} (hd : 1 ≤ d) (u : ℝ) :
    HasSum (fun k : ℕ => if d ∣ k then (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * k * u) / (k : ℝ) ^ 2
      else 0) (2 * Real.pi ^ 2 * (1 / 12 - periodicClampedKernel ((d : ℝ) * u))) := by
  have hinj : Function.Injective (fun n : ℕ => d * n) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (by omega) h
  refine (hinj.hasSum_iff fun k hk => ?_).mp ?_
  · rw [if_neg]
    rintro ⟨m, rfl⟩
    exact hk ⟨m, rfl⟩
  · refine (periodicClampedKernel_hasSum_cos ((d : ℝ) * u)).congr_fun fun n => ?_
    simp only [Function.comp_apply, dvd_mul_right, if_true]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      push_cast
      field_simp

/-- The dyadic harmonic sign as a divisor indicator: `χ(k) = 1 - 2 [2 ∣ k] + [4 ∣ k]`. -/
theorem dyadicHarmonicChi_eq_indicator (k : ℕ) :
    dyadicHarmonicChi k = 4 / 4 - 2 * (if 2 ∣ k then 1 else 0) + (if 4 ∣ k then 1 else 0) := by
  unfold dyadicHarmonicChi
  by_cases h1 : k % 2 = 1
  · have h2 : ¬ 2 ∣ k := by omega
    have h4 : ¬ 4 ∣ k := by omega
    simp [h1, h2, h4]
  · by_cases h3 : k % 4 = 2
    · have h2 : 2 ∣ k := by omega
      have h4 : ¬ 4 ∣ k := by omega
      simp [h1, h3, h2, h4]
      norm_num
    · have h2 : 2 ∣ k := by omega
      have h4 : 4 ∣ k := by omega
      simp [h1, h3, h2, h4]
      norm_num

/-- **Bernoulli expansion of the dyadic filter.** For every real `u`,
`∑_{k ≥ 1} χ(k) cos(2πku) / k² = -(π² / 2) P₀(u)`, where `P₀ = P - 3/16`. -/
theorem dyadicCenteredBernoulliFilter_hasSum (u : ℝ) :
    HasSum (fun k : ℕ => dyadicHarmonicChi k * Real.cos (2 * Real.pi * k * u) / (k : ℝ) ^ 2)
      (-(Real.pi ^ 2 / 2) * dyadicCenteredBernoulliFilter u) := by
  have h1 := periodicClampedKernel_mul_hasSum_cos (d := 1) le_rfl u
  have h2 := periodicClampedKernel_mul_hasSum_cos (d := 2) (by norm_num) u
  have h4 := periodicClampedKernel_mul_hasSum_cos (d := 4) (by norm_num) u
  have hc := ((h4.mul_left (1 / 16)).sub (h2.mul_left (1 / 2))).add (h1.mul_left 1)
  refine hasSum_of_eq_of_eq hc (fun k => ?_) ?_
  · rw [dyadicHarmonicChi_eq_indicator]
    simp only [one_dvd, if_true]
    split_ifs <;> push_cast <;> ring
  · unfold dyadicCenteredBernoulliFilter dyadicBernoulliFilter
    push_cast
    ring_nf

/-- **Bernoulli expansion of a factorial phase profile.** For every `N` and real `v`,
`∑_{k ≥ 1} (χ(k) / k²) (cos(2πkλ_N v) - cos(2πkN v)) = -(π² / 2) Φ_N(v)`. -/
theorem factorialPhaseProfile_hasSum (N : ℕ) (v : ℝ) :
    HasSum (fun k : ℕ => dyadicHarmonicChi k / (k : ℝ) ^ 2 *
      (Real.cos (2 * Real.pi * k * (factorialShiftedFreq N * v)) -
        Real.cos (2 * Real.pi * k * ((N : ℝ) * v))))
      (-(Real.pi ^ 2 / 2) * factorialPhaseProfile N v) := by
  have h := (dyadicCenteredBernoulliFilter_hasSum (factorialShiftedFreq N * v)).sub
    (dyadicCenteredBernoulliFilter_hasSum ((N : ℝ) * v))
  rw [factorialPhaseProfile_eq_centered]
  exact hasSum_of_eq_of_eq h (fun k => by ring) (by ring)

/-- The dyadic harmonic weight `w_k = χ(k) / k²`. -/
def dyadicHarmonicWeight (k : ℕ) : ℝ :=
  dyadicHarmonicChi k / (k : ℝ) ^ 2

theorem abs_dyadicHarmonicWeight_le (k : ℕ) : |dyadicHarmonicWeight k| ≤ 1 / (k : ℝ) ^ 2 := by
  unfold dyadicHarmonicWeight
  rw [abs_div, abs_of_nonneg (sq_nonneg (k : ℝ))]
  exact div_le_div_of_nonneg_right (abs_dyadicHarmonicChi_le_one k) (sq_nonneg _)

theorem summable_abs_dyadicHarmonicWeight : Summable fun k => |dyadicHarmonicWeight k| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_dyadicHarmonicWeight_le
    (Real.summable_one_div_nat_pow.mpr one_lt_two)

@[simp] theorem dyadicHarmonicWeight_zero : dyadicHarmonicWeight 0 = 0 := by
  simp [dyadicHarmonicWeight]

@[simp] theorem dyadicHarmonicWeight_one : dyadicHarmonicWeight 1 = 1 := by
  simp [dyadicHarmonicWeight]

/-- The higher-harmonic tail `∑_{k ≥ 2} |χ(k)| / k² ≤ 3/4`. -/
theorem tsum_abs_dyadicHarmonicWeight_tail_le :
    ∑' k, |dyadicHarmonicWeight (k + 2)| ≤ 3 / 4 := by
  have hs : Summable fun k => |dyadicHarmonicWeight (k + 2)| :=
    (summable_nat_add_iff 2).mpr summable_abs_dyadicHarmonicWeight
  refine hs.tsum_le_of_sum_range_le fun M => ?_
  have h := sum_Icc_two_abs_dyadicHarmonicChi_div_sq_le (M + 1)
  have he : (∑ k ∈ Finset.range M, |dyadicHarmonicWeight (k + 2)|) =
      ∑ k ∈ Finset.Icc 2 (M + 1), |dyadicHarmonicChi k| / (k : ℝ) ^ 2 := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k => |dyadicHarmonicWeight k|) 0 M 2,
      zero_add, ← Finset.Ico_add_one_right_eq_Icc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold dyadicHarmonicWeight
    rw [abs_div, abs_of_nonneg (sq_nonneg (k : ℝ))]
  rw [he]
  exact h

/-- The total harmonic weight `∑_{k ≥ 1} |χ(k)| / k² ≤ 7/4`. -/
theorem tsum_abs_dyadicHarmonicWeight_le : ∑' k, |dyadicHarmonicWeight k| ≤ 7 / 4 := by
  rw [summable_abs_dyadicHarmonicWeight.tsum_eq_zero_add,
    ((summable_nat_add_iff 1).mpr summable_abs_dyadicHarmonicWeight).tsum_eq_zero_add]
  simp only [zero_add, dyadicHarmonicWeight_zero, abs_zero, dyadicHarmonicWeight_one, abs_one]
  have h := tsum_abs_dyadicHarmonicWeight_tail_le
  simp only [show ∀ k : ℕ, k + 1 + 1 = k + 2 from fun k => rfl]
  linarith

/-- The `k`-th harmonic layer of a finite complex phase combination,
`H_k(v) = ∑_{n ∈ S} b_n (cos(2πkλ_{n+1}v) - cos(2πk(n+1)v))`. -/
def factorialHarmonicLayer (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) (v : ℝ) : ℂ :=
  ∑ n ∈ S, b n * ((Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v)) -
    Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v)) : ℝ) : ℂ)

/-- A finite complex combination of factorial phase profiles,
`B_b(v) = ∑_{n ∈ S} b_n Φ_{n+1}(v)`. -/
def factorialPhaseCombination (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) : ℂ :=
  ∑ n ∈ S, b n * (factorialPhaseProfile (n + 1) v : ℂ)

/-- **Harmonic expansion of a phase combination.** For every real `v`,
`∑_{k ≥ 1} w_k H_k(v) = -(π² / 2) B_b(v)`, with `w_k = χ(k) / k²`. -/
theorem factorialPhaseCombination_hasSum (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    HasSum (fun k => (dyadicHarmonicWeight k : ℂ) * factorialHarmonicLayer S b k v)
      (-((Real.pi ^ 2 / 2 : ℝ) : ℂ) * factorialPhaseCombination S b v) := by
  have hn (n : ℕ) := ((Complex.hasSum_ofReal.mpr
    (factorialPhaseProfile_hasSum (n + 1) v)).mul_left (b n))
  have h := hasSum_sum (s := S) fun n _ => hn n
  refine hasSum_of_eq_of_eq h (fun k => ?_) ?_
  · unfold factorialHarmonicLayer dyadicHarmonicWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  · unfold factorialPhaseCombination
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring

/-- Signed branch coefficients: `-b/2` on the integer branches and `b/2` on the shifted ones. -/
def factorialBranchCoeff (b : ℕ → ℂ) (i : ℕ × Fin 4) : ℂ :=
  if i.2.val % 2 = 0 then -(b i.1 / 2) else b i.1 / 2

theorem mvExp_add_mvExp_neg (u α : ℝ) :
    HTGeometry.mvExp u α + HTGeometry.mvExp (-u) α =
      2 * ((Real.cos (2 * Real.pi * u * α) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  unfold HTGeometry.mvExp
  push_cast
  ring_nf

/-- **Exponential-sum form of a dilated harmonic layer.** The layer `H_k(r v)` is the
exponential sum over the four signed branches with frequencies `r · factorialHarmonicBranchFreq`
and coefficients `± b / 2`. -/
theorem factorialHarmonicLayer_eq_expSum (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) (r v : ℝ) :
    factorialHarmonicLayer S b k (r * v) =
      ∑ i : S × Fin 4, factorialBranchCoeff b (i.1.val, i.2) *
        HTGeometry.mvExp (r * factorialHarmonicBranchFreq k (i.1.val, i.2)) v := by
  rw [Fintype.sum_prod_type]
  unfold factorialHarmonicLayer
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fin.sum_univ_four]
  simp [factorialBranchCoeff, factorialHarmonicBranchFreq, factorialBaseBranchFreq]
  have hN := mvExp_add_mvExp_neg (r * ((k : ℝ) * ((n : ℝ) + 1))) v
  have hL := mvExp_add_mvExp_neg (r * ((k : ℝ) * factorialShiftedFreq (n + 1))) v
  rw [show r * ((k : ℝ) * (-1 + -(n : ℝ))) = -(r * ((k : ℝ) * ((n : ℝ) + 1))) by ring]
  push_cast at hN hL ⊢
  ring_nf at hN hL ⊢
  linear_combination (b n / 2) * hN - (b n / 2) * hL

/-- The squared coefficient mass of the four-branch expansion is `∑_{n ∈ S} ‖b_n‖²`. -/
theorem sum_norm_sq_factorialBranchCoeff (S : Finset ℕ) (b : ℕ → ℂ) :
    ∑ i : S × Fin 4, ‖factorialBranchCoeff b (i.1.val, i.2)‖ ^ 2 = ∑ n ∈ S, ‖b n‖ ^ 2 := by
  rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fin.sum_univ_four]
  simp only [factorialBranchCoeff, Fin.val_zero, Fin.val_one, Fin.val_two,
    show ((3 : Fin 4) : ℕ) = 3 from rfl, Nat.zero_mod, Nat.mod_self,
    show (3 : ℕ) % 2 = 1 from rfl, if_true, one_ne_zero, if_false, norm_neg, norm_div,
    Complex.norm_ofNat]
  ring

/-- Dilation by `r ≥ 1` preserves the four-branch separation `k / 15`. -/
theorem factorialDilatedBranch_sep (k : ℕ) {r : ℝ} (hr : 1 ≤ r) (S : Finset ℕ) :
    ∀ i j : S × Fin 4, i ≠ j → (k : ℝ) / 15 ≤
      |r * factorialHarmonicBranchFreq k (i.1.val, i.2) -
        r * factorialHarmonicBranchFreq k (j.1.val, j.2)| := by
  intro i j hij
  have hne : (i.1.val, i.2) ≠ (j.1.val, j.2) := by
    intro h
    apply hij
    obtain ⟨⟨n, hn⟩, a⟩ := i
    obtain ⟨⟨m, hm⟩, c⟩ := j
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have hg := four_branch_harmonic_freq_gap_ge k hne
  rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < r)]
  exact hg.trans (le_mul_of_one_le_left (abs_nonneg _) hr)

/-- **Montgomery–Vaughan bounds for a dilated harmonic layer.** For `k ≥ 1`, `r ≥ 1`, and every
interval `[a, a + ℓ]`,
`(ℓ - K/k) ∑‖b_n‖² ≤ ∫_a^{a+ℓ} ‖H_k(r v)‖² dv ≤ (ℓ + K/k) ∑‖b_n‖²`, with `K = 390 / π`. -/
theorem factorialHarmonicLayer_interval_bounds (S : Finset ℕ) (b : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    {r : ℝ} (hr : 1 ≤ r) (a ℓ : ℝ) :
    (ℓ - factorialWindowGapConstant / k) * ∑ n ∈ S, ‖b n‖ ^ 2 ≤
        ∫ v in a..a + ℓ, ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2 ∧
      (∫ v in a..a + ℓ, ‖factorialHarmonicLayer S b k (r * v)‖ ^ 2) ≤
        (ℓ + factorialWindowGapConstant / k) * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  classical
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hD : (0 : ℝ) < k / 15 := by positivity
  have hsep := factorialDilatedBranch_sep k hr S
  have hlo := HTGeometry.interval_integral_normSq_expSum_ge
    (fun i : S × Fin 4 => r * factorialHarmonicBranchFreq k (i.1.val, i.2))
    (fun i => factorialBranchCoeff b (i.1.val, i.2)) (a := a) (ℓ := ℓ) hD hsep
  have hhi := HTGeometry.interval_integral_normSq_expSum_le
    (fun i : S × Fin 4 => r * factorialHarmonicBranchFreq k (i.1.val, i.2))
    (fun i => factorialBranchCoeff b (i.1.val, i.2)) (a := a) (ℓ := ℓ) hD hsep
  simp only [← factorialHarmonicLayer_eq_expSum, sum_norm_sq_factorialBranchCoeff,
    harmonic_layer_mv_penalty_eq] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem norm_factorialHarmonicLayer_le (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) (v : ℝ) :
    ‖factorialHarmonicLayer S b k v‖ ≤ 2 * ∑ n ∈ S, ‖b n‖ := by
  unfold factorialHarmonicLayer
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc : |Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v)) -
      Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v))| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one (2 * Real.pi * k *
      (factorialShiftedFreq (n + 1) * v)), Real.abs_cos_le_one (2 * Real.pi * k *
        (((n + 1 : ℕ) : ℝ) * v))])
  nlinarith [norm_nonneg (b n)]

theorem continuous_factorialHarmonicLayer (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) :
    Continuous (factorialHarmonicLayer S b k) := by
  unfold factorialHarmonicLayer
  fun_prop

/-- A phase combination is the uniformly convergent harmonic series, hence continuous. -/
theorem factorialPhaseCombination_eq_tsum (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    factorialPhaseCombination S b v = -((2 / Real.pi ^ 2 : ℝ) : ℂ) *
      ∑' k, (dyadicHarmonicWeight k : ℂ) * factorialHarmonicLayer S b k v := by
  rw [(factorialPhaseCombination_hasSum S b v).tsum_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem continuous_factorialPhaseCombination (S : Finset ℕ) (b : ℕ → ℂ) :
    Continuous (factorialPhaseCombination S b) := by
  have hc : Continuous fun v => ∑' k, (dyadicHarmonicWeight k : ℂ) *
      factorialHarmonicLayer S b k v := by
    refine continuous_tsum (fun k => continuous_const.mul
      (continuous_factorialHarmonicLayer S b k))
      (summable_abs_dyadicHarmonicWeight.mul_right (2 * ∑ n ∈ S, ‖b n‖)) fun k v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_factorialHarmonicLayer_le S b k v) (abs_nonneg _)
  have he : factorialPhaseCombination S b = fun v => -((2 / Real.pi ^ 2 : ℝ) : ℂ) *
      ∑' k, (dyadicHarmonicWeight k : ℂ) * factorialHarmonicLayer S b k v :=
    funext (factorialPhaseCombination_eq_tsum S b)
  rw [he]
  exact continuous_const.mul hc

/-- Pointwise bound `|Φ_N(v)| ≤ 2`. -/
theorem abs_factorialPhaseProfile_le (N : ℕ) (v : ℝ) : |factorialPhaseProfile N v| ≤ 2 := by
  have hP (u : ℝ) : -1 ≤ dyadicBernoulliFilter u ∧ dyadicBernoulliFilter u ≤ 1 := by
    obtain ⟨h1, h2⟩ := periodicClampedKernel_bounds u
    obtain ⟨h3, h4⟩ := periodicClampedKernel_bounds (2 * u)
    obtain ⟨h5, h6⟩ := periodicClampedKernel_bounds (4 * u)
    unfold dyadicBernoulliFilter
    constructor <;> linarith
  obtain ⟨a1, a2⟩ := hP (factorialShiftedFreq N * v)
  obtain ⟨c1, c2⟩ := hP ((N : ℝ) * v)
  unfold factorialPhaseProfile
  rw [abs_le]
  constructor <;> linarith

theorem norm_factorialPhaseCombination_le (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    ‖factorialPhaseCombination S b v‖ ≤ 2 * ∑ n ∈ S, ‖b n‖ := by
  unfold factorialPhaseCombination
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [norm_nonneg (b n), abs_factorialPhaseProfile_le (n + 1) v]

end

end GaloisForLFunctions.ArithmeticPositivityTheory
