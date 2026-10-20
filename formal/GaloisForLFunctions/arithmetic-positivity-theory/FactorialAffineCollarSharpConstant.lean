import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalAffineComparison
import GaloisForLFunctions.HTGeometry.FejerNearLattice

/-!
# Sharp constant of the affine collar comparison

The affine clock replaces the cubic collar frequency `λ_N` by `N + 1/12`. The error
`Φ_N - Ψ_N = P₀(λ_N v) - P₀((N+1/12)v)` has Bernoulli layers whose frequency intervals
`[2πkλ_N, 2πk(N+1/12)]` have length `2πk e_N` and stay separated for `k ≤ N`. The cosine-shell
Gram identity `∫ v⁻² L_k L_l = (π/2)|I_k ∩ I_l|` then makes the head exactly diagonal, the
harmonic tail is uniformly `O(1/N)`, and the collar cubic gives `N e_N → 1/144`. Hence

`N ∫_{v>1} v⁻² |Φ_N - Ψ_N|² → (4/π²)(1/144) Σ_k χ(k)²/k³ = 7ζ(3)/(256π²)`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The affine collar error `Φ_N - Ψ_N = P₀(λ_N v) - P₀((N + 1/12) v)`. -/
def factorialAffineCollarError (N : ℕ) (v : ℝ) : ℝ :=
  dyadicCenteredBernoulliFilter (factorialShiftedFreq N * v) -
    dyadicCenteredBernoulliFilter (((N : ℝ) + 1 / 12) * v)

/-- Harmonic layer `cos(2πkλ_N v) - cos(2πk(N + 1/12) v)` of the affine collar error. -/
def factorialAffineCollarLayer (N k : ℕ) (v : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * k * (factorialShiftedFreq N * v)) -
    Real.cos (2 * Real.pi * k * (((N : ℝ) + 1 / 12) * v))

/-- Bernoulli expansion `Σ_k w_k L_{N,k}(v) = -(π²/2)(Φ_N - Ψ_N)(v)`. -/
theorem factorialAffineCollarError_hasSum (N : ℕ) (v : ℝ) :
    HasSum (fun k : ℕ => dyadicHarmonicWeight k * factorialAffineCollarLayer N k v)
      (-(Real.pi ^ 2 / 2) * factorialAffineCollarError N v) := by
  have h := (dyadicCenteredBernoulliFilter_hasSum (factorialShiftedFreq N * v)).sub
    (dyadicCenteredBernoulliFilter_hasSum (((N : ℝ) + 1 / 12) * v))
  refine hasSum_of_eq_of_eq h (fun k => ?_) (by unfold factorialAffineCollarError; ring)
  unfold dyadicHarmonicWeight factorialAffineCollarLayer
  ring

/-- The dyadic filter is `9/2`-Lipschitz: each clamped kernel is `1/2`-Lipschitz. -/
theorem abs_dyadicCenteredBernoulliFilter_sub_le (x y : ℝ) :
    |dyadicCenteredBernoulliFilter x - dyadicCenteredBernoulliFilter y| ≤ (9 / 2) * |x - y| := by
  have hC (a b : ℝ) : |periodicClampedKernel a - periodicClampedKernel b| ≤ |a - b| / 2 := by
    unfold periodicClampedKernel
    rw [neg_sub_neg, abs_sub_comm]
    exact RHTower.DeletionMixedRefinement.bernoulliPeriodic_lipschitz_bound a b
  have h4 := hC (4 * x) (4 * y)
  have h2 := hC (2 * x) (2 * y)
  have h1 := hC x y
  rw [show 4 * x - 4 * y = 4 * (x - y) by ring, abs_mul] at h4
  rw [show 2 * x - 2 * y = 2 * (x - y) by ring, abs_mul] at h2
  norm_num at h4 h2
  unfold dyadicCenteredBernoulliFilter dyadicBernoulliFilter
  have e : periodicClampedKernel (4 * x) / 4 - 2 * periodicClampedKernel (2 * x) +
      4 * periodicClampedKernel x - 3 / 16 -
      (periodicClampedKernel (4 * y) / 4 - 2 * periodicClampedKernel (2 * y) +
        4 * periodicClampedKernel y - 3 / 16) =
      (periodicClampedKernel (4 * x) - periodicClampedKernel (4 * y)) / 4 -
        2 * (periodicClampedKernel (2 * x) - periodicClampedKernel (2 * y)) +
        4 * (periodicClampedKernel x - periodicClampedKernel y) := by ring
  rw [e]
  obtain ⟨a1, a2⟩ := abs_le.mp h4
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  obtain ⟨c1, c2⟩ := abs_le.mp h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Near the origin the collar error is at most `(9/2) e_N v`. -/
theorem abs_factorialAffineCollarError_le (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    |factorialAffineCollarError (n + 1) v| ≤ (9 / 2) * factorialAffineDefect (n + 1) * v := by
  have he := (factorialAffineDefect_bounds n).1
  have he0 : 0 ≤ factorialAffineDefect (n + 1) := le_trans (by positivity) he
  refine (abs_dyadicCenteredBernoulliFilter_sub_le _ _).trans (le_of_eq ?_)
  rw [show factorialShiftedFreq (n + 1) * v - (((n + 1 : ℕ) : ℝ) + 1 / 12) * v =
    -(factorialAffineDefect (n + 1) * v) by unfold factorialAffineDefect; ring,
    abs_neg, abs_of_nonneg (mul_nonneg he0 hv)]
  ring

/-- The cubic collar gives `N e_N = δ_N² + δ_N³/(3N)`. -/
theorem natCast_mul_factorialAffineDefect_eq {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * factorialAffineDefect N =
      factorialCollarShift N ^ 2 + factorialCollarShift N ^ 3 / (3 * (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc := four_mul_factorialShiftedFreq_cube hN
  rw [factorialShiftedFreq_eq_add_shift] at hc
  have hdef : factorialAffineDefect N = 1 / 12 - factorialCollarShift N := by
    unfold factorialAffineDefect; rw [factorialShiftedFreq_eq_add_shift]; ring
  rw [hdef]
  field_simp
  nlinarith [hc]

/-- The scaled affine defect tends to `1/144`. -/
theorem tendsto_natCast_mul_factorialAffineDefect :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * factorialAffineDefect (n + 1)) atTop
      (𝓝 (1 / 144)) := by
  have he : Tendsto (fun n : ℕ => factorialAffineDefect (n + 1)) atTop (𝓝 0) := by
    have hub : Tendsto (fun n : ℕ => 1 / (140 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 140 : ℝ)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    refine squeeze_zero (fun n => le_trans (by positivity) (factorialAffineDefect_bounds n).1)
      (fun n => (factorialAffineDefect_bounds n).2) hub
  have hδ : Tendsto (fun n : ℕ => factorialCollarShift (n + 1)) atTop (𝓝 (1 / 12)) := by
    have h := (tendsto_const_nhds (x := (1 / 12 : ℝ))).sub he
    simp only [sub_zero] at h
    refine h.congr fun n => ?_
    unfold factorialAffineDefect; rw [factorialShiftedFreq_eq_add_shift]; push_cast; ring
  have hinv : Tendsto (fun n : ℕ => 1 / (3 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 3 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    push_cast; field_simp
  have hlim := (hδ.pow 2).add ((hδ.pow 3).mul hinv)
  rw [show (1 / 12 : ℝ) ^ 2 + (1 / 12) ^ 3 * 0 = 1 / 144 by norm_num] at hlim
  refine hlim.congr fun n => ?_
  rw [natCast_mul_factorialAffineDefect_eq (by omega : 1 ≤ n + 1)]
  ring

/-! ### Cosine shells and their exact Gram matrix -/

private def collarShellDefect (a v : ℝ) : ℝ := (1 - Real.cos (a * v)) / v ^ 2

private theorem collarShellDefect_eq {a : ℝ} (ha : a ≠ 0) (v : ℝ) :
    collarShellDefect a v = a ^ 2 * oneSubCosKernel (a * v) := by
  unfold collarShellDefect oneSubCosKernel
  by_cases hv : v = 0
  · simp [hv]
  · field_simp

private theorem collarShellDefect_integrable (a : ℝ) : Integrable (collarShellDefect a) := by
  by_cases ha : a = 0
  · subst a
    change Integrable (fun v : ℝ => (1 - Real.cos (0 * v)) / v ^ 2)
    simp
  · exact ((integrable_oneSubCosKernel.comp_mul_left' ha).const_mul (a ^ 2)).congr
      (Eventually.of_forall fun v => (collarShellDefect_eq ha v).symm)

private theorem collarShellDefect_integral (a : ℝ) :
    (∫ v, collarShellDefect a v) = Real.pi * |a| := by
  by_cases ha : a = 0
  · simp [ha, collarShellDefect]
  · simp_rw [collarShellDefect_eq ha]
    rw [integral_const_mul, Measure.integral_comp_mul_left, integral_oneSubCosKernel,
      smul_eq_mul, abs_inv]
    have h : a ^ 2 * |a|⁻¹ = |a| := by
      rw [← sq_abs, pow_two, mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), mul_one]
    calc a ^ 2 * (|a|⁻¹ * Real.pi) = (a ^ 2 * |a|⁻¹) * Real.pi := by ring
      _ = Real.pi * |a| := by rw [h]; ring

/-- The cosine shell `(cos(av) - cos(bv))/v`, the Fourier image of a frequency interval. -/
private def collarShell (a b v : ℝ) : ℝ := (Real.cos (a * v) - Real.cos (b * v)) / v

private theorem collarShell_mul (a b c d v : ℝ) :
    collarShell a b v * collarShell c d v =
      (-(collarShellDefect (a - c) v) - collarShellDefect (a + c) v +
        collarShellDefect (a - d) v + collarShellDefect (a + d) v +
        collarShellDefect (b - c) v + collarShellDefect (b + c) v -
        collarShellDefect (b - d) v - collarShellDefect (b + d) v) / 2 := by
  unfold collarShell collarShellDefect
  by_cases hv : v = 0
  · simp [hv]
  · simp only [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    field_simp
    ring

private theorem collarShell_mul_integrable (a b c d : ℝ) :
    Integrable fun v => collarShell a b v * collarShell c d v := by
  have h := (((((((collarShellDefect_integrable (a - c)).neg.sub
    (collarShellDefect_integrable (a + c))).add
    (collarShellDefect_integrable (a - d))).add
    (collarShellDefect_integrable (a + d))).add
    (collarShellDefect_integrable (b - c))).add
    (collarShellDefect_integrable (b + c))).sub
    (collarShellDefect_integrable (b - d))).sub
    (collarShellDefect_integrable (b + d))
  exact (h.div_const 2).congr (Eventually.of_forall fun v => (collarShell_mul a b c d v).symm)

private theorem collarShell_mul_integral {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (∫ v, collarShell a b v * collarShell c d v) =
      Real.pi / 2 * (|a - d| + |b - c| - |a - c| - |b - d|) := by
  simp_rw [collarShell_mul]
  rw [integral_div, integral_sub, integral_sub, integral_add, integral_add, integral_add,
    integral_add, integral_sub, integral_neg]
  · simp only [collarShellDefect_integral]
    rw [abs_of_nonneg (add_nonneg ha hc), abs_of_nonneg (add_nonneg ha hd),
      abs_of_nonneg (add_nonneg hb hc), abs_of_nonneg (add_nonneg hb hd)]
    ring
  all_goals apply_rules [Integrable.add, Integrable.sub, Integrable.neg,
    collarShellDefect_integrable]

/-- Exact Gram law for separated frequency intervals: distinct shells are orthogonal and each
shell has energy `π (b - a)`. -/
private theorem collarShell_sum_sq (K : ℕ) (a b c : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i ≤ b i) (hsep : ∀ i j, i < j → j < K → b i ≤ a j) :
    Integrable (fun v => (∑ i ∈ Finset.range K, c i * collarShell (a i) (b i) v) ^ 2) ∧
    (∫ v, (∑ i ∈ Finset.range K, c i * collarShell (a i) (b i) v) ^ 2) =
      Real.pi * ∑ i ∈ Finset.range K, (b i - a i) * c i ^ 2 := by
  have hexp (v : ℝ) : (∑ i ∈ Finset.range K, c i * collarShell (a i) (b i) v) ^ 2 =
      ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
        c i * c j * (collarShell (a i) (b i) v * collarShell (a j) (b j) v) := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint (i j : ℕ) : Integrable fun v =>
      c i * c j * (collarShell (a i) (b i) v * collarShell (a j) (b j) v) :=
    (collarShell_mul_integrable _ _ _ _).const_mul _
  have hgram (i j : ℕ) (hi : i < K) (hj : j < K) :
      (∫ v, c i * c j * (collarShell (a i) (b i) v * collarShell (a j) (b j) v)) =
        if i = j then Real.pi * (b i - a i) * c i ^ 2 else 0 := by
    rw [integral_const_mul, collarShell_mul_integral (ha i) ((ha i).trans (hab i)) (ha j)
      ((ha j).trans (hab j))]
    split_ifs with h
    · subst h
      rw [sub_self, sub_self, abs_zero, abs_of_nonpos (sub_nonpos.mpr (hab i)),
        abs_of_nonneg (sub_nonneg.mpr (hab i))]
      ring
    · rcases lt_or_gt_of_ne h with hl | hl
      · have h1 := hsep i j hl hj
        rw [abs_of_nonpos (by linarith [hab i, hab j] : a i - b j ≤ 0),
          abs_of_nonpos (by linarith : b i - a j ≤ 0),
          abs_of_nonpos (by linarith [hab i] : a i - a j ≤ 0),
          abs_of_nonpos (by linarith [hab j] : b i - b j ≤ 0)]
        ring
      · have h1 := hsep j i hl hi
        rw [abs_of_nonneg (by linarith [hab i] : 0 ≤ a i - b j),
          abs_of_nonneg (by linarith [hab i, hab j] : 0 ≤ b i - a j),
          abs_of_nonneg (by linarith [hab j] : 0 ≤ a i - a j),
          abs_of_nonneg (by linarith [hab i] : 0 ≤ b i - b j)]
        ring
  refine ⟨(integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j).congr
    (Eventually.of_forall fun v => (hexp v).symm), ?_⟩
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ fun j _ => hint i j]
  rw [Finset.sum_congr rfl fun j hj => hgram i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
  rw [Finset.sum_ite_eq, if_pos hi]
  ring

/-- Harmonic head `Σ_{k<K} w_k L_{N,k}(v)` of the affine collar error. -/
def factorialAffineCollarHead (N K : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, dyadicHarmonicWeight k * factorialAffineCollarLayer N k v

/-- **Exact head energy.** For `K ≤ N + 1` the frequency intervals `[2πkλ_N, 2πk(N+1/12)]` are
separated, the shells are orthogonal, and `∫_{v>0} v⁻² A_K² = π² e_N Σ_{k<K} k w_k²`. -/
theorem factorialAffineCollarHead_energy (n : ℕ) {K : ℕ} (hK : K ≤ n + 2) :
    IntegrableOn (fun v => factorialAffineCollarHead (n + 1) K v ^ 2 / v ^ 2) (Ioi 0) ∧
    (∫ v in Ioi (0 : ℝ), factorialAffineCollarHead (n + 1) K v ^ 2 / v ^ 2) =
      Real.pi ^ 2 * factorialAffineDefect (n + 1) *
        ∑ k ∈ Finset.range K, (k : ℝ) * dyadicHarmonicWeight k ^ 2 := by
  set N := n + 1 with hNdef
  set lam := factorialShiftedFreq N
  set e := factorialAffineDefect N with hedef
  have hlam : lam = (N : ℝ) + 1 / 12 - e := by rw [hedef]; unfold factorialAffineDefect; ring
  have he0 : 0 ≤ e := le_trans (by positivity) (factorialAffineDefect_bounds n).1
  have he1 : e ≤ 1 / (140 * ((n : ℝ) + 1)) := (factorialAffineDefect_bounds n).2
  have hlam0 : 0 ≤ lam := (factorialShiftedFreq_pos (by omega : 1 ≤ N)).le
  let a : ℕ → ℝ := fun k => 2 * Real.pi * k * lam
  let b : ℕ → ℝ := fun k => 2 * Real.pi * k * ((N : ℝ) + 1 / 12)
  have ha (i : ℕ) : 0 ≤ a i := by positivity
  have hab (i : ℕ) : a i ≤ b i := by
    simp only [a, b]; apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have hsep (i j : ℕ) (hij : i < j) (hj : j < K) : b i ≤ a j := by
    simp only [a, b]
    have hjR : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have hjN : (j : ℝ) ≤ n + 1 := by exact_mod_cast (show j ≤ n + 1 by omega)
    have hNR : (N : ℝ) = n + 1 := by rw [hNdef]; push_cast; ring
    have hie : ((i : ℝ) + 1) * e ≤ 1 := by
      have : ((i : ℝ) + 1) * e ≤ (n + 1) * (1 / (140 * ((n : ℝ) + 1))) :=
        mul_le_mul (by linarith) he1 he0 (by positivity)
      have h2 : ((n : ℝ) + 1) * (1 / (140 * ((n : ℝ) + 1))) = 1 / 140 := by field_simp
      linarith
    have key : (i : ℝ) * ((N : ℝ) + 1 / 12) ≤ j * lam := by
      rw [hlam]
      have h1 : (i : ℝ) * ((N : ℝ) + 1 / 12) ≤ ((i : ℝ) + 1) * ((N : ℝ) + 1 / 12 - e) := by
        rw [hNR]; nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_right hjR (by rw [hNR]; nlinarith))
    have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith [this]
  have hG := collarShell_sum_sq K a b dyadicHarmonicWeight ha hab hsep
  have hfun (v : ℝ) : factorialAffineCollarHead N K v ^ 2 / v ^ 2 =
      (∑ i ∈ Finset.range K, dyadicHarmonicWeight i * collarShell (a i) (b i) v) ^ 2 := by
    rw [← div_pow]; congr 1
    unfold factorialAffineCollarHead
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [a, b, lam, collarShell, factorialAffineCollarLayer]
    ring_nf
  have hint : Integrable fun v => factorialAffineCollarHead N K v ^ 2 / v ^ 2 :=
    hG.1.congr (Eventually.of_forall fun v => (hfun v).symm)
  have hwhole : (∫ v, factorialAffineCollarHead N K v ^ 2 / v ^ 2) =
      2 * (Real.pi ^ 2 * e * ∑ k ∈ Finset.range K, (k : ℝ) * dyadicHarmonicWeight k ^ 2) := by
    simp_rw [hfun]
    rw [hG.2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [a, b]
    rw [hlam]; ring
  have heven (v : ℝ) : factorialAffineCollarHead N K (-v) ^ 2 / (-v) ^ 2 =
      factorialAffineCollarHead N K v ^ 2 / v ^ 2 := by
    unfold factorialAffineCollarHead factorialAffineCollarLayer
    simp only [mul_neg, Real.cos_neg, neg_sq]
  have hn : (∫ v in Iic (0 : ℝ), factorialAffineCollarHead N K v ^ 2 / v ^ 2) =
      ∫ v in Ioi (0 : ℝ), factorialAffineCollarHead N K v ^ 2 / v ^ 2 := by
    have h := integral_comp_neg_Iic (0 : ℝ)
      (fun v => factorialAffineCollarHead N K v ^ 2 / v ^ 2)
    rw [neg_zero] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Iic (fun v _ => (heven v).symm)
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hint.integrableOn hint.integrableOn
  rw [hn, hwhole] at hsplit
  exact ⟨hint.integrableOn, by linarith⟩

/-- Each layer is at most `2πk e_N v` near the origin. -/
theorem abs_factorialAffineCollarLayer_le (n k : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    |factorialAffineCollarLayer (n + 1) k v| ≤
      2 * Real.pi * k * factorialAffineDefect (n + 1) * v := by
  have he0 : 0 ≤ factorialAffineDefect (n + 1) :=
    le_trans (by positivity) (factorialAffineDefect_bounds n).1
  refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
  rw [show 2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v) -
      2 * Real.pi * k * ((((n + 1 : ℕ) : ℝ) + 1 / 12) * v) =
      -(2 * Real.pi * k * factorialAffineDefect (n + 1) * v) by
    unfold factorialAffineDefect; ring, abs_neg, abs_of_nonneg (by positivity)]

theorem abs_factorialAffineCollarLayer_le_two (N k : ℕ) (v : ℝ) :
    |factorialAffineCollarLayer N k v| ≤ 2 := by
  unfold factorialAffineCollarLayer
  have h1 := Real.abs_cos_le_one (2 * Real.pi * k * (factorialShiftedFreq N * v))
  have h2 := Real.abs_cos_le_one (2 * Real.pi * k * (((N : ℝ) + 1 / 12) * v))
  calc _ ≤ |Real.cos (2 * Real.pi * k * (factorialShiftedFreq N * v))| +
        |Real.cos (2 * Real.pi * k * (((N : ℝ) + 1 / 12) * v))| := abs_sub _ _
    _ ≤ 2 := by linarith

/-- The head grows at most like `2π e_N (1 + log N) v`, through the harmonic number. -/
theorem abs_factorialAffineCollarHead_le (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    |factorialAffineCollarHead (n + 1) (n + 2) v| ≤
      2 * Real.pi * factorialAffineDefect (n + 1) * (1 + Real.log ((n + 1 : ℕ) : ℝ)) * v := by
  have he0 : 0 ≤ factorialAffineDefect (n + 1) :=
    le_trans (by positivity) (factorialAffineDefect_bounds n).1
  have hterm (k : ℕ) : |dyadicHarmonicWeight k * factorialAffineCollarLayer (n + 1) k v| ≤
      2 * Real.pi * factorialAffineDefect (n + 1) * v * (1 / (k : ℝ)) := by
    rw [abs_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [dyadicHarmonicWeight]
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hw := abs_dyadicHarmonicWeight_le k
      have hl := abs_factorialAffineCollarLayer_le n k hv
      calc |dyadicHarmonicWeight k| * |factorialAffineCollarLayer (n + 1) k v| ≤
          (1 / (k : ℝ) ^ 2) * (2 * Real.pi * k * factorialAffineDefect (n + 1) * v) :=
            mul_le_mul hw hl (abs_nonneg _) (by positivity)
        _ = _ := by field_simp
  have hharm : (∑ k ∈ Finset.range (n + 2), (1 / (k : ℝ))) ≤ 1 + Real.log ((n + 1 : ℕ) : ℝ) := by
    have h := harmonic_le_one_add_log (n + 1)
    have e : (harmonic (n + 1) : ℝ) = ∑ k ∈ Finset.range (n + 2), (1 / (k : ℝ)) := by
      rw [Finset.sum_range_succ']
      simp [harmonic]
    rw [e] at h
    exact h
  unfold factorialAffineCollarHead
  calc _ ≤ ∑ k ∈ Finset.range (n + 2),
        |dyadicHarmonicWeight k * factorialAffineCollarLayer (n + 1) k v| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 2), 2 * Real.pi * factorialAffineDefect (n + 1) * v *
        (1 / (k : ℝ)) := Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * Real.pi * factorialAffineDefect (n + 1) * v *
        ∑ k ∈ Finset.range (n + 2), (1 / (k : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      rw [show 2 * Real.pi * factorialAffineDefect (n + 1) * (1 + Real.log ((n + 1 : ℕ) : ℝ)) * v =
        2 * Real.pi * factorialAffineDefect (n + 1) * v * (1 + Real.log ((n + 1 : ℕ) : ℝ)) by ring]
      exact mul_le_mul_of_nonneg_left hharm (by positivity)

/-- Harmonic tail of the affine collar error, `-(π²/2)(Φ_N - Ψ_N) - A_K`. -/
def factorialAffineCollarTail (N K : ℕ) (v : ℝ) : ℝ :=
  -(Real.pi ^ 2 / 2) * factorialAffineCollarError N v - factorialAffineCollarHead N K v

/-- The tail is the remaining harmonic series. -/
theorem factorialAffineCollarTail_eq_tsum (N K : ℕ) (v : ℝ) :
    factorialAffineCollarTail N K v =
      ∑' k : ℕ, dyadicHarmonicWeight (k + K) * factorialAffineCollarLayer N (k + K) v := by
  have h := factorialAffineCollarError_hasSum N v
  rw [factorialAffineCollarTail, ← h.tsum_eq, ← h.summable.sum_add_tsum_nat_add K]
  unfold factorialAffineCollarHead
  ring

/-- The harmonic tail beyond `K` is uniformly at most `4/K`. -/
theorem abs_factorialAffineCollarTail_le (N : ℕ) {K : ℕ} (hK : 1 ≤ K) (v : ℝ) :
    |factorialAffineCollarTail N K v| ≤ 4 / (K : ℝ) := by
  rw [factorialAffineCollarTail_eq_tsum]
  have hb (k : ℕ) : ‖dyadicHarmonicWeight (k + K) * factorialAffineCollarLayer N (k + K) v‖ ≤
      2 * (1 / ((k + K : ℕ) : ℝ) ^ 2) := by
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul (abs_factorialAffineCollarLayer_le_two _ _ _)
      (by simpa using abs_dyadicHarmonicWeight_le (k + K)) (abs_nonneg _) (by norm_num)
  have hs : Summable fun k : ℕ => 1 / ((k + K : ℕ) : ℝ) ^ 2 := by
    have := (summable_nat_add_iff K).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact this.congr fun k => by push_cast; ring_nf
  have htail : ∑' k : ℕ, 1 / ((k + K : ℕ) : ℝ) ^ 2 ≤ 2 / (K : ℝ) := by
    have h := GaloisForLFunctions.HTGeometry.tsum_ite_inv_sq_le (K - 1)
    have hsi : Summable fun n : ℕ => (if K - 1 ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0) := by
      refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
        ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two))
      split_ifs
      · push_cast; exact le_rfl
      · positivity
    rw [← hsi.sum_add_tsum_nat_add (K - 1)] at h
    have h0 : ∑ i ∈ Finset.range (K - 1), (if K - 1 ≤ i then 1 / ((i : ℝ) + 1) ^ 2 else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
    rw [h0, zero_add] at h
    have hK1 : ((K - 1 : ℕ) : ℝ) + 1 = K := by
      rw [Nat.cast_sub hK]; push_cast; ring
    rw [hK1] at h
    refine le_trans (le_of_eq (tsum_congr fun k => ?_)) h
    rw [if_pos (by omega)]
    congr 2
    push_cast [Nat.cast_sub hK]
    ring
  calc ‖∑' k : ℕ, dyadicHarmonicWeight (k + K) * factorialAffineCollarLayer N (k + K) v‖ ≤
      ∑' k : ℕ, 2 * (1 / ((k + K : ℕ) : ℝ) ^ 2) :=
        tsum_of_norm_bounded ((hs.mul_left 2).hasSum) hb
    _ = 2 * ∑' k : ℕ, 1 / ((k + K : ℕ) : ℝ) ^ 2 := tsum_mul_left
    _ ≤ 2 * (2 / (K : ℝ)) := mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 4 / (K : ℝ) := by ring

private theorem continuous_dyadicCenteredFilter : Continuous dyadicCenteredBernoulliFilter := by
  have h : LipschitzWith (Real.toNNReal (9 / 2)) dyadicCenteredBernoulliFilter :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by norm_num)]
      exact abs_dyadicCenteredBernoulliFilter_sub_le x y
  exact h.continuous

theorem continuous_factorialAffineCollarError (N : ℕ) : Continuous (factorialAffineCollarError N) := by
  unfold factorialAffineCollarError
  have := continuous_dyadicCenteredFilter
  fun_prop

theorem continuous_factorialAffineCollarHead (N K : ℕ) : Continuous (factorialAffineCollarHead N K) := by
  unfold factorialAffineCollarHead factorialAffineCollarLayer
  fun_prop

private theorem integrableOn_inv_sq_Ioi_one : IntegrableOn (fun v : ℝ => 1 / v ^ 2) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).congr_fun
    (fun v hv => ?_) measurableSet_Ioi
  have hv0 : 0 ≤ v := le_trans zero_le_one (le_of_lt hv)
  show v ^ (-2 : ℝ) = 1 / v ^ 2
  rw [Real.rpow_neg hv0, Real.rpow_two, one_div]

private theorem integral_inv_sq_Ioi_one : ∫ v in Ioi (1 : ℝ), 1 / v ^ 2 = 1 := by
  calc ∫ v in Ioi (1 : ℝ), 1 / v ^ 2 = ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioi fun v hv => by
          have hv0 : 0 ≤ v := le_trans zero_le_one (le_of_lt hv)
          show 1 / v ^ 2 = v ^ (-2 : ℝ)
          rw [Real.rpow_neg hv0, Real.rpow_two, one_div]
    _ = 1 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
      norm_num

/-- On `v > 1` the full error differs from its harmonic head by at most the uniform tail:
`|∫(A+B)² - ∫A²| ≤ ε∫A² + (1 + 1/ε)(4/K)²` against `v⁻²`. -/
theorem factorialAffineCollar_head_comparison (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    |(∫ v in Ioi (1 : ℝ), (-(Real.pi ^ 2 / 2) * factorialAffineCollarError (n + 1) v) ^ 2 / v ^ 2) -
      ∫ v in Ioi (1 : ℝ), factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2| ≤
      ε * (∫ v in Ioi (1 : ℝ), factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2) +
        (1 + 1 / ε) * (4 / ((n + 2 : ℕ) : ℝ)) ^ 2 := by
  set A := factorialAffineCollarHead (n + 1) (n + 2)
  set B := factorialAffineCollarTail (n + 1) (n + 2)
  set F := fun v => -(Real.pi ^ 2 / 2) * factorialAffineCollarError (n + 1) v
  have hF (v : ℝ) : F v = A v + B v := by
    simp only [F, A, B, factorialAffineCollarTail]; ring
  have hB (v : ℝ) : |B v| ≤ 4 / ((n + 2 : ℕ) : ℝ) :=
    abs_factorialAffineCollarTail_le (n + 1) (by omega) v
  set c := 4 / ((n + 2 : ℕ) : ℝ)
  have hAc : Continuous A := continuous_factorialAffineCollarHead _ _
  have hBc : Continuous B := by
    have h1 := continuous_factorialAffineCollarError (n + 1)
    have h2 := continuous_factorialAffineCollarHead (n + 1) (n + 2)
    show Continuous fun v => factorialAffineCollarTail (n + 1) (n + 2) v
    unfold factorialAffineCollarTail; fun_prop
  have hAi : IntegrableOn (fun v => A v ^ 2 / v ^ 2) (Ioi 1) :=
    (factorialAffineCollarHead_energy n le_rfl).1.mono_set (Ioi_subset_Ioi zero_le_one)
  have hBb (v : ℝ) : B v ^ 2 / v ^ 2 ≤ c ^ 2 * (1 / v ^ 2) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB v) 2)
      (sq_nonneg _)
  have hBi : IntegrableOn (fun v => B v ^ 2 / v ^ 2) (Ioi 1) := by
    refine (integrableOn_inv_sq_Ioi_one.const_mul (c ^ 2)).mono' ?_ ?_
    · have hBm : Measurable B := hBc.measurable
      exact (by fun_prop : Measurable fun v => B v ^ 2 / v ^ 2).aestronglyMeasurable
    · exact Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hBb v
  have hFi : IntegrableOn (fun v => F v ^ 2 / v ^ 2) (Ioi 1) := by
    refine ((hAi.const_mul 2).add (hBi.const_mul 2)).mono' ?_ ?_
    · have hFm : Measurable F := by
        have := continuous_factorialAffineCollarError (n + 1)
        exact (by fun_prop : Continuous F).measurable
      exact (by fun_prop : Measurable fun v => F v ^ 2 / v ^ 2).aestronglyMeasurable
    · exact Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)), hF]
        show (A v + B v) ^ 2 / v ^ 2 ≤ 2 * (A v ^ 2 / v ^ 2) + 2 * (B v ^ 2 / v ^ 2)
        rw [mul_div_assoc', mul_div_assoc', ← add_div]
        exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (A v - B v)]) (sq_nonneg _)
  have hpt (v : ℝ) : |F v ^ 2 / v ^ 2 - A v ^ 2 / v ^ 2| ≤
      ε * (A v ^ 2 / v ^ 2) + (1 + 1 / ε) * (B v ^ 2 / v ^ 2) := by
    have hamgm : 2 * |A v| * |B v| ≤ ε * A v ^ 2 + B v ^ 2 / ε := by
      have hq : 0 ≤ (ε * |A v| - |B v|) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
      have he : (ε * |A v| - |B v|) ^ 2 / ε = ε * A v ^ 2 + B v ^ 2 / ε - 2 * |A v| * |B v| := by
        rw [← sq_abs (A v), ← sq_abs (B v)]
        field_simp
        ring
      linarith
    have hnum : |F v ^ 2 - A v ^ 2| ≤ ε * A v ^ 2 + (1 + 1 / ε) * B v ^ 2 := by
      rw [hF, show (A v + B v) ^ 2 - A v ^ 2 = 2 * A v * B v + B v ^ 2 by ring]
      calc |2 * A v * B v + B v ^ 2| ≤ |2 * A v * B v| + |B v ^ 2| := abs_add_le _ _
        _ = 2 * |A v| * |B v| + B v ^ 2 := by
          rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg (B v))]
        _ ≤ _ := by
          have h1 : B v ^ 2 / ε = 1 / ε * B v ^ 2 := by ring
          linarith [hamgm]
    rw [← sub_div, abs_div, abs_of_nonneg (sq_nonneg v), mul_div_assoc', mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
  have hBint : (∫ v in Ioi (1 : ℝ), B v ^ 2 / v ^ 2) ≤ c ^ 2 := by
    calc (∫ v in Ioi (1 : ℝ), B v ^ 2 / v ^ 2) ≤ ∫ v in Ioi (1 : ℝ), c ^ 2 * (1 / v ^ 2) :=
          setIntegral_mono_on hBi (integrableOn_inv_sq_Ioi_one.const_mul _) measurableSet_Ioi
            fun v _ => hBb v
      _ = c ^ 2 := by rw [integral_const_mul, integral_inv_sq_Ioi_one, mul_one]
  have h1 : IntegrableOn (fun v => |F v ^ 2 / v ^ 2 - A v ^ 2 / v ^ 2|) (Ioi 1) :=
    (hFi.sub hAi).abs
  have h2 : IntegrableOn (fun v => ε * (A v ^ 2 / v ^ 2) + (1 + 1 / ε) * (B v ^ 2 / v ^ 2))
      (Ioi 1) := (hAi.const_mul ε).add (hBi.const_mul (1 + 1 / ε))
  rw [← integral_sub hFi hAi]
  calc |∫ v in Ioi (1 : ℝ), (F v ^ 2 / v ^ 2 - A v ^ 2 / v ^ 2)| ≤
      ∫ v in Ioi (1 : ℝ), |F v ^ 2 / v ^ 2 - A v ^ 2 / v ^ 2| := abs_integral_le_integral_abs
    _ ≤ ∫ v in Ioi (1 : ℝ), (ε * (A v ^ 2 / v ^ 2) + (1 + 1 / ε) * (B v ^ 2 / v ^ 2)) :=
        setIntegral_mono_on h1 h2 measurableSet_Ioi fun v _ => hpt v
    _ = ε * (∫ v in Ioi (1 : ℝ), A v ^ 2 / v ^ 2) + (1 + 1 / ε) * ∫ v in Ioi (1 : ℝ), B v ^ 2 / v ^ 2 := by
        rw [integral_add (hAi.const_mul _) (hBi.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ _ := by gcongr

/-- The diagonal constant `Σ k w_k² = Σ χ(k)²/k³` converges. -/
theorem summable_natCast_mul_dyadicHarmonicWeight_sq :
    Summable fun k : ℕ => (k : ℝ) * dyadicHarmonicWeight k ^ 2 := by
  refine (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)).of_norm_bounded fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hw := abs_dyadicHarmonicWeight_le k
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hkR, abs_pow]
    calc (k : ℝ) * |dyadicHarmonicWeight k| ^ 2 ≤ (k : ℝ) * (1 / (k : ℝ) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hw 2) hkR.le
      _ = 1 / (k : ℝ) ^ 3 := by field_simp

private theorem integral_head_Ioi_one (n : ℕ) :
    (∫ v in Ioi (1 : ℝ), factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2) =
      Real.pi ^ 2 * factorialAffineDefect (n + 1) *
        (∑ k ∈ Finset.range (n + 2), (k : ℝ) * dyadicHarmonicWeight k ^ 2) -
        ∫ v in Ioc (0 : ℝ) 1, factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2 := by
  obtain ⟨hi, he⟩ := factorialAffineCollarHead_energy n (le_refl (n + 2))
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
    measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one, he] at hsplit
  linarith

private theorem integral_head_Ioc_le (n : ℕ) :
    (∫ v in Ioc (0 : ℝ) 1, factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2) ≤
      (2 * Real.pi * factorialAffineDefect (n + 1) * (1 + Real.log ((n + 1 : ℕ) : ℝ))) ^ 2 := by
  set c := 2 * Real.pi * factorialAffineDefect (n + 1) * (1 + Real.log ((n + 1 : ℕ) : ℝ))
  have hpt : ∀ v ∈ Ioc (0 : ℝ) 1,
      factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2 ≤ c ^ 2 := by
    intro v hv
    have h := abs_factorialAffineCollarHead_le n hv.1.le
    rw [div_le_iff₀ (pow_pos hv.1 2), ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc (∫ v in Ioc (0 : ℝ) 1, factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2) ≤
      ∫ v in Ioc (0 : ℝ) 1, c ^ 2 :=
        setIntegral_mono_on ((factorialAffineCollarHead_energy n (le_refl (n + 2))).1.mono_set
          Ioc_subset_Ioi_self) (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc hpt
    _ = c ^ 2 := by simp

private theorem tendsto_one_add_log_sq_div :
    Tendsto (fun n : ℕ => (1 + Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero).comp hN
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN
  have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hN
  have h := (h0.add (h1.const_mul 2)).add h2
  simp only [mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, one_mul, pow_zero, pow_one]
  ring

/-- The scaled collar energy converges to `(Σ_k k w_k²)/(36π²)`. -/
theorem tendsto_factorialAffineCollarError_energy :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      ∫ v in Ioi (1 : ℝ), factorialAffineCollarError (n + 1) v ^ 2 / v ^ 2) atTop
      (𝓝 ((∑' k : ℕ, (k : ℝ) * dyadicHarmonicWeight k ^ 2) / (36 * Real.pi ^ 2))) := by
  set S := ∑' k : ℕ, (k : ℝ) * dyadicHarmonicWeight k ^ 2
  set N : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) with hNdef
  have hN0 (n : ℕ) : 0 < N n := by simp only [N]; positivity
  have hNtop : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  set Y : ℕ → ℝ := fun n => N n *
    ∫ v in Ioi (1 : ℝ), factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2 with hYdef
  -- the head converges to the diagonal constant
  have hpart : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 2),
      (k : ℝ) * dyadicHarmonicWeight k ^ 2) atTop (𝓝 S) :=
    summable_natCast_mul_dyadicHarmonicWeight_sq.hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 2)
  have hH : Tendsto (fun n : ℕ => N n * (Real.pi ^ 2 * factorialAffineDefect (n + 1) *
      ∑ k ∈ Finset.range (n + 2), (k : ℝ) * dyadicHarmonicWeight k ^ 2)) atTop
      (𝓝 (Real.pi ^ 2 * (1 / 144) * S)) := by
    have := ((tendsto_const_nhds (x := Real.pi ^ 2)).mul
      tendsto_natCast_mul_factorialAffineDefect).mul hpart
    refine this.congr fun n => ?_
    simp only [N]; ring
  have hL : Tendsto (fun n : ℕ => N n *
      ∫ v in Ioc (0 : ℝ) 1, factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2) atTop (𝓝 0) := by
    have hub : Tendsto (fun n : ℕ => (4 * Real.pi ^ 2 / 19600) *
        ((1 + Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      simpa using tendsto_one_add_log_sq_div.const_mul (4 * Real.pi ^ 2 / 19600)
    refine squeeze_zero (fun n => mul_nonneg (hN0 n).le (setIntegral_nonneg measurableSet_Ioc
      fun v _ => div_nonneg (sq_nonneg _) (sq_nonneg _))) (fun n => ?_) hub
    have hb := integral_head_Ioc_le n
    have he := factorialAffineDefect_bounds n
    have he0 : 0 ≤ factorialAffineDefect (n + 1) := le_trans (by positivity) he.1
    have hlog : 0 ≤ 1 + Real.log ((n + 1 : ℕ) : ℝ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos n)
      linarith
    have hNR : N n = (n : ℝ) + 1 := by simp only [N]; push_cast; ring
    calc N n * ∫ v in Ioc (0 : ℝ) 1, factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2 ≤
        N n * (2 * Real.pi * factorialAffineDefect (n + 1) *
          (1 + Real.log ((n + 1 : ℕ) : ℝ))) ^ 2 := mul_le_mul_of_nonneg_left hb (hN0 n).le
      _ ≤ N n * (2 * Real.pi * (1 / (140 * ((n : ℝ) + 1))) *
          (1 + Real.log ((n + 1 : ℕ) : ℝ))) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (hN0 n).le
          apply pow_le_pow_left₀ (by positivity)
          gcongr
          exact he.2
      _ = _ := by rw [hNR]; push_cast; field_simp; ring
  have hY : Tendsto Y atTop (𝓝 (Real.pi ^ 2 * (1 / 144) * S)) := by
    have := hH.sub hL
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    simp only [Y]
    rw [integral_head_Ioi_one]; ring
  -- the full error stays within the head up to a vanishing tail
  set Z : ℕ → ℝ := fun n => N n * ∫ v in Ioi (1 : ℝ),
    (-(Real.pi ^ 2 / 2) * factorialAffineCollarError (n + 1) v) ^ 2 / v ^ 2 with hZdef
  have hdiff (n : ℕ) : |Z n - Y n| ≤ Y n * (Real.sqrt (N n))⁻¹ + 16 / N n +
      16 * (Real.sqrt (N n))⁻¹ := by
    have hs : 0 < Real.sqrt (N n) := Real.sqrt_pos.mpr (hN0 n)
    have hsq : Real.sqrt (N n) ^ 2 = N n := Real.sq_sqrt (hN0 n).le
    have hc := factorialAffineCollar_head_comparison n (inv_pos.mpr hs)
    have hK : N n ≤ ((n + 2 : ℕ) : ℝ) := by simp only [N]; push_cast; linarith
    have htail : N n * ((1 + 1 / (Real.sqrt (N n))⁻¹) * (4 / ((n + 2 : ℕ) : ℝ)) ^ 2) ≤
        16 / N n + 16 * (Real.sqrt (N n))⁻¹ := by
      have h42 : (4 / ((n + 2 : ℕ) : ℝ)) ^ 2 ≤ 16 / N n ^ 2 := by
        rw [div_pow, show (4 : ℝ) ^ 2 = 16 by norm_num]
        exact div_le_div_of_nonneg_left (by norm_num) (pow_pos (hN0 n) 2)
          (pow_le_pow_left₀ (hN0 n).le hK 2)
      calc N n * ((1 + 1 / (Real.sqrt (N n))⁻¹) * (4 / ((n + 2 : ℕ) : ℝ)) ^ 2) ≤
          N n * ((1 + Real.sqrt (N n)) * (16 / N n ^ 2)) := by
            rw [one_div, inv_inv]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h42 (by positivity))
              (hN0 n).le
        _ = (Real.sqrt (N n)) ^ 2 * ((1 + Real.sqrt (N n)) * (16 / ((Real.sqrt (N n)) ^ 2) ^ 2)) := by
            rw [hsq]
        _ = 16 / (Real.sqrt (N n)) ^ 2 + 16 * (Real.sqrt (N n))⁻¹ := by
            field_simp
        _ = 16 / N n + 16 * (Real.sqrt (N n))⁻¹ := by rw [hsq]
    have hYnn : 0 ≤ ∫ v in Ioi (1 : ℝ), factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi fun v _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
    simp only [Z, Y]
    rw [← mul_sub, abs_mul, abs_of_pos (hN0 n)]
    calc N n * |_| ≤ N n * ((Real.sqrt (N n))⁻¹ *
          (∫ v in Ioi (1 : ℝ), factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2) +
          (1 + 1 / (Real.sqrt (N n))⁻¹) * (4 / ((n + 2 : ℕ) : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hc (hN0 n).le
      _ = (N n * ∫ v in Ioi (1 : ℝ), factorialAffineCollarHead (n + 1) (n + 2) v ^ 2 / v ^ 2) *
          (Real.sqrt (N n))⁻¹ + N n * ((1 + 1 / (Real.sqrt (N n))⁻¹) *
            (4 / ((n + 2 : ℕ) : ℝ)) ^ 2) := by ring
      _ ≤ _ := by linarith [htail]
  have hinvs : Tendsto (fun n => (Real.sqrt (N n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hNtop)
  have hinvN : Tendsto (fun n => 16 / N n) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hNtop).const_mul (16 : ℝ)
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using this
  have hbound : Tendsto (fun n => Y n * (Real.sqrt (N n))⁻¹ + 16 / N n +
      16 * (Real.sqrt (N n))⁻¹) atTop (𝓝 0) := by
    have := ((hY.mul hinvs).add hinvN).add (hinvs.const_mul 16)
    simpa using this
  have hZ : Tendsto Z atTop (𝓝 (Real.pi ^ 2 * (1 / 144) * S)) := by
    have hzero : Tendsto (fun n => Z n - Y n) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hdiff n) hbound
    simpa using hzero.add hY
  have hfinal := hZ.const_mul (4 / Real.pi ^ 4)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [show 4 / Real.pi ^ 4 * (Real.pi ^ 2 * (1 / 144) * S) = S / (36 * Real.pi ^ 2) by
    field_simp; ring] at hfinal
  refine hfinal.congr fun n => ?_
  simp only [Z]
  have hint : (∫ v in Ioi (1 : ℝ),
      (-(Real.pi ^ 2 / 2) * factorialAffineCollarError (n + 1) v) ^ 2 / v ^ 2) =
      (Real.pi ^ 4 / 4) * ∫ v in Ioi (1 : ℝ), factorialAffineCollarError (n + 1) v ^ 2 / v ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun v _ => by ring
  rw [hint]
  field_simp
  simp only [N]
  ring

private theorem dyadicHarmonicChi_sq (k : ℕ) :
    dyadicHarmonicChi k ^ 2 = if 4 ∣ k then 0 else 1 := by
  unfold dyadicHarmonicChi
  split_ifs <;> (try norm_num) <;> omega

/-- Only multiples of four are removed: `Σ_k χ(k)²/k³ = (63/64) ζ(3)`. -/
theorem tsum_natCast_mul_dyadicHarmonicWeight_sq :
    ∑' k : ℕ, (k : ℝ) * dyadicHarmonicWeight k ^ 2 = (63 / 64) * ∑' k : ℕ, 1 / (k : ℝ) ^ 3 := by
  have hz : Summable fun k : ℕ => 1 / (k : ℝ) ^ 3 := Real.summable_one_div_nat_pow.mpr (by norm_num)
  set f : ℕ → ℝ := fun k => if 4 ∣ k then 1 / (k : ℝ) ^ 3 else 0
  have hf : Summable f := hz.of_nonneg_of_le (fun k => by simp only [f]; split_ifs <;> positivity)
    fun k => by simp only [f]; split_ifs <;> [exact le_rfl; positivity]
  have hterm (k : ℕ) : (k : ℝ) * dyadicHarmonicWeight k ^ 2 = 1 / (k : ℝ) ^ 3 - f k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [f]
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      simp only [dyadicHarmonicWeight, f, div_pow, dyadicHarmonicChi_sq]
      split_ifs <;> field_simp <;> ring
  have hfour : ∑' k : ℕ, f k = (1 / 64) * ∑' k : ℕ, 1 / (k : ℝ) ^ 3 := by
    have hinj : Function.Injective fun j : ℕ => 4 * j := fun a b h => by simpa using h
    have hsupp : Function.support f ⊆ Set.range fun j : ℕ => 4 * j := by
      intro k hk
      simp only [Function.mem_support, f, ne_eq] at hk
      split_ifs at hk with h
      · obtain ⟨j, rfl⟩ := h; exact ⟨j, rfl⟩
      · exact absurd rfl hk
    rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [f, dvd_mul_right, if_true]
    push_cast
    ring
  rw [tsum_congr hterm, hz.tsum_sub hf, hfour]
  ring

/-- **Sharp affine collar constant.** The critical-weight energy of the affine clock error obeys
`N ∫_{v>1} v⁻² |Φ_N - Ψ_N|² → 7ζ(3)/(256π²)`. -/
theorem tendsto_factorialAffineCollarError_sharp :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      ∫ v in Ioi (1 : ℝ), factorialAffineCollarError (n + 1) v ^ 2 / v ^ 2) atTop
      (𝓝 (7 * (∑' k : ℕ, 1 / (k : ℝ) ^ 3) / (256 * Real.pi ^ 2))) := by
  have h := tendsto_factorialAffineCollarError_energy
  rw [tsum_natCast_mul_dyadicHarmonicWeight_sq] at h
  convert h using 2
  field_simp
  ring

/-- The affine collar error is the singleton span difference `Φ_N - Ψ_N`. -/
theorem factorialPhaseCombination_sub_affine_singleton (n : ℕ) (v : ℝ) :
    factorialPhaseCombination {n} (fun _ => 1) v - factorialAffinePhaseCombination {n} (fun _ => 1) v =
      (factorialAffineCollarError (n + 1) v : ℂ) := by
  simp only [factorialPhaseCombination, factorialAffinePhaseCombination, Finset.sum_singleton,
    one_mul, factorialPhaseProfile_eq_centered, factorialAffineCollarError]
  push_cast
  ring

/-- The README's affine model constant for a single source scale. -/
theorem tendsto_factorialAffinePhaseCombination_singleton_sharp :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ∫ v in Ioi (1 : ℝ),
      ‖factorialPhaseCombination {n} (fun _ => 1) v -
        factorialAffinePhaseCombination {n} (fun _ => 1) v‖ ^ 2 / v ^ 2) atTop
      (𝓝 (7 * (∑' k : ℕ, 1 / (k : ℝ) ^ 3) / (256 * Real.pi ^ 2))) := by
  refine tendsto_factorialAffineCollarError_sharp.congr fun n => ?_
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [factorialPhaseCombination_sub_affine_singleton, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

end GaloisForLFunctions.ArithmeticPositivityTheory
