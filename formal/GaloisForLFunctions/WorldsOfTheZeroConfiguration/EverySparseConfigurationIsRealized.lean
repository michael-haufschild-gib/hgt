import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheTailOfZetaBeyondACutoff
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EveryConfigurationThatApproachesTheLineIsRealized
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv

/-!
# Every sparse configuration is realized

A sparse configuration is a sequence `ρ_j` with `1/2 < Re ρ_j ≤ b` and `|Im ρ_j| ≥ (j+1)^A`,
where `b + 1/(2A) < 14/15` (`IsSparseConfig`).  The real parts are arbitrary: they may increase to
a limit that is not attained (world II), or be constant (zeros on a vertical line).

**Target.**  The pair `ρ_j` is on beyond its cutoff `N_j = ⌈|Im ρ_j|⌉²`:
`m(k) = Σ_{j : N_j < k} −2 Re k^{ρ_j − 1}` (`sparseTarget`).  At `k` at most `k^{1/(2A)}` pairs
are on, so `m(k) = O(k^{b + 1/(2A) − 1})`.

**Factor.**  `L = P · P̄`, the genus-one canonical products over the points and over their
conjugates (`sparseFactor`).  On `Re s > 1`

`L′/L = −Σ_k m(k) k^{−s} − Φ₀(s)`, `Φ₀ = Σ_j (Z_{N_j}(s + 1 − ρ_j) − 1/ρ_j) + (conjugates)`

(`logDeriv_sparseFactor_eq`): the series of the pair `j` is minus its two poles minus the cut
regular parts, and the sum over `j` and the sum over `k` commute.

**The regular part converges on `Re s > 1/2`** (`differentiableOn_regSeries`).  On
`{Re s > 1/2, |s| < T}` and for `|Im ρ_j| ≥ 2T + 3` the term `j` is at most
`11 |Im ρ_j|^{2b − 2} ≤ 11 (j+1)^{−A(2 − 2b)}`, and `A(2 − 2b) > 1`.  The exponent `2 − 2b` is that
of the density hypothesis: a configuration with `N(T) ≪ T^{2(1−b)−ε}` points up to height `T` is
sparse in this sense.

**Theorem** (`exists_isEdit_sparseTwin`).  The greedy edit of the target has

`(s − 1) ζ_B(s) = (s − 1) ζ(s) · C · L(s) · e^{H(s)}`, `H` holomorphic on `Re s > 1/2`

(`IsFactorTwin`), count `A x + O(x^β)` for every `β > b + 1/(2A)`, and its fake zeros right of
the line are exactly the points `ρ_j`, `ρ̄_j`.  Instances: infinitely many fake zeros on one
vertical line (`exists_isEdit_zeros_on_a_vertical_line`) and fake zeros whose real parts increase
to a limit that is not attained (`exists_isEdit_zeros_rising_to_a_line`).
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.CountableDivisor

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits

/-! ## Twins with a factor -/

/-- `B` is a **twin of `ζ` with the factor `L`**:
`(s − 1) ζ_B(s) = (s − 1) ζ(s) · C · L(s) · e^{H(s)}`, `C ≠ 0`, `H` holomorphic on `Re s > 1/2`. -/
def IsFactorTwin (B : BeurlingSystem) (L : ℂ → ℂ) : Prop :=
  ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ H {s : ℂ | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * L s * Complex.exp (H s))

/-- **The greedy edit of a target is a twin with the factor of the target.**  If
`|m(k)| ≤ A k^{−η}` with `1/15 < η ≤ 1/2` and `L′/L = −Σ m(k) k^{−s} − Φ₀` on `Re s > 1` with `Φ₀`
holomorphic on `Re s > 1/2`, the system of the greedy edit of `m` is a twin with the factor `L`. -/
theorem isFactorTwin_gedit {m : ℕ → ℝ} {A η : ℝ} (hA : 0 ≤ A) (hη : 1 / 15 < η)
    (hη1 : η ≤ 1 / 2) (hm0 : m 0 = 0) (hm : ∀ k : ℕ, 1 ≤ k → |m k| ≤ A * (k : ℝ) ^ (-η))
    {L Φ₀ : ℂ → ℂ} (hΦ₀ : DifferentiableOn ℂ Φ₀ {s : ℂ | 1 / 2 < s.re})
    (hL : ∀ s : ℂ, 1 < s.re → L s ≠ 0 ∧ DifferentiableAt ℂ L s ∧
      logDeriv L s = -LSeries (fun k => (m k : ℂ)) s - Φ₀ s) :
    IsFactorTwin (editSystem (gedit m)) L := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (17 / 30 + (1 / 2 + η)) / 2 := ⟨_, rfl⟩
  have hα0 : 17 / 30 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαc : α - η ≤ 1 / 2 := by rw [hα]; linarith
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths hα0 hα1
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_gdisc_le_rpow_of_abs_le (m := m) (A := A) (η := η)
    (c := 1 / 2) hA (by linarith) (by linarith) hm hα1 (by norm_num) hαc hwin
  have hsumm : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun k => (m k : ℂ)) s := by
    intro s hs
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1 - η) (by linarith)
      ⟨A, fun n hn => ?_⟩
    show ‖((m n : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, show 1 - η - 1 = -η by ring]
    exact hm n (Nat.one_le_iff_ne_zero.mpr hn)
  obtain ⟨C, K, hC, hK, hfac⟩ := exists_exp_geditSeries_eq (m := m) hm0 hK₀ (by norm_num)
    (by norm_num) hdisc hsumm (L := L) hΦ₀ hL
  have he := isEdit_gedit m
  refine ⟨C, fun s => K s + editRem (gedit m) s, hC, hK.add (differentiableOn_editRem he),
    fun s hs => ?_⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hEK : Complex.exp (LSeries (fun k => (gedit m k : ℂ)) s + editRem (gedit m) s) =
      C * L s * Complex.exp (K s + editRem (gedit m) s) := by
    rw [Complex.exp_add, hfac s hs, Complex.exp_add]
    ring
  rw [editSystem_zetaSeriesC he hs, hEK, zetaResidueUnit_of_ne hs1]
  ring

/-- The count of the greedy edit of a target of size `A k^{−η}`: `A′ x + O(x^β)`, `β > 1 − η`. -/
theorem editSystem_gedit_count {m : ℕ → ℝ} {A η : ℝ} (hA : 0 ≤ A) (hη1 : η < 1)
    (hm : ∀ k : ℕ, 1 ≤ k → |m k| ≤ A * (k : ℝ) ^ (-η)) {β : ℝ} (hβ : 1 - η < β)
    (hβ1 : β < 1) :
    ∃ A' C : ℝ, 0 ≤ A' ∧ ∀ x : ℝ, 1 ≤ x →
      |((editSystem (gedit m)).countBall x : ℝ) - A' * x| ≤ C * x ^ β := by
  have hθ : 0 < 1 - η := by linarith
  refine editSystem_count (by linarith) hβ1 (summable_abs_gedit_rpow (θ := 1 - η) hθ.le
    (K := A / (1 - η)) (div_nonneg hA hθ.le) (fun n _ => ?_) hβ)
  have hI : Ioc 0 n = Icc 1 n := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  calc ∑ k ∈ Ioc 0 n, |m k| ≤ ∑ k ∈ Icc 1 n, A * (k : ℝ) ^ ((1 - η) - 1) := by
        rw [hI]
        refine Finset.sum_le_sum fun k hk => ?_
        rw [show (1 - η) - 1 = -η by ring]
        exact hm k (Finset.mem_Icc.mp hk).1
    _ = A * ∑ k ∈ Icc 1 n, (k : ℝ) ^ ((1 - η) - 1) := by rw [Finset.mul_sum]
    _ ≤ A * ((n : ℝ) ^ (1 - η) / (1 - η)) :=
        mul_le_mul_of_nonneg_left (DeletionData.sum_rpow_le hθ (by linarith) n) hA
    _ = A / (1 - η) * (n : ℝ) ^ (1 - η) := by ring

/-- The fake zeros of a twin with a factor are the zeros of the factor. -/
theorem IsFactorTwin.hasFakeZeroSet {B : BeurlingSystem} {L : ℂ → ℂ} (h : IsFactorTwin B L)
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 / 2 < s.re}) :
    HasFakeZeroSet B {z : ℂ | L z = 0} := by
  obtain ⟨C, H, hC, hH, hfac⟩ := h
  refine ⟨fun s => zetaResidueUnit s * (C * L s * Complex.exp (H s)),
    differentiable_zetaResidueUnit.differentiableOn.mul
      (((differentiableOn_const C).mul hL).mul hH.cexp),
    fun s hs => (hfac s hs).symm, fun z _ hz1 hzζ => ?_⟩
  have hzu : zetaResidueUnit z ≠ 0 := by
    rw [zetaResidueUnit_of_ne hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) hzζ
  simp only [mul_eq_zero, hzu, hC, Complex.exp_ne_zero, false_or, or_false, Set.mem_setOf_eq]

/-! ## Sparse configurations -/

/-- `Σ_j (j+1)^p` converges for `p < −1`. -/
theorem summable_add_one_rpow {p : ℝ} (hp : p < -1) :
    Summable fun j : ℕ => ((j : ℝ) + 1) ^ p := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  refine h.congr fun n => ?_
  rw [Nat.cast_add, Nat.cast_one]

/-- A **sparse configuration**: points right of the line with real parts at most `b` whose
heights grow at least like `(j+1)^A`, with `b + 1/(2A) < 14/15`. -/
structure IsSparseConfig (ρ : ℕ → ℂ) (b A : ℝ) : Prop where
  half : ∀ j, 1 / 2 < (ρ j).re
  le : ∀ j, (ρ j).re ≤ b
  pos : 0 < A
  room : b + 1 / (2 * A) < 14 / 15
  height : ∀ j : ℕ, ((j : ℝ) + 1) ^ A ≤ |(ρ j).im|

/-- The cutoff of the pair `ρ_j`: the pair is on beyond `⌈|Im ρ_j|⌉²`. -/
def cutoff (ρ : ℕ → ℂ) (j : ℕ) : ℕ := ⌈|(ρ j).im|⌉₊ ^ 2

/-- The target of a sparse configuration. -/
def sparseTarget (ρ : ℕ → ℂ) (k : ℕ) : ℝ := ∑ j ∈ range k, cutTarget (ρ j) (cutoff ρ j) k

/-- The regular part of the pair `ρ_j` minus the convergence term of the canonical product. -/
def regTerm (ρ : ℕ → ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  zetaCut (cutoff ρ j) (s - (ρ j - 1)) - (ρ j)⁻¹

/-- The regular part of a configuration. -/
def regSeries (ρ : ℕ → ℂ) (s : ℂ) : ℂ := ∑' j, regTerm ρ j s

/-- The factor of a sparse configuration: the canonical products over the points and over
their conjugates. -/
def sparseFactor (ρ : ℕ → ℂ) (s : ℂ) : ℂ :=
  canonicalProductE1Indexed ρ s * canonicalProductE1Indexed (fun j => (starRingEnd ℂ) (ρ j)) s

theorem cutoff_conj (ρ : ℕ → ℂ) (j : ℕ) :
    cutoff (fun j => (starRingEnd ℂ) (ρ j)) j = cutoff ρ j := by
  simp only [cutoff, Complex.conj_im, abs_neg]

theorem sparseTarget_zero (ρ : ℕ → ℂ) : sparseTarget ρ 0 = 0 := by
  simp [sparseTarget]

theorem differentiable_regTerm (ρ : ℕ → ℂ) (j : ℕ) : Differentiable ℂ (regTerm ρ j) := by
  show Differentiable ℂ (fun s : ℂ => zetaCut (cutoff ρ j) (s - (ρ j - 1)) - (ρ j)⁻¹)
  exact ((differentiable_zetaCut _).comp (differentiable_id.sub_const _)).sub_const _

namespace IsSparseConfig

variable {ρ : ℕ → ℂ} {b A : ℝ}

theorem half_lt_b (h : IsSparseConfig ρ b A) : 1 / 2 < b := lt_of_lt_of_le (h.half 0) (h.le 0)

theorem b_lt (h : IsSparseConfig ρ b A) : b < 14 / 15 := by
  have h1 : 0 < 1 / (2 * A) := one_div_pos.mpr (by linarith [h.pos])
  linarith [h.room]

theorem one_lt (h : IsSparseConfig ρ b A) : 1 < A := by
  have h1 : 1 / (2 * A) < 13 / 30 := by linarith [h.room, h.half_lt_b]
  rw [div_lt_iff₀ (by linarith [h.pos] : (0 : ℝ) < 2 * A)] at h1
  linarith

/-- `A (2 − 2b) > 1`: the regular parts are summable. -/
theorem exponent (h : IsSparseConfig ρ b A) : A * (2 * b - 2) < -1 := by
  have h1 : 1 / (2 * A) < 1 - b := by linarith [h.room]
  rw [div_lt_iff₀ (by linarith [h.pos] : (0 : ℝ) < 2 * A)] at h1
  linarith

/-- The conjugate configuration is sparse. -/
theorem conj (h : IsSparseConfig ρ b A) :
    IsSparseConfig (fun j => (starRingEnd ℂ) (ρ j)) b A where
  half j := by
    show 1 / 2 < ((starRingEnd ℂ) (ρ j)).re
    rw [Complex.conj_re]
    exact h.half j
  le j := by
    show ((starRingEnd ℂ) (ρ j)).re ≤ b
    rw [Complex.conj_re]
    exact h.le j
  pos := h.pos
  room := h.room
  height j := by
    show ((j : ℝ) + 1) ^ A ≤ |((starRingEnd ℂ) (ρ j)).im|
    rw [Complex.conj_im, abs_neg]
    exact h.height j

theorem one_le_height (h : IsSparseConfig ρ b A) (j : ℕ) : (j : ℝ) + 1 ≤ |(ρ j).im| := by
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have h1 := Real.rpow_le_rpow_of_exponent_le hj h.one_lt.le
  rw [Real.rpow_one] at h1
  exact h1.trans (h.height j)

theorem ne_zero (h : IsSparseConfig ρ b A) (j : ℕ) : ρ j ≠ 0 := fun h0 => by
  have h1 := h.half j
  rw [h0, Complex.zero_re] at h1
  norm_num at h1

theorem add_one_le_norm (h : IsSparseConfig ρ b A) (j : ℕ) : (j : ℝ) + 1 ≤ ‖ρ j‖ :=
  (h.one_le_height j).trans (Complex.abs_im_le_norm _)

theorem summable_inv_sq (h : IsSparseConfig ρ b A) :
    Summable fun j => 1 / ‖ρ j‖ ^ (2 : ℕ) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_add_one_rpow (p := -2) (by norm_num))
  have h0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [Real.rpow_neg h0.le, Real.rpow_two, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h0.le (h.add_one_le_norm j) 2)

theorem locallyFinite (h : IsSparseConfig ρ b A) : LocallyFiniteDivisor ρ := fun r =>
  (Set.finite_Iio ⌈r⌉₊).subset fun j (hj : ‖ρ j‖ ≤ r) =>
    show j < ⌈r⌉₊ from Nat.lt_ceil.mpr (by linarith [h.add_one_le_norm j])

/-! ### The cutoff and the target -/

theorem rpow_le_cutoff (h : IsSparseConfig ρ b A) (j : ℕ) :
    ((j : ℝ) + 1) ^ (2 * A) ≤ (cutoff ρ j : ℝ) := by
  have h0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have h1 : ((j : ℝ) + 1) ^ A ≤ (⌈|(ρ j).im|⌉₊ : ℝ) := (h.height j).trans (Nat.le_ceil _)
  have h2 : (((j : ℝ) + 1) ^ A) ^ 2 ≤ (⌈|(ρ j).im|⌉₊ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg h0 _) h1 2
  have h3 : ((j : ℝ) + 1) ^ (2 * A) = (((j : ℝ) + 1) ^ A) ^ 2 := by
    rw [mul_comm, Real.rpow_mul h0, Real.rpow_two]
  rw [h3, cutoff, Nat.cast_pow]
  exact h2

theorem lt_cutoff (h : IsSparseConfig ρ b A) (j : ℕ) : j < cutoff ρ j := by
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have h2 := Real.rpow_le_rpow_of_exponent_le hj (by linarith [h.one_lt] : (1 : ℝ) ≤ 2 * A)
  rw [Real.rpow_one] at h2
  have h3 : ((j + 1 : ℕ) : ℝ) ≤ (cutoff ρ j : ℝ) := by
    push_cast
    exact h2.trans (h.rpow_le_cutoff j)
  exact Nat.lt_of_succ_le (by exact_mod_cast h3)

/-- At `k` at most `k^{1/(2A)}` pairs are on. -/
theorem card_on_le (h : IsSparseConfig ρ b A) (k : ℕ) :
    (((range k).filter fun j => cutoff ρ j < k).card : ℝ) ≤ (k : ℝ) ^ (1 / (2 * A)) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2A : 0 < 2 * A := by linarith [h.pos]
  have hsub : (range k).filter (fun j => cutoff ρ j < k) ⊆
      range ⌊(k : ℝ) ^ (1 / (2 * A))⌋₊ := by
    intro j hj
    have hjk : cutoff ρ j < k := (Finset.mem_filter.mp hj).2
    have h0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    have h1 : ((j : ℝ) + 1) ^ (2 * A) ≤ (k : ℝ) :=
      (h.rpow_le_cutoff j).trans (by exact_mod_cast hjk.le)
    have h3 := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) h1 (one_div_nonneg.mpr h2A.le)
    rw [← Real.rpow_mul h0, mul_one_div_cancel h2A.ne', Real.rpow_one] at h3
    exact Finset.mem_range.mpr (Nat.lt_of_succ_le (Nat.le_floor (by push_cast; exact h3)))
  calc (((range k).filter fun j => cutoff ρ j < k).card : ℝ)
      ≤ ((range ⌊(k : ℝ) ^ (1 / (2 * A))⌋₊).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (⌊(k : ℝ) ^ (1 / (2 * A))⌋₊ : ℝ) := by rw [Finset.card_range]
    _ ≤ (k : ℝ) ^ (1 / (2 * A)) := Nat.floor_le (Real.rpow_nonneg hk0 _)

/-- The target is `O(k^{b + 1/(2A) − 1})`. -/
theorem abs_sparseTarget_le (h : IsSparseConfig ρ b A) {k : ℕ} (hk : 1 ≤ k) :
    |sparseTarget ρ k| ≤ 2 * (k : ℝ) ^ (-(1 - (b + 1 / (2 * A)))) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hterm : ∀ j ∈ (range k).filter (fun j => cutoff ρ j < k),
      |target (ρ j) k| ≤ 2 * (k : ℝ) ^ (b - 1) := by
    intro j _
    have h1 : (k : ℝ) ^ ((ρ j).re - 1) ≤ (k : ℝ) ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [h.le j])
    linarith [abs_target_le (ρ j) hk]
  have hsum : sparseTarget ρ k =
      ∑ j ∈ (range k).filter (fun j => cutoff ρ j < k), target (ρ j) k := by
    simp only [sparseTarget, cutTarget, Finset.sum_filter]
  have hpow : (k : ℝ) ^ (1 / (2 * A)) * (k : ℝ) ^ (b - 1) =
      (k : ℝ) ^ (-(1 - (b + 1 / (2 * A)))) := by
    rw [← Real.rpow_add hk0]
    congr 1
    ring
  have hq : 0 ≤ 2 * (k : ℝ) ^ (b - 1) := mul_nonneg (by norm_num) (Real.rpow_nonneg hk0.le _)
  calc |sparseTarget ρ k|
      ≤ ∑ j ∈ (range k).filter (fun j => cutoff ρ j < k), |target (ρ j) k| := by
        rw [hsum]
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ (range k).filter (fun j => cutoff ρ j < k), 2 * (k : ℝ) ^ (b - 1) :=
        Finset.sum_le_sum hterm
    _ = ((range k).filter fun j => cutoff ρ j < k).card * (2 * (k : ℝ) ^ (b - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) ^ (1 / (2 * A)) * (2 * (k : ℝ) ^ (b - 1)) :=
        mul_le_mul_of_nonneg_right (h.card_on_le k) hq
    _ = 2 * (k : ℝ) ^ (-(1 - (b + 1 / (2 * A)))) := by rw [← hpow]; ring

/-! ### The series of the target is the sum of the series of its pairs -/

/-- A term of the series of the pair `j` is at most `2 (j+1)^{−2Aθ} k^{θ + b − 1 − Re s}`. -/
theorem norm_term_cutTarget_le (h : IsSparseConfig ρ b A) {s : ℂ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (j k : ℕ) :
    ‖LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k‖ ≤
      2 * ((j : ℝ) + 1) ^ (-(2 * A * θ)) * (k : ℝ) ^ (θ + b - 1 - s.re) := by
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ 2 * ((j : ℝ) + 1) ^ (-(2 * A * θ)) * (k : ℝ) ^ (θ + b - 1 - s.re) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hj0.le _))
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [LSeries.term_zero, norm_zero]
    exact hnonneg
  by_cases hon : cutoff ρ j < k
  · have hk1n : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1n
    have hkpos : (0 : ℝ) < k := by linarith
    have hnorm : ‖LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k‖ =
        |target (ρ j) k| / (k : ℝ) ^ s.re := by
      simp only [LSeries.term_of_ne_zero hk0, cutTarget, if_pos hon]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk0)]
    have h1 : |target (ρ j) k| ≤ 2 * (k : ℝ) ^ (b - 1) := by
      have h1 : (k : ℝ) ^ ((ρ j).re - 1) ≤ (k : ℝ) ^ (b - 1) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [h.le j])
      linarith [abs_target_le (ρ j) hk1n]
    have h2 : ((j : ℝ) + 1) ^ (2 * A * θ) ≤ (k : ℝ) ^ θ := by
      have h3 : ((j : ℝ) + 1) ^ (2 * A) ≤ (k : ℝ) :=
        (h.rpow_le_cutoff j).trans (by exact_mod_cast hon.le)
      have h4 := Real.rpow_le_rpow (Real.rpow_nonneg hj0.le _) h3 hθ0
      rwa [← Real.rpow_mul hj0.le] at h4
    have h5 : 1 ≤ ((j : ℝ) + 1) ^ (-(2 * A * θ)) * (k : ℝ) ^ θ := by
      rw [Real.rpow_neg hj0.le, ← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hj0 _),
        one_mul]
      exact h2
    have hsplit : (k : ℝ) ^ (θ + b - 1 - s.re) =
        (k : ℝ) ^ θ * ((k : ℝ) ^ (b - 1) / (k : ℝ) ^ s.re) := by
      rw [← Real.rpow_sub hkpos, ← Real.rpow_add hkpos]
      congr 1
      ring
    have hq : 0 ≤ (k : ℝ) ^ (b - 1) / (k : ℝ) ^ s.re :=
      div_nonneg (Real.rpow_nonneg hkpos.le _) (Real.rpow_nonneg hkpos.le _)
    have h6 : |target (ρ j) k| / (k : ℝ) ^ s.re ≤
        2 * ((k : ℝ) ^ (b - 1) / (k : ℝ) ^ s.re) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right h1 (Real.rpow_nonneg hkpos.le _)
    rw [hnorm, hsplit]
    calc |target (ρ j) k| / (k : ℝ) ^ s.re
        ≤ 1 * (2 * ((k : ℝ) ^ (b - 1) / (k : ℝ) ^ s.re)) := by rw [one_mul]; exact h6
      _ ≤ (((j : ℝ) + 1) ^ (-(2 * A * θ)) * (k : ℝ) ^ θ) *
            (2 * ((k : ℝ) ^ (b - 1) / (k : ℝ) ^ s.re)) :=
          mul_le_mul_of_nonneg_right h5 (by linarith)
      _ = 2 * ((j : ℝ) + 1) ^ (-(2 * A * θ)) *
            ((k : ℝ) ^ θ * ((k : ℝ) ^ (b - 1) / (k : ℝ) ^ s.re)) := by ring
  · have h0 : LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k =
        0 := by
      simp only [LSeries.term_of_ne_zero hk0, cutTarget, if_neg hon, Complex.ofReal_zero,
        zero_div]
    rw [h0, norm_zero]
    exact hnonneg

/-- **The sums over the pairs and over the integers commute**: for `Re s > 1` the Dirichlet
series of the target is the sum of the series of its pairs. -/
theorem hasSum_lseries_cutTarget (h : IsSparseConfig ρ b A) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun j : ℕ => LSeries (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s)
      (LSeries (fun k : ℕ => ((sparseTarget ρ k : ℝ) : ℂ)) s) := by
  have h2A : 0 < 2 * A := by linarith [h.pos]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 / (2 * A) + (s.re - b)) / 2 := ⟨_, rfl⟩
  have hθ1 : 1 / (2 * A) < θ := by rw [hθ]; linarith [h.room]
  have hθ2 : θ < s.re - b := by rw [hθ]; linarith [h.room]
  have hθ0 : 0 < θ := lt_trans (one_div_pos.mpr h2A) hθ1
  have hexp : 1 < 2 * A * θ := by
    have h1 := mul_lt_mul_of_pos_left hθ1 h2A
    rwa [mul_one_div_cancel h2A.ne'] at h1
  have hg : Summable fun j : ℕ => 2 * ((j : ℝ) + 1) ^ (-(2 * A * θ)) :=
    (summable_add_one_rpow (by linarith)).mul_left 2
  have hh : Summable fun k : ℕ => (k : ℝ) ^ (θ + b - 1 - s.re) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hmaj : Summable fun p : ℕ × ℕ =>
      2 * ((p.1 : ℝ) + 1) ^ (-(2 * A * θ)) * (p.2 : ℝ) ^ (θ + b - 1 - s.re) :=
    hg.mul_of_nonneg hh
      (fun j => mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
      (fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hsum2 : Summable (Function.uncurry fun j k : ℕ =>
      LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k) :=
    Summable.of_norm_bounded hmaj fun p => h.norm_term_cutTarget_le hθ0.le p.1 p.2
  have hcomm := hsum2.tsum_comm
  have hjsum : Summable fun j : ℕ => ∑' k : ℕ,
      LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k :=
    hsum2.prod
  -- at a fixed integer only finitely many pairs are on
  have hkj : ∀ k : ℕ, ∑' j : ℕ,
      LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k =
      LSeries.term (fun k : ℕ => ((sparseTarget ρ k : ℝ) : ℂ)) s k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk0
    · simp only [LSeries.term_zero, tsum_zero]
    · have hzero : ∀ j ∉ range k,
          LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k = 0 := by
        intro j hj
        have hjk : k ≤ j := not_lt.mp fun hlt => hj (Finset.mem_range.mpr hlt)
        have hoff : ¬ cutoff ρ j < k := fun hlt => by
          have h1 := h.lt_cutoff j
          omega
        simp only [LSeries.term_of_ne_zero hk0, cutTarget, if_neg hoff, Complex.ofReal_zero,
          zero_div]
      rw [tsum_eq_sum hzero]
      simp only [LSeries.term_of_ne_zero hk0, sparseTarget]
      push_cast
      rw [Finset.sum_div]
  have hval : ∑' j : ℕ, ∑' k : ℕ,
      LSeries.term (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s k =
      LSeries (fun k : ℕ => ((sparseTarget ρ k : ℝ) : ℂ)) s := by
    rw [← hcomm]
    exact tsum_congr hkj
  have hfin := hjsum.hasSum
  rw [hval] at hfin
  exact hfin

/-! ### The regular part -/

/-- Far above the point `s` the regular term of the pair `j` is `O((j+1)^{−A(2−2b)})`. -/
theorem norm_regTerm_le (h : IsSparseConfig ρ b A) {T : ℝ} (hT0 : 0 ≤ T) {j : ℕ}
    (hj : 2 * T + 3 ≤ |(ρ j).im|) {s : ℂ} (hs : 1 / 2 < s.re) (hsT : ‖s‖ ≤ T) :
    ‖regTerm ρ j s‖ ≤ 11 * ((j : ℝ) + 1) ^ (A * (2 * b - 2)) := by
  have ht1 : 1 ≤ |(ρ j).im| := by linarith
  have ht0 : 0 < |(ρ j).im| := by linarith
  have h1 := norm_zetaCut_sq_le (ρ := ρ j) (s := s) (b := b) (T := T)
    (by linarith [h.half j]) (h.le j) h.half_lt_b.le (by linarith [h.b_lt]) hT0 hj hs hsT
  have h2 : ‖(ρ j)⁻¹‖ ≤ |(ρ j).im| ^ (2 * b - 2) := by
    rw [norm_inv]
    have h3 : |(ρ j).im| ≤ ‖ρ j‖ := Complex.abs_im_le_norm _
    have h4 : ‖ρ j‖⁻¹ ≤ |(ρ j).im|⁻¹ := inv_anti₀ ht0 h3
    have h5 : |(ρ j).im| ^ (-1 : ℝ) ≤ |(ρ j).im| ^ (2 * b - 2) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [h.half_lt_b])
    rw [Real.rpow_neg_one] at h5
    exact h4.trans h5
  have h3 : |(ρ j).im| ^ (2 * b - 2) ≤ ((j : ℝ) + 1) ^ (A * (2 * b - 2)) := by
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h4 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hj0 A) (h.height j)
      (by linarith [h.b_lt] : 2 * b - 2 ≤ 0)
    rwa [← Real.rpow_mul hj0.le] at h4
  calc ‖regTerm ρ j s‖
      ≤ ‖zetaCut (cutoff ρ j) (s - (ρ j - 1))‖ + ‖(ρ j)⁻¹‖ := norm_sub_le _ _
    _ ≤ 10 * |(ρ j).im| ^ (2 * b - 2) + |(ρ j).im| ^ (2 * b - 2) := add_le_add h1 h2
    _ = 11 * |(ρ j).im| ^ (2 * b - 2) := by ring
    _ ≤ 11 * ((j : ℝ) + 1) ^ (A * (2 * b - 2)) := by linarith

/-- The regular terms beyond `J ≥ 2T + 3` are bounded on `{Re s > 1/2, |s| ≤ T}`. -/
theorem norm_regTerm_add_le (h : IsSparseConfig ρ b A) {T : ℝ} (hT0 : 0 ≤ T) {J : ℕ}
    (hJ : 2 * T + 3 ≤ (J : ℝ)) (j : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) (hsT : ‖s‖ ≤ T) :
    ‖regTerm ρ (j + J) s‖ ≤ 11 * ((j : ℝ) + 1) ^ (A * (2 * b - 2)) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hfar : 2 * T + 3 ≤ |(ρ (j + J)).im| := by
    have h1 := h.one_le_height (j + J)
    push_cast at h1
    linarith
  refine (h.norm_regTerm_le hT0 hfar hs hsT).trans
    (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by linarith [h.exponent])
  push_cast
  linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]

theorem summable_regTerm (h : IsSparseConfig ρ b A) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun j => regTerm ρ j s := by
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌈2 * ‖s‖ + 3⌉₊ := ⟨_, rfl⟩
  have hJ' : 2 * ‖s‖ + 3 ≤ (J : ℝ) := by rw [hJ]; exact Nat.le_ceil _
  refine (summable_nat_add_iff J).mp ?_
  exact Summable.of_norm_bounded ((summable_add_one_rpow h.exponent).mul_left 11)
    fun j => h.norm_regTerm_add_le (norm_nonneg s) hJ' j hs le_rfl

/-- **The regular part of a sparse configuration is holomorphic on `Re s > 1/2`.** -/
theorem differentiableOn_regSeries (h : IsSparseConfig ρ b A) :
    DifferentiableOn ℂ (regSeries ρ) {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ hs₀
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ‖s₀‖ + 1 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌈2 * T + 3⌉₊ := ⟨_, rfl⟩
  have hJ' : 2 * T + 3 ≤ (J : ℝ) := by rw [hJ]; exact Nat.le_ceil _
  have hUo : IsOpen ({s : ℂ | 1 / 2 < s.re} ∩ Metric.ball (0 : ℂ) T) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s₀ ∈ {s : ℂ | 1 / 2 < s.re} ∩ Metric.ball (0 : ℂ) T :=
    ⟨hs₀, by rw [Metric.mem_ball, dist_zero_right, hT]; linarith⟩
  have hball : ∀ w : ℂ, w ∈ {s : ℂ | 1 / 2 < s.re} ∩ Metric.ball (0 : ℂ) T → ‖w‖ ≤ T := by
    intro w hw
    have h1 := hw.2
    rw [Metric.mem_ball, dist_zero_right] at h1
    exact h1.le
  -- the terms beyond `J` converge uniformly on the bounded piece of the half-plane
  have htail : DifferentiableOn ℂ (fun w => ∑' j, regTerm ρ (j + J) w)
      ({s : ℂ | 1 / 2 < s.re} ∩ Metric.ball (0 : ℂ) T) :=
    Complex.differentiableOn_tsum_of_summable_norm
      ((summable_add_one_rpow h.exponent).mul_left 11)
      (fun j => (differentiable_regTerm ρ (j + J)).differentiableOn) hUo
      (fun j w hw => h.norm_regTerm_add_le hT0 hJ' j hw.1 (hball w hw))
  have hhead : DifferentiableOn ℂ (fun w => ∑ j ∈ range J, regTerm ρ j w)
      ({s : ℂ | 1 / 2 < s.re} ∩ Metric.ball (0 : ℂ) T) :=
    (Differentiable.fun_sum fun j _ => differentiable_regTerm ρ j).differentiableOn
  have hsplit : ∀ w ∈ {s : ℂ | 1 / 2 < s.re} ∩ Metric.ball (0 : ℂ) T,
      regSeries ρ w = (∑ j ∈ range J, regTerm ρ j w) + ∑' j, regTerm ρ (j + J) w :=
    fun w hw => ((h.summable_regTerm hw.1).sum_add_tsum_nat_add J).symm
  have hdiff : DifferentiableOn ℂ (regSeries ρ)
      ({s : ℂ | 1 / 2 < s.re} ∩ Metric.ball (0 : ℂ) T) := (hhead.add htail).congr hsplit
  exact (hdiff.differentiableAt (hUo.mem_nhds hmem)).differentiableWithinAt

/-! ### The canonical product -/

theorem differentiable_canonicalProduct (h : IsSparseConfig ρ b A) :
    Differentiable ℂ (canonicalProductE1Indexed ρ) := fun s =>
  (canonicalProductE1Indexed_analytic ρ h.ne_zero h.summable_inv_sq s
    (Set.mem_univ s)).differentiableAt

theorem differentiable_sparseFactor (h : IsSparseConfig ρ b A) :
    Differentiable ℂ (sparseFactor ρ) := by
  show Differentiable ℂ (fun s : ℂ => canonicalProductE1Indexed ρ s *
    canonicalProductE1Indexed (fun j => (starRingEnd ℂ) (ρ j)) s)
  exact h.differentiable_canonicalProduct.mul h.conj.differentiable_canonicalProduct

/-- The canonical product vanishes exactly at the points of the configuration. -/
theorem canonicalProduct_eq_zero_iff (h : IsSparseConfig ρ b A) (z : ℂ) :
    canonicalProductE1Indexed ρ z = 0 ↔ ∃ j, z = ρ j := by
  constructor
  · intro hz
    by_contra hne
    push Not at hne
    exact canonicalProductE1Indexed_ne_zero ρ h.ne_zero h.summable_inv_sq hne hz
  · rintro ⟨j, rfl⟩
    have hsplit := congrFun (canonicalProductE1Indexed_eq_pow_mul h.ne_zero h.summable_inv_sq
      h.locallyFinite (ρ j)) (ρ j)
    have hw : weierstrassE1 1 = 0 := by simp [weierstrassE1]
    have hn : ({i : ℕ | ρ i = ρ j} : Set ℕ).ncard ≠ 0 :=
      Set.ncard_ne_zero_of_mem (show j ∈ {i : ℕ | ρ i = ρ j} from rfl)
        (finite_fiber h.locallyFinite (ρ j))
    rw [hsplit, Pi.mul_apply]
    show weierstrassE1 (ρ j / ρ j) ^ ({i : ℕ | ρ i = ρ j} : Set ℕ).ncard * _ = 0
    rw [div_self (h.ne_zero j), hw, zero_pow hn, zero_mul]

/-- The factor vanishes exactly at the points of the configuration and their conjugates. -/
theorem sparseFactor_eq_zero_iff (h : IsSparseConfig ρ b A) (z : ℂ) :
    sparseFactor ρ z = 0 ↔ ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j) := by
  rw [sparseFactor, mul_eq_zero, h.canonicalProduct_eq_zero_iff,
    h.conj.canonicalProduct_eq_zero_iff]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨j, Or.inl hj⟩
    · exact ⟨j, Or.inr hj⟩
  · rintro ⟨j, hj | hj⟩
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr ⟨j, hj⟩

/-- The logarithmic derivative of the canonical product off the configuration. -/
theorem hasSum_logDeriv_canonicalProduct (h : IsSparseConfig ρ b A) {s : ℂ}
    (hs : ∀ j, s ≠ ρ j) :
    HasSum (fun j => (s - ρ j)⁻¹ + (ρ j)⁻¹) (logDeriv (canonicalProductE1Indexed ρ) s) := by
  have hsum : Summable fun j => (s - ρ j)⁻¹ + (ρ j)⁻¹ := by
    refine (summable_canonicalProductE1LogDerivTerm h.ne_zero h.summable_inv_sq hs).neg.congr
      fun j => ?_
    rw [← neg_sub s (ρ j), inv_neg]
    ring
  rw [logDeriv_canonicalProductE1Indexed h.ne_zero h.summable_inv_sq hs]
  exact hsum.hasSum

/-- **The factor of a sparse configuration against its target.**  On `Re s > 1`:
`L′/L = −Σ m(k) k^{−s} − (regular part)`. -/
theorem logDeriv_sparseFactor_eq (h : IsSparseConfig ρ b A) {s : ℂ} (hs : 1 < s.re) :
    sparseFactor ρ s ≠ 0 ∧ DifferentiableAt ℂ (sparseFactor ρ) s ∧
      logDeriv (sparseFactor ρ) s = -LSeries (fun k : ℕ => ((sparseTarget ρ k : ℝ) : ℂ)) s -
        (regSeries ρ s + regSeries (fun j => (starRingEnd ℂ) (ρ j)) s) := by
  have hb1 := h.b_lt
  have hne : ∀ j, s ≠ ρ j := fun j hj => by
    have h1 := h.le j
    rw [← hj] at h1
    linarith
  have hnec : ∀ j, s ≠ (starRingEnd ℂ) (ρ j) := fun j hj => by
    have h1 := h.le j
    rw [← Complex.conj_re (ρ j), ← hj] at h1
    linarith
  have hP : canonicalProductE1Indexed ρ s ≠ 0 :=
    canonicalProductE1Indexed_ne_zero ρ h.ne_zero h.summable_inv_sq hne
  have hPc : canonicalProductE1Indexed (fun j => (starRingEnd ℂ) (ρ j)) s ≠ 0 :=
    canonicalProductE1Indexed_ne_zero _ h.conj.ne_zero h.conj.summable_inv_sq hnec
  have hlog : logDeriv (sparseFactor ρ) s = logDeriv (canonicalProductE1Indexed ρ) s +
      logDeriv (canonicalProductE1Indexed fun j => (starRingEnd ℂ) (ρ j)) s :=
    logDeriv_mul s hP hPc (h.differentiable_canonicalProduct s)
      (h.conj.differentiable_canonicalProduct s)
  refine ⟨mul_ne_zero hP hPc, h.differentiable_sparseFactor s, ?_⟩
  have hhalf : 1 / 2 < s.re := by linarith
  -- the series over the pairs
  have hA := (h.hasSum_lseries_cutTarget hs).neg
  have hB := (h.summable_regTerm hhalf).hasSum
  have hBc := (h.conj.summable_regTerm hhalf).hasSum
  have hC := h.hasSum_logDeriv_canonicalProduct hne
  have hCc := h.conj.hasSum_logDeriv_canonicalProduct hnec
  have hterm : ∀ j, ((s - ρ j)⁻¹ + (ρ j)⁻¹) +
      ((s - (starRingEnd ℂ) (ρ j))⁻¹ + ((starRingEnd ℂ) (ρ j))⁻¹) =
      -LSeries (fun k : ℕ => ((cutTarget (ρ j) (cutoff ρ j) k : ℝ) : ℂ)) s -
        (regTerm ρ j s + regTerm (fun j => (starRingEnd ℂ) (ρ j)) j s) := by
    intro j
    rw [(lseriesHasSum_cutTarget (ρ := ρ j) (s := s) (by linarith [h.le j])
      (cutoff ρ j)).LSeries_eq]
    simp only [regTerm, cutoff_conj]
    ring
  rw [hlog]
  exact (hC.add hCc).tsum_eq.symm.trans
    ((tsum_congr hterm).trans (hA.sub (hB.add hBc)).tsum_eq)

/-- **The greedy edit of a sparse configuration is a twin with its canonical product.** -/
theorem isFactorTwin_sparse (h : IsSparseConfig ρ b A) :
    IsFactorTwin (editSystem (gedit (sparseTarget ρ))) (sparseFactor ρ) := by
  have hη : (1 : ℝ) / 15 < 1 - (b + 1 / (2 * A)) := by linarith [h.room]
  have hη1 : 1 - (b + 1 / (2 * A)) ≤ 1 / 2 := by
    have h1 : 0 < 1 / (2 * A) := one_div_pos.mpr (by linarith [h.pos])
    linarith [h.half_lt_b]
  exact isFactorTwin_gedit (A := 2) (η := 1 - (b + 1 / (2 * A))) (by norm_num) hη hη1
    (sparseTarget_zero ρ) (fun k hk => h.abs_sparseTarget_le hk)
    (Φ₀ := fun s => regSeries ρ s + regSeries (fun j => (starRingEnd ℂ) (ρ j)) s)
    (h.differentiableOn_regSeries.add h.conj.differentiableOn_regSeries)
    (fun s hs => h.logDeriv_sparseFactor_eq hs)

/-- **Every sparse configuration is realized.**  For every `β ∈ (b + 1/(2A), 1)` there is a
two-sided edit of the rational primes with count `A′ x + O(x^β)` whose zeta function is that of
`ζ` times the canonical product of the configuration and a zero-free factor; its fake zeros
right of the line are exactly the points `ρ_j`, `ρ̄_j`. -/
theorem exists_isEdit_sparseTwin (h : IsSparseConfig ρ b A) {β : ℝ}
    (hβ : b + 1 / (2 * A) < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A' C : ℝ, 0 ≤ A' ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A' * x| ≤ C * x ^ β) ∧
      IsFactorTwin (editSystem e) (sparseFactor ρ) ∧
      HasFakeZeroSet (editSystem e) {z : ℂ | ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  have htwin := h.isFactorTwin_sparse
  have hset : {z : ℂ | sparseFactor ρ z = 0} =
      {z : ℂ | ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
    ext z
    exact h.sparseFactor_eq_zero_iff z
  have hfake := htwin.hasFakeZeroSet h.differentiable_sparseFactor.differentiableOn
  rw [hset] at hfake
  have h1 : 0 < 1 / (2 * A) := one_div_pos.mpr (by linarith [h.pos])
  exact ⟨gedit (sparseTarget ρ), isEdit_gedit _,
    editSystem_gedit_count (A := 2) (η := 1 - (b + 1 / (2 * A))) (by norm_num)
      (by linarith [h.half_lt_b])
      (fun k hk => h.abs_sparseTarget_le hk) (by linarith) hβ1,
    htwin, hfake⟩

/-- **A fake with a prescribed sparse configuration.**  If `ζ` does not vanish at one point of
the configuration, the edit is an integer-norm fake. -/
theorem exists_isEdit_fake_sparse (h : IsSparseConfig ρ b A)
    (hζ : ∃ j, riemannZeta (ρ j) ≠ 0) {β : ℝ} (hβ : b + 1 / (2 * A) < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧ IsIntegerNormFakeAt (editSystem e) β ∧
      IsFactorTwin (editSystem e) (sparseFactor ρ) ∧
      HasFakeZeroSet (editSystem e) {z : ℂ | ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  obtain ⟨j₀, hζ₀⟩ := hζ
  obtain ⟨e, he, hcount, htwin, hfake⟩ := h.exists_isEdit_sparseTwin hβ hβ1
  obtain ⟨G, hG, hGF, hzero⟩ := hfake
  have hρ₀ne : ρ j₀ ≠ 1 := fun h1 => by
    have h2 := h.le j₀
    rw [h1, Complex.one_re] at h2
    linarith [h.b_lt]
  have hGz : G (ρ j₀) = 0 := (hzero (ρ j₀) (h.half j₀) hρ₀ne hζ₀).mpr ⟨j₀, Or.inl rfl⟩
  obtain ⟨k, hk⟩ := exists_ne_zero_of_fake_zero he hG hGF (h.half j₀) hρ₀ne hζ₀ hGz
  exact ⟨e, he, ⟨hasIntegerNorms_editSystem _, isDiscrete_editSystem _,
    notNormEquivPrimes_editSystem he hk, hcount, G, hG, hGF, ρ j₀, h.half j₀, hρ₀ne, hGz, hζ₀⟩,
    htwin, ⟨G, hG, hGF, hzero⟩⟩

end IsSparseConfig

/-! ## Two instances -/

/-- The points `σ + i (j+1)^A` of the vertical line `Re s = σ`. -/
def linePoints (σ A : ℝ) (j : ℕ) : ℂ := ⟨σ, ((j : ℝ) + 1) ^ A⟩

/-- Points whose real parts `σ − (σ − 1/2)/(j+2)` increase to `σ`, at the heights `(j+1)^A`. -/
def risingPoints (σ A : ℝ) (j : ℕ) : ℂ := ⟨σ - (σ - 1 / 2) / ((j : ℝ) + 2), ((j : ℝ) + 1) ^ A⟩

theorem isSparseConfig_linePoints {σ A : ℝ} (hσ : 1 / 2 < σ) (hA : 0 < A)
    (hroom : σ + 1 / (2 * A) < 14 / 15) : IsSparseConfig (linePoints σ A) σ A where
  half _ := hσ
  le _ := le_rfl
  pos := hA
  room := hroom
  height j := by
    show ((j : ℝ) + 1) ^ A ≤ |((j : ℝ) + 1) ^ A|
    exact le_abs_self _

theorem risingPoints_re_lt {σ : ℝ} (hσ : 1 / 2 < σ) (A : ℝ) (j : ℕ) :
    (risingPoints σ A j).re < σ := by
  show σ - (σ - 1 / 2) / ((j : ℝ) + 2) < σ
  have h1 : 0 < (σ - 1 / 2) / ((j : ℝ) + 2) := div_pos (by linarith) (by positivity)
  linarith

/-- The real parts of the rising points come arbitrarily close to `σ`. -/
theorem exists_risingPoints_re_gt (σ A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, σ - ε < (risingPoints σ A j).re := by
  obtain ⟨j, hj⟩ := exists_nat_gt ((σ - 1 / 2) / ε)
  refine ⟨j, ?_⟩
  show σ - ε < σ - (σ - 1 / 2) / ((j : ℝ) + 2)
  have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have h1 : (σ - 1 / 2) / ((j : ℝ) + 2) < ε := by
    rw [div_lt_iff₀ hj2]
    rw [div_lt_iff₀ hε] at hj
    nlinarith
  linarith

theorem isSparseConfig_risingPoints {σ A : ℝ} (hσ : 1 / 2 < σ) (hA : 0 < A)
    (hroom : σ + 1 / (2 * A) < 14 / 15) : IsSparseConfig (risingPoints σ A) σ A where
  half j := by
    show 1 / 2 < σ - (σ - 1 / 2) / ((j : ℝ) + 2)
    have h1 : (σ - 1 / 2) / ((j : ℝ) + 2) < σ - 1 / 2 :=
      div_lt_self (by linarith) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    linarith
  le j := (risingPoints_re_lt hσ A j).le
  pos := hA
  room := hroom
  height j := by
    show ((j : ℝ) + 1) ^ A ≤ |((j : ℝ) + 1) ^ A|
    exact le_abs_self _

/-- **Infinitely many fake zeros on one vertical line.**  For `1/2 < σ`, `σ + 1/(2A) < 14/15`
and `β ∈ (σ + 1/(2A), 1)` there is a two-sided edit of the rational primes with count
`A′ x + O(x^β)` whose fake zeros right of the line are exactly the points `σ ± i (j+1)^A`. -/
theorem exists_isEdit_zeros_on_a_vertical_line {σ A : ℝ} (hσ : 1 / 2 < σ) (hA : 0 < A)
    (hroom : σ + 1 / (2 * A) < 14 / 15) {β : ℝ} (hβ : σ + 1 / (2 * A) < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A' C : ℝ, 0 ≤ A' ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A' * x| ≤ C * x ^ β) ∧
      HasFakeZeroSet (editSystem e)
        {z : ℂ | ∃ j, z = linePoints σ A j ∨ z = (starRingEnd ℂ) (linePoints σ A j)} := by
  obtain ⟨e, he, hcount, -, hfake⟩ :=
    (isSparseConfig_linePoints hσ hA hroom).exists_isEdit_sparseTwin hβ hβ1
  exact ⟨e, he, hcount, hfake⟩

/-- **Fake zeros that rise to a line without reaching it.**  The fake zeros right of the line
are exactly the points `risingPoints σ A j` and their conjugates: their real parts are below `σ`
and come arbitrarily close to it (`risingPoints_re_lt`, `exists_risingPoints_re_gt`). -/
theorem exists_isEdit_zeros_rising_to_a_line {σ A : ℝ} (hσ : 1 / 2 < σ) (hA : 0 < A)
    (hroom : σ + 1 / (2 * A) < 14 / 15) {β : ℝ} (hβ : σ + 1 / (2 * A) < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A' C : ℝ, 0 ≤ A' ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A' * x| ≤ C * x ^ β) ∧
      HasFakeZeroSet (editSystem e)
        {z : ℂ | ∃ j, z = risingPoints σ A j ∨ z = (starRingEnd ℂ) (risingPoints σ A j)} := by
  obtain ⟨e, he, hcount, -, hfake⟩ :=
    (isSparseConfig_risingPoints hσ hA hroom).exists_isEdit_sparseTwin hβ hβ1
  exact ⟨e, he, hcount, hfake⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
