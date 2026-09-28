import GaloisForLFunctions.RHTower.ChronologicalTailRiemann
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.Chebyshev

/-!
# The half-tail Gram form of the fixed-order moment system

For `m ≥ 0` index the moment exponents `-1, 0, 1, 3, …, 2m - 1` by `Fin (m + 2)` and put
`v_i(x) = x^{e_i}`.  On `[1/2, 1]`:

* the limiting Gram form `Q(c) = ∫_{1/2}^1 (Σ cᵢ vᵢ)²` is positive definite: `x Σ cᵢ vᵢ(x)` is a
  polynomial with the distinct exponents `0, 1, 2, 4, …, 2m`, so it cannot vanish on `[1/2, 1]`
  unless `c = 0`; compactness of the unit sphere gives `Q(c) ≥ λ Σ cᵢ²` with `λ > 0`;
* the scaled discrete forms `Q_N(c) = N⁻¹ Σ_{N/2 < k ≤ N} (Σ cᵢ vᵢ(k/N))²` differ from `Q` entrywise
  by `O(1/N)` (first-order Riemann sums), hence `Q_N(c) ≥ (λ/2) Σ cᵢ²` for all large `N`.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace RHTower

/-! ### Exponents -/

/-- The moment exponents `-1, 0, 1, 3, …, 2m - 1`. -/
def gmExp (m : ℕ) (i : Fin (m + 2)) : ℤ :=
  if (i : ℕ) = 0 then -1 else if (i : ℕ) = 1 then 0 else 2 * (i : ℕ) - 3

/-- The shifted degrees `e_i + 1 = 0, 1, 2, 4, …, 2m`. -/
def gmDeg (m : ℕ) (i : Fin (m + 2)) : ℕ :=
  if (i : ℕ) = 0 then 0 else if (i : ℕ) = 1 then 1 else 2 * (i : ℕ) - 2

theorem gmDeg_cast (m : ℕ) (i : Fin (m + 2)) : (gmDeg m i : ℤ) = gmExp m i + 1 := by
  unfold gmDeg gmExp
  split_ifs with h0 h1
  · simp
  · simp
  · push_cast [show 2 ≤ 2 * (i : ℕ) by omega]; ring

theorem gmDeg_injective (m : ℕ) : Function.Injective (gmDeg m) := by
  intro i j h
  apply Fin.ext
  unfold gmDeg at h
  split_ifs at h <;> omega

theorem gmExp_ge (m : ℕ) (i : Fin (m + 2)) : -1 ≤ gmExp m i := by
  have := gmDeg_cast m i; omega

/-- On positive reals, `x^{deg_i} = x · x^{e_i}`. -/
theorem pow_gmDeg (m : ℕ) (i : Fin (m + 2)) {x : ℝ} (hx : x ≠ 0) :
    x ^ gmDeg m i = x * x ^ gmExp m i := by
  rw [← zpow_natCast, gmDeg_cast, zpow_add_one₀ hx, mul_comm]

/-! ### Smoothness of monomials on `[θ, 1]` -/

theorem contDiffOn_zpow_of_pos {θ : ℝ} (hθ0 : 0 < θ) (p : ℤ) :
    ContDiffOn ℝ 1 (fun x : ℝ => x ^ p) (Icc θ 1) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg p
  · simp only [zpow_natCast]
    exact (contDiff_id.pow n).contDiffOn
  · simp only [zpow_neg, zpow_natCast]
    exact (contDiff_id.pow n).contDiffOn.inv fun x hx => pow_ne_zero _ (hθ0.trans_le hx.1).ne'

/-! ### Real Riemann sums over the proportional tail -/

/-- **Real tail Riemann estimate.** -/
theorem abs_tailSampleSum_real_sub_integral_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {φ : ℝ → ℝ} {M L : ℝ} (hM : ∀ x ∈ Icc θ 1, |φ x| ≤ M)
    (hL : ∀ x ∈ Icc θ 1, ∀ y ∈ Icc θ 1, |φ x - φ y| ≤ L * |x - y|)
    (hint : IntervalIntegrable φ volume θ 1) {N : ℕ} (hN : 0 < N) :
    |(1 / (N : ℝ)) * ∑ k ∈ Finset.Ioc 0 N, (if θ * N < k then φ (k / N) else 0) -
        ∫ x in θ..1, φ x| ≤ (M + L) / N := by
  have h := norm_tailSampleSum_sub_integral_le hθ0 hθ1 (φ := fun x => (φ x : ℂ))
    (fun x hx => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM x hx)
    (fun x hx y hy => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hL x hx y hy)
    ⟨hint.1.ofReal, hint.2.ofReal⟩ hN
  have hsum : tailSampleSum θ N (fun x => (φ x : ℂ)) =
      ((∑ k ∈ Finset.Ioc 0 N, (if θ * N < k then φ (k / N) else 0) : ℝ) : ℂ) := by
    rw [tailSampleSum]; push_cast
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  rw [hsum, intervalIntegral.integral_ofReal, show (1 / (N : ℂ)) = ((1 / (N : ℝ) : ℝ) : ℂ) by
    push_cast; rfl, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

/-- The tail condition `θN < k` at `θ = 1/2` is `⌊N/2⌋ < k`. -/
theorem half_mul_lt_iff (N k : ℕ) : (1 / 2 : ℝ) * N < k ↔ N / 2 < k := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  constructor
  · intro h; exact_mod_cast (by linarith : (N : ℝ) < k * 2)
  · intro h; have : (N : ℝ) < k * 2 := by exact_mod_cast h
    linarith

/-- **Monomial tail sums.** For every exponent `p`, the scaled half-tail sum of `x^p` converges to
`∫_{1/2}^1 x^p` at rate `1/N`. -/
theorem exists_abs_halfTailSum_zpow_sub_le (p : ℤ) :
    ∃ C : ℝ, ∀ N : ℕ, 0 < N →
      |(1 / (N : ℝ)) * ∑ k ∈ Finset.Ioc 0 N, (if N / 2 < k then ((k : ℝ) / N) ^ p else 0) -
        ∫ x in (1 / 2 : ℝ)..1, x ^ p| ≤ C / N := by
  have hθ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hcd := contDiffOn_zpow_of_pos hθ0 p
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcd.continuousOn
  refine ⟨B + K, fun N hN => ?_⟩
  have h := abs_tailSampleSum_real_sub_integral_le hθ0 (by norm_num) (φ := fun x => x ^ p)
    (M := B) (L := K) (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)
    (fun x hx y hy => by simpa [Real.dist_eq] using hK.dist_le_mul x hx y hy)
    (hcd.continuousOn.intervalIntegrable_of_Icc (by norm_num)) hN
  refine (le_of_eq ?_).trans h
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [half_mul_lt_iff]

/-! ### Positive definiteness of the limit form -/

theorem integral_sq_pos_of_ne_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hne : f x₀ ≠ 0) :
    0 < ∫ x in a..b, f x ^ 2 := by
  have hint : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab.le
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (Eventually.of_forall fun x => sq_nonneg (f x)) hint]
  refine ⟨hab, ?_⟩
  obtain ⟨V, hVo, hxV, hVsub⟩ := mem_nhdsWithin.mp ((hf x₀ hx₀).eventually_ne hne)
  have hne' : (V ∩ Ioo a b).Nonempty := by
    have hcl : x₀ ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hx₀
    exact (mem_closure_iff.mp hcl) V hVo hxV
  refine lt_of_lt_of_le ((hVo.inter isOpen_Ioo).measure_pos volume hne') (measure_mono ?_)
  rintro x ⟨hxV', hxI⟩
  refine ⟨?_, hxI.1, hxI.2.le⟩
  exact pow_ne_zero 2 (hVsub ⟨hxV', hxI.1.le, hxI.2.le⟩)

/-- A combination of the moment monomials vanishing on `[1/2, 1]` has zero coefficients. -/
theorem eq_zero_of_gm_eqOn_zero {m : ℕ} {c : Fin (m + 2) → ℝ}
    (h : ∀ x ∈ Icc (1 / 2 : ℝ) 1, ∑ i, c i * x ^ gmExp m i = 0) : c = 0 := by
  classical
  set P : Polynomial ℝ := ∑ i, Polynomial.C (c i) * Polynomial.X ^ gmDeg m i with hP
  have hroot : ∀ x ∈ Icc (1 / 2 : ℝ) 1, P.IsRoot x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    rw [Polynomial.IsRoot, hP, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    calc ∑ i, c i * x ^ gmDeg m i = x * ∑ i, c i * x ^ gmExp m i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [pow_gmDeg m i hx0]; ring
      _ = 0 := by rw [h x hx, mul_zero]
  have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P
    ((Set.Icc_infinite (by norm_num : (1 / 2 : ℝ) < 1)).mono fun x hx => hroot x hx)
  funext i
  have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff (gmDeg m i)) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (gmDeg_injective m h.symm))
    (fun h => absurd (Finset.mem_univ i) h), if_pos rfl] at hcoeff
  exact hcoeff

/-- The limiting Gram entries `∫_{1/2}^1 x^{e_i + e_j}`. -/
def gmGramLim (m : ℕ) (i j : Fin (m + 2)) : ℝ := ∫ x in (1 / 2 : ℝ)..1, x ^ (gmExp m i + gmExp m j)

/-- The scaled discrete Gram entries `N⁻¹ Σ_{N/2 < k ≤ N} (k/N)^{e_i + e_j}`. -/
def gmGramDisc (m N : ℕ) (i j : Fin (m + 2)) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.Ioc 0 N,
    (if N / 2 < k then ((k : ℝ) / N) ^ (gmExp m i + gmExp m j) else 0)

/-- The quadratic form of a symmetric coefficient array. -/
def quadForm {n : ℕ} (G : Fin n → Fin n → ℝ) (c : Fin n → ℝ) : ℝ := ∑ i, ∑ j, c i * c j * G i j

theorem continuous_quadForm {n : ℕ} (G : Fin n → Fin n → ℝ) : Continuous (quadForm G) := by
  unfold quadForm
  fun_prop

theorem quadForm_smul {n : ℕ} (G : Fin n → Fin n → ℝ) (r : ℝ) (c : Fin n → ℝ) :
    quadForm G (r • c) = r ^ 2 * quadForm G c := by
  unfold quadForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- `Q(c) = ∫_{1/2}^1 (Σ cᵢ vᵢ)²`. -/
theorem quadForm_gmGramLim (m : ℕ) (c : Fin (m + 2) → ℝ) :
    quadForm (gmGramLim m) c = ∫ x in (1 / 2 : ℝ)..1, (∑ i, c i * x ^ gmExp m i) ^ 2 := by
  have hcont : ∀ p : ℤ, IntervalIntegrable (fun x : ℝ => x ^ p) volume (1 / 2) 1 := fun p =>
    (contDiffOn_zpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2) p).continuousOn.intervalIntegrable_of_Icc
      (by norm_num)
  have hpt : ∀ x ∈ uIcc (1 / 2 : ℝ) 1, (∑ i, c i * x ^ gmExp m i) ^ 2 =
      ∑ i, ∑ j, c i * c j * x ^ (gmExp m i + gmExp m j) := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [zpow_add₀ hx0]; ring
  have hij : ∀ i j, IntervalIntegrable
      (fun x : ℝ => c i * c j * x ^ (gmExp m i + gmExp m j)) volume (1 / 2) 1 :=
    fun i j => (hcont _).const_mul _
  have hi : ∀ i, IntervalIntegrable
      (fun x : ℝ => ∑ j, c i * c j * x ^ (gmExp m i + gmExp m j)) volume (1 / 2) 1 := fun i => by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ fun j _ => hij i j
  symm
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finsetSum fun i _ => hi i]
  unfold quadForm gmGramLim
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => hij i j]
  exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _

theorem quadForm_gmGramLim_pos (m : ℕ) {c : Fin (m + 2) → ℝ} (hc : c ≠ 0) :
    0 < quadForm (gmGramLim m) c := by
  rw [quadForm_gmGramLim]
  by_contra hle
  push Not at hle
  apply hc
  apply eq_zero_of_gm_eqOn_zero
  intro x₀ hx₀
  by_contra hne
  exact absurd hle (not_le.mpr (integral_sq_pos_of_ne_zero (by norm_num)
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
      (contDiffOn_zpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2) _).continuousOn) hx₀ hne))

/-- **A positive definite quadratic form dominates a multiple of the squared norm.** -/
theorem exists_quadForm_lower {n : ℕ} (G : Fin n → Fin n → ℝ)
    (hpos : ∀ c : Fin n → ℝ, c ≠ 0 → 0 < quadForm G c) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ c : Fin n → ℝ, lam * ∑ i, c i ^ 2 ≤ quadForm G c := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun c => by simp [quadForm]⟩
  set S : Set (Fin n → ℝ) := {c | ∑ i, c i ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq (by fun_prop) continuous_const) ?_
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun c hc => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_one]
    refine Real.sqrt_le_sqrt ?_
    rw [← show ∑ i, c i ^ 2 = 1 from hc]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
  have hSne : S.Nonempty := ⟨Pi.single ⟨0, hn⟩ 1, by
    simp [hS, Pi.single_apply, Finset.sum_ite_eq']⟩
  obtain ⟨c₀, hc₀S, hmin⟩ := hSc.exists_isMinOn hSne (continuous_quadForm G).continuousOn
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    simp [hS] at hc₀S
  refine ⟨quadForm G c₀, hpos c₀ hc₀, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc; simp [quadForm]
  set r := Real.sqrt (∑ i, c i ^ 2) with hr
  have hsum_pos : 0 < ∑ i, c i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    have hi' : c i ≠ 0 := hi
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun j _ => sq_nonneg (c j))
      (Finset.mem_univ i))
  have hr0 : 0 < r := Real.sqrt_pos.mpr hsum_pos
  have hmem : r⁻¹ • c ∈ S := by
    simp only [hS, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, inv_pow, hr, Real.sq_sqrt hsum_pos.le, inv_mul_cancel₀ hsum_pos.ne']
  have hle := hmin hmem
  simp only [Set.mem_setOf_eq] at hle
  rw [quadForm_smul, inv_pow, hr, Real.sq_sqrt hsum_pos.le] at hle
  rw [mul_comm]
  calc (∑ i, c i ^ 2) * quadForm G c₀ ≤ (∑ i, c i ^ 2) * ((∑ i, c i ^ 2)⁻¹ * quadForm G c) :=
        mul_le_mul_of_nonneg_left hle hsum_pos.le
    _ = quadForm G c := by field_simp

/-- **Discrete coercivity of the half-tail Gram form.** -/
theorem exists_gmGramDisc_coercive (m : ℕ) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ c : Fin (m + 2) → ℝ,
      lam * ∑ i, c i ^ 2 ≤ quadForm (gmGramDisc m N) c := by
  obtain ⟨lam, hlam, hQ⟩ := exists_quadForm_lower (gmGramLim m) fun c hc =>
    quadForm_gmGramLim_pos m hc
  choose C hC using fun (ij : Fin (m + 2) × Fin (m + 2)) =>
    exists_abs_halfTailSum_zpow_sub_le (gmExp m ij.1 + gmExp m ij.2)
  set K : ℝ := ∑ ij, |C ij| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCle : ∀ ij, C ij ≤ K := fun ij => (le_abs_self _).trans
    (Finset.single_le_sum (fun kl _ => abs_nonneg (C kl)) (Finset.mem_univ ij))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * (m + 2) * K / lam)
  refine ⟨lam / 2, by positivity, N₁ + 1, fun N hN c => ?_⟩
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNbig : 2 * (m + 2) * K / lam < N := hN₁.trans (by exact_mod_cast (by omega : N₁ < N))
  have hentry : ∀ i j, |gmGramDisc m N i j - gmGramLim m i j| ≤ K / N := fun i j =>
    (hC (i, j) N hNpos).trans (div_le_div_of_nonneg_right (hCle (i, j)) hNr.le)
  have hdiff : |quadForm (gmGramDisc m N) c - quadForm (gmGramLim m) c| ≤
      (m + 2) * (∑ i, c i ^ 2) * (K / N) := by
    have hrw : quadForm (gmGramDisc m N) c - quadForm (gmGramLim m) c =
        ∑ i, ∑ j, c i * c j * (gmGramDisc m N i j - gmGramLim m i j) := by
      unfold quadForm
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrw]
    calc |∑ i, ∑ j, c i * c j * (gmGramDisc m N i j - gmGramLim m i j)|
        ≤ ∑ i, ∑ j, |c i| * |c j| * (K / N) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hentry i j) (by positivity)
      _ = (∑ i, |c i|) ^ 2 * (K / N) := by
          rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
      _ ≤ (m + 2) * (∑ i, c i ^ 2) * (K / N) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin (m + 2) => |c i|)
          simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at this
          exact_mod_cast this
  have hsmall : (m + 2) * (∑ i, c i ^ 2) * (K / N) ≤ lam / 2 * ∑ i, c i ^ 2 := by
    have hS0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : (m + 2 : ℝ) * (K / N) ≤ lam / 2 := by
      rw [div_lt_iff₀ hlam] at hNbig
      rw [mul_div_assoc', div_le_iff₀ hNr]
      nlinarith
    nlinarith
  have hlow := hQ c
  have habs := (abs_le.mp hdiff).1
  linarith

end RHTower
