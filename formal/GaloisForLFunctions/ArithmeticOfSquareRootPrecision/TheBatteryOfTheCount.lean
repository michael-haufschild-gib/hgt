import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheCountIsTheRiemannHypothesis
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# The battery of the count

Which moves of the weight does the square-root count see? All statements are unconditional.

**Visible moves** (the moved weight never satisfies the count):
* every mixture `(1 − t) Λ + t λΛ` with the Liouville twin, `t ≠ 0`; in particular `λΛ` itself
  (`not_count_liouvilleMixture`, `not_count_liouvilleWeight`). The partial sums are
  `(1 − 2t) ψ(x) + O(√x)`, a multiple of `ψ` other than `ψ`;
* every scaling `c Λ`, `c ≠ 1` (`not_count_smul_vonMangoldt`), by the prime number theorem;
* every cofinite flip: a weight that agrees with `λΛ` beyond some point
  (`not_count_of_eventually_eq_liouvilleWeight`);
* `Λ + ε n^{−η}` for `ε ≠ 0`, `0 ≤ η < ½` (`not_count_vonMangoldt_add_smul_powerWeight`). This
  is unconditional: the count would make `ψ(x) − x` eventually one-signed of size `x^{1−η}`,
  against Littlewood's oscillation.

**Invisible moves** (the count holds after the move iff it holds before, i.e. iff RH):
* finite modifications (`count_congr_of_eventually_eq`);
* deleting or rescaling the Euler factor at a prime, `Λ + c Λ·1_{p^ℕ}`, including the flip
  `c = −2` (`count_vonMangoldt_add_smul_towerWeight_iff`): a prime tower carries `≤ log x` of
  partial sum;
* `Λ + ε n^{−η}` for `η ≥ ½`.

So the count selects `Λ` only modulo the square-root class: it is a tail statement, blind to every
finite set of Euler factors (`battery_classification`).
-/

noncomputable section

open Filter Asymptotics Real Finset RHTower
open ArithmeticFunction (vonMangoldt cardFactors)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- Adding an element of `𝒬` does not change whether the count holds. -/
theorem count_add_iff_of_mem_sqrtClass {a δ : ℕ → ℝ} (hδ : δ ∈ sqrtClass) :
    Count (a + δ) ↔ Count a := by
  refine ⟨fun h => ?_, fun h => (count_add_iff_mem_sqrtClass h δ).mpr hδ⟩
  have := (count_add_iff_mem_sqrtClass h ((-1 : ℝ) • δ)).mpr (PrecisionClass.smul_mem _ hδ)
  simpa using this

/-! ### Linear deviations -/

/-- `√x log² x = o(x)`. -/
theorem sqrtScale_isLittleO_id : sqrtScale =o[atTop] fun x => x := by
  have h := sqrtScale_isLittleO_rpow (η := 0) (by norm_num)
  simpa using h

/-- A deviation of linear size excludes the count. -/
theorem not_count_of_linear_deviation {a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ x in atTop, c * x ≤ |partialSum a x - x|) : ¬ Count a := by
  intro hC
  have ho := (hC : _ =O[atTop] sqrtScale).trans_isLittleO sqrtScale_isLittleO_id
  obtain ⟨x, ⟨h1, h2⟩, hx⟩ := ((h.and (ho.def (half_pos hc))).and (eventually_gt_atTop 0)).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx] at h2
  nlinarith

/-- The prime number theorem as `|ψ(x) − x| ≤ ε x` eventually. -/
theorem eventually_abs_psi_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, |Chebyshev.psi x - x| ≤ ε * x := by
  have h := tendsto_chebyshevPsiReal_div.eventually (Metric.closedBall_mem_nhds 1 hε)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [Real.dist_eq, chebyshevPsiReal_eq_psi] at hx
  have he : Chebyshev.psi x - x = x * (Chebyshev.psi x / x - 1) := by field_simp
  rw [he, abs_mul, abs_of_pos hx0]
  nlinarith

/-- **Multiples of `ψ` are visible.** If `A(x) = κ ψ(x) + o(x)` with `κ ≠ 1`, the count fails. -/
theorem not_count_of_isLittleO_sub_smul_psi {a : ℕ → ℝ} {κ : ℝ} (hκ : κ ≠ 1)
    (h : (fun x => partialSum a x - κ * Chebyshev.psi x) =o[atTop] fun x => x) : ¬ Count a := by
  have hd : 0 < |κ - 1| := abs_pos.mpr (sub_ne_zero.mpr hκ)
  refine not_count_of_linear_deviation (c := |κ - 1| / 2) (by positivity) ?_
  filter_upwards [h.def (c := |κ - 1| / 4) (by positivity),
    eventually_abs_psi_sub_le (ε := |κ - 1| / (4 * (|κ| + 1))) (by positivity),
    eventually_gt_atTop (0 : ℝ)] with x h1 h2 hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx] at h1
  have hsplit : partialSum a x - x =
      (κ - 1) * x + κ * (Chebyshev.psi x - x) + (partialSum a x - κ * Chebyshev.psi x) := by ring
  have h3 : |κ * (Chebyshev.psi x - x)| ≤ |κ - 1| / 4 * x := by
    rw [abs_mul]
    calc |κ| * |Chebyshev.psi x - x| ≤ |κ| * (|κ - 1| / (4 * (|κ| + 1)) * x) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg κ)
      _ ≤ |κ - 1| / 4 * x := by
          rw [show |κ| * (|κ - 1| / (4 * (|κ| + 1)) * x) =
            (|κ| / (|κ| + 1)) * (|κ - 1| / 4 * x) by field_simp]
          exact mul_le_of_le_one_left (by positivity)
            ((div_le_one (by positivity)).mpr (by linarith))
  have h4 : |(κ - 1) * x| = |κ - 1| * x := by rw [abs_mul, abs_of_pos hx]
  have e1 := abs_sub (partialSum a x - x - κ * (Chebyshev.psi x - x))
    (partialSum a x - κ * Chebyshev.psi x)
  have e2 := abs_sub (partialSum a x - x) (κ * (Chebyshev.psi x - x))
  rw [show partialSum a x - x - κ * (Chebyshev.psi x - x) - (partialSum a x - κ * Chebyshev.psi x)
    = (κ - 1) * x by ring, h4] at e1
  linarith

/-! ### Scalings -/

/-- **Scalings are visible**: `c Λ` with `c ≠ 1` never satisfies the count. -/
theorem not_count_smul_vonMangoldt {c : ℝ} (hc : c ≠ 1) : ¬ Count (c • vonMangoldtWeight) := by
  refine not_count_of_isLittleO_sub_smul_psi hc ?_
  simp only [partialSum_smul, partialSum_vonMangoldt, sub_self]
  exact isLittleO_zero _ _

/-! ### The Liouville twin and its mixtures -/

/-- The **Liouville twin** `λΛ`: `(−1)^{Ω(n)} Λ(n)`, equal to `(−1)^k log p` at `p^k`. -/
def liouvilleWeight (n : ℕ) : ℝ := (-1) ^ (cardFactors n) * vonMangoldt n

/-- `0 ≤ λΛ(n) + Λ(n) ≤ 2Λ(n)`, with `λΛ(p) + Λ(p) = 0` at primes. -/
theorem liouvilleWeight_add_vonMangoldt_le (n : ℕ) :
    0 ≤ liouvilleWeight n + vonMangoldt n ∧
      liouvilleWeight n + vonMangoldt n ≤ 2 * (if n.Prime then 0 else vonMangoldt n) := by
  have h0 : (0 : ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  unfold liouvilleWeight
  rcases neg_one_pow_eq_or ℝ (cardFactors n) with h | h <;> rw [h] <;> split_ifs with hp
  · rw [ArithmeticFunction.cardFactors_apply_prime hp] at h; norm_num at h
  · constructor <;> linarith
  · constructor <;> simp
  · constructor <;> linarith

/-- The Liouville twin's partial sums are `−ψ(x) + O(ψ − θ)`. -/
theorem partialSum_liouvilleWeight_add_psi (x : ℝ) :
    0 ≤ partialSum liouvilleWeight x + Chebyshev.psi x ∧
      partialSum liouvilleWeight x + Chebyshev.psi x ≤
        2 * (Chebyshev.psi x - Chebyshev.theta x) := by
  have hsum : partialSum liouvilleWeight x + Chebyshev.psi x =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (liouvilleWeight n + vonMangoldt n) := by
    rw [sum_add_distrib]; rfl
  rw [hsum, Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter, mul_sum]
  exact ⟨sum_nonneg fun n _ => (liouvilleWeight_add_vonMangoldt_le n).1,
    sum_le_sum fun n _ => by
      have := (liouvilleWeight_add_vonMangoldt_le n).2
      split_ifs at this ⊢ with hp <;> simpa [hp] using this⟩

/-- `ψ − θ = o(x)`. -/
theorem psi_sub_theta_isLittleO :
    (fun x => Chebyshev.psi x - Chebyshev.theta x) =o[atTop] fun x => x := by
  have h1 := Chebyshev.isBigO_psi_sub_theta_sqrt
  have h2 : (fun x : ℝ => √x) =O[atTop] sqrtScale := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg x), Real.norm_of_nonneg (sqrtScale_nonneg x),
      one_mul]
    exact sqrt_le_sqrtScale hx
  exact h1.trans_isLittleO (h2.trans_isLittleO sqrtScale_isLittleO_id)

/-- The Liouville mixture `(1 − t) Λ + t λΛ`. -/
def liouvilleMixture (t : ℝ) : ℕ → ℝ := (1 - t) • vonMangoldtWeight + t • liouvilleWeight

/-- **Liouville mixtures are visible**: for `t ≠ 0`, `(1 − t) Λ + t λΛ` never satisfies the count.
Its partial sums are `(1 − 2t) ψ(x) + t (A_λ(x) + ψ(x))`, and `0 ≤ A_λ + ψ ≤ 2(ψ − θ) = o(x)`. -/
theorem not_count_liouvilleMixture {t : ℝ} (ht : t ≠ 0) : ¬ Count (liouvilleMixture t) := by
  refine not_count_of_isLittleO_sub_smul_psi (κ := 1 - 2 * t) (by
    intro h; exact ht (by linarith)) ?_
  have hE : (fun x => partialSum liouvilleWeight x + Chebyshev.psi x) =o[atTop] fun x => x := by
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 2 ?_) psi_sub_theta_isLittleO
    filter_upwards with x
    obtain ⟨h1, h2⟩ := partialSum_liouvilleWeight_add_psi x
    rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg (by linarith)]
    exact h2
  refine (hE.const_mul_left t).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [liouvilleMixture, partialSum_add, partialSum_smul, partialSum_vonMangoldt]
  ring

/-- **The Liouville twin is visible**: `λΛ` never satisfies the count. -/
theorem not_count_liouvilleWeight : ¬ Count liouvilleWeight := by
  have h := not_count_liouvilleMixture (t := 1) one_ne_zero
  simpa [liouvilleMixture] using h

/-! ### Finite modifications and cofinite flips -/

/-- **Finite modifications are invisible**: weights that agree beyond some point satisfy the count
together. -/
theorem count_congr_of_eventually_eq {a b : ℕ → ℝ} {N : ℕ} (h : ∀ n, N < n → a n = b n) :
    Count a ↔ Count b := by
  have hmem : ∀ {u v : ℕ → ℝ}, (∀ n, N < n → u n = v n) → v - u ∈ sqrtClass := fun huv =>
    mem_sqrtClass_of_eventually_zero (N := N) fun n hn => by simp [huv n hn]
  constructor
  · intro ha
    simpa using (count_add_iff_mem_sqrtClass ha (b - a)).mpr (hmem h)
  · intro hb
    simpa using (count_add_iff_mem_sqrtClass hb (a - b)).mpr (hmem fun n hn => (h n hn).symm)

/-- **Cofinite flips are visible**: a weight agreeing with `λΛ` beyond some point never satisfies
the count. -/
theorem not_count_of_eventually_eq_liouvilleWeight {b : ℕ → ℝ} {N : ℕ}
    (h : ∀ n, N < n → b n = liouvilleWeight n) : ¬ Count b :=
  fun hb => not_count_liouvilleWeight ((count_congr_of_eventually_eq h).mp hb)

/-! ### Euler factors -/

/-- `n` is a power `p^k`, `k ≥ 1`. -/
def IsTowerPower (p n : ℕ) : Prop := ∃ k ∈ Finset.Icc 1 n, n = p ^ k

instance (p : ℕ) : DecidablePred (IsTowerPower p) := fun n => by
  unfold IsTowerPower; infer_instance

/-- The **Euler factor at `p`** as a weight: `Λ` restricted to the powers `p^k`, `k ≥ 1`. -/
def towerWeight (p n : ℕ) : ℝ := if IsTowerPower p n then vonMangoldt n else 0

/-- **A prime tower carries at most `log x` of partial sum.** -/
theorem partialSum_towerWeight_le {p : ℕ} (hp : p.Prime) (x : ℝ) :
    0 ≤ partialSum (towerWeight p) x ∧ partialSum (towerWeight p) x ≤ Real.log ⌊x⌋₊ := by
  have hnn : ∀ n, 0 ≤ towerWeight p n := fun n => by
    unfold towerWeight; split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  refine ⟨partialSum_nonneg hnn x, ?_⟩
  set N := ⌊x⌋₊
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [partialSum, N, hN]
  have hsub : (Ioc 0 N).filter (IsTowerPower p) ⊆
      (Icc 1 (Nat.log p N)).image (p ^ ·) := by
    intro n hn
    obtain ⟨hn1, k, hk, rfl⟩ := mem_filter.mp hn
    refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨(mem_Icc.mp hk).1, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (mem_Ioc.mp hn1).2
  calc partialSum (towerWeight p) x
      = ∑ n ∈ (Ioc 0 N).filter (IsTowerPower p), vonMangoldt n := by
        rw [sum_filter]; rfl
    _ ≤ ∑ n ∈ (Icc 1 (Nat.log p N)).image (p ^ ·), vonMangoldt n :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ k ∈ Icc 1 (Nat.log p N), vonMangoldt (p ^ k) :=
        sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = (Nat.log p N : ℝ) * Real.log p := by
        rw [sum_congr rfl fun k hk => by
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by have := (mem_Icc.mp hk).1; omega),
            ArithmeticFunction.vonMangoldt_apply_prime hp]]
        simp
    _ = Real.log ((p ^ Nat.log p N : ℕ) : ℝ) := by push_cast; rw [Real.log_pow]
    _ ≤ Real.log N := Real.log_le_log (by have := hp.pos; positivity)
          (by exact_mod_cast Nat.pow_log_le_self p hN.ne')

/-- Rescaled Euler factors lie in the square-root class. -/
theorem smul_towerWeight_mem_sqrtClass {p : ℕ} (hp : p.Prime) (c : ℝ) :
    c • towerWeight p ∈ sqrtClass := by
  refine PrecisionClass.smul_mem c (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  obtain ⟨h0, h1⟩ := partialSum_towerWeight_le hp x
  have hl1 : 1 ≤ Real.log x := by rw [← Real.log_exp 1]; exact Real.log_le_log (exp_pos 1) hx
  have hfl : Real.log ⌊x⌋₊ ≤ Real.log x := by
    have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx1
    exact Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (sqrtScale_nonneg x), one_mul]
  calc partialSum (towerWeight p) x ≤ Real.log x := h1.trans hfl
    _ ≤ Real.log x ^ 2 := by nlinarith
    _ ≤ sqrtScale x := le_mul_of_one_le_left (by positivity) (Real.one_le_sqrt.mpr hx1)

/-- **Euler factors are invisible**: deleting (`c = −1`), flipping (`c = −2`) or rescaling the
Euler factor at a prime does not change whether `Λ` satisfies the count. -/
theorem count_vonMangoldt_add_smul_towerWeight_iff {p : ℕ} (hp : p.Prime) (c : ℝ) :
    Count (vonMangoldtWeight + c • towerWeight p) ↔ RiemannHypothesis := by
  rw [← count_vonMangoldt_iff]
  exact count_add_iff_of_mem_sqrtClass (smul_towerWeight_mem_sqrtClass hp c)

/-! ### Power perturbations of `Λ` -/

/-- `ψ(x) − x` changes sign infinitely often (Littlewood). -/
theorem frequently_psi_sub_pos : ∃ᶠ x in atTop, 0 < Chebyshev.psi x - x := by
  refine (frequently_littlewood_lt_chebyshevPsi_sub.and_eventually
    (tendsto_logLogLog_atTop.eventually_gt_atTop 0 |>.and (eventually_gt_atTop 0))).mono
      fun x ⟨h1, h2, h3⟩ => lt_of_le_of_lt ?_ h1
  have := littlewoodConst_pos
  positivity

theorem frequently_psi_sub_neg : ∃ᶠ x in atTop, Chebyshev.psi x - x < 0 := by
  refine (frequently_chebyshevPsi_sub_lt_littlewood.and_eventually
    (tendsto_logLogLog_atTop.eventually_gt_atTop 0 |>.and (eventually_gt_atTop 0))).mono
      fun x ⟨h1, h2, h3⟩ => lt_of_lt_of_le h1 ?_
  have := littlewoodConst_pos
  have : 0 ≤ littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x)) := by positivity
  linarith

/-- **`Λ + ε n^{−η}` never satisfies the count for `ε ≠ 0`, `0 ≤ η < ½`**, unconditionally. The
count would make `ψ(x) − x = −ε Σ n^{−η} + O(√x log² x)`, eventually of the sign of `−ε`. -/
theorem not_count_vonMangoldt_add_smul_powerWeight {ε η : ℝ} (hε : ε ≠ 0) (hη0 : 0 ≤ η)
    (hη : η < 1 / 2) : ¬ Count (vonMangoldtWeight + ε • powerWeight η) := by
  intro hC
  obtain ⟨C, hC⟩ := isBigO_iff.mp hC
  have ho := ((sqrtScale_isLittleO_rpow hη).const_mul_left C).def
    (c := |ε| / 4) (by positivity)
  have hev : ∀ᶠ x in atTop, |Chebyshev.psi x - x + ε * partialSum (powerWeight η) x| ≤
      |ε| / 4 * x ^ (1 - η) ∧ 1 ≤ x := by
    filter_upwards [hC, ho, eventually_ge_atTop (1 : ℝ)] with x h1 h2 hx
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, partialSum_add, partialSum_smul, partialSum_vonMangoldt,
      Real.norm_of_nonneg (sqrtScale_nonneg x)] at h1
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at h2
    refine ⟨?_, hx⟩
    calc _ = |Chebyshev.psi x + ε * partialSum (powerWeight η) x - x| := by ring_nf
      _ ≤ C * sqrtScale x := h1
      _ ≤ |C * sqrtScale x| := le_abs_self _
      _ ≤ |ε| / 4 * x ^ (1 - η) := h2
  rcases lt_or_gt_of_ne hε with hneg | hpos
  · obtain ⟨x, ⟨h1, hx⟩, h2⟩ := (hev.and_frequently frequently_psi_sub_neg).exists
    have hS := partialSum_powerWeight_ge hη0 hx
    have hxp : 0 < x ^ (1 - η) := Real.rpow_pos_of_pos (by linarith) _
    rw [abs_of_neg hneg] at h1
    have := (abs_le.mp h1).1
    nlinarith
  · obtain ⟨x, ⟨h1, hx⟩, h2⟩ := (hev.and_frequently frequently_psi_sub_pos).exists
    have hS := partialSum_powerWeight_ge hη0 hx
    have hxp : 0 < x ^ (1 - η) := Real.rpow_pos_of_pos (by linarith) _
    rw [abs_of_pos hpos] at h1
    have := (abs_le.mp h1).2
    nlinarith

/-- **The power perturbations of `Λ`**: for `ε ≠ 0`, `η ≥ 0`, the weight `Λ + ε n^{−η}` satisfies
the count iff RH holds and `η ≥ ½`. -/
theorem count_vonMangoldt_add_smul_powerWeight_iff {ε η : ℝ} (hε : ε ≠ 0) (hη0 : 0 ≤ η) :
    Count (vonMangoldtWeight + ε • powerWeight η) ↔ RiemannHypothesis ∧ 1 / 2 ≤ η := by
  constructor
  · intro h
    by_cases hη : 1 / 2 ≤ η
    · exact ⟨count_vonMangoldt_iff.mp
        ((count_add_iff_of_mem_sqrtClass (smul_powerWeight_mem_sqrtClass hη ε)).mp h), hη⟩
    · exact absurd h (not_count_vonMangoldt_add_smul_powerWeight hε hη0 (not_le.mp hη))
  · rintro ⟨hRH, hη⟩
    exact count_add_smul_powerWeight (count_vonMangoldt_iff.mpr hRH) hη ε

/-! ### The classification -/

/-- **The battery of the count.** Unconditionally: mixtures with the Liouville twin, the twin
itself, cofinite flips, scalings and `n^{−η}` perturbations with `η < ½` are visible (never satisfy
the count); finite modifications, rescaled Euler factors and `n^{−η}` perturbations with `η ≥ ½` are
invisible (the moved weight satisfies the count iff RH). -/
theorem battery_classification :
    (∀ t : ℝ, t ≠ 0 → ¬ Count (liouvilleMixture t)) ∧
    ¬ Count liouvilleWeight ∧
    (∀ (b : ℕ → ℝ) (N : ℕ), (∀ n, N < n → b n = liouvilleWeight n) → ¬ Count b) ∧
    (∀ c : ℝ, c ≠ 1 → ¬ Count (c • vonMangoldtWeight)) ∧
    (∀ ε η : ℝ, ε ≠ 0 → 0 ≤ η → η < 1 / 2 → ¬ Count (vonMangoldtWeight + ε • powerWeight η)) ∧
    (∀ (b : ℕ → ℝ) (N : ℕ), (∀ n, N < n → b n = vonMangoldtWeight n) →
      (Count b ↔ RiemannHypothesis)) ∧
    (∀ (p : ℕ) (c : ℝ), p.Prime →
      (Count (vonMangoldtWeight + c • towerWeight p) ↔ RiemannHypothesis)) ∧
    (∀ ε η : ℝ, 1 / 2 ≤ η →
      (Count (vonMangoldtWeight + ε • powerWeight η) ↔ RiemannHypothesis)) :=
  ⟨fun _ ht => not_count_liouvilleMixture ht, not_count_liouvilleWeight,
    fun _ _ h => not_count_of_eventually_eq_liouvilleWeight h,
    fun _ hc => not_count_smul_vonMangoldt hc,
    fun _ _ hε hη0 hη => not_count_vonMangoldt_add_smul_powerWeight hε hη0 hη,
    fun _ _ h => (count_congr_of_eventually_eq h).trans count_vonMangoldt_iff,
    fun _ c hp => count_vonMangoldt_add_smul_towerWeight_iff hp c,
    fun ε _ hη => (count_add_iff_of_mem_sqrtClass (smul_powerWeight_mem_sqrtClass hη ε)).trans
      count_vonMangoldt_iff⟩

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
