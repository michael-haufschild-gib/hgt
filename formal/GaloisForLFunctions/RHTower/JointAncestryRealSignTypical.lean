import GaloisForLFunctions.RHTower.JointAncestryRealAmplitudeVertex
import GaloisForLFunctions.RHTower.JointAncestryRandomPhasePositivity
import GaloisForLFunctions.RHTower.JointAncestryLogBudgetProducer
import GaloisForLFunctions.RHTower.PrimeLagLandauWeights
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# Typical sign patterns are JAS-positive, uniformly in the prime set

For a finite set `P` of primes, a level `σ` and a sign pattern `ε ∈ {±1}^P` (written `ε_S`, `+1` on
`S ⊆ P` and `−1` off `S`) put `K_S(s) = ∏_{p ∈ P} (1 + ε_p p^{−σ} cosh((s − ½) log p))` and
`A_S = Σ_ρ K_S(ρ)/(ρ(1−ρ))`.  Under RH every `A_S` is positive at every level `σ ≥ 0`, and with
zeros approaching the line positivity of all `A_S` at `σ = 1` is RH
(`R:JointAncestryRealAmplitudeVertex`).

**Theorem** (`exists_card_jasRealSign_re_neg_le`).  For every level `σ ≥ 1` and every `ε > 0` there
is `X` such that for **every** finite set `P` of primes `p > X`, at most `ε · 2^{|P|}` sign patterns
give `Re A_S < 0`.  No hypothesis on the zeros is used.

Proof.
* Averaged over the signs, each factor is `1`, so `Σ_S K_S = 2^{|P|}`, and by the parallelogram law
  `Σ_S ‖K_S − 1‖² = 2^{|P|}(∏_P(1 + ‖c_p‖²) − 1)`, `c_p = p^{−σ} cosh((ρ − ½) log p)`
  (`sum_norm_sq_jasRealVecKernel_sign_sub_one`).
* At a zero, `‖c_p‖² ≤ p^{−s_ρ}` with `s_ρ = 2 − 2|Re ρ − ½| > 1` for `σ ≥ 1`.  The Euler product
  gives `∏_P(1 + p^{−s}) ≤ 1 + 1/(s − 1)`, uniformly in `P`; for zeros up to a fixed height the exponent
  is bounded away from `1`, so the product is close to `1` once all primes exceed `X`.
* The zero-free region `|Re ρ − ½| ≤ ½ − 1/(100 log |Im ρ|)` turns `1/(s_ρ − 1)` into
  `50 log |Im ρ|`, and `Σ_ρ |w_ρ| log(2 + |Im ρ|) < ∞` makes the high zeros negligible.  So
  `V = Σ_ρ |w_ρ| (∏_P(1 + p^{−s_ρ}) − 1)` tends to `0` as `X → ∞`, uniformly in `P`
  (`exists_jasSignVariance_le`).
* A negative `Re A_S` needs `‖A_S − Φ(0)‖ ≥ Φ(0)`, `Φ(0) = 2 + γ − log 4π`, and the weighted
  Cauchy–Schwarz inequality bounds the number of such patterns by `2^{|P|} W V/Φ(0)²`,
  `W = Σ_ρ |w_ρ|`.

So the sign patterns that can break positivity form a vanishing proportion of `{±1}^P`, for every
finite large-prime set at once, with no budget restriction.  The level `σ = 1` is the threshold: the
second moments `Σ_p p^{−2σ+2|Re ρ − ½|}` converge for every zero exactly when `σ ≥ 1`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Sign averages of the kernel -/

/-- `(1 + c) + (1 − c) = 2`. -/
theorem jasRealFactor_one_add_neg_one (σ : ℝ) (p : Nat.Primes) (s : ℂ) :
    jasRealFactor σ 1 p s + jasRealFactor σ (-1) p s = 2 := by
  rw [jasRealFactor_eq_affine σ (-1)]
  push_cast
  ring

/-- Expansion of a product of sums over the sign patterns. -/
theorem sum_powerset_prod_sdiff {R : Type*} [CommSemiring R] (P : Finset Nat.Primes)
    (f g : Nat.Primes → R) :
    ∑ S ∈ P.powerset, (∏ p ∈ S, f p) * ∏ p ∈ P \ S, g p = ∏ p ∈ P, (f p + g p) :=
  (Finset.prod_add f g P).symm

/-- **The sign average of the kernel is `1`.** -/
theorem sum_jasRealVecKernel_sign (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    ∑ S ∈ P.powerset, jasRealVecKernel P σ (jasSignVec S) s = 2 ^ P.card := by
  rw [Finset.sum_congr rfl fun S hS => jasRealVecKernel_sign (Finset.mem_powerset.mp hS) σ s,
    sum_powerset_prod_sdiff, Finset.prod_congr rfl fun p _ => jasRealFactor_one_add_neg_one σ p s,
    Finset.prod_const]

/-- `‖1 + c‖² + ‖1 − c‖² = 2(1 + ‖c‖²)` for the two signs. -/
theorem norm_sq_jasRealFactor_one_add_neg_one (σ : ℝ) (p : Nat.Primes) (s : ℂ) :
    ‖jasRealFactor σ 1 p s‖ ^ 2 + ‖jasRealFactor σ (-1) p s‖ ^ 2 =
      2 * (1 + ‖jasRealFactor σ 1 p s - 1‖ ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = jasRealFactor σ 1 p s - 1 := ⟨_, rfl⟩
  have h1 : jasRealFactor σ 1 p s = 1 + c := by rw [hc]; ring
  have h2 : jasRealFactor σ (-1) p s = 1 - c := by
    rw [jasRealFactor_eq_affine σ (-1), hc]; push_cast; ring
  rw [h1, h2, add_sub_cancel_left, parallelogram_law_with_norm ℝ (1 : ℂ) c, norm_one]
  ring

/-- `Σ_S ‖K_S‖² = 2^{|P|} ∏_P (1 + ‖c_p‖²)`. -/
theorem sum_norm_sq_jasRealVecKernel_sign (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    ∑ S ∈ P.powerset, ‖jasRealVecKernel P σ (jasSignVec S) s‖ ^ 2 =
      2 ^ P.card * ∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p s - 1‖ ^ 2) := by
  have e : ∀ S ∈ P.powerset, ‖jasRealVecKernel P σ (jasSignVec S) s‖ ^ 2 =
      (∏ p ∈ S, ‖jasRealFactor σ 1 p s‖ ^ 2) * ∏ p ∈ P \ S, ‖jasRealFactor σ (-1) p s‖ ^ 2 := by
    intro S hS
    rw [jasRealVecKernel_sign (Finset.mem_powerset.mp hS) σ s, norm_mul, norm_prod, norm_prod,
      mul_pow, Finset.prod_pow, Finset.prod_pow]
  rw [Finset.sum_congr rfl e, sum_powerset_prod_sdiff,
    Finset.prod_congr rfl fun p _ => norm_sq_jasRealFactor_one_add_neg_one σ p s,
    Finset.prod_mul_distrib, Finset.prod_const]

theorem norm_sq_sub_one (z : ℂ) : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  ring

/-- **The sign variance of the kernel.**
`Σ_S ‖K_S − 1‖² = 2^{|P|} (∏_P (1 + ‖c_p‖²) − 1)`. -/
theorem sum_norm_sq_jasRealVecKernel_sign_sub_one (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    ∑ S ∈ P.powerset, ‖jasRealVecKernel P σ (jasSignVec S) s - 1‖ ^ 2 =
      2 ^ P.card * ((∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p s - 1‖ ^ 2)) - 1) := by
  rw [Finset.sum_congr rfl fun S _ => norm_sq_sub_one (jasRealVecKernel P σ (jasSignVec S) s),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_norm_sq_jasRealVecKernel_sign,
    ← Finset.mul_sum, ← Complex.re_sum, sum_jasRealVecKernel_sign, Finset.sum_const,
    Finset.card_powerset]
  have e : ((2 : ℂ) ^ P.card).re = (2 : ℝ) ^ P.card := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [e, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-! ## The second moments at a zero -/

/-- The exponent `s_ρ = 2 − 2|Re ρ − ½|` of the second moments; `s_ρ > 1`. -/
def jasSignExponent (q : XiZeroCopy) : ℝ := 2 - 2 * |(q.1 : ℂ).re - 1 / 2|

theorem one_lt_jasSignExponent (q : XiZeroCopy) : 1 < jasSignExponent q := by
  unfold jasSignExponent
  have : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  linarith

/-- At a zero and a level `σ ≥ 1`, `‖c_p‖² ≤ p^{−s_ρ}`. -/
theorem norm_sq_jasRealFactor_sub_one_le {σ : ℝ} (hσ : 1 ≤ σ) (p : Nat.Primes) (q : XiZeroCopy) :
    ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2 ≤ Real.exp (-jasSignExponent q * Real.log p) := by
  have h := norm_jasRealFactor_sub_one_le zero_le_one p (q.1 : ℂ) (σ := σ)
  rw [one_mul] at h
  have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  calc ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2
      ≤ Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Real.exp (-(2 * (σ - |(q.1 : ℂ).re - 1 / 2|)) * Real.log p) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ Real.exp (-jasSignExponent q * Real.log p) := by
        refine Real.exp_le_exp.mpr ?_
        unfold jasSignExponent
        nlinarith

/-! ## The Euler product bound -/

/-- The completely multiplicative function `n ↦ n^{−s}`. -/
def rpowNegHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem exp_neg_mul_log_prime (s : ℝ) (p : Nat.Primes) :
    Real.exp (-s * Real.log p) = rpowNegHom s (p : ℕ) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  show Real.exp (-s * Real.log p) = ((p : ℕ) : ℝ) ^ (-s)
  rw [Real.rpow_def_of_pos hp]
  ring_nf

/-- **Euler product bound.**  `∏_{p ∈ P} (1 + p^{−s}) ≤ 1 + 1/(s − 1)` for `s > 1`. -/
theorem prod_one_add_exp_neg_le {s : ℝ} (hs : 1 < s) (P : Finset Nat.Primes) :
    ∏ p ∈ P, (1 + Real.exp (-s * Real.log p)) ≤ 1 + 1 / (s - 1) := by
  classical
  have hsum : Summable (rpowNegHom s) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hnn : ∀ n : ℕ, 0 ≤ rpowNegHom s n := fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = P.map (Function.Embedding.subtype _) := ⟨_, rfl⟩
  have hTprime : T.filter Nat.Prime = T := by
    rw [Finset.filter_eq_self, hT]
    intro n hn
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hn
    exact p.2
  have heuler := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum T
  rw [hTprime, hT, Finset.prod_map] at heuler
  have hlt : ∀ p : Nat.Primes, rpowNegHom s (p : ℕ) < 1 := fun p => by
    rw [← exp_neg_mul_log_prime, ← Real.exp_zero]
    refine Real.exp_lt_exp.mpr ?_
    have := log_prime_pos p
    nlinarith
  calc ∏ p ∈ P, (1 + Real.exp (-s * Real.log p))
      ≤ ∏ p ∈ P, (1 - rpowNegHom s (p : ℕ))⁻¹ := by
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
        rw [exp_neg_mul_log_prime]
        have h0 := hnn (p : ℕ)
        have h1 := hlt p
        rw [← one_div, le_div_iff₀ (by linarith)]
        nlinarith
    _ = ∑' m : ↥(Nat.factoredNumbers (P.map (Function.Embedding.subtype _))),
          rpowNegHom s (m : ℕ) := heuler
    _ ≤ ∑' n : ℕ, rpowNegHom s n := Summable.tsum_subtype_le (rpowNegHom s) _ hnn hsum
    _ ≤ 1 + 1 / (s - 1) := RHTower.Sieve.tsum_nat_rpow_neg_le hs

/-- **Tail bound.**  For a set of primes `p > X`, `∏_P (1 + p^{−s}) ≤ exp(Σ_{n > X} n^{−s₀})` when
`s ≥ s₀ > 1`. -/
theorem prod_one_add_exp_neg_le_exp_tail {s₀ s : ℝ} (hs₀ : 1 < s₀) (hs : s₀ ≤ s) {X : ℕ}
    {P : Finset Nat.Primes} (hP : ∀ p ∈ P, X < (p : ℕ)) :
    ∏ p ∈ P, (1 + Real.exp (-s * Real.log p)) ≤
      Real.exp (∑' n : ℕ, ({n : ℕ | X < n}.indicator (rpowNegHom s₀) n)) := by
  classical
  have hsum : Summable (rpowNegHom s₀) := Real.summable_nat_rpow.mpr (by linarith)
  have hnn : ∀ n : ℕ, 0 ≤ rpowNegHom s₀ n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hind : Summable fun n : ℕ => {n : ℕ | X < n}.indicator (rpowNegHom s₀) n :=
    hsum.indicator _
  calc ∏ p ∈ P, (1 + Real.exp (-s * Real.log p))
      ≤ ∏ p ∈ P, Real.exp (Real.exp (-s₀ * Real.log p)) := by
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
        refine (Real.add_one_le_exp _).trans' ?_
        rw [add_comm]
        have := log_prime_pos p
        have : Real.exp (-s * Real.log p) ≤ Real.exp (-s₀ * Real.log p) :=
          Real.exp_le_exp.mpr (by nlinarith)
        linarith
    _ = Real.exp (∑ p ∈ P, Real.exp (-s₀ * Real.log p)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n : ℕ, ({n : ℕ | X < n}.indicator (rpowNegHom s₀) n)) := by
        refine Real.exp_le_exp.mpr ?_
        have e : ∑ p ∈ P, Real.exp (-s₀ * Real.log p) =
            ∑ n ∈ P.map (Function.Embedding.subtype _),
              {n : ℕ | X < n}.indicator (rpowNegHom s₀) n := by
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Function.Embedding.coe_subtype,
            Set.indicator_of_mem (show (p : ℕ) ∈ {n : ℕ | X < n} from hP p hp),
            exp_neg_mul_log_prime]
        rw [e]
        exact hind.sum_le_tsum _ fun n _ => Set.indicator_nonneg (fun m _ => hnn m) n

theorem tendsto_tsum_indicator_rpowNegHom {s₀ : ℝ} (hs₀ : 1 < s₀) :
    Tendsto (fun X : ℕ => ∑' n : ℕ, ({n : ℕ | X < n}.indicator (rpowNegHom s₀) n))
      atTop (𝓝 0) := by
  have hsum : Summable (rpowNegHom s₀) := Real.summable_nat_rpow.mpr (by linarith)
  have hnn : ∀ n : ℕ, 0 ≤ rpowNegHom s₀ n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (bound := fun n => rpowNegHom s₀ n)
    (f := fun X n => {n : ℕ | X < n}.indicator (rpowNegHom s₀) n) (g := fun _ => (0 : ℝ))
    hsum (fun n => ?_) ?_
  · simpa using h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with X hX
    rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | X < n} by simp only [Set.mem_setOf_eq]; omega)]
  · refine Eventually.of_forall fun X n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun m _ => hnn m) n)]
    exact Set.indicator_le_self' (fun m _ => hnn m) n

/-! ## The uniform variance bound -/

/-- The variance functional `V_P = Σ_ρ |w_ρ| (∏_P (1 + p^{−s_ρ}) − 1)`. -/
def jasSignVariance (P : Finset Nat.Primes) : ℝ :=
  ∑' q : XiZeroCopy, ‖lagWeight q‖ * ((∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1)

theorem prod_one_add_exp_neg_sub_one_nonneg (s : ℝ) (P : Finset Nat.Primes) :
    0 ≤ (∏ p ∈ P, (1 + Real.exp (-s * Real.log p))) - 1 := by
  have h := Finset.prod_le_prod (s := P) (f := fun _ : Nat.Primes => (1 : ℝ))
    (g := fun p => 1 + Real.exp (-s * Real.log p)) (fun _ _ => zero_le_one)
    (fun p _ => by linarith [Real.exp_pos (-s * Real.log p)])
  rw [Finset.prod_const_one] at h
  linarith

theorem prod_one_add_exp_neg_le_two_pow (s : ℝ) (hs : 0 ≤ s) (P : Finset Nat.Primes) :
    ∏ p ∈ P, (1 + Real.exp (-s * Real.log p)) ≤ 2 ^ P.card := by
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
  have := log_prime_pos p
  have : Real.exp (-s * Real.log p) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  linarith

theorem summable_jasSignVariance_term (P : Finset Nat.Primes) :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ *
      ((∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1) := by
  refine Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _)
    (prod_one_add_exp_neg_sub_one_nonneg _ _)) (fun q => ?_)
    (summable_norm_lagWeight.mul_right ((2 : ℝ) ^ P.card))
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := prod_one_add_exp_neg_le_two_pow (jasSignExponent q)
    (by linarith [one_lt_jasSignExponent q]) P
  linarith

/-- The variance functional for a general exponent function `s`. -/
def jasSignVarianceAt (s : XiZeroCopy → ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∑' q : XiZeroCopy, ‖lagWeight q‖ * ((∏ p ∈ P, (1 + Real.exp (-s q * Real.log p))) - 1)

theorem jasSignVariance_eq (P : Finset Nat.Primes) :
    jasSignVariance P = jasSignVarianceAt jasSignExponent P := rfl

theorem summable_jasSignVarianceAt_term {s : XiZeroCopy → ℝ} (hs : ∀ q, 0 ≤ s q)
    (P : Finset Nat.Primes) :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ *
      ((∏ p ∈ P, (1 + Real.exp (-s q * Real.log p))) - 1) := by
  refine Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _)
    (prod_one_add_exp_neg_sub_one_nonneg _ _)) (fun q => ?_)
    (summable_norm_lagWeight.mul_right ((2 : ℝ) ^ P.card))
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := prod_one_add_exp_neg_le_two_pow (s q) (hs q) P
  linarith

/-- High zeros: `1/(s_ρ − 1) ≤ 50 log(2 + |Im ρ|)` for `|Im ρ| ≥ 4`. -/
theorem inv_jasSignExponent_sub_one_le {q : XiZeroCopy} (hq : 4 ≤ |(q.1 : ℂ).im|) :
    1 / (jasSignExponent q - 1) ≤ 50 * Real.log (2 + |zeroOrdinate q|) := by
  have hz := abs_re_sub_half_le_of_four_le q hq
  have hlog : 0 < Real.log |(q.1 : ℂ).im| := Real.log_pos (by linarith)
  have hlog2 : Real.log |(q.1 : ℂ).im| ≤ Real.log (2 + |zeroOrdinate q|) :=
    Real.log_le_log (by linarith) (by unfold zeroOrdinate; linarith)
  have hpos : 0 < jasSignExponent q - 1 := by linarith [one_lt_jasSignExponent q]
  have hge : 2 / 100 / Real.log |(q.1 : ℂ).im| ≤ jasSignExponent q - 1 := by
    unfold jasSignExponent
    have : 2 / 100 / Real.log |(q.1 : ℂ).im| = 2 * (1 / 100 / Real.log |(q.1 : ℂ).im|) := by ring
    linarith
  rw [div_le_iff₀ hpos]
  have hl0 : 0 ≤ 50 * Real.log (2 + |zeroOrdinate q|) := by linarith
  calc (1 : ℝ) = 50 * Real.log |(q.1 : ℂ).im| * (2 / 100 / Real.log |(q.1 : ℂ).im|) := by
        field_simp; norm_num
    _ ≤ 50 * Real.log (2 + |zeroOrdinate q|) * (jasSignExponent q - 1) := by
        gcongr

/-- **The variance tends to `0` uniformly in the prime set.**  For every `ε > 0` there is `X` with
`V_P ≤ ε` for every finite set `P` of primes `p > X`. -/
theorem exists_jasSignVariance_le {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℕ, ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → jasSignVariance P ≤ ε := by
  classical
  -- the high zeros
  obtain ⟨F, hF⟩ : ∃ F : Finset XiZeroCopy, ∑' q : {x // x ∉ F},
      ‖lagWeight q.1‖ * Real.log (2 + |zeroOrdinate q.1|) ≤ ε / 100 := by
    have h := tendsto_tsum_compl_atTop_zero
      (fun q : XiZeroCopy => ‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|))
    obtain ⟨F, hF⟩ := (h.eventually (ge_mem_nhds (show (0 : ℝ) < ε / 100 by positivity))).exists
    exact ⟨F, hF⟩
  obtain ⟨H, hH4, hHF⟩ : ∃ H : ℝ, 4 ≤ H ∧ ∀ q ∈ F, |(q.1 : ℂ).im| ≤ H := by
    have hs0 : 0 ≤ ∑ q ∈ F, |(q.1 : ℂ).im| := Finset.sum_nonneg fun q _ => abs_nonneg _
    refine ⟨4 + ∑ q ∈ F, |(q.1 : ℂ).im|, by linarith, fun q hq => ?_⟩
    have := Finset.single_le_sum (f := fun q : XiZeroCopy => |(q.1 : ℂ).im|)
      (fun q _ => abs_nonneg _) hq
    linarith
  -- the low zeros
  obtain ⟨η₀, hη₀, hlow⟩ := exists_low_zero_width_at H
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖lagWeight q‖ := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact tsum_nonneg fun q => norm_nonneg _
  have hs₀ : 1 < 1 + 2 * η₀ := by linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ε / (2 * (W + 1)) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hcont : Tendsto (fun X : ℕ => Real.exp (∑' n : ℕ,
      ({n : ℕ | X < n}.indicator (rpowNegHom (1 + 2 * η₀)) n)) - 1) atTop (𝓝 0) := by
    have := ((Real.continuous_exp.tendsto 0).comp (tendsto_tsum_indicator_rpowNegHom hs₀)).sub_const
      1
    simpa using this
  obtain ⟨X, hX⟩ := (hcont.eventually (ge_mem_nhds hθ)).exists
  refine ⟨X, fun P hP => ?_⟩
  -- termwise bound
  obtain ⟨g, hg⟩ : ∃ g : XiZeroCopy → ℝ, g = fun q => if q ∈ F then (0 : ℝ) else
      50 * (‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)) := ⟨_, rfl⟩
  have hfnn : ∀ q : XiZeroCopy, 0 ≤ 50 * (‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)) :=
    fun q => mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (Real.log_nonneg (by
      linarith [abs_nonneg (zeroOrdinate q)])))
  have hgnn : ∀ q, 0 ≤ g q := fun q => by
    rw [hg]; dsimp only; split_ifs
    · exact le_rfl
    · exact hfnn q
  have hgle : ∀ q, g q ≤ 50 * (‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)) := fun q => by
    rw [hg]; dsimp only; split_ifs
    · exact hfnn q
    · exact le_rfl
  have hgs : Summable g :=
    Summable.of_nonneg_of_le hgnn hgle (summable_lagWeight_mul_log.mul_left 50)
  have hterm : ∀ q : XiZeroCopy, ‖lagWeight q‖ *
      ((∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1) ≤
      θ * ‖lagWeight q‖ + g q := by
    intro q
    have hw := norm_nonneg (lagWeight q)
    by_cases hq : |(q.1 : ℂ).im| ≤ H
    · -- low zero
      have hδ := hlow q hq
      have hsq : 1 + 2 * η₀ ≤ jasSignExponent q := by unfold jasSignExponent; linarith
      have hprod := prod_one_add_exp_neg_le_exp_tail hs₀ hsq hP
      have hg0 : 0 ≤ g q := hgnn q
      nlinarith
    · -- high zero
      push Not at hq
      have hqF : q ∉ F := fun h => absurd (hHF q h) (not_le.mpr hq)
      have hgq : g q = 50 * (‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)) := by
        rw [hg]; simp [hqF]
      have he := prod_one_add_exp_neg_le (one_lt_jasSignExponent q) P
      have hinv := inv_jasSignExponent_sub_one_le (q := q) (hH4.trans hq.le)
      have : (∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1 ≤
          50 * Real.log (2 + |zeroOrdinate q|) := by linarith
      rw [hgq]
      nlinarith [mul_le_mul_of_nonneg_left this hw, mul_nonneg hθ.le hw]
  have hgsum : ∑' q, g q ≤ 50 * (ε / 100) := by
    have e : ∑' q, g q = 50 * ∑' q : {x // x ∉ F},
        ‖lagWeight q.1‖ * Real.log (2 + |zeroOrdinate q.1|) := by
      rw [← tsum_mul_left]
      rw [show (∑' q : {x // x ∉ F}, 50 * (‖lagWeight q.1‖ * Real.log (2 + |zeroOrdinate q.1|))) =
          ∑' q : ↥({x | x ∉ F} : Set XiZeroCopy),
            50 * (‖lagWeight q.1‖ * Real.log (2 + |zeroOrdinate q.1|)) from rfl,
        tsum_subtype ({x | x ∉ F} : Set XiZeroCopy)
          (fun q => 50 * (‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)))]
      refine tsum_congr fun q => ?_
      rw [hg]
      by_cases hq : q ∈ F
      · simp [hq]
      · simp [hq]
    rw [e]
    exact mul_le_mul_of_nonneg_left hF (by norm_num)
  unfold jasSignVariance
  calc ∑' q : XiZeroCopy, ‖lagWeight q‖ *
        ((∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1)
      ≤ ∑' q : XiZeroCopy, (θ * ‖lagWeight q‖ + g q) :=
        (summable_jasSignVariance_term P).tsum_le_tsum hterm
          ((summable_norm_lagWeight.mul_left θ).add hgs)
    _ = θ * W + ∑' q, g q := by
        rw [(summable_norm_lagWeight.mul_left θ).tsum_add hgs, tsum_mul_left, hW]
    _ ≤ ε := by
        have : θ * W ≤ ε / 2 := by
          rw [hθdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

theorem one_le_prod_one_add_norm_sq (σ : ℝ) (P : Finset Nat.Primes) (q : XiZeroCopy) :
    1 ≤ ∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2) := by
  have h := Finset.prod_le_prod (s := P) (f := fun _ : Nat.Primes => (1 : ℝ))
    (g := fun p => 1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2) (fun _ _ => zero_le_one)
    (fun p _ => by linarith [sq_nonneg ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖])
  rwa [Finset.prod_const_one] at h

theorem prod_one_add_norm_sq_le_two_pow {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes)
    (q : XiZeroCopy) :
    ∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2) ≤ 2 ^ P.card := by
  refine (Finset.prod_le_prod (f := fun p => 1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2)
    (g := fun p => 1 + Real.exp (-jasSignExponent q * Real.log p)) (fun p _ => by positivity)
    fun p _ => by linarith [norm_sq_jasRealFactor_sub_one_le hσ p q]).trans ?_
  exact prod_one_add_exp_neg_le_two_pow _ (by linarith [one_lt_jasSignExponent q]) P

/-! ## Counting the negative sign patterns -/

/-- The sign-pattern aggregate `A_S = Σ_ρ K_S(ρ)/(ρ(1−ρ))`. -/
def jasSignAggregate (P : Finset Nat.Primes) (σ : ℝ) (S : Finset Nat.Primes) : ℂ :=
  ∑' q : XiZeroCopy, jasRealVecTerm P σ (jasSignVec S) (q.1 : ℂ)

theorem jasRealVecTerm_eq_lagWeight_mul (P : Finset Nat.Primes) (σ : ℝ) (t : Nat.Primes → ℝ)
    (q : XiZeroCopy) :
    jasRealVecTerm P σ t (q.1 : ℂ) = lagWeight q * jasRealVecKernel P σ t (q.1 : ℂ) := by
  rw [jasRealVecTerm, lagWeight, div_eq_mul_one_div, mul_comm]

theorem norm_jasSignKernel_le (P : Finset Nat.Primes) (σ : ℝ) (S : Finset Nat.Primes)
    (q : XiZeroCopy) :
    ‖jasRealVecKernel P σ (jasSignVec S) (q.1 : ℂ) - 1‖ ≤
      ∏ p ∈ P, (1 + Real.exp (-(σ - 1 / 2) * Real.log p)) + 1 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  have h := norm_jasRealVecKernel_xiZero_le P σ (jasSignVec S) q
  have e : ∀ p ∈ P, 1 + |jasSignVec S p| * Real.exp (-(σ - 1 / 2) * Real.log p) =
      1 + Real.exp (-(σ - 1 / 2) * Real.log p) := fun p _ => by
    unfold jasSignVec; split_ifs <;> simp
  rw [Finset.prod_congr rfl e] at h
  linarith

/-- The deviation of an aggregate from `Φ(0)` is a weighted sum of kernel deviations. -/
theorem norm_jasSignAggregate_sub_le (P : Finset Nat.Primes) (σ : ℝ) (S : Finset Nat.Primes) :
    ‖jasSignAggregate P σ S - poleSharpConstant‖ ≤
      ∑' q : XiZeroCopy, ‖lagWeight q‖ * ‖jasRealVecKernel P σ (jasSignVec S) (q.1 : ℂ) - 1‖ := by
  have hw : Summable fun q : XiZeroCopy => lagWeight q := summable_inv_mul_one_sub
  have hK := summable_jasRealVecTerm P σ (jasSignVec S)
  have e : jasSignAggregate P σ S - poleSharpConstant =
      ∑' q : XiZeroCopy, lagWeight q * (jasRealVecKernel P σ (jasSignVec S) (q.1 : ℂ) - 1) := by
    have e1 : ∀ q : XiZeroCopy, lagWeight q * (jasRealVecKernel P σ (jasSignVec S) (q.1 : ℂ) - 1) =
        jasRealVecTerm P σ (jasSignVec S) (q.1 : ℂ) - lagWeight q := fun q => by
      rw [jasRealVecTerm_eq_lagWeight_mul]; ring
    simp_rw [e1]
    rw [hK.tsum_sub hw, jasSignAggregate]
    congr 1
    exact tsum_inv_zero_mul_one_sub_zero.symm
  rw [e]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun q => norm_mul _ _))
  refine Summable.of_norm_bounded ((summable_norm_lagWeight).mul_right
    (∏ p ∈ P, (1 + Real.exp (-(σ - 1 / 2) * Real.log p)) + 1)) fun q => ?_
  rw [norm_norm, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_jasSignKernel_le P σ S q) (norm_nonneg _)

/-- **Counting the negative sign patterns, for any exponent bound.**  If `‖c_p(ρ)‖² ≤ p^{−s_ρ}` at
every zero, the number of sign patterns with `Re A_S < 0` is at most
`2^{|P|} W V_P(s) / Φ(0)²`. -/
theorem card_jasRealSign_re_neg_le_of_exponent {σ : ℝ} {s : XiZeroCopy → ℝ}
    (hs : ∀ q, 0 ≤ s q)
    (hc : ∀ (p : Nat.Primes) (q : XiZeroCopy),
      ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2 ≤ Real.exp (-s q * Real.log p))
    (P : Finset Nat.Primes) :
    ((P.powerset.filter fun S => (jasSignAggregate P σ S).re < 0).card : ℝ) *
      poleSharpConstant ^ 2 ≤ lagWeightTotal * 2 ^ P.card * jasSignVarianceAt s P := by
  classical
  have hΦ := poleSharpConstant_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∏ p ∈ P, (1 + Real.exp (-(σ - 1 / 2) * Real.log p)) + 1 :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Finset Nat.Primes → XiZeroCopy → ℝ,
      D = fun S q => ‖jasRealVecKernel P σ (jasSignVec S) (q.1 : ℂ) - 1‖ := ⟨_, rfl⟩
  have hDle : ∀ S q, D S q ≤ B := fun S q => by rw [hD, hB]; exact norm_jasSignKernel_le P σ S q
  have hD0 : ∀ S q, 0 ≤ D S q := fun S q => by rw [hD]; exact norm_nonneg _
  have hs1 : ∀ S, Summable fun q => ‖lagWeight q‖ * D S q := fun S =>
    Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (hD0 S q))
      (fun q => mul_le_mul_of_nonneg_left (hDle S q) (norm_nonneg _))
      (summable_norm_lagWeight.mul_right B)
  have hs2 : ∀ S, Summable fun q => ‖lagWeight q‖ * D S q ^ 2 := fun S =>
    Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun q => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hD0 S q) (hDle S q) 2)
        (norm_nonneg _))
      (summable_norm_lagWeight.mul_right (B ^ 2))
  -- a negative pattern has a large deviation
  have hbad : ∀ S, (jasSignAggregate P σ S).re < 0 →
      poleSharpConstant ^ 2 ≤ lagWeightTotal * ∑' q, ‖lagWeight q‖ * D S q ^ 2 := by
    intro S hS
    have h1 : poleSharpConstant ≤ ‖jasSignAggregate P σ S - poleSharpConstant‖ := by
      have h := Complex.abs_re_le_norm (jasSignAggregate P σ S - poleSharpConstant)
      rw [Complex.sub_re, Complex.ofReal_re] at h
      have := neg_abs_le ((jasSignAggregate P σ S).re - poleSharpConstant)
      linarith
    have h2 := (h1.trans (norm_jasSignAggregate_sub_le P σ S))
    have hCS := sq_tsum_mul_le (c := fun q => ‖lagWeight q‖) (x := D S)
      (fun q => norm_nonneg _) summable_norm_lagWeight (hs1 S) (hs2 S)
    have hWt : ∑' q, ‖lagWeight q‖ = lagWeightTotal := rfl
    rw [hWt] at hCS
    have h2' : poleSharpConstant ≤ ∑' q, ‖lagWeight q‖ * D S q := by rw [hD]; exact h2
    exact (pow_le_pow_left₀ hΦ.le h2' 2).trans hCS
  -- sum over the patterns
  have hsumS : ∑ S ∈ P.powerset, ∑' q, ‖lagWeight q‖ * D S q ^ 2 =
      ∑' q, ‖lagWeight q‖ * (2 ^ P.card *
        ((∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2)) - 1)) := by
    rw [← Summable.tsum_finsetSum fun S _ => hs2 S]
    refine tsum_congr fun q => ?_
    rw [← Finset.mul_sum, ← sum_norm_sq_jasRealVecKernel_sign_sub_one, hD]
  have hvar : ∑' q, ‖lagWeight q‖ * (2 ^ P.card *
      ((∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2)) - 1)) ≤
      2 ^ P.card * jasSignVarianceAt s P := by
    unfold jasSignVarianceAt
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun q => ?_) ?_
      ((summable_jasSignVarianceAt_term hs P).mul_left _)
    · have hle : ∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2) ≤
          ∏ p ∈ P, (1 + Real.exp (-s q * Real.log p)) :=
        Finset.prod_le_prod (fun p _ => by positivity) fun p _ => by
          linarith [hc p q]
      have hw := norm_nonneg (lagWeight q)
      have h2 : (0 : ℝ) ≤ 2 ^ P.card := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg hw h2)]
    · refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_)
        (summable_norm_lagWeight.mul_right ((2 : ℝ) ^ P.card * 2 ^ P.card))
      · exact mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity)
          (by linarith [one_le_prod_one_add_norm_sq σ P q]))
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h3 : ∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2) ≤ 2 ^ P.card :=
          (Finset.prod_le_prod (f := fun p => 1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2)
            (g := fun p => 1 + Real.exp (-s q * Real.log p)) (fun p _ => by positivity)
            fun p _ => by linarith [hc p q]).trans (prod_one_add_exp_neg_le_two_pow _ (hs q) P)
        have h2 : (0 : ℝ) ≤ 2 ^ P.card := by positivity
        nlinarith [one_le_prod_one_add_norm_sq σ P q]
  have hW0 := lagWeightTotal_nonneg
  have hnnS : ∀ S, 0 ≤ lagWeightTotal * ∑' q, ‖lagWeight q‖ * D S q ^ 2 := fun S =>
    mul_nonneg hW0 (tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  calc ((P.powerset.filter fun S => (jasSignAggregate P σ S).re < 0).card : ℝ) *
        poleSharpConstant ^ 2
      = ∑ S ∈ P.powerset.filter (fun S => (jasSignAggregate P σ S).re < 0),
          poleSharpConstant ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ S ∈ P.powerset.filter (fun S => (jasSignAggregate P σ S).re < 0),
          lagWeightTotal * ∑' q, ‖lagWeight q‖ * D S q ^ 2 :=
        Finset.sum_le_sum fun S hS => hbad S (Finset.mem_filter.mp hS).2
    _ ≤ ∑ S ∈ P.powerset, lagWeightTotal * ∑' q, ‖lagWeight q‖ * D S q ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S _ _ => hnnS S
    _ = lagWeightTotal * ∑' q, ‖lagWeight q‖ * (2 ^ P.card *
          ((∏ p ∈ P, (1 + ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2)) - 1)) := by
        rw [← Finset.mul_sum, hsumS]
    _ ≤ lagWeightTotal * (2 ^ P.card * jasSignVarianceAt s P) :=
        mul_le_mul_of_nonneg_left hvar hW0
    _ = lagWeightTotal * 2 ^ P.card * jasSignVarianceAt s P := by ring

/-- **Counting the negative sign patterns.**  At a level `σ ≥ 1`, the number of sign patterns with
`Re A_S < 0` is at most `2^{|P|} W V_P / Φ(0)²`. -/
theorem card_jasRealSign_re_neg_le {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes) :
    ((P.powerset.filter fun S => (jasSignAggregate P σ S).re < 0).card : ℝ) *
      poleSharpConstant ^ 2 ≤ lagWeightTotal * 2 ^ P.card * jasSignVariance P := by
  rw [jasSignVariance_eq]
  exact card_jasRealSign_re_neg_le_of_exponent
    (fun q => by linarith [one_lt_jasSignExponent q])
    (fun p q => norm_sq_jasRealFactor_sub_one_le hσ p q) P

/-- **Typical sign patterns are positive, uniformly in the prime set.**  For every level `σ ≥ 1` and
every `ε > 0` there is `X` such that for every finite set `P` of primes `p > X` at most
`ε · 2^{|P|}` sign patterns `ε_S ∈ {±1}^P` give `Re Σ_ρ K_S(ρ)/(ρ(1−ρ)) < 0`. -/
theorem exists_card_jasRealSign_re_neg_le {σ : ℝ} (hσ : 1 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℕ, ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) →
      ((P.powerset.filter fun S => (jasSignAggregate P σ S).re < 0).card : ℝ) ≤
        ε * 2 ^ P.card := by
  have hΦ := poleSharpConstant_pos
  have hW0 := lagWeightTotal_nonneg
  obtain ⟨X, hX⟩ := exists_jasSignVariance_le
    (show 0 < ε * poleSharpConstant ^ 2 / (lagWeightTotal + 1) by positivity)
  refine ⟨X, fun P hP => ?_⟩
  have hc := card_jasRealSign_re_neg_le hσ P
  have hV := hX P hP
  have h2 : (0 : ℝ) < 2 ^ P.card := by positivity
  have hV0 : 0 ≤ jasSignVariance P := tsum_nonneg fun q =>
    mul_nonneg (norm_nonneg _) (prod_one_add_exp_neg_sub_one_nonneg _ _)
  have key : lagWeightTotal * jasSignVariance P ≤ ε * poleSharpConstant ^ 2 := by
    calc lagWeightTotal * jasSignVariance P
        ≤ (lagWeightTotal + 1) * (ε * poleSharpConstant ^ 2 / (lagWeightTotal + 1)) := by
          gcongr
          linarith
      _ = ε * poleSharpConstant ^ 2 := by field_simp
  have hΦ2 : 0 < poleSharpConstant ^ 2 := by positivity
  have : ((P.powerset.filter fun S => (jasSignAggregate P σ S).re < 0).card : ℝ) *
      poleSharpConstant ^ 2 ≤ ε * 2 ^ P.card * poleSharpConstant ^ 2 := by
    calc _ ≤ lagWeightTotal * 2 ^ P.card * jasSignVariance P := hc
      _ = 2 ^ P.card * (lagWeightTotal * jasSignVariance P) := by ring
      _ ≤ 2 ^ P.card * (ε * poleSharpConstant ^ 2) := mul_le_mul_of_nonneg_left key h2.le
      _ = ε * 2 ^ P.card * poleSharpConstant ^ 2 := by ring
  exact le_of_mul_le_mul_right this hΦ2

/-! ## Under a zero-free half-plane: typical positivity below level one -/

/-- At every level, `‖c_p(ρ)‖² ≤ p^{−(2σ − 2|Re ρ − ½|)}`. -/
theorem norm_sq_jasRealFactor_sub_one_le_level (σ : ℝ) (p : Nat.Primes) (q : XiZeroCopy) :
    ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2 ≤
      Real.exp (-(2 * σ - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log p) := by
  have h := norm_jasRealFactor_sub_one_le zero_le_one p (q.1 : ℂ) (σ := σ)
  rw [one_mul] at h
  calc ‖jasRealFactor σ 1 p (q.1 : ℂ) - 1‖ ^ 2
      ≤ Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Real.exp (-(2 * σ - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log p) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- Under a uniform exponent bound `s_ρ ≥ s₀ > 1`, the variance is at most
`W (exp(Σ_{n > X} n^{−s₀}) − 1)` for every set of primes `p > X`. -/
theorem jasSignVarianceAt_le_of_uniform {s : XiZeroCopy → ℝ} {s₀ : ℝ} (hs₀ : 1 < s₀)
    (hs : ∀ q, s₀ ≤ s q) {X : ℕ} {P : Finset Nat.Primes} (hP : ∀ p ∈ P, X < (p : ℕ)) :
    jasSignVarianceAt s P ≤ lagWeightTotal *
      (Real.exp (∑' n : ℕ, ({n : ℕ | X < n}.indicator (rpowNegHom s₀) n)) - 1) := by
  unfold jasSignVarianceAt lagWeightTotal
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun q => ?_)
    (summable_jasSignVarianceAt_term (fun q => by linarith [hs q]) P)
    (summable_norm_lagWeight.mul_right _)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  linarith [prod_one_add_exp_neg_le_exp_tail hs₀ (hs q) hP]

/-- **Typical positivity under a zero-free half-plane.**  If every zero satisfies
`|Re ρ − ½| ≤ α` and `σ > ½ + α`, then for every `ε > 0` there is `X` such that for every finite set
`P` of primes `p > X` at most `ε · 2^{|P|}` sign patterns give `Re A_S < 0`.  Under RH this holds at
every level `σ > ½`. -/
theorem exists_card_jasRealSign_re_neg_le_of_halfPlane {α σ : ℝ} (hXi : XiZeroHalfPlaneBound α)
    (hσ : 1 / 2 + α < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℕ, ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) →
      ((P.powerset.filter fun S => (jasSignAggregate P σ S).re < 0).card : ℝ) ≤
        ε * 2 ^ P.card := by
  have hΦ := poleSharpConstant_pos
  have hW0 := lagWeightTotal_nonneg
  obtain ⟨s, hsdef⟩ : ∃ s : XiZeroCopy → ℝ,
      s = fun q => 2 * σ - 2 * |(q.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  have hs₀ : 1 < 2 * σ - 2 * α := by linarith
  have hs : ∀ q, 2 * σ - 2 * α ≤ s q := fun q => by
    rw [hsdef]; dsimp only; linarith [abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q]
  have hcont : Tendsto (fun X : ℕ => Real.exp (∑' n : ℕ,
      ({n : ℕ | X < n}.indicator (rpowNegHom (2 * σ - 2 * α)) n)) - 1) atTop (𝓝 0) := by
    have := ((Real.continuous_exp.tendsto 0).comp
      (tendsto_tsum_indicator_rpowNegHom hs₀)).sub_const 1
    simpa using this
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ,
      θ = ε * poleSharpConstant ^ 2 / ((lagWeightTotal + 1) * (lagWeightTotal + 1)) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; positivity
  obtain ⟨X, hX⟩ := (hcont.eventually (ge_mem_nhds hθ)).exists
  refine ⟨X, fun P hP => ?_⟩
  have hc := card_jasRealSign_re_neg_le_of_exponent (σ := σ) (s := s)
    (fun q => by linarith [hs q]) (fun p q => by
      rw [hsdef]; exact norm_sq_jasRealFactor_sub_one_le_level σ p q) P
  have hV := jasSignVarianceAt_le_of_uniform hs₀ hs hP
  have h2 : (0 : ℝ) < 2 ^ P.card := by positivity
  have hV0 : 0 ≤ jasSignVarianceAt s P := tsum_nonneg fun q =>
    mul_nonneg (norm_nonneg _) (prod_one_add_exp_neg_sub_one_nonneg _ _)
  have key : lagWeightTotal * jasSignVarianceAt s P ≤ ε * poleSharpConstant ^ 2 := by
    have h1 : jasSignVarianceAt s P ≤ lagWeightTotal * θ :=
      hV.trans (mul_le_mul_of_nonneg_left hX hW0)
    calc lagWeightTotal * jasSignVarianceAt s P ≤ lagWeightTotal * (lagWeightTotal * θ) :=
          mul_le_mul_of_nonneg_left h1 hW0
      _ ≤ (lagWeightTotal + 1) * ((lagWeightTotal + 1) * θ) := by gcongr <;> linarith
      _ = ε * poleSharpConstant ^ 2 := by rw [hθdef]; field_simp
  have hΦ2 : 0 < poleSharpConstant ^ 2 := by positivity
  have : ((P.powerset.filter fun S => (jasSignAggregate P σ S).re < 0).card : ℝ) *
      poleSharpConstant ^ 2 ≤ ε * 2 ^ P.card * poleSharpConstant ^ 2 := by
    calc _ ≤ lagWeightTotal * 2 ^ P.card * jasSignVarianceAt s P := hc
      _ = 2 ^ P.card * (lagWeightTotal * jasSignVarianceAt s P) := by ring
      _ ≤ 2 ^ P.card * (ε * poleSharpConstant ^ 2) := mul_le_mul_of_nonneg_left key h2.le
      _ = ε * 2 ^ P.card * poleSharpConstant ^ 2 := by ring
  exact le_of_mul_le_mul_right this hΦ2

end

end RHTower
