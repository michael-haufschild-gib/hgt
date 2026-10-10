import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorLagAggregate
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit

/-!
# The JAS positivity abscissa

Dress the lag-weighted aggregate of explicit-formula sectors by the prime-Poisson sector `μ_σ`:
its coefficient at a rational character `n = u/v` is

`N_σ(n) = (uv)^{-σ} · Φ(log v - log u)`,

the Weil lag function times the character moment `(uv)^{-σ}` of `μ_σ` at real height.  At
`σ = 1/2` this is the JAS aggregate of the explicit-formula sectors.

* **Monotonicity.**  `N_σ = N_{σ'} · μ̂_{σ-σ'}`, and the moment function of the positive measure
  `μ_{σ-σ'}` is positive definite; hence positive semidefiniteness of `N_{σ'}` implies that of
  `N_σ` for every `σ ≥ σ'` (Schur product through the Poisson convolution semigroup).  The set of
  positive dressings is an up-ray.
* **Finiteness.**  `|Φ(L)| ≤ C e^{|L|/2}` with `C = Σ_ρ |1/(ρ(1-ρ))|`, so off the trivial character
  `|N_σ(n)| ≤ C (uv)^{-(σ-1/2)}`, and the sum over all nontrivial characters is at most
  `C (ζ(σ - 1/2)² - 1)`.  Since `N_σ(0) = Φ(0) = 2 + γ - log 4π > 0`, a Gershgorin bound gives
  positive semidefiniteness for all large `σ`, unconditionally.
* **RH.**  Under RH the aggregate at `σ = 1/2` is positive semidefinite, hence every dressing
  `σ ≥ 1/2` is.

So the positivity abscissa `σ* = inf {σ : N_σ is positive semidefinite}` is finite unconditionally
and at most `1/2` under RH.  The phase-budget, total-variation and Kronecker-amplification
theorems for single explicit-formula sectors indicate a gap: an off-line zero at distance `δ` from
the critical line has phase budget and amplification `Σ_p p^{-σ+δ} = ∞` for every `σ ≤ 1 + δ`,
which predicts `σ* ≥ 1 + δ` off RH.  On that prediction RH is equivalent to positivity of the
dressing by the pole sector `μ_1`, and positivity at any `σ < 3/2` would give a uniform zero-free
strip.
-/

open Complex MeasureTheory
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- `log u + log v = Σ_p |n_p| log p`. -/
def jasLogSize (n : Nat.Primes →₀ ℤ) : ℝ := jasLogPos n + jasLogNeg n

theorem jasLogPos_nonneg (n : Nat.Primes →₀ ℤ) : 0 ≤ jasLogPos n :=
  Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (log_prime_pos p).le

theorem jasLogNeg_nonneg (n : Nat.Primes →₀ ℤ) : 0 ≤ jasLogNeg n :=
  Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (log_prime_pos p).le

theorem jasLogSize_eq (n : Nat.Primes →₀ ℤ) :
    jasLogSize n = n.sum fun p k => (|k| : ℝ) * Real.log p := by
  unfold jasLogSize jasLogPos jasLogNeg Finsupp.sum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← add_mul, ← Nat.cast_add, Int.toNat_add_toNat_neg_eq_natAbs, Nat.cast_natAbs, Int.cast_abs]

/-- The lag aggregate dressed by the prime-Poisson sector `μ_σ`. -/
def jasDressedLagAggregate (σ : ℝ) (n : Nat.Primes →₀ ℤ) : ℂ :=
  (Real.exp (-σ * jasLogSize n) : ℂ) * weilLagFunction (jasLogNeg n - jasLogPos n)

theorem jasDressedLagAggregate_half (n : Nat.Primes →₀ ℤ) :
    jasDressedLagAggregate (1 / 2) n = jasLagAggregate n := by
  rw [jasDressedLagAggregate, jasLagAggregate_eq, jasLogSize]
  congr 3
  ring

/-- Positive semidefiniteness of the `σ`-dressed aggregate on every finite family of distinct
rational characters. -/
def JasDressedPSD (σ : ℝ) : Prop :=
  ∀ (ι : Type) (t : Finset ι) (c : ι → ℂ) (n : ι → Nat.Primes →₀ ℤ), Set.InjOn n t →
    0 ≤ (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ (n i - n j)).re

/-- The character moments of the real-height prime-Poisson sector: `μ̂_c(n) = e^{-c Σ |n_p| log p}`. -/
theorem integral_infiniteTorusFourier_primePoissonMeasure_real {c : ℝ} (hc : 0 < c)
    (n : Nat.Primes →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(primePoissonMeasure c 0 hc) =
      (Real.exp (-c * jasLogSize n) : ℂ) := by
  have hexp : Real.exp (-c * jasLogSize n) =
      ∏ p ∈ n.support, Real.exp (-c * ((|n p| : ℝ) * Real.log p)) := by
    rw [jasLogSize_eq, Finsupp.sum, Finset.mul_sum, Real.exp_sum]
  rw [integral_infiniteTorusFourier_primePoissonMeasure, hexp, Complex.ofReal_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hval : (primePoissonParameter c 0 hc p : ℂ) = (Real.exp (-c * Real.log p) : ℂ) := by
    rw [coe_primePoissonParameter, primePoissonParameterValue, Complex.ofReal_exp]
    congr 1; push_cast; ring
  rcases (n p) with m | m
  · have hm : |((Int.ofNat m : ℤ) : ℝ)| = (m : ℝ) := by simp
    simp only [circlePoissonFourierMoment, hval, ← Complex.ofReal_pow, ← Real.exp_nat_mul, hm]
    congr 2; ring
  · have hm : |((Int.negSucc m : ℤ) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
      rw [Int.cast_negSucc, abs_neg]; push_cast; rw [abs_of_nonneg (by positivity)]
    simp only [circlePoissonFourierMoment, hval, Complex.conj_ofReal, ← Complex.ofReal_pow,
      ← Real.exp_nat_mul, hm]
    congr 2; ring

/-- **Monotonicity.**  A positive dressing stays positive under further dressing. -/
theorem JasDressedPSD.mono {σ' σ : ℝ} (h : JasDressedPSD σ') (hle : σ' ≤ σ) :
    JasDressedPSD σ := by
  intro ι t c n hinj
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact h ι t c n hinj
  set κ := σ - σ' with hκ
  have hκ0 : 0 < κ := sub_pos.mpr hlt
  set μ := primePoissonMeasure κ 0 hκ0 with hμ
  have hsplit : ∀ m : Nat.Primes →₀ ℤ, jasDressedLagAggregate σ m =
      jasDressedLagAggregate σ' m * ∫ x, infiniteTorusFourier m x ∂μ := by
    intro m
    rw [hμ, integral_infiniteTorusFourier_primePoissonMeasure_real, jasDressedLagAggregate,
      jasDressedLagAggregate, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  have hint : ∀ m : Nat.Primes →₀ ℤ, Integrable (fun x => infiniteTorusFourier m x) μ :=
    integrable_infiniteTorusFourier μ
  have hpt : ∀ x, ∑ i ∈ t, ∑ j ∈ t, (c i * infiniteTorusFourier (n i) x) *
      conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j) =
      ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) *
        (jasDressedLagAggregate σ' (n i - n j) * infiniteTorusFourier (n i - n j) x) := by
    intro x
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sub_eq_add_neg, infiniteTorusFourier_add, infiniteTorusFourier_neg, map_mul]
    ring
  have heq : ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ (n i - n j) =
      ∫ x, ∑ i ∈ t, ∑ j ∈ t, (c i * infiniteTorusFourier (n i) x) *
        conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j) ∂μ := by
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, integral_const_mul, hsplit]
      · intro j _; exact ((hint _).const_mul _).const_mul _
    · intro i _
      exact integrable_finsetSum _ fun j _ => ((hint _).const_mul _).const_mul _
  have hInt : Integrable (fun x => ∑ i ∈ t, ∑ j ∈ t, (c i * infiniteTorusFourier (n i) x) *
      conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j)) μ := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    have : Continuous fun x => (c i * infiniteTorusFourier (n i) x) *
        conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j) := by
      fun_prop
    exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre := integral_re hInt
  simp only [RCLike.re_to_complex] at hre
  rw [heq, ← hre]
  exact integral_nonneg fun x => h ι t (fun i => c i * infiniteTorusFourier (n i) x) n hinj

/-- **RH ⟹ every dressing `σ ≥ 1/2` is positive.** -/
theorem jasDressedPSD_of_riemannHypothesis (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    JasDressedPSD σ := by
  apply JasDressedPSD.mono _ hσ
  intro ι t c n _
  simp_rw [jasDressedLagAggregate_half]
  exact (jasLagAggregate_posSemidef_of_riemannHypothesis hRH t c n).2

/-! ## Unconditional positivity for large dressing -/

/-- Total absolute lag weight. -/
def jasLagAbsMass : ℝ := ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖

theorem norm_weilLagFunction_le (L : ℝ) : ‖weilLagFunction L‖ ≤ Real.exp (|L| / 2) * jasLagAbsMass := by
  unfold weilLagFunction jasLagAbsMass
  refine (norm_tsum_le_tsum_norm (summable_weilLagTerm L).norm).trans ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (norm_weilLagTerm_le L) (summable_weilLagTerm L).norm
    (summable_inv_mul_one_sub.norm.mul_left _)

theorem norm_jasDressedLagAggregate_le (σ : ℝ) (n : Nat.Primes →₀ ℤ) :
    ‖jasDressedLagAggregate σ n‖ ≤ jasLagAbsMass * Real.exp (-(σ - 1 / 2) * jasLogSize n) := by
  rw [jasDressedLagAggregate, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine (mul_le_mul_of_nonneg_left (norm_weilLagFunction_le _) (Real.exp_pos _).le).trans ?_
  have hL : |jasLogNeg n - jasLogPos n| ≤ jasLogSize n := by
    rw [jasLogSize, abs_le]
    constructor <;> linarith [jasLogPos_nonneg n, jasLogNeg_nonneg n]
  have h2 : Real.exp (|jasLogNeg n - jasLogPos n| / 2) ≤ Real.exp (jasLogSize n / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hA : 0 ≤ jasLagAbsMass := tsum_nonneg fun _ => norm_nonneg _
  calc Real.exp (-σ * jasLogSize n) * (Real.exp (|jasLogNeg n - jasLogPos n| / 2) * jasLagAbsMass)
      ≤ Real.exp (-σ * jasLogSize n) * (Real.exp (jasLogSize n / 2) * jasLagAbsMass) := by
        gcongr
    _ = jasLagAbsMass * Real.exp (-(σ - 1 / 2) * jasLogSize n) := by
        rw [mul_left_comm, ← mul_assoc, ← Real.exp_add, mul_comm]
        congr 2; ring

theorem jasDressedLagAggregate_zero (σ : ℝ) :
    jasDressedLagAggregate σ 0 = (poleSharpConstant : ℂ) := by
  simp [jasDressedLagAggregate, jasLogSize, jasLogPos, jasLogNeg, weilLagFunction_zero]

theorem jasDressedLagAggregate_neg (σ : ℝ) (n : Nat.Primes →₀ ℤ) :
    jasDressedLagAggregate σ (-n) = jasDressedLagAggregate σ n := by
  have hpos : jasLogPos (-n) = jasLogNeg n := by
    unfold jasLogPos jasLogNeg; rw [Finsupp.sum_neg_index (by simp)]
  have hneg : jasLogNeg (-n) = jasLogPos n := by
    unfold jasLogPos jasLogNeg; rw [Finsupp.sum_neg_index (by simp)]; simp
  rw [jasDressedLagAggregate, jasDressedLagAggregate, jasLogSize, jasLogSize, hpos, hneg,
    show jasLogPos n - jasLogNeg n = -(jasLogNeg n - jasLogPos n) by ring, weilLagFunction_neg,
    add_comm]

/-! ### Encoding rational characters by pairs of natural numbers -/

/-- Numerator `u = ∏ p^{n_p⁺}`. -/
def jasNum (n : Nat.Primes →₀ ℤ) : ℕ := n.prod fun p k => (p : ℕ) ^ k.toNat

/-- Denominator `v = ∏ p^{n_p⁻}`. -/
def jasDen (n : Nat.Primes →₀ ℤ) : ℕ := n.prod fun p k => (p : ℕ) ^ (-k).toNat

theorem factorization_prime_pow_prod (n : Nat.Primes →₀ ℤ) (e : ℤ → ℕ) (he : e 0 = 0)
    (q : Nat.Primes) :
    (n.prod fun p k => (p : ℕ) ^ e k).factorization q = e (n q) := by
  classical
  unfold Finsupp.prod
  rw [Nat.factorization_prod (fun p _ => pow_ne_zero _ p.2.ne_zero), Finset.sum_apply']
  rw [Finset.sum_congr rfl fun p _ => by rw [Nat.Prime.factorization_pow p.2]]
  by_cases hq : q ∈ n.support
  · rw [Finset.sum_eq_single q]
    · simp
    · intro p _ hpq
      rw [Finsupp.single_apply, if_neg]
      intro h; exact hpq (Subtype.ext h)
    · intro h; exact absurd hq h
  · rw [Finset.sum_eq_zero, Finsupp.notMem_support_iff.mp hq, he]
    intro p hp
    rw [Finsupp.single_apply, if_neg]
    intro h; exact hq ((Subtype.ext h : p = q) ▸ hp)

theorem jasNum_jasDen_injective :
    Function.Injective fun n : Nat.Primes →₀ ℤ => (jasNum n, jasDen n) := by
  intro n m h
  simp only [Prod.mk.injEq] at h
  ext q
  have h1 := congrArg (fun x => Nat.factorization x q) h.1
  have h2 := congrArg (fun x => Nat.factorization x q) h.2
  simp only [jasNum, jasDen] at h1 h2
  rw [factorization_prime_pow_prod n _ (by simp), factorization_prime_pow_prod m _ (by simp)] at h1 h2
  omega

theorem jasNum_pos (n : Nat.Primes →₀ ℤ) : 0 < jasNum n :=
  Finset.prod_pos fun p _ => pow_pos p.2.pos _

theorem jasDen_pos (n : Nat.Primes →₀ ℤ) : 0 < jasDen n :=
  Finset.prod_pos fun p _ => pow_pos p.2.pos _

theorem exp_neg_mul_jasLogSize (a : ℝ) (n : Nat.Primes →₀ ℤ) :
    Real.exp (-a * jasLogSize n) = ((jasNum n : ℝ) ^ a)⁻¹ * ((jasDen n : ℝ) ^ a)⁻¹ := by
  have hlogNum : Real.log (jasNum n : ℝ) = jasLogPos n := by
    unfold jasNum jasLogPos Finsupp.prod Finsupp.sum
    push_cast
    rw [Real.log_prod (fun p _ => pow_ne_zero _ (by exact_mod_cast p.2.ne_zero))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_pow]
  have hlogDen : Real.log (jasDen n : ℝ) = jasLogNeg n := by
    unfold jasDen jasLogNeg Finsupp.prod Finsupp.sum
    push_cast
    rw [Real.log_prod (fun p _ => pow_ne_zero _ (by exact_mod_cast p.2.ne_zero))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_pow]
  have hu := jasNum_pos n
  have hv := jasDen_pos n
  rw [Real.rpow_def_of_pos (by exact_mod_cast hu), Real.rpow_def_of_pos (by exact_mod_cast hv),
    hlogNum, hlogDen, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, jasLogSize]
  congr 1; ring

theorem jasNum_jasDen_ne_one_one {n : Nat.Primes →₀ ℤ} (hn : n ≠ 0) :
    (jasNum n, jasDen n) ≠ (1, 1) := by
  intro h
  apply hn
  apply jasNum_jasDen_injective
  show (jasNum n, jasDen n) = (jasNum 0, jasDen 0)
  rw [h]
  simp [jasNum, jasDen]

/-- Nontrivial characters: `Σ e^{-a·size} ≤ ζ(a)² - 1` for `a > 1`. -/
theorem sum_exp_neg_mul_jasLogSize_le {a : ℝ} (ha : 1 < a) (T : Finset (Nat.Primes →₀ ℤ))
    (hT : (0 : Nat.Primes →₀ ℤ) ∉ T) :
    ∑ m ∈ T, Real.exp (-a * jasLogSize m) ≤ (∑' k : ℕ, ((k : ℝ) ^ a)⁻¹) ^ 2 - 1 := by
  classical
  set f : ℕ → ℝ := fun k => ((k : ℝ) ^ a)⁻¹ with hf
  have hsum : Summable f := Real.summable_nat_rpow_inv.mpr ha
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  set g : ℕ × ℕ → ℝ := fun z => f z.1 * f z.2 with hg
  have hgs : Summable g := by
    have := (summable_mul_of_summable_norm (f := f) (g := f) (by simpa [Real.norm_of_nonneg (hf0 _)])
      (by simpa [Real.norm_of_nonneg (hf0 _)]))
    exact this
  have hg0 : ∀ z, 0 ≤ g z := fun z => mul_nonneg (hf0 _) (hf0 _)
  have htot : ∑' z, g z = (∑' k, f k) ^ 2 := by
    rw [sq, tsum_mul_tsum_of_summable_norm (by simpa [Real.norm_of_nonneg (hf0 _)])
      (by simpa [Real.norm_of_nonneg (hf0 _)])]
  have hg11 : g (1, 1) = 1 := by simp [hg, hf]
  have himg : ∑ m ∈ T, Real.exp (-a * jasLogSize m) =
      ∑ z ∈ T.image (fun m => (jasNum m, jasDen m)), g z := by
    rw [Finset.sum_image (fun x _ y _ h => jasNum_jasDen_injective h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [exp_neg_mul_jasLogSize]
  rw [himg]
  have hnot : (1, 1) ∉ T.image (fun m => (jasNum m, jasDen m)) := by
    intro h
    obtain ⟨m, hm, hm11⟩ := Finset.mem_image.mp h
    exact jasNum_jasDen_ne_one_one (fun h0 => hT (h0 ▸ hm)) hm11
  have hle := hgs.sum_le_tsum (insert (1, 1) (T.image (fun m => (jasNum m, jasDen m))))
    (fun z _ => hg0 z)
  rw [Finset.sum_insert hnot, hg11, htot] at hle
  linarith

/-- `Σ_k k^{-a} ≤ 1 + 2^{3-a}` for `a ≥ 2`. -/
theorem tsum_rpow_inv_le {a : ℝ} (ha : 2 ≤ a) :
    ∑' k : ℕ, ((k : ℝ) ^ a)⁻¹ ≤ 1 + 2 ^ (3 - a) := by
  have hs2 : Summable fun k : ℕ => ((k : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hsa : Summable fun k : ℕ => ((k : ℝ) ^ a)⁻¹ := Real.summable_nat_rpow_inv.mpr (by linarith)
  -- split off k = 0, 1
  rw [← hsa.sum_add_tsum_nat_add 2]
  have h01 : ∑ k ∈ Finset.range 2, ((k : ℝ) ^ a)⁻¹ = 1 := by
    simp [Finset.sum_range_succ, Real.zero_rpow (by linarith : a ≠ 0)]
  rw [h01]
  have htail : ∀ k : ℕ, (((k + 2 : ℕ) : ℝ) ^ a)⁻¹ ≤ 2 ^ (2 - a) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ := by
    intro k
    have hk : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
    have hpos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by linarith
    rw [show ((k + 2 : ℕ) : ℝ) ^ a = ((k + 2 : ℕ) : ℝ) ^ (2 : ℝ) * ((k + 2 : ℕ) : ℝ) ^ (a - 2) by
      rw [← Real.rpow_add hpos]; ring_nf]
    rw [mul_inv, mul_comm]
    gcongr
    rw [show (2 : ℝ) ^ (2 - a) = ((2 : ℝ) ^ (a - 2))⁻¹ by rw [← Real.rpow_neg (by norm_num)]; ring_nf]
    gcongr
  have hs2' : Summable fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ :=
    (summable_nat_add_iff 2).mpr hs2
  have hsa' : Summable fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ a)⁻¹ := (summable_nat_add_iff 2).mpr hsa
  have hbound : ∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ ≤ 2 := by
    have hz := hasSum_zeta_two
    have hle : ∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ ≤ ∑' k : ℕ, ((k : ℝ) ^ (2 : ℝ))⁻¹ := by
      rw [← hs2.sum_add_tsum_nat_add 2]
      have : 0 ≤ ∑ k ∈ Finset.range 2, ((k : ℝ) ^ (2 : ℝ))⁻¹ :=
        Finset.sum_nonneg fun k _ => by positivity
      linarith
    have heq : ∑' k : ℕ, ((k : ℝ) ^ (2 : ℝ))⁻¹ = Real.pi ^ 2 / 6 := by
      rw [← hz.tsum_eq]
      congr 1; funext k
      rw [one_div, Real.rpow_two]
    have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
      have := Real.pi_lt_d2
      have := Real.pi_pos
      nlinarith
    linarith
  have : ∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ a)⁻¹ ≤ 2 ^ (2 - a) * 2 := by
    calc ∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ a)⁻¹
        ≤ ∑' k : ℕ, 2 ^ (2 - a) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ :=
          Summable.tsum_le_tsum htail hsa' (hs2'.mul_left _)
      _ = 2 ^ (2 - a) * ∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ := tsum_mul_left
      _ ≤ 2 ^ (2 - a) * 2 := by gcongr
  have h3 : (2 : ℝ) ^ (2 - a) * 2 = 2 ^ (3 - a) := by
    rw [show (3 : ℝ) - a = (2 - a) + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  push_cast at this ⊢
  linarith

/-- **Unconditional positivity for large dressing.** -/
theorem exists_jasDressedPSD : ∃ σ₀ : ℝ, ∀ σ, σ₀ ≤ σ → JasDressedPSD σ := by
  set C := jasLagAbsMass with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  set A := poleSharpConstant with hA
  have hA0 : 0 < A := poleSharpConstant_pos
  -- choose `a = σ₀ - 1/2 ≥ 2` with `C ((1 + 2^{3-a})² - 1) ≤ A`
  obtain ⟨a, ha2, ha3, hsmall⟩ : ∃ a : ℝ, 2 ≤ a ∧ 3 ≤ a ∧ 3 * C * 2 ^ (3 - a) ≤ A := by
    have h6 : 0 ≤ 6 * C / A := by positivity
    refine ⟨3 + 6 * C / A, by linarith, by linarith, ?_⟩
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hbig : 1 + 3 * C / A ≤ (2 : ℝ) ^ (6 * C / A) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have := Real.add_one_le_exp (Real.log 2 * (6 * C / A))
      have : 3 * C / A ≤ Real.log 2 * (6 * C / A) := by
        have h0 : 0 ≤ 6 * C / A := by positivity
        rw [show 3 * C / A = (1 / 2) * (6 * C / A) by ring]
        exact mul_le_mul_of_nonneg_right hlog2 h0
      linarith
    have hpow : (2 : ℝ) ^ (3 - (3 + 6 * C / A)) = ((2 : ℝ) ^ (6 * C / A))⁻¹ := by
      rw [show (3 : ℝ) - (3 + 6 * C / A) = -(6 * C / A) by ring, Real.rpow_neg (by norm_num)]
    rw [hpow]
    have hpos : 0 < (2 : ℝ) ^ (6 * C / A) := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have : 3 * C ≤ A * (1 + 3 * C / A) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hA0.ne']; linarith
    nlinarith
  refine ⟨a + 1 / 2, fun σ hσ => ?_⟩
  apply JasDressedPSD.mono _ hσ
  intro ι t c n hinj
  classical
  set K := jasDressedLagAggregate (a + 1 / 2) with hK
  have hε : (2 : ℝ) ^ (3 - a) ≤ 1 := by
    rw [show (1 : ℝ) = 2 ^ (0 : ℝ) by simp]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [ha3])
  have hzeta := tsum_rpow_inv_le ha2
  have hZ0 : 1 ≤ ∑' k : ℕ, ((k : ℝ) ^ a)⁻¹ := by
    have hsa : Summable fun k : ℕ => ((k : ℝ) ^ a)⁻¹ := Real.summable_nat_rpow_inv.mpr (by linarith)
    have := hsa.le_tsum 1 (fun k _ => by positivity)
    simpa using this
  -- off-diagonal row bound
  have hrow : ∀ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i), ‖K (n i - n j)‖ ≤ A := by
    intro i hi
    have hbound : ∀ j, ‖K (n i - n j)‖ ≤ C * Real.exp (-a * jasLogSize (n i - n j)) := by
      intro j
      have := norm_jasDressedLagAggregate_le (a + 1 / 2) (n i - n j)
      rw [show a + 1 / 2 - 1 / 2 = a by ring] at this
      exact this
    refine (Finset.sum_le_sum fun j _ => hbound j).trans ?_
    rw [← Finset.mul_sum]
    have himg : ∑ j ∈ t.filter (fun j => j ≠ i), Real.exp (-a * jasLogSize (n i - n j)) =
        ∑ m ∈ (t.filter (fun j => j ≠ i)).image (fun j => n i - n j),
          Real.exp (-a * jasLogSize m) := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      exact hinj hx.1 hy.1 (by simpa using hxy)
    rw [himg]
    have h0 : (0 : Nat.Primes →₀ ℤ) ∉ (t.filter (fun j => j ≠ i)).image (fun j => n i - n j) := by
      intro h
      obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp h
      have hj' := Finset.mem_filter.mp hj
      exact hj'.2 (hinj hj'.1 hi (sub_eq_zero.mp hj0).symm)
    have hS := sum_exp_neg_mul_jasLogSize_le (a := a) (by linarith) _ h0
    calc C * ∑ m ∈ (t.filter (fun j => j ≠ i)).image (fun j => n i - n j),
          Real.exp (-a * jasLogSize m)
        ≤ C * ((∑' k : ℕ, ((k : ℝ) ^ a)⁻¹) ^ 2 - 1) := by gcongr
      _ ≤ C * ((1 + 2 ^ (3 - a)) ^ 2 - 1) := by gcongr
      _ ≤ 3 * C * 2 ^ (3 - a) := by
          have hε0 : (0 : ℝ) ≤ 2 ^ (3 - a) := Real.rpow_nonneg (by norm_num) _
          have key : (1 + (2 : ℝ) ^ (3 - a)) ^ 2 - 1 ≤ 3 * 2 ^ (3 - a) := by nlinarith
          calc C * ((1 + 2 ^ (3 - a)) ^ 2 - 1) ≤ C * (3 * 2 ^ (3 - a)) :=
                mul_le_mul_of_nonneg_left key hC0
            _ = 3 * C * 2 ^ (3 - a) := by ring
      _ ≤ A := hsmall
  -- Gershgorin
  have hdiag : ∀ i, K (n i - n i) = (A : ℂ) := by
    intro i; rw [sub_self, hK, jasDressedLagAggregate_zero]
  have hsymm : ∀ i j, ‖K (n j - n i)‖ = ‖K (n i - n j)‖ := by
    intro i j
    rw [show n j - n i = -(n i - n j) by abel, hK, jasDressedLagAggregate_neg]
  have hsplit : ∀ i ∈ t, ∑ j ∈ t, c i * conj (c j) * K (n i - n j) =
      c i * conj (c i) * A + ∑ j ∈ t.filter (fun j => j ≠ i), c i * conj (c j) * K (n i - n j) := by
    intro i hi
    rw [← Finset.add_sum_erase t _ hi, Finset.filter_ne', hdiag]
  have hre : ∀ i ∈ t, ‖c i‖ ^ 2 * A - ∑ j ∈ t.filter (fun j => j ≠ i), ‖c i‖ * ‖c j‖ * ‖K (n i - n j)‖ ≤
      (∑ j ∈ t, c i * conj (c j) * K (n i - n j)).re := by
    intro i hi
    rw [hsplit i hi, Complex.add_re]
    have h1 : (c i * conj (c i) * (A : ℂ)).re = ‖c i‖ ^ 2 * A := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [h1]
    have h2 : -(∑ j ∈ t.filter (fun j => j ≠ i), ‖c i‖ * ‖c j‖ * ‖K (n i - n j)‖) ≤
        (∑ j ∈ t.filter (fun j => j ≠ i), c i * conj (c j) * K (n i - n j)).re := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have := Complex.abs_re_le_norm (c i * conj (c j) * K (n i - n j))
      rw [norm_mul, norm_mul, Complex.norm_conj] at this
      linarith [neg_abs_le (c i * conj (c j) * K (n i - n j)).re]
    linarith
  rw [Complex.re_sum]
  calc (0 : ℝ) ≤ ∑ i ∈ t, (‖c i‖ ^ 2 * A -
        ∑ j ∈ t.filter (fun j => j ≠ i), ‖c i‖ * ‖c j‖ * ‖K (n i - n j)‖) := by
        -- Σ_{i≠j} |c_i||c_j||K| ≤ Σ_i |c_i|² Σ_{j≠i}|K| ≤ A Σ |c_i|²
        have hamgm : ∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i), ‖c i‖ * ‖c j‖ * ‖K (n i - n j)‖ ≤
            ∑ i ∈ t, ‖c i‖ ^ 2 * ∑ j ∈ t.filter (fun j => j ≠ i), ‖K (n i - n j)‖ := by
          have hpt : ∀ i j, ‖c i‖ * ‖c j‖ * ‖K (n i - n j)‖ ≤
              (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖K (n i - n j)‖ := by
            intro i j
            have := norm_nonneg (K (n i - n j))
            nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
          calc ∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i), ‖c i‖ * ‖c j‖ * ‖K (n i - n j)‖
              ≤ ∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i),
                  (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖K (n i - n j)‖ :=
                Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
            _ = ∑ i ∈ t, ‖c i‖ ^ 2 * ∑ j ∈ t.filter (fun j => j ≠ i), ‖K (n i - n j)‖ := by
                have hsw : ∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i), ‖c j‖ ^ 2 * ‖K (n i - n j)‖ =
                    ∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i), ‖c i‖ ^ 2 * ‖K (n i - n j)‖ := by
                  simp_rw [Finset.sum_filter]
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                  split_ifs with h1 h2 h2
                  · rw [hsymm]
                  · exact absurd h1.symm h2
                  · exact absurd h2.symm h1
                  · rfl
                have hhalf : ∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i),
                    (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖K (n i - n j)‖ =
                    (1 / 2) * (∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i), ‖c i‖ ^ 2 * ‖K (n i - n j)‖) +
                    (1 / 2) * (∑ i ∈ t, ∑ j ∈ t.filter (fun j => j ≠ i),
                      ‖c j‖ ^ 2 * ‖K (n i - n j)‖) := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  ring
                rw [hhalf, hsw]
                simp_rw [Finset.mul_sum]
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
        have hrowsum : ∑ i ∈ t, ‖c i‖ ^ 2 * ∑ j ∈ t.filter (fun j => j ≠ i), ‖K (n i - n j)‖ ≤
            ∑ i ∈ t, ‖c i‖ ^ 2 * A :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
        rw [Finset.sum_sub_distrib]
        linarith
    _ ≤ ∑ i ∈ t, (∑ j ∈ t, c i * conj (c j) * K (n i - n j)).re :=
        Finset.sum_le_sum fun i hi => hre i hi

end

end RHTower
