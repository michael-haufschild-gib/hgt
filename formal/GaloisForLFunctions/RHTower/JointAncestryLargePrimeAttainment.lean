import GaloisForLFunctions.RHTower.JointAncestryLargePrimeAbscissa
import GaloisForLFunctions.RHTower.JointAncestryLargePrimeMaximalExclusion
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros
import GaloisForLFunctions.RHTower.PrimeLagLandauWeights
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic

/-!
# Attained large-prime JAS positivity and the pole threshold `σ = 3/2`

`JasDressedPSDAbove X σ` is positivity of the dressed aggregate
`A_σ(u/v) = (uv)^{−σ} Φ(log v − log u)` on rational characters supported on primes `p > X`.
Write `d_ρ = |Re ρ − ½|` and `w_ρ = 1/(ρ(1−ρ))`.

* **Summability criterion** (`exists_jasDressedPSDAbove_of_summable`).  Let `σ₀ > 1`,
  `d_ρ < σ₀ − 1` for every zero, and `Σ_ρ |w_ρ|/(σ₀ − 1 − d_ρ) < ∞`.  Then one `X` gives positivity
  above `X` at every `σ ≥ σ₀`.  A zero contributes at most `|w_ρ| e^{−σ log(uv)} e^{d_ρ|log(v/u)|}`
  to `A_σ(u/v)`, which is `≤ |w_ρ| (u^{−(σ₀−d_ρ)} v^{−σ₀} + u^{−σ₀} v^{−(σ₀−d_ρ)})`.  The numerator and
  the denominator of a character on primes `> X` are each `1` or `> X`.  So the off-diagonal mass of
  a row is at most `Σ_ρ 2|w_ρ| ((1 + T_X(σ₀ − d_ρ))(1 + T_X(σ₀)) − 1)` with `T_X(a) = Σ_{k>X} k^{−a}`.
  This tends to `0` as `X → ∞` by dominated convergence, because `T_0(a) ≤ 1 + 1/(a − 1)`.  Once it
  is below the diagonal `Φ(0) = 2 + γ − log 4π > 0`, diagonal dominance gives positivity.
* **Pole threshold** (`exists_jasDressedPSDAbove_three_halves`).  At `σ₀ = 3/2` the condition reads
  `Σ_ρ |w_ρ|/(½ − d_ρ) < ∞`.  It holds unconditionally: the zero-free region
  `d_ρ ≤ ½ − 1/(58 log|γ_ρ|)` gives `1/(½ − d_ρ) ≤ 58 log|γ_ρ|`, and `Σ_ρ |w_ρ| log(2 + |γ_ρ|)`
  converges.  So a single `X` serves every `σ ≥ 3/2`.  Per-zero phase budgets fail here: zeros near
  `Re s = 1` have widths of order `p^{−(1+κ)}` with no uniform tail over `p > X`.  The zero weights
  pay for them collectively.
* **Attained abscissa for chains** (`isLeast_largePrime_abscissa_of_chain`).  Suppose a half-plane
  bound below `½` holds and the off-line zeros form a chain with supremum `δ*`.  If
  `Σ_ρ |w_ρ|/(δ* − d_ρ) < ∞`, then `1 + δ*` is the least `σ` with large-prime positivity, and it is
  attained.
* **Producer dichotomy** (`jasDressedPSDAbove_zeroFree_or_edge`).  Without any hypothesis,
  positivity above some `X` at `σ ≥ 1` forces `|Re ρ − ½| ≤ σ − 1` for every zero, unless
  `sup |Re ρ − ½| = ½`.  A farthest zero is excluded by the large-prime maximal exclusion, and a
  chain with supremum `< ½` by the chain lower bound under its own half-plane bound.  With the
  summability criterion this is the large-prime producer law (`largePrime_producer_law`).  Below
  `3/2`, a large-prime JAS producer is the same thing as a zero-free strip, up to zeros accumulating
  at `Re s ∈ {0, 1}` and the boundary series.
* **Attainment detects chains** (`largePrime_producer_set_of_farthest`,
  `jasOffLineChain_of_isLeast_largePrime`).  If a farthest off-line zero `ρ₀` exists, the levels with
  large-prime positivity are exactly `σ > 1 + |Re ρ₀ − ½|`.  The endpoint itself fails by the
  maximal exclusion at exponent one.  So off RH, a least level forces the off-line zeros to form a
  chain.  Conversely, a chain with convergent boundary series attains its level.
* **Small primes cost a strict amount** (`lt_jasAbscissa_of_farthest`).  The all-prime abscissa
  `σ*` is attained, so with a farthest zero `σ* > 1 + |Re ρ₀ − ½|`, strictly above the large-prime
  abscissa.  Off RH, `σ* ≤ 1 + sup |Re ρ − ½|` therefore forces a chain
  (`jasOffLineChain_of_jasAbscissa_le_one_add_sSup`).
* **Product tests suffice** (`riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi`,
  `jasDressedPSD_one_of_exists_jasProductPositiveAbove_of_quasi`).  Every exclusion above uses only
  the Bernoulli tests `x ↦ ∏_{p ∈ P} z_p^{x_p}`, `x ∈ {0,1}^P`: rank-one product vectors on
  squarefree characters.  So RH holds iff these product tests are positive on all sufficiently
  large primes at `σ = 1` and some half-plane bound below `½` holds.  Under that bound, positivity
  on product vectors forces positivity on all vectors: the zero operators
  `Σ_ρ w_ρ ⊗_{p ∈ P} M_{ρ,p}` (`M_{ρ,p}` the local `2 × 2` Bernoulli matrices) are positive on all
  vectors as soon as they are positive on product vectors.
* **Single-level large-prime capstone** (`riemannHypothesis_iff_exists_jasDressedPSDAbove_one_and_quasi`).
  RH holds iff some `X` gives positivity on characters of primes `> X` at the single level
  `σ = 1`, and some half-plane bound below `½` holds.  More generally, under a half-plane bound
  below `½`, large-prime positivity at `σ ≥ 1` gives the half-plane bound `σ − 1`
  (`xiZeroHalfPlaneBound_of_jasDressedPSDAbove_of_quasi`).
* **Log-window producer below the pole threshold** (`jasDressedPSD_of_logWindow`,
  `eventually_jasDressedPSD_logWindow`).  For every `σ > 1` and `κ < 2(σ − 1)`, once `X` is large,
  the dressed aggregate is positive on every family of characters of primes `> X` whose pairwise
  log-ratios are at most `κ log X`.  This needs only the strip bound `|Φ(L)| ≤ e^{|L|/2} Σ_ρ |w_ρ|`:
  on a window of log-ratio `a` the zeros cost `e^{a/2}`, and the off-diagonal mass is
  `≤ e^{a/2}((1 + T_X(σ))² − 1)` with `T_X(σ) ≤ X^{1−σ}/(σ − 1)`.  So any detection of off-line
  zeros at a level `σ < 3/2` on large primes needs log-ratios beyond `2(σ − 1) log X`.
* **Few-primes producer at the target level** (`jasDressedPSDOn_of_card_le_sqrt`).  For every
  `σ ≥ 1`, the aggregate is positive on all characters supported on at most `(7/5)√X` primes `> X`,
  with arbitrary exponents.  Each zero's local phase width at `σ = 1` is at most `p^{−1/2} ≤ X^{−1/2}`,
  so the per-zero budget `π/2` holds.  Detecting an off-line zero at `σ = 1` therefore needs more
  than `(7/5)√X` primes above `X`.  At a general level `σ ≥ 1` the same per-zero budget allows
  `(7/10) X^{σ−½}` primes (`jasDressedPSDOn_of_card_le_rpow`), since every local width is at most
  `2p^{−(σ−½)}`.  The count grows to `X` as `σ → 3/2`, where the global producer takes over.
  Under a half-plane bound `Re ρ ≤ ½ + α` the count improves to `(7/10) X^{σ−α}`
  (`jasDressedPSDOn_of_card_le_rpow_of_halfPlane`): a zero-free strip of width `½ − α` raises the
  admissible number of primes by the factor `X^{½−α}`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Diagonal dominance -/

/-- A kernel with constant real diagonal `A`, symmetric moduli, and off-diagonal row sums at most
`A` gives a nonnegative quadratic form. -/
theorem gram_re_nonneg_of_row_le {ι : Type*} [DecidableEq ι] (t : Finset ι) (c : ι → ℂ)
    (K : ι → ι → ℂ) {A : ℝ} (hdiag : ∀ i ∈ t, K i i = A)
    (hsymm : ∀ i ∈ t, ∀ j ∈ t, ‖K j i‖ = ‖K i j‖)
    (hrow : ∀ i ∈ t, ∑ j ∈ t.erase i, ‖K i j‖ ≤ A) :
    0 ≤ (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * K i j).re := by
  have hlow : ∀ i ∈ t, ‖c i‖ ^ 2 * A - ∑ j ∈ t.erase i, ‖c i‖ * ‖c j‖ * ‖K i j‖ ≤
      (∑ j ∈ t, c i * conj (c j) * K i j).re := by
    intro i hi
    rw [← Finset.add_sum_erase t (fun j => c i * conj (c j) * K i j) hi, hdiag i hi,
      Complex.add_re]
    have h1 : (c i * conj (c i) * (A : ℂ)).re = ‖c i‖ ^ 2 * A := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h2 : -(∑ j ∈ t.erase i, ‖c i‖ * ‖c j‖ * ‖K i j‖) ≤
        (∑ j ∈ t.erase i, c i * conj (c j) * K i j).re := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have := Complex.abs_re_le_norm (c i * conj (c j) * K i j)
      rw [norm_mul, norm_mul, Complex.norm_conj] at this
      linarith [neg_abs_le (c i * conj (c j) * K i j).re]
    rw [h1]
    linarith
  have e : ∀ F : ι → ι → ℝ, ∑ i ∈ t, ∑ j ∈ t.erase i, F i j =
      ∑ i ∈ t, ∑ j ∈ t, F i j - ∑ i ∈ t, F i i := by
    intro F
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi => Finset.sum_erase_eq_sub hi
  have hswap : ∑ i ∈ t, ∑ j ∈ t.erase i, ‖c j‖ ^ 2 * ‖K i j‖ =
      ∑ i ∈ t, ∑ j ∈ t.erase i, ‖c i‖ ^ 2 * ‖K i j‖ := by
    rw [e, e, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
      rw [hsymm i hi j hj]
  have hamgm : ∑ i ∈ t, ∑ j ∈ t.erase i, ‖c i‖ * ‖c j‖ * ‖K i j‖ ≤
      ∑ i ∈ t, ‖c i‖ ^ 2 * ∑ j ∈ t.erase i, ‖K i j‖ := by
    have hpt : ∀ i j, ‖c i‖ * ‖c j‖ * ‖K i j‖ ≤
        ‖c i‖ ^ 2 * ‖K i j‖ / 2 + ‖c j‖ ^ 2 * ‖K i j‖ / 2 := by
      intro i j
      have := norm_nonneg (K i j)
      nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
    calc ∑ i ∈ t, ∑ j ∈ t.erase i, ‖c i‖ * ‖c j‖ * ‖K i j‖
        ≤ ∑ i ∈ t, ∑ j ∈ t.erase i, (‖c i‖ ^ 2 * ‖K i j‖ / 2 + ‖c j‖ ^ 2 * ‖K i j‖ / 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
      _ = (∑ i ∈ t, ∑ j ∈ t.erase i, ‖c i‖ ^ 2 * ‖K i j‖ +
            ∑ i ∈ t, ∑ j ∈ t.erase i, ‖c j‖ ^ 2 * ‖K i j‖) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i ∈ t, ‖c i‖ ^ 2 * ∑ j ∈ t.erase i, ‖K i j‖ := by
          rw [hswap, add_self_div_two]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hrowsum : ∑ i ∈ t, ‖c i‖ ^ 2 * ∑ j ∈ t.erase i, ‖K i j‖ ≤ ∑ i ∈ t, ‖c i‖ ^ 2 * A :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
  rw [Complex.re_sum]
  calc (0 : ℝ) ≤ ∑ i ∈ t, (‖c i‖ ^ 2 * A - ∑ j ∈ t.erase i, ‖c i‖ * ‖c j‖ * ‖K i j‖) := by
        rw [Finset.sum_sub_distrib]
        linarith
    _ ≤ _ := Finset.sum_le_sum hlow

/-! ## Numerators and denominators on large primes -/

/-- A product of powers of primes `> X` is `1` or `> X`. -/
theorem prod_prime_pow_eq_one_or_lt {X : ℕ} (s : Finset Nat.Primes) (hs : ∀ p ∈ s, X < (p : ℕ))
    (e : Nat.Primes → ℕ) : ∏ p ∈ s, (p : ℕ) ^ e p = 1 ∨ X < ∏ p ∈ s, (p : ℕ) ^ e p := by
  by_cases h : ∀ p ∈ s, e p = 0
  · exact Or.inl (Finset.prod_eq_one fun p hp => by rw [h p hp, pow_zero])
  · simp only [not_forall] at h
    obtain ⟨p, hp, hep⟩ := h
    exact Or.inr ((hs p hp).trans_le ((Nat.le_self_pow hep _).trans
      (Finset.single_le_prod' (fun r _ => Nat.one_le_pow _ _ r.2.pos) hp)))

theorem jasNum_eq_one_or_lt {X : ℕ} {n : Nat.Primes →₀ ℤ} (hn : ∀ p ∈ n.support, X < (p : ℕ)) :
    jasNum n = 1 ∨ X < jasNum n :=
  prod_prime_pow_eq_one_or_lt n.support hn fun p => (n p).toNat

theorem jasDen_eq_one_or_lt {X : ℕ} {n : Nat.Primes →₀ ℤ} (hn : ∀ p ∈ n.support, X < (p : ℕ)) :
    jasDen n = 1 ∨ X < jasDen n :=
  prod_prime_pow_eq_one_or_lt n.support hn fun p => (-(n p)).toNat

theorem log_jasNum (n : Nat.Primes →₀ ℤ) : Real.log (jasNum n : ℝ) = jasLogPos n := by
  unfold jasNum jasLogPos Finsupp.prod Finsupp.sum
  push_cast
  rw [Real.log_prod (fun p _ => pow_ne_zero _ (by exact_mod_cast p.2.ne_zero))]
  exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]

theorem log_jasDen (n : Nat.Primes →₀ ℤ) : Real.log (jasDen n : ℝ) = jasLogNeg n := by
  unfold jasDen jasLogNeg Finsupp.prod Finsupp.sum
  push_cast
  rw [Real.log_prod (fun p _ => pow_ne_zero _ (by exact_mod_cast p.2.ne_zero))]
  exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]

/-- `k ↦ k^{−a}`. -/
def jasInvPow (a : ℝ) (k : ℕ) : ℝ := ((k : ℝ) ^ a)⁻¹

theorem jasInvPow_nonneg (a : ℝ) (k : ℕ) : 0 ≤ jasInvPow a k := by
  unfold jasInvPow; positivity

theorem jasInvPow_one (a : ℝ) : jasInvPow a 1 = 1 := by simp [jasInvPow]

theorem jasInvPow_le_one {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 1 ≤ k) : jasInvPow a k ≤ 1 :=
  inv_le_one_of_one_le₀ (Real.one_le_rpow (by exact_mod_cast hk) ha)

theorem summable_jasInvPow {a : ℝ} (ha : 1 < a) : Summable (jasInvPow a) :=
  Real.summable_nat_rpow_inv.mpr ha

theorem exp_neg_mul_jasLogPos (a : ℝ) (n : Nat.Primes →₀ ℤ) :
    Real.exp (-a * jasLogPos n) = jasInvPow a (jasNum n) := by
  rw [jasInvPow, Real.rpow_def_of_pos (by exact_mod_cast jasNum_pos n), log_jasNum,
    ← Real.exp_neg]
  congr 1
  ring

theorem exp_neg_mul_jasLogNeg (a : ℝ) (n : Nat.Primes →₀ ℤ) :
    Real.exp (-a * jasLogNeg n) = jasInvPow a (jasDen n) := by
  rw [jasInvPow, Real.rpow_def_of_pos (by exact_mod_cast jasDen_pos n), log_jasDen,
    ← Real.exp_neg]
  congr 1
  ring

/-! ## Tails -/

/-- The tail `Σ_{k > X} f k`. -/
def largePrimeTail (f : ℕ → ℝ) (X : ℕ) : ℝ := ∑' k : ℕ, f (k + (X + 1))

theorem largePrimeTail_nonneg {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (X : ℕ) :
    0 ≤ largePrimeTail f X :=
  tsum_nonneg fun _ => hf0 _

/-- A finite sum over integers `> X` is bounded by the tail. -/
theorem sum_le_largePrimeTail {X : ℕ} {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hfs : Summable f)
    (s : Finset ℕ) (hs : ∀ k ∈ s, X < k) : ∑ k ∈ s, f k ≤ largePrimeTail f X := by
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℝ, ∀ k, h k = if X < k then f k else 0 := ⟨_, fun _ => rfl⟩
  have hh0 : ∀ k, 0 ≤ h k := fun k => by
    rw [hh]; split_ifs
    · exact hf0 k
    · exact le_rfl
  have hhs : Summable h := hfs.of_nonneg_of_le hh0 fun k => by
    rw [hh]; split_ifs
    · exact le_rfl
    · exact hf0 k
  have h1 : ∑ k ∈ s, f k = ∑ k ∈ s, h k :=
    Finset.sum_congr rfl fun k hk => by rw [hh, if_pos (hs k hk)]
  have h2 := hhs.sum_add_tsum_nat_add (X + 1)
  have h3 : ∑ i ∈ Finset.range (X + 1), h i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have := Finset.mem_range.mp hi
      rw [hh, if_neg (by omega)]
  have h4 : ∑' i : ℕ, h (i + (X + 1)) = largePrimeTail f X :=
    tsum_congr fun i => by rw [hh, if_pos (by omega)]
  rw [h1]
  calc ∑ k ∈ s, h k ≤ ∑' k, h k := hhs.sum_le_tsum s fun k _ => hh0 k
    _ = largePrimeTail f X := by rw [← h2, h3, zero_add, h4]

theorem tendsto_largePrimeTail (f : ℕ → ℝ) :
    Tendsto (largePrimeTail f) atTop (𝓝 0) := by
  have := (tendsto_sum_nat_add f).comp (Filter.tendsto_add_atTop_nat 1)
  exact this.congr fun X => rfl

/-- `T_X(a) ≤ ζ(a) ≤ 1 + 1/(a − 1)`. -/
theorem largePrimeTail_jasInvPow_le {a : ℝ} (ha : 1 < a) (X : ℕ) :
    largePrimeTail (jasInvPow a) X ≤ 1 + 1 / (a - 1) := by
  have hs := summable_jasInvPow ha
  have hs1 : Summable fun k : ℕ => jasInvPow a (k + 1) := (summable_nat_add_iff 1).mpr hs
  have hsX : Summable fun k : ℕ => jasInvPow a (k + (X + 1)) := (summable_nat_add_iff (X + 1)).mpr hs
  have hmono : ∀ k : ℕ, jasInvPow a (k + (X + 1)) ≤ jasInvPow a (k + 1) := fun k => by
    unfold jasInvPow
    have h0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hle : ((k + 1 : ℕ) : ℝ) ≤ ((k + (X + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega)
    exact inv_anti₀ (Real.rpow_pos_of_pos h0 a) (Real.rpow_le_rpow h0.le hle (by linarith))
  have hshift : ∑' k : ℕ, jasInvPow a (k + 1) ≤ ∑' k : ℕ, jasInvPow a k := by
    have h := hs.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    linarith [jasInvPow_nonneg a 0]
  have hzeta : ∑' k : ℕ, jasInvPow a k = ∑' k : ℕ, (k : ℝ) ^ (-a) :=
    tsum_congr fun k => by rw [jasInvPow, Real.rpow_neg (Nat.cast_nonneg k)]
  calc largePrimeTail (jasInvPow a) X ≤ ∑' k : ℕ, jasInvPow a (k + 1) :=
        Summable.tsum_le_tsum hmono hsX hs1
    _ ≤ ∑' k : ℕ, jasInvPow a k := hshift
    _ ≤ 1 + 1 / (a - 1) := by rw [hzeta]; exact Sieve.tsum_nat_rpow_neg_le ha

/-! ## Pair sums over numerators and denominators -/

/-- Over distinct nontrivial characters on primes `> X`,
`Σ f(u) g(v) ≤ (1 + T_X f)(1 + T_X g) − 1`. -/
theorem sum_jasNum_jasDen_le {X : ℕ} (M : Finset (Nat.Primes →₀ ℤ))
    (hM0 : (0 : Nat.Primes →₀ ℤ) ∉ M) (hMX : ∀ m ∈ M, ∀ p ∈ m.support, X < (p : ℕ))
    {f g : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k) (hf1 : f 1 = 1) (hg1 : g 1 = 1)
    (hfs : Summable f) (hgs : Summable g) :
    ∑ m ∈ M, f (jasNum m) * g (jasDen m) ≤
      (1 + largePrimeTail f X) * (1 + largePrimeTail g X) - 1 := by
  classical
  have hsumZ : ∑ m ∈ M, f (jasNum m) * g (jasDen m) =
      ∑ z ∈ M.image (fun m => (jasNum m, jasDen m)), f z.1 * g z.2 := by
    rw [Finset.sum_image fun x _ y _ h => jasNum_jasDen_injective h]
  have h11 : ((1 : ℕ), (1 : ℕ)) ∉ M.image (fun m => (jasNum m, jasDen m)) := by
    intro h
    obtain ⟨m, hm, hm11⟩ := Finset.mem_image.mp h
    exact jasNum_jasDen_ne_one_one (fun h0 => hM0 (h0 ▸ hm)) hm11
  have hAX : ∀ k ∈ ((M.image (fun m => (jasNum m, jasDen m))).image Prod.fst).erase 1, X < k := by
    intro k hk
    obtain ⟨hk1, hk⟩ := Finset.mem_erase.mp hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
    exact (jasNum_eq_one_or_lt (hMX m hm)).resolve_left hk1
  have hBX : ∀ k ∈ ((M.image (fun m => (jasNum m, jasDen m))).image Prod.snd).erase 1, X < k := by
    intro k hk
    obtain ⟨hk1, hk⟩ := Finset.mem_erase.mp hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
    exact (jasDen_eq_one_or_lt (hMX m hm)).resolve_left hk1
  set Z := M.image (fun m => (jasNum m, jasDen m))
  set A := (Z.image Prod.fst).erase 1
  set B := (Z.image Prod.snd).erase 1
  have hsub : insert (1, 1) Z ⊆ (insert 1 A) ×ˢ (insert 1 B) := by
    intro z hz
    rw [Finset.mem_product]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    · constructor
      · by_cases h1 : z.1 = 1
        · rw [h1]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h1, Finset.mem_image_of_mem _ hz⟩)
      · by_cases h1 : z.2 = 1
        · rw [h1]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h1, Finset.mem_image_of_mem _ hz⟩)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z : ℕ × ℕ => f z.1 * g z.2) hsub
    fun z _ _ => mul_nonneg (hf0 _) (hg0 _)
  have hprod : ∑ z ∈ (insert 1 A) ×ˢ (insert 1 B), f z.1 * g z.2 =
      (∑ k ∈ insert 1 A, f k) * ∑ k ∈ insert 1 B, g k := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  rw [hprod, Finset.sum_insert h11, Finset.sum_insert (Finset.notMem_erase 1 _),
    Finset.sum_insert (Finset.notMem_erase 1 _), hf1, hg1] at hle
  have hTA := sum_le_largePrimeTail hf0 hfs A hAX
  have hTB := sum_le_largePrimeTail hg0 hgs B hBX
  have hB0 : 0 ≤ ∑ k ∈ B, g k := Finset.sum_nonneg fun k _ => hg0 k
  have hTA0 := largePrimeTail_nonneg hf0 X
  have hmul : (1 + ∑ k ∈ A, f k) * (1 + ∑ k ∈ B, g k) ≤
      (1 + largePrimeTail f X) * (1 + largePrimeTail g X) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  rw [hsumZ]
  simp only [one_mul] at hle
  linarith

/-! ## The zero-side bound -/

/-- The leaning exponent `σ₀ − d_ρ`. -/
def jasLeanExp (σ₀ : ℝ) (q : XiZeroCopy) : ℝ := σ₀ - |(q.1 : ℂ).re - 1 / 2|

/-- The contribution bound of one zero to the aggregate at a character with numerator `u` and
denominator `v`: `|w_ρ| (u^{−(σ₀−d_ρ)} v^{−σ₀} + u^{−σ₀} v^{−(σ₀−d_ρ)})`. -/
def jasLargePrimeZeroTerm (σ₀ : ℝ) (n : Nat.Primes →₀ ℤ) (q : XiZeroCopy) : ℝ :=
  ‖lagWeight q‖ * (jasInvPow (jasLeanExp σ₀ q) (jasNum n) * jasInvPow σ₀ (jasDen n) +
    jasInvPow σ₀ (jasNum n) * jasInvPow (jasLeanExp σ₀ q) (jasDen n))

/-- The row bound of one zero: `2|w_ρ|((1 + T_X(σ₀ − d_ρ))(1 + T_X(σ₀)) − 1)`. -/
def jasLargePrimeZeroBound (σ₀ : ℝ) (X : ℕ) (q : XiZeroCopy) : ℝ :=
  ‖lagWeight q‖ * (2 * ((1 + largePrimeTail (jasInvPow (jasLeanExp σ₀ q)) X) *
    (1 + largePrimeTail (jasInvPow σ₀) X) - 1))

/-- `‖e^{L(ρ−½)}/(ρ(1−ρ))‖ ≤ e^{d_ρ |L|} |w_ρ|`. -/
theorem norm_weilLagTerm_le_exp_abs (L : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      Real.exp (|(q.1 : ℂ).re - 1 / 2| * |L|) * ‖lagWeight q‖ := by
  rw [div_eq_mul_one_div, norm_mul, Complex.norm_exp, lagWeight]
  gcongr
  have hre : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * (((q.1 : ℂ)).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [hre]
  calc L * ((q.1 : ℂ).re - 1 / 2) ≤ |L * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |(q.1 : ℂ).re - 1 / 2| * |L| := by rw [abs_mul, mul_comm]

/-- `e^{−σ(P+N)} e^{d|N−P|} ≤ e^{−(σ₀−d)P} e^{−σ₀N} + e^{−σ₀P} e^{−(σ₀−d)N}` for `σ ≥ σ₀`. -/
theorem exp_dressed_split_le {σ₀ σ d P N : ℝ} (hσ : σ₀ ≤ σ) (hd : 0 ≤ d) (hP : 0 ≤ P)
    (hN : 0 ≤ N) :
    Real.exp (-σ * (P + N)) * Real.exp (d * |N - P|) ≤
      Real.exp (-(σ₀ - d) * P) * Real.exp (-σ₀ * N) +
        Real.exp (-σ₀ * P) * Real.exp (-(σ₀ - d) * N) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have h1 := mul_nonneg (sub_nonneg.2 hσ) (add_nonneg hP hN)
  rcases le_total N P with h | h
  · have : -σ * (P + N) + d * |N - P| ≤ -(σ₀ - d) * P + -σ₀ * N := by
      rw [abs_of_nonpos (by linarith)]
      nlinarith [mul_nonneg hd hN]
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have : -σ * (P + N) + d * |N - P| ≤ -σ₀ * P + -(σ₀ - d) * N := by
      rw [abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg hd hP]
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

theorem jasLargePrimeZeroTerm_le {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    (hd : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < σ₀ - 1) (n : Nat.Primes →₀ ℤ)
    (q : XiZeroCopy) : jasLargePrimeZeroTerm σ₀ n q ≤ 2 * ‖lagWeight q‖ := by
  have hlean : 0 ≤ jasLeanExp σ₀ q := by unfold jasLeanExp; linarith [hd q]
  have hu := jasInvPow_le_one hlean (jasNum_pos n)
  have hv := jasInvPow_le_one hlean (jasDen_pos n)
  have hu' := jasInvPow_le_one (by linarith : (0 : ℝ) ≤ σ₀) (jasNum_pos n)
  have hv' := jasInvPow_le_one (by linarith : (0 : ℝ) ≤ σ₀) (jasDen_pos n)
  have h1 : jasInvPow (jasLeanExp σ₀ q) (jasNum n) * jasInvPow σ₀ (jasDen n) ≤ 1 :=
    mul_le_one₀ hu (jasInvPow_nonneg _ _) hv'
  have h2 : jasInvPow σ₀ (jasNum n) * jasInvPow (jasLeanExp σ₀ q) (jasDen n) ≤ 1 :=
    mul_le_one₀ hu' (jasInvPow_nonneg _ _) hv
  unfold jasLargePrimeZeroTerm
  nlinarith [norm_nonneg (lagWeight q)]

theorem summable_jasLargePrimeZeroTerm {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    (hd : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < σ₀ - 1) (n : Nat.Primes →₀ ℤ) :
    Summable (jasLargePrimeZeroTerm σ₀ n) :=
  (summable_norm_lagWeight.mul_left 2).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (add_nonneg
      (mul_nonneg (jasInvPow_nonneg _ _) (jasInvPow_nonneg _ _))
      (mul_nonneg (jasInvPow_nonneg _ _) (jasInvPow_nonneg _ _))))
    (jasLargePrimeZeroTerm_le hσ₀ hd n)

/-- Each aggregate value is bounded by the zero sum of the contribution bounds. -/
theorem norm_jasDressedLagAggregate_le_tsum {σ₀ σ : ℝ} (hσ₀ : 1 < σ₀) (hσ : σ₀ ≤ σ)
    (hd : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < σ₀ - 1) (n : Nat.Primes →₀ ℤ) :
    ‖jasDressedLagAggregate σ n‖ ≤ ∑' q : XiZeroCopy, jasLargePrimeZeroTerm σ₀ n q := by
  set L := jasLogNeg n - jasLogPos n
  have hΦ : ‖weilLagFunction L‖ ≤ ∑' q : XiZeroCopy,
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    norm_tsum_le_tsum_norm (summable_weilLagTerm L).norm
  rw [jasDressedLagAggregate, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine (mul_le_mul_of_nonneg_left hΦ (Real.exp_pos _).le).trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun q => ?_) ((summable_weilLagTerm L).norm.mul_left _)
    (summable_jasLargePrimeZeroTerm hσ₀ hd n)
  have hP := jasLogPos_nonneg n
  have hN := jasLogNeg_nonneg n
  have hsplit := exp_dressed_split_le hσ (abs_nonneg ((q.1 : ℂ).re - 1 / 2)) hP hN
  rw [exp_neg_mul_jasLogPos, exp_neg_mul_jasLogNeg, exp_neg_mul_jasLogPos,
    exp_neg_mul_jasLogNeg] at hsplit
  have hterm := norm_weilLagTerm_le_exp_abs L q
  have hLabs : |L| = |jasLogNeg n - jasLogPos n| := rfl
  calc Real.exp (-σ * jasLogSize n) *
        ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
      ≤ Real.exp (-σ * jasLogSize n) *
          (Real.exp (|(q.1 : ℂ).re - 1 / 2| * |L|) * ‖lagWeight q‖) :=
        mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
    _ = ‖lagWeight q‖ * (Real.exp (-σ * (jasLogPos n + jasLogNeg n)) *
          Real.exp (|(q.1 : ℂ).re - 1 / 2| * |jasLogNeg n - jasLogPos n|)) := by
        rw [jasLogSize, hLabs]; ring
    _ ≤ jasLargePrimeZeroTerm σ₀ n q := by
        unfold jasLargePrimeZeroTerm jasLeanExp
        exact mul_le_mul_of_nonneg_left hsplit (norm_nonneg _)

/-- The off-diagonal mass of a large-prime row is bounded by `Σ_ρ` of the row bounds. -/
theorem sum_norm_jasDressedLagAggregate_le {σ₀ σ : ℝ} (hσ₀ : 1 < σ₀) (hσ : σ₀ ≤ σ)
    (hd : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < σ₀ - 1) {X : ℕ}
    (hB : Summable (jasLargePrimeZeroBound σ₀ X)) (M : Finset (Nat.Primes →₀ ℤ))
    (hM0 : (0 : Nat.Primes →₀ ℤ) ∉ M) (hMX : ∀ m ∈ M, ∀ p ∈ m.support, X < (p : ℕ)) :
    ∑ m ∈ M, ‖jasDressedLagAggregate σ m‖ ≤ ∑' q, jasLargePrimeZeroBound σ₀ X q := by
  have hFs := summable_jasLargePrimeZeroTerm hσ₀ hd
  calc ∑ m ∈ M, ‖jasDressedLagAggregate σ m‖
      ≤ ∑ m ∈ M, ∑' q, jasLargePrimeZeroTerm σ₀ m q :=
        Finset.sum_le_sum fun m _ => norm_jasDressedLagAggregate_le_tsum hσ₀ hσ hd m
    _ = ∑' q, ∑ m ∈ M, jasLargePrimeZeroTerm σ₀ m q :=
        (Summable.tsum_finsetSum fun m _ => hFs m).symm
    _ ≤ ∑' q, jasLargePrimeZeroBound σ₀ X q := by
        refine Summable.tsum_le_tsum (fun q => ?_) (summable_sum fun m _ => hFs m) hB
        have hlean : 1 < jasLeanExp σ₀ q := by unfold jasLeanExp; linarith [hd q]
        have hf0 := jasInvPow_nonneg (jasLeanExp σ₀ q)
        have hg0 := jasInvPow_nonneg σ₀
        have h1 := sum_jasNum_jasDen_le M hM0 hMX hf0 hg0 (jasInvPow_one _) (jasInvPow_one _)
          (summable_jasInvPow hlean) (summable_jasInvPow hσ₀)
        have h2 := sum_jasNum_jasDen_le M hM0 hMX hg0 hf0 (jasInvPow_one _) (jasInvPow_one _)
          (summable_jasInvPow hσ₀) (summable_jasInvPow hlean)
        have hsum : ∑ m ∈ M, jasLargePrimeZeroTerm σ₀ m q = ‖lagWeight q‖ *
            (∑ m ∈ M, jasInvPow (jasLeanExp σ₀ q) (jasNum m) * jasInvPow σ₀ (jasDen m) +
              ∑ m ∈ M, jasInvPow σ₀ (jasNum m) * jasInvPow (jasLeanExp σ₀ q) (jasDen m)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          rfl
        rw [hsum]
        unfold jasLargePrimeZeroBound
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        linarith

/-- Domination of the row bounds, uniformly in `X`. -/
theorem jasLargePrimeZeroBound_le {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    (hd : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < σ₀ - 1) (X : ℕ) (q : XiZeroCopy) :
    jasLargePrimeZeroBound σ₀ X q ≤
      ‖lagWeight q‖ * (4 * (2 + 1 / (σ₀ - 1))) +
        2 * (2 + 1 / (σ₀ - 1)) * (‖lagWeight q‖ / (σ₀ - 1 - |(q.1 : ℂ).re - 1 / 2|)) := by
  have hlean : 1 < jasLeanExp σ₀ q := by unfold jasLeanExp; linarith [hd q]
  have hTf := largePrimeTail_jasInvPow_le hlean X
  have hTg := largePrimeTail_jasInvPow_le hσ₀ X
  have hTf0 := largePrimeTail_nonneg (jasInvPow_nonneg (jasLeanExp σ₀ q)) X
  have hTg0 := largePrimeTail_nonneg (jasInvPow_nonneg σ₀) X
  have hκ : jasLeanExp σ₀ q - 1 = σ₀ - 1 - |(q.1 : ℂ).re - 1 / 2| := by unfold jasLeanExp; ring
  rw [hκ] at hTf
  set κ := σ₀ - 1 - |(q.1 : ℂ).re - 1 / 2|
  have hκ0 : 0 < κ := by linarith [hd q]
  have hc0 : 0 < 1 / (σ₀ - 1) := by have : 0 < σ₀ - 1 := by linarith
                                    positivity
  have hk0 : 0 < 1 / κ := by positivity
  have hW := norm_nonneg (lagWeight q)
  have hprod : (1 + largePrimeTail (jasInvPow (jasLeanExp σ₀ q)) X) *
      (1 + largePrimeTail (jasInvPow σ₀) X) ≤ (2 + 1 / κ) * (2 + 1 / (σ₀ - 1)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  unfold jasLargePrimeZeroBound
  have hdiv : ‖lagWeight q‖ / κ = ‖lagWeight q‖ * (1 / κ) := by ring
  rw [hdiv]
  nlinarith [mul_le_mul_of_nonneg_left hprod hW]

theorem jasLargePrimeZeroBound_nonneg (σ₀ : ℝ) (X : ℕ) (q : XiZeroCopy) :
    0 ≤ jasLargePrimeZeroBound σ₀ X q := by
  have hTf0 := largePrimeTail_nonneg (jasInvPow_nonneg (jasLeanExp σ₀ q)) X
  have hTg0 := largePrimeTail_nonneg (jasInvPow_nonneg σ₀) X
  unfold jasLargePrimeZeroBound
  refine mul_nonneg (norm_nonneg _) ?_
  nlinarith [mul_nonneg hTf0 hTg0]

/-! ## The criterion and the pole threshold -/

/-- **Summability criterion for large-prime positivity.**  If `σ₀ > 1`, every zero has
`|Re ρ − ½| < σ₀ − 1`, and `Σ_ρ |w_ρ|/(σ₀ − 1 − |Re ρ − ½|) < ∞`, then a single `X` gives
positivity on characters of primes `> X` at every `σ ≥ σ₀`. -/
theorem exists_jasDressedPSDAbove_of_summable {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    (hd : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < σ₀ - 1)
    (hsum : Summable fun q : XiZeroCopy =>
      ‖lagWeight q‖ / (σ₀ - 1 - |(q.1 : ℂ).re - 1 / 2|)) :
    ∃ X : ℕ, ∀ σ : ℝ, σ₀ ≤ σ → JasDressedPSDAbove X σ := by
  have hdom : Summable fun q : XiZeroCopy =>
      ‖lagWeight q‖ * (4 * (2 + 1 / (σ₀ - 1))) +
        2 * (2 + 1 / (σ₀ - 1)) * (‖lagWeight q‖ / (σ₀ - 1 - |(q.1 : ℂ).re - 1 / 2|)) :=
    (summable_norm_lagWeight.mul_right _).add (hsum.mul_left _)
  have hBs : ∀ X, Summable (jasLargePrimeZeroBound σ₀ X) := fun X =>
    hdom.of_nonneg_of_le (jasLargePrimeZeroBound_nonneg σ₀ X) (jasLargePrimeZeroBound_le hσ₀ hd X)
  have htend : Tendsto (fun X : ℕ => ∑' q, jasLargePrimeZeroBound σ₀ X q) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun X q => jasLargePrimeZeroBound σ₀ X q)
      (g := fun _ => (0 : ℝ)) hdom (fun q => ?_) (Eventually.of_forall fun X q => by
        rw [Real.norm_of_nonneg (jasLargePrimeZeroBound_nonneg σ₀ X q)]
        exact jasLargePrimeZeroBound_le hσ₀ hd X q)
    · simpa using h
    · have hf := tendsto_largePrimeTail (jasInvPow (jasLeanExp σ₀ q))
      have hg := tendsto_largePrimeTail (jasInvPow σ₀)
      have hlim : Tendsto (fun X : ℕ => jasLargePrimeZeroBound σ₀ X q) atTop
          (𝓝 (‖lagWeight q‖ * (2 * ((1 + 0) * (1 + 0) - 1)))) := by
        unfold jasLargePrimeZeroBound
        exact ((((tendsto_const_nhds.add hf).mul (tendsto_const_nhds.add hg)).sub
          tendsto_const_nhds).const_mul 2).const_mul _
      simpa using hlim
  obtain ⟨X, hX⟩ := (htend.eventually (gt_mem_nhds poleSharpConstant_pos)).exists
  refine ⟨X, fun σ hσ S hS ι t c n hinj hsupp => ?_⟩
  classical
  refine gram_re_nonneg_of_row_le t c (fun i j => jasDressedLagAggregate σ (n i - n j))
    (A := poleSharpConstant) (fun i _ => by rw [sub_self, jasDressedLagAggregate_zero])
    (fun i _ j _ => by
      rw [show n j - n i = -(n i - n j) by abel, jasDressedLagAggregate_neg]) (fun i hi => ?_)
  have himg : ∑ j ∈ t.erase i, ‖jasDressedLagAggregate σ (n i - n j)‖ =
      ∑ m ∈ (t.erase i).image (fun j => n i - n j), ‖jasDressedLagAggregate σ m‖ := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hinj (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy)
      (sub_right_injective hxy)
  have hM0 : (0 : Nat.Primes →₀ ℤ) ∉ (t.erase i).image (fun j => n i - n j) := by
    intro h
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp h
    obtain ⟨hji, hjt⟩ := Finset.mem_erase.mp hj
    exact hji (hinj hjt hi (sub_eq_zero.mp hj0).symm)
  have hMX : ∀ m ∈ (t.erase i).image (fun j => n i - n j), ∀ p ∈ m.support, X < (p : ℕ) := by
    intro m hm p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    have hjt := Finset.mem_of_mem_erase hj
    rcases Finset.mem_union.mp (Finsupp.support_sub hp) with h | h
    · exact hS p (hsupp i hi h)
    · exact hS p (hsupp j hjt h)
  rw [himg]
  exact (sum_norm_jasDressedLagAggregate_le hσ₀ hσ hd (hBs X) _ hM0 hMX).trans hX.le

/-- The two-sided zero-free region for every zero copy. -/
theorem xiZeroCopy_two_sided_zero_free (q : XiZeroCopy) :
    4 ≤ |(q.1 : ℂ).im| ∧ 1 / 58 / Real.log |(q.1 : ℂ).im| ≤ (q.1 : ℂ).re ∧
      (q.1 : ℂ).re ≤ 1 - 1 / 58 / Real.log |(q.1 : ℂ).im| := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hxi := xi_eq_zero_of_mem_divisor_support q.1
  have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h] at hstrip; simp at hstrip
  have hzeta : riemannZeta (q.1 : ℂ) = 0 := (xi_eq_zero_iff hstrip.1 hne1).1 hxi
  exact ⟨four_le_abs_im_of_zeta_zero hstrip.1 hstrip.2 hzeta,
    one_div_le_re_of_zeta_zero hstrip.1 hstrip.2 hzeta,
    re_le_one_sub_of_zeta_zero hstrip.1 hstrip.2 hzeta⟩

/-- **Large-prime positivity at the pole threshold.**  A single `X` gives positivity of the dressed
aggregate on characters of primes `> X` at every `σ ≥ 3/2`. -/
theorem exists_jasDressedPSDAbove_three_halves :
    ∃ X : ℕ, ∀ σ : ℝ, 3 / 2 ≤ σ → JasDressedPSDAbove X σ := by
  have hκ : ∀ q : XiZeroCopy, 1 / 58 / Real.log |(q.1 : ℂ).im| ≤
      3 / 2 - 1 - |(q.1 : ℂ).re - 1 / 2| ∧ 0 < Real.log |(q.1 : ℂ).im| := by
    intro q
    obtain ⟨h4, hlo, hhi⟩ := xiZeroCopy_two_sided_zero_free q
    refine ⟨?_, Real.log_pos (by linarith)⟩
    rcases abs_cases ((q.1 : ℂ).re - 1 / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  refine exists_jasDressedPSDAbove_of_summable (by norm_num) (fun q => ?_) ?_
  · obtain ⟨h1, h2⟩ := hκ q
    have : 0 < 1 / 58 / Real.log |(q.1 : ℂ).im| := by positivity
    linarith
  · refine (summable_lagWeight_mul_log.mul_left 58).of_nonneg_of_le (fun q => ?_) (fun q => ?_)
    · obtain ⟨h1, h2⟩ := hκ q
      have : 0 < 1 / 58 / Real.log |(q.1 : ℂ).im| := by positivity
      exact div_nonneg (norm_nonneg _) (by linarith)
    · obtain ⟨h1, h2⟩ := hκ q
      have hpos : 0 < 1 / 58 / Real.log |(q.1 : ℂ).im| := by positivity
      have hκ0 : 0 < 3 / 2 - 1 - |(q.1 : ℂ).re - 1 / 2| := by linarith
      have hinv : 1 / (3 / 2 - 1 - |(q.1 : ℂ).re - 1 / 2|) ≤ 58 * Real.log |(q.1 : ℂ).im| := by
        rw [div_le_iff₀ hκ0]
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 58 * Real.log |(q.1 : ℂ).im|)
        rw [show 58 * Real.log |(q.1 : ℂ).im| * (1 / 58 / Real.log |(q.1 : ℂ).im|) = 1 by
          field_simp] at this
        linarith
      have hlog : Real.log |(q.1 : ℂ).im| ≤ Real.log (2 + |zeroOrdinate q|) :=
        Real.log_le_log (by linarith [(xiZeroCopy_two_sided_zero_free q).1]) (by
          unfold zeroOrdinate; linarith)
      have hW := norm_nonneg (lagWeight q)
      calc ‖lagWeight q‖ / (3 / 2 - 1 - |(q.1 : ℂ).re - 1 / 2|)
          = ‖lagWeight q‖ * (1 / (3 / 2 - 1 - |(q.1 : ℂ).re - 1 / 2|)) := by ring
        _ ≤ ‖lagWeight q‖ * (58 * Real.log (2 + |zeroOrdinate q|)) :=
            mul_le_mul_of_nonneg_left (hinv.trans (by linarith)) hW
        _ = 58 * (‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)) := by ring

/-- **Attained large-prime abscissa for chains.**  Under a half-plane bound below `½`, if the
off-line zeros form a chain with supremum distance `δ*` and `Σ_ρ |w_ρ|/(δ* − |Re ρ − ½|) < ∞`, then
`1 + δ*` is the least level with large-prime positivity. -/
theorem isLeast_largePrime_abscissa_of_chain {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) (hch : JasOffLineChain)
    (hsum : Summable fun q : XiZeroCopy => ‖lagWeight q‖ /
      (sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) -
        |(q.1 : ℂ).re - 1 / 2|)) :
    IsLeast {σ : ℝ | ∃ X : ℕ, JasDressedPSDAbove X σ}
      (1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|)) := by
  set δ := sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|)
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨q, rfl⟩
    have h0 := xiZeroCopy_re_pos q
    have h1 := xiZeroCopy_re_lt_one q
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hle : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ := fun q =>
    le_csSup hbdd ⟨q, rfl⟩
  have hlt : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < δ := by
    intro q
    by_cases hq : (q.1 : ℂ).re = 1 / 2
    · obtain ⟨q₁, hq₁⟩ := hch.1
      have hpos : 0 < |(q₁.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hq₁)
      rw [hq, sub_self, abs_zero]
      exact hpos.trans_le (hle q₁)
    · obtain ⟨q', hq'⟩ := hch.2 q hq
      exact hq'.trans_le (hle q')
  have hδ0 : 0 < δ := by
    obtain ⟨q₁, _⟩ := hch.1
    exact (abs_nonneg _).trans_lt (hlt q₁)
  refine ⟨?_, fun σ ⟨X, hX⟩ => one_add_sSup_le_of_jasDressedPSDAbove_of_chain halpha0 halpha hXi
    hX hch⟩
  obtain ⟨X, hX⟩ := exists_jasDressedPSDAbove_of_summable (σ₀ := 1 + δ) (by linarith)
    (fun q => by linarith [hlt q]) (hsum.congr fun q => by ring_nf)
  exact ⟨X, hX _ le_rfl⟩

/-- **Producer dichotomy for product tests.**  Positivity of the Bernoulli product tests on primes
`> X` at a level `σ ≥ 1` forces `|Re ρ − ½| ≤ σ − 1` for every zero, unless the zeros accumulate
at `Re s ∈ {0, 1}`. -/
theorem jasProductPositiveAbove_zeroFree_or_edge {X : ℕ} {σ : ℝ} (hσ : 1 ≤ σ)
    (h : JasProductPositiveAbove X σ) :
    (∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ σ - 1) ∨
      sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) = 1 / 2 := by
  set δ := sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|)
  have hhalf : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := fun q => by
    have h0 := xiZeroCopy_re_pos q
    have h1 := xiZeroCopy_re_lt_one q
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨1 / 2, by rintro _ ⟨q, rfl⟩; exact hhalf q⟩
  have hle : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ := fun q => le_csSup hbdd ⟨q, rfl⟩
  have hδ : δ ≤ 1 / 2 := csSup_le (Set.range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact hhalf q)
  by_cases hon : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2
  · left
    intro q
    rw [hon q, sub_self, abs_zero]
    linarith
  push Not at hon
  by_cases hch : JasOffLineChain
  · rcases lt_or_eq_of_le hδ with hlt | heq
    · left
      have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hle hon.choose)
      have hXi : XiZeroHalfPlaneBound δ := by
        intro ρ hρ
        obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
        linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2), hle q]
      have := one_add_sSup_le_of_jasProductPositiveAbove_of_chain hδ0 hlt hXi h hch
      exact fun q => by linarith [hle q]
    · exact Or.inr heq
  · left
    obtain ⟨q₀, hoff, hmax⟩ : ∃ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 ∧
        ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
      by_contra hno
      push Not at hno
      exact hch ⟨hon, fun q₀ h₀ => hno q₀ h₀⟩
    have hσ₀ : 1 + |(q₀.1 : ℂ).re - 1 / 2| ≤ σ := by
      by_contra hlt
      exact not_jasProductPositiveAbove_of_maximal_offLine_of_le X q₀ hoff hmax (by linarith)
        (not_le.mp hlt).le h
    exact fun q => by linarith [hmax q]

/-- **Producer dichotomy.**  Positivity on characters of primes `> X` at a level `σ ≥ 1` forces
`|Re ρ − ½| ≤ σ − 1` for every zero, unless the zeros accumulate at `Re s ∈ {0, 1}`. -/
theorem jasDressedPSDAbove_zeroFree_or_edge {X : ℕ} {σ : ℝ} (hσ : 1 ≤ σ)
    (h : JasDressedPSDAbove X σ) :
    (∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ σ - 1) ∨
      sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) = 1 / 2 :=
  jasProductPositiveAbove_zeroFree_or_edge hσ h.productPositive

/-- **The large-prime producer law.**  For `σ > 1`: a zero-free strip `|Re ρ − ½| < σ − 1` with
convergent boundary series `Σ_ρ |w_ρ|/(σ − 1 − |Re ρ − ½|)` produces positivity above some `X` at
every level `≥ σ`; and positivity above some `X` at `σ` gives the closed strip
`|Re ρ − ½| ≤ σ − 1`, unless the zeros accumulate at `Re s ∈ {0, 1}`. -/
theorem largePrime_producer_law {σ : ℝ} (hσ : 1 < σ) :
    ((∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < σ - 1) →
        (Summable fun q : XiZeroCopy => ‖lagWeight q‖ / (σ - 1 - |(q.1 : ℂ).re - 1 / 2|)) →
        ∃ X : ℕ, ∀ σ' : ℝ, σ ≤ σ' → JasDressedPSDAbove X σ') ∧
      ((∃ X : ℕ, JasDressedPSDAbove X σ) →
        (∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ σ - 1) ∨
          sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) = 1 / 2) :=
  ⟨fun hd hsum => exists_jasDressedPSDAbove_of_summable hσ hd hsum,
    fun ⟨_, hX⟩ => jasDressedPSDAbove_zeroFree_or_edge hσ.le hX⟩

/-- **A farthest zero leaves the large-prime abscissa unattained.**  If an off-line zero `ρ₀`
maximizes `|Re ρ − ½|`, the levels with large-prime positivity are exactly
`σ > 1 + |Re ρ₀ − ½|`. -/
theorem largePrime_producer_set_of_farthest {q₀ : XiZeroCopy} (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) :
    {σ : ℝ | ∃ X : ℕ, JasDressedPSDAbove X σ} = Set.Ioi (1 + |(q₀.1 : ℂ).re - 1 / 2|) := by
  ext σ
  constructor
  · rintro ⟨X, hX⟩
    by_contra h
    exact not_jasDressedPSDAbove_of_maximal_offLine_of_le X q₀ hoff hmax (not_lt.mp h) hX
  · intro hσ
    have hσ' : 1 + |(q₀.1 : ℂ).re - 1 / 2| < σ := hσ
    have hd0 : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
    have hpos : 0 < σ - 1 - |(q₀.1 : ℂ).re - 1 / 2| := by linarith
    obtain ⟨X, hX⟩ := exists_jasDressedPSDAbove_of_summable (σ₀ := σ) (by linarith)
      (fun q => by linarith [hmax q])
      ((summable_norm_lagWeight.div_const (σ - 1 - |(q₀.1 : ℂ).re - 1 / 2|)).of_nonneg_of_le
        (fun q => div_nonneg (norm_nonneg _) (by linarith [hmax q]))
        (fun q => div_le_div_of_nonneg_left (norm_nonneg _) hpos (by linarith [hmax q])))
    exact ⟨X, hX σ le_rfl⟩

/-- **Attainment excludes a farthest zero.**  If the levels with large-prime positivity have a
least element, no off-line zero is farthest from the critical line. -/
theorem not_farthest_of_isLeast_largePrime {σ₀ : ℝ}
    (h : IsLeast {σ : ℝ | ∃ X : ℕ, JasDressedPSDAbove X σ} σ₀) :
    ¬ ∃ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 ∧
      ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
  rintro ⟨q₀, hoff, hmax⟩
  rw [largePrime_producer_set_of_farthest hoff hmax] at h
  have h1 : 1 + |(q₀.1 : ℂ).re - 1 / 2| < σ₀ := h.1
  obtain ⟨b, hab, hbσ⟩ := exists_between h1
  exact absurd (h.2 (show b ∈ Set.Ioi (1 + |(q₀.1 : ℂ).re - 1 / 2|) from hab)) (not_le.mpr hbσ)

/-- **Attainment detects chains.**  Off RH, if the levels with large-prime positivity have a least
element, the off-line zeros form a chain. -/
theorem jasOffLineChain_of_isLeast_largePrime (hRH : ¬ RiemannHypothesis) {σ₀ : ℝ}
    (h : IsLeast {σ : ℝ | ∃ X : ℕ, JasDressedPSDAbove X σ} σ₀) : JasOffLineChain := by
  by_contra hch
  exact not_farthest_of_isLeast_largePrime h (exists_farthest_offLine_of_not_jasOffLineChain hch hRH)

/-- **The all-prime abscissa exceeds the large-prime one strictly when a farthest zero exists.** -/
theorem lt_jasAbscissa_of_farthest {q₀ : XiZeroCopy} (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) :
    1 + |(q₀.1 : ℂ).re - 1 / 2| < jasAbscissa := by
  have hmem : jasAbscissa ∈ {σ : ℝ | ∃ X : ℕ, JasDressedPSDAbove X σ} :=
    ⟨0, fun S _ => jasDressedPSD_jasAbscissa.on S⟩
  rw [largePrime_producer_set_of_farthest hoff hmax] at hmem
  exact hmem

/-- Off RH, an all-prime abscissa at most `1 + sup |Re ρ − ½|` forces a chain. -/
theorem jasOffLineChain_of_jasAbscissa_le_one_add_sSup (hRH : ¬ RiemannHypothesis)
    (h : jasAbscissa ≤ 1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|)) :
    JasOffLineChain := by
  by_contra hch
  obtain ⟨q₀, hoff, hmax⟩ := exists_farthest_offLine_of_not_jasOffLineChain hch hRH
  have hsup : sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) =
      |(q₀.1 : ℂ).re - 1 / 2| :=
    le_antisymm (csSup_le (Set.range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact hmax q))
      (le_csSup ⟨_, by rintro _ ⟨q, rfl⟩; exact hmax q⟩ ⟨q₀, rfl⟩)
  have := lt_jasAbscissa_of_farthest hoff hmax
  rw [hsup] at h
  linarith

/-- Under a half-plane bound below `½`, product-test positivity on large primes at `σ ≥ 1` gives
the half-plane bound `σ − 1`. -/
theorem xiZeroHalfPlaneBound_of_jasProductPositiveAbove_of_quasi {X : ℕ} {σ alpha : ℝ}
    (hσ : 1 ≤ σ) (h : JasProductPositiveAbove X σ) (halpha : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) : XiZeroHalfPlaneBound (σ - 1) := by
  have hle : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ σ - 1 := by
    rcases jasProductPositiveAbove_zeroFree_or_edge hσ h with h1 | h1
    · exact h1
    · exfalso
      have hsup : sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ alpha :=
        csSup_le (Set.range_nonempty _) (by
          rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q)
      linarith
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2), hle q]

/-- Under a half-plane bound below `½`, large-prime positivity at `σ ≥ 1` gives the half-plane
bound `σ − 1`. -/
theorem xiZeroHalfPlaneBound_of_jasDressedPSDAbove_of_quasi {X : ℕ} {σ alpha : ℝ} (hσ : 1 ≤ σ)
    (h : JasDressedPSDAbove X σ) (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) :
    XiZeroHalfPlaneBound (σ - 1) :=
  xiZeroHalfPlaneBound_of_jasProductPositiveAbove_of_quasi hσ h.productPositive halpha hXi

/-- **Product-test capstone.**  RH holds iff the Bernoulli product tests on all sufficiently large
primes are positive at the single level `σ = 1` and some half-plane bound below `½` holds. -/
theorem riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi :
    RiemannHypothesis ↔ (∃ X : ℕ, JasProductPositiveAbove X 1) ∧
      ∃ alpha : ℝ, alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  constructor
  · intro hRH
    refine ⟨⟨0, JasDressedPSDAbove.productPositive fun S _ =>
      (jasDressedPSD_of_riemannHypothesis hRH (by norm_num)).on S⟩, 0, by norm_num, fun ρ hρ => ?_⟩
    have := xi_zero_re_eq_half_of_RH hRH hρ
    linarith
  · rintro ⟨⟨X, hX⟩, alpha, halpha, hXi⟩
    have h0 := xiZeroHalfPlaneBound_of_jasProductPositiveAbove_of_quasi le_rfl hX halpha hXi
    refine riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase fun q => ?_
    have := abs_re_sub_half_le_of_xiZeroHalfPlaneBound h0 q
    rw [sub_self] at this
    have h1 := abs_nonneg ((q.1 : ℂ).re - 1 / 2)
    have h2 : |(q.1 : ℂ).re - 1 / 2| = 0 := le_antisymm this h1
    linarith [abs_eq_zero.mp h2]

/-- **The positivity hierarchy collapses.**  Under a half-plane bound below `½`, positivity of the
rank-one Bernoulli product tests on the squarefree characters of large primes at `σ = 1` already
gives positivity of the dressed aggregate on all characters, over all primes, with all exponents. -/
theorem jasDressedPSD_one_of_exists_jasProductPositiveAbove_of_quasi {alpha : ℝ}
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha)
    (h : ∃ X : ℕ, JasProductPositiveAbove X 1) : JasDressedPSD 1 :=
  jasDressedPSD_of_riemannHypothesis
    (riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi.mpr ⟨h, alpha, halpha, hXi⟩)
    (by norm_num)

/-- **Single-level large-prime capstone.**  RH holds iff positivity holds on the characters of all
sufficiently large primes at the single level `σ = 1` and some half-plane bound below `½` holds. -/
theorem riemannHypothesis_iff_exists_jasDressedPSDAbove_one_and_quasi :
    RiemannHypothesis ↔ (∃ X : ℕ, JasDressedPSDAbove X 1) ∧
      ∃ alpha : ℝ, alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  refine ⟨fun hRH => ⟨⟨0, fun S _ => (jasDressedPSD_of_riemannHypothesis hRH (by norm_num)).on S⟩,
    (riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi.mp hRH).2⟩, ?_⟩
  rintro ⟨⟨X, hX⟩, hq⟩
  exact riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi.mpr
    ⟨⟨X, hX.productPositive⟩, hq⟩

/-! ## The log-window producer -/

/-- `T_X(σ) ≤ X^{1−σ}/(σ − 1)`. -/
theorem largePrimeTail_jasInvPow_le_div {σ : ℝ} (hσ : 1 < σ) {X : ℕ} (hX : 1 ≤ X) :
    largePrimeTail (jasInvPow σ) X ≤ (X : ℝ) ^ (1 - σ) / (σ - 1) := by
  have h := GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le (q := 1 - σ) (by linarith) hX
  rw [show -(1 - σ) = σ - 1 by ring, show 1 - σ - 1 = -σ by ring] at h
  refine le_of_eq_of_le (tsum_congr fun k => ?_) h
  unfold jasInvPow
  rw [← Real.rpow_neg (by positivity)]
  push_cast
  ring_nf

/-- **Log-window producer.**  If `T` bounds the tail `Σ_{k>X} k^{−σ}` and
`Σ_ρ |w_ρ| · e^{a/2} · (2T + T²) ≤ Φ(0)`, the `σ`-dressed aggregate is positive on every family of
distinct characters of primes `> X` whose pairwise log-ratios are at most `a`. -/
theorem jasDressedPSD_of_logWindow {σ a T : ℝ} (hσ : 1 < σ) {X : ℕ}
    (hT : largePrimeTail (jasInvPow σ) X ≤ T)
    (hsmall : jasLagAbsMass * Real.exp (a / 2) * (2 * T + T ^ 2) ≤ poleSharpConstant)
    {ι : Type} (t : Finset ι) (c : ι → ℂ) (n : ι → Nat.Primes →₀ ℤ) (hinj : Set.InjOn n t)
    (hsupp : ∀ i ∈ t, ∀ p ∈ (n i).support, X < (p : ℕ))
    (hwin : ∀ i ∈ t, ∀ j ∈ t, |jasLogNeg (n i - n j) - jasLogPos (n i - n j)| ≤ a) :
    0 ≤ (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ (n i - n j)).re := by
  classical
  have hW0 : 0 ≤ jasLagAbsMass := tsum_nonneg fun _ => norm_nonneg _
  have hT0 := largePrimeTail_nonneg (jasInvPow_nonneg σ) X
  have hpoint : ∀ m : Nat.Primes →₀ ℤ, |jasLogNeg m - jasLogPos m| ≤ a →
      ‖jasDressedLagAggregate σ m‖ ≤ jasLagAbsMass * Real.exp (a / 2) *
        (jasInvPow σ (jasNum m) * jasInvPow σ (jasDen m)) := by
    intro m hm
    rw [jasDressedLagAggregate, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hΦ := norm_weilLagFunction_le (jasLogNeg m - jasLogPos m)
    have he : Real.exp (|jasLogNeg m - jasLogPos m| / 2) ≤ Real.exp (a / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hsize : Real.exp (-σ * jasLogSize m) = jasInvPow σ (jasNum m) * jasInvPow σ (jasDen m) := by
      rw [jasLogSize, mul_add, Real.exp_add, exp_neg_mul_jasLogPos, exp_neg_mul_jasLogNeg]
    rw [hsize]
    have hprod0 : 0 ≤ jasInvPow σ (jasNum m) * jasInvPow σ (jasDen m) :=
      mul_nonneg (jasInvPow_nonneg _ _) (jasInvPow_nonneg _ _)
    calc jasInvPow σ (jasNum m) * jasInvPow σ (jasDen m) * ‖weilLagFunction (jasLogNeg m - jasLogPos m)‖
        ≤ jasInvPow σ (jasNum m) * jasInvPow σ (jasDen m) *
            (Real.exp (a / 2) * jasLagAbsMass) :=
          mul_le_mul_of_nonneg_left (hΦ.trans (mul_le_mul_of_nonneg_right he hW0)) hprod0
      _ = _ := by ring
  refine gram_re_nonneg_of_row_le t c (fun i j => jasDressedLagAggregate σ (n i - n j))
    (A := poleSharpConstant) (fun i _ => by rw [sub_self, jasDressedLagAggregate_zero])
    (fun i _ j _ => by
      rw [show n j - n i = -(n i - n j) by abel, jasDressedLagAggregate_neg]) (fun i hi => ?_)
  have himg : ∑ j ∈ t.erase i, ‖jasDressedLagAggregate σ (n i - n j)‖ =
      ∑ m ∈ (t.erase i).image (fun j => n i - n j), ‖jasDressedLagAggregate σ m‖ := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hinj (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) (sub_right_injective hxy)
  have hM0 : (0 : Nat.Primes →₀ ℤ) ∉ (t.erase i).image (fun j => n i - n j) := by
    intro h
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp h
    obtain ⟨hji, hjt⟩ := Finset.mem_erase.mp hj
    exact hji (hinj hjt hi (sub_eq_zero.mp hj0).symm)
  have hMX : ∀ m ∈ (t.erase i).image (fun j => n i - n j), ∀ p ∈ m.support, X < (p : ℕ) := by
    intro m hm p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    rcases Finset.mem_union.mp (Finsupp.support_sub hp) with h | h
    · exact hsupp i hi p h
    · exact hsupp j (Finset.mem_of_mem_erase hj) p h
  have hMwin : ∀ m ∈ (t.erase i).image (fun j => n i - n j), |jasLogNeg m - jasLogPos m| ≤ a := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    exact hwin i hi j (Finset.mem_of_mem_erase hj)
  have hpair := sum_jasNum_jasDen_le _ hM0 hMX (jasInvPow_nonneg σ) (jasInvPow_nonneg σ)
    (jasInvPow_one σ) (jasInvPow_one σ) (summable_jasInvPow hσ) (summable_jasInvPow hσ)
  rw [himg]
  calc ∑ m ∈ (t.erase i).image (fun j => n i - n j), ‖jasDressedLagAggregate σ m‖
      ≤ ∑ m ∈ (t.erase i).image (fun j => n i - n j), jasLagAbsMass * Real.exp (a / 2) *
          (jasInvPow σ (jasNum m) * jasInvPow σ (jasDen m)) :=
        Finset.sum_le_sum fun m hm => hpoint m (hMwin m hm)
    _ = jasLagAbsMass * Real.exp (a / 2) * ∑ m ∈ (t.erase i).image (fun j => n i - n j),
          jasInvPow σ (jasNum m) * jasInvPow σ (jasDen m) := by rw [Finset.mul_sum]
    _ ≤ jasLagAbsMass * Real.exp (a / 2) * (2 * T + T ^ 2) := by
        refine mul_le_mul_of_nonneg_left (hpair.trans ?_) (mul_nonneg hW0 (Real.exp_pos _).le)
        nlinarith
    _ ≤ poleSharpConstant := hsmall

/-- **Log-window producer, asymptotic form.**  For `σ > 1` and `κ < 2(σ − 1)` there is `X₀` such
that, for every `X ≥ X₀`, the `σ`-dressed aggregate is positive on every family of distinct
characters of primes `> X` whose pairwise log-ratios are at most `κ log X`. -/
theorem eventually_jasDressedPSD_logWindow {σ κ : ℝ} (hσ : 1 < σ) (hκ : κ < 2 * (σ - 1)) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ {ι : Type} (t : Finset ι) (c : ι → ℂ)
      (n : ι → Nat.Primes →₀ ℤ), Set.InjOn n t → (∀ i ∈ t, ∀ p ∈ (n i).support, X < (p : ℕ)) →
      (∀ i ∈ t, ∀ j ∈ t, |jasLogNeg (n i - n j) - jasLogPos (n i - n j)| ≤ κ * Real.log X) →
      0 ≤ (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ (n i - n j)).re := by
  have hσ1 : 0 < σ - 1 := by linarith
  set C := (2 + 1 / (σ - 1)) / (σ - 1) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  set W := jasLagAbsMass with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hη : 0 < (σ - 1) - κ / 2 := by linarith
  have hlim : Tendsto (fun X : ℕ => ((X : ℕ) : ℝ) ^ (-((σ - 1) - κ / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop
  have hpos : 0 < poleSharpConstant / (W * C + 1) :=
    div_pos poleSharpConstant_pos (by nlinarith)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((hlim.eventually (ge_mem_nhds hpos)).and (eventually_ge_atTop 1))
  refine ⟨X₀, fun X hX ι t c n hinj hsupp hwin => ?_⟩
  obtain ⟨hsmallX, hX1⟩ := hX₀ X hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hX1' : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  set T := (X : ℝ) ^ (1 - σ) / (σ - 1) with hTdef
  refine jasDressedPSD_of_logWindow (a := κ * Real.log X) (T := T) hσ
    (largePrimeTail_jasInvPow_le_div hσ hX1) ?_ t c n hinj hsupp hwin
  have hexp : Real.exp (κ * Real.log X / 2) = (X : ℝ) ^ (κ / 2) := by
    rw [Real.rpow_def_of_pos hX0]; congr 1; ring
  have hXp1 : (X : ℝ) ^ (1 - σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1' (by linarith)
  have hXp0 : 0 ≤ (X : ℝ) ^ (1 - σ) := Real.rpow_nonneg hX0.le _
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hT1 : T ≤ 1 / (σ - 1) := by rw [hTdef]; exact div_le_div_of_nonneg_right hXp1 hσ1.le
  have hcomb : (X : ℝ) ^ (κ / 2) * (X : ℝ) ^ (1 - σ) = (X : ℝ) ^ (-((σ - 1) - κ / 2)) := by
    rw [← Real.rpow_add hX0]; congr 1; ring
  have hXk0 : 0 ≤ (X : ℝ) ^ (κ / 2) := Real.rpow_nonneg hX0.le _
  rw [hexp]
  calc W * (X : ℝ) ^ (κ / 2) * (2 * T + T ^ 2)
      = W * (X : ℝ) ^ (κ / 2) * T * (2 + T) := by ring
    _ ≤ W * (X : ℝ) ^ (κ / 2) * T * (2 + 1 / (σ - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = W * C * (X : ℝ) ^ (-((σ - 1) - κ / 2)) := by
        rw [← hcomb, hTdef, hC]; field_simp
    _ ≤ W * C * (poleSharpConstant / (W * C + 1)) :=
        mul_le_mul_of_nonneg_left hsmallX (by positivity)
    _ ≤ poleSharpConstant := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by nlinarith)]
        nlinarith [poleSharpConstant_pos]

/-- **Few-primes producer.**  For `σ ≥ 1`, positivity holds on every set of at most `(7/5)√X`
primes `> X`. -/
theorem jasDressedPSDOn_of_card_le_sqrt {X : ℕ} (hX : 1 ≤ X) (S : Finset Nat.Primes)
    (hS : ∀ p ∈ S, X < (p : ℕ)) (hcard : (S.card : ℝ) ≤ 7 / 5 * Real.sqrt X) {σ : ℝ}
    (hσ : 1 ≤ σ) : JasDressedPSDOn S σ := by
  refine (jasDressedPSDOn_one_of_sum_le S ?_).mono hσ
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hterm : ∀ p ∈ S, Real.sqrt (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) ^ 2 + (p : ℕ) + 1)) ≤
      1 / Real.sqrt X := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hpX : (X : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hS p hp).le
    rw [le_div_iff₀ hsX, ← Real.sqrt_mul (div_nonneg hp0.le (by positivity))]
    rw [Real.sqrt_le_one]
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  have hsum : ∑ p ∈ S, Real.sqrt (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) ^ 2 + (p : ℕ) + 1)) ≤ 7 / 5 := by
    calc _ ≤ ∑ _p ∈ S, 1 / Real.sqrt X := Finset.sum_le_sum hterm
      _ = S.card * (1 / Real.sqrt X) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 / 5 * Real.sqrt X * (1 / Real.sqrt X) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 7 / 5 := by field_simp
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  linarith

/-- At dressing `c ≥ ½` every local phase width is at most `2 p^{−c}`. -/
theorem jasPhaseWidth_le_two_exp {c : ℝ} (hc : 1 / 2 ≤ c) (q : XiZeroCopy) (p : Nat.Primes) :
    jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) ≤
      2 * Real.exp (-c * Real.log p) := by
  have hβ0 := (xi_divisor_support_re_mem_open_unit q.1).1
  have hβ1 := (xi_divisor_support_re_mem_open_unit q.1).2
  have hlp := log_prime_pos p
  set t := Real.exp (-c * Real.log p) with htdef
  have ht0 : 0 < t := Real.exp_pos _
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    rw [htdef, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-c * Real.log p) = -(2 * c) * Real.log p by
      push_cast; ring]
    have hp2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
    have h1 : -(2 * c) * Real.log p ≤ -Real.log 2 := by nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
    calc Real.exp (-(2 * c) * Real.log p) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr h1
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hr1 : jasR1 ((q.1 : ℂ) + c) p ≤ t := by
    rw [jasR1_dressed, htdef]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hr2 : jasR2 ((q.1 : ℂ) - c) p ≤ t := by
    rw [jasR2_dressed, htdef]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hr10 : 0 ≤ jasR1 ((q.1 : ℂ) + c) p := by rw [jasR1_dressed]; exact (Real.exp_pos _).le
  have hr20 : 0 ≤ jasR2 ((q.1 : ℂ) - c) p := by rw [jasR2_dressed]; exact (Real.exp_pos _).le
  set r₁ := jasR1 ((q.1 : ℂ) + c) p
  set r₂ := jasR2 ((q.1 : ℂ) - c) p
  have hden : 1 / 2 ≤ Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) * (1 / 2)) by
      rw [Real.sqrt_mul_self (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have h1 : r₁ ^ 2 ≤ 1 / 2 := by nlinarith
    have h2 : r₂ ^ 2 ≤ 1 / 2 := by nlinarith
    nlinarith
  have hnum : |r₁ - r₂| ≤ t := by rw [abs_le]; constructor <;> linarith
  unfold jasPhaseWidth
  refine (arctan_le_self_of_nonneg' (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **Few-primes producer at a general level.**  For `σ ≥ 1`, positivity holds on every set of
at most `(7/10) X^{σ−½}` primes `> X`. -/
theorem jasDressedPSDOn_of_card_le_rpow {X : ℕ} (hX : 1 ≤ X) {σ : ℝ} (hσ : 1 ≤ σ)
    (S : Finset Nat.Primes) (hS : ∀ p ∈ S, X < (p : ℕ))
    (hcard : (S.card : ℝ) ≤ 7 / 10 * (X : ℝ) ^ (σ - 1 / 2)) : JasDressedPSDOn S σ := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hc : 1 / 2 ≤ σ - 1 / 2 := by linarith
  have hσeq : σ = 1 / 2 + (σ - 1 / 2) := by ring
  rw [hσeq]
  refine jasDressedPSDOn_of_phaseBudget (by linarith) S fun q => ?_
  have harg := abs_arg_jasWeight_le q
  have hterm : ∀ p ∈ S, jasPhaseWidth (jasR1 ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasR2 ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ≤ 2 * (X : ℝ) ^ (-(σ - 1 / 2)) := by
    intro p hp
    refine (jasPhaseWidth_le_two_exp hc q p).trans ?_
    have hpX : (X : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hS p hp).le
    rw [show Real.exp (-(σ - 1 / 2) * Real.log p) = ((p : ℕ) : ℝ) ^ (-(σ - 1 / 2)) by
      rw [Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]; ring_nf]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hX0 hpX (by linarith)) (by norm_num)
  have hsum : ∑ p ∈ S, jasPhaseWidth (jasR1 ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasR2 ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ≤ 7 / 5 := by
    calc _ ≤ ∑ _p ∈ S, 2 * (X : ℝ) ^ (-(σ - 1 / 2)) := Finset.sum_le_sum hterm
      _ = S.card * (2 * (X : ℝ) ^ (-(σ - 1 / 2))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 / 10 * (X : ℝ) ^ (σ - 1 / 2) * (2 * (X : ℝ) ^ (-(σ - 1 / 2))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 7 / 5 := by
          rw [show 7 / 10 * (X : ℝ) ^ (σ - 1 / 2) * (2 * (X : ℝ) ^ (-(σ - 1 / 2))) =
            7 / 5 * ((X : ℝ) ^ (σ - 1 / 2) * (X : ℝ) ^ (-(σ - 1 / 2))) by ring,
            ← Real.rpow_add hX0]
          simp
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  linarith

/-- Under a half-plane bound `α ≤ c`, every local phase width at dressing `c` is at most
`2 p^{−(c + ½ − α)}`. -/
theorem jasPhaseWidth_le_two_exp_of_halfPlane {α c : ℝ} (hαc : α ≤ c)
    (hXi : XiZeroHalfPlaneBound α) (q : XiZeroCopy) (p : Nat.Primes) :
    jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) ≤
      2 * Real.exp (-(c + 1 / 2 - α) * Real.log p) := by
  have hd := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q
  have hlp := log_prime_pos p
  have hdl := (abs_le.mp hd).1
  have hdr := (abs_le.mp hd).2
  set t := Real.exp (-(c + 1 / 2 - α) * Real.log p) with htdef
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    rw [htdef, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(c + 1 / 2 - α) * Real.log p) =
      -(2 * (c + 1 / 2 - α)) * Real.log p by push_cast; ring]
    have hp2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
    have h1 : -(2 * (c + 1 / 2 - α)) * Real.log p ≤ -Real.log 2 := by
      nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
    calc Real.exp (-(2 * (c + 1 / 2 - α)) * Real.log p) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr h1
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hr1 : jasR1 ((q.1 : ℂ) + c) p ≤ t := by
    rw [jasR1_dressed, htdef]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hr2 : jasR2 ((q.1 : ℂ) - c) p ≤ t := by
    rw [jasR2_dressed, htdef]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hr10 : 0 ≤ jasR1 ((q.1 : ℂ) + c) p := by rw [jasR1_dressed]; exact (Real.exp_pos _).le
  have hr20 : 0 ≤ jasR2 ((q.1 : ℂ) - c) p := by rw [jasR2_dressed]; exact (Real.exp_pos _).le
  set r₁ := jasR1 ((q.1 : ℂ) + c) p
  set r₂ := jasR2 ((q.1 : ℂ) - c) p
  have hden : 1 / 2 ≤ Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) * (1 / 2)) by
      rw [Real.sqrt_mul_self (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have h1 : r₁ ^ 2 ≤ 1 / 2 := by nlinarith
    have h2 : r₂ ^ 2 ≤ 1 / 2 := by nlinarith
    nlinarith
  have hnum : |r₁ - r₂| ≤ t := by rw [abs_le]; constructor <;> linarith
  unfold jasPhaseWidth
  refine (arctan_le_self_of_nonneg' (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **Few-primes producer under a half-plane bound.**  If every zero satisfies
`Re ρ ≤ ½ + α` with `α ≤ ½`, then for `σ ≥ 1` positivity holds on every set of at most
`(7/10) X^{σ−α}` primes `> X`. -/
theorem jasDressedPSDOn_of_card_le_rpow_of_halfPlane {α : ℝ} (hα : α ≤ 1 / 2)
    (hXi : XiZeroHalfPlaneBound α) {X : ℕ} (hX : 1 ≤ X) {σ : ℝ} (hσ : 1 ≤ σ)
    (S : Finset Nat.Primes) (hS : ∀ p ∈ S, X < (p : ℕ))
    (hcard : (S.card : ℝ) ≤ 7 / 10 * (X : ℝ) ^ (σ - α)) : JasDressedPSDOn S σ := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hc : 1 / 2 ≤ σ - 1 / 2 := by linarith
  have hσeq : σ = 1 / 2 + (σ - 1 / 2) := by ring
  rw [hσeq]
  refine jasDressedPSDOn_of_phaseBudget (by linarith) S fun q => ?_
  have harg := abs_arg_jasWeight_le q
  have hterm : ∀ p ∈ S, jasPhaseWidth (jasR1 ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasR2 ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ≤ 2 * (X : ℝ) ^ (-(σ - α)) := by
    intro p hp
    refine (jasPhaseWidth_le_two_exp_of_halfPlane (by linarith) hXi q p).trans ?_
    have hpX : (X : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hS p hp).le
    rw [show Real.exp (-((σ - 1 / 2) + 1 / 2 - α) * Real.log p) = ((p : ℕ) : ℝ) ^ (-(σ - α)) by
      rw [Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]; ring_nf]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hX0 hpX (by linarith)) (by norm_num)
  have hsum : ∑ p ∈ S, jasPhaseWidth (jasR1 ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasR2 ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ≤ 7 / 5 := by
    calc _ ≤ ∑ _p ∈ S, 2 * (X : ℝ) ^ (-(σ - α)) := Finset.sum_le_sum hterm
      _ = S.card * (2 * (X : ℝ) ^ (-(σ - α))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 / 10 * (X : ℝ) ^ (σ - α) * (2 * (X : ℝ) ^ (-(σ - α))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 7 / 5 := by
          rw [show 7 / 10 * (X : ℝ) ^ (σ - α) * (2 * (X : ℝ) ^ (-(σ - α))) =
            7 / 5 * ((X : ℝ) ^ (σ - α) * (X : ℝ) ^ (-(σ - α))) by ring, ← Real.rpow_add hX0]
          simp
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  linarith

end

end RHTower
