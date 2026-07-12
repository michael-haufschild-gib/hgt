import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import GaloisForLFunctions.RHTower.MollifierDetection
import GaloisForLFunctions.RHTower.MFreeTower

/-!
# Square support forces prime-mass content

The budget law generalizes: every square-supported quadratic functional in the tree
carries forced Mertens mass, because prime squares contribute their full reciprocal
weight.  Two more instances of the positive law:

* `RHTower.primeMass_le_sqrtQuarter_diagonal` — the quarter-weighted second-moment
  diagonal of the square-dilated mollifier **must carry the Mertens mass** of the primes
  up to `√y`: `∑_{p ≤ √y} 1/p ≤ ∑_{n ≤ y} (sqrtMoebiusCoeff n · n^(-1/4))²`.  Through
  `secondMoment_meanValue` this is a forced lower bound on the quarter-weighted window
  mass.
* `RHTower.detCoeffW_prime_sq` / `RHTower.windowPrimeMass_le_detection_diagonal` — the
  σ-weighted detection coefficient at a prime square in the window `√y < p ≤ y` is
  exactly `-(p^(-σ))²`, so the detection diagonal at `σ = 1/4` **must carry the window
  prime mass**: `∑_{√y < p ≤ y} 1/p ≤ ∑_k e_k(1/4)²`.  Detection mass is not free below
  weight `1/4 + ε` — the same square-support mechanism that funds the carrier budget
  also funds the detection diagonal.
-/

noncomputable section

namespace RHTower

open Complex

/-! ## The abstract forced-content law -/

/-- **The abstract forced-content law, tower core.**  Any quadratic functional over an
index set containing the `m`-th powers of a prime family, whose coefficients at those
prime powers are at least `δ·p^(-1/2)` in absolute value, dominates `δ²` times the prime
reciprocal mass of the family.  Prime powers inject their full reciprocal weight into
every power-supported quadratic functional — one law per dilation rung. -/
theorem primeMass_le_pow_sum_of_forced {S P : Finset ℕ} {b : ℕ → ℝ} {δ : ℝ} {m : ℕ}
    (hm : m ≠ 0) (hδ0 : 0 ≤ δ) (hmem : ∀ p ∈ P, p ^ m ∈ S)
    (hval : ∀ p ∈ P, δ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |b (p ^ m)|) :
    δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ ≤ ∑ k ∈ S, (b k) ^ 2 := by
  have himg : P.image (fun p => p ^ m) ⊆ S := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact hmem p hp
  have hsub : ∑ n ∈ P.image (fun p => p ^ m), (b n) ^ 2 ≤ ∑ k ∈ S, (b k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun i _ _ => by positivity
  refine le_trans ?_ hsub
  rw [Finset.sum_image ((Nat.pow_left_injective hm).injOn), Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hsq : (δ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ (b (p ^ m)) ^ 2 := by
    rw [← sq_abs (b (p ^ m))]
    exact pow_le_pow_left₀ (by positivity) (hval p hp) 2
  refine le_trans (le_of_eq ?_) hsq
  rw [mul_pow, ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) 2,
    ← Real.rpow_mul (Nat.cast_nonneg p),
    show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]

/-- The square case of the tower core. -/
theorem primeMass_le_sq_sum_of_forced {S P : Finset ℕ} {b : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hmem : ∀ p ∈ P, p ^ 2 ∈ S)
    (hval : ∀ p ∈ P, δ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |b (p ^ 2)|) :
    δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ ≤ ∑ k ∈ S, (b k) ^ 2 :=
  primeMass_le_pow_sum_of_forced two_ne_zero hδ0 hmem hval

/-- Real `m`-th-power dilation: `((k^m:ℕ):ℝ)^y = (k:ℝ)^(m·y)`. -/
theorem natCast_pow_rpow (k m : ℕ) (y : ℝ) :
    ((k ^ m : ℕ) : ℝ) ^ y = ((k : ℕ) : ℝ) ^ ((m : ℝ) * y) := by
  push_cast
  rw [← Real.rpow_natCast ((k : ℕ) : ℝ) m, ← Real.rpow_mul (Nat.cast_nonneg k)]

/-- **The forced-content tower, rung `m`.**  If `|a(p^m)| ≥ δ` on primes, the
`1/(2m)`-weighted quadratic functional of `a` dominates `δ²` times the prime mass of the
rung: the weight threshold `1/4` of the square rung generalizes to `1/(2m)` at dilation
`m` — the `m`-free ladder's spectral fingerprint. -/
theorem primeMass_le_rung_weighted_sq_sum {a : ℕ → ℝ} {δ : ℝ} {m : ℕ} (hm : m ≠ 0)
    (hδ0 : 0 ≤ δ) (hδ : ∀ p : ℕ, p.Prime → δ ≤ |a (p ^ m)|) (y : ℕ) :
    δ ^ 2 * ∑ p ∈ (Nat.primesBelow (y + 1)).filter (fun p => p ^ m ≤ y), (p : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y, (a n * (n : ℝ) ^ (-(1 / (2 * (m : ℝ))))) ^ 2 := by
  refine primeMass_le_pow_sum_of_forced hm hδ0 (fun p hp => ?_) fun p hp => ?_
  · obtain ⟨hpmem, hpm⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpp⟩ := Nat.mem_primesBelow.mp hpmem
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hpp.pos, hpm⟩
  · obtain ⟨hpmem, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpp⟩ := Nat.mem_primesBelow.mp hpmem
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hm0 : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
    have hpow : ((p ^ m : ℕ) : ℝ) ^ (-(1 / (2 * (m : ℝ))))
        = ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [natCast_pow_rpow]
      congr 1
      field_simp
    rw [abs_mul, hpow, abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
    exact mul_le_mul_of_nonneg_right (hδ p hpp) (Real.rpow_nonneg hp0.le _)

/-- **The `mPart` carrier instance of rung `m`**: the `1/(2m)`-weighted second-moment
diagonal of the `m`-th-power-dilated Möbius carrier must carry the prime mass of its
rung. -/
theorem primeMass_le_mPart_weighted_diagonal {m : ℕ} (hm : m ≠ 0) (y : ℕ) :
    ∑ p ∈ (Nat.primesBelow (y + 1)).filter (fun p => p ^ m ≤ y), (p : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y,
          (mPartMoebiusCoeff m n * (n : ℝ) ^ (-(1 / (2 * (m : ℝ))))) ^ 2 := by
  have h := primeMass_le_rung_weighted_sq_sum (a := mPartMoebiusCoeff m) (δ := 1) hm
    zero_le_one (fun p hpp => ?_) y
  · simpa using h
  · rw [mPartMoebiusCoeff, mPart_apply_pow hm, ArithmeticFunction.moebius_apply_prime hpp]
    norm_num

/-! ## The mixed-radix compound fingerprint -/

/-- **The full ladder of fingerprints in one carrier.**  The `M`-free indicator is
supported at *every* prime power `p^e` with `e < M`, so it satisfies the rung-`e`
forced-content law for every such `e` simultaneously: one carrier, `M - 1` spectral
lines. -/
theorem primeMass_le_mFreeIndicator_weighted_diagonal {M e : ℕ} (hM : M ≠ 0)
    (he : e ≠ 0) (hlt : e < M) (y : ℕ) :
    ∑ p ∈ (Nat.primesBelow (y + 1)).filter (fun p => p ^ e ≤ y), (p : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y,
          (((mFreeIndicator M n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / (2 * (e : ℝ))))) ^ 2 := by
  have h := primeMass_le_rung_weighted_sq_sum
    (a := fun n => ((mFreeIndicator M n : ℤ) : ℝ)) (δ := 1) he
    zero_le_one (fun p hpp => ?_) y
  · simpa using h
  · show (1 : ℝ) ≤ |((mFreeIndicator M (p ^ e) : ℤ) : ℝ)|
    rw [mFreeIndicator_apply_prime_pow hM hpp, if_pos hlt]
    norm_num

/-- **The mixed-radix compound spectral signature.**  The convolution of the dilated
`m_k`-free carriers along the telescope carries the entire ladder of rung fingerprints
at once: for every exponent `e` below the full modulus `P_K = m₀⋯m_(K-1)`, the
`1/(2e)`-weighted diagonal of the convolved carrier dominates the rung-`e` prime mass.
The telescope compounds the per-rung fingerprints into one carrier. -/
theorem telescope_compound_fingerprint (m : ℕ → ℕ) (hm : ∀ k, m k ≠ 0) (K : ℕ)
    {e : ℕ} (he : e ≠ 0) (hlt : e < ∏ k ∈ Finset.range K, m k) (y : ℕ) :
    ∑ p ∈ (Nat.primesBelow (y + 1)).filter (fun p => p ^ e ≤ y), (p : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y,
          ((((∏ k ∈ Finset.range K,
              mPart (∏ j ∈ Finset.range k, m j) (mFreeIndicator (m k))) n : ℤ) : ℝ)
            * (n : ℝ) ^ (-(1 / (2 * (e : ℝ))))) ^ 2 := by
  rw [prod_mPart_mFreeIndicator_mixed m hm K]
  exact primeMass_le_mFreeIndicator_weighted_diagonal
    (Finset.prod_ne_zero_iff.mpr fun k _ => hm k) he hlt y

/-- **The abstract forced-content law, quarter-weighted form.**  If `|a(p²)| ≥ δ` on
primes, the `1/4`-weighted quadratic functional of `a` dominates `δ²` times the Mertens
mass: `δ²·∑_{p ≤ √y} 1/p ≤ ∑_{n ≤ y} (a n · n^(-1/4))²`.  This subsumes every
square-supported carrier. -/
theorem primeMass_le_quarter_weighted_sq_sum {a : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ p : ℕ, p.Prime → δ ≤ |a (p ^ 2)|) (y : ℕ) :
    δ ^ 2 * ∑ p ∈ Nat.primesBelow (Nat.sqrt y + 1), (p : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y, (a n * (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 := by
  refine primeMass_le_sq_sum_of_forced hδ0 (fun p hp => ?_) fun p hp => ?_
  · obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hple : p ≤ Nat.sqrt y := by omega
    refine Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hpp.pos, ?_⟩
    rw [pow_two]
    exact Nat.le_sqrt.mp hple
  · obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hpow : ((p ^ 2 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) = ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [natCast_sq_rpow]
      congr 1
      ring
    rw [abs_mul, hpow, abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
    exact mul_le_mul_of_nonneg_right (hδ p hpp) (Real.rpow_nonneg hp0.le _)

/-! ## The quarter-weighted mollifier diagonal -/

/-- **The quarter-weighted diagonal must carry the Mertens mass.**  The second-moment
diagonal of the square-dilated mollifier with weight `n^(-1/4)` dominates the prime
reciprocal sum up to `√y`: each prime square contributes exactly `p⁻¹`. -/
theorem primeMass_le_sqrtQuarter_diagonal (y : ℕ) :
    ∑ p ∈ Nat.primesBelow (Nat.sqrt y + 1), (p : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y, (sqrtMoebiusCoeff n * (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 := by
  have h := primeMass_le_quarter_weighted_sq_sum (a := sqrtMoebiusCoeff) (δ := 1)
    zero_le_one (fun p hpp => ?_) y
  · simpa using h
  · rw [sqrtMoebiusCoeff, sqrtPart_apply_sq, ArithmeticFunction.moebius_apply_prime hpp]
    norm_num

/-! ## The detection diagonal at prime squares -/

/-- The convolution fiber of a prime square inside the window `√y < p ≤ y` is the single
diagonal pair `(p, p)`. -/
theorem filter_mul_eq_prime_sq {y p : ℕ} (hp : p.Prime) (hpy : p ≤ y) (hyp : y < p ^ 2) :
    ((Finset.Icc 1 y ×ˢ Finset.Icc 1 y).filter (fun q => q.1 * q.2 = p ^ 2))
      = {(p, p)} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨ha1, hay⟩, hb1, hby⟩, hab⟩
    have hadvd : a ∣ p ^ 2 := ⟨b, hab.symm⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hadvd
    interval_cases i
    · rw [pow_zero, one_mul] at hab
      omega
    · rw [pow_one] at hab ⊢
      have hb : p * b = p * p := by
        rw [hab, pow_two]
      exact ⟨rfl, (Nat.eq_of_mul_eq_mul_left hp.pos hb).symm ▸ rfl⟩
    · omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨⟨hp.pos, hpy⟩, hp.pos, hpy⟩, (pow_two _).symm⟩

/-- **The detection coefficient at a prime square** in the window `√y < p ≤ y` is exactly
`-(p^(-σ))²`: the fiber collapses to the diagonal pair, contributing the full Möbius
weight. -/
theorem detCoeffW_prime_sq {y p : ℕ} (hp : p.Prime) (hpy : p ≤ y) (hyp : y < p ^ 2)
    (σ : ℝ) :
    detCoeffW y y σ (p ^ 2) = -(((p : ℕ) : ℝ) ^ (-σ)) ^ 2 := by
  have hne1 : p ^ 2 ≠ 1 := (Nat.one_lt_pow two_ne_zero hp.one_lt).ne'
  rw [detCoeffW, dpolyConv, filter_mul_eq_prime_sq hp hpy hyp, Finset.sum_singleton,
    if_neg hne1, sub_zero, ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-- **The detection diagonal at weight `1/4` must carry the window prime mass**:
`∑_{√y < p ≤ y} 1/p ≤ ∑_k e_k(1/4)²`.  The same square-support mechanism that funds the
carrier budget funds the detection diagonal. -/
theorem windowPrimeMass_le_detection_diagonal (y : ℕ) :
    ∑ p ∈ (Nat.primesBelow (y + 1)).filter (fun p => y < p ^ 2), (p : ℝ)⁻¹
      ≤ ∑ k ∈ prodSupport (Finset.Icc 1 y) (Finset.Icc 1 y),
          (detCoeffW y y (1 / 4 : ℝ) k) ^ 2 := by
  have h := primeMass_le_sq_sum_of_forced (δ := 1)
    (S := prodSupport (Finset.Icc 1 y) (Finset.Icc 1 y))
    (P := (Nat.primesBelow (y + 1)).filter (fun p => y < p ^ 2))
    (b := detCoeffW y y (1 / 4 : ℝ)) zero_le_one (fun p hp => ?_) (fun p hp => ?_)
  · simpa using h
  · obtain ⟨hpmem, hyp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hpmem
    refine Finset.mem_image.mpr ⟨(p, p), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpp.pos, by omega⟩, Finset.mem_Icc.mpr ⟨hpp.pos, by omega⟩⟩,
      (pow_two p).symm⟩
  · obtain ⟨hpmem, hyp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hpmem
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    rw [detCoeffW_prime_sq hpp (by omega) hyp, one_mul, abs_neg, abs_of_nonneg
      (by positivity), ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 2,
      ← Real.rpow_mul hp0.le]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring

/-- **The joint spectral statement.**  One carrier and one weight — the `M`-free
indicator with the minimal-prime weight `(minFac n)^(-1/2)` — force the *sum of all rung
prime masses at once*: the index runs over every pair `(e, p)` with `1 ≤ e < M` and
`p^e ≤ y`, and each pair contributes its full `p⁻¹`.  Prime-power uniqueness
(`p^e` determines `p` as its minimal factor and then `e`) makes the pairs inject into
the support: a certified multi-scale prime detector. -/
theorem joint_spectral_forced_content {M : ℕ} (hM : M ≠ 0) (y : ℕ) :
    ∑ q ∈ ((Finset.Icc 1 (M - 1)) ×ˢ Nat.primesBelow (y + 1)).filter
        (fun q => q.2 ^ q.1 ≤ y), ((q.2 : ℕ) : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y,
          (((mFreeIndicator M n : ℤ) : ℝ)
            * ((n.minFac : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
  set T := ((Finset.Icc 1 (M - 1)) ×ˢ Nat.primesBelow (y + 1)).filter
    (fun q => q.2 ^ q.1 ≤ y) with hT
  have hmemT : ∀ q ∈ T, 1 ≤ q.1 ∧ q.1 ≤ M - 1 ∧ q.2.Prime ∧ q.2 ^ q.1 ≤ y := by
    intro q hq
    obtain ⟨hqmem, hqle⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqmem
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hq1
    exact ⟨h1, h2, (Nat.mem_primesBelow.mp hq2).2, hqle⟩
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2 ^ q.1) T := by
    intro a ha b hb hab
    obtain ⟨ha1, -, hap, -⟩ := hmemT a ha
    obtain ⟨hb1, -, hbp, -⟩ := hmemT b hb
    simp only at hab
    have hmina := Nat.Prime.pow_minFac hap (by omega : a.1 ≠ 0)
    have hminb := Nat.Prime.pow_minFac hbp (by omega : b.1 ≠ 0)
    have hpeq : a.2 = b.2 := by rw [← hmina, ← hminb, hab]
    have heeq : a.1 = b.1 := by
      rw [hpeq] at hab
      exact Nat.pow_right_injective hbp.two_le hab
    exact Prod.ext heeq hpeq
  have himg : T.image (fun q : ℕ × ℕ => q.2 ^ q.1) ⊆ Finset.Icc 1 y := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨h1, -, hp, hle⟩ := hmemT q hq
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, hle⟩
  have hsub : ∑ n ∈ T.image (fun q : ℕ × ℕ => q.2 ^ q.1),
      (((mFreeIndicator M n : ℤ) : ℝ) * ((n.minFac : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 y,
          (((mFreeIndicator M n : ℤ) : ℝ) * ((n.minFac : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun i _ _ => by positivity
  refine le_trans (le_of_eq ?_) hsub
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨h1, h2, hp, hle⟩ := hmemT q hq
  have hlt : q.1 < M := by omega
  have hp0 : (0 : ℝ) < ((q.2 : ℕ) : ℝ) := by exact_mod_cast hp.pos
  rw [Nat.Prime.pow_minFac hp (by omega : q.1 ≠ 0),
    mFreeIndicator_apply_prime_pow hM hp, if_pos hlt]
  push_cast
  rw [one_mul, ← Real.rpow_natCast (((q.2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) 2,
    ← Real.rpow_mul hp0.le,
    show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]

/-- **The calibrated multi-scale detector.**  Rung-dependent weights `c e` tune the
spectral line intensities: the `M`-free carrier with weight
`c(exponent)·(minFac n)^(-1/2)` — the exponent read off the carrier support as
`n.factorization n.minFac` — forces the calibrated spectrum
`∑_(e,p) c(e)²·p⁻¹`.  Matching the profile `c` to a carrier's second moment reads off
which dilation rungs dominate it: the spectral decomposition of carriers by forced
prime content. -/
theorem calibrated_detector {M : ℕ} (hM : M ≠ 0) (c : ℕ → ℝ) (y : ℕ) :
    ∑ q ∈ ((Finset.Icc 1 (M - 1)) ×ˢ Nat.primesBelow (y + 1)).filter
        (fun q => q.2 ^ q.1 ≤ y), (c q.1) ^ 2 * ((q.2 : ℕ) : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Icc 1 y,
          (((mFreeIndicator M n : ℤ) : ℝ) * (c (n.factorization n.minFac)
            * ((n.minFac : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2 := by
  set T := ((Finset.Icc 1 (M - 1)) ×ˢ Nat.primesBelow (y + 1)).filter
    (fun q => q.2 ^ q.1 ≤ y) with hT
  have hmemT : ∀ q ∈ T, 1 ≤ q.1 ∧ q.1 ≤ M - 1 ∧ q.2.Prime ∧ q.2 ^ q.1 ≤ y := by
    intro q hq
    obtain ⟨hqmem, hqle⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqmem
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hq1
    exact ⟨h1, h2, (Nat.mem_primesBelow.mp hq2).2, hqle⟩
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2 ^ q.1) T := by
    intro a ha b hb hab
    obtain ⟨ha1, -, hap, -⟩ := hmemT a ha
    obtain ⟨hb1, -, hbp, -⟩ := hmemT b hb
    simp only at hab
    have hmina := Nat.Prime.pow_minFac hap (by omega : a.1 ≠ 0)
    have hminb := Nat.Prime.pow_minFac hbp (by omega : b.1 ≠ 0)
    have hpeq : a.2 = b.2 := by rw [← hmina, ← hminb, hab]
    have heeq : a.1 = b.1 := by
      rw [hpeq] at hab
      exact Nat.pow_right_injective hbp.two_le hab
    exact Prod.ext heeq hpeq
  have himg : T.image (fun q : ℕ × ℕ => q.2 ^ q.1) ⊆ Finset.Icc 1 y := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨h1, -, hp, hle⟩ := hmemT q hq
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, hle⟩
  have hsub : ∑ n ∈ T.image (fun q : ℕ × ℕ => q.2 ^ q.1),
      (((mFreeIndicator M n : ℤ) : ℝ) * (c (n.factorization n.minFac)
        * ((n.minFac : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 y,
          (((mFreeIndicator M n : ℤ) : ℝ) * (c (n.factorization n.minFac)
            * ((n.minFac : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun i _ _ => by positivity
  refine le_trans (le_of_eq ?_) hsub
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨h1, h2, hp, hle⟩ := hmemT q hq
  have hlt : q.1 < M := by omega
  have hp0 : (0 : ℝ) < ((q.2 : ℕ) : ℝ) := by exact_mod_cast hp.pos
  rw [Nat.Prime.pow_minFac hp (by omega : q.1 ≠ 0),
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    mFreeIndicator_apply_prime_pow hM hp, if_pos hlt]
  push_cast
  rw [one_mul, mul_pow, ← Real.rpow_natCast (((q.2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) 2,
    ← Real.rpow_mul hp0.le,
    show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]

end RHTower
