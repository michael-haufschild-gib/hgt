import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import GaloisForLFunctions.RHTower.MollifierDetection

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

/-- **The abstract forced-content law, core form.**  Any quadratic functional over an
index set containing the squares of a prime family, whose coefficients at those prime
squares are at least `δ·p^(-1/2)` in absolute value, dominates `δ²` times the prime
reciprocal mass of the family.  Prime squares inject their full reciprocal weight into
every square-supported quadratic functional. -/
theorem primeMass_le_sq_sum_of_forced {S P : Finset ℕ} {b : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hmem : ∀ p ∈ P, p ^ 2 ∈ S)
    (hval : ∀ p ∈ P, δ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |b (p ^ 2)|) :
    δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ ≤ ∑ k ∈ S, (b k) ^ 2 := by
  have himg : P.image (fun p => p ^ 2) ⊆ S := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact hmem p hp
  have hsub : ∑ n ∈ P.image (fun p => p ^ 2), (b n) ^ 2 ≤ ∑ k ∈ S, (b k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun i _ _ => by positivity
  refine le_trans ?_ hsub
  rw [Finset.sum_image ((Nat.pow_left_injective two_ne_zero).injOn), Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hsq : (δ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ (b (p ^ 2)) ^ 2 := by
    rw [← sq_abs (b (p ^ 2))]
    exact pow_le_pow_left₀ (by positivity) (hval p hp) 2
  refine le_trans (le_of_eq ?_) hsq
  rw [mul_pow, ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) 2,
    ← Real.rpow_mul (Nat.cast_nonneg p),
    show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]

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

end RHTower
