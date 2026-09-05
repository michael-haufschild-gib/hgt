import GaloisForLFunctions.RHTower.CoprimeBlockCarryTransgression

/-!
# Literal Euler-deletion Dirichlet Gram law

Exact infinite covariance of `1 - p [p ∣ n]`, with the source weight `n^(-α)`.
All moduli retain their coefficients, and shared divisibility is recorded by `lcm`.
This is a standard Dirichlet-series identity, not a replication/dilation coherence
theorem, an RH producer, or a new positivity principle.
-/

namespace RHTower

open scoped BigOperators

noncomputable def deletionDirichletWeight (α : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-α)

noncomputable def deletionDirichletMass (α : ℝ) : ℝ :=
  ∑' n : ℕ, deletionDirichletWeight α n

noncomputable def deletionDivisibilityWeight (α : ℝ) (p n : ℕ) : ℝ :=
  if p ∣ n then deletionDirichletWeight α n else 0

theorem summable_deletionDirichletWeight {α : ℝ} (hα : 1 < α) :
    Summable (deletionDirichletWeight α) := by
  exact Real.summable_nat_rpow.mpr (by linarith)

theorem summable_deletionDivisibilityWeight {α : ℝ} (hα : 1 < α) (p : ℕ) :
    Summable (deletionDivisibilityWeight α p) := by
  apply ((summable_deletionDirichletWeight hα).indicator {n : ℕ | p ∣ n}).congr
  intro n
  simp [deletionDivisibilityWeight, Set.indicator_apply]

/-- Multiples retain the exact dilation coefficient, with no discarded tail. -/
theorem tsum_deletionDivisibilityWeight (α : ℝ) {p : ℕ} (hp : 0 < p) :
    ∑' n, deletionDivisibilityWeight α p n =
      (p : ℝ) ^ (-α) * deletionDirichletMass α := by
  have hi : Function.Injective (fun n : ℕ => p * n) := fun _ _ h => Nat.mul_left_cancel hp h
  have hs : Function.support (deletionDivisibilityWeight α p) ⊆
      Set.range (fun n : ℕ => p * n) := by
    intro n hn
    have hd : p ∣ n := by
      by_contra hd
      exact hn (by simp [deletionDivisibilityWeight, hd])
    obtain ⟨k, rfl⟩ := hd
    exact ⟨k, rfl⟩
  rw [← hi.tsum_eq hs]
  simp only [deletionDivisibilityWeight, dvd_mul_right, if_true,
    deletionDirichletWeight, Nat.cast_mul]
  calc
    (∑' n : ℕ, ((p : ℝ) * n) ^ (-α)) =
        ∑' n : ℕ, (p : ℝ) ^ (-α) * (n : ℝ) ^ (-α) := by
      apply tsum_congr
      intro n
      exact Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg n)
    _ = _ := tsum_mul_left

theorem deletionDirichletMass_pos {α : ℝ} (hα : 1 < α) :
    0 < deletionDirichletMass α := by
  exact (summable_deletionDirichletWeight hα).tsum_pos
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) 1 (by simp [deletionDirichletWeight])

/-- The normalization is the actual Riemann zeta value, not an independently chosen budget. -/
theorem deletionDirichletMass_eq_riemannZeta {α : ℝ} (hα : 1 < α) :
    (deletionDirichletMass α : ℂ) = riemannZeta (α : ℂ) := by
  rw [deletionDirichletMass, Complex.ofReal_tsum,
    zeta_eq_tsum_one_div_nat_cpow (by simpa using hα)]
  apply tsum_congr
  intro n
  rw [deletionDirichletWeight, Real.rpow_neg (Nat.cast_nonneg n),
    Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp

private theorem deletionDirichlet_first_expansion (α : ℝ) (p n : ℕ) :
    (blockDeletionCoefficient p n : ℝ) * deletionDirichletWeight α n =
      deletionDirichletWeight α n - p * deletionDivisibilityWeight α p n := by
  by_cases h : p ∣ n
  · simp [blockDeletionCoefficient, deletionDivisibilityWeight, h]
    ring
  · simp [blockDeletionCoefficient, deletionDivisibilityWeight, h]

theorem summable_deletionDirichlet_first {α : ℝ} (hα : 1 < α) (p : ℕ) :
    Summable (fun n => (blockDeletionCoefficient p n : ℝ) * deletionDirichletWeight α n) := by
  simp_rw [deletionDirichlet_first_expansion]
  exact (summable_deletionDirichletWeight hα).sub
    ((summable_deletionDivisibilityWeight hα p).mul_left (p : ℝ))

/-- The first moment is computed from the same literal coefficient stream as the Gram matrix. -/
theorem tsum_deletionDirichlet_first {α : ℝ} (hα : 1 < α)
    {p : ℕ} (hp : 0 < p) :
    ∑' n, (blockDeletionCoefficient p n : ℝ) * deletionDirichletWeight α n =
      deletionDirichletMass α * (1 - p * (p : ℝ) ^ (-α)) := by
  simp_rw [deletionDirichlet_first_expansion]
  rw [(summable_deletionDirichletWeight hα).tsum_sub
    ((summable_deletionDivisibilityWeight hα p).mul_left (p : ℝ)), tsum_mul_left,
    tsum_deletionDivisibilityWeight α hp]
  unfold deletionDirichletMass
  ring

private theorem deletionDirichlet_gram_expansion (α : ℝ) (p q n : ℕ) :
    (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) *
      deletionDirichletWeight α n =
    deletionDirichletWeight α n - p * deletionDivisibilityWeight α p n -
      q * deletionDivisibilityWeight α q n +
      (p : ℝ) * q * deletionDivisibilityWeight α (Nat.lcm p q) n := by
  by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;>
    simp [blockDeletionCoefficient, deletionDivisibilityWeight, Nat.lcm_dvd_iff, hp, hq] <;> ring

/-- Absolute cofinal admission is proved from the literal arithmetic coefficients. -/
theorem summable_deletionDirichlet_gram {α : ℝ} (hα : 1 < α) (p q : ℕ) :
    Summable (fun n => (blockDeletionCoefficient p n : ℝ) *
      (blockDeletionCoefficient q n : ℝ) * deletionDirichletWeight α n) := by
  simp_rw [deletionDirichlet_gram_expansion]
  exact (((summable_deletionDirichletWeight hα).sub
    ((summable_deletionDivisibilityWeight hα p).mul_left (p : ℝ))).sub
    ((summable_deletionDivisibilityWeight hα q).mul_left (q : ℝ))).add
    ((summable_deletionDivisibilityWeight hα (Nat.lcm p q)).mul_left ((p : ℝ) * q))

/-- Exact source Gram law for all positive integer moduli, including shared factors. -/
theorem tsum_deletionDirichlet_gram {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∑' n, (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) *
      deletionDirichletWeight α n =
    deletionDirichletMass α * (1 - p * (p : ℝ) ^ (-α) - q * (q : ℝ) ^ (-α) +
      (p : ℝ) * q * (Nat.lcm p q : ℝ) ^ (-α)) := by
  have h0 := summable_deletionDirichletWeight hα
  have h1 := (summable_deletionDivisibilityWeight hα p).mul_left (p : ℝ)
  have h2 := (summable_deletionDivisibilityWeight hα q).mul_left (q : ℝ)
  have h3 := (summable_deletionDivisibilityWeight hα (Nat.lcm p q)).mul_left ((p : ℝ) * q)
  simp_rw [deletionDirichlet_gram_expansion]
  rw [((h0.sub h1).sub h2).tsum_add h3, (h0.sub h1).tsum_sub h2, h0.tsum_sub h1]
  simp only [tsum_mul_left]
  rw [tsum_deletionDivisibilityWeight α hp, tsum_deletionDivisibilityWeight α hq,
    tsum_deletionDivisibilityWeight α (Nat.lcm_pos hp hq)]
  unfold deletionDirichletMass
  ring

/-- Coprime cross terms factor; independence is not uncentered cancellation. -/
theorem tsum_deletionDirichlet_gram_of_coprime {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    ∑' n, (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) *
      deletionDirichletWeight α n =
    deletionDirichletMass α * (1 - p * (p : ℝ) ^ (-α)) *
      (1 - q * (q : ℝ) ^ (-α)) := by
  rw [tsum_deletionDirichlet_gram hα hp hq, hpq.lcm_eq_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
  ring

/-- The diagonal is not the product of its first moments: its retained variance is explicit. -/
theorem tsum_deletionDirichlet_gram_self {α : ℝ} (hα : 1 < α)
    {p : ℕ} (hp : 0 < p) :
    ∑' n, (blockDeletionCoefficient p n : ℝ) ^ 2 * deletionDirichletWeight α n =
      deletionDirichletMass α *
        ((1 - p * (p : ℝ) ^ (-α)) ^ 2 +
          (p : ℝ) ^ 2 * (p : ℝ) ^ (-α) * (1 - (p : ℝ) ^ (-α))) := by
  simp_rw [pow_two]
  rw [tsum_deletionDirichlet_gram hα hp hp, Nat.lcm_self]
  ring

/-- Centering cannot erase even one nontrivial modulus' diagonal source energy. -/
theorem deletionDirichlet_centeredVariance_pos {α : ℝ} (hα : 1 < α)
    {p : ℕ} (hp : 1 < p) :
    0 < deletionDirichletMass α * (p : ℝ) ^ 2 * (p : ℝ) ^ (-α) *
      (1 - (p : ℝ) ^ (-α)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpow := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < p) (-α)
  have hlt := Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith : -α < 0)
  exact mul_pos (mul_pos (mul_pos (deletionDirichletMass_pos hα)
    (sq_pos_of_pos (by linarith))) hpow) (by linarith)

/-- The squared source mass strictly exceeds its normalized first-moment square. -/
theorem deletionDirichlet_gram_self_gt_mean_square {α : ℝ} (hα : 1 < α)
    {p : ℕ} (hp : 1 < p) :
    deletionDirichletMass α * (1 - p * (p : ℝ) ^ (-α)) ^ 2 <
      ∑' n, (blockDeletionCoefficient p n : ℝ) ^ 2 * deletionDirichletWeight α n := by
  rw [tsum_deletionDirichlet_gram_self hα (by omega : 0 < p)]
  have h := deletionDirichlet_centeredVariance_pos hα hp
  nlinarith

/-- Centering uses the proved first moment of the literal source. -/
noncomputable def deletionCenteredCoefficient (α : ℝ) (p n : ℕ) : ℝ :=
  (blockDeletionCoefficient p n : ℝ) - (1 - p * (p : ℝ) ^ (-α))

/-- Exact centered covariance, retaining the arithmetic overlap term at every modulus pair. -/
theorem tsum_deletionCenteredCoefficient_pair {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∑' n, deletionCenteredCoefficient α p n * deletionCenteredCoefficient α q n *
      deletionDirichletWeight α n =
    deletionDirichletMass α * (p : ℝ) * q *
      ((Nat.lcm p q : ℝ) ^ (-α) - (p : ℝ) ^ (-α) * (q : ℝ) ^ (-α)) := by
  let mp : ℝ := 1 - p * (p : ℝ) ^ (-α)
  let mq : ℝ := 1 - q * (q : ℝ) ^ (-α)
  have he (n : ℕ) :
      deletionCenteredCoefficient α p n * deletionCenteredCoefficient α q n *
          deletionDirichletWeight α n =
      (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) *
          deletionDirichletWeight α n -
        mq * ((blockDeletionCoefficient p n : ℝ) * deletionDirichletWeight α n) -
        mp * ((blockDeletionCoefficient q n : ℝ) * deletionDirichletWeight α n) +
        (mp * mq) * deletionDirichletWeight α n := by
    dsimp [deletionCenteredCoefficient, mp, mq]
    ring
  have h0 := summable_deletionDirichlet_gram hα p q
  have h1 := (summable_deletionDirichlet_first hα p).mul_left mq
  have h2 := (summable_deletionDirichlet_first hα q).mul_left mp
  have h3 := (summable_deletionDirichletWeight hα).mul_left (mp * mq)
  simp_rw [he]
  rw [((h0.sub h1).sub h2).tsum_add h3, (h0.sub h1).tsum_sub h2, h0.tsum_sub h1]
  simp only [tsum_mul_left]
  rw [tsum_deletionDirichlet_gram hα hp hq, tsum_deletionDirichlet_first hα hp,
    tsum_deletionDirichlet_first hα hq]
  dsimp [mp, mq, deletionDirichletMass]
  ring

/-- Coprime source channels are orthogonal only after subtracting their actual means. -/
theorem tsum_deletionCenteredCoefficient_pair_of_coprime {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    ∑' n, deletionCenteredCoefficient α p n * deletionCenteredCoefficient α q n *
      deletionDirichletWeight α n = 0 := by
  rw [tsum_deletionCenteredCoefficient_pair hα hp hq, hpq.lcm_eq_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
  ring

/-- The centered same-modulus covariance remains strictly positive. -/
theorem tsum_deletionCenteredCoefficient_sq_pos {α : ℝ} (hα : 1 < α)
    {p : ℕ} (hp : 1 < p) :
    0 < ∑' n, (deletionCenteredCoefficient α p n) ^ 2 * deletionDirichletWeight α n := by
  simp_rw [pow_two]
  rw [tsum_deletionCenteredCoefficient_pair hα (by omega : 0 < p) (by omega : 0 < p),
    Nat.lcm_self]
  convert deletionDirichlet_centeredVariance_pos hα hp using 1
  ring

/-- Literal complex Mellin source, with the ordinary integer deletion coefficient. -/
noncomputable def deletionMellinSource (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  ((blockDeletionCoefficient p n : ℝ) : ℂ) * (n : ℂ) ^ (-s)

/-- Pointwise Hermitian pairing retains the coefficient product and the exact doubled abscissa. -/
theorem deletionMellinSource_pair_re {s : ℂ} (hs : 1 / 2 < s.re) (p q n : ℕ) :
    (deletionMellinSource p s n * star (deletionMellinSource q s n)).re =
      (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) *
        deletionDirichletWeight (2 * s.re) n := by
  by_cases hn : n = 0
  · subst n
    have hs0 : -s ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.zero_re] at hh
      linarith
    simp [deletionMellinSource, deletionDirichletWeight, Complex.zero_cpow hs0,
      Real.zero_rpow (by linarith : -(2 * s.re) ≠ 0)]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnorm : Complex.normSq ((n : ℂ) ^ (-s)) =
        deletionDirichletWeight (2 * s.re) n := by
      rw [Complex.normSq_eq_norm_sq]
      have h := Complex.norm_cpow_eq_rpow_re_of_pos hnR (-s)
      simp only [Complex.ofReal_natCast, Complex.neg_re] at h
      rw [h, pow_two, ← Real.rpow_add hnR]
      unfold deletionDirichletWeight
      congr 1
      ring
    rw [← hnorm]
    simp [deletionMellinSource, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring

/-- The full Hermitian pairing is real; the preceding real-part formula loses no Gram entry. -/
theorem deletionMellinSource_pair {s : ℂ} (hs : 1 / 2 < s.re) (p q n : ℕ) :
    deletionMellinSource p s n * star (deletionMellinSource q s n) =
      (((blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) *
        deletionDirichletWeight (2 * s.re) n : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa using deletionMellinSource_pair_re hs p q n
  · simp [deletionMellinSource, Complex.mul_im, Complex.mul_re]
    ring

/-- The completed literal Mellin-source Gram is the same LCM kernel, with no Xi-zero premise. -/
theorem tsum_deletionMellinSource_pair_re {s : ℂ} (hs : 1 / 2 < s.re)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∑' n, (deletionMellinSource p s n * star (deletionMellinSource q s n)).re =
      deletionDirichletMass (2 * s.re) *
        (1 - p * (p : ℝ) ^ (-(2 * s.re)) - q * (q : ℝ) ^ (-(2 * s.re)) +
          (p : ℝ) * q * (Nat.lcm p q : ℝ) ^ (-(2 * s.re))) := by
  simp_rw [deletionMellinSource_pair_re hs]
  exact tsum_deletionDirichlet_gram (by linarith) hp hq

/-- Absolute convergence of the actual, not fitted, Mellin-source pairing. -/
theorem summable_norm_deletionMellinSource_pair_re {s : ℂ} (hs : 1 / 2 < s.re)
    (p q : ℕ) :
    Summable (fun n => ‖(deletionMellinSource p s n * star (deletionMellinSource q s n)).re‖) := by
  simp_rw [deletionMellinSource_pair_re hs]
  exact (summable_deletionDirichlet_gram (by linarith) p q).norm

/-- Absolute convergence of the full complex source pairing, before taking any real part. -/
theorem summable_norm_deletionMellinSource_pair {s : ℂ} (hs : 1 / 2 < s.re)
    (p q : ℕ) :
    Summable (fun n => ‖deletionMellinSource p s n * star (deletionMellinSource q s n)‖) := by
  simp_rw [deletionMellinSource_pair hs]
  exact (Complex.summable_ofReal.mpr
    (summable_deletionDirichlet_gram (by linarith) p q)).norm

/-- Complete complex Gram law with the literal zeta normalization and all modulus coefficients. -/
theorem tsum_deletionMellinSource_pair {s : ℂ} (hs : 1 / 2 < s.re)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∑' n, deletionMellinSource p s n * star (deletionMellinSource q s n) =
      riemannZeta ((2 * s.re : ℝ) : ℂ) *
        ((1 - p * (p : ℝ) ^ (-(2 * s.re)) - q * (q : ℝ) ^ (-(2 * s.re)) +
          (p : ℝ) * q * (Nat.lcm p q : ℝ) ^ (-(2 * s.re)) : ℝ) : ℂ) := by
  simp_rw [deletionMellinSource_pair hs]
  rw [← Complex.ofReal_tsum, tsum_deletionDirichlet_gram (by linarith) hp hq,
    Complex.ofReal_mul, deletionDirichletMass_eq_riemannZeta (by linarith)]

end RHTower
