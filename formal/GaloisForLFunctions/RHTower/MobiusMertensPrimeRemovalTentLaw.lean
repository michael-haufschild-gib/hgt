import GaloisForLFunctions.RHTower.MobiusMertensSelfConvolutionCriterion

/-!
# Prime-removal tent law for signed Mertens antidiagonals

The finite transfer kernel produced by removing one Euler prime is a discrete tent, hence
nonnegative.  The prime-2 kernel is pointwise minimal.  In contrast, simultaneous removal of any
two distinct primes creates a strictly negative unit-seed lobe.  This is the exact local sign wall
behind the remaining global signed-cancellation source in the Mertens antidiagonal RH criterion.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Truncated affine weight.  With `T = N + 1`, this is `(N - x + 1)₊`. -/
def mertensWindowHinge (T x : ℕ) : ℤ :=
  (T - x : ℕ)

/-- Second finite difference of a truncated affine weight. -/
def mertensDiscreteTent (A R S : ℕ) : ℤ :=
  (A : ℤ) - (A - R : ℕ) - (A - S : ℕ) + (A - (R + S) : ℕ)

/-- Every discrete tent is nonnegative. -/
theorem mertensDiscreteTent_nonneg (A R S : ℕ) :
    0 ≤ mertensDiscreteTent A R S := by
  simp only [mertensDiscreteTent]
  omega

/-- Exact support law for a nondegenerate discrete tent. -/
theorem mertensDiscreteTent_pos_iff
    {A R S : ℕ} (hR : 0 < R) (hS : 0 < S) :
    0 < mertensDiscreteTent A R S ↔ 0 < A ∧ A < R + S := by
  simp only [mertensDiscreteTent]
  omega

/-- A discrete tent is bounded by its left interval length. -/
theorem mertensDiscreteTent_le_left (A R S : ℕ) :
    mertensDiscreteTent A R S ≤ R := by
  simp only [mertensDiscreteTent]
  omega

/-- A discrete tent is bounded by its right interval length. -/
theorem mertensDiscreteTent_le_right (A R S : ℕ) :
    mertensDiscreteTent A R S ≤ S := by
  simp only [mertensDiscreteTent]
  omega

/-- Enlarging the left interval can only enlarge the transfer tent. -/
theorem mertensDiscreteTent_mono_left {A R R' S : ℕ} (hRR' : R ≤ R') :
    mertensDiscreteTent A R S ≤ mertensDiscreteTent A R' S := by
  simp only [mertensDiscreteTent]
  omega

/-- Enlarging the right interval can only enlarge the transfer tent. -/
theorem mertensDiscreteTent_mono_right {A R S S' : ℕ} (hSS' : S ≤ S') :
    mertensDiscreteTent A R S ≤ mertensDiscreteTent A R S' := by
  simp only [mertensDiscreteTent]
  omega

/-- Transfer kernel for one dilation factor `c + 1`. -/
def mertensOneDilationTransferKernel (c T r s : ℕ) : ℤ :=
  mertensWindowHinge T (r + s) -
    mertensWindowHinge T ((c + 1) * r + s) -
    mertensWindowHinge T (r + (c + 1) * s) +
    mertensWindowHinge T ((c + 1) * r + (c + 1) * s)

/-- Inclusion-exclusion for one removed dilation is exactly a discrete tent. -/
theorem mertensOneDilationTransferKernel_eq_tent (c T r s : ℕ) :
    mertensOneDilationTransferKernel c T r s =
      mertensDiscreteTent (T - (r + s)) (c * r) (c * s) := by
  have hleft : (c + 1) * r + s = (r + s) + c * r := by ring
  have hright : r + (c + 1) * s = (r + s) + c * s := by ring
  have hboth :
      (c + 1) * r + (c + 1) * s = (r + s) + (c * r + c * s) := by
    ring
  simp only [mertensOneDilationTransferKernel, mertensWindowHinge, mertensDiscreteTent]
  rw [hleft, hright, hboth]
  omega

/-- One-prime transfer kernels are nonnegative. -/
theorem mertensOneDilationTransferKernel_nonneg (c T r s : ℕ) :
    0 ≤ mertensOneDilationTransferKernel c T r s := by
  rw [mertensOneDilationTransferKernel_eq_tent]
  exact mertensDiscreteTent_nonneg _ _ _

/-- One-prime transfer kernels grow monotonically with the removed prime factor. -/
theorem mertensOneDilationTransferKernel_mono
    {c c' T r s : ℕ} (hcc' : c ≤ c') :
    mertensOneDilationTransferKernel c T r s ≤
      mertensOneDilationTransferKernel c' T r s := by
  rw [mertensOneDilationTransferKernel_eq_tent,
    mertensOneDilationTransferKernel_eq_tent]
  exact (mertensDiscreteTent_mono_left (Nat.mul_le_mul_right r hcc')).trans
    (mertensDiscreteTent_mono_right (Nat.mul_le_mul_right s hcc'))

/-- Prime-parameterized form of the one-dilation transfer kernel. -/
def mertensOnePrimeTransferKernel (p T r s : ℕ) : ℤ :=
  mertensOneDilationTransferKernel (p - 1) T r s

/-- The prime-parameterized kernel has the expected four-hinge formula. -/
theorem mertensOnePrimeTransferKernel_eq_four_hinges
    {p T r s : ℕ} (hp : 1 ≤ p) :
    mertensOnePrimeTransferKernel p T r s =
      mertensWindowHinge T (r + s) - mertensWindowHinge T (p * r + s) -
        mertensWindowHinge T (r + p * s) + mertensWindowHinge T (p * r + p * s) := by
  simp only [mertensOnePrimeTransferKernel, mertensOneDilationTransferKernel]
  rw [Nat.sub_add_cancel hp]

/-- Prime `2` is pointwise minimal among all genuine one-prime transfer kernels. -/
theorem mertensPrimeTwoTransferKernel_minimal
    {p T r s : ℕ} (hp : 2 ≤ p) :
    mertensOnePrimeTransferKernel 2 T r s ≤
      mertensOnePrimeTransferKernel p T r s := by
  exact mertensOneDilationTransferKernel_mono (by omega)

/-- Möbius seed with the Euler prime `p` removed. -/
def mobiusPrimeFreeCoefficient (p n : ℕ) : ℂ :=
  if p.Coprime n then mobiusComplexCoefficient n else 0

theorem mobiusComplexCoefficient_mul_prime_of_coprime
    {p r : ℕ} (hp : p.Prime) (hpr : p.Coprime r) :
    mobiusComplexCoefficient (p * r) = -mobiusComplexCoefficient r := by
  rw [mobiusComplexCoefficient, mobiusComplexCoefficient,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpr,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

theorem mobiusComplexCoefficient_mul_prime_of_not_coprime
    {p r : ℕ} (hpr : ¬p.Coprime r) :
    mobiusComplexCoefficient (p * r) = 0 := by
  rw [mobiusComplexCoefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
  · norm_num
  · intro hsquarefree
    exact hpr (Nat.coprime_of_squarefree_mul hsquarefree)

/-- Coefficientwise removal of one Euler prime. -/
theorem mobiusComplexCoefficient_eq_primeFree_difference
    {p n : ℕ} (hp : p.Prime) :
    mobiusComplexCoefficient n = mobiusPrimeFreeCoefficient p n -
      if p ∣ n then mobiusPrimeFreeCoefficient p (n / p) else 0 := by
  by_cases hpn : p ∣ n
  · obtain ⟨r, rfl⟩ := hpn
    have hp0 : p ≠ 0 := hp.ne_zero
    have hnot : ¬p.Coprime (p * r) := by
      intro h
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes h (dvd_refl p) (dvd_mul_right p r))
    by_cases hpr : p.Coprime r
    · rw [mobiusComplexCoefficient_mul_prime_of_coprime hp hpr]
      simp [mobiusPrimeFreeCoefficient, hnot, hpr, hp0]
    · rw [mobiusComplexCoefficient_mul_prime_of_not_coprime hpr]
      simp [mobiusPrimeFreeCoefficient, hnot, hpr, hp0]
  · have hcop : p.Coprime n := (hp.coprime_iff_not_dvd).mpr hpn
    simp [mobiusPrimeFreeCoefficient, hpn, hcop]

private theorem sum_prime_dilated_coefficients
    (c : ℕ → ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), if p ∣ n then c (n / p) else 0) =
      ∑ r ∈ Finset.range (N / p + 1), c r := by
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij' (fun r _ => p * r) (fun n _ => n / p) ?_ ?_ ?_ ?_ ?_).symm
  · intro r hr
    simp only [Finset.mem_range, Finset.mem_filter]
    have hrle : r ≤ N / p :=
      Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hr)
    exact ⟨by
      rw [Nat.lt_add_one_iff]
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hrle, dvd_mul_right p r⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ
      (by simpa [Nat.succ_eq_add_one] using hn.1)))
  · intro r _hr
    exact Nat.mul_div_cancel_left r hp
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro r _hr
    rw [Nat.mul_div_cancel_left r hp]

/-- Prime-free interval window whose coefficient is the Mertens partial sum. -/
def mobiusPrimeWindowPartialSum (p N : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico (N / p + 1) (N + 1), mobiusPrimeFreeCoefficient p r

/-- Exact one-prime window law for every Mertens partial sum. -/
theorem mobiusMertensPartialSum_eq_primeWindow
    {p : ℕ} (hp : p.Prime) (N : ℕ) :
    mobiusMertensPartialSum N = mobiusPrimeWindowPartialSum p N := by
  have hdiv := sum_prime_dilated_coefficients (mobiusPrimeFreeCoefficient p) hp.pos N
  rw [mobiusMertensPartialSum, mobiusPrimeWindowPartialSum]
  calc
    (∑ n ∈ Finset.range (N + 1), mobiusComplexCoefficient n) =
        ∑ n ∈ Finset.range (N + 1),
          (mobiusPrimeFreeCoefficient p n -
            if p ∣ n then mobiusPrimeFreeCoefficient p (n / p) else 0) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact mobiusComplexCoefficient_eq_primeFree_difference hp
    _ = (∑ n ∈ Finset.range (N + 1), mobiusPrimeFreeCoefficient p n) -
        ∑ n ∈ Finset.range (N + 1),
          (if p ∣ n then mobiusPrimeFreeCoefficient p (n / p) else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ n ∈ Finset.range (N + 1), mobiusPrimeFreeCoefficient p n) -
        ∑ r ∈ Finset.range (N / p + 1), mobiusPrimeFreeCoefficient p r := by
      rw [hdiv]
    _ = ∑ r ∈ Finset.Ico (N / p + 1) (N + 1),
        mobiusPrimeFreeCoefficient p r := by
      rw [Finset.sum_Ico_eq_sub]
      exact Nat.add_le_add_right (Nat.div_le_self N p) 1

/-- Self-convolution of the exact prime-free Mertens windows. -/
def mobiusPrimeWindowSelfConvolution (p N : ℕ) : ℂ :=
  ∑ ab ∈ Finset.antidiagonal N,
    mobiusPrimeWindowPartialSum p ab.1 * mobiusPrimeWindowPartialSum p ab.2

/-- The signed Mertens antidiagonal is exactly its one-prime window convolution. -/
theorem mobiusMertensSelfConvolution_eq_primeWindow
    {p : ℕ} (hp : p.Prime) (N : ℕ) :
    mobiusMertensSelfConvolution N = mobiusPrimeWindowSelfConvolution p N := by
  apply Finset.sum_congr rfl
  intro ab _hab
  rw [mobiusMertensPartialSum_eq_primeWindow hp,
    mobiusMertensPartialSum_eq_primeWindow hp]

/-- Existing RH-bearing second-Cesàro source, rewritten through any one-prime window. -/
theorem mobiusAdditiveTriangleSecondCesaro_eq_primeWindow
    {p : ℕ} (hp : p.Prime) (N : ℕ) :
    mobiusAdditiveTriangleSecondCesaro N = mobiusPrimeWindowSelfConvolution p N := by
  rw [mobiusAdditiveTriangleSecondCesaro_eq_mobiusMertensSelfConvolution,
    mobiusMertensSelfConvolution_eq_primeWindow hp]

/-- Expanded unit-seed transfer kernel after simultaneous removal of factors `p` and `q`. -/
def mertensTwoPrimeUnitTransferKernel (p q T : ℕ) : ℤ :=
  mertensWindowHinge T 2 -
    2 * mertensWindowHinge T (p + 1) -
    2 * mertensWindowHinge T (q + 1) +
    2 * mertensWindowHinge T (p * q + 1) +
    mertensWindowHinge T (2 * p) +
    2 * mertensWindowHinge T (p + q) -
    2 * mertensWindowHinge T (p + p * q) +
    mertensWindowHinge T (2 * q) -
    2 * mertensWindowHinge T (q + p * q) +
    mertensWindowHinge T (2 * (p * q))

/-- Index of a guaranteed negative lobe for two removed factors. -/
def mertensTwoPrimeSignWallIndex (p q : ℕ) : ℕ :=
  max (q + 1) (2 * p - 1)

/-- **Universal two-prime sign wall.** Every pair `2 ≤ p < q` creates a strictly negative
unit-seed transfer coefficient. -/
theorem mertensTwoPrimeUnitTransferKernel_sign_wall
    {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) :
    mertensTwoPrimeUnitTransferKernel p q
      (mertensTwoPrimeSignWallIndex p q + 1) < 0 := by
  let k := mertensTwoPrimeSignWallIndex p q
  have hkq : q + 1 ≤ k := by
    exact Nat.le_max_left _ _
  have hkp : 2 * p - 1 ≤ k := by
    exact Nat.le_max_right _ _
  have hk2q : k < 2 * q := by
    dsimp only [k, mertensTwoPrimeSignWallIndex]
    rw [max_lt_iff]
    constructor <;> omega
  have h2q_pq : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp
  have hkpq : k + 1 ≤ p * q + 1 := by omega
  have hkp_pq : k + 1 ≤ p + p * q := by omega
  have hkq_pq : k + 1 ≤ q + p * q := by omega
  have hk2pq : k + 1 ≤ 2 * (p * q) := by omega
  have hk2q' : k + 1 ≤ 2 * q := by omega
  rw [mertensTwoPrimeUnitTransferKernel]
  simp only [mertensWindowHinge]
  rw [Nat.sub_eq_zero_of_le hkpq, Nat.sub_eq_zero_of_le hkp_pq,
    Nat.sub_eq_zero_of_le hk2q', Nat.sub_eq_zero_of_le hkq_pq,
    Nat.sub_eq_zero_of_le hk2pq]
  dsimp only [k, mertensTwoPrimeSignWallIndex]
  rcases le_total (2 * p - 1) (q + 1) with h | h
  · rw [max_eq_left h]
    omega
  · rw [max_eq_right h]
    omega

/-- Minimal explicit negative lobe: factors `2` and `3`, total degree `4`. -/
theorem mertensTwoPrimeUnitTransferKernel_two_three :
    mertensTwoPrimeUnitTransferKernel 2 3 5 = -2 := by
  norm_num [mertensTwoPrimeUnitTransferKernel, mertensWindowHinge]

end

end RHTower
