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

/-- Antidiagonal count of a doubly half-lined lattice equals a window hinge:
`∑_{a+b=N} 1_{α≤a} 1_{β≤b} = (N + 1 - (α + β))₊`. -/
private theorem antidiagonalHalfLineCount (N α β : ℕ) :
    (∑ ab ∈ Finset.antidiagonal N,
      (if α ≤ ab.1 then (1 : ℤ) else 0) * (if β ≤ ab.2 then 1 else 0))
      = mertensWindowHinge (N + 1) (α + β) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hcongr : ∀ a ∈ Finset.range (N + 1),
      (if α ≤ a then (1 : ℤ) else 0) * (if β ≤ N - a then 1 else 0)
        = if α ≤ a ∧ a + β ≤ N then 1 else 0 := by
    intro a ha
    simp only [Finset.mem_range] at ha
    by_cases h1 : α ≤ a
    · by_cases h2 : a + β ≤ N
      · rw [if_pos h1, if_pos (show β ≤ N - a by omega), one_mul, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg (show ¬ β ≤ N - a by omega), mul_zero,
          if_neg (by rintro ⟨_, h⟩; exact h2 h)]
    · rw [if_neg h1, zero_mul, if_neg (by rintro ⟨h, _⟩; exact h1 h)]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfilter : Finset.filter (fun a => α ≤ a ∧ a + β ≤ N) (Finset.range (N + 1))
      = Finset.Ico α (N + 1 - β) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfilter, Nat.card_Ico]
  simp only [mertensWindowHinge]; omega

/-- A two-sided window indicator splits into a difference of two half-line indicators. -/
private theorem twoSidedWindowIndicator {p : ℕ} (hp : 1 ≤ p) (x c : ℕ) :
    (if c ≤ x ∧ x < p * c then (1 : ℤ) else 0)
      = (if c ≤ x then 1 else 0) - (if p * c ≤ x then 1 else 0) := by
  by_cases h1 : c ≤ x
  · by_cases h2 : p * c ≤ x
    · rw [if_pos h1, if_pos h2, if_neg (by rintro ⟨_, h⟩; omega)]; ring
    · rw [if_pos h1, if_neg h2, if_pos ⟨h1, by omega⟩]; ring
  · have hc : c ≤ p * c := Nat.le_mul_of_pos_left c (by omega)
    rw [if_neg h1, if_neg (show ¬ p * c ≤ x by omega), if_neg (by rintro ⟨h, _⟩; exact h1 h)]
    ring

/-- The antidiagonal count of the two paired window indicators is exactly the one-prime transfer
kernel, by inclusion–exclusion over the four half-line counts. -/
private theorem antidiagonalWindowKernelCount {p : ℕ} (hp : 1 ≤ p) (N r s : ℕ) :
    (∑ ab ∈ Finset.antidiagonal N,
      (if r ≤ ab.1 ∧ ab.1 < p * r then (1 : ℤ) else 0)
        * (if s ≤ ab.2 ∧ ab.2 < p * s then 1 else 0))
      = mertensOnePrimeTransferKernel p (N + 1) r s := by
  rw [mertensOnePrimeTransferKernel_eq_four_hinges hp]
  have expand : ∀ ab : ℕ × ℕ,
      (if r ≤ ab.1 ∧ ab.1 < p * r then (1 : ℤ) else 0)
        * (if s ≤ ab.2 ∧ ab.2 < p * s then 1 else 0)
      = (if r ≤ ab.1 then 1 else 0) * (if s ≤ ab.2 then 1 else 0)
        - (if r ≤ ab.1 then 1 else 0) * (if p * s ≤ ab.2 then 1 else 0)
        - (if p * r ≤ ab.1 then 1 else 0) * (if s ≤ ab.2 then 1 else 0)
        + (if p * r ≤ ab.1 then 1 else 0) * (if p * s ≤ ab.2 then 1 else 0) := by
    intro ab
    rw [twoSidedWindowIndicator hp ab.1 r, twoSidedWindowIndicator hp ab.2 s]; ring
  rw [Finset.sum_congr rfl (fun ab _ => expand ab), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    antidiagonalHalfLineCount, antidiagonalHalfLineCount, antidiagonalHalfLineCount,
    antidiagonalHalfLineCount]
  ring

/-- Complex form of the window-kernel count. -/
private theorem antidiagonalWindowKernelCount_complex {p : ℕ} (hp : 1 ≤ p) (N r s : ℕ) :
    (∑ ab ∈ Finset.antidiagonal N,
      (if r ≤ ab.1 ∧ ab.1 < p * r then (1 : ℂ) else 0)
        * (if s ≤ ab.2 ∧ ab.2 < p * s then 1 else 0))
      = ((mertensOnePrimeTransferKernel p (N + 1) r s : ℤ) : ℂ) := by
  rw [← antidiagonalWindowKernelCount hp N r s]
  push_cast
  apply Finset.sum_congr rfl
  intro ab _
  split_ifs <;> simp

/-- Prime-free Mertens window as a full-range weighted window indicator sum. -/
private theorem primeWindowPartialSum_flat {p : ℕ} (hp : p.Prime) (N a : ℕ) (ha : a ≤ N) :
    mobiusPrimeWindowPartialSum p a
      = ∑ r ∈ Finset.range (N + 1),
          (if r ≤ a ∧ a < p * r then (1 : ℂ) else 0) * mobiusPrimeFreeCoefficient p r := by
  have hstep : (∑ r ∈ Finset.range (N + 1),
      (if r ≤ a ∧ a < p * r then (1 : ℂ) else 0) * mobiusPrimeFreeCoefficient p r)
      = ∑ r ∈ Finset.range (N + 1),
          if r ≤ a ∧ a < p * r then mobiusPrimeFreeCoefficient p r else 0 := by
    apply Finset.sum_congr rfl; intro r _; split_ifs <;> simp
  rw [hstep, ← Finset.sum_filter]
  unfold mobiusPrimeWindowPartialSum
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext r
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
  have hdiv : a < p * r ↔ a / p + 1 ≤ r := by
    rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hp.pos, Nat.mul_comm]
  omega

/-- **Flattened one-prime tent double-sum law (equation (4)).**  For every prime `p`, the signed
Mertens antidiagonal `U(N)` is the exact finite prime-free double sum weighted by the one-prime
transfer kernel:
`U(N) = ∑_{r,s} μ⁽ᵖ⁾(r) μ⁽ᵖ⁾(s) K_{p,N}(r,s)`. -/
theorem mobiusMertensSelfConvolution_eq_primeKernelDoubleSum {p : ℕ} (hp : p.Prime) (N : ℕ) :
    mobiusMertensSelfConvolution N
      = ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
          mobiusPrimeFreeCoefficient p r * mobiusPrimeFreeCoefficient p s
            * ((mertensOnePrimeTransferKernel p (N + 1) r s : ℤ) : ℂ) := by
  rw [mobiusMertensSelfConvolution_eq_primeWindow hp, mobiusPrimeWindowSelfConvolution]
  have hexp : ∀ ab ∈ Finset.antidiagonal N,
      mobiusPrimeWindowPartialSum p ab.1 * mobiusPrimeWindowPartialSum p ab.2
      = ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
          ((if r ≤ ab.1 ∧ ab.1 < p * r then (1 : ℂ) else 0) * mobiusPrimeFreeCoefficient p r)
            * ((if s ≤ ab.2 ∧ ab.2 < p * s then (1 : ℂ) else 0) * mobiusPrimeFreeCoefficient p s) := by
    intro ab hab
    rw [Finset.mem_antidiagonal] at hab
    rw [primeWindowPartialSum_flat hp N ab.1 (by omega),
      primeWindowPartialSum_flat hp N ab.2 (by omega), Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← antidiagonalWindowKernelCount_complex hp.pos N r s, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _
  ring

end

end RHTower
