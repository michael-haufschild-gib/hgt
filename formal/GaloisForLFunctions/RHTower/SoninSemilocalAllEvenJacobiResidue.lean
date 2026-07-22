import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation
import GaloisForLFunctions.RHTower.WeldRateLattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# All-even Jacobi signs in the semilocal Sonin source

This module isolates the exact closed Fourier kernel that drives the semilocal all-even
Jacobi residue tower.  It proves the alternating sign at every positive even degree, the
strict positive-weight packet theorem, and the unique-factorization fact excluding every
nontrivial zero prime-log frequency.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- The positive normalization appearing in the archimedean Jacobi Fourier transform. -/
def semilocalArchimedeanJacobiNormalization (n : ℕ) : ℝ :=
  Real.sqrt ((Nat.factorial (2 * n) : ℝ)) /
    ((2 : ℝ) ^ n * (Nat.factorial n : ℝ))

theorem semilocalArchimedeanJacobiNormalization_pos (n : ℕ) :
    0 < semilocalArchimedeanJacobiNormalization n := by
  unfold semilocalArchimedeanJacobiNormalization
  exact div_pos (Real.sqrt_pos.2 (by positivity)) (mul_pos (by positivity) (by positivity))

/-- The closed Fourier transform predicted by the archimedean Jacobi recurrence. -/
def semilocalArchimedeanJacobiFourierClosedForm (n : ℕ) (t : ℝ) : ℂ :=
  Complex.I ^ n * semilocalArchimedeanJacobiNormalization n *
    semilocalArchimedeanCharacteristic t * Real.tanh t ^ n

/-- At even degree the complex phase is the real alternating sign. -/
theorem semilocalArchimedeanJacobiFourierClosedForm_even (k : ℕ) (t : ℝ) :
    semilocalArchimedeanJacobiFourierClosedForm (2 * k) t =
      ((-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
        semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k) : ℝ) := by
  rw [semilocalArchimedeanJacobiFourierClosedForm, pow_mul, Complex.I_sq]
  norm_cast

/-- The real all-even Fourier kernel. -/
def semilocalArchimedeanEvenJacobiKernel (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
    semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k)

theorem semilocalArchimedeanCharacteristic_pos (t : ℝ) :
    0 < semilocalArchimedeanCharacteristic t :=
  Real.rpow_pos_of_pos (Real.cosh_pos t) (-(1 : ℝ) / 2)

theorem tanh_even_pow_pos {k : ℕ} {t : ℝ} (ht : t ≠ 0) :
    0 < Real.tanh t ^ (2 * k) := by
  have htanh : Real.tanh t ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have hsinh : Real.sinh t ≠ 0 := by
      simpa using Real.sinh_strictMono.injective.ne ht
    exact div_ne_zero hsinh (Real.cosh_pos t).ne'
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero htanh) k

/-- Every nonzero frequency has the rigid sign `(-1)^k` at every even degree `2k`. -/
theorem semilocalArchimedeanEvenJacobiKernel_signed_pos
    {k : ℕ} {t : ℝ} (ht : t ≠ 0) :
    0 < (-1 : ℝ) ^ k * semilocalArchimedeanEvenJacobiKernel k t := by
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [semilocalArchimedeanEvenJacobiKernel]
  calc
    0 < semilocalArchimedeanJacobiNormalization (2 * k) *
        semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k) :=
      mul_pos
        (mul_pos (semilocalArchimedeanJacobiNormalization_pos _)
          (semilocalArchimedeanCharacteristic_pos t))
        (tanh_even_pow_pos ht)
    _ = (-1 : ℝ) ^ k *
        (((-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
          semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k))) := by
      symm
      calc
        (-1 : ℝ) ^ k *
            (((-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
              semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k))) =
            ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
              (semilocalArchimedeanJacobiNormalization (2 * k) *
                semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k)) := by ring
        _ = semilocalArchimedeanJacobiNormalization (2 * k) *
              semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k) := by
          rw [hsign, one_mul]

/-- A nonempty positive packet of nonzero frequencies retains the same strict alternating sign. -/
theorem semilocalArchimedeanEvenJacobiKernel_weightedPacket_signed_pos
    {ι : Type*} {k : ℕ} (s : Finset ι) (hs : s.Nonempty)
    (weight frequency : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hfrequency : ∀ i ∈ s, frequency i ≠ 0) :
    0 < (-1 : ℝ) ^ k *
      ∑ i ∈ s, weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_pos
  · intro i hi
    have hkernel :=
      semilocalArchimedeanEvenJacobiKernel_signed_pos (k := k) (hfrequency i hi)
    calc
      0 < weight i *
          ((-1 : ℝ) ^ k * semilocalArchimedeanEvenJacobiKernel k (frequency i)) :=
        mul_pos (hweight i hi) hkernel
      _ = (-1 : ℝ) ^ k *
          (weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i)) := by ring
  · exact hs

/-- Summable positive packets retain the strict all-even sign.  This is the limit theorem used
after the absolutely convergent semilocal Poisson expansion. -/
theorem semilocalArchimedeanEvenJacobiKernel_weightedSeries_signed_pos
    {ι : Type*} [Nonempty ι] {k : ℕ}
    (weight frequency : ι → ℝ)
    (hweight : ∀ i, 0 < weight i) (hfrequency : ∀ i, frequency i ≠ 0)
    (hsummable : Summable fun i =>
      weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i)) :
    0 < (-1 : ℝ) ^ k * ∑' i,
      weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i) := by
  let i₀ : ι := Classical.choice inferInstance
  have hterm (i : ι) :
      0 < (-1 : ℝ) ^ k *
        (weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i)) := by
    have hkernel :=
      semilocalArchimedeanEvenJacobiKernel_signed_pos (k := k) (hfrequency i)
    calc
      0 < weight i *
          ((-1 : ℝ) ^ k * semilocalArchimedeanEvenJacobiKernel k (frequency i)) :=
        mul_pos (hweight i) hkernel
      _ = (-1 : ℝ) ^ k *
          (weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i)) := by ring
  have hscaled : Summable fun i => (-1 : ℝ) ^ k *
      (weight i * semilocalArchimedeanEvenJacobiKernel k (frequency i)) :=
    hsummable.mul_left _
  have hle := hscaled.le_tsum i₀ (fun i _ => (hterm i).le)
  rw [tsum_mul_left] at hle
  exact (hterm i₀).trans_le hle

/-- A finite integer packet on distinct primes has nonzero prime-log frequency unless it is the
zero packet. -/
theorem finitePrimeLogFrequency_ne_zero
    {n : ℕ} (p : Fin n → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (m : Fin n → ℤ) (hm : ∃ i, m i ≠ 0) :
    ∑ i, (m i : ℝ) * Real.log (p i) ≠ 0 := by
  intro hzero
  have hindex : Function.Injective
      (fun i : Fin n => (⟨p i, hprime i⟩ : Nat.Primes)) := by
    intro i j hij
    exact hp (congrArg Subtype.val hij)
  have hLI := GaloisForLFunctions.RHTower.primeLog_linearIndependent.comp
    (fun i : Fin n => (⟨p i, hprime i⟩ : Nat.Primes)) hindex
  have hall : ∀ i, m i = 0 := (Fintype.linearIndependent_iff.mp hLI) m (by
    simpa [zsmul_eq_mul] using hzero)
  obtain ⟨i, hi⟩ := hm
  exact hi (hall i)

/-- Finite Poisson packets over distinct prime-log frequencies already satisfy the full
all-even alternating sign law.  The infinite Poisson expansion is obtained by summable passage
from these packets. -/
theorem finitePrimePoissonPacket_evenJacobi_signed_pos
    {ι : Type*} {n k : ℕ}
    (p : Fin n → ℕ) (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (packet : ι → Fin n → ℤ) (s : Finset ι) (hs : s.Nonempty)
    (hpacket : ∀ j ∈ s, ∃ i, packet j i ≠ 0)
    (weight : ι → ℝ) (hweight : ∀ j ∈ s, 0 < weight j) :
    0 < (-1 : ℝ) ^ k * ∑ j ∈ s, weight j *
      semilocalArchimedeanEvenJacobiKernel k
        (∑ i, (packet j i : ℝ) * Real.log (p i)) := by
  exact semilocalArchimedeanEvenJacobiKernel_weightedPacket_signed_pos s hs weight
    (fun j ↦ ∑ i, (packet j i : ℝ) * Real.log (p i)) hweight
    (fun j hj ↦ finitePrimeLogFrequency_ne_zero p hp hprime (packet j) (hpacket j hj))

/-! ## The convergent finite-prime Poisson assembly -/

/-- The Poisson radius attached to a finite prime. -/
def semilocalPrimePoissonRatio (p : ℕ) : ℝ :=
  (Real.sqrt p)⁻¹

theorem semilocalPrimePoissonRatio_pos {p : ℕ} (hp : p.Prime) :
    0 < semilocalPrimePoissonRatio p := by
  unfold semilocalPrimePoissonRatio
  exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hp.pos))

theorem semilocalPrimePoissonRatio_lt_one {p : ℕ} (hp : p.Prime) :
    semilocalPrimePoissonRatio p < 1 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hsqrt1 : 1 < Real.sqrt (p : ℝ) := by
    nlinarith [Real.sq_sqrt hp0.le, Real.sqrt_nonneg (p : ℝ),
      (show (1 : ℝ) < p by exact_mod_cast hp.one_lt)]
  exact inv_lt_one_of_one_lt₀ hsqrt1

/-- The bilateral geometric weight is summable. -/
theorem summable_int_pow_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun m : ℤ => r ^ m.natAbs := by
  rw [summable_int_iff_summable_nat_and_neg_add_zero]
  have hgeom : Summable fun n : ℕ => r ^ n :=
    summable_geometric_of_lt_one hr0 hr1
  constructor
  · simpa using hgeom
  · apply (hgeom.mul_left r).congr
    intro n
    rw [Int.natAbs_neg]
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
    rw [Int.natAbs_natCast, pow_succ, mul_comm]

/-- Product Poisson coefficient of an integer packet on a finite prime family. -/
def semilocalFinitePrimePoissonWeight {n : ℕ}
    (p : Fin n → ℕ) (m : Fin n → ℤ) : ℝ :=
  ∏ i, semilocalPrimePoissonRatio (p i) ^ (m i).natAbs

theorem semilocalFinitePrimePoissonWeight_pos
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime)
    (m : Fin n → ℤ) :
    0 < semilocalFinitePrimePoissonWeight p m := by
  unfold semilocalFinitePrimePoissonWeight
  exact Finset.prod_pos fun i _ =>
    pow_pos (semilocalPrimePoissonRatio_pos (hprime i)) _

/-- A finite product of bilateral Poisson coefficients is summable over its integer lattice. -/
theorem summable_semilocalFinitePrimePoissonWeight
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    Summable fun m : Fin n → ℤ => semilocalFinitePrimePoissonWeight p m := by
  induction n with
  | zero =>
      apply summable_of_hasFiniteSupport
      refine (Set.finite_singleton (0 : Fin 0 → ℤ)).subset ?_
      intro m _hm
      simp only [Set.mem_singleton_iff]
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
        Fin.consEquiv fun _ => ℤ
      refine e.summable_iff.mp ?_
      have hhead : Summable fun z : ℤ =>
          semilocalPrimePoissonRatio (p 0) ^ z.natAbs :=
        summable_int_pow_natAbs
          (semilocalPrimePoissonRatio_pos (hprime 0)).le
          (semilocalPrimePoissonRatio_lt_one (hprime 0))
      have htail : Summable fun m : Fin n → ℤ =>
          semilocalFinitePrimePoissonWeight (fun i => p i.succ) m :=
        ih (fun i => p i.succ) (fun i => hprime i.succ)
      have hprod : Summable fun x : ℤ × (Fin n → ℤ) =>
          semilocalPrimePoissonRatio (p 0) ^ x.1.natAbs *
            semilocalFinitePrimePoissonWeight (fun i => p i.succ) x.2 :=
        hhead.mul_of_nonneg htail
          (fun z => pow_nonneg
            (semilocalPrimePoissonRatio_pos (hprime 0)).le _)
          (fun m => (semilocalFinitePrimePoissonWeight_pos
            (fun i => p i.succ) (fun i => hprime i.succ) m).le)
      simpa [e, semilocalFinitePrimePoissonWeight, Function.comp_def,
        Fin.prod_univ_succ] using hprod

/-- Prime-log frequency of an integer packet. -/
def semilocalFinitePrimeLogFrequency {n : ℕ}
    (p : Fin n → ℕ) (m : Fin n → ℤ) : ℝ :=
  ∑ i, (m i : ℝ) * Real.log (p i)

/-- Nonzero integer packets on a nonempty finite prime family. -/
abbrev SemilocalNonzeroPrimePacket (n : ℕ) :=
  {m : Fin (n + 1) → ℤ // m ≠ 0}

/-- A canonical nonzero packet, used only to witness that the nonzero packet lattice is nonempty. -/
def semilocalUnitPrimePacket (n : ℕ) : SemilocalNonzeroPrimePacket n :=
  ⟨fun i => if i = 0 then 1 else 0, by
    intro hzero
    have h := congrFun hzero (0 : Fin (n + 1))
    simp at h⟩

instance semilocalNonzeroPrimePacket_nonempty (n : ℕ) :
    Nonempty (SemilocalNonzeroPrimePacket n) :=
  ⟨semilocalUnitPrimePacket n⟩

theorem semilocalNonzeroPrimeLogFrequency_ne_zero
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (m : SemilocalNonzeroPrimePacket n) :
    semilocalFinitePrimeLogFrequency p m.1 ≠ 0 := by
  apply finitePrimeLogFrequency_ne_zero p hp hprime m.1
  by_contra hall
  push Not at hall
  apply m.2
  funext i
  exact hall i

theorem summable_semilocalNonzeroPrimePoissonWeight
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    Summable fun m : SemilocalNonzeroPrimePacket n =>
      semilocalFinitePrimePoissonWeight p m.1 := by
  simpa only [SemilocalNonzeroPrimePacket] using
    (summable_semilocalFinitePrimePoissonWeight p hprime).subtype
      (fun m => m ≠ 0)

theorem semilocalArchimedeanCharacteristic_le_one (t : ℝ) :
    semilocalArchimedeanCharacteristic t ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_cosh t) (by norm_num)

/-- The absolute all-even kernel is bounded by its degree normalization. -/
theorem abs_semilocalArchimedeanEvenJacobiKernel_le (k : ℕ) (t : ℝ) :
    |semilocalArchimedeanEvenJacobiKernel k t| ≤
      semilocalArchimedeanJacobiNormalization (2 * k) := by
  have hnorm := semilocalArchimedeanJacobiNormalization_pos (2 * k)
  have hchar := semilocalArchimedeanCharacteristic_pos t
  have htanh : |Real.tanh t| ≤ 1 := (Real.abs_tanh_lt_one t).le
  rw [semilocalArchimedeanEvenJacobiKernel]
  calc
    |(-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k) *
        semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k)| =
        semilocalArchimedeanJacobiNormalization (2 * k) *
          semilocalArchimedeanCharacteristic t * |Real.tanh t| ^ (2 * k) := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos hnorm, abs_of_pos hchar]
    _ ≤ semilocalArchimedeanJacobiNormalization (2 * k) * 1 * 1 := by
      gcongr
      · exact semilocalArchimedeanCharacteristic_le_one t
      · exact pow_le_one₀ (abs_nonneg _) htanh
    _ = semilocalArchimedeanJacobiNormalization (2 * k) := by ring

/-- Absolute convergence of the finite-prime all-even Poisson numerator. -/
theorem summable_semilocalFinitePrimeEvenJacobiTerm
    {n k : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    Summable fun m : SemilocalNonzeroPrimePacket n =>
      semilocalFinitePrimePoissonWeight p m.1 *
        semilocalArchimedeanEvenJacobiKernel k
          (semilocalFinitePrimeLogFrequency p m.1) := by
  have hweight := summable_semilocalNonzeroPrimePoissonWeight p hprime
  have hmajor := hweight.mul_left
    (semilocalArchimedeanJacobiNormalization (2 * k))
  refine hmajor.of_norm_bounded ?_
  intro m
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (semilocalFinitePrimePoissonWeight_pos p hprime m.1)]
  calc
    semilocalFinitePrimePoissonWeight p m.1 *
        |semilocalArchimedeanEvenJacobiKernel k
          (semilocalFinitePrimeLogFrequency p m.1)| ≤
      semilocalFinitePrimePoissonWeight p m.1 *
        semilocalArchimedeanJacobiNormalization (2 * k) :=
      mul_le_mul_of_nonneg_left
        (abs_semilocalArchimedeanEvenJacobiKernel_le k _)
        (semilocalFinitePrimePoissonWeight_pos p hprime m.1).le
    _ = semilocalArchimedeanJacobiNormalization (2 * k) *
        semilocalFinitePrimePoissonWeight p m.1 := by ring

/-- The unnormalized nonzero-frequency all-even Jacobi residue. -/
def semilocalFinitePrimeEvenJacobiNumerator
    {n : ℕ} (k : ℕ) (p : Fin (n + 1) → ℕ) : ℝ :=
  ∑' m : SemilocalNonzeroPrimePacket n,
    semilocalFinitePrimePoissonWeight p m.1 *
      semilocalArchimedeanEvenJacobiKernel k
        (semilocalFinitePrimeLogFrequency p m.1)

/-- Every nonempty finite set of distinct primes has the strict all-even alternating residue sign. -/
theorem semilocalFinitePrimeEvenJacobiNumerator_signed_pos
    {n k : ℕ}
    (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < (-1 : ℝ) ^ k * semilocalFinitePrimeEvenJacobiNumerator k p := by
  exact semilocalArchimedeanEvenJacobiKernel_weightedSeries_signed_pos
    (fun m : SemilocalNonzeroPrimePacket n =>
      semilocalFinitePrimePoissonWeight p m.1)
    (fun m : SemilocalNonzeroPrimePacket n =>
      semilocalFinitePrimeLogFrequency p m.1)
    (fun m => semilocalFinitePrimePoissonWeight_pos p hprime m.1)
    (fun m => semilocalNonzeroPrimeLogFrequency_ne_zero p hp hprime m)
    (summable_semilocalFinitePrimeEvenJacobiTerm p hprime)

/-- The Poisson-series normalizing mass.  The common local prefactor
`prod_p (1-r_p^2)^{-1}` cancels from normalized moments and is therefore omitted. -/
def semilocalFinitePrimePoissonMass
    {n : ℕ} (p : Fin (n + 1) → ℕ) : ℝ :=
  ∑' m : Fin (n + 1) → ℤ,
    semilocalFinitePrimePoissonWeight p m *
      semilocalArchimedeanCharacteristic
        (semilocalFinitePrimeLogFrequency p m)

theorem summable_semilocalFinitePrimePoissonMassTerm
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    Summable fun m : Fin (n + 1) → ℤ =>
      semilocalFinitePrimePoissonWeight p m *
        semilocalArchimedeanCharacteristic
          (semilocalFinitePrimeLogFrequency p m) := by
  have hweight := summable_semilocalFinitePrimePoissonWeight p hprime
  refine hweight.of_norm_bounded ?_
  intro m
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (semilocalFinitePrimePoissonWeight_pos p hprime m),
    abs_of_pos (semilocalArchimedeanCharacteristic_pos _)]
  simpa using mul_le_mul_of_nonneg_left
    (semilocalArchimedeanCharacteristic_le_one
      (semilocalFinitePrimeLogFrequency p m))
    (semilocalFinitePrimePoissonWeight_pos p hprime m).le

theorem semilocalFinitePrimePoissonMass_pos
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < semilocalFinitePrimePoissonMass p := by
  let z : Fin (n + 1) → ℤ := 0
  have hterm (m : Fin (n + 1) → ℤ) :
      0 < semilocalFinitePrimePoissonWeight p m *
        semilocalArchimedeanCharacteristic
          (semilocalFinitePrimeLogFrequency p m) :=
    mul_pos (semilocalFinitePrimePoissonWeight_pos p hprime m)
      (semilocalArchimedeanCharacteristic_pos _)
  have hsum := summable_semilocalFinitePrimePoissonMassTerm p hprime
  exact (hterm z).trans_le (by
    simpa only [semilocalFinitePrimePoissonMass] using
      hsum.le_tsum z (fun m _ => (hterm m).le))

/-- The normalized finite-prime even Jacobi moment. -/
def semilocalFinitePrimeEvenJacobiMoment
    {n : ℕ} (k : ℕ) (p : Fin (n + 1) → ℕ) : ℝ :=
  semilocalFinitePrimeEvenJacobiNumerator k p /
    semilocalFinitePrimePoissonMass p

/-- **Normalized all-even semilocal Jacobi tower.**  Every nonempty finite family of distinct
primes gives a nonzero ground-state component in every even archimedean mode, including degree
zero, with sign `(-1)^k`. -/
theorem semilocalFinitePrimeEvenJacobiMoment_signed_pos
    {n k : ℕ}
    (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < (-1 : ℝ) ^ k * semilocalFinitePrimeEvenJacobiMoment k p := by
  rw [semilocalFinitePrimeEvenJacobiMoment]
  rw [← mul_div_assoc]
  exact div_pos (semilocalFinitePrimeEvenJacobiNumerator_signed_pos p hp hprime)
    (semilocalFinitePrimePoissonMass_pos p hprime)

/-- Ground-state row of the number-operator naturality defect. -/
def semilocalFinitePrimeGradingGroundDefect
    {n : ℕ} (k : ℕ) (p : Fin (n + 1) → ℕ) : ℝ :=
  -((2 * k : ℕ) : ℝ) * semilocalFinitePrimeEvenJacobiMoment k p

/-- The grading naturality defect has the opposite rigid sign. -/
theorem semilocalFinitePrimeGradingGroundDefect_signed_pos
    {n k : ℕ} (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < (-1 : ℝ) ^ (k + 1) * semilocalFinitePrimeGradingGroundDefect k p := by
  have hmom := semilocalFinitePrimeEvenJacobiMoment_signed_pos (k := k) p hp hprime
  rw [semilocalFinitePrimeGradingGroundDefect, pow_succ]
  calc
    (-1 : ℝ) ^ k * -1 *
        (-((2 * k : ℕ) : ℝ) * semilocalFinitePrimeEvenJacobiMoment k p) =
      ((2 * k : ℕ) : ℝ) *
        ((-1 : ℝ) ^ k * semilocalFinitePrimeEvenJacobiMoment k p) := by ring
    _ > 0 := mul_pos (by positivity) hmom

/-- Ground-state row of the formal prolate naturality defect.  The common differential term has
cancelled, leaving `lambda^2` times the grading defect. -/
def semilocalFinitePrimeProlateGroundDefect
    {n : ℕ} (lambda : ℝ) (k : ℕ) (p : Fin (n + 1) → ℕ) : ℝ :=
  lambda ^ 2 * semilocalFinitePrimeGradingGroundDefect k p

/-- Every positive prolate parameter preserves the strict alternating defect sign. -/
theorem semilocalFinitePrimeProlateGroundDefect_signed_pos
    {n k : ℕ} {lambda : ℝ} (hlambda : 0 < lambda) (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < (-1 : ℝ) ^ (k + 1) *
      semilocalFinitePrimeProlateGroundDefect lambda k p := by
  have hgrading :=
    semilocalFinitePrimeGradingGroundDefect_signed_pos hk p hp hprime
  rw [semilocalFinitePrimeProlateGroundDefect]
  calc
    (-1 : ℝ) ^ (k + 1) *
        (lambda ^ 2 * semilocalFinitePrimeGradingGroundDefect k p) =
      lambda ^ 2 *
        ((-1 : ℝ) ^ (k + 1) * semilocalFinitePrimeGradingGroundDefect k p) := by ring
    _ > 0 := mul_pos (sq_pos_of_pos hlambda) hgrading

end RHTower
