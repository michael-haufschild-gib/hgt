import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Factorization.Basic

/-!
# `N`-th roots of pointed multiplicative maps

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 4.6 (`t46n`).

Let `R` be an integral domain with quotient field `K`, let `N ≥ 1` be an integer such that every
element of `R` is an `N`-th power and such that `μ_N (R) = μ_N (K)`, and let

`P : R → 𝔬`

be a multiplicative map with `P 1 = 1` and `P 0 = 0` — that is, a `MonoidWithZeroHom`.

* Part 1 (`deningerPointedMulRoot_exists_iff`, `deningerPointedMulRoot_unique`): a multiplicative
  `Q` with `Q ^ N = P` exists if and only if `P` is trivial on the `N`-th roots of unity of `R`,
  and `Q` is then unique.
* Part 2 (`deningerPointedMulRoot_exists_iff_card_dvd`): for `R = K` an algebraically closed field
  and finite kernel `P⁻¹(1)`, such a `Q` exists exactly when `#μ_N (K)` divides `#P⁻¹(1)`.

The source phrases part 2 in terms of `N'`, the prime-to-`char K` part of `N`.  That the two
formulations agree is the content of `deningerCard_rootsOfUnity_charZero` and
`deningerCard_rootsOfUnity_charP`, which evaluate `#μ_N (K)` as `N` in characteristic zero and as
`ordCompl[p] N` in characteristic `p`.

Everything here is unconditional: no `sorry`, no added axioms.
-/

namespace RHTower

/-! ## Part 1: existence and uniqueness of the `N`-th root -/

/-- Two elements of a domain with equal nonzero `N`-th powers differ by an `N`-th root of unity
*inside the domain*, provided every `N`-th root of unity of the fraction field already lies in the
domain.  This is Deninger's hypothesis `μ_N (R) = μ_N (K)` in the form in which it is used. -/
theorem deningerRootOfUnityFactor
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {N : ℕ}
    (hμ : ∀ z : K, z ^ N = 1 → ∃ r : R, algebraMap R K r = z)
    {s s' : R} (hs : s ≠ 0) (h : s' ^ N = s ^ N) :
    ∃ ζ : R, ζ ^ N = 1 ∧ s' = ζ * s := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have ha : algebraMap R K s ≠ 0 := fun hc => hs (hinj (by simpa using hc))
  set z : K := algebraMap R K s' / algebraMap R K s with hz
  have hzN : z ^ N = 1 := by
    rw [hz, div_pow, ← map_pow, ← map_pow, h]
    exact div_self (by rw [map_pow]; exact pow_ne_zero _ ha)
  obtain ⟨ζ, hζ⟩ := hμ z hzN
  refine ⟨ζ, ?_, ?_⟩
  · apply hinj
    rw [map_pow, hζ, hzN, map_one]
  · apply hinj
    rw [map_mul, hζ, hz, div_mul_cancel₀ _ ha]

/-- **Deninger, Lemma 4.6(1), necessity.**  A pointed multiplicative map admitting an `N`-th root
in the same class is trivial on the `N`-th roots of unity. -/
theorem deningerPointedMulRoot_eq_one_of_exists
    {R O : Type*} [CommMonoidWithZero R] [CommMonoidWithZero O] {N : ℕ}
    (P : R →*₀ O) (Q : R →*₀ O) (hQ : ∀ r, Q r ^ N = P r)
    (ζ : R) (hζ : ζ ^ N = 1) : P ζ = 1 := by
  rw [← hQ ζ, ← map_pow, hζ, map_one]

/-- **Deninger, Lemma 4.6(1), uniqueness.**  If every element of `R` is an `N`-th power, a pointed
multiplicative `N`-th root of `P` is unique. -/
theorem deningerPointedMulRoot_unique
    {R O : Type*} [CommMonoidWithZero R] [CommMonoidWithZero O] {N : ℕ}
    (hpow : ∀ r : R, ∃ s : R, s ^ N = r)
    (P Q Q' : R →*₀ O) (hQ : ∀ r, Q r ^ N = P r) (hQ' : ∀ r, Q' r ^ N = P r) :
    Q = Q' := by
  ext r
  obtain ⟨s, hs⟩ := hpow r
  rw [← hs, map_pow, map_pow, hQ, hQ']

/-- **Deninger, Lemma 4.6(1), existence.** -/
theorem deningerPointedMulRoot_exists
    {R K O : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommMonoidWithZero O] {N : ℕ} (hN : N ≠ 0)
    (hpow : ∀ r : R, ∃ s : R, s ^ N = r)
    (hμ : ∀ z : K, z ^ N = 1 → ∃ r : R, algebraMap R K r = z)
    (P : R →*₀ O) (hP : ∀ ζ : R, ζ ^ N = 1 → P ζ = 1) :
    ∃ Q : R →*₀ O, ∀ r, Q r ^ N = P r := by
  classical
  choose root hroot using hpow
  have key : ∀ (r s : R), s ^ N = r → P s = P (root r) := by
    intro r s hsr
    have hrr : root r ^ N = r := hroot r
    by_cases hr : r = 0
    · have hs0 : s = 0 := by
        have : s ^ N = 0 := by rw [hsr, hr]
        exact pow_eq_zero_iff hN |>.mp this
      have hz0 : root r = 0 := by
        have : root r ^ N = 0 := by rw [hrr, hr]
        exact pow_eq_zero_iff hN |>.mp this
      rw [hs0, hz0]
    · have hne : root r ≠ 0 := by
        intro hc
        exact hr (by rw [← hrr, hc, zero_pow hN])
      obtain ⟨ζ, hζ1, hζ2⟩ :=
        deningerRootOfUnityFactor (K := K) hμ hne (by rw [hsr, hrr])
      rw [hζ2, map_mul, hP ζ hζ1, one_mul]
  refine ⟨{ toFun := fun r => P (root r)
            map_zero' := ?_
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · rw [← key 0 0 (zero_pow hN), map_zero]
  · rw [← key 1 1 (one_pow N), map_one]
  · intro a b
    rw [← key (a * b) (root a * root b) (by rw [mul_pow, hroot, hroot]), map_mul]
  · intro r
    show P (root r) ^ N = P r
    rw [← map_pow, hroot]

/-- **Deninger, Lemma 4.6(1).**  A pointed multiplicative map on a domain in which every element is
an `N`-th power and whose `N`-th roots of unity are those of its fraction field admits a pointed
multiplicative `N`-th root exactly when it is trivial on the `N`-th roots of unity. -/
theorem deningerPointedMulRoot_exists_iff
    {R K O : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommMonoidWithZero O] {N : ℕ} (hN : N ≠ 0)
    (hpow : ∀ r : R, ∃ s : R, s ^ N = r)
    (hμ : ∀ z : K, z ^ N = 1 → ∃ r : R, algebraMap R K r = z)
    (P : R →*₀ O) :
    (∃ Q : R →*₀ O, ∀ r, Q r ^ N = P r) ↔ ∀ ζ : R, ζ ^ N = 1 → P ζ = 1 := by
  refine ⟨fun ⟨Q, hQ⟩ => deningerPointedMulRoot_eq_one_of_exists P Q hQ, fun hP =>
    deningerPointedMulRoot_exists (K := K) hN hpow hμ P hP⟩

/-! ## Part 2: the criterion `N' ∣ #P⁻¹(1)` over an algebraically closed field -/

/-- The kernel `P⁻¹(1)` of a pointed multiplicative map, as a subgroup of the unit group. -/
def deningerPointedMulKernel {K O : Type*} [Field K] [CommMonoidWithZero O] (P : K →*₀ O) :
    Subgroup Kˣ :=
  MonoidHom.ker (Units.map (P : K →* O))

theorem deningerPointedMulKernel_mem_iff {K O : Type*} [Field K] [CommMonoidWithZero O]
    (P : K →*₀ O) (u : Kˣ) : u ∈ deningerPointedMulKernel P ↔ P (u : K) = 1 := by
  simp [deningerPointedMulKernel, MonoidHom.mem_ker, Units.ext_iff]

/-- Triviality of `P` on the `N`-th roots of unity is exactly the containment `μ_N ⊆ P⁻¹(1)`. -/
theorem deningerPointedMul_rootsOfUnity_le_kernel_iff {K O : Type*} [Field K]
    [CommMonoidWithZero O] {N : ℕ} (hN : N ≠ 0) (P : K →*₀ O) :
    rootsOfUnity N K ≤ deningerPointedMulKernel P ↔ ∀ ζ : K, ζ ^ N = 1 → P ζ = 1 := by
  constructor
  · intro h ζ hζ
    have hζ0 : ζ ≠ 0 := by
      intro hc
      rw [hc, zero_pow hN] at hζ
      exact zero_ne_one hζ
    have hu : (Units.mk0 ζ hζ0) ∈ rootsOfUnity N K := by
      rw [mem_rootsOfUnity]
      ext
      simpa using hζ
    exact (deningerPointedMulKernel_mem_iff P _).mp (h hu)
  · intro h u hu
    rw [mem_rootsOfUnity] at hu
    rw [deningerPointedMulKernel_mem_iff]
    exact h _ (by simpa using congrArg (Units.val) hu)

/-- A finite subgroup of the unit group of a field is the full group of roots of unity of its own
order. -/
theorem deningerFiniteSubgroupUnits_eq_rootsOfUnity {K : Type*} [Field K] (H : Subgroup Kˣ)
    [Finite H] : H = rootsOfUnity (Nat.card H) K := by
  haveI : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro u hu
    rw [mem_rootsOfUnity]
    have h1 : (⟨u, hu⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    have h2 : ((⟨u, hu⟩ : H) : Kˣ) ^ Nat.card H = 1 := by
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    exact h2
  · exact card_rootsOfUnity _ _

theorem deningerRootsOfUnity_le_of_dvd {K : Type*} [Field K] {d m : ℕ} (h : d ∣ m) :
    rootsOfUnity d K ≤ rootsOfUnity m K := by
  intro u hu
  rw [mem_rootsOfUnity] at hu ⊢
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, hu, one_pow]

/-- **Deninger, Lemma 4.6(2).**  Over an algebraically closed field with finite `P⁻¹(1)`, a pointed
multiplicative `N`-th root of `P` exists exactly when the order of `μ_N (K)` divides the order of
`P⁻¹(1)`. -/
theorem deningerPointedMulRoot_exists_iff_card_dvd
    {K O : Type*} [Field K] [IsAlgClosed K] [CommMonoidWithZero O] {N : ℕ} (hN : N ≠ 0)
    (P : K →*₀ O) [Finite (deningerPointedMulKernel P)] :
    (∃ Q : K →*₀ O, ∀ r, Q r ^ N = P r) ↔
      Nat.card (rootsOfUnity N K) ∣ Nat.card (deningerPointedMulKernel P) := by
  haveI : NeZero N := ⟨hN⟩
  have hpow : ∀ r : K, ∃ s : K, s ^ N = r := fun r =>
    IsAlgClosed.exists_pow_nat_eq r (Nat.pos_of_ne_zero hN)
  have hμ : ∀ z : K, z ^ N = 1 → ∃ r : K, algebraMap K K r = z := fun z _ => ⟨z, by simp⟩
  rw [deningerPointedMulRoot_exists_iff (K := K) hN hpow hμ P,
    ← deningerPointedMul_rootsOfUnity_le_kernel_iff hN P]
  constructor
  · exact fun h => Subgroup.card_dvd_of_le h
  · intro h
    have h1 : rootsOfUnity N K = rootsOfUnity (Nat.card (rootsOfUnity N K)) K :=
      deningerFiniteSubgroupUnits_eq_rootsOfUnity _
    have h2 : deningerPointedMulKernel P
        = rootsOfUnity (Nat.card (deningerPointedMulKernel P)) K :=
      deningerFiniteSubgroupUnits_eq_rootsOfUnity _
    rw [h1, h2]
    exact deningerRootsOfUnity_le_of_dvd h

/-! ## The order of `μ_N (K)`: Deninger's `N'` -/

/-- Over a separably closed field the group of `m`-th roots of unity has exactly `m` elements as
soon as `m` is invertible in the field. -/
theorem deningerCard_rootsOfUnity_of_neZero_cast {K : Type*} [Field K] [IsSepClosed K] (m : ℕ)
    [NeZero (m : K)] : Nat.card (rootsOfUnity m K) = m := by
  haveI : NeZero m := NeZero.of_neZero_natCast (R := K)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := K) (n := m)
  exact hζ.card_rootsOfUnity

/-- **Deninger's `N'` in characteristic zero:** `#μ_N (K) = N`. -/
theorem deningerCard_rootsOfUnity_charZero {K : Type*} [Field K] [IsSepClosed K] [CharZero K]
    {N : ℕ} (hN : N ≠ 0) : Nat.card (rootsOfUnity N K) = N := by
  haveI : NeZero (N : K) := ⟨Nat.cast_ne_zero.mpr hN⟩
  exact deningerCard_rootsOfUnity_of_neZero_cast N

/-- In characteristic `p` a `p`-power root of unity is trivial. -/
theorem deningerPowCharPow_eq_one {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {y : K} {a : ℕ} (h : y ^ p ^ a = 1) : y = 1 := by
  induction a with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    have hfr : (y ^ p ^ n) ^ p = (1 : K) ^ p := by
      rw [one_pow, ← pow_mul, ← pow_succ]
      exact h
    exact frobenius_inj K p hfr

/-- **Deninger's `N'` in characteristic `p`:** only the prime-to-`p` part of `N` survives, i.e.
`#μ_N (K) = ordCompl[p] N`. -/
theorem deningerCard_rootsOfUnity_charP {K : Type*} [Field K] [IsSepClosed K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {N : ℕ} (hN : N ≠ 0) :
    Nat.card (rootsOfUnity N K) = ordCompl[p] N := by
  have hp : p.Prime := Fact.out
  have hnd : ¬ p ∣ ordCompl[p] N := Nat.not_dvd_ordCompl hp hN
  haveI : NeZero ((ordCompl[p] N : ℕ) : K) := by
    refine ⟨fun hc => hnd ?_⟩
    exact (CharP.cast_eq_zero_iff K p _).mp hc
  have hsplit : ordProj[p] N * ordCompl[p] N = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have heq : rootsOfUnity N K = rootsOfUnity (ordCompl[p] N) K := by
    apply le_antisymm
    · intro u hu
      rw [mem_rootsOfUnity] at hu ⊢
      have h1 : ((u : Kˣ) : K) ^ N = 1 := by simpa using congrArg (Units.val) hu
      have h2 : (((u : Kˣ) : K) ^ ordCompl[p] N) ^ p ^ (N.factorization p) = 1 := by
        rw [← pow_mul, mul_comm, hsplit]
        exact h1
      have h3 : ((u : Kˣ) : K) ^ ordCompl[p] N = 1 := deningerPowCharPow_eq_one h2
      ext
      simpa using h3
    · exact deningerRootsOfUnity_le_of_dvd (Nat.ordCompl_dvd N p)
  rw [heq]
  exact deningerCard_rootsOfUnity_of_neZero_cast _

end RHTower
