import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FractionalDiscrepancyAtThePrimeMidpoint
import GaloisForLFunctions.Core
import Mathlib.NumberTheory.Bertrand

/-!
# Two prime lists in a single fractional observation

The half-order integral divided by π is a signed sum of prime logarithms.
It determines both prime lists uniquely. Integer cross-products give a
finite separation bound even if the reading is perturbed. Bertrand's
theorem supplies a nonzero reading in every positive-index window.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def primeWindow (a b : ℕ) : Finset Nat.Primes := (Ioc a b).subtype Nat.Prime

def signedPrimeLog (L U : Finset Nat.Primes) : ℝ :=
  (∑ p ∈ L, Real.log (p:ℕ))-(∑ p ∈ U, Real.log (p:ℕ))

private def listVector (L : Finset Nat.Primes) : Nat.Primes →₀ ℤ :=
  ∑ p ∈ L, Finsupp.single p 1

private theorem listVector_apply (L : Finset Nat.Primes) (p : Nat.Primes) :
    listVector L p=if p ∈ L then 1 else 0 := by
  classical
  simp [listVector,Finsupp.finset_sum_apply,Finsupp.single_apply]

private theorem listVector_log (L U : Finset Nat.Primes) :
    Finsupp.linearCombination ℤ (fun p : Nat.Primes => Real.log (p:ℕ)) (listVector L-listVector U)=
      signedPrimeLog L U := by
  simp only [listVector,signedPrimeLog,map_sub,map_sum,Finsupp.linearCombination_single,one_smul]

/-- Each prime occurs in at most one list in a signed observation. Its
integer coefficient therefore determines both membership decisions. -/
theorem signed_prime_lists_identifiable {L U L' U' : Finset Nat.Primes}
    (hd : Disjoint L U) (hd' : Disjoint L' U') :
    signedPrimeLog L U=signedPrimeLog L' U' ↔ L=L' ∧ U=U' := by
  constructor
  · intro h
    rw [←listVector_log,←listVector_log] at h
    have he := (linearIndependent_iff_injective_finsuppLinearCombination.mp
      GaloisForLFunctions.logPrime_linearIndependent_int) h
    have signs {S T : Finset Nat.Primes} (hst : Disjoint S T) (p : Nat.Primes) :
        (p ∈ S ↔ (listVector S-listVector T) p=1) ∧ (p ∈ T ↔ (listVector S-listVector T) p= -1) := by
      simp only [Finsupp.sub_apply,listVector_apply]
      by_cases hs : p ∈ S
      · simp [hs,Finset.disjoint_left.mp hst hs]
      · by_cases ht : p ∈ T <;> simp [hs,ht]
    exact ⟨Finset.ext fun p => by rw [(signs hd p).1,he,←(signs hd' p).1],
      Finset.ext fun p => by rw [(signs hd p).2,he,←(signs hd' p).2]⟩
  · rintro ⟨rfl,rfl⟩
    rfl

private theorem windows_disjoint (n : ℕ) : Disjoint (primeWindow (2*n) (3*n)) (primeWindow (3*n) (4*n)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  exact ((mem_Ioc.mp (mem_subtype.mp hp)).2).not_gt (mem_Ioc.mp (mem_subtype.mp hp')).1

/-- This one scalar is the signed logarithmic price of the two prime sets. -/
def halfOrderMidpointRead (n : ℕ) :=
  (∫ t, midpointFractionalTest n (1/2) t * midpointFractionalField n (1/2) t)/Real.pi

theorem halfOrderMidpointRead_price (n : ℕ) : halfOrderMidpointRead n=primeMidpointPrice n := by
  rw [halfOrderMidpointRead,half_order_prime_midpoint,mul_div_cancel_left₀ _ Real.pi_pos.ne']

theorem halfOrderMidpointRead_eq (n : ℕ) : halfOrderMidpointRead n =
    signedPrimeLog (primeWindow (2*n) (3*n)) (primeWindow (3*n) (4*n)) := by
  rw [halfOrderMidpointRead_price]
  have h (a b : ℕ) := sum_subtype_eq_sum_filter (s := Ioc a b) (p := Nat.Prime)
    (fun k : ℕ => Real.log (k : ℝ))
  exact congrArg₂ (· - ·) (h (2*n) (3*n)).symm (h (3*n) (4*n)).symm

/-- Exact decoding of the two adjacent ordinary-prime intervals. -/
theorem fractional_read_recovers_prime_lists (n : ℕ) {L U : Finset Nat.Primes} (hd : Disjoint L U) :
    signedPrimeLog L U=halfOrderMidpointRead n ↔
      L=primeWindow (2*n) (3*n) ∧ U=primeWindow (3*n) (4*n) := by
  rw [halfOrderMidpointRead_eq,signed_prime_lists_identifiable hd (windows_disjoint n)]

/-- Equality of two raw prices determines both window lists separately. -/
theorem equal_prime_midpoints_iff_lists (n m : ℕ) :
    primeMidpointPrice n=primeMidpointPrice m ↔
      primeWindow (2*n) (3*n)=primeWindow (2*m) (3*m) ∧
      primeWindow (3*n) (4*n)=primeWindow (3*m) (4*m) := by
  rw [←halfOrderMidpointRead_price n,←halfOrderMidpointRead_price m,
    halfOrderMidpointRead_eq,halfOrderMidpointRead_eq]
  exact signed_prime_lists_identifiable (windows_disjoint n) (windows_disjoint m)

private theorem occupied_window {n : ℕ} (hn : 0 < n) :
    ∃ p : Nat.Primes, p ∈ primeWindow (2*n) (3*n) ∨ p ∈ primeWindow (3*n) (4*n) := by
  obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (2*n) (by omega)
  refine ⟨⟨p,hp⟩,?_⟩
  by_cases h : p ≤ 3*n
  · exact Or.inl (mem_subtype.mpr (mem_Ioc.mpr ⟨hl,h⟩))
  · exact Or.inr (mem_subtype.mpr (mem_Ioc.mpr ⟨lt_of_not_ge h,by change p ≤ 4*n; omega⟩))

/-- A positive window cannot cancel exactly. In addition, any two
non-overlapping octave windows have different signed readings. -/
theorem separated_half_order_readings {n m : ℕ} (hn : 0 < n) (hm : 2*n ≤ m) :
    halfOrderMidpointRead n ≠ 0 ∧ halfOrderMidpointRead n ≠ halfOrderMidpointRead m := by
  obtain ⟨p,hp⟩ := occupied_window hn
  constructor
  · intro hz
    have e : signedPrimeLog ∅ ∅=halfOrderMidpointRead n := by simp [signedPrimeLog,hz]
    obtain ⟨hL,hU⟩ := (fractional_read_recovers_prime_lists n (disjoint_empty_left ∅)).mp e
    rw [←hL,←hU] at hp
    simpa only [notMem_empty,or_self] using hp
  · intro he
    rw [halfOrderMidpointRead_eq n] at he
    obtain ⟨hL,hU⟩ := (fractional_read_recovers_prime_lists m (windows_disjoint n)).mp he
    rcases hp with hp | hp
    · have hpn := mem_Ioc.mp (mem_subtype.mp hp)
      rw [hL] at hp
      have hpm := mem_Ioc.mp (mem_subtype.mp hp)
      omega
    · have hpn := mem_Ioc.mp (mem_subtype.mp hp)
      rw [hU] at hp
      have hpm := mem_Ioc.mp (mem_subtype.mp hp)
      omega

/-- Product of a list of distinct primes. -/
def primeListProduct (L : Finset Nat.Primes) := ∏ p ∈ L, (p:ℕ)

private theorem product_pos (S : Finset Nat.Primes) : 0 < primeListProduct S :=
  Finset.prod_pos fun p _ => p.property.pos

private theorem product_log (S : Finset Nat.Primes) :
    Real.log (primeListProduct S)=∑ p ∈ S, Real.log (p:ℕ) := by
  rw [primeListProduct,Nat.cast_prod]
  exact Real.log_prod (fun p _ => (Nat.cast_pos.mpr p.property.pos).ne')

private theorem integer_log_gap {a b : ℕ} (ha : 0<a) (hb : 0<b) (hne : a≠b) :
    (1:ℝ)/(max a b:ℕ) ≤ |Real.log a-Real.log b| := by
  have one_side {u v : ℕ} (hu : 0<u) (huv : u<v) : 1/(v:ℝ) ≤ Real.log v-Real.log u := by
    have hv : 0<(v:ℝ) := Nat.cast_pos.mpr (hu.trans huv)
    have hu' : 0<(u:ℝ) := Nat.cast_pos.mpr hu
    have h := Real.log_le_sub_one_of_pos (div_pos hu' hv)
    rw [Real.log_div hu'.ne' hv.ne'] at h
    have hg : (u:ℝ)+1 ≤ v := by exact_mod_cast huv
    have hfrac : 1/(v:ℝ) ≤ 1-u/v := by
      rw [le_sub_iff_add_le,←add_div,div_le_one hv]
      linarith only [hg]
    linarith only [h,hfrac]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [max_eq_right h.le,abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (Nat.cast_pos.mpr ha) (Nat.cast_le.mpr h.le))),neg_sub]
    exact one_side ha h
  · rw [max_eq_left h.le,abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (Nat.cast_pos.mpr hb) (Nat.cast_le.mpr h.le)))]
    exact one_side hb h

/-- A reading closer than the reciprocal of the larger cross-product
already forces equality of both prime lists. The threshold is expressed
in the integer products of the two competing candidate pairs. -/
theorem prime_list_separation {L U L' U' : Finset Nat.Primes} (hd : Disjoint L U)
    (hd' : Disjoint L' U') (hne : ¬(L=L' ∧ U=U')) :
    (1:ℝ)/(max (primeListProduct L*primeListProduct U') (primeListProduct L'*primeListProduct U):ℕ) ≤
      |signedPrimeLog L U-signedPrimeLog L' U'| := by
  let A := primeListProduct L*primeListProduct U'
  let B := primeListProduct L'*primeListProduct U
  have hA : 0 < A := Nat.mul_pos (product_pos _) (product_pos _)
  have hB : 0 < B := Nat.mul_pos (product_pos _) (product_pos _)
  have cross (S T : Finset Nat.Primes) : Real.log ((primeListProduct S*primeListProduct T:ℕ):ℝ)=
      (∑ p ∈ S, Real.log (p:ℕ))+(∑ p ∈ T, Real.log (p:ℕ)) := by
    rw [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr (product_pos _).ne')
      (Nat.cast_ne_zero.mpr (product_pos _).ne'),product_log,product_log]
  have he : signedPrimeLog L U-signedPrimeLog L' U'=Real.log A-Real.log B := by
    unfold A B signedPrimeLog
    rw [cross,cross]
    ring
  have hn : A≠B := by
    intro h
    rw [h,sub_self,sub_eq_zero] at he
    exact hne ((signed_prime_lists_identifiable hd hd').mp he)
  rw [he]
  exact integer_log_gap hA hB hn

/-- A single progression gives length-L intervals with no prime crossed
by any of the first d dilations. -/
def primePlateauStride (d L : ℕ) := (d*(2+L)).factorial

def primePlateauStart (d L q : ℕ) := primePlateauStride d L*(q+1)+2

/-- A prime cannot occur at kM+r when M and r have a common divisor
strictly larger than one and kM is positive. -/
theorem prime_plateau_of_shared_divisors {d L M : ℕ} (hM : 0<M)
    (hcov : ∀ r, 1<r → r≤d*(2+L) → ∃ u, 1<u ∧ u∣r ∧ u∣M)
    {j k : ℕ} (hj : j ≤ L) (hk : 0 < k) (hd : k ≤ d) (p : Nat.Primes) :
    (p:ℕ) ≤ k*((M+2)+j) ↔ (p:ℕ) ≤ k*(M+2) := by
  have hkm := Nat.mul_pos hk hM
  rw [Nat.add_assoc,Nat.mul_add,Nat.mul_add k M 2]
  constructor
  · intro hp
    by_contra! h
    let r := (p:ℕ)-k*M
    have hr : k*M+r=(p:ℕ) := by dsimp only [r]; omega
    have hr₂ : 1 < r := by omega
    have hrp : r < (p:ℕ) := by omega
    have hcap : r ≤ d*(2+L) := by
      have hkj := Nat.mul_le_mul_left k (Nat.add_le_add_left hj 2)
      have hkd := Nat.mul_le_mul_right (2+L) hd
      omega
    obtain ⟨u,hu,hur,huM⟩ := hcov r hr₂ hcap
    have hsmall := (Nat.le_of_dvd (by omega) hur).trans_lt hrp
    have hdiv : u ∣ k*M := huM.trans (Nat.dvd_mul_left M k)
    have hpr := p.property.eq_one_or_self_of_dvd u (hr ▸ dvd_add hdiv hur)
    omega
  · exact fun h => h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k (by omega)) _)

theorem simultaneous_prime_plateau (d L q : ℕ) {j k : ℕ} (hj : j ≤ L)
    (hk : 0 < k) (hd : k ≤ d) (p : Nat.Primes) :
    (p:ℕ) ≤ k*(primePlateauStart d L q+j) ↔ (p:ℕ) ≤ k*primePlateauStart d L q := by
  apply prime_plateau_of_shared_divisors (d:=d) (L:=L)
    (Nat.mul_pos (Nat.factorial_pos _) (Nat.succ_pos q)) _ hj hk hd p
  intro r hr hcap
  exact ⟨r,hr,dvd_refl r,(Nat.dvd_factorial (by omega) hcap).trans (Nat.dvd_mul_right _ _)⟩

theorem halfOrderMidpointRead_eq_of_frozen_thresholds {n j : ℕ}
    (h : ∀ k, 0<k → k≤4 → ∀ p : Nat.Primes, (p:ℕ) ≤ k*(n+j) ↔ (p:ℕ) ≤ k*n) :
    halfOrderMidpointRead (n+j)=halfOrderMidpointRead n := by
  have same (a b : ℕ) (ha : 0 < a) (ha' : a ≤ 4) (hb : 0 < b) (hb' : b ≤ 4) :
      primeWindow (a*(n+j)) (b*(n+j))=primeWindow (a*n) (b*n) := by
    ext p
    have hp (u v : ℕ) : p ∈ primeWindow u v ↔ u < (p:ℕ) ∧ (p:ℕ) ≤ v :=
      mem_subtype.trans mem_Ioc
    simp only [hp,←Nat.not_le]
    exact and_congr (not_congr (h a ha ha' p)) (h b hb hb' p)
  simp only [halfOrderMidpointRead_eq,same 2 3 (by decide) (by decide) (by decide) (by decide),
    same 3 4 (by decide) (by decide) (by decide) (by decide)]

/-- At infinitely many equally spaced starts the half-order reading is
constant for L consecutive steps. Its signed prime lists are unchanged
at every intervening sample, and the common reading is nonzero. -/
theorem half_order_prime_plateau (L q : ℕ) :
    let n := primePlateauStart 4 L q
    halfOrderMidpointRead n ≠ 0 ∧ ∀ j ≤ L, halfOrderMidpointRead (n+j)=halfOrderMidpointRead n := by
  let n := primePlateauStart 4 L q
  have hn : 0 < n := by unfold n primePlateauStart; omega
  refine ⟨(separated_half_order_readings hn (m:=2*n) le_rfl).1,?_⟩
  intro j hj
  exact halfOrderMidpointRead_eq_of_frozen_thresholds
    (fun k hk hd p => simultaneous_prime_plateau 4 L q hj hk hd p)

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
