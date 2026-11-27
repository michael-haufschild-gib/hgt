import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Integer

/-! # A single integer-temperature comparison for distinct elementary primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic

open Finset
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

def Coincides (a : I → ℕ+) (t : ℝ) := finiteGibbsPartition t (centered (labelEnergy a)) =
  finiteGibbsPartition (-t) (centered (labelEnergy a))

private theorem balance [Nonempty I] {a : I → ℕ+} {j : ℕ} (h : Coincides a j) (p : ℕ) :
    (2*j)*(labelProduct a).factorization p + Fintype.card I*(reverse a j).factorization p =
    (Fintype.card I*j)*(labelProduct a).factorization p + Fintype.card I*(direct a j).factorization p := by
  have val (x y s t : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
      (x^s*y^t).factorization p = s*x.factorization p+t*y.factorization p := by
    simp only [Nat.factorization_mul (pow_ne_zero _ hx) (pow_ne_zero _ hy),Finsupp.add_apply,
      Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
  have hr : 0<reverse a j := sum_pos (fun i _ => pow_pos (omitted_pos a i) j) univ_nonempty
  have hd : 0<direct a j := sum_pos (fun i _ => pow_pos (a i).pos j) univ_nonempty
  have eq := congrArg (fun x : ℕ => x.factorization p) ((trace_iff_integer a j).mp h)
  exact (val _ _ _ _ (product_pos a).ne' hr.ne').symm.trans (eq.trans (val _ _ _ _ (product_pos a).ne' hd.ne'))

/-- Coincidence at one integer order imposes simultaneous divisibility on all
prime valuations of the product of the labels. -/
theorem dimension_dvd [Nonempty I] {a : I → ℕ+} {j : ℕ} (h : Coincides a j) (p : ℕ) :
    Fintype.card I ∣ (2*j)*(labelProduct a).factorization p := by
  have eq := balance h p
  have hd : Fintype.card I ∣ (2*j)*(labelProduct a).factorization p +
      Fintype.card I*(reverse a j).factorization p := by
    refine ⟨j*(labelProduct a).factorization p + (direct a j).factorization p,?_⟩
    rw [eq]; ring
  exact (Nat.dvd_add_iff_left (Nat.dvd_mul_right _ _)).mpr hd

/-- A private prime factor singles out one nonzero complementary product modulo that prime. -/
private theorem reverse_unit {a : I → ℕ+} {p j : ℕ} (hp : p.Prime) (hj : 0<j)
    (x : I) (hx : p ∣ (a x : ℕ)) (privateFactor : ∀ y, y ≠ x → ¬p ∣ (a y : ℕ)) :
    ¬p ∣ reverse a j := by
  classical
  have exceptional : ¬p ∣ (omitted a x)^j := by
    intro hd
    obtain ⟨y,hy,div⟩ := hp.prime.exists_mem_finset_dvd (hp.dvd_of_dvd_pow hd : p ∣ omitted a x)
    exact privateFactor y (mem_erase.mp hy).1 div
  have others : p ∣ ∑ y ∈ univ.erase x, (omitted a y)^j := by
    apply dvd_sum
    intro y hy
    have mem : x ∈ univ.erase y := mem_erase.mpr ⟨(mem_erase.mp hy).1.symm, mem_univ _⟩
    exact dvd_pow (hx.trans (dvd_prod_of_mem (fun i => (a i : ℕ)) mem)) hj.ne'
  unfold reverse
  rw [← sum_erase_add _ _ (mem_univ x)]
  exact fun hd => exceptional ((Nat.dvd_add_iff_right others).mpr hd)

/-- A prime appearing in just one label rules out a coincident trace at every
positive integer order as soon as there are at least three states. -/
theorem exclusive_prime {a : I → ℕ+} {p j : ℕ} (hp : p.Prime) (hj : 0<j)
    (hn : 2<Fintype.card I) (x : I) (hx : p ∣ (a x : ℕ))
    (privateFactor : ∀ y, y ≠ x → ¬p ∣ (a y : ℕ)) : ¬Coincides a j := by
  classical
  letI : Nonempty I := ⟨x⟩
  intro eq
  have val := balance eq p
  have hpA : p ∣ labelProduct a := hx.trans (dvd_prod_of_mem (fun i => (a i : ℕ)) (mem_univ x))
  have hA := hp.factorization_pos_of_dvd (product_pos a).ne' hpA
  rw [Nat.factorization_eq_zero_of_not_dvd (reverse_unit hp hj x hx privateFactor),mul_zero,add_zero] at val
  have lt := Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hn hj) hA
  omega

/-- Every centered spectrum with at most two labels pairs at every real probe. -/
theorem small_packet (a : I → ℕ+) (size : Fintype.card I ≤ 2) (t : ℝ) : Coincides a t := by
  let E := labelEnergy a
  have cut : cutoff (Fintype.card I)=0 := by unfold cutoff; omega
  have tests : HeatTests (centered E) (cutoff (Fintype.card I)) := by
    intro r hr lo; rw [cut] at lo; omega
  have pair := (reflects_iff_centered_pair E).mp ((centered_heat_iff_reflects E).mp tests)
  have matchE := (pairs_iff_matches _ _).mp pair
  change finiteGibbsPartition t (centered E)=finiteGibbsPartition (-t) (centered E)
  rw [partition_negative]
  simpa only [zero_sub] using partition_congr matchE t

def elementary {S : Finset Nat.Primes} (p : S) : ℕ+ := ⟨p.val.val,p.val.property.pos⟩

/-- Every occupied prime label in the one-particle packet has its own prime factor. -/
theorem elementary_exclusive {S : Finset Nat.Primes} (x y : S) (hy : y≠x) :
    ¬x.val.val ∣ (elementary y : ℕ) := fun div => hy (Subtype.ext (Subtype.ext
      ((Nat.prime_dvd_prime_iff_eq x.val.property y.val.property).mp div).symm))

/-- At integer probes the complete exceptional set for a packet of distinct primes
consists of zero temperature order and packets of size at most two. -/
theorem prime_packet_iff (S : Finset Nat.Primes) (j : ℕ) :
    Coincides (elementary (S := S)) j ↔ j=0 ∨ S.card≤2 := by
  constructor
  · intro eq
    by_contra! fail
    obtain ⟨hj,hn⟩ := fail
    obtain ⟨p,hp⟩ := card_pos.mp (show 0<S.card by omega)
    let x : S := ⟨p,hp⟩
    exact exclusive_prime (a := elementary) p.property (Nat.pos_of_ne_zero hj)
      (by simpa only [Fintype.card_coe] using hn) x (dvd_refl _) (elementary_exclusive x) eq
  · rintro (rfl | small)
    · simp only [Coincides,Nat.cast_zero,neg_zero]
    · exact small_packet _ (by simpa only [Fintype.card_coe] using small) _

#print axioms dimension_dvd
#print axioms exclusive_prime
#print axioms prime_packet_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic
