import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.SquareTowerPolarForm
import Mathlib.Data.Nat.Prime.Basic

/-!
# Signed unit sites on a prime square tower

At polar energy two the integral endpoint readings multiply to pᵈ.
Their absolute values are complementary powers of p and their signs
agree. Each factorization is realized by exactly one signed site. The
unrestricted directions in the coefficients are precisely the fibers of
the two endpoint readings.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower

def primeBase (p : Nat.Primes) : Base := ⟨p.val,p.property.two_le⟩

abbrev Label (d : ℕ) := Bool × Fin (d+1)

def signed (negate : Bool) (a : ℤ) := if negate then -a else a

def atom {d : ℕ} (l : Label d) : Coeff (d+1) := Pi.single l.2 (signed l.1 1)

def sitePair (b : ℤ) {d : ℕ} (l : Label d) : ℤ × ℤ :=
  (signed l.1 (b^l.2.val),signed l.1 (b^l.2.rev.val))

theorem atom_readings (b : ℤ) {d : ℕ} (l : Label d) :
    (forward b (atom l),backward b (atom l))=sitePair b l := by
  obtain ⟨s,i⟩ := l
  cases s <;> simp [forward,backward,atom,sitePair,signed,Pi.single_apply,ite_mul]

theorem site_product (b : ℤ) {d : ℕ} (l : Label d) :
    (sitePair b l).1*(sitePair b l).2=b^d := by
  obtain ⟨s,i⟩ := l
  have product : b^i.val*b^i.rev.val=b^d := by rw [←pow_add,complementary_exponents]
  cases s
  · exact product
  · change (-b^i.val)*(-b^i.rev.val)=b^d
    rwa [neg_mul_neg]

theorem first_abs (b : Base) {d : ℕ} (l : Label d) :
    (sitePair b.val l).1.natAbs=b.val^l.2.val := by
  obtain ⟨s,i⟩ := l
  cases s <;> simp [sitePair,signed,Int.natAbs_pow]

theorem label_injective (b : Base) (d : ℕ) : Function.Injective (sitePair b.val (d:=d)) := by
  rintro ⟨s,i⟩ ⟨t,j⟩ h
  have absEq := congrArg (fun u : ℤ × ℤ => u.1.natAbs) h
  change (sitePair b.val (s,i)).1.natAbs=(sitePair b.val (t,j)).1.natAbs at absEq
  rw [first_abs b,first_abs b] at absEq
  have ij : i=j := Fin.ext (Nat.pow_right_injective b.property absEq)
  subst j
  have fst := congrArg Prod.fst h
  have pos : 0<(b.val:ℤ)^i.val := pow_pos (by exact_mod_cast (show 0<b.val by have h := b.property; omega)) _
  cases s <;> cases t <;> try rfl
  all_goals
    exfalso
    simp [sitePair,signed] at fst
    omega

/-- Integral factorizations of a prime power are the signed pairs of
complementary powers of that prime. -/
theorem prime_factor_pair (p : Nat.Primes) (d : ℕ) (a c : ℤ) (h : a*c=(p.val:ℤ)^d) :
    ∃ l : Label d, (a,c)=sitePair p.val l := by
  have absEq : a.natAbs*c.natAbs=p.val^d := by
    simpa [Int.natAbs_mul,Int.natAbs_pow] using congrArg Int.natAbs h
  obtain ⟨j,hj,ha⟩ := (Nat.dvd_prime_pow p.property).mp (show a.natAbs∣p.val^d from ⟨_,absEq.symm⟩)
  let i : Fin (d+1) := ⟨j,by omega⟩
  have nz : a≠0 := by
    intro e
    rw [e,zero_mul] at h
    exact (pow_ne_zero d (by exact_mod_cast p.property.ne_zero : (p.val:ℤ)≠0)) h.symm
  have complete (l : Label d) (e : a=(sitePair p.val l).1) : (a,c)=sitePair p.val l := by
    apply Prod.ext e
    apply mul_left_cancel₀ nz
    calc
      a*c=(p.val:ℤ)^d := h
      _=a*(sitePair p.val l).2 := by rw [e,site_product]
  rcases Int.natAbs_eq_iff.mp ha with plus|minus
  · exact ⟨(false,i),complete _ (by simpa [sitePair,signed,i] using plus)⟩
  · exact ⟨(true,i),complete _ (by simpa [sitePair,signed,i] using minus)⟩

/-- At polar energy two a unique signed site has exactly the two measured
endpoint values, for integer sections of arbitrary sign. -/
theorem unit_iff_unique_site (p : Nat.Primes) {d : ℕ} (x : Coeff (d+1)) :
    polar (primeBase p) x=2 ↔ ∃! l : Label d, (forward p.val x,backward p.val x)=sitePair p.val l := by
  rw [unit_iff]
  constructor
  · intro h
    obtain ⟨l,e⟩ := prime_factor_pair p d _ _ h
    exact ⟨l,e,fun y hy => label_injective (primeBase p) d (hy.symm.trans e)⟩
  · rintro ⟨l,h,_⟩
    exact (congrArg (fun u : ℤ × ℤ => u.1*u.2) h).trans (site_product p.val l)

/-- The apparent congruence condition on factor pairs at the prime-tower
unit level discards none of the complementary signed prime powers. -/
def admissibleSites (p : Nat.Primes) (d : ℕ) : Label d ≃ Admissible p.val d ((p.val:ℤ)^d) := by
  let f (l : Label d) : Admissible p.val d ((p.val:ℤ)^d) := ⟨sitePair p.val l,site_product _ _,by
    rw [←atom_readings p.val l]
    exact endpoint_congruence p.val d (atom l)⟩
  apply Equiv.ofBijective f
  constructor
  · exact fun _ _ h => label_injective (primeBase p) d (congrArg Subtype.val h)
  · intro u
    obtain ⟨l,h⟩ := prime_factor_pair p d u.val.1 u.val.2 u.property.1
    exact ⟨l,Subtype.ext h.symm⟩

/-- On n+2 prime-square sites the entire signed polar unit shell is a
disjoint union of 2(n+2) copies of the rank-n integer lattice. -/
def unitEquiv (p : Nat.Primes) (n : ℕ) :
    {x : Coeff (n+2) // polar (primeBase p) x=2} ≃ Label (n+1) × Coeff n :=
  ((Equiv.subtypeEquivRight (fun x => unit_iff (primeBase p) x)).trans
    (levelEquiv (primeBase p) n ((p.val:ℤ)^(n+1)))).trans
      ((admissibleSites p (n+1)).symm.prodCongr (Equiv.refl _))

/-- With at least three sites a fixed energy shell already has infinitely
many integer sections, despite its finite set of signed endpoint classes. -/
theorem infinite_polar_units (p : Nat.Primes) (n : ℕ) :
    Infinite {x : Coeff (n+3) // polar (primeBase p) x=2} := by
  let e := unitEquiv p (n+1)
  apply Infinite.of_injective (fun k : ℤ => e.symm ((false,0),fun _ => k))
  intro k l h
  have eq := congrArg e h
  simp only [e.apply_symm_apply] at eq
  exact congrArg (fun y : Label (n+2) × Coeff (n+1) => y.2 0) eq

#print axioms unit_iff_unique_site
#print axioms admissibleSites
#print axioms unitEquiv
#print axioms infinite_polar_units
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower
