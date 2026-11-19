import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.PrimeSquareTowerPolarShell
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.ZMod.Basic

/-!
# Prime-power rigidity of polar energy two

For a factorization AC=bᵈ, the endpoint congruence reduces to A²=1
modulo b²−1. In a prime-power base b=pᵉ, the order of p modulo
p²ᵉ−1 forces the exponent of |A| to be a multiple of e. In every
other base a single prime factor supplies a non-site endpoint pair
in degree φ(b²−1).
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower

def modulus (b : Base) := b.val^2-1

private theorem wrap (p e : ℕ) (hp : 0<p) : (p : ZMod (p^e-1))^e=1 := by
  let M := p^e-1
  have h : p^e=M+1 := by dsimp [M]; have := pow_pos hp e; omega
  change (p : ZMod M)^e=1
  calc
    _ = ((p^e:ℕ):ZMod M) := (Nat.cast_pow ..).symm
    _ = ((M+1:ℕ):ZMod M) := congrArg (fun v : ℕ => (v : ZMod M)) h
    _ = 1 := by simp

/-- Exact period of p in the residue ring modulo pᵉ−1, including e=1. -/
theorem power_congruence_iff (p e k : ℕ) (hp : 1<p) (he : 0<e) :
    (p : ZMod (p^e-1))^k=1 ↔ e∣k := by
  let M := p^e-1
  let q : ZMod M := p
  have cycle : q^e=1 := wrap p e (by omega)
  constructor
  · intro h
    have reduced : q^k=q^(k%e) := by
      calc
        _ = q^(k%e+e*(k/e)) := congrArg (fun j : ℕ => q^j) (Nat.mod_add_div k e).symm
        _ = _ := by rw [pow_add,pow_mul,cycle,one_pow,mul_one]
    by_contra hn
    have nonzero : k%e≠0 := fun z => hn (Nat.dvd_of_mod_eq_zero z)
    have lower : 1<p^(k%e) := one_lt_pow₀ hp nonzero
    have upper : p^(k%e)<p^e := Nat.pow_lt_pow_right hp (Nat.mod_lt k he)
    have hz : ((p^(k%e)-1:ℕ):ZMod M)=0 := by
      rw [Nat.cast_sub lower.le,Nat.cast_pow,Nat.cast_one]
      exact sub_eq_zero.mpr (reduced.symm.trans h)
    have bound := Nat.le_of_dvd (by omega : 0<p^(k%e)-1) ((ZMod.natCast_eq_zero_iff _ M).mp hz)
    dsimp only [M] at bound
    omega
  · rintro ⟨u,rfl⟩
    change q^(e*u)=1
    rw [pow_mul,cycle,one_pow]

/-- On the unit hyperbola the linear endpoint congruence is precisely
a square-root-of-one condition on the first factor. -/
theorem congruence_iff_square (b : Base) (d : ℕ) (a c : ℤ) (h : a*c=(b.val:ℤ)^d) :
    (∃ k : ℤ, c=a*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*k) ↔ (a : ZMod (modulus b))^2=1 := by
  let S := ZMod (modulus b)
  let A : S := a
  let C : S := c
  let B : S := b.val
  have bpos : 0<b.val := lt_of_lt_of_le (by decide : 0<2) b.property
  have base_sq : B^2=1 := wrap b.val 2 bpos
  have bd : (B^d)^2=1 := by rw [pow_right_comm,base_sq,one_pow]
  have ac : A*C=B^d := by
    change (a : ZMod (modulus b))*(c : ZMod (modulus b))=(b.val : ZMod (modulus b))^d
    calc
      _ = ((a*c:ℤ) : ZMod (modulus b)) := (Int.cast_mul a c).symm
      _ = (((b.val:ℤ)^d:ℤ) : ZMod (modulus b)) := congrArg (fun v : ℤ => (v : ZMod (modulus b))) h
      _ = _ := by rw [Int.cast_pow,Int.cast_natCast]
  have hm : ((modulus b:ℕ):ℤ)=(b.val:ℤ)^2-1 := by
    simp only [modulus,Nat.cast_sub (pow_pos bpos 2),Nat.cast_pow,Nat.cast_one]
  have linear : (∃ k : ℤ, c=a*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*k) ↔ C=A*B^d := by
    have eq : C=A*B^d ↔ ((modulus b:ℕ):ℤ) ∣ a*(b.val:ℤ)^d-c := by
      simpa only [C,A,B,Int.cast_mul,Int.cast_pow,Int.cast_natCast] using
        ZMod.intCast_eq_intCast_iff_dvd_sub c (a*(b.val:ℤ)^d) (modulus b)
    rw [eq,hm]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k,by rw [hk]; ring⟩
    · rintro ⟨k,hk⟩
      exact ⟨k,by linear_combination -hk⟩
  rw [linear]
  change C=A*B^d ↔ A^2=1
  constructor
  · intro eq
    have hprod : A^2*B^d=B^d := calc
      A^2*B^d=A*(A*B^d) := by ring
      _=A*C := by rw [←eq]
      _=B^d := ac
    calc
      A^2 = (A^2*B^d)*B^d := by rw [mul_assoc,←sq,bd,mul_one]
      _ = 1 := by rw [hprod,←sq,bd]
  · intro hs
    calc
      C = A^2*C := by rw [hs,one_mul]
      _ = A*(A*C) := by ring
      _ = A*B^d := by rw [ac]

private theorem primePower_pair (b : Base) {p e : ℕ} (hp : p.Prime) (he : 0<e)
    (hb : p^e=b.val) (d : ℕ) (a c : ℤ) (ac : a*c=(b.val:ℤ)^d)
    (hs : (a : ZMod (modulus b))^2=1) : ∃ l : Label d, (a,c)=sitePair b.val l := by
  have prod : a*c=(p:ℤ)^(e*d) := by rw [pow_mul,←Nat.cast_pow,hb]; exact ac
  obtain ⟨⟨s,i⟩,hi⟩ := prime_factor_pair ⟨p,hp⟩ (e*d) a c prod
  have ai : a=signed s ((p:ℤ)^i.val) := congrArg Prod.fst hi
  have primeSq : (p : ZMod (modulus b))^(i.val*2)=1 := by
    rw [ai] at hs
    cases s <;> simpa [signed,pow_mul] using hs
  have hm : modulus b=p^(e*2)-1 := by rw [modulus,←hb,pow_mul]
  rw [hm] at primeSq
  have dv := (power_congruence_iff p (e*2) (i.val*2) hp.one_lt (by omega)).mp primeSq
  obtain ⟨v,hv⟩ := (Nat.mul_dvd_mul_iff_right (by decide : 0<2)).mp dv
  have hindex : e*v≤e*d := by rw [←hv]; exact Nat.le_of_lt_succ i.isLt
  let l : Label d := (s,⟨v,Nat.lt_succ_of_le (Nat.le_of_mul_le_mul_left hindex he)⟩)
  have first : a=(sitePair b.val l).1 := by
    change a=signed s ((b.val:ℤ)^v)
    rw [ai,hv,pow_mul,←Nat.cast_pow,hb]
  have nz : a≠0 := by
    intro z
    rw [z,zero_mul] at ac
    have bn : (b.val:ℤ)≠0 := by exact_mod_cast (show b.val≠0 by have := b.property; omega)
    exact pow_ne_zero _ bn ac.symm
  refine ⟨l,Prod.ext first (mul_left_cancel₀ nz ?_)⟩
  calc
    a*c=(b.val:ℤ)^d := ac
    _=a*(sitePair b.val l).2 := by rw [first,site_product]

private theorem attainable_positive (b : Base) {d : ℕ} (hd : 0<d) (a c : ℤ)
    (hc : ∃ k : ℤ, c=a*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*k) :
    ∃ x : Coeff (d+1), forward b.val x=a ∧ backward b.val x=c := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  exact (attainable_pair b.val n a c).mpr hc

/-- A base with at least two distinct prime factors admits an explicit degree in
which the polar unit shell has an endpoint pair outside the signed sites. -/
theorem nonprime_power_witness (b : Base) (hn : ¬IsPrimePow b.val) :
    let d := (modulus b).totient
    ∃ x : Coeff (d+1), polar b x=2 ∧ ∀ l : Label d,
      (forward b.val x,backward b.val x)≠sitePair b.val l := by
  intro d
  let p := b.val.minFac
  have hb := b.property
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have divides : p∣b.val := Nat.minFac_dvd _
  obtain ⟨w,hw⟩ := divides
  have bs : 1<b.val^2 := one_lt_pow₀ (by omega) (by decide)
  have hd : 0<d := Nat.totient_pos.mpr (by dsimp [modulus]; omega)
  have coprime : p.Coprime (modulus b) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro bad
    have h := Nat.dvd_sub ((Nat.minFac_dvd b.val).trans (dvd_pow_self b.val (by decide : 2≠0))) bad
    exact hp.not_dvd_one (by simpa only [modulus,show b.val^2-(b.val^2-1)=1 by omega] using h)
  have cycle : (p : ZMod (modulus b))^d=1 := by
    simpa only [Nat.cast_pow,Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (p^d) 1 (modulus b)).mpr (Nat.ModEq.pow_totient coprime)
  have ac : (p:ℤ)^d*(w:ℤ)^d=(b.val:ℤ)^d := by rw [←mul_pow,hw,Nat.cast_mul]
  have residue : (((p:ℤ)^d:ℤ) : ZMod (modulus b))^2=1 := by
    rw [Int.cast_pow,Int.cast_natCast,cycle,one_pow]
  obtain ⟨x,f,g⟩ := attainable_positive b hd _ _ ((congruence_iff_square b d _ _ ac).mpr residue)
  refine ⟨x,(unit_iff b x).mpr (by rw [f,g]; exact ac),?_⟩
  intro l eq
  have ah := congrArg (fun v : ℤ × ℤ => v.1.natAbs) eq
  change (forward b.val x).natAbs=(sitePair b.val l).1.natAbs at ah
  rw [f,first_abs b] at ah
  have powers : p^d=b.val^l.2.val := by simpa [Int.natAbs_pow] using ah
  have pos : 1<p^d := one_lt_pow₀ hp.one_lt hd.ne'
  have index : l.2.val≠0 := by intro z; rw [z,pow_zero] at powers; omega
  apply hn ((isPrimePow_pow_iff index).mp ?_)
  rw [←powers]
  exact hp.isPrimePow.pow hd.ne'

/-- Signed sites exhaust the measured polar unit shell at every length
exactly when the base is a prime power. -/
theorem all_units_are_sites_iff (b : Base) :
    (∀ d (x : Coeff (d+1)), polar b x=2 → ∃! l : Label d,
      (forward b.val x,backward b.val x)=sitePair b.val l) ↔ IsPrimePow b.val := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨x,hx,missing⟩ := nonprime_power_witness b hn
    obtain ⟨l,hl,_⟩ := h _ x hx
    exact missing l hl
  · rintro h d x hx
    obtain ⟨p,e,hp,he,hb⟩ := (isPrimePow_nat_iff _).mp h
    have ac := (unit_iff b x).mp hx
    have square := (congruence_iff_square b d _ _ ac).mp (endpoint_congruence b.val d x)
    obtain ⟨l,h⟩ := primePower_pair b hp he hb d _ _ ac square
    exact ⟨l,h,fun l' h' => label_injective b d (h'.symm.trans h)⟩

/-- Checking only degree φ(b²−1) decides whether signed sites exhaust
the measured unit shell simultaneously at every tower length. -/
theorem totient_degree_detects_all (b : Base) :
    (∀ x : Coeff ((modulus b).totient+1), polar b x=2 → ∃ l : Label (modulus b).totient,
      (forward b.val x,backward b.val x)=sitePair b.val l) ↔ IsPrimePow b.val := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨x,hx,missing⟩ := nonprime_power_witness b hn
    obtain ⟨l,hl⟩ := h x hx
    exact missing l hl
  · intro hb x hx
    exact ((all_units_are_sites_iff b).mpr hb _ x hx).exists

/-- Each signed site on a prime-power tower of n+2 sites labels a full
copy of ℤⁿ inside the integral polar unit shell. -/
noncomputable def primePowerUnitEquiv (b : Base) (hb : IsPrimePow b.val) (n : ℕ) :
    {x : Coeff (n+2) // polar b x=2} ≃ Label (n+1) × Coeff n := by
  let f (l : Label (n+1)) : Admissible b.val (n+1) ((b.val:ℤ)^(n+1)) :=
    ⟨sitePair b.val l,site_product _ _,by
      rw [←atom_readings b.val l]
      exact endpoint_congruence b.val _ (atom l)⟩
  have onto : Function.Surjective f := by
    intro u
    obtain ⟨p,e,hp,he,hpow⟩ := (isPrimePow_nat_iff _).mp hb
    have sq := (congruence_iff_square b _ _ _ u.property.1).mp u.property.2
    obtain ⟨l,hl⟩ := primePower_pair b hp he hpow _ _ _ u.property.1 sq
    exact ⟨l,Subtype.ext hl.symm⟩
  let labels := Equiv.ofBijective f ⟨fun _ _ h => label_injective b _ (congrArg Subtype.val h),onto⟩
  exact ((Equiv.subtypeEquivRight (fun x => unit_iff b x)).trans
    (levelEquiv b n ((b.val:ℤ)^(n+1)))).trans (labels.symm.prodCongr (Equiv.refl _))

#print axioms power_congruence_iff
#print axioms congruence_iff_square
#print axioms nonprime_power_witness
#print axioms all_units_are_sites_iff
#print axioms totient_degree_detects_all
#print axioms primePowerUnitEquiv
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower
