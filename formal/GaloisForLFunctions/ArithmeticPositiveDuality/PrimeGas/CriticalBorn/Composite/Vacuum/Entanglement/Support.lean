import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Posterior
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement.Grams

/-! # The two occupied branches of the physical elementary split -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement

open Finset Real

def prepared (s : ℂ) (N : ℕ) (z : SplitParameter) := retained 1 s N (fun _ => z) 0

def output (s : ℂ) (N : ℕ) (z : SplitParameter) := splitIsometry z (prepared s N z)

private theorem prime_support {s : ℂ} {N : ℕ} {z : SplitParameter} {n : ℕ+}
    (hn : prepared s N z n≠0) : ∃ p : PrimeAt N, n=primeLabel p := by
  have nz : multiplicity 1 N n≠0 := by
    intro eq
    apply hn
    change (‖wave 1 s N‖:ℂ)⁻¹*wave 1 (s+shift (fun _ => z) 0) N n=0
    rw [wave_apply,eq,Nat.cast_zero,sqrt_zero,Complex.ofReal_zero,zero_mul,mul_zero]
  change (univ.filter fun q : Fin 1 → PrimeAt N => productLabel q=n).card≠0 at nz
  obtain ⟨q,hq⟩ := card_pos.mp (Nat.pos_of_ne_zero nz)
  exact ⟨q 0,by simpa [productLabel] using (mem_filter.mp hq).2.symm⟩

theorem prime_ne_unit {N : ℕ} (p : PrimeAt N) : primeLabel p≠1 :=
  fun e => (Nat.mem_primesBelow.mp p.property).2.ne_one (congrArg PNat.val e)

/-- Every nonzero coefficient of the full Hilbert-space output lies in the
vacuum row or the vacuum column, since its underlying product is prime. -/
theorem occupied (s : ℂ) (N : ℕ) (z : SplitParameter) (w : ℕ+ × ℕ+) (h : output s N z w≠0) :
    ∃ p : PrimeAt N, w=(1,primeLabel p) ∨ w=(primeLabel p,1) := by
  rcases w with ⟨a,b⟩
  have hn : prepared s N z (a*b)≠0 := by
    intro e
    apply h
    change channel z.val (a*b) a.val * prepared s N z (a*b)=0
    rw [e,mul_zero]
  obtain ⟨p,prod⟩ := prime_support hn
  have dvd : a.val∣p.val := ⟨b.val,(congrArg PNat.val prod).symm⟩
  obtain e|e := (Nat.mem_primesBelow.mp p.property).2.eq_one_or_self_of_dvd _ dvd
  · have ae : a=1 := PNat.coe_injective e
    subst a
    rw [one_mul] at prod
    exact ⟨p,Or.inl (congrArg (Prod.mk 1) prod)⟩
  · have ae : a=primeLabel p := PNat.coe_injective e
    have be : b=1 := mul_left_cancel (show a*b=a*1 by rw [prod,ae,mul_one])
    rw [ae,be]
    exact ⟨p,Or.inr rfl⟩

def basisLabel {N : ℕ} : Option (PrimeAt N) → ℕ+
  | none => 1
  | some p => primeLabel p

/-- Finite coefficient table containing the full support of the split. -/
def amplitudes (s : ℂ) (N : ℕ) (z : SplitParameter) (v : Option (PrimeAt N) × Option (PrimeAt N)) :=
  output s N z (basisLabel v.1,basisLabel v.2)

def vacuumRow (s : ℂ) (N : ℕ) (z : SplitParameter) (p : PrimeAt N) := output s N z (1,primeLabel p)

def vacuumColumn (s : ℂ) (N : ℕ) (z : SplitParameter) (p : PrimeAt N) := output s N z (primeLabel p,1)

theorem amplitudes_eq (s : ℂ) (N : ℕ) (z : SplitParameter) :
    amplitudes s N z=shared (vacuumRow s N z) (vacuumColumn s N z) := by
  funext v
  rcases v with ⟨i,j⟩
  cases i with
  | none =>
    cases j with
    | none =>
      change output s N z (1,1)=0
      by_contra h
      obtain ⟨p,e|e⟩ := occupied s N z _ h
      · exact prime_ne_unit p (congrArg Prod.snd e).symm
      · exact prime_ne_unit p (congrArg Prod.fst e).symm
    | some p => rfl
  | some p =>
    cases j with
    | none => rfl
    | some q =>
      change output s N z (primeLabel p,primeLabel q)=0
      by_contra h
      obtain ⟨r,e|e⟩ := occupied s N z _ h
      · exact prime_ne_unit p (congrArg Prod.fst e)
      · exact prime_ne_unit q (congrArg Prod.snd e)

#print axioms occupied
#print axioms amplitudes_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement
