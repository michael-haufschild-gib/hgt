import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum.Readout

/-! # Prime energies as the indecomposable observed levels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum

open Real MeasureTheory InverseSpectrum.ShellMixing

/-- A level is measured when its exponential is a positive atom. -/
def level (μ : Measure ℝ) (e : ℝ) := ∃ x : ℝ, 0 < μ.real {x} ∧ e = -log x

/-- A positive observed level which cannot be composed from two positive observed levels. -/
def elementary (μ : Measure ℝ) (e : ℝ) :=
  level μ e ∧ 0 < e ∧ ¬ ∃ a b : ℝ, level μ a ∧ level μ b ∧ 0 < a ∧ 0 < b ∧ a+b=e

private theorem node_energy (k : ℕ) : -log (occupationWeight k) = energy (number k) := by
  rw [occupationWeight_eq,log_inv,neg_neg]
  change _ = log ((k+1:ℕ):ℝ)
  rw [Nat.cast_add,Nat.cast_one]

theorem levels (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (e : ℝ) :
    level (measured t z) e ↔ ∃ n : ℕ+, e=energy n := by
  constructor
  · rintro ⟨x,h,rfl⟩
    obtain ⟨k,rfl⟩ := (measured_atoms t z x).mp h
    exact ⟨number k,node_energy k⟩
  · rintro ⟨n,rfl⟩
    obtain ⟨k,rfl⟩ := number_surjective n
    exact ⟨_,(measured_atoms t z _).mpr ⟨k,rfl⟩,(node_energy k).symm⟩

private theorem energy_pos (n : ℕ+) : 0 < energy n ↔ 1 < n.val := by
  change 0 < log (n.val:ℝ) ↔ _
  rw [log_pos_iff (Nat.cast_nonneg n.val)]
  exact_mod_cast (Iff.rfl : 1<n.val ↔ 1<n.val)

private theorem energy_injective : Function.Injective energy := by
  intro n m h
  have hn : (0 : ℝ) < n.val := Nat.cast_pos.mpr n.pos
  have hm : (0 : ℝ) < m.val := Nat.cast_pos.mpr m.pos
  have he := log_injOn_pos hn hm h
  exact PNat.coe_injective (Nat.cast_injective he)

private theorem indecomposable (n : ℕ+) :
    (1 < n.val ∧ ¬ ∃ a b : ℕ+, 1<a.val ∧ 1<b.val ∧ a*b=n) ↔ n.val.Prime := by
  constructor
  · rintro ⟨hn,ind⟩
    by_contra bad
    obtain ⟨a,⟨b,he⟩,ha,han⟩ := (Nat.not_prime_iff_exists_dvd_lt hn).mp bad
    have hb : 1 < b := by
      by_contra! low
      obtain eq|eq : b=0 ∨ b=1 := by omega
      · rw [eq,mul_zero] at he
        omega
      · rw [eq,mul_one] at he
        omega
    exact ind ⟨⟨a,by omega⟩,⟨b,by omega⟩,ha,hb,PNat.coe_injective he.symm⟩
  · intro hp
    refine ⟨hp.one_lt,?_⟩
    rintro ⟨a,b,ha,hb,prod⟩
    have dvd : a.val ∣ n.val := ⟨b.val,(congrArg PNat.val prod).symm⟩
    obtain eq|eq := hp.eq_one_or_self_of_dvd _ dvd
    · omega
    · have ae : a=n := PNat.coe_injective eq
      have be : b=1 := mul_left_cancel (show a*b=a*1 by rw [prod,ae,mul_one])
      rw [be] at hb
      exact (lt_irrefl 1 hb)

/-- The indecomposable positive measured levels are exactly the prime energies. -/
theorem elementary_levels (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (e : ℝ) :
    elementary (measured t z) e ↔ ∃ p : Nat.Primes, e=log (p.val:ℝ) := by
  constructor
  · rintro ⟨seen,pos,ind⟩
    obtain ⟨n,rfl⟩ := (levels t z e).mp seen
    have prime : n.val.Prime := (indecomposable n).mp ⟨(energy_pos n).mp pos,by
      rintro ⟨a,b,ha,hb,prod⟩
      exact ind ⟨energy a,energy b,(levels t z _).mpr ⟨a,rfl⟩,(levels t z _).mpr ⟨b,rfl⟩,
        (energy_pos a).mpr ha,(energy_pos b).mpr hb,(energy_mul a b).symm.trans (congrArg energy prod)⟩⟩
    exact ⟨⟨n.val,prime⟩,rfl⟩
  · rintro ⟨p,rfl⟩
    let n : ℕ+ := ⟨p.val,p.property.pos⟩
    change elementary (measured t z) (energy n)
    refine ⟨(levels t z _).mpr ⟨n,rfl⟩,(energy_pos n).mpr p.property.one_lt,?_⟩
    rintro ⟨x,y,hx,hy,px,py,sum⟩
    obtain ⟨a,rfl⟩ := (levels t z x).mp hx
    obtain ⟨b,rfl⟩ := (levels t z y).mp hy
    exact ((indecomposable n).mpr p.property).2
      ⟨a,b,(energy_pos a).mp px,(energy_pos b).mp py,energy_injective ((energy_mul a b).trans sum)⟩

#print axioms levels
#print axioms elementary_levels

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum
