import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.RejectedHeat

/-!
# The exceptional physical clock times

A nonempty antipodal rejection is an odd half-turn on a rational label
ratio. The exceptional times form a countable dense set. Already the
single pair consisting of the prime two and the vacuum witnesses density.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary

open SampledClocks Set MeasureTheory

private theorem odd_phase (v : ℝ) :
    Circle.exp v = -1 ↔ ∃ j : ℤ, v = (2*(j:ℝ)+1)*Real.pi := by
  rw [← exp_pi,Circle.exp_eq_exp]
  exact exists_congr fun j => by ring_nf

theorem lost_winding (t : ℝ) (x : Word) : rejected t x ↔
    ∃ (k : ℕ) (j : ℤ), ((2:ℝ)^k*t)*(energy (x false)-energy (x true)) = (2*(j:ℝ)+1)*Real.pi := by
  rw [rejected_iff,misses_pi]
  apply exists_congr
  intro k
  change (Circle.exp (t*(energy (x false)-energy (x true))))^(2^k : ℕ) = -1 ↔ _
  rw [← Circle.exp_natCast_mul,odd_phase,Nat.cast_pow,mul_assoc]
  norm_num

private theorem powered_energy (a : ℕ+) (n : ℕ) : energy (a^n) = (n:ℝ)*energy a := by
  simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow]

private theorem gap_ne {a b : ℕ+} (h : a ≠ b) : energy a-energy b ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  apply h
  have hp := congrArg Real.exp he
  rw [energy,energy,Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at hp
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) hp)

def exceptional : Set ℝ := {t | ∃ x, rejected t x}

theorem exceptional_iff (t : ℝ) : t ∈ exceptional ↔
    ∃ (a b : ℕ+) (j : ℤ), a ≠ b ∧ t = (2*(j:ℝ)+1)*Real.pi/(energy a-energy b) := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨k,j,hj⟩ := (lost_winding t x).mp hx
    let n := 2^k
    have he : t*(energy ((x false)^n)-energy ((x true)^n)) = (2*(j:ℝ)+1)*Real.pi := by
      rw [powered_energy,powered_energy,← mul_sub]
      dsimp [n]
      push_cast
      exact (by linear_combination hj)
    have hab : (x false)^n ≠ (x true)^n := by
      intro h
      rw [h,sub_self,mul_zero] at he
      have hodd : (2*(j:ℝ)+1) ≠ 0 := by exact_mod_cast (show (2*j+1:ℤ) ≠ 0 by omega)
      exact (mul_ne_zero hodd Real.pi_ne_zero) he.symm
    exact ⟨_,_,j,hab,(eq_div_iff (gap_ne hab)).mpr he⟩
  · rintro ⟨a,b,j,hab,ht⟩
    let x (i : Bool) := cond i b a
    refine ⟨x,(lost_winding t x).mpr ⟨0,j,?_⟩⟩
    simpa only [pow_zero,one_mul,x,cond_false,cond_true] using (eq_div_iff (gap_ne hab)).mp ht

theorem exceptional_countable : exceptional.Countable := by
  let time (u : (ℕ+ × ℕ+) × ℤ) := (2*(u.2:ℝ)+1)*Real.pi/(energy u.1.1-energy u.1.2)
  apply (countable_range time).mono
  intro t ht
  obtain ⟨a,b,j,_,hj⟩ := (exceptional_iff t).mp ht
  exact ⟨((a,b),j),hj.symm⟩

def primeVacuum (b : Bool) : ℕ+ := cond b 1 2

theorem prime_vacuum_dense : Dense {t : ℝ | rejected t primeVacuum} := by
  rw [Metric.dense_iff]
  intro t ε hε
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (Real.pi/(ε*Real.log 2)) (by norm_num : (1:ℝ)<2)
  let A := (2:ℝ)^k*Real.log 2
  have hA : 0 < A := mul_pos (pow_pos (by norm_num) k) hd
  have hsmall : Real.pi < ε*A := ((div_lt_iff₀ (mul_pos hε hd)).mp hk).trans_eq (by dsimp [A]; ring)
  let j := ⌊t*A/(2*Real.pi)⌋
  let y := (2*(j:ℝ)+1)*Real.pi/A
  have hy : y*A = (2*(j:ℝ)+1)*Real.pi := div_mul_cancel₀ _ hA.ne'
  have hπ : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have lo : (j:ℝ)*(2*Real.pi) ≤ t*A := (le_div_iff₀ hπ).mp (Int.floor_le _)
  have hi : t*A < ((j:ℝ)+1)*(2*Real.pi) := (div_lt_iff₀ hπ).mp (Int.lt_floor_add_one _)
  have hb : |y-t| * A ≤ Real.pi := by
    calc
      _ = |y*A-t*A| := by rw [← sub_mul,abs_mul,abs_of_pos hA]
      _ ≤ Real.pi := by
        rw [hy]
        exact abs_le.mpr ⟨by linarith only [hi],by linarith only [lo]⟩
  refine ⟨y,?_,(lost_winding y _).mpr ⟨k,j,?_⟩⟩
  · change dist y t < ε
    rw [Real.dist_eq]
    by_contra! hn
    exact (not_le.mpr hsmall) ((mul_le_mul_of_nonneg_right hn hA.le).trans hb)
  · have he : energy (primeVacuum false)-energy (primeVacuum true) = Real.log 2 := by
      norm_num [primeVacuum,energy]
    rw [he]
    calc
      _ = y*A := by dsimp [A]; ring
      _ = _ := hy

theorem exceptional_dense : Dense exceptional :=
  Dense.mono (fun t (h : rejected t primeVacuum) => ⟨primeVacuum,h⟩) prime_vacuum_dense

theorem exceptional_null : volume exceptional = 0 := exceptional_countable.measure_zero volume

#print axioms exceptional_iff
#print axioms prime_vacuum_dense
#print axioms exceptional_countable
#print axioms exceptional_dense
#print axioms exceptional_null

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary
