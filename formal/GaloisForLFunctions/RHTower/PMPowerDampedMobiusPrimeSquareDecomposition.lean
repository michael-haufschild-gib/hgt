import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRoughInverse
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMean
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Cast

/-!
# Exact prime-square decomposition of the actual PM core

At reciprocal scale between `P²` and `2P²`, the rough inverse contains only
one, primes and semiprimes. Prime squares remain in the positive mass, whose
bound uses the full unordered-pair count including its diagonal.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace RHTower

private theorem pmq_rough_ge {P n : ℕ} (hn : 1 < n)
    (hr : ∀ p : ℕ,p.Prime → p ∣ n → P ≤ p) : P ≤ n := by
  exact (hr n.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)).trans
    (Nat.minFac_le (by omega))

private theorem pmq_rough_below_cube {P n : ℕ} (hn0 : n ≠ 0)
    (hr : ∀ p : ℕ,p.Prime → p ∣ n → P ≤ p) (hn : n < P^3) :
    n = 1 ∨ n.Prime ∨ ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ P ≤ p ∧ P ≤ q ∧ p ≤ q ∧ n = p*q := by
  by_cases hn1 : n = 1
  · exact Or.inl hn1
  by_cases hnp : n.Prime
  · exact Or.inr (Or.inl hnp)
  have hp := Nat.minFac_prime hn1
  have hPp := hr n.minFac hp (Nat.minFac_dvd n)
  obtain ⟨q,hq⟩ := Nat.minFac_dvd n
  have hqn : q ∣ n := ⟨n.minFac,by nlinarith [hq]⟩
  have hq1 : 1 < q := by
    by_contra hh
    have hh' : q = 0 ∨ q = 1 := by omega
    rcases hh' with rfl | rfl
    · simp at hq
      exact hn0 hq
    · simp only [mul_one] at hq
      exact hnp (hq.symm ▸ hp)
  have hqr : ∀ p : ℕ,p.Prime → p ∣ q → P ≤ p :=
    fun p hpp hpd => hr p hpp (hpd.trans hqn)
  have hPq := pmq_rough_ge hq1 hqr
  have hqp : q.Prime := by
    by_contra hqp
    obtain ⟨a,b,ha,hb,hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hqp
    have ha2 : 2 ≤ a := by
      by_contra hh
      have hh' : a = 0 ∨ a = 1 := by omega
      rcases hh' with ha0 | ha1
      · rw [ha0,zero_mul] at hab
        omega
      · rw [ha1,one_mul] at hab
        omega
    have hb2 : 2 ≤ b := by
      by_contra hh
      have hh' : b = 0 ∨ b = 1 := by omega
      rcases hh' with hb0 | hb1
      · rw [hb0,mul_zero] at hab
        omega
      · rw [hb1,mul_one] at hab
        omega
    have haq : a ∣ q := ⟨b,hab.symm⟩
    have hbq : b ∣ q := ⟨a,by nlinarith [hab]⟩
    have hPa := pmq_rough_ge (by omega : 1 < a)
      (fun p hpp hpd => hqr p hpp (hpd.trans haq))
    have hPb := pmq_rough_ge (by omega : 1 < b)
      (fun p hpp hpd => hqr p hpp (hpd.trans hbq))
    have hbad : P^3 ≤ n := by
      calc
        _ = P*(P*P) := by ring
        _ ≤ n.minFac*(a*b) := Nat.mul_le_mul hPp (Nat.mul_le_mul hPa hPb)
        _ = n := by rw [hab]; exact hq.symm
    omega
  exact Or.inr (Or.inr ⟨n.minFac,q,hp,hqp,hPp,hPq,
    Nat.minFac_le_of_dvd hqp.two_le hqn,hq⟩)

/-- Positive rough-composite mass. Below twice the prime-threshold square,
these are exactly the semiprimes, including prime squares. -/
def pmPrimeSquareRoughMass (ε : ℝ) (P : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter
    (fun n => n ≠ 1 ∧ ¬n.Prime ∧ ∀ p ∈ n.primeFactors,P ≤ p), (n : ℝ)^(-ε)

private theorem pmq_rough_indicator {P n : ℕ} (hP : 2 ≤ P) (hn : n ≠ 0) :
    CoprimeMobius.smoothAF (↑(mobiusFinitePrimeAperture (P-1)) : Set ℕ)ᶜ n =
      if ∀ p ∈ n.primeFactors,P ≤ p then 1 else 0 := by
  classical
  have hP1 : 1 ≤ P := by omega
  have hi : CoprimeMobius.IsSmooth
      (↑(mobiusFinitePrimeAperture (P-1)) : Set ℕ)ᶜ n ↔
      ∀ p ∈ n.primeFactors,P ≤ p := by
    simp only [CoprimeMobius.IsSmooth,hn,ne_eq,not_false_eq_true,true_and]
    apply forall_congr'
    intro p
    apply forall_congr'
    intro hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    simp only [Set.mem_compl_iff,Finset.mem_coe,mobiusFinitePrimeAperture,
      Finset.mem_filter,Finset.mem_range,Nat.sub_add_cancel hP1,hpp,and_true,not_lt]
  rw [CoprimeMobius.smoothAF_apply,hi]
  split_ifs <;> rfl

/-- The canonical core at prime-square scale has exactly one full-source,
one prime-convolution and one positive rough-composite contribution. -/
theorem pmFinitePrimePowerDampedFermiSource_prime_square_decomposition
    (ε : ℝ) {P : ℕ} (hP : 2 ≤ P) {X : ℝ}
    (hPX : (P : ℝ)^2 ≤ X) (hXP : X < 2*(P : ℝ)^2) :
    pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/X) =
      pmPowerDampedFermiSource ε (1/X)+
      (∑ q ∈ Finset.Icc 1 ⌊X⌋₊,
        if q.Prime ∧ P ≤ q then (((q : ℝ)^(-ε) : ℝ) : ℂ)*
          pmPowerDampedFermiSource ε ((q : ℝ)/X) else 0)+
      (pmPrimeSquareRoughMass ε P X : ℂ) := by
  classical
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hX4 : 4 ≤ X := by nlinarith
  have hX0 : 0 < X := by linarith
  have hS : ∀ p ∈ mobiusFinitePrimeAperture (P-1),p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  rw [pmFinitePrimePowerDampedFermiSource_rough_inverse hS ε (by positivity),one_div_one_div]
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) :
      (CoprimeMobius.smoothAF (↑(mobiusFinitePrimeAperture (P-1)) : Set ℕ)ᶜ n : ℂ)*
        (((n : ℝ)^(-ε) : ℝ) : ℂ)*pmPowerDampedFermiSource ε ((n : ℝ)*(1/X)) =
      (if n = 1 then pmPowerDampedFermiSource ε (1/X) else 0)+
      (if n.Prime ∧ P ≤ n then (((n : ℝ)^(-ε) : ℝ) : ℂ)*
        pmPowerDampedFermiSource ε ((n : ℝ)/X) else 0)+
      (if n ≠ 1 ∧ ¬n.Prime ∧ ∀ p ∈ n.primeFactors,P ≤ p then
        (((n : ℝ)^(-ε) : ℝ) : ℂ) else 0) := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (Finset.mem_Icc.mp hn).2
    rw [pmq_rough_indicator hP hn0]
    by_cases hnOne : n = 1
    · subst n
      simp [Nat.not_prime_one]
    by_cases hnPrime : n.Prime
    · have hp : (∀ p ∈ n.primeFactors,P ≤ p) ↔ P ≤ n := by
        rw [hnPrime.primeFactors]
        simp
      simp only [hp,hnOne,hnPrime,not_true_eq_false,
        true_and,false_and,and_false,if_false,zero_add,add_zero]
      by_cases hPn : P ≤ n <;> simp [hPn,div_eq_mul_inv]
    by_cases hr : ∀ p ∈ n.primeFactors,P ≤ p
    · have hrough : ∀ p : ℕ,p.Prime → p ∣ n → P ≤ p :=
        fun p hp hd => hr p (Nat.mem_primeFactors.mpr ⟨hp,hd,hn0⟩)
      have hnCube : n < P^3 := by
        have hc : (n : ℝ) < (P : ℝ)^3 := by
          have hh := mul_le_mul_of_nonneg_right hPr (sq_nonneg (P : ℝ))
          nlinarith
        exact_mod_cast hc
      rcases pmq_rough_below_cube hn0 hrough hnCube with hh | hh | ⟨p,q,hp,hq,hPp,hPq,_,heq⟩
      · exact False.elim (hnOne hh)
      · exact False.elim (hnPrime hh)
      have hPn : P^2 ≤ n := by
        rw [heq,pow_two]
        exact Nat.mul_le_mul hPp hPq
      have hPnR : (P : ℝ)^2 ≤ n := by exact_mod_cast hPn
      have hband : (n : ℝ)/X ∈ Ioc (1/2 : ℝ) 1 := by
        constructor
        · apply (lt_div_iff₀ hX0).mpr
          nlinarith
        · exact (div_le_one hX0).mpr hnX
      rw [if_pos hr,if_neg hnOne,if_neg (fun h => hnPrime h.1),
        if_pos ⟨hnOne,hnPrime,hr⟩]
      simp only [Int.cast_one,one_mul,zero_add]
      rw [show (n : ℝ)*(1/X) = (n : ℝ)/X by ring,
        pmPowerDampedFermiSource_first_band ε hband,mul_one]
    · rw [if_neg hr,if_neg hnOne,if_neg (fun h => hnPrime h.1),
        if_neg (fun h => hr h.2.2)]
      simp
  rw [Finset.sum_congr rfl hterm,Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 ⌊X⌋₊ := by
    exact Finset.mem_Icc.mpr ⟨le_rfl,Nat.le_floor (by norm_num only [Nat.cast_one]; linarith)⟩
  simp only [Finset.sum_ite_eq',hmem,if_true]
  congr 1
  simp only [pmPrimeSquareRoughMass,Finset.sum_filter,Complex.ofReal_sum,apply_ite,
    Complex.ofReal_zero]

/-- Square-inclusive semiprime mass is bounded by the unordered prime-pair
count, retaining its factor one half and diagonal contribution. -/
theorem pmPrimeSquareRoughMass_le_prime_pairs {ε : ℝ} (hε : 0 ≤ ε)
    {P : ℕ} (hP : 2 ≤ P) {X : ℝ}
    (hPX : (P : ℝ)^2 ≤ X) (hXP : X < 2*(P : ℝ)^2) :
    pmPrimeSquareRoughMass ε P X ≤
      ((((Finset.Icc P ⌊X/(P : ℝ)⌋₊).filter Nat.Prime).card : ℝ)^2+
        (((Finset.Icc P ⌊X/(P : ℝ)⌋₊).filter Nat.Prime).card : ℝ))/2*
        (P : ℝ)^(-2*ε) := by
  classical
  let M := (Finset.Icc 1 ⌊X⌋₊).filter
    (fun n => n ≠ 1 ∧ ¬n.Prime ∧ ∀ p ∈ n.primeFactors,P ≤ p)
  let B := (Finset.Icc P ⌊X/(P : ℝ)⌋₊).filter Nat.Prime
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hX0 : 0 < X := by nlinarith
  have hfact (n : ℕ) (hn : n ∈ M) :
      ∃ p ∈ B, ∃ q ∈ B, n = p*q ∧ P^2 ≤ n := by
    obtain ⟨hnI,hnOne,hnPrime,hr⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hnI).1; omega
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (Finset.mem_Icc.mp hnI).2
    have hrough : ∀ p : ℕ,p.Prime → p ∣ n → P ≤ p :=
      fun p hp hd => hr p (Nat.mem_primeFactors.mpr ⟨hp,hd,hn0⟩)
    have hnCube : n < P^3 := by
      have hc : (n : ℝ) < (P : ℝ)^3 := by
        have hh := mul_le_mul_of_nonneg_right hPr (sq_nonneg (P : ℝ))
        nlinarith
      exact_mod_cast hc
    rcases pmq_rough_below_cube hn0 hrough hnCube with hh | hh | ⟨p,q,hp,hq,hPp,hPq,_,heq⟩
    · exact False.elim (hnOne hh)
    · exact False.elim (hnPrime hh)
    have hprod : (n : ℝ) = (p : ℝ)*(q : ℝ) := by exact_mod_cast heq
    have hPpr : (P : ℝ) ≤ p := by exact_mod_cast hPp
    have hPqr : (P : ℝ) ≤ q := by exact_mod_cast hPq
    have hpX : (p : ℝ) ≤ X/(P : ℝ) := by
      apply (le_div_iff₀ hP0).mpr
      nlinarith
    have hqX : (q : ℝ) ≤ X/(P : ℝ) := by
      apply (le_div_iff₀ hP0).mpr
      nlinarith
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hPp,
      (Nat.le_floor_iff (by positivity)).mpr hpX⟩,hp⟩,
      q,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hPq,
      (Nat.le_floor_iff (by positivity)).mpr hqX⟩,hq⟩,heq,?_⟩
    rw [heq,pow_two]
    exact Nat.mul_le_mul hPp hPq
  have hsub : M ⊆ B.sym2.image Sym2.mul := by
    intro n hn
    obtain ⟨p,hp,q,hq,heq,_⟩ := hfact n hn
    exact Finset.mem_image.mpr ⟨Sym2.mk p q,Finset.mk_mem_sym2_iff.mpr ⟨hp,hq⟩,
      by simpa only [Sym2.mul_mk] using heq.symm⟩
  have hcard : M.card ≤ (B.card+1).choose 2 := by
    calc
      _ ≤ (B.sym2.image Sym2.mul).card := Finset.card_le_card hsub
      _ ≤ B.sym2.card := Finset.card_image_le
      _ = _ := Finset.card_sym2 B
  have hweight (n : ℕ) (hn : n ∈ M) : (n : ℝ)^(-ε) ≤ (P : ℝ)^(-2*ε) := by
    obtain ⟨_,_,_,_,_,hPn⟩ := hfact n hn
    have hPnR : (P : ℝ)^2 ≤ n := by exact_mod_cast hPn
    have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (P : ℝ)^2)
      hPnR (by linarith : -ε ≤ 0)
    have hp : ((P : ℝ)^2)^(-ε) = (P : ℝ)^(-2*ε) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hP0.le]
      congr 1
      norm_num
    exact hh.trans_eq hp
  have hsum : pmPrimeSquareRoughMass ε P X ≤ (M.card : ℝ)*(P : ℝ)^(-2*ε) := by
    change (∑ n ∈ M,(n : ℝ)^(-ε)) ≤ _
    exact (Finset.sum_le_card_nsmul M
      (fun n => (n : ℝ)^(-ε)) ((P : ℝ)^(-2*ε)) hweight).trans_eq (by rw [nsmul_eq_mul])
  have hcardR : (M.card : ℝ) ≤ ((B.card : ℝ)^2+(B.card : ℝ))/2 := by
    calc
      _ ≤ ((B.card+1).choose 2 : ℝ) := by exact_mod_cast hcard
      _ = _ := by rw [Nat.cast_choose_two]; push_cast; ring
  exact hsum.trans (mul_le_mul_of_nonneg_right hcardR (Real.rpow_nonneg hP0.le _))

end RHTower
