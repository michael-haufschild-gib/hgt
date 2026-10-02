import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanAbsolute

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

def pmPowerDampedMobiusAF (ε : ℝ) : ArithmeticFunction ℂ where
  toFun := pmPowerDampedMobiusCoeff ε
  map_zero' := pmPowerDampedMobiusCoeff_zero ε

def pmPowerDampedUnitAF (ε : ℝ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else (((n : ℝ)^(-ε) : ℝ) : ℂ)
  map_zero' := by simp

theorem pmPowerDampedUnitAF_mul_mobius (ε : ℝ) :
    pmPowerDampedUnitAF ε * pmPowerDampedMobiusAF ε = 1 := by
  ext n
  by_cases hn : n = 0
  · subst n; simp
  rw [ArithmeticFunction.mul_apply]
  have he : (∑ x ∈ n.divisorsAntidiagonal,
      pmPowerDampedUnitAF ε x.1 * pmPowerDampedMobiusAF ε x.2) =
      (((n : ℝ)^(-ε) : ℝ) : ℂ) *
        ∑ x ∈ n.divisorsAntidiagonal, (moebius x.2 : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hm := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hx0 : x.1 ≠ 0 := by intro hz; simp only [hz, zero_mul] at hm; exact hn hm.symm
    have hw := congrArg (fun y : ℝ => (y : ℂ))
      ((pmNaturalRpowHom ε).map_mul x.1 x.2)
    change ((((x.1*x.2 : ℕ) : ℝ)^(-ε) : ℝ) : ℂ) =
      (((x.1 : ℝ)^(-ε) * (x.2 : ℝ)^(-ε) : ℝ) : ℂ) at hw
    rw [hm, Complex.ofReal_mul] at hw
    simp only [pmPowerDampedUnitAF, pmPowerDampedMobiusAF, ArithmeticFunction.coe_mk,
      if_neg hx0, pmPowerDampedMobiusCoeff, Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [hw]
    ring
  rw [he, pm_mobius_antidiagonal_sum, ArithmeticFunction.one_apply]
  split_ifs with h
  · simp [h]
  · simp

def pmPowerDampedRamanujanColumn (ε : ℝ) (m : ℕ) : ArithmeticFunction ℂ where
  toFun d := (d : ℂ)*(moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)
  map_zero' := by simp

def pmPowerDampedRamanujanTransfer (ε : ℝ) (m : ℕ) : ArithmeticFunction ℂ :=
  pmPowerDampedUnitAF ε * pmPowerDampedRamanujanColumn ε m

theorem pmPowerDampedRamanujanTransfer_inversion (ε : ℝ) (m : ℕ) :
    pmPowerDampedRamanujanTransfer ε m * pmPowerDampedMobiusAF ε =
      pmPowerDampedRamanujanColumn ε m := by
  rw [pmPowerDampedRamanujanTransfer, mul_right_comm,
    pmPowerDampedUnitAF_mul_mobius, one_mul]

def pmArithmeticFermiPrefix (f : ArithmeticFunction ℂ) (Q : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 Q, f d * fermiNymanGen (d : ℝ) t)

theorem pmArithmeticFermiPrefix_mobius (ε : ℝ) (Q : ℕ) (t : ℝ) :
    pmArithmeticFermiPrefix (pmPowerDampedMobiusAF ε) Q t =
      pmPowerDampedFermiPrefix ε Q t := by
  simp only [pmArithmeticFermiPrefix, pmPowerDampedFermiPrefix,
    pmPowerDampedMobiusAF, ArithmeticFunction.coe_mk, pmPowerDampedMobiusCoeff,
    Complex.ofReal_mul, Complex.ofReal_intCast]

theorem pm_fermiNymanGen_mul (a b t : ℝ) :
    fermiNymanGen (a*b) t = fermiNymanGen b (a*t) := by
  rw [pm_fermiNymanGen_dilate, pm_fermiNymanGen_dilate b]
  congr 1
  ring

theorem pmArithmeticFermiPrefix_convolution (f g : ArithmeticFunction ℂ) (Q : ℕ) (t : ℝ) :
    pmArithmeticFermiPrefix (f*g) Q t =
      ∑ r ∈ Finset.Icc 1 Q, f r * pmArithmeticFermiPrefix g (Q/r) ((r : ℝ)*t) := by
  have he : (∑ n ∈ Finset.Icc 1 Q, (f*g) n*fermiNymanGen (n : ℝ) t) =
      ∑ n ∈ Finset.Icc 1 Q, ∑ x ∈ n.divisorsAntidiagonal,
        f x.1*g x.2*fermiNymanGen ((x.1*x.2 : ℕ) : ℝ) t := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  unfold pmArithmeticFermiPrefix
  rw [he, Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun a b => f a*g b*fermiNymanGen ((a*b : ℕ) : ℝ) t)]
  simp only [Nat.cast_mul, pm_fermiNymanGen_mul, mul_neg, Finset.mul_sum,
    ← Finset.sum_neg_distrib, mul_assoc]

theorem pm_hyperbola_sum_swap (F : ℕ → ℕ → ℂ) (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q/d), F d m) =
      ∑ m ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 1 (Q/m), F d m := by
  rw [← Sieve.sum_Icc_divisorsAntidiagonal_swap,
    ← Sieve.sum_Icc_divisorsAntidiagonal_swap]
  apply Finset.sum_congr rfl
  intro n hn
  conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal (n := n), Finset.sum_map]
  rfl

def pmPowerDampedRamanujanFermiPrefix (ε : ℝ) (Q : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 Q, pmPowerDampedRamanujanCofactor ε Q d *
    fermiNymanGen (d : ℝ) t)

theorem pmPowerDampedRamanujanFermiPrefix_eq_columns (ε : ℝ) (Q : ℕ) (t : ℝ) :
    pmPowerDampedRamanujanFermiPrefix ε Q t =
      ∑ m ∈ Finset.Icc 1 Q, pmArithmeticFermiPrefix (pmPowerDampedRamanujanColumn ε m) (Q/m) t := by
  unfold pmPowerDampedRamanujanFermiPrefix
  have he : (∑ d ∈ Finset.Icc 1 Q,
      pmPowerDampedRamanujanCofactor ε Q d * fermiNymanGen (d : ℝ) t) =
      ∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q/d),
        pmPowerDampedRamanujanColumn ε m d * fermiNymanGen (d : ℝ) t := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [pmPowerDampedRamanujanCofactor, Finset.mul_sum, Finset.sum_mul,
      pmPowerDampedRamanujanColumn, ArithmeticFunction.coe_mk, mul_assoc]
  rw [he, pm_hyperbola_sum_swap]
  simp only [pmArithmeticFermiPrefix, Finset.sum_neg_distrib]

theorem pmPowerDampedRamanujanFermiPrefix_eq_transfer (ε : ℝ) (Q : ℕ) (t : ℝ) :
    pmPowerDampedRamanujanFermiPrefix ε Q t =
      ∑ m ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (Q/m),
        pmPowerDampedRamanujanTransfer ε m r *
          pmPowerDampedFermiPrefix ε (Q/(m*r)) ((r : ℝ)*t) := by
  rw [pmPowerDampedRamanujanFermiPrefix_eq_columns]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← pmPowerDampedRamanujanTransfer_inversion ε m, pmArithmeticFermiPrefix_convolution]
  simp only [pmArithmeticFermiPrefix_mobius, Nat.div_div_eq_div_mul]

end RHTower
