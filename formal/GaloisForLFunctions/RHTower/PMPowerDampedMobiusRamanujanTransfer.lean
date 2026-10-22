import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanAbsolute

/-!
# Transfer from Ramanujan Fermi prefixes to dilated Möbius Fermi prefixes

The damped Möbius function `μ_ε(n) = μ(n) n^(−ε)` has Dirichlet inverse `u_ε(n) = n^(−ε)`.
Each Ramanujan column `k_m(d) = d μ(m) w_ε(dm)` is therefore `T_m * μ_ε` for the transfer
coefficients `T_m = u_ε * k_m`. Fermi prefixes `−∑_{d≤Q} f(d) φ_d(t)`, with
`φ_a(t) = {1/(at)} − 2{1/(2at)}`, convert Dirichlet convolution into sums of dilated prefixes,
because `φ_{ab}(t) = φ_b(a t)`. Combining these with a hyperbola swap rewrites the Ramanujan Fermi
prefix `−∑_{d≤Q} K_Q(d) φ_d(t)` exactly as a finite combination of dilated power-damped Möbius
Fermi prefixes `−∑_{d≤M} μ(d) d^(−ε) φ_d(r t)`.

## Main results

- `pmPowerDampedUnitAF_mul_mobius`: `u_ε * μ_ε = 1` in the ring of arithmetic functions.
- `pmPowerDampedRamanujanTransfer_inversion`: `T_m * μ_ε = k_m`.
- `pmArithmeticFermiPrefix_convolution`: the Fermi prefix of `f * g` is `∑_{r≤Q} f(r) · (Fermi prefix of g, length ⌊Q/r⌋, at r t)`.
- `pmPowerDampedRamanujanFermiPrefix_eq_columns`: the Ramanujan Fermi prefix is the sum over `m ≤ Q` of the column prefixes of length `⌊Q/m⌋`.
- `pmPowerDampedRamanujanFermiPrefix_eq_transfer`: the Ramanujan Fermi prefix equals `∑_{m≤Q} ∑_{r≤Q/m} T_m(r) · F^ε_{⌊Q/(mr)⌋}(r t)`, with `F^ε_M` the power-damped Möbius Fermi prefix.

## Hypotheses

All results are unconditional finite algebraic identities; no restriction on `ε` is needed.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The damped Möbius function `μ_ε(n) = μ(n) n^(−ε)` as an arithmetic function. -/
def pmPowerDampedMobiusAF (ε : ℝ) : ArithmeticFunction ℂ where
  toFun := pmPowerDampedMobiusCoeff ε
  map_zero' := pmPowerDampedMobiusCoeff_zero ε

/-- The completely multiplicative function `u_ε(n) = n^(−ε)` (`u_ε(0) = 0`). -/
def pmPowerDampedUnitAF (ε : ℝ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else (((n : ℝ)^(-ε) : ℝ) : ℂ)
  map_zero' := by simp

/-- `u_ε` and `μ_ε` are Dirichlet inverses: `u_ε * μ_ε = 1`. -/
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

/-- The Ramanujan column `k_m(d) = d μ(m) w_ε(dm)`. -/
def pmPowerDampedRamanujanColumn (ε : ℝ) (m : ℕ) : ArithmeticFunction ℂ where
  toFun d := (d : ℂ)*(moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)
  map_zero' := by simp

/-- The transfer coefficients `T_m = u_ε * k_m`. -/
def pmPowerDampedRamanujanTransfer (ε : ℝ) (m : ℕ) : ArithmeticFunction ℂ :=
  pmPowerDampedUnitAF ε * pmPowerDampedRamanujanColumn ε m

/-- The transfer coefficients reproduce the column: `T_m * μ_ε = k_m`. -/
theorem pmPowerDampedRamanujanTransfer_inversion (ε : ℝ) (m : ℕ) :
    pmPowerDampedRamanujanTransfer ε m * pmPowerDampedMobiusAF ε =
      pmPowerDampedRamanujanColumn ε m := by
  rw [pmPowerDampedRamanujanTransfer, mul_right_comm,
    pmPowerDampedUnitAF_mul_mobius, one_mul]

/-- The Fermi prefix `−∑_{d≤Q} f(d) φ_d(t)` of an arithmetic function `f`. -/
def pmArithmeticFermiPrefix (f : ArithmeticFunction ℂ) (Q : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 Q, f d * fermiNymanGen (d : ℝ) t)

/-- The Fermi prefix of `μ_ε` is the power-damped Möbius Fermi prefix. -/
theorem pmArithmeticFermiPrefix_mobius (ε : ℝ) (Q : ℕ) (t : ℝ) :
    pmArithmeticFermiPrefix (pmPowerDampedMobiusAF ε) Q t =
      pmPowerDampedFermiPrefix ε Q t := by
  simp only [pmArithmeticFermiPrefix, pmPowerDampedFermiPrefix,
    pmPowerDampedMobiusAF, ArithmeticFunction.coe_mk, pmPowerDampedMobiusCoeff,
    Complex.ofReal_mul, Complex.ofReal_intCast]

/-- Dilation rule for the alternating Nyman generator: `φ_{ab}(t) = φ_b(a t)`. -/
theorem pm_fermiNymanGen_mul (a b t : ℝ) :
    fermiNymanGen (a*b) t = fermiNymanGen b (a*t) := by
  rw [pm_fermiNymanGen_dilate, pm_fermiNymanGen_dilate b]
  congr 1
  ring

/-- Convolution rule: the Fermi prefix of `f * g` of length `Q` at `t` equals
`∑_{r≤Q} f(r) · (Fermi prefix of g of length ⌊Q/r⌋ at r t)`. -/
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

/-- Hyperbola swap `∑_{d≤Q} ∑_{m≤Q/d} F(d,m) = ∑_{m≤Q} ∑_{d≤Q/m} F(d,m)`. -/
theorem pm_hyperbola_sum_swap (F : ℕ → ℕ → ℂ) (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q/d), F d m) =
      ∑ m ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 1 (Q/m), F d m := by
  rw [← Sieve.sum_Icc_divisorsAntidiagonal_swap,
    ← Sieve.sum_Icc_divisorsAntidiagonal_swap]
  apply Finset.sum_congr rfl
  intro n hn
  conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal (n := n), Finset.sum_map]
  rfl

/-- The Ramanujan Fermi prefix `−∑_{d≤Q} K_Q(d) φ_d(t)` built from the cofactors `K_Q(d)`. -/
def pmPowerDampedRamanujanFermiPrefix (ε : ℝ) (Q : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 Q, pmPowerDampedRamanujanCofactor ε Q d *
    fermiNymanGen (d : ℝ) t)

/-- The Ramanujan Fermi prefix is `∑_{m≤Q}` of the Fermi prefixes of the columns `k_m` of length `⌊Q/m⌋`. -/
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

/-- Transfer identity: the Ramanujan Fermi prefix equals
`∑_{m≤Q} ∑_{r≤Q/m} T_m(r) · F^ε_{⌊Q/(mr)⌋}(r t)`, a combination of dilated damped Möbius Fermi prefixes. -/
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
