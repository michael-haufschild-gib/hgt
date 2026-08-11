import GaloisForLFunctions.RHTower.Sieve.MoebiusLogRecursion

/-!
# Finite Heath--Brown identity

Let `M_L` be the Möbius arithmetic function cut off at `L` and put
`E_L = 1 - M_L * ζ`.  Möbius inversion makes `E_L(n) = 0` for `n ≤ L`; hence the
`k`-fold convolution power has no coefficient below `(L+1)^k`.  The geometric identity

`Λ = Λ * E_L^k + M_L * log * ∑_{j<k} E_L^j`

therefore becomes an exact finite identity on that whole coefficient range.  Expanding the defect
powers gives the monomial packet `M_L^(r+1) * ζ^r * log` used by Heath--Brown/Maynard
Dirichlet-polynomial arguments.  Everything here is finite and unconditional.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped zeta Moebius

/-- An arithmetic function has no coefficient below `B`. -/
def VanishesBelow {R : Type*} [Zero R] (F : ArithmeticFunction R) (B : ℕ) : Prop :=
  ∀ n, n < B → F n = 0

/-- Multiplicative convolution multiplies lower support thresholds. -/
theorem vanishesBelow_mul {R : Type*} [CommSemiring R]
    {F G : ArithmeticFunction R} {A B : ℕ}
    (hF : VanishesBelow F A) (hG : VanishesBelow G B) :
    VanishesBelow (F * G) (A * B) := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  by_cases hxa : x.1 < A
  · rw [hF x.1 hxa, zero_mul]
  · have hAle : A ≤ x.1 := Nat.le_of_not_gt hxa
    by_cases hyb : x.2 < B
    · rw [hG x.2 hyb, mul_zero]
    · have hBle : B ≤ x.2 := Nat.le_of_not_gt hyb
      have hprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hab : A * B ≤ n := by
        rw [← hprod]
        exact Nat.mul_le_mul hAle hBle
      exact (not_le_of_gt hn hab).elim

/-- A convolution power raises the lower support threshold to the same power. -/
theorem vanishesBelow_pow {R : Type*} [CommSemiring R]
    {F : ArithmeticFunction R} {B k : ℕ} (hF : VanishesBelow F B) :
    VanishesBelow (F ^ k) (B ^ k) := by
  induction k with
  | zero =>
      intro n hn
      have hn0 : n = 0 := by simpa using hn
      subst n
      simp
  | succ k ih =>
      simpa [pow_succ] using vanishesBelow_mul ih hF

/-- Möbius truncated sharply at `L`. -/
def truncatedMoebius (L : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ L then ((moebius n : ℤ) : ℝ) else 0
  map_zero' := by simp

@[simp] theorem truncatedMoebius_apply (L n : ℕ) :
    truncatedMoebius L n = if n ≤ L then ((moebius n : ℤ) : ℝ) else 0 := rfl

/-- Error made by replacing Möbius by its sharp truncation before convolving with zeta. -/
def moebiusZetaDefect (L : ℕ) : ArithmeticFunction ℝ :=
  1 - truncatedMoebius L * (zeta : ArithmeticFunction ℝ)

/-- The truncation defect starts strictly above `L`. -/
theorem moebiusZetaDefect_vanishesBelow (L : ℕ) :
    VanishesBelow (moebiusZetaDefect L) (L + 1) := by
  intro n hn
  have hnL : n ≤ L := by omega
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [moebiusZetaDefect]
  · have hconv :
        (truncatedMoebius L * (zeta : ArithmeticFunction ℝ)) n =
          (((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
            (zeta : ArithmeticFunction ℝ)) n := by
      simp only [ArithmeticFunction.mul_apply]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxdvd : x.1 ∣ n :=
        Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
      have hxle : x.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hxdvd
      rw [truncatedMoebius_apply, if_pos (hxle.trans hnL)]
      rfl
    rw [moebiusZetaDefect]
    change (1 : ArithmeticFunction ℝ) n -
      (truncatedMoebius L * (zeta : ArithmeticFunction ℝ)) n = 0
    rw [hconv, coe_moebius_mul_coe_zeta]
    simp

/-- The `k`th defect power starts at `(L+1)^k`. -/
theorem moebiusZetaDefect_pow_vanishesBelow (L k : ℕ) :
    VanishesBelow ((moebiusZetaDefect L) ^ k) ((L + 1) ^ k) :=
  vanishesBelow_pow (moebiusZetaDefect_vanishesBelow L)

theorem vonMangoldt_vanishesBelow_one :
    VanishesBelow (vonMangoldt : ArithmeticFunction ℝ) 1 := by
  intro n hn
  have hn0 : n = 0 := by omega
  subst n
  simp

/-- The remainder in the finite decomposition vanishes below `(L+1)^k`. -/
theorem vonMangoldt_mul_defect_pow_vanishesBelow (L k : ℕ) :
    VanishesBelow
      ((vonMangoldt : ArithmeticFunction ℝ) * (moebiusZetaDefect L) ^ k)
      ((L + 1) ^ k) := by
  simpa using vanishesBelow_mul vonMangoldt_vanishesBelow_one
    (moebiusZetaDefect_pow_vanishesBelow L k)

/-- Algebraic finite Heath--Brown decomposition, before the support cutoff is used. -/
theorem heathBrown_geometric_decomposition (L k : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) =
      vonMangoldt * (moebiusZetaDefect L) ^ k +
        truncatedMoebius L * ArithmeticFunction.log *
          (∑ j ∈ Finset.range k, (moebiusZetaDefect L) ^ j) := by
  set M := truncatedMoebius L
  set E := moebiusZetaDefect L
  set Z := (zeta : ArithmeticFunction ℝ)
  have hE : 1 - E = M * Z := by
    simp [E, moebiusZetaDefect, M, Z]
  have hMlog :
      (vonMangoldt : ArithmeticFunction ℝ) * (1 - E) =
        M * ArithmeticFunction.log := by
    calc
      (vonMangoldt : ArithmeticFunction ℝ) * (1 - E) = vonMangoldt * (M * Z) := by rw [hE]
      _ = M * (vonMangoldt * Z) := by ring
      _ = M * ArithmeticFunction.log := by rw [vonMangoldt_mul_zeta]
  have hgeom :
      (1 - E) * (∑ j ∈ Finset.range k, E ^ j) = 1 - E ^ k :=
    mul_neg_geom_sum E k
  calc
    (vonMangoldt : ArithmeticFunction ℝ) = vonMangoldt * E ^ k + vonMangoldt * (1 - E ^ k) := by ring
    _ = vonMangoldt * E ^ k + vonMangoldt *
        ((1 - E) * (∑ j ∈ Finset.range k, E ^ j)) := by rw [hgeom]
    _ = vonMangoldt * E ^ k + (vonMangoldt * (1 - E)) *
        (∑ j ∈ Finset.range k, E ^ j) := by ring
    _ = vonMangoldt * E ^ k + M * ArithmeticFunction.log *
        (∑ j ∈ Finset.range k, E ^ j) := by rw [hMlog]

/-- Finite Heath--Brown identity on every coefficient below the sharp support threshold. -/
theorem heathBrown_identity_of_lt_pow (L k n : ℕ) (hn : n < (L + 1) ^ k) :
    vonMangoldt n =
      (truncatedMoebius L * ArithmeticFunction.log *
        (∑ j ∈ Finset.range k, (moebiusZetaDefect L) ^ j)) n := by
  have hdecomp := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (heathBrown_geometric_decomposition L k)
  have hrem := vonMangoldt_mul_defect_pow_vanishesBelow L k n hn
  simpa [hrem] using hdecomp

/-- Binomial expansion exposing the Dirichlet-polynomial factors in one defect power. -/
theorem moebiusZetaDefect_pow_expansion (L j : ℕ) :
    (moebiusZetaDefect L) ^ j =
      ∑ m ∈ Finset.range (j + 1),
        (-1 : ArithmeticFunction ℝ) ^ (m + j) *
          (truncatedMoebius L) ^ (j - m) *
          (zeta : ArithmeticFunction ℝ) ^ (j - m) *
          (j.choose m : ArithmeticFunction ℝ) := by
  rw [moebiusZetaDefect]
  rw [sub_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [one_pow, mul_pow]
  ring

/-- Explicit finite packet: every term has at least one truncated Möbius factor and at most `k`
such factors.  This is the form consumed by Dirichlet-polynomial estimates. -/
def heathBrownMonomialPacket (L k : ℕ) : ArithmeticFunction ℝ :=
  ∑ j ∈ Finset.range k, ∑ m ∈ Finset.range (j + 1),
    (-1 : ArithmeticFunction ℝ) ^ (m + j) *
      (j.choose m : ArithmeticFunction ℝ) *
      (truncatedMoebius L) ^ (j - m + 1) *
      (zeta : ArithmeticFunction ℝ) ^ (j - m) * ArithmeticFunction.log

theorem heathBrown_geometricPacket_eq_monomialPacket (L k : ℕ) :
    truncatedMoebius L * ArithmeticFunction.log *
        (∑ j ∈ Finset.range k, (moebiusZetaDefect L) ^ j) =
      heathBrownMonomialPacket L k := by
  rw [heathBrownMonomialPacket]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [moebiusZetaDefect_pow_expansion, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pow_succ']
  ring

/-- **Finite Heath--Brown identity, monomial form.**  Below `(L+1)^k`, the von Mangoldt
coefficient is a finite signed sum of terms `M^(r+1) * ζ^r * log`, with `r < k`. -/
theorem heathBrown_monomial_identity_of_lt_pow (L k n : ℕ) (hn : n < (L + 1) ^ k) :
    vonMangoldt n = heathBrownMonomialPacket L k n := by
  rw [← heathBrown_geometricPacket_eq_monomialPacket]
  exact heathBrown_identity_of_lt_pow L k n hn

end RHTower.Sieve
