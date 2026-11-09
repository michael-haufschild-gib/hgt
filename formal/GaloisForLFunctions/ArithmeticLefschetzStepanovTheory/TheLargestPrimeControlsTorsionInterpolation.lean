import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TorsionNewtonRemainders

/-!
# The sharp arithmetic length of integral torsion interpolation

For a nonempty prime set with largest prime `p`, every integral class modulo
`(u_s^q - 1 : s ∈ P)^r` has a representative of length at most `N` exactly
when `N ≥ (∏ s, s^(q-1)) p^(q(r-1))`. The last necessary Newton index uses
every residue exponent `q-1` and places all quotient blocks on `p`.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open ArithmeticHarmonicAnalysis
variable {P : Finset Nat.Primes}

/-- Weight of the last quotient-basis index when `p` is the largest allowed prime. -/
def torsionInterpolationThreshold (q r : ℕ) (p : P) : ℕ :=
  (∏ s : P, ((s : Nat.Primes) : ℕ) ^ (q - 1)) * ((p : Nat.Primes) : ℕ) ^ (q * (r - 1))

/-- The largest residue exponent in each prime coordinate. -/
def torsionBoxTop (q : ℕ) : P →₀ ℕ :=
  Finsupp.onFinset univ (fun _ => q - 1) (fun p _ => mem_univ p)

theorem torsionBoxTop_apply (q : ℕ) (p : P) : torsionBoxTop q p = q - 1 := rfl

/-- All quotient blocks placed on one prime, with all residue exponents maximal. -/
def torsionInterpolationIndex (q r : ℕ) (p : P) : P →₀ ℕ :=
  torsionBoxTop q + Finsupp.single p (q * (r - 1))

theorem torsionInterpolationIndex_order (q r : ℕ) [NeZero q] (p : P) :
    torsionQuotientOrder q (torsionInterpolationIndex q r p) = r - 1 := by
  classical
  have hrem : q - 1 < q := by have := NeZero.pos q; omega
  rw [torsionQuotientOrder, sum_eq_single p]
  · simp only [torsionInterpolationIndex, Finsupp.add_apply, torsionBoxTop_apply,
      Finsupp.single_apply, if_true]
    rw [Nat.add_mul_div_left _ _ (NeZero.pos q), Nat.div_eq_of_lt hrem, zero_add]
  · intro s _ hsp
    have hps : p ≠ s := fun h => hsp h.symm
    simp only [torsionInterpolationIndex, Finsupp.add_apply, torsionBoxTop_apply,
      Finsupp.single_apply, if_neg hps, add_zero, Nat.div_eq_of_lt hrem]
  · intro h
    exact (h (mem_univ p)).elim

theorem weight_torsionInterpolationIndex (q r : ℕ) (p : P) :
    weight (torsionInterpolationIndex q r p) = torsionInterpolationThreshold q r p := by
  rw [torsionInterpolationIndex, weight_add, weight_single]
  rfl

/-- Remainder exponents are bounded coordinatewise; quotient blocks favor the largest prime. -/
theorem weight_le_torsionInterpolationThreshold (q r : ℕ) [NeZero q] (p : P)
    (hmax : ∀ s : P, ((s : Nat.Primes) : ℕ) ≤ ((p : Nat.Primes) : ℕ))
    (a : P →₀ ℕ) (ha : torsionQuotientOrder q a < r) :
    weight a ≤ torsionInterpolationThreshold q r p := by
  have hrem (s : P) : a s % q ≤ q - 1 := by
    have := Nat.mod_lt (a s) (NeZero.pos q)
    omega
  have hquot : torsionQuotientOrder q a ≤ r - 1 := by omega
  calc
    weight a = ∏ s : P,
        ((s : Nat.Primes) : ℕ) ^ (a s % q) * ((s : Nat.Primes) : ℕ) ^ (q * (a s / q)) := by
      unfold weight
      apply prod_congr rfl
      intro s _
      rw [← pow_add, Nat.mod_add_div]
    _ = (∏ s : P, ((s : Nat.Primes) : ℕ) ^ (a s % q)) *
        (∏ s : P, ((s : Nat.Primes) : ℕ) ^ (q * (a s / q))) := prod_mul_distrib
    _ ≤ (∏ s : P, ((s : Nat.Primes) : ℕ) ^ (q - 1)) *
        (∏ s : P, ((p : Nat.Primes) : ℕ) ^ (q * (a s / q))) :=
      Nat.mul_le_mul
        (prod_le_prod' fun s _ => Nat.pow_le_pow_right (s : Nat.Primes).2.pos (hrem s))
        (prod_le_prod' fun s _ => Nat.pow_le_pow_left (hmax s) _)
    _ = (∏ s : P, ((s : Nat.Primes) : ℕ) ^ (q - 1)) *
        ((p : Nat.Primes) : ℕ) ^ (q * torsionQuotientOrder q a) := by
      rw [prod_pow_eq_pow_sum, ← mul_sum]
      rfl
    _ ≤ torsionInterpolationThreshold q r p :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (p : Nat.Primes).2.pos
        (Nat.mul_le_mul_left q hquot))

/-- The exact length threshold for all integral torsion jet classes. -/
theorem universal_torsion_interpolation_iff_largestPrime (q r N : ℕ) [NeZero q]
    (p : P) (hmax : ∀ s : P, ((s : Nat.Primes) : ℕ) ≤ ((p : Nat.Primes) : ℕ))
    (hr : 0 < r) :
    (∀ F : MvPolynomial P ℤ, ∃ G, length G ≤ N ∧ F - G ∈ torsionGridIdeal q ^ r) ↔
      torsionInterpolationThreshold q r p ≤ N := by
  rw [universal_torsion_interpolation_iff_index_weights]
  constructor
  · intro h
    have htop : torsionQuotientOrder q (torsionInterpolationIndex q r p) < r := by
      rw [torsionInterpolationIndex_order]
      omega
    simpa only [weight_torsionInterpolationIndex] using h (torsionInterpolationIndex q r p) htop
  · intro h a ha
    exact (weight_le_torsionInterpolationThreshold q r p hmax a ha).trans h

/-- At order zero there are no jet constraints. -/
theorem universal_torsion_interpolation_zero (q N : ℕ) [NeZero q] :
    ∀ F : MvPolynomial P ℤ, ∃ G, length G ≤ N ∧ F - G ∈ torsionGridIdeal q ^ 0 := by
  rw [universal_torsion_interpolation_iff_index_weights]
  intro a ha
  exact (Nat.not_lt_zero _ ha).elim

/-- With no prime variables, integral classes are constants and require length one. -/
theorem universal_torsion_interpolation_empty (q r N : ℕ) [NeZero q] (hr : 0 < r) :
    (∀ F : MvPolynomial (∅ : Finset Nat.Primes) ℤ,
      ∃ G, length G ≤ N ∧ F - G ∈ torsionGridIdeal q ^ r) ↔ 1 ≤ N := by
  rw [universal_torsion_interpolation_iff_index_weights]
  constructor
  · intro h
    have ha : torsionQuotientOrder q (0 : (∅ : Finset Nat.Primes) →₀ ℕ) < r := by
      simpa only [torsionQuotientOrder, univ_eq_empty, sum_empty] using hr
    simpa only [weight, univ_eq_empty, prod_empty] using h 0 ha
  · intro h a _
    simpa only [weight, univ_eq_empty, prod_empty] using h

/-- The universal cutoff, including zero order and empty prime support. -/
def torsionInterpolationCutoff (P : Finset Nat.Primes) (q r : ℕ) : ℕ :=
  if r = 0 then 0 else
    (∏ s : P, ((s : Nat.Primes) : ℕ) ^ (q - 1)) *
      (max 1 (P.sup (fun p : Nat.Primes => (p : ℕ)))) ^ (q * (r - 1))

/-- All integral torsion jet classes can be interpolated exactly at this arithmetic cutoff. -/
theorem universal_torsion_interpolation_iff_cutoff (q r N : ℕ) [NeZero q] :
    (∀ F : MvPolynomial P ℤ, ∃ G, length G ≤ N ∧ F - G ∈ torsionGridIdeal q ^ r) ↔
      torsionInterpolationCutoff P q r ≤ N := by
  classical
  by_cases hr0 : r = 0
  · subst r
    simp only [torsionInterpolationCutoff, if_true, Nat.zero_le, iff_true]
    exact universal_torsion_interpolation_zero (P := P) q N
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  by_cases hP : P.Nonempty
  · obtain ⟨p, hp, hmax⟩ := exists_max_image P (fun p : Nat.Primes => (p : ℕ)) hP
    have hsup : P.sup (fun p : Nat.Primes => (p : ℕ)) = (p : ℕ) :=
      le_antisymm (Finset.sup_le hmax) (le_sup hp)
    have hp1 : 1 ≤ (p : ℕ) := p.2.one_lt.le
    rw [torsionInterpolationCutoff, if_neg hr0, hsup, max_eq_right hp1]
    exact universal_torsion_interpolation_iff_largestPrime q r N ⟨p, hp⟩
      (fun s => hmax s s.2) hr
  · have he : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    rw [universal_torsion_interpolation_empty q r N hr]
    simp [torsionInterpolationCutoff, hr0]

#print axioms universal_torsion_interpolation_iff_largestPrime
#print axioms universal_torsion_interpolation_empty
#print axioms universal_torsion_interpolation_iff_cutoff

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
