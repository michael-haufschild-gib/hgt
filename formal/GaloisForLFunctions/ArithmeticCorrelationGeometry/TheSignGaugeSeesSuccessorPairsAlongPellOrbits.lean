import GaloisForLFunctions.ArithmeticCorrelationGeometry.RealMultiplicativeDataSeeOnlySquareSuccessorPairs
import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.LinearCombination

/-!
# The sign gauge sees successor pairs along Pell orbits

Real sources are twisted by completely multiplicative signs `ε_s` (the `2`-torsion of the gauge
torus). The phase gauge makes the terms of a successor correlation `C_h = Σ_j a_j a_{j+h}`
orthogonal — distinct pairs have distinct ratios — so its gauge variance is the diagonal
`Σ_j (a_j a_{j+h})²`. The sign gauge does not.

* **Sign-gauge second moment** (`sum_sq_signTwistedSuccCorr`). If `S` contains every prime of every
  `j(j+h)`, then `Σ_s (C_h^s)² = 2^{|S|} Σ_{j, j'} [j(j+h) · j'(j'+h) = □] a_j a_{j+h} a_{j'} a_{j'+h}`:
  the sign gauge pairs `j` with `j'` exactly when `j(j+h)` and `j'(j'+h)` have the same squarefree
  kernel. The diagonal `j = j'` is the phase-gauge variance (`sum_sq_signTwistedSuccCorr_eq`); the
  rest is the **Pell part**.
* **Every non-square class is a Pell orbit** (`exists_large_pellClass`). If `M = j(j+h)` is not a
  square, `X = 2j + h` solves `X² − 4M U² = h²` with `U = 1`, and the Pell unit of `ℤ[√(4M)]` moves
  it to solutions of every size; each gives `j'` with `j'(j'+h) = M U²`. The class of `j` is
  infinite, while square pairs are finite (`two_mul_add_le_sq_of_squarePair`).
* **The Pell part is unbounded** (`exists_le_card_pellPairs`). For every shift `h ≥ 1` the number of
  off-diagonal coincident pairs `j ≠ j' ≤ N` tends to infinity with the horizon.

Gauge status: the sign-gauge mean of `C_h` sees only the finitely many square pairs, but its
sign-gauge second moment sees infinitely many Pell coincidences. Real multiplicative data are
therefore strictly richer than phase data on successor correlations: they fix, beyond the
coefficient energy, the class sums `Σ_{j(j+h) ∈ k·□} a_j a_{j+h}`, one for each squarefree kernel
`k`, and each class is a Pell orbit.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-! ### Multiplicativity and parity -/

theorem primeSignTwist_mul (S : Finset ℕ) (s : S → ℤˣ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeSignTwist S s (m * n) = primeSignTwist S s m * primeSignTwist S s n := by
  rw [primeSignTwist, primeSignTwist, primeSignTwist, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul hm hn, Finsupp.add_apply, pow_add]

/-- A positive integer is a square iff all its exponents are even. -/
theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨y, rfl⟩ p
    have hy : y ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hy hy, Finsupp.add_apply]
    exact ⟨_, rfl⟩
  · intro he
    obtain ⟨y, hy⟩ := exists_sq_eq_of_even_factorization hn he
    exact ⟨y, hy.symm⟩

/-! ### The sign-gauge second moment -/

open scoped Classical in
/-- **The sign-gauge second moment of a successor correlation.** If `S` contains every prime of
every `j(j+h)`, `j ∈ A`, the sum over all sign vectors of `(C_h^s)²` keeps exactly the pairs
`(j, j')` with `j(j+h) · j'(j'+h)` a perfect square. -/
theorem sum_sq_signTwistedSuccCorr (S A : Finset ℕ) (hA : ∀ j ∈ A, j ≠ 0) (h : ℕ)
    (hS : ∀ j ∈ A, ∀ p, p.Prime → p ∣ j * (j + h) → p ∈ S) (a : ℕ → ℝ) :
    ∑ s : S → ℤˣ, signTwistedSuccCorr S s A h a ^ 2 =
      2 ^ S.card * ∑ j ∈ A, ∑ j' ∈ A,
        if IsSquare (j * (j + h) * (j' * (j' + h))) then
          a j * a (j + h) * (a j' * a (j' + h)) else 0 := by
  have hM0 : ∀ j ∈ A, j * (j + h) ≠ 0 := fun j hj => Nat.mul_ne_zero (hA j hj) (by
    have := hA j hj; omega)
  -- each successor term is the sign twist of `j(j+h)`
  have hterm : ∀ s : S → ℤˣ, signTwistedSuccCorr S s A h a =
      ∑ j ∈ A, ((primeSignTwist S s (j * (j + h)) : ℤ) : ℝ) * (a j * a (j + h)) := by
    intro s
    refine sum_congr rfl fun j hj => ?_
    rw [primeSignTwist_mul S s (hA j hj) (by have := hA j hj; omega)]
    push_cast
    ring
  have hsq : ∀ s : S → ℤˣ, signTwistedSuccCorr S s A h a ^ 2 =
      ∑ j ∈ A, ∑ j' ∈ A, (((primeSignTwist S s (j * (j + h)) *
        primeSignTwist S s (j' * (j' + h)) : ℤ)) : ℝ) * (a j * a (j + h) * (a j' * a (j' + h))) := by
    intro s
    rw [hterm, sq, sum_mul_sum]
    refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
    push_cast
    ring
  simp_rw [hsq]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun j' hj' => ?_
  rw [← sum_mul, ← Int.cast_sum, sum_primeSignTwist_mul,
    prod_two_or_zero S (fun p => (j * (j + h)).factorization p + (j' * (j' + h)).factorization p)]
  -- parity at the primes of `S` is parity everywhere
  have hfac : ∀ p, (j * (j + h) * (j' * (j' + h))).factorization p =
      (j * (j + h)).factorization p + (j' * (j' + h)).factorization p := fun p => by
    rw [Nat.factorization_mul (hM0 j hj) (hM0 j' hj')]; rfl
  have hiff : (∀ p ∈ S, Even ((j * (j + h)).factorization p + (j' * (j' + h)).factorization p)) ↔
      IsSquare (j * (j + h) * (j' * (j' + h))) := by
    rw [isSquare_iff_even_factorization (Nat.mul_ne_zero (hM0 j hj) (hM0 j' hj'))]
    constructor
    · intro hS' p
      rw [hfac]
      by_cases hp : p ∈ S
      · exact hS' p hp
      · have hz : ∀ i ∈ A, (i * (i + h)).factorization p = 0 := by
          intro i hi
          by_contra hne
          have hpr : p.Prime := Nat.prime_of_mem_primeFactors
            (Finsupp.mem_support_iff.mpr hne |> (Nat.support_factorization _ ▸ ·))
          exact hp (hS i hi p hpr (Nat.dvd_of_factorization_pos hne))
        rw [hz j hj, hz j' hj']
        exact ⟨0, rfl⟩
    · intro he p _
      rw [← hfac]
      exact he p
  by_cases hcls : IsSquare (j * (j + h) * (j' * (j' + h)))
  · rw [if_pos (hiff.mpr hcls), if_pos hcls]
    push_cast
    ring
  · rw [if_neg (fun h' => hcls (hiff.mp h')), if_neg hcls]
    simp

open scoped Classical in
/-- **Diagonal plus Pell part.** The sign-gauge second moment is the phase-gauge variance
`Σ_j (a_j a_{j+h})²` plus the off-diagonal pairs of equal squarefree kernel. -/
theorem sum_sq_signTwistedSuccCorr_eq (S A : Finset ℕ) (hA : ∀ j ∈ A, j ≠ 0) (h : ℕ)
    (hS : ∀ j ∈ A, ∀ p, p.Prime → p ∣ j * (j + h) → p ∈ S) (a : ℕ → ℝ) :
    ∑ s : S → ℤˣ, signTwistedSuccCorr S s A h a ^ 2 =
      2 ^ S.card * (∑ j ∈ A, (a j * a (j + h)) ^ 2 + ∑ j ∈ A, ∑ j' ∈ A,
        if j ≠ j' ∧ IsSquare (j * (j + h) * (j' * (j' + h))) then
          a j * a (j + h) * (a j' * a (j' + h)) else 0) := by
  rw [sum_sq_signTwistedSuccCorr S A hA h hS a, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [← add_sum_erase A _ hj, ← add_sum_erase A (fun j' => if j ≠ j' ∧ _ then _ else 0) hj,
    if_pos ⟨j * (j + h), rfl⟩, if_neg (fun h' => h'.1 rfl), zero_add, sq, add_right_inj]
  refine sum_congr rfl fun j' hj' => ?_
  have hne : j ≠ j' := fun h' => (ne_of_mem_erase hj') h'.symm
  simp only [hne, ne_eq, not_false_eq_true, true_and]

/-! ### Pell orbits -/

/-- The Pell step: if `J(J+h) = M U²` and `c² + c = M b²`, the image under the unit
`(2c+1) + b √(4M)` is again a solution, with `J' = (2c+1)J + ch + 2MbU`. -/
theorem pell_step {M h J U b c : ℕ} (e1 : J * (J + h) = M * U ^ 2) (e2 : c ^ 2 + c = M * b ^ 2) :
    ((2 * c + 1) * J + c * h + 2 * M * b * U) * ((2 * c + 1) * J + c * h + 2 * M * b * U + h) =
      M * (b * (2 * J + h) + (2 * c + 1) * U) ^ 2 := by
  have e1' : (J : ℤ) * (J + h) = M * U ^ 2 := by exact_mod_cast e1
  have e2' : (c : ℤ) ^ 2 + c = M * b ^ 2 := by exact_mod_cast e2
  have : ((((2 * c + 1) * J + c * h + 2 * M * b * U) * ((2 * c + 1) * J + c * h + 2 * M * b * U + h) :
      ℕ) : ℤ) = ((M * (b * (2 * J + h) + (2 * c + 1) * U) ^ 2 : ℕ) : ℤ) := by
    push_cast
    linear_combination (1 + 4 * ((c : ℤ) ^ 2 + c - M * b ^ 2)) * e1' + (h : ℤ) ^ 2 * e2'
  exact_mod_cast this

/-- A Pell unit of `ℤ[√(4M)]` for a non-square `M`, written as `(2c+1) + b√(4M)`. -/
theorem exists_pell_unit {M : ℕ} (hM : 0 < M) (hns : ¬ IsSquare M) :
    ∃ b c : ℕ, 0 < b ∧ c ^ 2 + c = M * b ^ 2 := by
  have hns4 : ¬ IsSquare ((4 * M : ℕ) : ℤ) := by
    rintro ⟨r, hr⟩
    have hev : Even (r * r) := by
      rw [← hr]; push_cast; exact ⟨2 * M, by ring⟩
    obtain ⟨t, rfl⟩ := (Int.even_mul.mp hev).elim id id
    apply hns
    rw [← Int.isSquare_natCast_iff]
    exact ⟨t, by push_cast at hr; linarith⟩
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (by positivity) hns4
  set A := x.natAbs
  set B := y.natAbs
  have hAB : A ^ 2 = 4 * M * B ^ 2 + 1 := by
    have : ((A ^ 2 : ℕ) : ℤ) = ((4 * M * B ^ 2 + 1 : ℕ) : ℤ) := by
      push_cast
      rw [Int.natAbs_sq, Int.natAbs_sq]
      push_cast at hxy
      linarith
    exact_mod_cast this
  have hodd : A % 2 = 1 := by
    rcases Nat.even_or_odd A with ⟨k, hk⟩ | hk
    · exfalso
      rw [hk, show (k + k) ^ 2 = 2 * (2 * k ^ 2) by ring,
        show 4 * M * B ^ 2 + 1 = 2 * (2 * M * B ^ 2) + 1 by ring] at hAB
      omega
    · exact Nat.odd_iff.mp hk
  refine ⟨B, A / 2, Int.natAbs_pos.mpr hy, ?_⟩
  have hA : A = 2 * (A / 2) + 1 := by omega
  rw [hA] at hAB
  nlinarith

/-- **Every non-square class is infinite.** If `j(j+h)` is not a perfect square, there are `j'`
beyond every bound with `j'(j'+h) = j(j+h) U²` for some `U`. -/
theorem exists_large_pellClass {j h : ℕ} (hj : 1 ≤ j) (hns : ¬ IsSquare (j * (j + h))) (N : ℕ) :
    ∃ j' U : ℕ, N < j' ∧ j' * (j' + h) = j * (j + h) * U ^ 2 := by
  set M := j * (j + h)
  have hM : 0 < M := Nat.mul_pos hj (by omega)
  obtain ⟨b, c, hb, hbc⟩ := exists_pell_unit hM hns
  -- iterate the Pell step from `(J, U) = (j, 1)`
  let step : ℕ × ℕ → ℕ × ℕ := fun q =>
    ((2 * c + 1) * q.1 + c * h + 2 * M * b * q.2, b * (2 * q.1 + h) + (2 * c + 1) * q.2)
  have hinv : ∀ n : ℕ, (step^[n] (j, 1)).1 * ((step^[n] (j, 1)).1 + h) = M * (step^[n] (j, 1)).2 ^ 2
      ∧ 1 ≤ (step^[n] (j, 1)).2 ∧ j + n ≤ (step^[n] (j, 1)).1 := by
    intro n
    induction n with
    | zero => simp [M]
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨pell_step h1 hbc, ?_, ?_⟩
      · show 1 ≤ b * (2 * (step^[n] (j, 1)).1 + h) + (2 * c + 1) * (step^[n] (j, 1)).2
        nlinarith
      · show j + (n + 1) ≤ (2 * c + 1) * (step^[n] (j, 1)).1 + c * h + 2 * M * b * (step^[n] (j, 1)).2
        have : 1 ≤ 2 * M * b * (step^[n] (j, 1)).2 := by
          have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) hM) hb) h2
          simpa using this.trans' (by norm_num)
        nlinarith
  obtain ⟨h1, -, h3⟩ := hinv (N + 1)
  exact ⟨_, _, by omega, h1⟩

/-- Membership in the Pell class of `j` gives a sign-gauge coincidence with `j`. -/
theorem isSquare_of_pellClass {j h j' U : ℕ} (he : j' * (j' + h) = j * (j + h) * U ^ 2) :
    IsSquare (j * (j + h) * (j' * (j' + h))) :=
  ⟨j * (j + h) * U, by rw [he]; ring⟩

open scoped Classical in
/-- The off-diagonal sign-gauge coincidences up to the horizon `N`. -/
def pellPairs (h N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N).filter fun q => q.1 ≠ q.2 ∧ IsSquare (q.1 * (q.1 + h) * (q.2 * (q.2 + h)))

/-- A shift-`h` successor pair beyond the square-pair range is not a square pair. -/
theorem not_isSquare_succ_mul {h : ℕ} (hh : 1 ≤ h) : ¬ IsSquare (h * h * (h * h + h)) := by
  rintro ⟨y, hy⟩
  have := two_mul_add_le_sq_of_eq hh hy.symm
  nlinarith

/-- **The Pell part is unbounded.** For every shift `h ≥ 1` and every `K`, some horizon carries at
least `K` off-diagonal sign-gauge coincidences. -/
theorem exists_le_card_pellPairs {h : ℕ} (hh : 1 ≤ h) (K : ℕ) : ∃ N, K ≤ #(pellPairs h N) := by
  classical
  set j₀ := h * h
  have hj₀ : 1 ≤ j₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hns := not_isSquare_succ_mul hh
  -- `K` distinct members of the Pell class of `j₀`, all beyond `j₀`
  have hT : ∀ K : ℕ, ∃ T : Finset ℕ, #T = K ∧ ∀ j' ∈ T, j₀ < j' ∧
      IsSquare (j₀ * (j₀ + h) * (j' * (j' + h))) := by
    intro K
    induction K with
    | zero => exact ⟨∅, rfl, by simp⟩
    | succ K ih =>
      obtain ⟨T, hTK, hTmem⟩ := ih
      obtain ⟨j', U, hlt, he⟩ := exists_large_pellClass hj₀ hns (T.sup id + j₀)
      have hnot : j' ∉ T := fun hj' => by
        have := Finset.le_sup (f := id) hj'
        simp at this
        omega
      refine ⟨insert j' T, by rw [card_insert_of_notMem hnot, hTK], fun i hi => ?_⟩
      rcases mem_insert.mp hi with rfl | hi
      · exact ⟨by omega, isSquare_of_pellClass he⟩
      · exact hTmem i hi
  obtain ⟨T, hTK, hTmem⟩ := hT K
  refine ⟨T.sup id + j₀, ?_⟩
  rw [← hTK]
  refine card_le_card_of_injOn (fun j' => (j₀, j')) (fun j' hj' => ?_) (fun x _ y _ hxy => ?_)
  · obtain ⟨hlt, hsq⟩ := hTmem j' hj'
    have hle : j' ≤ T.sup id := Finset.le_sup (f := id) hj'
    simp only [pellPairs, coe_filter, Set.mem_setOf_eq, mem_product, mem_Icc]
    exact ⟨⟨⟨hj₀, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, hsq⟩
  · exact (Prod.mk.inj hxy).2

end GaloisForLFunctions.ArithmeticCorrelationGeometry
