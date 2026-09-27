import GaloisForLFunctions.RHTower.ThetaPrimeFrustratedTriangle
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Arbitrarily large finite prime-packet cliques

Euclid supplies a prime sequence with each next prime greater than twice its
predecessor. A common positive radius makes every hub edge prime-resonant and
every leaf edge positive and atom-free. All choices are constructed internally.
-/

noncomputable section

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

def spacedPrimeChoice (N : ℕ) : ℕ := (Nat.exists_infinite_primes N).choose

theorem spacedPrimeChoice_ge (N : ℕ) : N ≤ spacedPrimeChoice N :=
  (Nat.exists_infinite_primes N).choose_spec.1

theorem spacedPrimeChoice_prime (N : ℕ) : Nat.Prime (spacedPrimeChoice N) :=
  (Nat.exists_infinite_primes N).choose_spec.2

def spacedPrimeSequence (N : ℕ) : ℕ → ℕ
  | 0 => spacedPrimeChoice N
  | n + 1 => spacedPrimeChoice (2 * spacedPrimeSequence N n + 1)

theorem spacedPrimeSequence_prime (N n : ℕ) : Nat.Prime (spacedPrimeSequence N n) := by
  cases n <;> exact spacedPrimeChoice_prime _

theorem spacedPrimeSequence_double_succ (N n : ℕ) :
    2 * spacedPrimeSequence N n < spacedPrimeSequence N (n + 1) := by
  have h := spacedPrimeChoice_ge (2 * spacedPrimeSequence N n + 1)
  change 2 * spacedPrimeSequence N n + 1 ≤ spacedPrimeSequence N (n + 1) at h
  omega

theorem strictMono_spacedPrimeSequence (N : ℕ) : StrictMono (spacedPrimeSequence N) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := spacedPrimeSequence_double_succ N n
  omega

theorem spacedPrimeSequence_ge (N n : ℕ) : N ≤ spacedPrimeSequence N n :=
  (spacedPrimeChoice_ge N).trans ((strictMono_spacedPrimeSequence N).monotone (Nat.zero_le n))

theorem spacedPrimeSequence_double_lt (N : ℕ) {i j : ℕ} (hij : i < j) :
    2 * spacedPrimeSequence N i < spacedPrimeSequence N j :=
  (spacedPrimeSequence_double_succ N i).trans_le
    ((strictMono_spacedPrimeSequence N).monotone (Nat.succ_le_of_lt hij))

theorem exists_pos_le_finite_family {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ e i := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    have hs : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
    refine ⟨Finset.univ.inf' hs e, (Finset.lt_inf'_iff _).mpr (fun i _ => he i), ?_⟩
    intro i
    exact Finset.inf'_le _ (Finset.mem_univ i)
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨1, zero_lt_one, fun i => isEmptyElim i⟩

theorem exists_cofinal_thetaFinitePrime_clique (N n : ℕ) :
    ∃ (p : Fin n → ℕ) (r : ℝ) (hr : 0 < r),
      (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
      (∀ i j, i < j → 2 * p i < p j) ∧
      (∀ i, thetaRealWeilPolar (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (Real.log (p i))) < 0) ∧
      (∀ i j, i < j → 0 < thetaRealWeilPolar
        (thetaTranslatedBumpGround r hr (Real.log (p i)))
        (thetaTranslatedBumpGround r hr (Real.log (p j)))) := by
  classical
  let p : Fin n → ℕ := fun i => spacedPrimeSequence N i.val
  have hp (i : Fin n) : Nat.Prime (p i) := spacedPrimeSequence_prime N i.val
  have hpair (i j : Fin n) (hij : i < j) : 2 * p i < p j :=
    spacedPrimeSequence_double_lt N hij
  choose e he hneg using fun i : Fin n => exists_thetaTranslatedBump_prime_negative_radius (hp i)
  have hex (i j : Fin n) : ∃ d : ℝ, 0 < d ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ d →
      i < j → 0 < thetaRealWeilPolar (thetaTranslatedBumpGround r hr (Real.log (p i)))
        (thetaTranslatedBumpGround r hr (Real.log (p j))) := by
    by_cases hij : i < j
    · have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
      have hlog := Real.log_lt_log (mul_pos (by positivity : (0 : ℝ) < 2) hp0)
        (show (2 : ℝ) * p i < p j by exact_mod_cast hpair i j hij)
      rw [Real.log_mul (by norm_num) hp0.ne'] at hlog
      have ht : screwSignThreshold < Real.log 2 :=
        Real.log_lt_log plasticRoot_pos plasticRoot_mem_Ioo.2
      obtain ⟨d, hd, hgood⟩ := exists_thetaTranslatedBump_atomFree_positive_radius
        (show screwSignThreshold < Real.log (p j) - Real.log (p i) by linarith)
        (fun m hm => prime_log_difference_ne_log_nat (hp i) (hp j) (by
          have h := hpair i j hij
          omega) hm)
      exact ⟨d, hd, fun r hr hrd _ => hgood r hr hrd⟩
    · exact ⟨1, zero_lt_one, fun _ _ _ hij' => False.elim (hij hij')⟩
  choose d hd hpos using hex
  let eps : Fin n ⊕ (Fin n × Fin n) → ℝ := Sum.elim e (fun ij => d ij.1 ij.2)
  have heps (i : Fin n ⊕ (Fin n × Fin n)) : 0 < eps i := by
    cases i with
    | inl i => exact he i
    | inr ij => exact hd ij.1 ij.2
  obtain ⟨r, hr, hsmall⟩ := exists_pos_le_finite_family eps heps
  exact ⟨p, r, hr, (fun i => ⟨spacedPrimeSequence_ge N i.val, hp i⟩), hpair,
    (fun i => hneg i r hr (hsmall (Sum.inl i))),
    (fun i j hij => hpos i j r hr (hsmall (Sum.inr (i, j))) hij)⟩

end RHTower
