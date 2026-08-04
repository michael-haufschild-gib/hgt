import GaloisForLFunctions.RHTower.Sieve.DirichletCubeCoefficients
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# The fibre of a threefold product is divisor-bounded

A triple `(n,m,k)` with `nmk = j` is determined by the pair `(n, nm)`, and both entries divide `j`.
So the fibre has at most `d(j)²` points, and the divisor bound turns that into

    #fibre ≤ C_ε · N^ε

uniformly over the fibres of `[1,N]³ → [1,N³]`.  This is the coefficient input the sixth-moment
large-values estimate needs: the crude bound `#fibre ≤ N²` is replaced by an arbitrarily small power
of `N`.
-/

namespace RHTower.Sieve

open Finset

/-- **A fibre injects into pairs of divisors.** -/
theorem cubeFibre_card_le_divisors_sq (N : ℕ) (j : Fin (N ^ 3)) :
    (cubeFibre N j).card ≤ (Nat.divisors ((j : ℕ) + 1)).card ^ 2 := by
  classical
  set F : Fin N × Fin N × Fin N → ℕ × ℕ :=
    fun p => ((p.1 : ℕ) + 1, ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1)) with hF
  have hprod : ∀ p ∈ cubeFibre N j,
      ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) = (j : ℕ) + 1 := by
    intro p hp
    simp only [cubeFibre, Finset.mem_filter] at hp
    rw [← cubeIdx_val_add_one p, hp.2]
  have hmaps : ∀ p ∈ cubeFibre N j,
      F p ∈ (Nat.divisors ((j : ℕ) + 1)) ×ˢ (Nat.divisors ((j : ℕ) + 1)) := by
    intro p hp
    have hj : ((j : ℕ) + 1) ≠ 0 := by omega
    have he := hprod p hp
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · refine Nat.mem_divisors.2 ⟨⟨((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1), ?_⟩, hj⟩
      rw [← he]; ring
    · refine Nat.mem_divisors.2 ⟨⟨((p.2.2 : ℕ) + 1), ?_⟩, hj⟩
      rw [← he]
  have hinj : Set.InjOn F (cubeFibre N j) := by
    intro p hp q hq hpq
    have hep := hprod p hp
    have heq := hprod q hq
    have h1n : (p.1 : ℕ) + 1 = (q.1 : ℕ) + 1 := congrArg (fun x : ℕ × ℕ => x.1) hpq
    have h2n : ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) = ((q.1 : ℕ) + 1) * ((q.2.1 : ℕ) + 1) :=
      congrArg (fun x : ℕ × ℕ => x.2) hpq
    have h1 : p.1 = q.1 := Fin.ext (by omega)
    have hpos1 : 0 < (q.1 : ℕ) + 1 := Nat.succ_pos _
    have h2n' := h2n
    rw [h1n] at h2n'
    have h2 : p.2.1 = q.2.1 := Fin.ext (by
      have := Nat.eq_of_mul_eq_mul_left hpos1 h2n'
      omega)
    have heq' : ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((q.2.2 : ℕ) + 1) = (j : ℕ) + 1 := by
      rw [h1, h2]; exact heq
    have hpos2 : 0 < ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) := by positivity
    have h3n : ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1)
        = ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((q.2.2 : ℕ) + 1) := by
      rw [hep, heq']
    have h3 : p.2.2 = q.2.2 := Fin.ext (by
      have := Nat.eq_of_mul_eq_mul_left hpos2 h3n
      omega)
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hcard := Finset.card_le_card_of_injOn F hmaps hinj
  simpa [Finset.card_product, sq] using hcard

/-- **The fibre bound with an arbitrarily small power.** -/
theorem exists_cubeFibre_card_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ j : Fin (N ^ 3),
      ((cubeFibre N j).card : ℝ) ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨C₀, hC₀, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow (ε := ε / 6) (by linarith)
  refine ⟨C₀ ^ 2, by positivity, ?_⟩
  intro N hN j
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hjle : ((j : ℕ) + 1) ≤ N ^ 3 := j.isLt
  have hjcast : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ ((N : ℝ)) ^ (3 : ℕ) := by
    have : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) := by exact_mod_cast hjle
    simpa using this
  have hd := hdiv ((j : ℕ) + 1) (by omega)
  -- the divisor bound at exponent `ε/6`, evaluated at a number of size at most `N³`
  have hbase : (((j : ℕ) + 1 : ℕ) : ℝ) ^ (ε / 6) ≤ ((N : ℝ) ^ (3 : ℕ)) ^ (ε / 6) :=
    Real.rpow_le_rpow (by positivity) hjcast (by linarith)
  have hpow : ((N : ℝ) ^ (3 : ℕ)) ^ (ε / 6) = (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_mul hN0]
    congr 1
    push_cast
    ring
  rw [hpow] at hbase
  have hdle : ((Nat.divisors ((j : ℕ) + 1)).card : ℝ) ≤ C₀ * (N : ℝ) ^ (ε / 2) := by
    refine le_trans hd ?_
    exact mul_le_mul_of_nonneg_left hbase hC₀.le
  have hd0 : (0 : ℝ) ≤ ((Nat.divisors ((j : ℕ) + 1)).card : ℝ) := Nat.cast_nonneg _
  have hsq : ((cubeFibre N j).card : ℝ) ≤ (((Nat.divisors ((j : ℕ) + 1)).card : ℝ)) ^ 2 := by
    have := cubeFibre_card_le_divisors_sq N j
    exact_mod_cast this
  have hmono : (((Nat.divisors ((j : ℕ) + 1)).card : ℝ)) ^ 2
      ≤ (C₀ * (N : ℝ) ^ (ε / 2)) ^ 2 := by
    exact pow_le_pow_left₀ hd0 hdle 2
  have hfinal : (C₀ * (N : ℝ) ^ (ε / 2)) ^ 2 = C₀ ^ 2 * (N : ℝ) ^ ε := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 2)) 2, ← Real.rpow_mul hN0]
    congr 2
    push_cast
    ring
  rw [hfinal] at hmono
  linarith

end RHTower.Sieve
