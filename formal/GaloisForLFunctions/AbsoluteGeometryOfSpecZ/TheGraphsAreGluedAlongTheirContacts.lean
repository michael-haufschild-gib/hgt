import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFrobeniusGraphsMeetInThePrimes

/-!
# The graphs are glued along their contacts

The arithmetic square is the union of the Frobenius graphs. This file makes the gluing explicit.

* **Two graphs form a fibre product** (`exists_ghostComponent_eq_iff`): a pair `(u, v)` of integers
  is the restriction of an element of the square to `Γ_m ∪ Γ_n` iff `u − v ∈ J(m, n)`. The index of
  the restriction lattice in `ℤ²` is the order of the contact scheme: for `Γ_1, Γ_n` its logarithm
  is `Λ(n)`.
* **The first `N` graphs form a lattice of index `N!`.** A tuple `(y_n)_{n ≤ N}` extends to the
  square iff it has integral necklace coordinates (`exists_ghost_extension_iff`), and the necklace
  matrix `(d·[d ∣ n])` has determinant `N!` (`det_necklaceMatrix`). The number of gluing conditions
  of the first `N` graphs, in logarithmic measure, is `log N! = Σ_{k ≤ N} ψ(N/k)`.
* **The gluing is not planar** (`exists_ghostComponent_one_two_four_iff`). The graphs
  `Γ_1, Γ_2, Γ_4` restrict to the triples with `2 ∣ v − u` and `4 ∣ w − v`: a lattice of index
  `2³`. Their pairwise contacts at the prime `2` are `1, 2, 1` (`graphIdeal_mul_prime_pow`), of
  sum `4`. For three curves on a regular surface the gluing index is the product of the pairwise
  contact orders; here it is smaller. The arithmetic square has more functions than the trace of a
  surface on its Frobenius graphs.
-/

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- **Two graphs are glued exactly along their contact.** -/
theorem exists_ghostComponent_eq_iff (m n : ℕ+) (u v : ℤ) :
    (∃ x : ghostRing, ghostComponent m x = u ∧ ghostComponent n x = v) ↔
      u - v ∈ graphIdeal m n := by
  constructor
  · rintro ⟨x, rfl, rfl⟩
    exact Ideal.subset_span ⟨x, rfl⟩
  · intro h
    -- the differences `x_m − x_n` already form an ideal
    have hrange : ∀ z ∈ graphIdeal m n,
        ∃ x : ghostRing, ghostComponent m x - ghostComponent n x = z := by
      intro z hz
      refine Submodule.span_induction
        (p := fun z _ => ∃ x : ghostRing, ghostComponent m x - ghostComponent n x = z)
        ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · exact ⟨0, by simp⟩
      · rintro a b _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, by rw [map_add, map_add]; ring⟩
      · rintro c a _ ⟨x, rfl⟩
        exact ⟨(c : ghostRing) * x, by
          simp only [map_mul, map_intCast, Int.cast_id, smul_eq_mul, mul_sub]⟩
    obtain ⟨z, hz⟩ := hrange _ h
    refine ⟨z + ((v - ghostComponent n z : ℤ) : ghostRing), ?_, ?_⟩
    · rw [map_add, map_intCast, Int.cast_id]; linarith
    · rw [map_add, map_intCast, Int.cast_id]; ring

/-! ### The first `N` graphs -/

/-- **The restriction to the first `N` graphs**: a tuple extends to the arithmetic square iff it
has integral necklace coordinates. -/
theorem exists_ghost_extension_iff (N : ℕ) (y : ℕ → ℤ) :
    (∃ x : ghostRing, ∀ n : ℕ+, (n : ℕ) ≤ N → ghostComponent n x = y n) ↔
      ∃ b : ℕ → ℤ, ∀ n : ℕ+, (n : ℕ) ≤ N → y n = ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * b d := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨coord x, fun n hn => by rw [← hx n hn, ghostComponent_eq_sum_coord]⟩
  · rintro ⟨b, hb⟩
    refine ⟨⟨fun n => ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * b d,
      isGhost_of_necklace (b := b) fun _ => rfl⟩, fun n hn => ?_⟩
    rw [hb n hn]
    rfl

/-- The necklace matrix of the first `N` graphs: `M_{n,d} = d` if `d ∣ n`, else `0`. -/
def necklaceMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => if ((j : ℕ) + 1) ∣ ((i : ℕ) + 1) then (((j : ℕ) + 1 : ℕ) : ℤ) else 0

/-- **The gluing index of the first `N` graphs is `N!`.** -/
theorem det_necklaceMatrix (N : ℕ) : (necklaceMatrix N).det = (N.factorial : ℤ) := by
  have htri : (necklaceMatrix N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := hij
    have hnd : ¬ ((j : ℕ) + 1) ∣ ((i : ℕ) + 1) := fun hd => by
      have := Nat.le_of_dvd (Nat.succ_pos _) hd
      omega
    simp only [necklaceMatrix, Matrix.of_apply, if_neg hnd]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp only [necklaceMatrix, Matrix.of_apply, dvd_refl, if_true]
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => ((i + 1 : ℕ) : ℤ)) N, ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]

/-! ### Three graphs through the prime `2` -/

/-- **The graphs `Γ_1, Γ_2, Γ_4`** restrict to the triples `(u, v, w)` with `2 ∣ v − u` and
`4 ∣ w − v`: a lattice of index `8` in `ℤ³`. -/
theorem exists_ghostComponent_one_two_four_iff (u v w : ℤ) :
    (∃ x : ghostRing, ghostComponent 1 x = u ∧ ghostComponent 2 x = v ∧ ghostComponent 4 x = w) ↔
      (2 : ℤ) ∣ v - u ∧ (4 : ℤ) ∣ w - v := by
  have h2 : (2 : ℕ+).Prime := Nat.prime_two
  constructor
  · rintro ⟨x, rfl, rfl, rfl⟩
    have h1 := x.2 2 h2 1
    have h3 := x.2 2 h2 2
    have e24 : (2 : ℕ+) * 2 = 4 := by decide
    have e21 : (2 : ℕ+) * 1 = 2 := by decide
    have f1 : (((1 : ℕ+) : ℕ)).factorization ((2 : ℕ+) : ℕ) = 0 := by
      rw [PNat.one_coe, Nat.factorization_one]; rfl
    have f2 : (((2 : ℕ+) : ℕ)).factorization ((2 : ℕ+) : ℕ) = 1 :=
      Nat.Prime.factorization_self Nat.prime_two
    rw [f1, e21] at h1
    rw [f2, e24] at h3
    exact ⟨by simpa using h1, by simpa using h3⟩
  · rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    refine ⟨(u : ghostRing) + a • orbit 2 + c • orbit 4, ?_, ?_, ?_⟩
    · rw [map_add, map_add, map_intCast, Int.cast_id, map_zsmul, map_zsmul, ghostComponent_apply,
        ghostComponent_apply, orbit_apply, orbit_apply, if_neg (by decide), if_neg (by decide)]
      simp
    · rw [map_add, map_add, map_intCast, Int.cast_id, map_zsmul, map_zsmul, ghostComponent_apply,
        ghostComponent_apply, orbit_apply, orbit_apply, if_pos (by decide), if_neg (by decide)]
      have : (((2 : ℕ+) : ℕ) : ℤ) = 2 := rfl
      rw [this, smul_zero, add_zero, smul_eq_mul]
      linarith
    · rw [map_add, map_add, map_intCast, Int.cast_id, map_zsmul, map_zsmul, ghostComponent_apply,
        ghostComponent_apply, orbit_apply, orbit_apply, if_pos (by decide), if_pos (by decide)]
      have e2 : (((2 : ℕ+) : ℕ) : ℤ) = 2 := rfl
      have e4 : (((4 : ℕ+) : ℕ) : ℤ) = 4 := rfl
      rw [e2, e4, smul_eq_mul, smul_eq_mul]
      linarith

/-- The pairwise contacts of `Γ_1, Γ_2, Γ_4`: orders `1, 2, 1` at the prime `2`. -/
theorem graphIdeal_one_two_four :
    graphIdeal 1 2 = Ideal.span {(2 : ℤ)} ∧ graphIdeal 2 4 = Ideal.span {(4 : ℤ)} ∧
      graphIdeal 1 4 = Ideal.span {(2 : ℤ)} := by
  have h2 : (2 : ℕ+).Prime := Nat.prime_two
  have f2 : (((2 : ℕ+) : ℕ)).factorization ((2 : ℕ+) : ℕ) = 1 :=
    Nat.Prime.factorization_self Nat.prime_two
  refine ⟨?_, ?_, ?_⟩
  · have h := graphIdeal_one_prime_pow h2 (k := 1) one_ne_zero
    rwa [pow_one] at h
  · have h := graphIdeal_mul_prime_pow 2 h2 (j := 1) one_ne_zero
    rw [f2, pow_one] at h
    have e : (2 : ℕ+) * 2 = 4 := by decide
    rw [e] at h
    rw [h]
    norm_num
  · have h := graphIdeal_one_prime_pow h2 (k := 2) two_ne_zero
    have e : (2 : ℕ+) ^ 2 = 4 := by decide
    rwa [e] at h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
