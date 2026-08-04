import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureSixthMoment
import GaloisForLFunctions.RHTower.Sieve.DirichletSymmSplit

/-!
# Prime-supported cubes have absolutely bounded fibres

For coefficients supported on shifted primes, the only triples contributing to the threefold
convolution are triples of primes.  By uniqueness of factorization, a triple of primes with a fixed
product has its first two coordinates among the at most three prime factors of that product, and
the third coordinate is then determined; the contributing fibre has at most nine points.

The sixth-moment level-set bound for a prime-supported Dirichlet polynomial therefore carries the
absolute constant `9` in place of the divisor-bound factor `C_ε N^ε`: no power of the length is
lost.  This is the coefficient input for the factorized mean square, where the short factor is a
polynomial over a dyadic range of primes.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The part of a cube fibre whose three coordinates lie in a support. -/
noncomputable def cubeFibreOn (N : ℕ) (S : Finset (Fin N)) (j : Fin (N ^ 3)) :
    Finset (Fin N × Fin N × Fin N) :=
  (cubeFibre N j).filter (fun p => p.1 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S)

/-- **The `ℓ²` norm of the threefold convolution, through a support.**  Only fibre points with all
three coordinates in the support of the coefficients contribute, so only their count enters the
Cauchy–Schwarz step. -/
theorem sum_normSq_convCube_le_of_support (N : ℕ) (a : Fin N → ℂ) (S : Finset (Fin N))
    (hsupp : ∀ n : Fin N, a n ≠ 0 → n ∈ S) {D : ℝ}
    (hD : ∀ j : Fin (N ^ 3), ((cubeFibreOn N S j).card : ℝ) ≤ D) (hD0 : 0 ≤ D) :
    ∑ j : Fin (N ^ 3), ‖convCube N a j‖ ^ 2
      ≤ D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3 := by
  classical
  set g : Fin N × Fin N × Fin N → ℝ := fun p => ‖a p.1 * a p.2.1 * a p.2.2‖ with hg
  have hconv : ∀ j : Fin (N ^ 3),
      convCube N a j = ∑ p ∈ cubeFibreOn N S j, a p.1 * a p.2.1 * a p.2.2 := by
    intro j
    rw [convCube, cubeFibreOn, cubeFibre]
    exact (Finset.sum_filter_of_ne (fun p _ hne => by
      rcases mul_ne_zero_iff.mp hne with ⟨h12, h3⟩
      rcases mul_ne_zero_iff.mp h12 with ⟨h1, h2⟩
      exact ⟨hsupp _ h1, hsupp _ h2, hsupp _ h3⟩)).symm
  have hfibre : ∀ j : Fin (N ^ 3),
      ‖convCube N a j‖ ^ 2 ≤ D * ∑ p ∈ cubeFibreOn N S j, g p ^ 2 := by
    intro j
    have hnorm : ‖convCube N a j‖ ≤ ∑ p ∈ cubeFibreOn N S j, g p := by
      rw [hconv j]
      exact norm_sum_le _ _
    have hsq : ‖convCube N a j‖ ^ 2 ≤ (∑ p ∈ cubeFibreOn N S j, g p) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs : (∑ p ∈ cubeFibreOn N S j, g p) ^ 2
        ≤ ((cubeFibreOn N S j).card : ℝ) * ∑ p ∈ cubeFibreOn N S j, g p ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hsum0 : (0 : ℝ) ≤ ∑ p ∈ cubeFibreOn N S j, g p ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hmul : ((cubeFibreOn N S j).card : ℝ) * ∑ p ∈ cubeFibreOn N S j, g p ^ 2
        ≤ D * ∑ p ∈ cubeFibreOn N S j, g p ^ 2 :=
      mul_le_mul_of_nonneg_right (hD j) hsum0
    linarith
  have hsum : ∑ j : Fin (N ^ 3), ‖convCube N a j‖ ^ 2
      ≤ ∑ j : Fin (N ^ 3), D * ∑ p ∈ cubeFibreOn N S j, g p ^ 2 :=
    Finset.sum_le_sum fun j _ => hfibre j
  set sSet : Finset (Fin N × Fin N × Fin N) :=
    (Finset.univ : Finset (Fin N × Fin N × Fin N)).filter
      (fun p => p.1 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S) with hsSet
  have hfibreOn : ∀ j : Fin (N ^ 3),
      cubeFibreOn N S j = sSet.filter (fun p => cubeIdx p = j) := by
    intro j
    rw [cubeFibreOn, cubeFibre, hsSet]
    exact Finset.filter_comm _ _ _
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := sSet) (t := (Finset.univ : Finset (Fin (N ^ 3)))) (g := fun p => cubeIdx p)
    (f := fun p : Fin N × Fin N × Fin N => g p ^ 2)
    (fun p _ => Finset.mem_univ _)
  have hcollect : ∑ j : Fin (N ^ 3), D * ∑ p ∈ cubeFibreOn N S j, g p ^ 2
      = D * ∑ p ∈ sSet, g p ^ 2 := by
    simp only [hfibreOn]
    rw [← Finset.mul_sum, hfib]
  have hmono : ∑ p ∈ sSet, g p ^ 2 ≤ ∑ p : Fin N × Fin N × Fin N, g p ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => sq_nonneg _)
  have hprod : ∑ p : Fin N × Fin N × Fin N, g p ^ 2
      = (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3 := by
    have hpt : ∀ p : Fin N × Fin N × Fin N,
        g p ^ 2 = ‖a p.1‖ ^ 2 * (‖a p.2.1‖ ^ 2 * ‖a p.2.2‖ ^ 2) := by
      intro p
      rw [hg]
      simp only [norm_mul]
      ring
    simp only [hpt, Fintype.sum_prod_type]
    rw [pow_three]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  calc ∑ j : Fin (N ^ 3), ‖convCube N a j‖ ^ 2
      ≤ ∑ j : Fin (N ^ 3), D * ∑ p ∈ cubeFibreOn N S j, g p ^ 2 := hsum
    _ = D * ∑ p ∈ sSet, g p ^ 2 := hcollect
    _ ≤ D * ∑ p : Fin N × Fin N × Fin N, g p ^ 2 :=
        mul_le_mul_of_nonneg_left hmono hD0
    _ = D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3 := by rw [hprod]

/-- The shifted-prime support inside a coefficient range. -/
def primeSupport (N : ℕ) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)).filter (fun n => Nat.Prime ((n : ℕ) + 1))

/-- A prime dividing a product of three primes is one of them. -/
theorem prime_eq_of_dvd_mul_three {p a b c : ℕ} (hp : p.Prime) (ha : a.Prime) (hb : b.Prime)
    (hc : c.Prime) (hdvd : p ∣ a * b * c) : p = a ∨ p = b ∨ p = c := by
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp ha).mp h')
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hb).mp h'))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hc).mp h))

/-- **A prime-supported cube fibre has at most nine points.**  The first two coordinates of any
fibre point lie among the at most three prime factors of the anchored product, and the third is
determined by the product. -/
theorem cubeFibreOn_primeSupport_card_le_nine (N : ℕ) (j : Fin (N ^ 3)) :
    ((cubeFibreOn N (primeSupport N) j).card : ℝ) ≤ 9 := by
  classical
  have hprodEq : ∀ p ∈ cubeFibreOn N (primeSupport N) j,
      ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) = (j : ℕ) + 1 := by
    intro p hp
    rw [cubeFibreOn, Finset.mem_filter] at hp
    have hmem := hp.1
    rw [cubeFibre, Finset.mem_filter] at hmem
    rw [← cubeIdx_val_add_one p, hmem.2]
  have hprime : ∀ p ∈ cubeFibreOn N (primeSupport N) j,
      Nat.Prime ((p.1 : ℕ) + 1) ∧ Nat.Prime ((p.2.1 : ℕ) + 1)
        ∧ Nat.Prime ((p.2.2 : ℕ) + 1) := by
    intro p hp
    rw [cubeFibreOn, Finset.mem_filter] at hp
    obtain ⟨h1, h2, h3⟩ := hp.2
    rw [primeSupport, Finset.mem_filter] at h1 h2 h3
    exact ⟨h1.2, h2.2, h3.2⟩
  have hnat : (cubeFibreOn N (primeSupport N) j).card ≤ 9 := by
    rcases Finset.eq_empty_or_nonempty (cubeFibreOn N (primeSupport N) j) with he | hne
    · rw [he]
      norm_num
    · obtain ⟨q₀, hq₀⟩ := hne
      obtain ⟨hqa, hqb, hqc⟩ := hprime q₀ hq₀
      have hq₀prod := hprodEq q₀ hq₀
      set T : Finset (Fin N) := insert q₀.1 (insert q₀.2.1 {q₀.2.2}) with hT
      have hTcard : T.card ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
        refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
        simp
      have hcoordT : ∀ p ∈ cubeFibreOn N (primeSupport N) j,
          ∀ x : Fin N, Nat.Prime ((x : ℕ) + 1) →
          ((x : ℕ) + 1) ∣ ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) →
          x ∈ T := by
        intro p hp x hx hdvd
        rw [hprodEq p hp, ← hq₀prod] at hdvd
        rcases prime_eq_of_dvd_mul_three hx hqa hqb hqc hdvd with h | h | h
        · exact Finset.mem_insert.mpr (Or.inl (Fin.ext (by omega)))
        · refine Finset.mem_insert.mpr (Or.inr ?_)
          exact Finset.mem_insert.mpr (Or.inl (Fin.ext (by omega)))
        · refine Finset.mem_insert.mpr (Or.inr ?_)
          refine Finset.mem_insert.mpr (Or.inr ?_)
          exact Finset.mem_singleton.mpr (Fin.ext (by omega))
      have hmaps : ∀ p ∈ cubeFibreOn N (primeSupport N) j,
          (p.1, p.2.1) ∈ T ×ˢ T := by
        intro p hp
        obtain ⟨h1, h2, _⟩ := hprime p hp
        refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · exact hcoordT p hp p.1 h1 ⟨((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1), by ring⟩
        · exact hcoordT p hp p.2.1 h2 ⟨((p.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1), by ring⟩
      have hinj : Set.InjOn (fun p : Fin N × Fin N × Fin N => (p.1, p.2.1))
          (cubeFibreOn N (primeSupport N) j) := by
        intro p hp q hq hpq
        have hp1 := hprodEq p (Finset.mem_coe.mp hp)
        have hq1 := hprodEq q (Finset.mem_coe.mp hq)
        have hpq' : (p.1, p.2.1) = (q.1, q.2.1) := hpq
        have h1 : p.1 = q.1 := congrArg (fun x : Fin N × Fin N => x.1) hpq'
        have h2 : p.2.1 = q.2.1 := congrArg (fun x : Fin N × Fin N => x.2) hpq'
        have hpos : 0 < ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) := by positivity
        have heq : ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1)
            = ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((q.2.2 : ℕ) + 1) := by
          rw [hp1, h1, h2, hq1]
        have h3 : (p.2.2 : ℕ) + 1 = (q.2.2 : ℕ) + 1 :=
          Nat.eq_of_mul_eq_mul_left hpos heq
        have h3' : p.2.2 = q.2.2 := Fin.ext (by omega)
        exact Prod.ext h1 (Prod.ext h2 h3')
      have hcard := Finset.card_le_card_of_injOn
        (f := fun p : Fin N × Fin N × Fin N => (p.1, p.2.1))
        (s := cubeFibreOn N (primeSupport N) j) (t := T ×ˢ T) hmaps hinj
      have hTT : (T ×ˢ T).card ≤ 9 := by
        rw [Finset.card_product]
        nlinarith [hTcard]
      exact le_trans hcard hTT
  exact_mod_cast le_trans hnat (by norm_num)

/-- **The `ℓ²` norm of the cube of a prime-supported coefficient vector**, with the absolute
constant nine. -/
theorem sum_normSq_convCube_le_of_prime_support (N : ℕ) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1)) :
    ∑ j : Fin (N ^ 3), ‖convCube N a j‖ ^ 2
      ≤ 9 * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3 :=
  sum_normSq_convCube_le_of_support N a (primeSupport N)
    (fun n hn => by
      rw [primeSupport, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hsupp n hn⟩)
    (fun j => cubeFibreOn_primeSupport_card_le_nine N j) (by norm_num)

/-- **The sixth-moment level-set bound for a prime-supported polynomial.**  No power of the length
is lost: the fibre constant is nine. -/
theorem volume_largeValues_sixth_le_of_prime_support (N : ℕ) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 6 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
          * (9 * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3) := by
  have hV3 : (0 : ℝ) ≤ V ^ 3 := by positivity
  have hbase := volume_largeValues_le (N ^ 3) (convCube N a) hT hV3
  rw [largeValues_cube_setOf N a _ hV] at hbase
  have hpow : (V ^ 3) ^ 2 = V ^ 6 := by ring
  rw [hpow] at hbase
  refine le_trans hbase ?_
  have hlogN3 : (0 : ℝ) ≤ Real.log ((N ^ 3 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ 3) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ 3 := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)) := by nlinarith
  exact mul_le_mul_of_nonneg_left
    (sum_normSq_convCube_le_of_prime_support N a hsupp) hfactor

/-- **The sixth-moment level-set bound on a symmetric range, prime-supported coefficients.** -/
theorem volume_largeValues_sixth_symm_le_of_prime_support (N : ℕ) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 6 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 2 * ((T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
          * (9 * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3)) := by
  have hV3 : (0 : ℝ) ≤ V ^ 3 := by positivity
  have hbase := volume_largeValues_symm_le (N ^ 3) (convCube N a) hT hV3
  rw [largeValues_cube_setOf N a (Set.Icc (-T) T) hV] at hbase
  have hpow : (V ^ 3) ^ 2 = V ^ 6 := by ring
  rw [hpow] at hbase
  refine le_trans hbase ?_
  have hlogN3 : (0 : ℝ) ≤ Real.log ((N ^ 3 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ 3) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ 3 := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)) := by nlinarith
  have hstep := mul_le_mul_of_nonneg_left
    (sum_normSq_convCube_le_of_prime_support N a hsupp) hfactor
  linarith

end RHTower.Sieve
