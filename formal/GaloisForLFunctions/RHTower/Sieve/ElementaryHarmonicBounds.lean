import GaloisForLFunctions.RHTower.PrimeMassLowerBound
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.AuxResults

/-!
# Elementary harmonic and square-root sums

The unsigned estimates behind the Route E cofactor card's `(7)` and `(9)`: a two-sided comparison
for `∑_{n ≤ M} n^{-1/2}`, the reindexing of a divisibility-restricted sum, the resulting bounds for
the mass carried by the multiples of a fixed modulus, and the convergence of the reciprocal squares
of the odd numbers above one, with the explicit constant `1/4` that the squarefree extraction needs.

Everything is proved by telescoping; no analytic input is used.  The upper bound
`∑_{n ≤ M} n^{-1/2} ≤ 2√M` is already in the corpus as `RHTower.sum_one_div_sqrt_le` and is reused.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The square-root harmonic sum from below.**  `2√(M+1) − 2 ≤ ∑_{n ≤ M} n^{-1/2}`. -/
theorem two_mul_sqrt_succ_sub_two_le_sum (M : ℕ) :
    2 * Real.sqrt ((M : ℝ) + 1) - 2 ≤ ∑ n ∈ Finset.Icc 1 M, 1 / Real.sqrt (n : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hv : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
    have hw : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 2) := Real.sqrt_nonneg _
    have hv2 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hw2 : Real.sqrt ((m : ℝ) + 2) ^ 2 = (m : ℝ) + 2 := Real.sq_sqrt (by positivity)
    have hv1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by nlinarith [hv, hv2]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast, show ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 from by ring]
    have hstep : 2 * Real.sqrt ((m : ℝ) + 2) - 2 * Real.sqrt ((m : ℝ) + 1)
        ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg (Real.sqrt ((m : ℝ) + 2) - Real.sqrt ((m : ℝ) + 1)), hv2, hw2]
    linarith [ih, hstep]

/-- The multiples of `p` below `M`, reindexed by their cofactor. -/
theorem sum_filter_dvd_eq {M p : ℕ} (hp : 1 ≤ p) (f : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), f n
      = ∑ k ∈ Finset.Icc 1 (M / p), f (p * k) := by
  classical
  have hp0 : 0 < p := hp
  have himg : (Finset.Icc 1 M).filter (fun n => p ∣ n)
      = (Finset.Icc 1 (M / p)).image (fun k => p * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h1
        · exact hk
      · exact (Nat.le_div_iff_mul_le hp0).2 (by rw [Nat.mul_comm]; exact h2)
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.2 (by positivity)
      · have hkp := (Nat.le_div_iff_mul_le hp0).1 hk2
        rw [Nat.mul_comm]
        exact hkp
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hp0 hab

/-- **The square-root mass of the multiples of `p`.** -/
theorem sum_inv_sqrt_dvd_le {M p : ℕ} (hp : 1 ≤ p) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), 1 / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt (M : ℝ) / (p : ℝ) := by
  classical
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsp : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp0
  rw [sum_filter_dvd_eq hp (fun n => 1 / Real.sqrt (n : ℝ))]
  have hterm : ∀ k ∈ Finset.Icc 1 (M / p),
      1 / Real.sqrt ((p * k : ℕ) : ℝ) = (1 / Real.sqrt (p : ℝ)) * (1 / Real.sqrt (k : ℝ)) := by
    intro k _
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbase : ∑ k ∈ Finset.Icc 1 (M / p), 1 / Real.sqrt (k : ℝ)
      ≤ 2 * Real.sqrt ((M / p : ℕ) : ℝ) := sum_one_div_sqrt_le (M / p)
  have hdiv : ((M / p : ℕ) : ℝ) ≤ (M : ℝ) / (p : ℝ) := Nat.cast_div_le
  have hsq : Real.sqrt ((M / p : ℕ) : ℝ) ≤ Real.sqrt (M : ℝ) / Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_div' _ (le_of_lt hp0)] at *
    exact Real.sqrt_le_sqrt hdiv
  have hstep : (1 / Real.sqrt (p : ℝ)) * ∑ k ∈ Finset.Icc 1 (M / p), 1 / Real.sqrt (k : ℝ)
      ≤ (1 / Real.sqrt (p : ℝ)) * (2 * (Real.sqrt (M : ℝ) / Real.sqrt (p : ℝ))) := by
    refine mul_le_mul_of_nonneg_left (le_trans hbase ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  refine le_trans hstep (le_of_eq ?_)
  have hsp2 : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
    Real.mul_self_sqrt hp0.le
  field_simp
  nlinarith [hsp2, Real.sqrt_nonneg (M : ℝ)]

/-- **The harmonic mass of the multiples of `p`.** -/
theorem sum_inv_dvd_le {M p : ℕ} (hp : 1 ≤ p) (hM : 1 ≤ M) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), 1 / (n : ℝ)
      ≤ (1 + Real.log (M : ℝ)) / (p : ℝ) := by
  classical
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  rw [sum_filter_dvd_eq hp (fun n => 1 / (n : ℝ))]
  rcases Nat.eq_zero_or_pos (M / p) with hzero | hpos
  · rw [hzero, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hterm : ∀ k ∈ Finset.Icc 1 (M / p),
        1 / ((p * k : ℕ) : ℝ) = (1 / (p : ℝ)) * (1 / (k : ℝ)) := by
      intro k _
      rw [Nat.cast_mul]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hbase : ∑ k ∈ Finset.Icc 1 (M / p), 1 / (k : ℝ)
        ≤ 1 + Real.log ((M / p : ℕ) : ℝ) := by
      have := Aux.sum_inv_le_log (M / p) hpos
      simpa [one_div] using this
    have hmono : Real.log ((M / p : ℕ) : ℝ) ≤ Real.log (M : ℝ) := by
      refine Real.log_le_log (by exact_mod_cast hpos) ?_
      exact_mod_cast Nat.div_le_self M p
    have hchain : ∑ k ∈ Finset.Icc 1 (M / p), 1 / (k : ℝ) ≤ 1 + Real.log (M : ℝ) := by
      linarith [hbase, hmono]
    have hgoal : (1 / (p : ℝ)) * ∑ k ∈ Finset.Icc 1 (M / p), 1 / (k : ℝ)
        ≤ (1 / (p : ℝ)) * (1 + Real.log (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hchain (by positivity)
    have heq : (1 / (p : ℝ)) * (1 + Real.log (M : ℝ)) = (1 + Real.log (M : ℝ)) / (p : ℝ) := by
      field_simp
    linarith [hgoal, heq.le, heq.ge]

/-- The telescoping sum `∑_{1 ≤ j ≤ J} (1/j − 1/(j+1)) = 1 − 1/(J+1)`. -/
theorem sum_telescope_inv (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) = 1 - 1 / ((J : ℝ) + 1) := by
  induction J with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hm1 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast, show ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 from by ring]
    field_simp
    ring

/-- **The reciprocal squares of the odd numbers above one sum to at most `1/4`.** -/
theorem sum_inv_sq_odd_le {s : Finset ℕ} (hs : ∀ d ∈ s, 3 ≤ d ∧ ¬ 2 ∣ d) :
    ∑ d ∈ s, 1 / ((d : ℝ)) ^ 2 ≤ 1 / 4 := by
  classical
  set t : Finset ℕ := s.image (fun d => (d - 1) / 2) with ht
  have hrec : ∀ d ∈ s, 2 * ((d - 1) / 2) + 1 = d := by
    intro d hd
    obtain ⟨h3, hodd⟩ := hs d hd
    omega
  have hinj : Set.InjOn (fun d => (d - 1) / 2) s := by
    intro a ha b hb hab
    have h1 := hrec a ha
    have h2 := hrec b hb
    simp only at hab
    omega
  have hmapped : ∑ d ∈ s, 1 / ((d : ℝ)) ^ 2
      = ∑ j ∈ t, 1 / (((2 * j + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [ht, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hrec d hd]
  set J : ℕ := s.sup id with hJ
  have hsubset : t ⊆ Finset.Icc 1 J := by
    intro j hj
    rw [ht, Finset.mem_image] at hj
    obtain ⟨d, hd, rfl⟩ := hj
    obtain ⟨h3, hodd⟩ := hs d hd
    have hdJ : d ≤ J := Finset.le_sup (f := id) hd
    rw [Finset.mem_Icc]
    omega
  have hterm : ∀ j ∈ Finset.Icc 1 J,
      1 / (((2 * j + 1 : ℕ) : ℝ)) ^ 2 ≤ (1 / 4) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
    have hcast : (((2 * j + 1 : ℕ)) : ℝ) = 2 * (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    rw [div_le_iff₀ (by positivity)]
    have hexpand : (1 / 4 : ℝ) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) * (2 * (j : ℝ) + 1) ^ 2
        = (2 * (j : ℝ) + 1) ^ 2 / (4 * (j : ℝ) * ((j : ℝ) + 1)) := by
      field_simp
      ring
    rw [hexpand, le_div_iff₀ (by positivity)]
    nlinarith [hj0]
  have hnn : ∀ j ∈ Finset.Icc 1 J, (0 : ℝ) ≤ (1 / 4) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
    have : 1 / ((j : ℝ) + 1) ≤ 1 / (j : ℝ) :=
      one_div_le_one_div_of_le hj0 (by linarith)
    linarith
  have hstep : ∑ j ∈ t, 1 / (((2 * j + 1 : ℕ) : ℝ)) ^ 2
      ≤ ∑ j ∈ Finset.Icc 1 J, (1 / 4) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) := by
    refine le_trans (Finset.sum_le_sum (fun j hj => hterm j (hsubset hj))) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j hj _ => hnn j hj)
  have hval : ∑ j ∈ Finset.Icc 1 J, (1 / 4 : ℝ) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))
      = (1 / 4) * (1 - 1 / ((J : ℝ) + 1)) := by
    rw [← Finset.mul_sum, sum_telescope_inv]
  have hle : (1 / 4 : ℝ) * (1 - 1 / ((J : ℝ) + 1)) ≤ 1 / 4 := by
    have : (0 : ℝ) < (J : ℝ) + 1 := by positivity
    have h1 : (0 : ℝ) < 1 / ((J : ℝ) + 1) := by positivity
    nlinarith [h1]
  rw [hmapped]
  linarith [hstep, hval.le, hval.ge, hle]

end

end RHTower.Sieve
