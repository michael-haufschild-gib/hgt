import GaloisForLFunctions.RHTower.Sieve.TwistedDiagonalSqrtEvaluation

/-!
# The twisted diagonal with cutoffs adapted to the twist

The approximate functional equation for `ζ` holds for every split `2πxy = t` of the archimedean
scale.  Choosing the split *adapted to the twist* `(h,k)`,

```text
x = √( t k / (2π h) ),      y = √( t h / (2π k) ),
```

makes the two cutoffs coincide along the reduced diagonal ray `m = k'd`, `n = h'd`:
`x/k' = y/h' = D`.  The diagonal condition then reads simply `d ≤ D`, and the diagonal sum is a
*complete* harmonic sum up to `D` — no truncation is wasted.

This file evaluates that adapted diagonal:

```text
∑_{m ≤ k'D, n ≤ h'D, nk = mh} (mn)^{-1/2}  =  ((h,k)/√(hk)) · H_D
      =  ((h,k)/√(hk)) · ( log D + γ ) + O( (h,k)/(√(hk) D) ).
```

With `D = √(t(h,k)²/(2πhk))` this is exactly the Balasubramanian--Conrey--Heath-Brown weight
`½ log( t(h,k)²/(2πhk) ) + γ`, whose double integrates to
`T ((h,k)/√(hk)) ( log(T(h,k)²/(2πhk)) + 2γ − 1 )`.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- The diagonal reindexing with independent cutoffs for the two variables. -/
theorem twisted_diagonal_reindex_pair {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M)
    (s t : Finset ℕ) {h k : ℕ} (hk : 1 ≤ k) (hcop : Nat.Coprime h k)
    (D : Finset ℕ) (hD : ∀ d : ℕ, d ∈ D ↔ (k * d ∈ s ∧ h * d ∈ t)) :
    ∑ m ∈ s, ∑ n ∈ t.filter (fun n => n * k = m * h), f m n
      = ∑ d ∈ D, f (k * d) (h * d) := by
  classical
  have hk0 : 0 < k := hk
  have hprod : ∑ m ∈ s, ∑ n ∈ t.filter (fun n => n * k = m * h), f m n
      = ∑ p ∈ (s ×ˢ t).filter (fun p : ℕ × ℕ => p.2 * k = p.1 * h), f p.1 p.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_filter]
  rw [hprod]
  refine (Finset.sum_nbij' (i := fun d => ((k * d, h * d) : ℕ × ℕ))
    (j := fun p : ℕ × ℕ => p.1 / k) ?_ ?_ ?_ ?_ ?_).symm
  · intro d hd
    obtain ⟨h1, h2⟩ := (hD d).mp hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, ?_⟩
    simp only
    ring
  · intro p hp
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hmem
    obtain ⟨he1, he2⟩ := twisted_diagonal_decomp hk0 hcop heq
    refine (hD (p.1 / k)).mpr ⟨?_, ?_⟩
    · rw [← he1]; exact hp1
    · rw [← he2]; exact hp2
  · intro d _
    simp only
    rw [Nat.mul_div_cancel_left _ hk0]
  · intro p hp
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨he1, he2⟩ := twisted_diagonal_decomp hk0 hcop heq
    exact Prod.ext he1.symm he2.symm
  · intro d _
    rfl

/-- The two-cutoff reindexing for arbitrary positive twist indices. -/
theorem twisted_diagonal_reindex_gcd_pair {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M)
    (s t : Finset ℕ) {h k : ℕ} (hk : 1 ≤ k)
    (D : Finset ℕ)
    (hD : ∀ d : ℕ, d ∈ D ↔
      ((k / Nat.gcd h k) * d ∈ s ∧ (h / Nat.gcd h k) * d ∈ t)) :
    ∑ m ∈ s, ∑ n ∈ t.filter (fun n => n * k = m * h), f m n =
      ∑ d ∈ D, f ((k / Nat.gcd h k) * d) ((h / Nat.gcd h k) * d) := by
  classical
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_right h hk0
  have hcop : Nat.Coprime (h / Nat.gcd h k) (k / Nat.gcd h k) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hkred : 1 ≤ k / Nat.gcd h k := by
    apply Nat.one_le_div_iff (by omega) |>.2
    exact Nat.gcd_le_right h (by omega)
  have hfilter : ∀ m : ℕ,
      t.filter (fun n => n * k = m * h) =
        t.filter (fun n => n * (k / Nat.gcd h k) = m * (h / Nat.gcd h k)) := by
    intro m
    apply Finset.filter_congr
    intro n _
    exact twisted_diagonal_eq_reduced_iff hk
  simp_rw [hfilter]
  exact twisted_diagonal_reindex_pair f s t hkred hcop D hD

/-- With cutoffs `k'D` and `h'D` the diagonal range is exactly `1 ≤ d ≤ D`. -/
theorem twistedDiagonalAdapted_membership {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (D d : ℕ) :
    d ∈ Finset.Icc 1 D ↔
      ((k / Nat.gcd h k) * d ∈ Finset.Icc 1 ((k / Nat.gcd h k) * D) ∧
        (h / Nat.gcd h k) * d ∈ Finset.Icc 1 ((h / Nat.gcd h k) * D)) := by
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left k hh
  have hh' : 0 < h / Nat.gcd h k :=
    Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h k)) hg
  have hk' : 0 < k / Nat.gcd h k :=
    Nat.div_pos (Nat.le_of_dvd hk (Nat.gcd_dvd_right h k)) hg
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨hd1, hd2⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hk'.ne' (by omega)),
        Nat.mul_le_mul_left _ hd2⟩,
      ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hh'.ne' (by omega)),
        Nat.mul_le_mul_left _ hd2⟩⟩
  · rintro ⟨⟨hk1, hk2⟩, ⟨_, _⟩⟩
    have hd1 : 1 ≤ d := by
      by_contra hcon
      have hd0 : d = 0 := by omega
      rw [hd0, Nat.mul_zero] at hk1
      omega
    exact ⟨hd1, Nat.le_of_mul_le_mul_left hk2 hk'⟩

/-- **The adapted twisted diagonal is a complete harmonic sum.** -/
theorem twistedDiagonalAdapted_sum_eq {h k : ℕ} (hh : 0 < h) (hk : 1 ≤ k) (D : ℕ) :
    (∑ m ∈ Finset.Icc 1 ((k / Nat.gcd h k) * D),
        ∑ n ∈ (Finset.Icc 1 ((h / Nat.gcd h k) * D)).filter (fun n => n * k = m * h),
        (1 : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) =
      ((Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ))) * (harmonic D : ℝ) := by
  rw [twisted_diagonal_reindex_gcd_pair (fun m n => (1 : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))
    (Finset.Icc 1 ((k / Nat.gcd h k) * D)) (Finset.Icc 1 ((h / Nat.gcd h k) * D)) hk
    (Finset.Icc 1 D) (twistedDiagonalAdapted_membership hh (by omega) D)]
  rw [← sum_Icc_one_div_eq_harmonic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact twistedDiagonalSqrtWeight hh (by omega) (Finset.mem_Icc.mp hd).1

/-- **The adapted diagonal main term, with its explicit error.**  This is the exact
Balasubramanian--Conrey--Heath-Brown weight: no cutoff loss, so the direct diagonal alone carries
the whole main term of the twisted second moment. -/
theorem abs_twistedDiagonalAdapted_sub_main_le {h k : ℕ} (hh : 0 < h) (hk : 1 ≤ k) {D : ℕ}
    (hD : 1 ≤ D) :
    |(∑ m ∈ Finset.Icc 1 ((k / Nat.gcd h k) * D),
          ∑ n ∈ (Finset.Icc 1 ((h / Nat.gcd h k) * D)).filter (fun n => n * k = m * h),
          (1 : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) -
        ((Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ))) *
          (Real.log (D : ℝ) + Real.eulerMascheroniConstant)| ≤
      ((Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ))) * (1 / (D : ℝ)) := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hconst : (0 : ℝ) ≤ (Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ)) := by
    have : (0 : ℝ) < Real.sqrt ((h : ℝ) * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [twistedDiagonalAdapted_sum_eq hh hk D, ← mul_sub, abs_mul, abs_of_nonneg hconst]
  refine mul_le_mul_of_nonneg_left ?_ hconst
  have hsub : (harmonic D : ℝ) - (Real.log (D : ℝ) + Real.eulerMascheroniConstant) =
      (harmonic D : ℝ) - Real.log (D : ℝ) - Real.eulerMascheroniConstant := by ring
  rw [hsub]
  exact HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hD

end RHTower.Sieve
