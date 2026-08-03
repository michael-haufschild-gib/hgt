import GaloisForLFunctions.RHTower.Sieve.FareySet

/-!
# The dual large sieve for separated frequencies

`LargeSieveExplicit.lean` develops the Bessel form.  The bilinear form of `LargeSieveWeak.lean`
carries the same admissible `Δ`, so the whole chain — separation, chord bound, circle row sum,
harmonic bound — applies verbatim and gives

`‖∑_r c_r e(λ_r)‖² ≤ (N + δ^{-1}(1 + log((2δ)^{-1} + 1))) ∑_r |c_r|²`

for frequencies `δ`-separated in `ℝ/ℤ`.  Read in coordinates this is a bound on the mean square of a
sum of exponentials over `n < N`, which is the shape the Halász–Montgomery argument consumes.

The two ingredients the bilinear form needs — nontriviality of the correlations and the row bound —
are isolated here so both forms rest on the same statements.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Distinct separated frequencies have nontrivial correlation. -/
theorem circleFreq_corr_ne_one {ι : Type*} (s : Finset ι) (lam : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a)) :
    ∀ r ∈ s, ∀ t ∈ s, r ≠ t →
      (starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) ≠ 1 := by
  intro r hr t ht hrt hcon
  have hs := hsep r hr t ht hrt
  have hchord := four_mul_toIntDist_le_norm_sub (lam r) (lam t)
  rw [hcon, sub_self, norm_zero] at hchord
  linarith

/-- The Gram row of a separated family of circle frequencies. -/
theorem circleFreq_row_le {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (lam : ι → ℝ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a))
    {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ)) :
    ∀ r ∈ s, (N : ℝ)
      + ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
      ≤ (N : ℝ) + (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
  intro r hr
  have hterm : ∀ t ∈ s.erase r,
      2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
        ≤ (1 / 2) * (1 / toIntDist (lam t - lam r)) := by
    intro t ht
    have ht' := Finset.mem_erase.mp ht
    have hsep' := hsep r hr t ht'.2 (Ne.symm ht'.1)
    have hchord := four_mul_toIntDist_le_norm_sub (lam r) (lam t)
    have hpos : (0 : ℝ) < 4 * toIntDist (lam t - lam r) := by linarith
    have hstep : 2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
        ≤ 2 / (4 * toIntDist (lam t - lam r)) := by gcongr
    have hval : 2 / (4 * toIntDist (lam t - lam r))
        = (1 / 2) * (1 / toIntDist (lam t - lam r)) := by
      rw [div_mul_eq_div_div_swap]
      ring
    rw [hval] at hstep
    exact hstep
  have hrow := circle_row_sum_le s lam hδ0 hδ hsep (r := r) hr (M := M) hM
  have hchain : ∑ t ∈ s.erase r,
      2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
        ≤ (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
    calc ∑ t ∈ s.erase r,
          2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
        ≤ ∑ t ∈ s.erase r, (1 / 2) * (1 / toIntDist (lam t - lam r)) :=
          Finset.sum_le_sum hterm
      _ = (1 / 2) * ∑ t ∈ s.erase r, 1 / toIntDist (lam t - lam r) := by rw [Finset.mul_sum]
      _ ≤ (1 / 2) * ((2 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hrow (by norm_num)
      _ = (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by ring
  linarith

/-- **Dual large sieve for separated frequencies.** -/
theorem largeSieve_separated_bilinear {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι)
    (lam : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a))
    (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • expRow N (circleFreq (lam r))‖ ^ 2
      ≤ ((N : ℝ) + (1 / δ) * (1 + Real.log (1 / (2 * δ) + 1))) * ∑ r ∈ s, ‖c r‖ ^ 2 := by
  have hx : (0 : ℝ) < 1 / (2 * δ) := by positivity
  set M : ℕ := ⌈1 / (2 * δ)⌉₊ with hMdef
  have hM : 1 / (2 * δ) ≤ (M : ℝ) := Nat.le_ceil _
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hx hM
  have hMlt : (M : ℝ) < 1 / (2 * δ) + 1 := Nat.ceil_lt_add_one (le_of_lt hx)
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have hΔ : ∀ r ∈ s, (N : ℝ)
      + ∑ t ∈ s.erase r, 2 / ‖(starRingEnd ℂ) (circleFreq (lam r)) * circleFreq (lam t) - 1‖
      ≤ (N : ℝ) + (1 / δ) * (1 + Real.log (1 / (2 * δ) + 1)) := by
    intro r hr
    have h1 := circleFreq_row_le N s lam hδ0 hδ hsep hM r hr
    have h2 : ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ≤ 1 + Real.log M :=
      sum_Icc_one_div_le_one_add_log M
    have h3 : Real.log M ≤ Real.log (1 / (2 * δ) + 1) :=
      Real.log_le_log hMpos (le_of_lt hMlt)
    have h5 : ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ≤ 1 + Real.log (1 / (2 * δ) + 1) := by
      linarith
    have h4 := mul_le_mul_of_nonneg_left h5 hδinv
    linarith
  exact largeSieve_bilinear N s (fun r => circleFreq (lam r))
    (fun r _ => norm_circleFreq _) (circleFreq_corr_ne_one s lam hδ0 hsep) hΔ c

/-- The bilinear form in coordinates: a mean square over `n < N`. -/
theorem norm_sq_sum_smul_expRow {ι : Type*} (N : ℕ) (s : Finset ι) (ξ : ι → ℂ) (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • expRow N (ξ r)‖ ^ 2
      = ∑ n : Fin N, ‖∑ r ∈ s, c r * (ξ r) ^ (n : ℕ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have happ : (∑ r ∈ s, c r • expRow N (ξ r)) n = ∑ r ∈ s, c r * (ξ r) ^ (n : ℕ) := by
    simp [expRow]
  rw [happ]

/-- Farey fractions of order `Q` are `Q^{-2}`-separated on the circle. -/
theorem fareySet_sep {Q : ℕ} :
    ∀ p ∈ fareySet Q, ∀ r ∈ fareySet Q, p ≠ r →
      1 / (Q : ℝ) ^ 2 ≤ toIntDist ((r.1 : ℝ) / (r.2 : ℝ) - (p.1 : ℝ) / (p.2 : ℝ)) := by
  intro p hp r hr hpr
  obtain ⟨⟨hp1, _⟩, ⟨hp2, hpQ⟩, hple, hpc⟩ := mem_fareySet.mp hp
  obtain ⟨⟨hr1, _⟩, ⟨hr2, hrQ⟩, hrle, hrc⟩ := mem_fareySet.mp hr
  have hne : (r.1, r.2) ≠ (p.1, p.2) := by simpa using (Ne.symm hpr)
  have hcross := not_dvd_farey_cross hr2 hp2 hr1 hrle hp1 hple hrc hpc hne
  have hfarey := one_div_le_toIntDist_farey (q := r.2) (q' := p.2) hr2 hp2
    (a := (r.1 : ℤ)) (a' := (p.1 : ℤ)) hcross
  have hp2R : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hp2
  have hr2R : (0 : ℝ) < (r.2 : ℝ) := by exact_mod_cast hr2
  have hpb : (p.2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpQ
  have hrb : (r.2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrQ
  have hprod : (r.2 : ℝ) * (p.2 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hmono : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((r.2 : ℝ) * (p.2 : ℝ)) := by gcongr
  refine le_trans hmono (le_trans hfarey (le_of_eq ?_))
  congr 1

/-- **Dual large sieve on the Farey set of order `Q`.**  A mean square over `n < N`. -/
theorem largeSieve_dual_fareySet (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (b : ℕ × ℕ → ℂ) :
    ∑ n : Fin N, ‖∑ p ∈ fareySet Q, b p * (circleFreq ((p.1 : ℝ) / (p.2 : ℝ))) ^ (n : ℕ)‖ ^ 2
      ≤ ((N : ℝ) + (Q : ℝ) ^ 2 * (1 + Real.log ((Q : ℝ) ^ 2 / 2 + 1)))
          * ∑ p ∈ fareySet Q, ‖b p‖ ^ 2 := by
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hδ0 : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hδ : 1 / (Q : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hQR]
  have hbase := largeSieve_separated_bilinear (δ := 1 / (Q : ℝ) ^ 2) N (fareySet Q)
    (fun p => (p.1 : ℝ) / (p.2 : ℝ)) hδ0 hδ fareySet_sep b
  rw [norm_sq_sum_smul_expRow] at hbase
  have e1 : (1 : ℝ) / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by field_simp
  have e2 : (1 : ℝ) / (2 * (1 / (Q : ℝ) ^ 2)) = (Q : ℝ) ^ 2 / 2 := by
    rw [mul_one_div, one_div_div]
  rw [e1, e2] at hbase
  exact hbase

end RHTower.Sieve
