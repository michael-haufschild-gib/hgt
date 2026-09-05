/-
# The determinant-defect completion law `(DC)`

The closure of the finite-rank determinant graph over the Schatten `p`-class, taken in the product
of the Schatten topology and the compact-open topology, is exactly the set of pairs
`(A, exp(Q)·det_p(1 − zA))` with `Q` a jet of degree below `p` and vanishing constant term.  The
inclusion `⊆` is the normalized-logarithm argument run against the Weierstrass convergence theorem;
the inclusion `⊇` is the vanishing micro-spectrum construction placed beside a greedy truncation.
Both halves are unconditional.

Main results:
* `DetGraphClosure` — membership in the closure of the finite-rank determinant graph.
* `DetCompletionFibre` — the completion fibre presentation.
* `detGraphClosure_eq_detCompletionFibre` — **`(DC)`: the two sets are equal**.
-/
import GaloisForLFunctions.HTGeometry.OperatorDeterminantUniform

open Filter Topology Metric ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A pair of a Schatten-`p` operator and a function lies in the **closure of the finite-rank
determinant graph** when some finite-rank sequence converges to the operator in the Schatten norm
with plain determinants converging locally uniformly to the function on a disc about the origin. -/
def DetGraphClosure (p : ℕ) : Set ((H →L[ℂ] H) × (ℂ → ℂ)) :=
  {q | MemSchattenClass (p : ℝ) q.1 ∧ ∃ (A : ℕ → H →L[ℂ] H) (r : ℝ), 0 < r ∧
      (∀ n, ∃ N : ℕ, HasRankLE (A n) N) ∧
      Tendsto (fun n => schattenNorm (p : ℝ) (A n - q.1)) atTop (nhds 0) ∧
      TendstoLocallyUniformlyOn (fun n z => opSchattenDet 1 (A n) z) q.2 atTop
        (ball (0 : ℂ) r)}

/-- The **completion fibre presentation**: the order-`p` regularized determinant times the
exponential of a jet of degree below `p` with vanishing constant term. -/
def DetCompletionFibre (p : ℕ) : Set ((H →L[ℂ] H) × (ℂ → ℂ)) :=
  {q | MemSchattenClass (p : ℝ) q.1 ∧ ∃ (Q : Polynomial ℂ) (r : ℝ), 0 < r ∧
      Q.natDegree ≤ p - 1 ∧ Q.coeff 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) r,
        q.2 z = opSchattenDet p q.1 z * Complex.exp (Polynomial.eval z Q)}

variable {H}

/-- **`(DC)`, the determinant-defect completion law.**  On an infinite-dimensional Hilbert space the
closure of the finite-rank determinant graph over the Schatten `p`-class is exactly the completion
fibre: the regularized determinant times the exponential of a jet of degree below `p` with vanishing
constant term. -/
theorem detGraphClosure_eq_detCompletionFibre (hH : ¬ FiniteDimensional ℂ H) {p : ℕ} (hp : 0 < p) :
    DetGraphClosure H p = DetCompletionFibre H p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  apply Set.eq_of_subset_of_subset
  · -- necessity
    rintro ⟨T, F⟩ ⟨hT, A, r, hr0, hArank, hDtend, hFlu⟩
    refine ⟨hT, ?_⟩
    have hAmem : ∀ n, MemSchattenClass (p : ℝ) (A n) := by
      intro n
      obtain ⟨N, hN⟩ := hArank n
      exact memSchattenClass_of_hasRankLE hpR hN
    have hDmem : ∀ n, MemSchattenClass (p : ℝ) (A n - T) := by
      intro n
      rw [sub_eq_add_neg]
      exact memSchattenClass_add hpR (hAmem n) (memSchattenClass_neg hT)
    obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ n, schattenNorm (p : ℝ) (A n - T) ≤ C₀ := by
      obtain ⟨C₀, hC₀⟩ := hDtend.bddAbove_range
      exact ⟨C₀, fun n => hC₀ ⟨n, rfl⟩⟩
    have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans (schattenNorm_nonneg _ _) (hC₀ 0)
    obtain ⟨K, hK⟩ : ∃ K : ℝ,
        K = 2 ^ ((p : ℝ) + 1) * (C₀ ^ (p : ℝ) + schattenNorm (p : ℝ) T ^ (p : ℝ)) := ⟨_, rfl⟩
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ,
        C = max 1 (max (K ^ (1 / (p : ℝ))) (schattenNorm (p : ℝ) T)) := ⟨_, rfl⟩
    have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
    have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
    have hCT : schattenNorm (p : ℝ) T ≤ C := by
      rw [hCdef]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have htwo : (0 : ℝ) ≤ 2 ^ ((p : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
    have hCA : ∀ n, schattenNorm (p : ℝ) (A n) ≤ C := by
      intro n
      have hsplit : schattenNorm (p : ℝ) (A n) ^ (p : ℝ)
          ≤ 2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) (A n - T) ^ (p : ℝ)
            + schattenNorm (p : ℝ) T ^ (p : ℝ)) := by
        have h := schattenNorm_add_rpow_le hpR (hDmem n) hT
        rwa [show A n - T + T = A n by abel] at h
      have hmono : schattenNorm (p : ℝ) (A n - T) ^ (p : ℝ) ≤ C₀ ^ (p : ℝ) :=
        Real.rpow_le_rpow (schattenNorm_nonneg _ _) (hC₀ n) hpR.le
      have hAK : schattenNorm (p : ℝ) (A n) ^ (p : ℝ) ≤ K := by
        rw [hK]
        nlinarith [hsplit, hmono, htwo]
      have hnn : (0 : ℝ) ≤ schattenNorm (p : ℝ) (A n) := schattenNorm_nonneg _ _
      calc schattenNorm (p : ℝ) (A n)
          = (schattenNorm (p : ℝ) (A n) ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
            rw [← Real.rpow_mul hnn, mul_one_div, div_self hpR.ne', Real.rpow_one]
        _ ≤ K ^ (1 / (p : ℝ)) := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hAK (by positivity)
        _ ≤ C := by rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    obtain ⟨r₁, hr₁def⟩ : ∃ r₁ : ℝ, r₁ = min r (1 / (4 * C)) := ⟨_, rfl⟩
    have hr₁0 : 0 < r₁ := by rw [hr₁def]; exact lt_min hr0 (by positivity)
    have hr₁r : r₁ ≤ r := by rw [hr₁def]; exact min_le_left _ _
    have hr₁B : r₁ * (2 * C) < 1 := by
      have h1 : r₁ ≤ 1 / (4 * C) := by rw [hr₁def]; exact min_le_right _ _
      have h2 : r₁ * (2 * C) ≤ (1 / (4 * C)) * (2 * C) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      have h3 : (1 / (4 * C)) * (2 * C) = 1 / 2 := by field_simp; ring
      rw [h3] at h2
      linarith
    obtain ⟨ρ, Q, hρ0, hρr, hQdeg, hQ0, hQval⟩ :=
      exists_poly_of_tendstoLocallyUniformlyOn_opSchattenDet hp hAmem hT hDmem hC1 hCA hCT
        hDtend hr₁0 hr₁B (hFlu.mono (ball_subset_ball hr₁r))
    exact ⟨Q, ρ, hρ0, hQdeg, hQ0, hQval⟩
  · -- sufficiency
    rintro ⟨T, F⟩ ⟨hT, Q, r, hr0, hQdeg, hQ0, hQval⟩
    refine ⟨hT, ?_⟩
    obtain ⟨Fam, r', hr'0, hFamrank, hFamtend, hFamlu⟩ :=
      exists_finiteRank_tendstoLocallyUniformlyOn_opSchattenDet_one hH hp hT hQdeg hQ0
    obtain ⟨r₂, hr₂def⟩ : ∃ r₂ : ℝ, r₂ = min r r' := ⟨_, rfl⟩
    have hr₂0 : 0 < r₂ := by rw [hr₂def]; exact lt_min hr0 hr'0
    have hr₂r : r₂ ≤ r := by rw [hr₂def]; exact min_le_left _ _
    have hr₂r' : r₂ ≤ r' := by rw [hr₂def]; exact min_le_right _ _
    refine ⟨Fam, r₂, hr₂0, hFamrank, hFamtend, ?_⟩
    refine (hFamlu.mono (ball_subset_ball hr₂r')).congr_right ?_
    intro z hz
    exact (hQval z (ball_subset_ball hr₂r hz)).symm

end

end GaloisForLFunctions.HTGeometry
