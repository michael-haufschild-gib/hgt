import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneral
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

/-!
# Truncating the direct edge of the smooth AFE

The Gaussian cutoff decays faster than any power, so the direct Dirichlet edge of the smooth
approximate functional equation may be truncated at any length with a power-saving error — at *any*
abscissa, the cutoff rather than the exponent supplying the convergence.

Choosing the decay exponent `A` large makes the tail beyond `L` at most `C·x^A·L^{1-σ-A}`, which for
`L` a small power of `x` above `x` itself is negligible.  This is what turns the AFE into an honest
finite Dirichlet polynomial, ready for a mean-value theorem.
-/

open Complex

noncomputable section

namespace RHTower

theorem norm_smoothAFE_term_le {A : ℝ} {K : ℝ}
    (hK : ∀ {v : ℝ}, 0 < v → ‖smoothAFECutoff v‖ ≤ K * v ^ (-A))
    {x : ℝ} (hx : 0 < x) (s : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ‖((n : ℂ)) ^ (-s) * smoothAFECutoff ((n : ℝ) / x)‖
      ≤ (K * x ^ A) * ((n : ℝ)) ^ (-(s.re + A)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : ‖((n : ℂ)) ^ (-s)‖ = ((n : ℝ)) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  have hquot : (0 : ℝ) < (n : ℝ) / x := by positivity
  have hcut : ‖smoothAFECutoff ((n : ℝ) / x)‖ ≤ K * (((n : ℝ)) / x) ^ (-A) := hK hquot
  have hsplit : (((n : ℝ)) / x) ^ (-A) = ((n : ℝ)) ^ (-A) * x ^ A := by
    rw [Real.div_rpow hn0.le hx.le, Real.rpow_neg hx.le]
    field_simp
  rw [norm_mul, hpow]
  calc ((n : ℝ)) ^ (-s.re) * ‖smoothAFECutoff ((n : ℝ) / x)‖
      ≤ ((n : ℝ)) ^ (-s.re) * (K * (((n : ℝ)) ^ (-A) * x ^ A)) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hn0.le _)
    _ = (K * x ^ A) * (((n : ℝ)) ^ (-s.re) * ((n : ℝ)) ^ (-A)) := by ring
    _ = (K * x ^ A) * ((n : ℝ)) ^ (-(s.re + A)) := by
        rw [← Real.rpow_add hn0]
        ring_nf

/-- **The truncated direct edge of the smooth AFE.** -/
theorem exists_smoothAFE_direct_tail_le {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ), 0 < x → 1 < s.re + A → ∀ L : ℕ, 1 ≤ L →
      ∑' j : ℕ, ‖(((j + L + 1 : ℕ) : ℂ)) ^ (-s)
          * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x)‖
        ≤ C * x ^ A * (((L : ℝ)) ^ (1 - (s.re + A)) / (s.re + A - 1)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_smoothAFECutoff_le_neg_rpow hA
  refine ⟨K, hK0, fun s x hx hsA L hL => ?_⟩
  set p : ℝ := s.re + A with hp
  have hp1 : 1 < p := hsA
  have hmaj : Summable (fun j : ℕ => (K * x ^ A) * ((((j + L + 1 : ℕ) : ℝ)) ^ (-p))) := by
    refine Summable.mul_left _ ?_
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-p)) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hshift := (summable_nat_add_iff (L + 1)).mpr hbase
    refine hshift.congr fun n => ?_
    push_cast
    congr 1
    ring
  have hle : ∀ j : ℕ, ‖(((j + L + 1 : ℕ) : ℂ)) ^ (-s)
      * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x)‖
      ≤ (K * x ^ A) * ((((j + L + 1 : ℕ) : ℝ)) ^ (-p)) := by
    intro j
    exact norm_smoothAFE_term_le hK hx s (j + L + 1) (by omega)
  have hsummable := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle hmaj
  calc ∑' j : ℕ, ‖(((j + L + 1 : ℕ) : ℂ)) ^ (-s)
        * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x)‖
      ≤ ∑' j : ℕ, (K * x ^ A) * ((((j + L + 1 : ℕ) : ℝ)) ^ (-p)) :=
        hsummable.tsum_le_tsum hle hmaj
    _ = (K * x ^ A) * ∑' j : ℕ, ((((j + L + 1 : ℕ) : ℝ)) ^ (-p)) := tsum_mul_left
    _ ≤ (K * x ^ A) * (((L : ℝ)) ^ (1 - p) / (p - 1)) := by
        refine mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hp1 hL) ?_
        have : (0 : ℝ) ≤ x ^ A := Real.rpow_nonneg hx.le _
        positivity
    _ = K * x ^ A * (((L : ℝ)) ^ (1 - (s.re + A)) / (s.re + A - 1)) := by rw [hp]

/-- Summability of the direct Gaussian edge at any abscissa. -/
theorem summable_smoothAFE_direct {A : ℝ} (hA : 0 < A) {s : ℂ} {x : ℝ} (hx : 0 < x)
    (hsA : 1 < s.re + A) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℂ)) ^ (-s)
      * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_smoothAFECutoff_le_neg_rpow hA
  set p : ℝ := s.re + A with hp
  have hmaj : Summable (fun n : ℕ => (K * x ^ A) * ((((n + 1 : ℕ) : ℝ)) ^ (-p))) := by
    refine Summable.mul_left _ ?_
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-p)) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hshift := (summable_nat_add_iff 1).mpr hbase
    refine hshift.congr fun n => ?_
    push_cast
    congr 1
  refine Summable.of_norm_bounded hmaj fun n => ?_
  exact norm_smoothAFE_term_le hK hx s (n + 1) (by omega)

/-- **The smooth AFE as a finite Dirichlet polynomial with a power-saving error.**  At any point of
the strip the zeta function is a Dirichlet polynomial of length `L`, minus the reflected edge and
the pole term, up to `C·x^A·L^{1-Re s-A}`. -/
theorem exists_riemannZeta_sub_smoothAFE_head_le {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ) (L : ℕ), 0 < x → s ≠ 1 → 0 < s.re → s.re < 2 →
      1 < s.re + A → 1 ≤ L →
      ‖riemannZeta s
          - ((∑ n ∈ Finset.range L, (((n + 1 : ℕ) : ℂ)) ^ (-s)
                * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))
            - smoothAFEZetaDualMellinGeneral s x
            - smoothAFEZetaShiftedPoleResidue s x)‖
        ≤ C * x ^ A * (((L : ℝ)) ^ (1 - (s.re + A)) / (s.re + A - 1)) := by
  obtain ⟨C, hC0, hC⟩ := exists_smoothAFE_direct_tail_le hA
  refine ⟨C, hC0, fun s x L hx hs hre0 hre2 hsA hL => ?_⟩
  have hsum := summable_smoothAFE_direct hA hx hsA
  have hafe : riemannZeta s =
      (∑' n : ℕ, (((n + 1 : ℕ) : ℂ)) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))
        - smoothAFEZetaDualMellinGeneral s x
        - smoothAFEZetaShiftedPoleResidue s x := by
    rw [riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general hx hs hre0 hre2]
    congr 2
    refine tsum_congr fun n => ?_
    push_cast
    try ring
  have hsplit := hsum.sum_add_tsum_nat_add L
  have hdiff : riemannZeta s
      - ((∑ n ∈ Finset.range L, (((n + 1 : ℕ) : ℂ)) ^ (-s)
            * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))
        - smoothAFEZetaDualMellinGeneral s x
        - smoothAFEZetaShiftedPoleResidue s x)
      = ∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ)) ^ (-s)
          * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x) := by
    rw [hafe, ← hsplit]
    abel
  rw [hdiff]
  have hsummable : Summable (fun j : ℕ => (((j + L + 1 : ℕ) : ℂ)) ^ (-s)
      * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x)) := by
    have h := hsum.comp_injective (add_left_injective L)
    simpa [Function.comp_def] using h
  exact le_trans (norm_tsum_le_tsum_norm hsummable.norm) (hC s x hx hsA L hL)

end RHTower

end
