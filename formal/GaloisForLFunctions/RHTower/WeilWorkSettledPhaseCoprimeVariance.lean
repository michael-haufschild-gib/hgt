import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeCovariance

/-!
# A common residual-variance budget for all finite coprime masks

The final theorem has only the original full-positivity premise. Residues and
the logarithmic variance are produced for the actual forward source.
-/

open Complex Filter Finset
open scoped Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

private theorem summable_centered_source {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => sourceCoeff lam n - sourceCompletion hW 1) (s : ℂ) := by
  have hc : LSeriesSummable (fun _ : ℕ => sourceCompletion hW 1) (s : ℂ) := by
    have he : (sourceCompletion hW 1) • (1 : ℕ → ℂ) =
        fun _ : ℕ => sourceCompletion hW 1 := by ext n; simp
    rw [← he]
    exact (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs)).smul _
  exact (sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1.sub hc

private theorem centered_source_residue {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => sourceCoeff lam n - sourceCompletion hW 1) (s : ℂ))
      (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
  let B := sourceCompletion hW 1
  have ht := (forward_source_residue hW).sub (constant_one_residue.const_mul B)
  simp only [mul_one] at ht
  change Tendsto _ _ (𝓝 (B - B)) at ht
  rw [sub_self] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have he : (fun n => sourceCoeff lam n - B) = sourceCoeff lam - B • (1 : ℕ → ℂ) := by
    ext n; simp
  rw [he, LSeries_sub (sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1
    ((LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs)).smul B), LSeries_smul]
  ring

private theorem centered_coprime_source_residue {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] {r : ℝ}
    (hr : Tendsto (fun s : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (s : ℂ) /
      LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r : ℂ))) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (coprimePart Q (fun n => sourceCoeff lam n - sourceCompletion hW 1)) (s : ℂ))
      (𝓝[>] 1) (𝓝 (sourceCompletion hW 1 * ((r - coprimeDensity Q : ℝ) : ℂ))) := by
  let B := sourceCompletion hW 1
  have ha : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (coprimePart Q (sourceCoeff lam)) (s : ℂ))
      (𝓝[>] 1) (𝓝 ((r : ℂ) * B)) := by
    apply (hr.mul (forward_source_residue hW)).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : LSeries (sourceCoeff lam) (s : ℂ) ≠ 0 := by
      rw [(sourceCoeff_LSeries hW (s := (s : ℂ)) hs).2, IntegerMassRigidity.zetaOf]
      exact Complex.exp_ne_zero _
    field_simp [hn]
  have ht := ha.sub ((coprimePart_one_residue Q).const_mul B)
  have he : (r : ℂ) * B - B * (coprimeDensity Q : ℂ) =
      B * ((r - coprimeDensity Q : ℝ) : ℂ) := by push_cast; ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hec : coprimePart Q (fun n => sourceCoeff lam n - B) =
      coprimePart Q (sourceCoeff lam) - B • coprimePart Q 1 := by
    ext n
    simp only [coprimePart, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    ring
  rw [hec, LSeries_sub (summable_coprimePart Q
    (sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1)
    ((summable_coprimePart Q
      (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs))).smul B), LSeries_smul]
  ring

/-- Every finite coprime combination is charged to one actual source variance. -/
theorem exists_forward_coprime_covariance {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ (V : ℝ) (r : ℕ → ℝ), 0 ≤ V ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N,
        ‖sourceCoeff lam n - sourceCompletion hW 1‖ ^ 2 / n) / Real.log N)
        atTop (𝓝 V) ∧
      (∀ Q : ℕ, Q ≠ 0 → 0 < r Q ∧
        Tendsto (fun s : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r Q : ℂ))) ∧
      ∀ (S : Finset ℕ), (∀ Q ∈ S, Q ≠ 0) → ∀ c : ℕ → ℝ,
        ‖sourceCompletion hW 1‖ ^ 2 *
          (∑ Q ∈ S, c Q * (r Q - coprimeDensity Q)) ^ 2 ≤
        V * ∑ Q ∈ S, ∑ R ∈ S, c Q * c R *
          (coprimeDensity (Q * R) - coprimeDensity Q * coprimeDensity R) := by
  classical
  obtain ⟨_, V, _, hV0, _, _, hV⟩ := exists_forwardCoeff_energy_variance hW
  simp only [forwardCoeff_eq_sourceCoeff] at hV
  have hex (Q : ℕ) : ∃ r : ℝ, Q ≠ 0 → 0 < r ∧
      Tendsto (fun s : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r : ℂ)) := by
    by_cases hQ : Q = 0
    · exact ⟨0, fun h => (h hQ).elim⟩
    haveI : NeZero Q := ⟨hQ⟩
    obtain ⟨r, _, _, hr, _, _, hRatio, _⟩ := exists_coprime_source_ratio_limit hW Q
    exact ⟨r, fun _ => ⟨hr, hRatio⟩⟩
  choose r hr using hex
  refine ⟨V, r, hV0, hV, hr, ?_⟩
  intro S hS c
  let B := sourceCompletion hW 1
  let f : ℕ → ℂ := fun n => sourceCoeff lam n - B
  let b : ℝ := -(∑ Q ∈ S, c Q * coprimeDensity Q)
  have he : Tendsto (fun N : ℕ =>
      weightPartialSum (fun n => ‖f n‖ ^ 2 / n) N / Real.log N) atTop (𝓝 V) := by
    apply hV.congr
    intro N
    congr 1
    unfold weightPartialSum
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hn).2⟩
    · intro n hn hn'
      have hn0 : n = 0 := by
        have := Finset.mem_Icc.mp hn
        by_contra hn0
        exact hn' (Finset.mem_Icc.mpr ⟨by omega, this.2⟩)
      simp [hn0]
  have hR := coprimeAffineMask_residue S id c b
    (fun _ hs => summable_centered_source hW hs) (centered_source_residue hW)
    (fun Q hQ => by
      haveI : NeZero Q := ⟨hS Q hQ⟩
      exact centered_coprime_source_residue hW Q (hr Q (hS Q hQ)).2)
  have hlim : ((b : ℂ) * 0 + ∑ Q ∈ S,
      (c Q : ℂ) * (B * ((r Q - coprimeDensity Q : ℝ) : ℂ))) =
      B * ((∑ Q ∈ S, c Q * (r Q - coprimeDensity Q) : ℝ) : ℂ) := by
    simp only [mul_zero, zero_add, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q _
    ring
  rw [hlim] at hR
  have hb := norm_masked_residue_sq_le_log_energy hV0 he
    (fun s hs => summable_coprimeAffineMask_mul S id c b (summable_centered_source hW hs))
    (fun s hs => summable_coprimeAffineMask_square S id c b hs)
    (coprimeAffineMask_square_residue S id hS c b) hR
  have hD : coprimeAffineSquareDensity S id c b =
      ∑ Q ∈ S, ∑ R ∈ S, c Q * c R *
        (coprimeDensity (Q * R) - coprimeDensity Q * coprimeDensity R) :=
    coprimeAffineSquareDensity_centered S id c
  rw [hD, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
  exact hb

end RHTower.WeilSingularArithmetic
