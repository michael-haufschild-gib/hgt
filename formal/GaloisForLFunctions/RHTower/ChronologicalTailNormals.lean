import GaloisForLFunctions.RHTower.ChronologicalTailHeatVectors
import GaloisForLFunctions.RHTower.ChronologicalTailProjectionPerturbation

/-!
# The critical normal and its discrete approximations

Let `g₁, …, g_l` be Lipschitz on `[θ, 1]` with linearly independent restrictions, `W` the complex
span of their tail heat vectors `F_{g_i}` and `W_N` the span of the discrete tails `F_{g_i,N}`.
For `Re ρ = 1/2`:

* the unit normal `ψ` of the critical vector `K_ρ` against `W` satisfies `ψ ⊥ W` and
  `⟪ψ, K_ρ⟫ = dist(K_ρ, W) > 0`;
* for all large `N` there is a unit vector `ψ_N ⊥ W_N` with `‖ψ_N - ψ‖ ≤ C/N`.

The second statement combines the `O(1/N)` Riemann estimate with the lower frame bound of the
linearly independent limit family.
-/

open MeasureTheory Set Filter

noncomputable section

namespace RHTower

/-- The residual of `v` against `W` realises the distance from `v` to `W`. -/
theorem orthoDefect_eq_infDist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] (v : E) :
    orthoDefect W v = Metric.infDist v (W : Set E) := by
  rw [orthoDefect, Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

/-- **The critical normal and its discrete approximations.** -/
theorem exists_tail_normals {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    {l : ℕ} {g : Fin l → ℝ → ℝ} {K : Fin l → NNReal}
    (hg : ∀ i, LipschitzOnWith (K i) (g i) (Icc θ 1))
    (hind : ∀ c : Fin l → ℝ, (∀ x ∈ Icc θ 1, ∑ i, c i * g i x = 0) → c = 0) :
    ∃ ψ : SampleSpace, ‖ψ‖ = 1 ∧ (∀ i, (inner ℂ ψ (tailVec θ (g i)) : ℂ) = 0) ∧
      (inner ℂ ψ (critVec θ ρ) : ℂ) =
        ((Metric.infDist (critVec θ ρ)
          (Submodule.span ℂ (Set.range fun i => tailVec θ (g i)) : Set SampleSpace) : ℝ) : ℂ) ∧
      0 < Metric.infDist (critVec θ ρ)
          (Submodule.span ℂ (Set.range fun i => tailVec θ (g i)) : Set SampleSpace) ∧
      ∃ C : ℝ, ∃ N₁ : ℕ, 0 < N₁ ∧ ∀ N : ℕ, N₁ ≤ N → ∃ ψN : SampleSpace, ‖ψN‖ = 1 ∧
        (∀ i, (inner ℂ ψN (tailSampleVec θ N (g i)) : ℂ) = 0) ∧ ‖ψN - ψ‖ ≤ C / N := by
  set e : Fin l → SampleSpace := fun i => tailVec θ (g i) with he
  set W : Submodule ℂ SampleSpace := Submodule.span ℂ (Set.range e) with hW
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  have hcont : ∀ i, ContinuousOn (g i) (Icc θ 1) := fun i => (hg i).continuousOn
  have hK : critVec θ ρ ∉ W := critVec_not_mem_span hθ0 hθ1 hρ hcont
  set ψ := unitNormal W (critVec θ ρ) with hψdef
  have hψ1 : ‖ψ‖ = 1 := norm_unitNormal hK
  have hψe : ∀ i, (inner ℂ ψ (e i) : ℂ) = 0 := fun i =>
    unitNormal_inner_eq_zero _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨ψ, hψ1, hψe, ?_, ?_, ?_⟩
  · rw [inner_unitNormal_self hK, orthoDefect_eq_infDist]
  · rw [← orthoDefect_eq_infDist]; exact orthoDefect_pos hK
  -- the frame bound and the Riemann rates
  obtain ⟨lam, hlam, hframe⟩ :=
    exists_frame_lower_bound (linearIndependent_tailVec hθ0 hθ1 hcont hind)
  choose Cr hCr using fun i => exists_norm_tailSampleVec_sub_tailVec_le hθ0 hθ1 (hg i)
  set Cs : ℝ := ∑ i, |Cr i| with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCle : ∀ i, Cr i ≤ Cs := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (Cr j)) (Finset.mem_univ i))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 * l * Cs / lam)
  refine ⟨4 * l * Cs / lam, N₁ + 1, Nat.succ_pos _, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_pos N₁).trans_le hN
  have hNbig : 4 * l * Cs / lam < N := hN₁.trans (by exact_mod_cast Nat.lt_of_succ_le hN)
  set ε : ℝ := Cs / N with hε
  have hε0 : 0 ≤ ε := div_nonneg hCs0 hNpos.le
  have hclose : ∀ i, ‖tailSampleVec θ N (g i) - e i‖ ≤ ε := fun i =>
    (hCr i N (by exact_mod_cast hNpos)).trans (div_le_div_of_nonneg_right (hCle i) hNpos.le)
  have hlε : 4 * (l * ε) ≤ lam := by
    have h := (div_lt_iff₀ hlam).mp hNbig
    rw [hε, ← mul_div_assoc, ← mul_div_assoc, div_le_iff₀ hNpos]
    nlinarith
  have hsmall : l * ε ≤ lam / 2 := by nlinarith [mul_nonneg (Nat.cast_nonneg l) hε0]
  have hframe' := frame_lower_bound_of_perturb hframe hclose hsmall
  set WN : Submodule ℂ SampleSpace :=
    Submodule.span ℂ (Set.range fun i => tailSampleVec θ N (g i)) with hWN
  haveI : FiniteDimensional ℂ WN := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hψe' : ∀ i, (inner ℂ (e i) ψ : ℂ) = 0 := fun i => by
    rw [← inner_conj_symm, hψe i, map_zero]
  have hproj := norm_starProjection_le_of_perturb hlam hε0 hframe' hclose hψe' WN hWN
  rw [hψ1, mul_one] at hproj
  have hη : ‖WN.starProjection ψ‖ < 1 := by
    refine hproj.trans_lt ?_
    rw [div_lt_one hlam]
    nlinarith [mul_nonneg (Nat.cast_nonneg l) hε0]
  obtain ⟨hnot, hdist⟩ := norm_unitNormal_sub_le hψ1 hη
  refine ⟨unitNormal WN ψ, norm_unitNormal hnot, fun i =>
    unitNormal_inner_eq_zero _ (Submodule.subset_span ⟨i, rfl⟩), hdist.trans ?_⟩
  calc 2 * ‖WN.starProjection ψ‖ ≤ 2 * (2 * l * ε / lam) := by linarith
    _ = 4 * l * Cs / lam / N := by rw [hε]; field_simp; ring

end RHTower
