import GaloisForLFunctions.RHTower.CHMDCompactOrbitInertia
import GaloisForLFunctions.RHTower.WeilCompactNegativeSubspace

/-!
# Unrestricted finite Xi orbit inertia on actual compact polar tests

Every finite family of distinct nonreal centered-Xi symmetry orbits produces
an equally dimensional complex subspace of actual compact C² polar-zero
tests. Its complete Weil form has a strict ordinary-L2-relative negative gap.
One finite interval supports the entire subspace, hence every larger window
does too. No separation, isolation, visibility, or simple-zero premise occurs.
The support threshold is existential, with no effective bound claimed.
-/

open MeasureTheory Set Complex Zeta23

noncomputable section

namespace RHTower

open CHMDDoobGraph

/-- Unrestricted compact realization of every finite nonreal Xi orbit block,
with exact polar cancellation and no loss of complex dimension. -/
theorem exists_compact_polar_negative_subspace_of_distinct_Xi_orbits
    {k : ℕ} (a : Fin k → ℂ) (ha : ∀ i, 0 < (a i).re)
    (hz : ∀ i, XiC (a i) = 0) (hi : ∀ i, (a i).im ≠ 0)
    (ho : ∀ i j, i ≠ j → a j ∉ cardinalOrbit (a i)) :
    ∃ A : ℝ, 0 < A ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧ Module.finrank ℂ V = k ∧
        (∀ b : ℝ, A ≤ b → ∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-b) b ∧
          paperFT f (I/2) = 0 ∧ paperFT f (-I/2) = 0) ∧
        ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -ε * ∫ x, ‖f x‖^2 := by
  classical
  obtain ⟨q, hq, hpolar, hgram⟩ :=
    exists_compact_polar_negative_gram a ha hz hi ho
  have hv (i : Fin k) : ∃ v hv hc, q i = compactLift v hv hc := hq i
  choose v hv hc he using hv
  let f : Fin k → ℝ → ℝ := fun i => phiDoobTest (v i)
  have hf (i : Fin k) : ContDiff ℝ 2 (f i) := contDiff_phiDoobTest (hv i)
  have hfc (i : Fin k) : HasCompactSupport (f i) := hasCompactSupport_phiDoobTest (hc i)
  have hLift (i : Fin k) : testLift (f i) (hf i) (hfc i) = q i := by
    rw [he i]
    exact testLift_phi (v i) (hv i) (hc i)
  have hp (i : Fin k) : paperFT (fun x => (f i x : ℂ)) (I/2) = 0 ∧
      paperFT (fun x => (f i x : ℂ)) (-I/2) = 0 := by
    have hh := hpolar i
    rw [← hLift i, graphFourierReadout_testLift, graphFourierReadout_testLift] at hh
    exact hh
  have hneg (c : Fin k → ℂ) :
      (zetaZeroConfig.W (fun x => ∑ i, c i * (f i x : ℂ))
        (fun x => ∑ i, c i * (f i x : ℂ))).re ≤ -(1/2 : ℝ)*‖c‖^2 := by
    rw [re_W_compact_synthesis_eq_gram f hf hfc hp c]
    simpa only [hLift] using hgram c
  obtain ⟨A, hA, ε, hε, V, hVfin, hVdim, hVtest, hVneg⟩ :=
    exists_compact_negative_subspace_of_coefficient_gap (fun i x => (f i x : ℂ))
      (fun i => Complex.ofRealCLM.contDiff.comp (hf i))
      (fun i => (hfc i).comp_left Complex.ofReal_zero) hp hneg
  refine ⟨A, hA, ε, hε, V, hVfin, hVdim, ?_, hVneg⟩
  intro b hb f hfV
  obtain ⟨hfd, hfs, hfp, hfm⟩ := hVtest f hfV
  exact ⟨hfd, hfs.trans (Icc_subset_Icc (neg_le_neg hb) hb), hfp, hfm⟩

end RHTower
