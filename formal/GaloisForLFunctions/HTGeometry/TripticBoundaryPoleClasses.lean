import GaloisForLFunctions.HTGeometry.TripticLineFiniteness
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentOrderVanishing
import GaloisForLFunctions.HTGeometry.TripticGermConstraint

/-!
# The boundary function of a mixed-constraint source has finitely many pole classes

For a `1`-periodic meromorphic function with constant mixed second difference, the `σ`-boundary
function `Δ_σ F` is exactly `1`-periodic and changes by a constant under a `τ`-step.  A constant
does not move any Laurent coefficient of negative index, so the pole set of `Δ_σ F` is invariant
under the whole lattice `ℤ + ℤτ`, and a meromorphic function has finitely many poles in a compact
fundamental parallelogram.

This is the finiteness that bounds the orbital divisor of a general source: only finitely many
cosets of `ℤ + ℤτ` carry poles at all.

* `pole_invariant_zsmul` — a translation invariance of the negative Laurent coefficients invariates
  the pole set under the whole cyclic group it generates;
* `exists_finset_boundaryPoleClasses`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Pole invariance propagates along the cyclic group of a translation.** -/
theorem pole_invariant_zsmul {U : ℂ → ℂ} {w : ℂ} (hU : MeromorphicOn U (Set.univ : Set ℂ))
    (hinv : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ, laurentCoeff U (z + w) ℓ = laurentCoeff U z ℓ)
    (k : ℤ) {z : ℂ} (hz : meromorphicOrderAt U z < 0) :
    meromorphicOrderAt U (z + (k : ℂ) * w) < 0 := by
  have hinv' : ∀ ℓ : ℤ, ℓ < 0 → ∀ y : ℂ, laurentCoeff U (y + -w) ℓ = laurentCoeff U y ℓ := by
    intro ℓ hℓ y
    have h := hinv ℓ hℓ (y + -w)
    rw [show y + -w + w = y by ring] at h
    exact h.symm
  induction k using Int.induction_on with
  | zero => simpa using hz
  | succ n ih =>
      rw [show ((((n : ℤ) + 1 : ℤ)) : ℂ) = ((n : ℤ) : ℂ) + 1 by push_cast; ring,
        show z + (((n : ℤ) : ℂ) + 1) * w = (z + ((n : ℤ) : ℂ) * w) + w by ring]
      exact pole_invariant_of_laurentCoeff_invariant hU hinv ih
  | pred n ih =>
      rw [show ((((-(n : ℤ) - 1 : ℤ)) : ℂ)) = ((-(n : ℤ) : ℤ) : ℂ) - 1 by push_cast; ring,
        show z + (((-(n : ℤ) : ℤ) : ℂ) - 1) * w = (z + ((-(n : ℤ) : ℤ) : ℂ) * w) + -w by ring]
      exact pole_invariant_of_laurentCoeff_invariant hU hinv' ih

/-- **Coefficient invariance propagates along the cyclic group of a translation.** -/
theorem laurentCoeff_invariant_zsmul {U : ℂ → ℂ} {w : ℂ}
    (hinv : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ, laurentCoeff U (z + w) ℓ = laurentCoeff U z ℓ)
    (k : ℤ) {ℓ : ℤ} (hℓ : ℓ < 0) (z : ℂ) :
    laurentCoeff U (z + (k : ℂ) * w) ℓ = laurentCoeff U z ℓ := by
  have hinv' : ∀ ℓ : ℤ, ℓ < 0 → ∀ y : ℂ, laurentCoeff U (y + -w) ℓ = laurentCoeff U y ℓ := by
    intro ℓ' hℓ' y
    have h := hinv ℓ' hℓ' (y + -w)
    rw [show y + -w + w = y by ring] at h
    exact h.symm
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [show ((((n : ℤ) + 1 : ℤ)) : ℂ) = ((n : ℤ) : ℂ) + 1 by push_cast; ring,
        show z + (((n : ℤ) : ℂ) + 1) * w = (z + ((n : ℤ) : ℂ) * w) + w by ring,
        hinv ℓ hℓ, ih]
  | pred n ih =>
      rw [show ((((-(n : ℤ) - 1 : ℤ)) : ℂ)) = ((-(n : ℤ) : ℤ) : ℂ) - 1 by push_cast; ring,
        show z + (((-(n : ℤ) : ℤ) : ℂ) - 1) * w = (z + ((-(n : ℤ) : ℤ) : ℂ) * w) + -w by ring,
        hinv' ℓ hℓ, ih]

/-- **The boundary function of a mixed-constraint source has finitely many pole classes.** -/
theorem exists_finset_boundaryPoleClasses {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) :
    ∃ P : Finset ℂ, ∀ z : ℂ,
      meromorphicOrderAt (fun w ↦ F (w + σ) - F w) z < 0 →
        ∃ m n : ℤ, z - (m • (1 : ℂ) + n • τ) ∈ P := by
  set U : ℂ → ℂ := fun w ↦ F (w + σ) - F w with hUdef
  have hUmero : MeromorphicOn U (Set.univ : Set ℂ) := fun z _ ↦
    (meromorphicAt_comp_add.mpr (hF (z + σ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  -- germ `1`-periodicity
  have hU1 : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ, laurentCoeff U (z + 1) ℓ = laurentCoeff U z ℓ := by
    intro ℓ _ z
    have hmero : MeromorphicAt (fun w ↦ U (w + 1)) z :=
      meromorphicAt_comp_add.mpr (hUmero (z + 1) (Set.mem_univ _))
    calc laurentCoeff U (z + 1) ℓ
        = laurentCoeff (fun w ↦ U (w + 1)) z ℓ := (laurentCoeff_comp_add U z 1 ℓ).symm
      _ = laurentCoeff U z ℓ :=
          laurentCoeff_congr hmero (eventuallyEq_boundary_shift_one hper σ z) ℓ
  -- a `τ`-step changes it by the mixed constant
  have hUτ : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ, laurentCoeff U (z + τ) ℓ = laurentCoeff U z ℓ := by
    intro ℓ hℓ z
    have hmero : MeromorphicAt (fun w ↦ U (w + τ)) z :=
      meromorphicAt_comp_add.mpr (hUmero (z + τ) (Set.mem_univ _))
    calc laurentCoeff U (z + τ) ℓ
        = laurentCoeff (fun w ↦ U (w + τ)) z ℓ := (laurentCoeff_comp_add U z τ ℓ).symm
      _ = laurentCoeff (fun w ↦ U w + Cst) z ℓ :=
          laurentCoeff_congr hmero (eventuallyEq_boundary_shift_tau hmixed z) ℓ
      _ = laurentCoeff U z ℓ := laurentCoeff_add_const (hUmero z (Set.mem_univ z)) Cst hℓ
  -- hence the pole set is invariant under the whole lattice
  have hinv : ∀ (m n : ℤ) (z : ℂ), meromorphicOrderAt U z < 0 →
      meromorphicOrderAt U (z - (m • (1 : ℂ) + n • τ)) < 0 := by
    intro m n z hz
    have h1 : meromorphicOrderAt U (z + ((-m : ℤ) : ℂ) * 1) < 0 :=
      pole_invariant_zsmul hUmero hU1 (-m) hz
    have h2 : meromorphicOrderAt U ((z + ((-m : ℤ) : ℂ) * 1) + ((-n : ℤ) : ℂ) * τ) < 0 :=
      pole_invariant_zsmul hUmero hUτ (-n) h1
    have hpt : (z + ((-m : ℤ) : ℂ) * 1) + ((-n : ℤ) : ℂ) * τ
        = z - (m • (1 : ℂ) + n • τ) := by
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rwa [hpt] at h2
  exact exists_finset_pole_classes hUmero hindepτ hinv

/-- **The orders of the boundary function are bounded below.**  Its poles lie on finitely many
lattice cosets and its Laurent coefficients are lattice invariant, so one bound taken over a finite
set of representatives works at every point of the plane. -/
theorem exists_orderBound_boundary {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) :
    ∃ L : ℤ, ∀ (z : ℂ) (ℓ : ℤ), ℓ < L →
      laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ = 0 := by
  classical
  set U : ℂ → ℂ := fun w ↦ F (w + σ) - F w with hUdef
  have hUmero : MeromorphicOn U (Set.univ : Set ℂ) := fun z _ ↦
    (meromorphicAt_comp_add.mpr (hF (z + σ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  have hU1 : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ, laurentCoeff U (z + 1) ℓ = laurentCoeff U z ℓ := by
    intro ℓ _ z
    have hmero : MeromorphicAt (fun w ↦ U (w + 1)) z :=
      meromorphicAt_comp_add.mpr (hUmero (z + 1) (Set.mem_univ _))
    calc laurentCoeff U (z + 1) ℓ
        = laurentCoeff (fun w ↦ U (w + 1)) z ℓ := (laurentCoeff_comp_add U z 1 ℓ).symm
      _ = laurentCoeff U z ℓ :=
          laurentCoeff_congr hmero (eventuallyEq_boundary_shift_one hper σ z) ℓ
  have hUτ : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ, laurentCoeff U (z + τ) ℓ = laurentCoeff U z ℓ := by
    intro ℓ hℓ z
    have hmero : MeromorphicAt (fun w ↦ U (w + τ)) z :=
      meromorphicAt_comp_add.mpr (hUmero (z + τ) (Set.mem_univ _))
    calc laurentCoeff U (z + τ) ℓ
        = laurentCoeff (fun w ↦ U (w + τ)) z ℓ := (laurentCoeff_comp_add U z τ ℓ).symm
      _ = laurentCoeff (fun w ↦ U w + Cst) z ℓ :=
          laurentCoeff_congr hmero (eventuallyEq_boundary_shift_tau hmixed z) ℓ
      _ = laurentCoeff U z ℓ := laurentCoeff_add_const (hUmero z (Set.mem_univ z)) Cst hℓ
  obtain ⟨P, hP⟩ := exists_finset_boundaryPoleClasses hF hper hmixed hindepτ
  set Lq : ℂ → ℤ := fun q ↦ (meromorphicOrderAt U q).untop₀ with hLq
  set S : Finset ℤ := insert (0 : ℤ) (P.image Lq) with hS
  have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hSne, fun z ℓ hℓ ↦ ?_⟩
  have hℓ0 : ℓ < 0 := lt_of_lt_of_le hℓ (S.min'_le 0 (Finset.mem_insert_self _ _))
  have hvanish : ∀ q : ℂ, ℓ < Lq q → laurentCoeff U q ℓ = 0 := by
    intro q hq
    refine laurentCoeff_eq_zero_of_lt_meromorphicOrderAt (hUmero q (Set.mem_univ q)) ?_
    rcases eq_or_ne (meromorphicOrderAt U q) ⊤ with htop | htop
    · rw [htop]
      exact WithTop.coe_lt_top ℓ
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hn]
      have hun : (meromorphicOrderAt U q).untop₀ = n := by
        rw [← hn]
        simp
      have hq' : ℓ < n := by simpa [hLq, hun] using hq
      exact_mod_cast hq'
  rcases lt_or_ge (meromorphicOrderAt U z) 0 with hpole | hreg
  · obtain ⟨m, n, hmem⟩ := hP z hpole
    have hshift : laurentCoeff U (z - (m • (1 : ℂ) + n • τ)) ℓ = laurentCoeff U z ℓ := by
      have h1 := laurentCoeff_invariant_zsmul hU1 (-m) hℓ0 z
      have h2 := laurentCoeff_invariant_zsmul hUτ (-n) hℓ0 (z + ((-m : ℤ) : ℂ) * 1)
      have hpt : (z + ((-m : ℤ) : ℂ) * 1) + ((-n : ℤ) : ℂ) * τ
          = z - (m • (1 : ℂ) + n • τ) := by
        simp only [zsmul_eq_mul]
        push_cast
        ring
      rw [hpt] at h2
      rw [h2, h1]
    rw [← hshift]
    refine hvanish _ (lt_of_lt_of_le hℓ (S.min'_le _ ?_))
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem Lq hmem)
  · exact laurentCoeff_eq_zero_of_meromorphicOrderAt_nonneg (hUmero z (Set.mem_univ z)) hreg hℓ0

end

end GaloisForLFunctions.HTGeometry
