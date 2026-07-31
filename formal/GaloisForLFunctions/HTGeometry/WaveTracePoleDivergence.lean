import GaloisForLFunctions.HTGeometry.WaveTracePoleTransform

/-!
# Reinforcement of residues at an active resolvent pole

Frequencies sharing a square contribute identical resolvent terms: the trace coefficient and
the phase numerator each change sign under `gamma ↦ -gamma`, so their product is invariant.
Therefore the residues of a common pole reinforce and can never cancel, and the pole of an
active frequency is genuine.

At the pole the phase numerator collapses to the frequency itself, which is nonzero, so the
head of the series is an honest simple pole while the remaining terms stay bounded.
-/

open Complex Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

namespace WaveSpectrum

noncomputable section

variable {G : Type*} (S : WaveSpectrum G)

/-- Locally finite frequency divisor: only finitely many frequencies in any bounded region. -/
def IsLocallyFiniteSpectrum : Prop := ∀ R : ℝ, {g : G | ‖S.gamma g‖ ≤ R}.Finite

/-- Frequencies sharing their square with a given one. -/
def squareFiber (g₀ : G) : Set G := {g | S.gamma g ^ 2 = S.gamma g₀ ^ 2}

theorem norm_eq_of_mem_squareFiber {g₀ g : G} (hg : g ∈ S.squareFiber g₀) :
    ‖S.gamma g‖ = ‖S.gamma g₀‖ := by
  have hsq : ‖S.gamma g‖ ^ 2 = ‖S.gamma g₀‖ ^ 2 := by
    rw [← norm_pow, ← norm_pow]
    exact congrArg norm hg
  have h1 : (0 : ℝ) ≤ ‖S.gamma g‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖S.gamma g₀‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

theorem squareFiber_finite (hlf : S.IsLocallyFiniteSpectrum) (g₀ : G) :
    (S.squareFiber g₀).Finite :=
  Set.Finite.subset (hlf ‖S.gamma g₀‖) fun _ hg => le_of_eq (S.norm_eq_of_mem_squareFiber hg)

theorem gamma_eq_or_eq_neg_of_mem_squareFiber {g₀ g : G} (hg : g ∈ S.squareFiber g₀) :
    S.gamma g = S.gamma g₀ ∨ S.gamma g = -S.gamma g₀ := by
  have hfac : (S.gamma g - S.gamma g₀) * (S.gamma g + S.gamma g₀) = 0 := by
    have : S.gamma g ^ 2 = S.gamma g₀ ^ 2 := hg
    linear_combination this
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

/-- **Square separation.** A locally finite divisor keeps every other frequency square at a
positive distance from a given one. -/
theorem exists_square_separation (hlf : S.IsLocallyFiniteSpectrum) (g₀ : G) :
    ∃ d : ℝ, 0 < d ∧
      ∀ g : G, g ∉ S.squareFiber g₀ → d ≤ ‖S.gamma g ^ 2 - S.gamma g₀ ^ 2‖ := by
  classical
  set R : ℝ := ‖S.gamma g₀‖ + 1 with hR
  set F : Finset G := (hlf R).toFinset with hF
  set Fbad : Finset G := F.filter (fun g => S.gamma g ^ 2 ≠ S.gamma g₀ ^ 2) with hFbad
  have hfar : ∀ g : G, R < ‖S.gamma g‖ → (1 : ℝ) ≤ ‖S.gamma g ^ 2 - S.gamma g₀ ^ 2‖ := by
    intro g hg
    have h1 : ‖S.gamma g₀‖ + 1 < ‖S.gamma g‖ := hg
    have h2 : (0 : ℝ) ≤ ‖S.gamma g₀‖ := norm_nonneg _
    have hlow : ‖S.gamma g₀‖ ^ 2 + 1 ≤ ‖S.gamma g‖ ^ 2 := by nlinarith
    have hge : ‖S.gamma g‖ ^ 2 - ‖S.gamma g₀‖ ^ 2 ≤ ‖S.gamma g ^ 2 - S.gamma g₀ ^ 2‖ := by
      have := norm_sub_norm_le (S.gamma g ^ 2) (S.gamma g₀ ^ 2)
      rwa [norm_pow, norm_pow] at this
    linarith
  by_cases hne : Fbad.Nonempty
  · set d0 : ℝ := Fbad.inf' hne (fun g => ‖S.gamma g ^ 2 - S.gamma g₀ ^ 2‖) with hd0
    have hd0pos : 0 < d0 := by
      rw [hd0, Finset.lt_inf'_iff]
      intro g hg
      have hgne : S.gamma g ^ 2 ≠ S.gamma g₀ ^ 2 := (Finset.mem_filter.mp hg).2
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hgne)
    refine ⟨min d0 1, lt_min hd0pos one_pos, fun g hg => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · have hmemF : g ∈ F := by
        rw [hF, Set.Finite.mem_toFinset]
        exact hsmall
      have hmem : g ∈ Fbad := Finset.mem_filter.mpr ⟨hmemF, hg⟩
      exact le_trans (min_le_left _ _) (Finset.inf'_le _ hmem)
    · exact le_trans (min_le_right _ _) (hfar g (lt_of_not_ge hsmall))
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · exfalso
      have hmemF : g ∈ F := by
        rw [hF, Set.Finite.mem_toFinset]
        exact hsmall
      exact hne ⟨g, Finset.mem_filter.mpr ⟨hmemF, hg⟩⟩
    · exact hfar g (lt_of_not_ge hsmall)

/-! ## Reinforcement of residues -/

variable {S}

/-- The phase numerator collapses to the frequency itself at its own resolvent pole. -/
theorem poleNumer_at_pole (T : ℝ) (g : G) :
    S.poleNumer T (Complex.I * S.gamma g) g = S.gamma g := by
  rw [poleNumer]
  have hEuler : Complex.cos (S.gamma g * (T : ℂ)) +
      Complex.sin (S.gamma g * (T : ℂ)) * Complex.I =
      Complex.exp (S.gamma g * (T : ℂ) * Complex.I) := (Complex.exp_mul_I _).symm
  have hrw : Complex.I * S.gamma g * Complex.sin (S.gamma g * (T : ℂ)) +
      S.gamma g * Complex.cos (S.gamma g * (T : ℂ)) =
      S.gamma g * Complex.exp (S.gamma g * (T : ℂ) * Complex.I) := by
    rw [← hEuler]; ring
  rw [hrw]
  rw [← mul_assoc, mul_comm (Complex.exp (-(Complex.I * S.gamma g) * (T : ℂ))) (S.gamma g),
    mul_assoc, ← Complex.exp_add]
  rw [show -(Complex.I * S.gamma g) * (T : ℂ) + S.gamma g * (T : ℂ) * Complex.I = 0 by ring]
  simp

/-- Frequencies of the same square contribute identical resolvent numerators: both factors
change sign together, so residues reinforce. -/
theorem traceCoeff_mul_poleNumer_eq_of_mem_squareFiber (P : Polynomial ℝ) (T : ℝ) (s : ℂ)
    {g₀ g : G} (hg : g ∈ S.squareFiber g₀) :
    S.traceCoeff P g * S.poleNumer T s g = S.traceCoeff P g₀ * S.poleNumer T s g₀ := by
  have hsq : S.gamma g ^ 2 = S.gamma g₀ ^ 2 := hg
  rcases S.gamma_eq_or_eq_neg_of_mem_squareFiber hg with hgamma | hgamma
  · rw [traceCoeff, traceCoeff, poleNumer, poleNumer, hgamma]
  · have hcoeff : S.traceCoeff P g = -S.traceCoeff P g₀ := by
      rw [traceCoeff, traceCoeff, hsq, hgamma]
      ring
    have hnumer : S.poleNumer T s g = -S.poleNumer T s g₀ := by
      rw [poleNumer, poleNumer, hgamma]
      rw [show -S.gamma g₀ * (T : ℂ) = -(S.gamma g₀ * (T : ℂ)) by ring,
        Complex.sin_neg, Complex.cos_neg]
      ring
    rw [hcoeff, hnumer]
    ring

end

end WaveSpectrum

end GaloisForLFunctions.HTGeometry
