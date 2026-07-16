import GaloisForLFunctions.HTGeometry.GeometricPolynomialFaceCancellation

/-!
# Torsion-language exclusion of a geometric integer ADE
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries MvPolynomial Topology

noncomputable section

/-- A positive-degree integer ADE with one balanced surviving pattern is incompatible with an
exact geometric magnitude profile and a torsion-language-universal unit phase. -/
theorem no_integerADE_of_geometric_torsionLanguageUniversal
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    {A lam c₀ : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds c₀))
    (hbpos : ∀ i, 0 < A * lam ^ i + c i)
    (hgrowth : UniformGeometricGrowth (fun i => A * lam ^ i + c i))
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(A * lam ^ i + c i)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    (hu : TorsionLanguageUniversal u)
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    False := by
  have hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(A * lam ^ i + c i)) := by
    intro i
    rw [hcoeff, norm_mul, huNorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  obtain ⟨K, M, hS, hcluster⟩ :=
    exists_normalizedGeometricPolynomialFaceCluster_tendsto_zero
      hA hlam hc hbpos hgrowth F hb Q hrel hD hDmax p₀ hcount₀ hw₀
  let Face := geometricPolynomialPatternFace n D K τ Q M lam
  let w : ℕ → (Fin M → Fin (D + 1)) → ℂ := fun t p =>
    normalizedGeometricPolynomialFaceWeight n D K τ Q M lam c₀ c t p
  let ell : (Fin M → Fin (D + 1)) → ℂ := fun p =>
    geometricPolynomialFaceWeightLimit n D K τ Q M lam p
  have hw : ∀ p ∈ Face, Tendsto (fun t => w t p) atTop (nhds (ell p)) := by
    intro p hp
    exact tendsto_normalizedGeometricPolynomialFaceWeight Q hc hp
  have hface : Tendsto (fun t =>
      ∑ p ∈ Face, w t p * ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ))
      atTop (nhds 0) := by
    apply hcluster.congr'
    filter_upwards with t
    rw [normalizedGeometricPolynomialFaceCluster]
    apply Finset.sum_congr rfl
    intro p hp
    rw [normalizedAtomPhase_shiftedAtomPatternKey_eq F
      (fun i => A * lam ^ i + c i) u hcoeff]
    congr 2
    funext r
    rw [windowShift, Nat.add_sub_cancel]
  have hall := face_weights_eq_zero_of_torsionLanguageUniversal u hu Face w ell hw hface
  obtain ⟨p, hp, hpne⟩ :=
    exists_ne_zero_geometricPolynomialFaceWeightLimit Q lam hS
  exact hpne (hall p hp)

end

end GaloisForLFunctions
