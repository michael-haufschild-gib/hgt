import GaloisForLFunctions.HTGeometry.GeometricPolynomialFaceGap
import GaloisForLFunctions.HTGeometry.PolynomialTaylorProuhetPhaseLock

/-!
# Vanishing of the normalized least geometric ADE face
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries MvPolynomial Topology

noncomputable section

/-- The normalized least-face cluster, before replacing intrinsic phases by a prescribed phase
sequence. -/
def normalizedGeometricPolynomialFaceCluster
    (F : PowerSeries ℂ) (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (M : ℕ)
    (A lam c₀ : ℝ) (c : ℕ → ℝ) (t : ℕ) : ℂ :=
  ∑ p ∈ geometricPolynomialPatternFace n D K τ Q M lam,
    normalizedGeometricPolynomialFaceWeight n D K τ Q M lam c₀ c t p *
      normalizedAtomPhase F (fun i => A * lam ^ i + c i)
        (shiftedAtomPatternKey (t + K) K p)

/-- The exact coefficient identity and the unconditional geometric face gap force the normalized
least-face cluster to converge to zero. -/
theorem exists_normalizedGeometricPolynomialFaceCluster_tendsto_zero
    {A lam c₀ : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds c₀))
    (hbpos : ∀ i, 0 < A * lam ^ i + c i)
    (hgrowth : UniformGeometricGrowth (fun i => A * lam ^ i + c i))
    {n D K₀ τ M₀ : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(A * lam ^ i + c i)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    ∃ K M : ℕ,
      (polynomialPatternSurvivors n D K τ Q M).Nonempty ∧
      Tendsto (normalizedGeometricPolynomialFaceCluster F n D K τ Q M A lam c₀ c)
        atTop (nhds 0) := by
  classical
  obtain ⟨K, M, hS, γ, hγ, hgap⟩ :=
    exists_geometricPolynomialFace_activeAtom_gap hA hlam hc hbpos hgrowth Q hD hDmax
      p₀ hcount₀ hw₀
  let S := polynomialPatternSurvivors n D K τ Q M
  let Face := geometricPolynomialPatternFace n D K τ Q M lam
  let H := geometricPolynomialFaceWeightDegree n D K τ Q M lam
  obtain ⟨P, hmass⟩ := exists_aevalWeight_mass_natPow_bound n D τ Q
  have hmassT := (tendsto_add_atTop_nat K).eventually hmass
  have hactiveT := (tendsto_add_atTop_nat K).eventually
    (polynomialPatternSurvivors_eventually_weight_ne_zero
      (n := n) (D := D) (K := K) (τ := τ) (M := M) Q)
  have hdecay := tendsto_natAdd_pow_mul_exp_neg_geometric hlam hγ K P
  have hbound : ∀ᶠ t : ℕ in atTop,
      ‖normalizedGeometricPolynomialFaceCluster F n D K τ Q M A lam c₀ c t‖ ≤
        (((t + K : ℕ) : ℝ) ^ P) * Real.exp (-γ * lam ^ t) := by
    filter_upwards [hmassT, hactiveT, hgap, eventually_ge_atTop 1] with
      t hmassq hactiveq hgapq ht
    let q := t + K
    let T := activeAevalAtoms n (D * q + τ) Q
    let Ckey := Face.image (shiftedAtomPatternKey q K)
    let m := geometricPolynomialFaceBaseline n D K τ Q M A lam c₀ t
    let den : ℂ := ((q : ℕ) : ℂ) ^ H
    have hden : 1 ≤ ‖den‖ := by
      dsimp [den]
      rw [norm_pow, Complex.norm_natCast]
      exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ q by dsimp [q]; omega))
    have hCkeyT : Ckey ⊆ T := by
      intro ν hν
      obtain ⟨p, hpFace, rfl⟩ := Finset.mem_image.mp hν
      have hpS : p ∈ S := (mem_geometricPatternFace_iff.mp hpFace).1
      have hw := hactiveq p hpS
      rw [mem_activeAevalAtoms]
      exact ⟨mem_appearingAtoms_of_aevalWeight_ne_zero hw, hw⟩
    let fraw : (ℕ →₀ ℕ) → ℂ := fun ν =>
      aevalWeight n (D * q + τ) Q ν *
        (Real.exp (-(atomValuation (fun i => A * lam ^ i + c i) ν - m)) : ℂ) *
          normalizedAtomPhase F (fun i => A * lam ^ i + c i) ν
    let fscaled : (ℕ →₀ ℕ) → ℂ := fun ν =>
      (aevalWeight n (D * q + τ) Q ν / den) *
        (Real.exp (-(atomValuation (fun i => A * lam ^ i + c i) ν - m)) : ℂ) *
          normalizedAtomPhase F (fun i => A * lam ^ i + c i) ν
    have hzeroRaw : ∑ ν ∈ T, fraw ν = 0 := by
      simpa [T, fraw, q, m] using normalized_active_aeval_coefficient_identity
        n (D * q + τ) F Q (fun i => A * lam ^ i + c i) hrel m
    have hzero : ∑ ν ∈ T, fscaled ν = 0 := by
      calc
        ∑ ν ∈ T, fscaled ν = (∑ ν ∈ T, fraw ν) / den := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro ν hν
          dsimp [fscaled, fraw]
          ring
        _ = 0 := by rw [hzeroRaw, zero_div]
    have hbalance : ∑ ν ∈ Ckey, fscaled ν =
        -∑ ν ∈ T \ Ckey, fscaled ν :=
      normalized_cluster_balance_of_identity T Ckey hCkeyT fscaled hzero
    have hphase : ∀ ν ∈ T,
        ‖normalizedAtomPhase F (fun i => A * lam ^ i + c i) ν‖ ≤ 1 := by
      intro ν hν
      rw [norm_normalizedAtomPhase F (fun i => A * lam ^ i + c i) hb ν]
    have hmassScaled :
        (∑ ν ∈ T, ‖aevalWeight n (D * q + τ) Q ν / den‖) ≤
          (q : ℝ) ^ P := by
      calc
        (∑ ν ∈ T, ‖aevalWeight n (D * q + τ) Q ν / den‖) =
            (∑ ν ∈ T, ‖aevalWeight n (D * q + τ) Q ν‖) / ‖den‖ := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro ν hν
          rw [norm_div]
        _ ≤ ∑ ν ∈ T, ‖aevalWeight n (D * q + τ) Q ν‖ :=
          div_le_self (by positivity) hden
        _ ≤ (q : ℝ) ^ P := by simpa [T, q] using hmassq
    have hcluster := norm_cluster_sum_le_mass_mul_exp_neg_gap T Ckey hCkeyT
      (fun ν => aevalWeight n (D * q + τ) Q ν / den)
      (fun ν => normalizedAtomPhase F (fun i => A * lam ^ i + c i) ν)
      (fun ν => atomValuation (fun i => A * lam ^ i + c i) ν)
      m (γ * lam ^ t) ((q : ℝ) ^ P)
      (by simpa [fscaled] using hbalance) hphase
      (by simpa [T, Ckey, q, m] using hgapq) hmassScaled
    rw [sum_image_shiftedAtomPatternKey Face (fun ν =>
      (aevalWeight n (D * q + τ) Q ν / den) *
        (Real.exp (-(atomValuation (fun i => A * lam ^ i + c i) ν - m)) : ℂ) *
          normalizedAtomPhase F (fun i => A * lam ^ i + c i) ν)] at hcluster
    have hfaceEq :
        (∑ p ∈ Face,
          (aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) / den) *
            (Real.exp (-(atomValuation (fun i => A * lam ^ i + c i)
              (shiftedAtomPatternKey q K p) - m)) : ℂ) *
              normalizedAtomPhase F (fun i => A * lam ^ i + c i)
                (shiftedAtomPatternKey q K p)) =
          normalizedGeometricPolynomialFaceCluster F n D K τ Q M A lam c₀ c t := by
      rw [normalizedGeometricPolynomialFaceCluster]
      apply Finset.sum_congr rfl
      intro p hp
      have hpval := (mem_geometricPatternFace_iff.mp hp).2
      rw [atomValuation_shiftedAtomPatternKey_geometric A lam c q K p]
      dsimp [normalizedGeometricPolynomialFaceWeight, den, H, m,
        geometricPolynomialFaceBaseline, Face, S, q]
      rw [Nat.add_sub_cancel, hpval]
      push_cast
      ring
    rw [hfaceEq] at hcluster
    simpa [q] using hcluster
  refine ⟨K, M, hS, ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t => norm_nonneg _
  · exact hbound
  · exact hdecay

end

end GaloisForLFunctions
