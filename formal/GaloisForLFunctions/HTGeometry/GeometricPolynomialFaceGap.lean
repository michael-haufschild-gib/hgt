import GaloisForLFunctions.HTGeometry.GeometricProfileAsymptotics

/-!
# Unconditional geometric gap around the least polynomial ADE face

The balanced-survival pattern, generic active-atom confinement, and the finite least-value face
combine to separate every active atom outside that face by a fixed positive multiple of `lam^t`.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries MvPolynomial Topology

noncomputable section

/-- Baseline valuation shared asymptotically by the least geometric survivor face. -/
def geometricPolynomialFaceBaseline
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (M : ℕ)
    (A lam c₀ : ℝ) (t : ℕ) : ℝ :=
  A * lam ^ t * geometricPatternMinimum lam
      (polynomialPatternSurvivors n D K τ Q M) + D * c₀

/-- Every active atom outside the canonical least geometric survivor face has an eventual
exponential valuation gap.  All windows and the gap constant are constructed from one actual
balanced nonzero pattern. -/
theorem exists_geometricPolynomialFace_activeAtom_gap
    {A lam c₀ : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds c₀))
    (hbpos : ∀ i, 0 < A * lam ^ i + c i)
    (hgrowth : UniformGeometricGrowth (fun i => A * lam ^ i + c i))
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    ∃ K M : ℕ,
      let S := polynomialPatternSurvivors n D K τ Q M
      let Face := geometricPatternFace lam S
      S.Nonempty ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ t : ℕ in atTop,
        ∀ ν ∈ activeAevalAtoms n (D * (t + K) + τ) Q \
            Face.image (shiftedAtomPatternKey (t + K) K),
          geometricPolynomialFaceBaseline n D K τ Q M A lam c₀ t +
              γ * lam ^ t ≤
            atomValuation (fun i => A * lam ^ i + c i) ν := by
  classical
  obtain ⟨K, M, hK₀K, hpattern⟩ :=
    exists_eventually_activeAtom_geometricWitness_pattern hbpos hgrowth Q hD hDmax
      p₀ hcount₀
  let S := polynomialPatternSurvivors n D K τ Q M
  let Face := geometricPatternFace lam S
  have hpatternT := (tendsto_add_atTop_nat K).eventually hpattern
  have hw₀T := (tendsto_add_atTop_nat K).eventually hw₀
  have hS_eventual : ∀ᶠ t : ℕ in atTop, S.Nonempty := by
    filter_upwards [hpatternT, hw₀T, eventually_ge_atTop n] with t hpat hw tn
    let q := t + K
    let νw := shiftedAtomPatternKey q K₀ p₀
    have hνw : νw ∈ activeAevalAtoms n (D * q + τ) Q := by
      rw [mem_activeAevalAtoms]
      exact ⟨mem_appearingAtoms_of_aevalWeight_ne_zero hw, hw⟩
    have hnear : atomValuation (fun i => A * lam ^ i + c i) νw <
        atomValuation (fun i => A * lam ^ i + c i) νw +
          (A * lam ^ (q - K₀ + atomPatternMaxOffset p₀ hcount₀) +
            c (q - K₀ + atomPatternMaxOffset p₀ hcount₀)) := by
      exact lt_add_of_pos_right _ (hbpos _)
    obtain ⟨p, hpcount, hpkey⟩ := hpat νw hνw hnear
    have hpweight : aevalWeight n (D * q + τ) Q
        (shiftedAtomPatternKey q K p) ≠ 0 := by
      rw [hpkey]
      simpa [q, νw] using hw
    have hpS : p ∈ S := by
      dsimp [S]
      exact mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpcount
        (by dsimp [q]; omega) hpweight
    exact ⟨p, hpS⟩
  obtain ⟨tS, htS⟩ := hS_eventual.exists
  have hS : S.Nonempty := htS
  obtain ⟨δ, hδ, hfaceGap⟩ := exists_pos_geometricPatternFace_gap lam S hS
  let γ : ℝ := min (A / 4) (A * δ / 2)
  have hγ : 0 < γ := by
    dsimp [γ]
    exact lt_min (by positivity) (by positivity)
  have hremLower : ∀ᶠ t : ℕ in atTop,
      ∀ p ∈ S,
        D * c₀ - 1 < geometricPatternRemainder c (t + K) K p := by
    rw [Finset.eventually_all]
    intro p hpS
    have hpcount : (∑ r, (p r : ℕ)) = D :=
      polynomialPatternSurvivors_count hpS
    have hlim := (tendsto_geometricPatternRemainder hc K p hpcount).comp
      (tendsto_add_atTop_nat K)
    exact (tendsto_order.1 hlim).1 (D * c₀ - 1) (by linarith)
  let C₀ := K - K₀ + atomPatternMaxOffset p₀ hcount₀
  have hcenterLower : ∀ᶠ t : ℕ in atTop,
      A / 2 * lam ^ t ≤
        A * lam ^ (t + C₀) + c (t + C₀) :=
    eventually_geometricProfile_half_lower hA hlam hc C₀
  have honeGlobal := eventually_one_le_mul_geometric hlam
    (show 0 < A / 4 by positivity)
  have honeFace := eventually_one_le_mul_geometric hlam
    (show 0 < A * δ / 2 by positivity)
  refine ⟨K, M, ?_⟩
  dsimp only
  refine ⟨hS, γ, hγ, ?_⟩
  filter_upwards [hpatternT, hw₀T, hremLower, hcenterLower,
    honeGlobal, honeFace, eventually_ge_atTop n] with
      t hpat hw hrem hcenter honeG honeF tn
  intro ν hν
  let q := t + K
  let νw := shiftedAtomPatternKey q K₀ p₀
  have hν_active : ν ∈ activeAevalAtoms n (D * q + τ) Q := by
    simpa [q] using (Finset.mem_sdiff.mp hν).1
  have hν_notFace : ν ∉ Face.image (shiftedAtomPatternKey q K) := by
    simpa [q] using (Finset.mem_sdiff.mp hν).2
  have hνw : νw ∈ activeAevalAtoms n (D * q + τ) Q := by
    rw [mem_activeAevalAtoms]
    exact ⟨mem_appearingAtoms_of_aevalWeight_ne_zero hw, hw⟩
  have hnearw : atomValuation (fun i => A * lam ^ i + c i) νw <
      atomValuation (fun i => A * lam ^ i + c i) νw +
        (A * lam ^ (q - K₀ + atomPatternMaxOffset p₀ hcount₀) +
          c (q - K₀ + atomPatternMaxOffset p₀ hcount₀)) :=
    lt_add_of_pos_right _ (hbpos _)
  obtain ⟨pw, hpwcount, hpwkey⟩ := hpat νw hνw hnearw
  have hpwweight : aevalWeight n (D * q + τ) Q
      (shiftedAtomPatternKey q K pw) ≠ 0 := by
    rw [hpwkey]
    simpa [q, νw] using hw
  have hpwS : pw ∈ S := by
    dsimp [S]
    exact mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpwcount
      (by dsimp [q]; omega) hpwweight
  have hminw := geometricPatternMinimum_le lam S hS hpwS
  have hremw := hrem pw hpwS
  have hwval : atomValuation (fun i => A * lam ^ i + c i) νw =
      A * lam ^ t * geometricPatternValue lam pw +
        geometricPatternRemainder c q K pw := by
    rw [← hpwkey,
      atomValuation_shiftedAtomPatternKey_geometric A lam c q K pw]
    congr 2
    dsimp [q]
    rw [Nat.add_sub_cancel]
  have hwBaseline :
      geometricPolynomialFaceBaseline n D K τ Q M A lam c₀ t - 1 <
        atomValuation (fun i => A * lam ^ i + c i) νw := by
    rw [hwval]
    dsimp [geometricPolynomialFaceBaseline, S]
    have hpow : 0 ≤ A * lam ^ t :=
      mul_nonneg hA.le (pow_nonneg (zero_lt_one.trans hlam).le t)
    have := mul_le_mul_of_nonneg_left hminw hpow
    linarith
  have hcenter' : A / 2 * lam ^ t ≤
      A * lam ^ (q - K₀ + atomPatternMaxOffset p₀ hcount₀) +
        c (q - K₀ + atomPatternMaxOffset p₀ hcount₀) := by
    have hidx : q - K₀ + atomPatternMaxOffset p₀ hcount₀ = t + C₀ := by
      dsimp [q, C₀]
      omega
    rw [hidx]
    exact hcenter
  have hγGlobal : γ * lam ^ t ≤ A / 4 * lam ^ t := by
    exact mul_le_mul_of_nonneg_right (min_le_left _ _)
      (pow_nonneg (zero_lt_one.trans hlam).le t)
  have hγFace : γ * lam ^ t ≤ A * δ / 2 * lam ^ t := by
    exact mul_le_mul_of_nonneg_right (min_le_right _ _)
      (pow_nonneg (zero_lt_one.trans hlam).le t)
  by_cases hνS : ν ∈ S.image (shiftedAtomPatternKey q K)
  · obtain ⟨p, hpS, hpkey⟩ := Finset.mem_image.mp hνS
    have hpNotFace : p ∉ Face := by
      intro hpF
      exact hν_notFace (Finset.mem_image.mpr ⟨p, hpF, hpkey⟩)
    have hpDiff : p ∈ S \ Face := Finset.mem_sdiff.mpr ⟨hpS, hpNotFace⟩
    have hpGap := hfaceGap p hpDiff
    have hpcount := polynomialPatternSurvivors_count hpS
    have hprem := hrem p hpS
    rw [← hpkey,
      atomValuation_shiftedAtomPatternKey_geometric A lam c q K p]
    dsimp [geometricPolynomialFaceBaseline, S]
    rw [show q - K = t by dsimp [q]; omega]
    have hscale := mul_le_mul_of_nonneg_left hpGap
      (mul_nonneg hA.le (pow_nonneg (zero_lt_one.trans hlam).le t))
    linarith
  · have hfar : atomValuation (fun i => A * lam ^ i + c i) νw +
          (A * lam ^ (q - K₀ + atomPatternMaxOffset p₀ hcount₀) +
            c (q - K₀ + atomPatternMaxOffset p₀ hcount₀)) ≤
        atomValuation (fun i => A * lam ^ i + c i) ν := by
      by_contra hnot
      have hnear : atomValuation (fun i => A * lam ^ i + c i) ν <
          atomValuation (fun i => A * lam ^ i + c i) νw +
            (A * lam ^ (q - K₀ + atomPatternMaxOffset p₀ hcount₀) +
              c (q - K₀ + atomPatternMaxOffset p₀ hcount₀)) :=
        lt_of_not_ge hnot
      obtain ⟨p, hpcount, hpkey⟩ := hpat ν hν_active hnear
      have hpweight : aevalWeight n (D * q + τ) Q
          (shiftedAtomPatternKey q K p) ≠ 0 := by
        have := (mem_activeAevalAtoms.mp hν_active).2
        rw [hpkey]
        exact this
      have hpS : p ∈ S := by
        dsimp [S]
        exact mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpcount
          (by dsimp [q]; omega) hpweight
      exact hνS (Finset.mem_image.mpr ⟨p, hpS, hpkey⟩)
    dsimp [geometricPolynomialFaceBaseline, S]
    have honeQuarter : 1 ≤ A / 4 * lam ^ t := honeG
    have hcenterGamma : 1 + γ * lam ^ t ≤
        A * lam ^ (q - K₀ + atomPatternMaxOffset p₀ hcount₀) +
          c (q - K₀ + atomPatternMaxOffset p₀ hcount₀) := by
      calc
        1 + γ * lam ^ t ≤ A / 4 * lam ^ t + A / 4 * lam ^ t :=
          add_le_add honeQuarter hγGlobal
        _ = A / 2 * lam ^ t := by ring
        _ ≤ _ := hcenter'
    have hadd := add_le_add hwBaseline.le hcenterGamma
    convert hadd.trans hfar using 1 <;>
      dsimp [geometricPolynomialFaceBaseline, S] <;> ring

end

end GaloisForLFunctions
