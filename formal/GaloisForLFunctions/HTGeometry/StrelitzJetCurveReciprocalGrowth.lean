import GaloisForLFunctions.HTGeometry.StrelitzJetCurveRootGrowth
import GaloisForLFunctions.HTGeometry.RatApproximant

/-!
# Reciprocal growth of nonzero Strelitz jet-curve roots

The least nonzero coefficient of the fixed curve remains its least nonzero coefficient after every
sufficiently large specialization.  Polynomial reversal converts a nonzero root to its reciprocal;
Cauchy's root bound then gives the reciprocal the same polynomial envelope as the original branch.
This excludes super-polynomial decay without assuming convergence of a Puiseux expansion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem coeff_invReverse_natDegree_sub (Q : Polynomial ℂ) {j : ℕ} (hj : j ≤ Q.natDegree) :
    (invReverse Q).coeff (Q.natDegree - j) = Q.coeff j := by
  classical
  rw [invReverse]
  simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega)) ?_ |>.trans ?_
  · intro k hk hkj
    have hkD : k ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_monomial, if_neg]
    intro h
    apply hkj
    omega
  · simp

theorem invReverse_eq_reverse (Q : Polynomial ℂ) :
    invReverse Q = Q.reverse := by
  classical
  ext n
  by_cases hn : n ≤ Q.natDegree
  · have hsub : Q.natDegree - n ≤ Q.natDegree := Nat.sub_le _ _
    have hcoeff := coeff_invReverse_natDegree_sub Q hsub
    rw [Nat.sub_sub_self hn] at hcoeff
    rw [hcoeff, Polynomial.coeff_reverse, Polynomial.revAt_le hn]
  · have hdn : Q.natDegree < n := lt_of_not_ge hn
    have hinv : (invReverse Q).coeff n = 0 := by
      rw [invReverse]
      simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero ?_
      intro k hk
      rw [Polynomial.coeff_monomial, if_neg]
      omega
    rw [hinv, Polynomial.coeff_reverse,
      Polynomial.revAt_eq_self_of_lt hdn,
      Polynomial.coeff_eq_zero_of_natDegree_lt hdn]

theorem invReverse_isRoot_inv {Q : Polynomial ℂ} {y : ℂ} (hy : y ≠ 0)
    (hroot : Q.IsRoot y) :
    (invReverse Q).IsRoot y⁻¹ := by
  rw [Polynomial.IsRoot, eval_invReverse _ (inv_ne_zero hy)]
  have hroot' : Q.eval y = 0 := hroot
  simp [hroot']

open Filter

/-- Specializing along an escaping base family eventually preserves both endpoint degrees and
keeps both endpoint coefficients uniformly away from zero. -/
theorem exists_eventually_strelitzJetCurve_endpointData
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).natDegree =
          (strelitzJetCurvePolynomial S).natDegree ∧
        (strelitzJetCurveSpecialization S (u n)).natTrailingDegree =
          (strelitzJetCurvePolynomial S).natTrailingDegree ∧
        c ≤ ‖(strelitzJetCurveSpecialization S (u n)).leadingCoeff‖ ∧
        c ≤ ‖(strelitzJetCurveSpecialization S (u n)).trailingCoeff‖ := by
  let R := strelitzJetCurvePolynomial S
  have hR : R ≠ 0 := strelitzJetCurvePolynomial_ne_zero hS
  have htrail : R.trailingCoeff ≠ 0 := by
    rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_eq_support_min' hR]
    exact Polynomial.mem_support_iff.mp
      (Finset.min'_mem R.support (Polynomial.support_nonempty.mpr hR))
  obtain ⟨c₁, hc₁, hlead⟩ :=
    exists_eventually_strelitzJetCurve_degree_eq_and_leadingCoeff_lower hS huTop
  obtain ⟨c₀, hc₀, hlow⟩ := exists_eventually_pos_le_norm_eval_finOne htrail huTop
  let c := min c₀ c₁
  have hc : 0 < c := lt_min hc₀ hc₁
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlead, hlow] with n hnlead hnlow
  let p := strelitzJetCurveSpecialization S (u n)
  let m := R.natTrailingDegree
  have hpne : p ≠ 0 := by
    intro hp
    have hz : ‖p.leadingCoeff‖ = 0 := by rw [hp]; simp
    have hnleadLower := hnlead.2
    change c₁ ≤ ‖p.leadingCoeff‖ at hnleadLower
    rw [hz] at hnleadLower
    linarith
  have hcoeff (j : ℕ) : p.coeff j = MvPolynomial.eval ![u n] (R.coeff j) := by
    dsimp [p, R]
    rw [strelitzJetCurveSpecialization, Polynomial.coeff_map]
  have hpm : p.coeff m ≠ 0 := by
    intro hz
    have hnorm : ‖MvPolynomial.eval ![u n] R.trailingCoeff‖ = 0 := by
      rw [Polynomial.trailingCoeff]
      simpa [m, hcoeff m] using congrArg norm hz
    linarith
  have hbelow : ∀ j < m, p.coeff j = 0 := by
    intro j hj
    rw [hcoeff]
    have : R.coeff j = 0 := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
    rw [this]
    simp
  have hptrail : p.natTrailingDegree = m := by
    rw [Polynomial.natTrailingDegree_eq_support_min' hpne]
    apply Nat.le_antisymm
    · exact Finset.min'_le p.support m (Polynomial.mem_support_iff.mpr hpm)
    · by_contra hnot
      have hlt : p.support.min' (Polynomial.support_nonempty.mpr hpne) < m := lt_of_not_ge hnot
      have hmem := Finset.min'_mem p.support (Polynomial.support_nonempty.mpr hpne)
      exact Polynomial.mem_support_iff.mp hmem (hbelow _ hlt)
  have htrailEq : p.trailingCoeff = MvPolynomial.eval ![u n] R.trailingCoeff := by
    rw [Polynomial.trailingCoeff, hptrail, Polynomial.trailingCoeff]
    exact hcoeff m
  refine ⟨hnlead.1, hptrail, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) hnlead.2
  · rw [htrailEq]
    exact le_trans (min_le_left _ _) hnlow

/-- Every eventually nonzero specialized root also has polynomially bounded reciprocal.  Thus an
algebraic branch cannot decay faster than every power of the escaping base variable. -/
theorem exists_eventually_norm_inv_root_le_strelitzJetCurvePolynomialGrowth
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u root : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ‖(root n)⁻¹‖ ≤ C * (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S := by
  obtain ⟨c, hc, hdata⟩ := exists_eventually_strelitzJetCurve_endpointData hS huTop
  let C : ℝ := strelitzJetCurveCoefficientMass S / c + 1
  have hC : 0 < C := by
    dsimp [C]
    have hm := strelitzJetCurveCoefficientMass_pos S
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hroot, hroot0, hdata] with n hnroot hnroot0 hndata
  let p := strelitzJetCurveSpecialization S (u n)
  let q := p.reverse
  let B : ℝ := strelitzJetCurveCoefficientMass S *
    (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (strelitzJetCurveCoefficientMass_pos S).le (by positivity)
  let Bnn : NNReal := ⟨B, hB⟩
  let cnn : NNReal := ⟨c, hc.le⟩
  have hqlead : c ≤ ‖q.leadingCoeff‖ := by
    change c ≤ ‖p.reverse.leadingCoeff‖
    rw [Polynomial.reverse_leadingCoeff]
    simpa [p] using hndata.2.2.2
  have hclead : cnn ≤ ‖q.leadingCoeff‖₊ := by
    change c ≤ ‖q.leadingCoeff‖
    exact hqlead
  have hcoeff : ∀ i, ‖q.coeff i‖₊ ≤ Bnn := by
    intro i
    change ‖q.coeff i‖ ≤ B
    change ‖p.reverse.coeff i‖ ≤ B
    rw [Polynomial.coeff_reverse]
    simpa [p, B] using norm_coeff_strelitzJetCurveSpecialization_le S (u n)
      ((Polynomial.revAt p.natDegree) i)
  have hcb := GaloisForLFunctions.Nevanlinna.cauchyBound_coe_le_of_coeff_bound
    (p := q) (C := Bnn) (L := cnn) (by exact_mod_cast hc) hclead hcoeff
  have hqne : q ≠ 0 := by
    intro hq0
    have hz : ‖q.leadingCoeff‖ = 0 := by rw [hq0]; simp
    rw [hz] at hqlead
    linarith
  have hproot : p.IsRoot (root n) := by simpa [p] using hnroot
  have hqroot : q.IsRoot (root n)⁻¹ := by
    have h := invReverse_isRoot_inv hnroot0 hproot
    rwa [invReverse_eq_reverse] at h
  have hrootlt : ‖(root n)⁻¹‖ < ((Polynomial.cauchyBound q : NNReal) : ℝ) := by
    exact_mod_cast hqroot.norm_lt_cauchyBound hqne
  have hbasepow : (1 : ℝ) ≤
      (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S := by
    exact one_le_pow₀ (by linarith [norm_nonneg (u n)])
  change ‖(root n)⁻¹‖ ≤ C * (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S
  have hratio : B / c + 1 ≤
      C * (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S := by
    calc
      B / c + 1 = (strelitzJetCurveCoefficientMass S / c) *
          (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S + 1 := by
        dsimp [B]
        ring
      _ ≤ (strelitzJetCurveCoefficientMass S / c) *
          (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S +
            (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S := by
        linarith
      _ = C * (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S := by
        dsimp [C]
        ring
  exact hrootlt.le.trans (hcb.trans hratio)

end

end GaloisForLFunctions.HTGeometry
