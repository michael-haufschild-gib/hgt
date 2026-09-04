import GaloisForLFunctions.HTGeometry.StrelitzJetCurveRootProximity
import GaloisForLFunctions.HTGeometry.NevanlinnaRootEstimate

/-!
# Polynomial growth of roots of the Strelitz jet curve

The coefficients of the fixed jet curve are ordinary polynomials in the escaping first logarithmic
jet.  One finite coefficient mass and one finite coefficient degree therefore bound every
specialization.  The leading coefficient stays uniformly away from zero, so Cauchy's root bound
forces every selected numerical branch to grow at most polynomially in the first jet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Uniform coefficient mass for the ordinary one-variable coefficients of a Strelitz jet curve. -/
def strelitzJetCurveCoefficientMass (S : MvPolynomial (Fin 2) ℂ) : ℝ :=
  1 + ∑ j ∈ Finset.range ((strelitzJetCurvePolynomial S).natDegree + 1),
    coeffNormSum (finOnePolynomial ((strelitzJetCurvePolynomial S).coeff j))

/-- Largest base-variable degree among the coefficients of a Strelitz jet curve. -/
def strelitzJetCurveCoefficientDegree (S : MvPolynomial (Fin 2) ℂ) : ℕ :=
  Finset.sup (Finset.range ((strelitzJetCurvePolynomial S).natDegree + 1))
    (fun j => (finOnePolynomial ((strelitzJetCurvePolynomial S).coeff j)).natDegree)

theorem strelitzJetCurveCoefficientMass_pos (S : MvPolynomial (Fin 2) ℂ) :
    0 < strelitzJetCurveCoefficientMass S := by
  rw [strelitzJetCurveCoefficientMass]
  have hsum : 0 ≤ ∑ j ∈ Finset.range ((strelitzJetCurvePolynomial S).natDegree + 1),
      coeffNormSum (finOnePolynomial ((strelitzJetCurvePolynomial S).coeff j)) :=
    Finset.sum_nonneg fun j _ => coeffNormSum_nonneg _
  linarith

/-- Every coefficient of a specialized Strelitz jet curve has one uniform polynomial bound in the
escaping base variable. -/
theorem norm_coeff_strelitzJetCurveSpecialization_le
    (S : MvPolynomial (Fin 2) ℂ) (u : ℂ) (j : ℕ) :
    ‖(strelitzJetCurveSpecialization S u).coeff j‖ ≤
      strelitzJetCurveCoefficientMass S *
        (1 + ‖u‖) ^ strelitzJetCurveCoefficientDegree S := by
  classical
  let R := strelitzJetCurvePolynomial S
  let q : Polynomial ℂ := finOnePolynomial (R.coeff j)
  have hcoeff : (strelitzJetCurveSpecialization S u).coeff j = q.eval u := by
    rw [strelitzJetCurveSpecialization, Polynomial.coeff_map]
    simpa [q, R] using
      (eval_finOnePolynomial ((strelitzJetCurvePolynomial S).coeff j) u).symm
  rw [hcoeff]
  by_cases hj : j ≤ R.natDegree
  · have hjmem : j ∈ Finset.range (R.natDegree + 1) := Finset.mem_range.mpr (by omega)
    have hmass : coeffNormSum q ≤ strelitzJetCurveCoefficientMass S := by
      have hsingle := Finset.single_le_sum
        (f := fun k : ℕ => coeffNormSum (finOnePolynomial (R.coeff k)))
        (fun k _ => coeffNormSum_nonneg _) hjmem
      rw [strelitzJetCurveCoefficientMass]
      dsimp [R] at hsingle ⊢
      linarith
    have hdegree : q.natDegree ≤ strelitzJetCurveCoefficientDegree S := by
      rw [strelitzJetCurveCoefficientDegree]
      exact Finset.le_sup (f := fun k =>
        (finOnePolynomial ((strelitzJetCurvePolynomial S).coeff k)).natDegree) hjmem
    have hbase : (1 : ℝ) ≤ 1 + ‖u‖ := by
      linarith [norm_nonneg u]
    calc
      ‖q.eval u‖ ≤ coeffNormSum q * (1 + ‖u‖) ^ q.natDegree :=
        norm_eval_le_coeffNormSum q u
      _ ≤ strelitzJetCurveCoefficientMass S * (1 + ‖u‖) ^ q.natDegree := by
        exact mul_le_mul_of_nonneg_right hmass (by positivity)
      _ ≤ strelitzJetCurveCoefficientMass S *
          (1 + ‖u‖) ^ strelitzJetCurveCoefficientDegree S := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hdegree)
          (strelitzJetCurveCoefficientMass_pos S).le
  · have hjlt : R.natDegree < j := lt_of_not_ge hj
    have hRcoeff : R.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hjlt
    have hq : q = 0 := by simp [q, finOnePolynomial, hRcoeff]
    rw [hq, Polynomial.eval_zero, norm_zero]
    exact mul_nonneg (strelitzJetCurveCoefficientMass_pos S).le (by positivity)

/-- Every root of a fixed Strelitz jet curve, specialized along an escaping base family, has at
most polynomial growth in that base variable. -/
theorem exists_eventually_norm_root_le_strelitzJetCurvePolynomialGrowth
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u root : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ‖root n‖ ≤ C * (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S := by
  obtain ⟨c, hc, hdata⟩ :=
    exists_eventually_strelitzJetCurve_degree_eq_and_leadingCoeff_lower hS huTop
  let C : ℝ := strelitzJetCurveCoefficientMass S / c + 1
  have hC : 0 < C := by
    dsimp [C]
    have hm := strelitzJetCurveCoefficientMass_pos S
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hroot, hdata] with n hnroot hndata
  let p := strelitzJetCurveSpecialization S (u n)
  let B : ℝ := strelitzJetCurveCoefficientMass S *
    (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (strelitzJetCurveCoefficientMass_pos S).le (by positivity)
  let Bnn : NNReal := ⟨B, hB⟩
  let cnn : NNReal := ⟨c, hc.le⟩
  have hclead : cnn ≤ ‖p.leadingCoeff‖₊ := by
    change c ≤ ‖p.leadingCoeff‖
    simpa [p] using hndata.2
  have hcoeff : ∀ i, ‖p.coeff i‖₊ ≤ Bnn := by
    intro i
    change ‖p.coeff i‖ ≤ B
    simpa [p, B] using norm_coeff_strelitzJetCurveSpecialization_le S (u n) i
  have hcb := GaloisForLFunctions.Nevanlinna.cauchyBound_coe_le_of_coeff_bound
    (p := p) (C := Bnn) (L := cnn) (by exact_mod_cast hc) hclead hcoeff
  have hpne : p ≠ 0 := by
    intro hp
    have : ‖p.leadingCoeff‖ = 0 := by rw [hp]; simp
    rw [this] at hndata
    linarith
  have hrootlt : ‖root n‖ < ((Polynomial.cauchyBound p : NNReal) : ℝ) := by
    exact_mod_cast hnroot.norm_lt_cauchyBound hpne
  have hbasepow : (1 : ℝ) ≤
      (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S := by
    exact one_le_pow₀ (by linarith [norm_nonneg (u n)])
  change ‖root n‖ ≤ C * (1 + ‖u n‖) ^ strelitzJetCurveCoefficientDegree S
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
