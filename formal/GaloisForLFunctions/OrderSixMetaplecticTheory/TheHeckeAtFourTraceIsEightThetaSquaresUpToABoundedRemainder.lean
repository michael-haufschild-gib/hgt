import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckePointsOfARamifiedCuspAreRamified

/-!
# The Hecke-at-four trace is eight theta squares up to a bounded remainder

The remainder `G' = Tr F − 8 θ_s²` (`fourRemainder`) of the Hecke-at-four trace of the projected theta function:

* transforms by `ρ²` under the rational extension `Γ(3)·SL₂(ℤ)` (`norm_fourRemainder_rational`);
* is `O(v^{−7/3})` on the standard strip above any fixed height (`norm_fourRemainder_strip`): at the Hecke points
  `(2z, 2v)` and `((z + 3t)/2, v/2)` the theta function is `c h^{2/3} + O(h^{−3})`, the growing parts give
  `8 · c²(2v)^{2/3}(v/2)^{2/3} = 8c²v^{4/3}`, and the twisted products `Σ_u u (c(v/2)^{2/3})²` cancel because
  `1 + ω + ω² = 0`;
* is bounded at the ramified cusps, where every Hecke point is ramified (`norm_fourRemainder_ramified`);
* hence is **bounded on `ℍ³`** (`fourRemainder_bounded`) and square integrable on the fundamental domain.

So `Tr F` and `8θ_s²` have the same growth at every cusp of `Γ(3)`: the 2-adic correlation carries no new growth.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- `G' = Tr F − 8θ_s²`. -/
def fourRemainder (w : HyperbolicSpace) : ℂ := sourceFourTrace w - 8 * sourceTheta w ^ 2

/-! ### Equivariance -/

theorem sourceTheta_rational_inv (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    sourceTheta (integralComplexMatrix (rationalEmbedding r) • w) = sourceTheta w :=
  cubicSourceResidualFunction_rational r w

theorem fourRemainder_rationalExtension (G : rationalExtension) (w : HyperbolicSpace) :
    fourRemainder (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G ^ 2 * fourRemainder w := by
  obtain ⟨n, r, hG⟩ := G.2
  have hρ : extendedComplexCharacter G = complexCharacter n := rationalExtensionValue_of_product G n r hG
  have hw : integralComplexMatrix (G : SL(2, O)) • w =
      complexMatrix n • (integralComplexMatrix (rationalEmbedding r) • w) := by
    rw [← hG, map_mul, mul_smul]
    rfl
  have hθ := cubicSourceResidualFunction_automorphy G w
  unfold fourRemainder
  have hr : sourceFourTrace (integralComplexMatrix (rationalEmbedding r) • w) = sourceFourTrace w :=
    heckeFourTrace_rational sourceTheta sourceTheta_automorphy sourceTheta_rational_inv r w
  rw [show sourceTheta (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G * sourceTheta w from hθ,
    hw, sourceFourTrace_automorphy, hr, hρ]
  ring

theorem norm_fourRemainder_rational (G : rationalExtension) (w : HyperbolicSpace) :
    ‖fourRemainder (integralComplexMatrix (G : SL(2, O)) • w)‖ = ‖fourRemainder w‖ := by
  rw [fourRemainder_rationalExtension, norm_mul, norm_pow, norm_extendedComplexCharacter, one_pow, one_mul]

/-! ### The standard strip -/

theorem heckeHigh_source_point (z : ℂ) (v : ℝ) (hv : 0 < v) :
    heckeHigh sourceTheta (upperPoint z v hv) = sourceTheta (upperPoint (2 * z) (2 * v) (by positivity)) := by
  rw [heckeHigh, fourDilation_upperPoint]

theorem heckeLow_source_point (s : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    heckeLow sourceTheta s (upperPoint z v hv) =
      sourceTheta (upperPoint ((z + 3 * ringComplex s) / 2) (v / 2) (by positivity)) := by
  rw [heckeLow, transThree_smul_upperPoint, fourContraction_upperPoint]

/-- `‖(P + d)(Q + e) − PQ‖ ≤ ‖P‖‖e‖ + ‖d‖‖Q‖ + ‖d‖‖e‖`. -/
theorem norm_mul_add_sub_le (P Q d e : ℂ) :
    ‖(P + d) * (Q + e) - P * Q‖ ≤ ‖P‖ * ‖e‖ + ‖d‖ * ‖Q‖ + ‖d‖ * ‖e‖ := by
  have h : (P + d) * (Q + e) - P * Q = P * e + d * Q + d * e := by ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (le_of_eq ?_)) (le_of_eq (norm_mul _ _))
  rw [norm_mul, norm_mul]

theorem norm_ringComplex_uO (k : Fin 3) : ‖ringComplex (uO k)‖ = 1 := by
  have h3 : ringComplex (uO k) ^ 3 = 1 := by rw [← map_pow, uO_cube, map_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (3 : ℕ) ≠ 0)).mp (by rw [← norm_pow, h3, norm_one])

theorem sum_ringComplex_uO : ∑ k : Fin 3, ringComplex (uO k) = 0 := by
  rw [Fin.sum_univ_three]
  simp only [uO, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_one, map_pow]
  linear_combination omega_complex_rel


/-- `‖XY − PQ‖ ≤ 2MD + D²` when `X, Y` are within `D` of `P, Q` and `‖P‖, ‖Q‖ ≤ M`. -/
theorem norm_mul_sub_mul_le {X Y P Q : ℂ} {M D : ℝ} (hP : ‖P‖ ≤ M) (hQ : ‖Q‖ ≤ M) (hX : ‖X - P‖ ≤ D)
    (hY : ‖Y - Q‖ ≤ D) : ‖X * Y - P * Q‖ ≤ 2 * M * D + D ^ 2 := by
  have h := norm_mul_add_sub_le P Q (X - P) (Y - Q)
  rw [show (P + (X - P)) * (Q + (Y - Q)) - P * Q = X * Y - P * Q by ring] at h
  have hD : 0 ≤ D := (norm_nonneg _).trans hX
  refine h.trans ?_
  have e1 := mul_le_mul hP hY (norm_nonneg _) ((norm_nonneg _).trans hP)
  have e2 := mul_le_mul hX hQ (norm_nonneg _) hD
  have e3 := mul_le_mul hX hY (norm_nonneg _) hD
  nlinarith

theorem norm_cpow_two_thirds {h : ℝ} (hh : 0 < h) : ‖(h : ℂ) ^ (2 / 3 : ℂ)‖ = h ^ ((2 : ℝ) / 3) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hh]
  norm_num

/-- **`G' = O(v^{−7/3})` on the standard strip above any fixed height.** -/
theorem norm_fourRemainder_strip (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖fourRemainder (upperPoint z v hv)‖ ≤ K * v ^ (-(7 : ℝ) / 3) := by
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height (a / 2) (by positivity)
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue with hcdef
  refine ⟨28 * (32 * ‖c‖ * C₁ + 64 * C₁ ^ 2 * a ^ (-(11 : ℝ) / 3)), by positivity, fun z v hv hav => ?_⟩
  have hv2 : 0 < 2 * v := by positivity
  have hvh : 0 < v / 2 := by positivity
  set P := c * ((2 * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) with hPdef
  set Q := c * ((v / 2 : ℝ) : ℂ) ^ (2 / 3 : ℂ) with hQdef
  set R := c * (v : ℂ) ^ (2 / 3 : ℂ) with hRdef
  have hPQ : P * Q = R * R := by
    rw [hPdef, hQdef, hRdef, show c * ((2 * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) * (c * ((v / 2 : ℝ) : ℂ) ^ (2 / 3 : ℂ)) =
      c ^ 2 * (((2 * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) * ((v / 2 : ℝ) : ℂ) ^ (2 / 3 : ℂ)) by ring,
      cpow_two_mul_mul_cpow_half v hv]
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    rw [show (4 / 3 : ℂ) = 2 / 3 + 2 / 3 by norm_num, Complex.cpow_add _ _ hv0]
    ring
  set M := 2 * ‖c‖ * v ^ ((2 : ℝ) / 3)
  set D := 8 * C₁ / v ^ 3
  have hp23 : 0 ≤ v ^ ((2 : ℝ) / 3) := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hPM : ‖P‖ ≤ M := by
    rw [hPdef, norm_mul, norm_cpow_two_thirds hv2, Real.mul_rpow (by norm_num) hv.le]
    have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    nlinarith [norm_nonneg c]
  have hQM : ‖Q‖ ≤ M := by
    rw [hQdef, norm_mul, norm_cpow_two_thirds hvh]
    have h1 : (v / 2) ^ ((2 : ℝ) / 3) ≤ v ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow hvh.le (by linarith) (by norm_num)
    nlinarith [norm_nonneg c]
  have hRM : ‖R‖ ≤ M := by
    rw [hRdef, norm_mul, norm_cpow_two_thirds hv]
    nlinarith [norm_nonneg c]
  have hcube : ∀ (ζ : ℂ) (h : ℝ) (hh : 0 < h), v / 2 ≤ h →
      ‖sourceTheta (upperPoint ζ h hh) - c * (h : ℂ) ^ (2 / 3 : ℂ)‖ ≤ D := by
    intro ζ h hh hvh'
    have hd := hdec h hh (by linarith) ζ
    refine hd.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (v / 2) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hvh.le hvh' 3
    nlinarith
  have hA : ‖sourceTheta (upperPoint (2 * z) (2 * v) hv2) - P‖ ≤ D := hcube _ _ hv2 (by linarith)
  have hB : ∀ s : O, ‖sourceTheta (upperPoint ((z + 3 * ringComplex s) / 2) (v / 2) hvh) - Q‖ ≤ D :=
    fun s => hcube _ _ hvh le_rfl
  have h0 : ‖sourceTheta (upperPoint z v hv) - R‖ ≤ D := hcube _ _ hv (by linarith)
  set θA := sourceTheta (upperPoint (2 * z) (2 * v) hv2)
  set θB : O → ℂ := fun s => sourceTheta (upperPoint ((z + 3 * ringComplex s) / 2) (v / 2) hvh)
  set θ0 := sourceTheta (upperPoint z v hv)
  have htr : sourceFourTrace (upperPoint z v hv) =
      ∑ x : Fin 4, θA * θB (tO x) + ∑ x : Fin 4, θB (-1 + tO x) * θA +
        ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x)) := by
    rw [sourceFourTrace, heckeFourTrace_eq_hecke sourceTheta sourceTheta_automorphy]
    simp only [heckeHigh_source_point, heckeLow_source_point]
    rfl
  have hident : fourRemainder (upperPoint z v hv) =
      ∑ x : Fin 4, (θA * θB (tO x) - P * Q) + ∑ x : Fin 4, (θB (-1 + tO x) * θA - Q * P) +
        ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x) - Q * Q) -
          8 * (θ0 * θ0 - R * R) := by
    have hu := sum_ringComplex_uO
    have e3 : ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x) - Q * Q) =
        ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x)) -
          4 * (Q * Q) * ∑ k : Fin 3, ringComplex (uO k) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [fourRemainder, htr, Finset.sum_sub_distrib, Finset.sum_sub_distrib, e3, hu]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    linear_combination 8 * hPQ
  have hEb : ∀ X Y PP QQ : ℂ, ‖PP‖ ≤ M → ‖QQ‖ ≤ M → ‖X - PP‖ ≤ D → ‖Y - QQ‖ ≤ D →
      ‖X * Y - PP * QQ‖ ≤ 2 * M * D + D ^ 2 := fun X Y PP QQ h1 h2 h3 h4 => norm_mul_sub_mul_le h1 h2 h3 h4
  set Eb := 2 * M * D + D ^ 2
  have hs1 : ‖∑ x : Fin 4, (θA * θB (tO x) - P * Q)‖ ≤ 4 * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : Fin 4, ‖θA * θB (tO x) - P * Q‖ ≤ ∑ _x : Fin 4, Eb :=
          Finset.sum_le_sum fun x _ => hEb _ _ _ _ hPM hQM hA (hB _)
      _ = 4 * Eb := by simp
  have hs2 : ‖∑ x : Fin 4, (θB (-1 + tO x) * θA - Q * P)‖ ≤ 4 * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : Fin 4, ‖θB (-1 + tO x) * θA - Q * P‖ ≤ ∑ _x : Fin 4, Eb :=
          Finset.sum_le_sum fun x _ => hEb _ _ _ _ hQM hPM (hB _) hA
      _ = 4 * Eb := by simp
  have hs3 : ‖∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x) - Q * Q)‖ ≤
      12 * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k : Fin 3, ‖∑ x : Fin 4, ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x) - Q * Q)‖
        ≤ ∑ _k : Fin 3, 4 * Eb := by
          refine Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans ?_
          calc ∑ x : Fin 4, ‖ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x) - Q * Q)‖
              ≤ ∑ _x : Fin 4, Eb := Finset.sum_le_sum fun x _ => by
                rw [norm_mul, norm_ringComplex_uO, one_mul]
                exact hEb _ _ _ _ hQM hQM (hB _) (hB _)
            _ = 4 * Eb := by simp
      _ = 12 * Eb := by simp; ring
  have hs4 : ‖8 * (θ0 * θ0 - R * R)‖ ≤ 8 * Eb := by
    rw [norm_mul, show ‖(8 : ℂ)‖ = 8 by norm_num]
    exact mul_le_mul_of_nonneg_left (hEb _ _ _ _ hRM hRM h0 h0) (by norm_num)
  have htotal : ‖fourRemainder (upperPoint z v hv)‖ ≤ 28 * Eb := by
    rw [hident]
    calc _ ≤ ‖∑ x : Fin 4, (θA * θB (tO x) - P * Q) + ∑ x : Fin 4, (θB (-1 + tO x) * θA - Q * P) +
            ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) * (θB (-(uO k ^ 2) + tO x) * θB (tO x) - Q * Q)‖ +
          ‖8 * (θ0 * θ0 - R * R)‖ := norm_sub_le _ _
      _ ≤ (4 * Eb + 4 * Eb + 12 * Eb) + 8 * Eb := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hs1 hs2)) hs3)
      _ = 28 * Eb := by ring
  refine htotal.trans ?_
  -- `Eb = 32‖c‖C₁ v^{−7/3} + 64C₁² v^{−6}`
  have hv3 : v ^ ((2 : ℝ) / 3) / v ^ 3 = v ^ (-(7 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hv]
    norm_num
  have hv6 : 1 / v ^ 6 ≤ a ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
    have hsplit : 1 / v ^ 6 = v ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
      rw [← Real.rpow_add hv, one_div, ← Real.rpow_natCast, ← Real.rpow_neg hv.le]
      norm_num
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hav (by norm_num)) (by positivity)
  have hEbv : Eb = 32 * ‖c‖ * C₁ * (v ^ ((2 : ℝ) / 3) / v ^ 3) + 64 * C₁ ^ 2 * (1 / v ^ 6) := by
    simp only [Eb, M, D]
    field_simp
    ring
  rw [hEbv, hv3]
  have := mul_le_mul_of_nonneg_left hv6 (by positivity : (0 : ℝ) ≤ 64 * C₁ ^ 2)
  nlinarith [norm_nonneg c, Real.rpow_nonneg hv.le (-(7 : ℝ) / 3)]


/-! ### The ramified cusps -/

theorem cuspRepresentative_entries (j : Fin 3) :
    (cuspRepresentative j : SL(2, O)) 0 0 = 1 ∧ (cuspRepresentative j : SL(2, O)) 1 0 = cuspParameter j := by
  simp [cuspRepresentative, lowerCuspMatrix]

theorem colRes_one_cuspParameter (j : Fin 3) (hj : j ≠ 0) : colRes 1 (cuspParameter j) ≠ 0 := by
  rw [colRes, cuspResidue_one, cuspParameter_residue]
  fin_cases j
  · exact absurd rfl hj
  · simp [cuspResidueParameter]
  · simp [cuspResidueParameter]

theorem colRes_cuspRepresentative (j : Fin 3) (hj : j ≠ 0) :
    colRes ((cuspRepresentative j : SL(2, O)) 0 0) ((cuspRepresentative j : SL(2, O)) 1 0) ≠ 0 := by
  rw [(cuspRepresentative_entries j).1, (cuspRepresentative_entries j).2]
  exact colRes_one_cuspParameter j hj

theorem colRes_trans_cuspRepresentative (s : O) (j : Fin 3) (hj : j ≠ 0) :
    colRes (((transThree s : SL(2, O)) * cuspRepresentative j) 0 0)
      (((transThree s : SL(2, O)) * cuspRepresentative j) 1 0) ≠ 0 := by
  have h00 : ((transThree s : SL(2, O)) * cuspRepresentative j) 0 0 = 1 + 3 * s * cuspParameter j := by
    simp [transThree, cuspRepresentative, lowerCuspMatrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  have h10 : ((transThree s : SL(2, O)) * cuspRepresentative j) 1 0 = cuspParameter j := by
    simp [transThree, cuspRepresentative, lowerCuspMatrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  rw [h00, h10, colRes, cuspResidue_congr (show (3 : O) ∣ 1 + 3 * s * cuspParameter j - 1 from
    ⟨s * cuspParameter j, by ring⟩)]
  exact colRes_one_cuspParameter j hj

/-- **`G'` is bounded at the ramified cusps.** -/
theorem norm_fourRemainder_ramified (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Fin 3), j ≠ 0 → ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖fourRemainder (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ K := by
  obtain ⟨C, β, hC, hβ, hhecke⟩ := sourceTheta_hecke_ramified a ha
  obtain ⟨C', β', hC', hβ', hram⟩ := sourceTheta_ramified_decay a ha
  refine ⟨20 * C ^ 2 + 8 * C' ^ 2, by positivity, fun j hj z v hv hav => ?_⟩
  set x := upperPoint z v hv
  set w := integralComplexMatrix (cuspRepresentative j) • x
  have he : Real.exp (-(β / 2) * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he' : Real.exp (-β' * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hH : ‖heckeHigh sourceTheta w‖ ≤ C := by
    rw [heckeHigh]
    refine ((hhecke _ (colRes_cuspRepresentative j hj) z v hv hav).1).trans ?_
    nlinarith
  have hL : ∀ s : O, ‖heckeLow sourceTheta s w‖ ≤ C := by
    intro s
    have hw : complexMatrix (transThree s) • w =
        integralComplexMatrix ((transThree s : SL(2, O)) * cuspRepresentative j) • x := by
      rw [map_mul, mul_smul]
      rfl
    rw [heckeLow, hw]
    refine ((hhecke _ (colRes_trans_cuspRepresentative s j hj) z v hv hav).2).trans ?_
    nlinarith
  have hθ : ‖sourceTheta w‖ ≤ C' := by
    refine (hram _ (colRes_cuspRepresentative j hj) z v hv hav).trans ?_
    nlinarith
  have hprod : ∀ X Y : ℂ, ‖X‖ ≤ C → ‖Y‖ ≤ C → ‖X * Y‖ ≤ C ^ 2 := fun X Y hX hY => by
    rw [norm_mul, sq]
    exact mul_le_mul hX hY (norm_nonneg _) hC
  have htr : ‖sourceFourTrace w‖ ≤ 20 * C ^ 2 := by
    rw [sourceFourTrace, heckeFourTrace_eq_hecke sourceTheta sourceTheta_automorphy]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖∑ x : Fin 4, heckeHigh sourceTheta w * heckeLow sourceTheta (tO x) w‖ ≤ 4 * C ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _x : Fin 4, C ^ 2 := Finset.sum_le_sum fun x _ => hprod _ _ hH (hL _)
        _ = 4 * C ^ 2 := by simp
    have h2 : ‖∑ x : Fin 4, heckeLow sourceTheta (-1 + tO x) w * heckeHigh sourceTheta w‖ ≤ 4 * C ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _x : Fin 4, C ^ 2 := Finset.sum_le_sum fun x _ => hprod _ _ (hL _) hH
        _ = 4 * C ^ 2 := by simp
    have h3 : ‖∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) *
        (heckeLow sourceTheta (-(uO k ^ 2) + tO x) w * heckeLow sourceTheta (tO x) w)‖ ≤ 12 * C ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _k : Fin 3, 4 * C ^ 2 := by
            refine Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans ?_
            calc _ ≤ ∑ _x : Fin 4, C ^ 2 := Finset.sum_le_sum fun x _ => by
                  rw [norm_mul, norm_ringComplex_uO, one_mul]
                  exact hprod _ _ (hL _) (hL _)
              _ = 4 * C ^ 2 := by simp
        _ = 12 * C ^ 2 := by simp; ring
    calc _ ≤ ‖∑ x : Fin 4, heckeHigh sourceTheta w * heckeLow sourceTheta (tO x) w‖ +
          ‖∑ x : Fin 4, heckeLow sourceTheta (-1 + tO x) w * heckeHigh sourceTheta w‖ +
            ‖∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) *
              (heckeLow sourceTheta (-(uO k ^ 2) + tO x) w * heckeLow sourceTheta (tO x) w)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ 4 * C ^ 2 + 4 * C ^ 2 + 12 * C ^ 2 := by gcongr
      _ = 20 * C ^ 2 := by ring
  rw [fourRemainder]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_pow, show ‖(8 : ℂ)‖ = 8 by norm_num]
  have hθ2 : ‖sourceTheta w‖ ^ 2 ≤ C' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hθ 2
  linarith

/-! ### Boundedness -/

/-- **`G' = Tr F − 8θ_s²` is bounded on hyperbolic three-space.** -/
theorem fourRemainder_bounded : ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖fourRemainder w‖ ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨K₀, hK₀, hstrip⟩ := norm_fourRemainder_strip a₀ ha₀
  obtain ⟨K₁, hK₁, hram⟩ := norm_fourRemainder_ramified a₀ ha₀
  refine ⟨K₀ * a₀ ^ (-(7 : ℝ) / 3) + K₁, fun w => ?_⟩
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨G', j, T, hT, -, hu1, hdec'⟩ := three_cusp_decomposition M⁻¹
  have hw : w = integralComplexMatrix (G' : SL(2, O)) •
      (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) := by
    rw [← mul_smul, ← map_mul, ← mul_assoc, ← hdec', ← hMw, ← mul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]
  rw [hw, norm_fourRemainder_rational]
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  rw [map_mul, mul_smul, ← hp]
  by_cases hj : j = 0
  · subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    rw [hc1, map_one, one_smul]
    refine (hstrip z' v' hv' hfloor).trans ?_
    have : v' ^ (-(7 : ℝ) / 3) ≤ a₀ ^ (-(7 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos ha₀ hfloor (by norm_num)
    nlinarith
  · exact (hram j hj z' v' hv' hfloor).trans (by nlinarith [Real.rpow_nonneg ha₀.le (-(7 : ℝ) / 3)])

/-! ### Square integrability -/

theorem sourceFourTrace_continuous_hyperbolic : Continuous sourceFourTrace := by
  have h : sourceFourTrace = fun w => ∑ i : CosetIndex,
      heckeFourCorrelation sourceTheta (complexMatrix (cosetRep i) • w) :=
    funext (heckeFourTrace_eq_sum sourceTheta sourceTheta_automorphy)
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  unfold heckeFourCorrelation
  exact (cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _))).mul
    (cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _)))

theorem fourRemainder_continuous : Continuous fourRemainder :=
  sourceFourTrace_continuous_hyperbolic.sub (continuous_const.mul (cubicSourceResidualFunction_continuous.pow 2))

/-- `G'` is square integrable on the fundamental domain of `Γ(3)`. -/
theorem fourRemainder_memLp : MemLp fourRemainder 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := fourRemainder_bounded
  exact MemLp.of_bound fourRemainder_continuous.measurable.aestronglyMeasurable B (Eventually.of_forall hB)

end GaloisForLFunctions.OrderSixMetaplecticTheory
