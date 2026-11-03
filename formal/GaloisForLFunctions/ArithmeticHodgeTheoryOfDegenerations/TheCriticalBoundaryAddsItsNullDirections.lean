import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCanonicalCriticalClockEntersFromTheNegativeSide
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedSectorInheritsThePolarization

/-!
# The critical boundary adds its null directions

The inverse-square correction is negative definite on every independent
finite family of windows. On the exact critical clock the complete family's
negative index therefore includes the null index of the leading pencil.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strict decrease makes the whole nonpositive spectral subspace negative. -/
private theorem negIndex_add_nullIndex_le_of_strict_order {P H : Matrix ι ι ℂ}
    (hP : P.IsHermitian)
    (hlt : ∀ x : ι → ℂ, x ≠ 0 → hermQuad H x < hermQuad P x) :
    hermNegIndex P + hermNullIndex P ≤ hermNegIndex H := by
  let U : Matrix ι ι ℂ := hP.eigenvectorUnitary
  let s : Finset ι := {i | hP.eigenvalues i ≤ 0}
  let V := coordSupport s
  let W := V.map U.mulVecLin
  have hU : IsUnit U := isUnit_eigenvectorUnitary hP
  have hdim : Module.finrank ℂ W = s.card := by
    calc Module.finrank ℂ W = Module.finrank ℂ V :=
          ((Submodule.equivMapOfInjective U.mulVecLin (mulVecLin_injective hU) V).symm).finrank_eq
      _ = s.card := finrank_coordSupport s
  have hnonpos (x : ι → ℂ) (hx : x ∈ V) : hermQuad P (U *ᵥ x) ≤ 0 := by
    rw [← hermQuad_conjugate, show Uᴴ * P * U =
      diagonal (fun i => ((hP.eigenvalues i : ℝ) : ℂ)) from
        conjTranspose_mul_mul_eigenvectorUnitary hP, hermQuad_diagonal]
    refine Finset.sum_nonpos fun i _ => ?_
    by_cases hi : i ∈ s
    · have he : hP.eigenvalues i ≤ 0 := by simpa only [s, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
      exact mul_nonpos_of_nonpos_of_nonneg he (Complex.normSq_nonneg _)
    · have hz : x i = 0 := hx i hi
      rw [hz, Complex.normSq_zero, mul_zero]
  have hneg : IsPosDefOn (-H) W := by
    rintro y ⟨x, hx, rfl⟩ hy
    rw [hermQuad_neg]
    exact neg_pos.mpr ((hlt _ hy).trans_le (hnonpos x hx))
  have hbound := finrank_le_posIndex hneg
  rw [hdim] at hbound
  have hdisj : Disjoint ({i | hP.eigenvalues i < 0} : Finset ι)
      ({i | hP.eigenvalues i = 0} : Finset ι) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact (ne_of_lt hi) hj
  have hs : s = ({i | hP.eigenvalues i < 0} : Finset ι) ∪
      ({i | hP.eigenvalues i = 0} : Finset ι) := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact ⟨lt_or_eq_of_le, fun hi => hi.elim le_of_lt le_of_eq⟩
  rw [hs, Finset.card_union_of_disjoint hdisj, ← negIndex_eq_card_neg_eigenvalues hP,
    ← nullIndex_eq_card_zero_eigenvalues hP] at hbound
  exact hbound

/-- Approaching a Hermitian form strictly from below moves its null space
into the negative index while its positive index persists. -/
private theorem eventually_inertia_of_strict_approach {H : ℕ → Matrix ι ι ℂ}
    {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hH : ∀ N, (H N).IsHermitian)
    (hlim : ∀ i j, Tendsto (fun N => H N i j) atTop (𝓝 (P i j)))
    (hlt : ∀ᶠ N in atTop, ∀ x : ι → ℂ, x ≠ 0 → hermQuad (H N) x < hermQuad P x) :
    ∀ᶠ N in atTop,
      hermNegIndex (H N) = hermNegIndex P + hermNullIndex P ∧
      hermPosIndex (H N) = hermPosIndex P ∧ hermNullIndex (H N) = 0 := by
  have hnegLim : ∀ i j, Tendsto (fun N => (-H N) i j) atTop (𝓝 ((-P) i j)) :=
    fun i j => (hlim i j).neg
  have hpos := HeckeKreinToeplitz.eventually_le_hermNegIndex hP.neg hnegLim
  simp only [hermNegIndex, neg_neg] at hpos
  filter_upwards [hlt, hpos] with N hltN hposN
  have hn := negIndex_add_nullIndex_le_of_strict_order hP hltN
  have hsum := posIndex_add_negIndex_add_nullIndex (hH N)
  have hsumP := posIndex_add_negIndex_add_nullIndex hP
  omega

/-- The normalized complete horizon matrix on the canonical critical clock. -/
def canonicalHorizonGram (K : ℝ) (h : ι → ℝ → ℝ) (N : ℕ) : Matrix ι ι ℂ :=
  (((canonicalCriticalClock K N)⁻¹ /
      ∫ u, atomDilate tiltedUnitSpline (canonicalCriticalClock K N / N) u ^ 2 : ℝ) : ℂ) •
    horizonGram tiltedUnitSpline h (canonicalCriticalClock K N) N

omit [Fintype ι] [DecidableEq ι] in
private theorem canonicalHorizonGram_isHermitian (K : ℝ) (h : ι → ℝ → ℝ) (N : ℕ) :
    (canonicalHorizonGram K h N).IsHermitian := by
  ext j i
  have hG := (weilGram_isHermitian (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    fun i => ArithmeticCastelnuovoSeveri.cx
      (horizonTest tiltedUnitSpline (h i) (canonicalCriticalClock K N) N)).apply j i
  simp only [canonicalHorizonGram, Matrix.conjTranspose_apply, Matrix.smul_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
  unfold horizonGram
  rw [← Complex.star_def, hG]

private theorem canonical_energy_correction {h : ℝ → ℝ} {A K : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hK : 0 < K) :
    Tendsto (fun N => canonicalCriticalClock K N ^ 2 *
      (tiltedHorizonEnergy h (canonicalCriticalClock K N) N -
        secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne K h)) atTop
      (𝓝 (-(tiltedNextAliasCoefficient / K *
        ∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2))) := by
  have ht := tiltedHorizonEnergy_quadratic_correction hh hsupp hA
    (canonicalCriticalClock_one_le K) hK
    (criticalCurve_ratio_of_exact (canonicalCriticalClock_exact hK))
  refine ht.congr' ?_
  filter_upwards [canonicalCriticalClock_exact hK] with N hN
  have hc : canonicalCriticalClock K N ≠ 0 := by linarith [canonicalCriticalClock_one_le K N]
  have heq : Real.log N / canonicalCriticalClock K N ^ 8 = K⁻¹ := by
    rw [div_eq_iff (pow_ne_zero 8 hc), hN]
    field_simp
  rw [heq]
  simp only [secondOrderLimit, show (7 : ℝ) + 1 = 8 by norm_num]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The normalized canonical horizon matrices converge to the leading pencil. -/
theorem tendsto_canonicalHorizonGram {h : ι → ℝ → ℝ} {A K : ℝ}
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hA : 0 ≤ A) (hK : 0 < K) (i j : ι) :
    Tendsto (fun N => canonicalHorizonGram K h N i j) atTop
      (𝓝 (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h i j)) := by
  have hlim : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g →
      (∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) →
      Tendsto (fun N => tiltedHorizonEnergy g (canonicalCriticalClock K N) N) atTop
        (𝓝 (secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne K g)) := by
    intro g hg hgs
    simpa only [secondOrderLimit, tiltedHorizonEnergy, show (7 : ℝ) + 1 = 8 by norm_num] using
      horizon_layer_criticalCurve_exact hg hA hgs (canonicalCriticalClock_one_le K) hK
        (criticalCurve_ratio_of_exact (canonicalCriticalClock_exact hK))
  have hp := hlim (fun y => h i y + h j y) ((hh i).add (hh j))
    (fun y hy => by simp only [hsupp i y hy, hsupp j y hy, add_zero])
  have hm := hlim (fun y => h i y - h j y) ((hh i).sub (hh j))
    (fun y hy => by simp only [hsupp i y hy, hsupp j y hy, sub_self])
  have hr := (hp.sub hm).div_const 4
  refine ((Complex.continuous_ofReal.tendsto _).comp hr).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hc : 0 < canonicalCriticalClock K N := by linarith [canonicalCriticalClock_one_le K N]
  simp only [Function.comp_def, canonicalHorizonGram, Matrix.smul_apply, smul_eq_mul]
  rw [horizonGram_apply contDiff_tiltedUnitSpline tiltedUnitSpline_support h hc hN,
    ← Complex.ofReal_mul]
  congr 1
  dsimp only [tiltedHorizonEnergy, horizonTest]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The first matrix correction to the leading pencil is the negative
exponential Gram matrix of exponent ten. -/
theorem canonicalHorizonGram_quadratic_correction {h : ι → ℝ → ℝ} {A K : ℝ}
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hA : 0 ≤ A) (hK : 0 < K) (i j : ι) :
    Tendsto (fun N => (((canonicalCriticalClock K N ^ 2 : ℝ) : ℂ) •
      (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h - canonicalHorizonGram K h N)) i j)
      atTop (𝓝 ((((tiltedNextAliasCoefficient / K : ℝ) : ℂ) • aliasGram 9 h) i j)) := by
  have hp := canonical_energy_correction ((hh i).add (hh j))
    (fun y hy => by simp only [hsupp i y hy, hsupp j y hy, add_zero]) hA hK
  have hm := canonical_energy_correction ((hh i).sub (hh j))
    (fun y hy => by simp only [hsupp i y hy, hsupp j y hy, sub_self]) hA hK
  have hr := ((hp.sub hm).div_const 4).neg
  have hpol := integral_polarize_of_window (A := A)
    (w := fun y => Real.exp (-(10 * y))) (by fun_prop)
    (contDiff_halfWeight (hh i)).continuous (contDiff_halfWeight (hh j)).continuous
    (halfWeight_eq_zero_of_window (hsupp i)) (halfWeight_eq_zero_of_window (hsupp j))
  have hval : -((-(tiltedNextAliasCoefficient / K *
      ∫ y, Real.exp (-(10 * y)) * halfWeight (fun y => h i y + h j y) y ^ 2) -
      -(tiltedNextAliasCoefficient / K *
      ∫ y, Real.exp (-(10 * y)) * halfWeight (fun y => h i y - h j y) y ^ 2)) / 4) =
      tiltedNextAliasCoefficient / K *
        ∫ y, Real.exp (-(10 * y)) * (halfWeight (h i) y * halfWeight (h j) y) := by
    rw [halfWeight_add, halfWeight_sub]
    beta_reduce at hpol ⊢
    rw [← hpol]
    ring
  rw [hval] at hr
  have hgoal : (((tiltedNextAliasCoefficient / K : ℝ) : ℂ) • aliasGram 9 h) i j =
      ((tiltedNextAliasCoefficient / K *
        ∫ y, Real.exp (-(10 * y)) * (halfWeight (h i) y * halfWeight (h j) y) : ℝ) : ℂ) := by
    simp only [Matrix.smul_apply, smul_eq_mul, aliasGram,
      show (9 : ℝ) + 1 = 10 by norm_num, Complex.ofReal_mul]
  rw [hgoal]
  refine ((Complex.continuous_ofReal.tendsto _).comp hr).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hc : 0 < canonicalCriticalClock K N := by linarith [canonicalCriticalClock_one_le K N]
  simp only [Function.comp_def, Matrix.smul_apply, Matrix.sub_apply, canonicalHorizonGram,
    smul_eq_mul, pencilGram]
  rw [horizonGram_apply contDiff_tiltedUnitSpline tiltedUnitSpline_support h hc hN]
  push_cast
  dsimp only [tiltedHorizonEnergy, horizonTest]
  push_cast
  ring

/-- On every independent finite family, the normalized canonical horizon
matrix has all null directions of its leading pencil in its negative index. -/
theorem canonicalHorizonGram_inertia {h : ι → ℝ → ℝ} {A K : ℝ}
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hA : 0 ≤ A) (hlin : LinearIndependent ℝ h) (hK : 0 < K) :
    ∀ᶠ N in atTop,
      hermNegIndex (canonicalHorizonGram K h N) =
        hermNegIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h) +
          hermNullIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h) ∧
      hermPosIndex (canonicalHorizonGram K h N) =
        hermPosIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h) ∧
      hermNullIndex (canonicalHorizonGram K h N) = 0 := by
  let P := pencilGram tiltedUnitSpline 7 tiltedJordanOne K h
  have hcrit : Tendsto (fun N => canonicalCriticalClock K N ^ ((7 : ℝ) + 1) / Real.log N)
      atTop (𝓝 K) := by
    simpa only [show (7 : ℝ) + 1 = (8 : ℕ) by norm_num, Real.rpow_natCast] using
      criticalCurve_ratio_of_exact (canonicalCriticalClock_exact hK)
  have hdecay : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hP : P.IsHermitian := pencilGram_isHermitian contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num)
    hdecay tiltedUnitSpline_decay (β := 7) (by norm_num)
    tendsto_rpow_seven_mul_completedShellEnergy_tilted hh hA hsupp
    (canonicalCriticalClock_one_le K) hK hcrit
  have hC : (aliasGram 9 h).PosDef := aliasGram_posDef 9 hh hsupp hlin
  have hpos : ∀ x : ι → ℂ, x ≠ 0 →
      0 < hermQuad (twistLimitGram 9 (tiltedNextAliasCoefficient / K) h) x := by
    intro x hx
    rw [twistLimitGram, hermQuad_ofReal_smul]
    have hquad : 0 < hermQuad (aliasGram 9 h) x := by
      have ht := (Matrix.posDef_iff_dotProduct_mulVec.mp hC).2 hx
      simpa only [hermQuad, Complex.zero_re] using (Complex.lt_def.mp ht).1
    exact mul_pos (div_pos tiltedNextAliasCoefficient_pos hK) hquad
  have hstrict := eventually_hermQuad_pos_of_tendsto
    (twistLimitGram_isHermitian 9 (tiltedNextAliasCoefficient / K) h) hpos
    (canonicalHorizonGram_quadratic_correction hh hsupp hA hK)
  have hlt : ∀ᶠ N in atTop, ∀ x : ι → ℂ, x ≠ 0 →
      hermQuad (canonicalHorizonGram K h N) x < hermQuad P x := by
    filter_upwards [hstrict] with N hN x hx
    have hq := hN x hx
    rw [hermQuad_ofReal_smul] at hq
    have hsub : hermQuad (P - canonicalHorizonGram K h N) x =
        hermQuad P x - hermQuad (canonicalHorizonGram K h N) x := by
      simp only [hermQuad, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    change 0 < canonicalCriticalClock K N ^ 2 *
      hermQuad (P - canonicalHorizonGram K h N) x at hq
    rw [hsub] at hq
    apply sub_pos.mp
    by_contra! hz
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hz)) hq
  exact eventually_inertia_of_strict_approach hP
    (canonicalHorizonGram_isHermitian K h) (tendsto_canonicalHorizonGram hh hsupp hA hK) hlt

/-- The complete horizon Gram matrix on the canonical critical clock has
eventual inertia `(n₊(P), n₋(P)+n₀(P), 0)`, including every jump threshold. -/
theorem canonicalCriticalClock_horizonGram_inertia {h : ι → ℝ → ℝ} {A K : ℝ}
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hA : 0 ≤ A) (hlin : LinearIndependent ℝ h) (hK : 0 < K) :
    ∀ᶠ N in atTop,
      hermNegIndex (horizonGram tiltedUnitSpline h (canonicalCriticalClock K N) N) =
        hermNegIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h) +
          hermNullIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h) ∧
      hermPosIndex (horizonGram tiltedUnitSpline h (canonicalCriticalClock K N) N) =
        hermPosIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h) ∧
      hermNullIndex (horizonGram tiltedUnitSpline h (canonicalCriticalClock K N) N) = 0 := by
  filter_upwards [canonicalHorizonGram_inertia hh hsupp hA hlin hK,
    eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc : 0 < canonicalCriticalClock K N := by linarith [canonicalCriticalClock_one_le K N]
  have hw : 0 < canonicalCriticalClock K N / N := div_pos hc hN0
  have hs : 0 < (canonicalCriticalClock K N)⁻¹ /
      ∫ u, atomDilate tiltedUnitSpline (canonicalCriticalClock K N / N) u ^ 2 := by
    rw [integral_atomDilate_sq tiltedUnitSpline hw]
    have hM := integral_tiltedUnitSpline_sq_pos
    positivity
  have hn := hN.1
  have hp := hN.2.1
  simp only [canonicalHorizonGram, hermNegIndex_ofReal_smul hs] at hn
  simp only [canonicalHorizonGram, hermPosIndex_ofReal_smul hs] at hp
  have hG : (horizonGram tiltedUnitSpline h (canonicalCriticalClock K N) N).IsHermitian :=
    weilGram_isHermitian _ _
  have hsum := posIndex_add_negIndex_add_nullIndex hG
  have hsumNorm := posIndex_add_negIndex_add_nullIndex (canonicalHorizonGram_isHermitian K h N)
  rw [hN.1, hN.2.1, hN.2.2] at hsumNorm
  exact ⟨hn, hp, by omega⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.canonicalCriticalClock_horizonGram_inertia
