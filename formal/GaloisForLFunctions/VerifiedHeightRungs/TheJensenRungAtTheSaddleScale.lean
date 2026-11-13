import GaloisForLFunctions.FiniteFreeProbability.JensenSectorTheorem
import GaloisForLFunctions.VerifiedHeightRungs.JensenEntries
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven
import GaloisForLFunctions.BiScaleUncertainty.WeilLagCriticalDeficitEndpointAndLimitLaw

/-!
# The Jensen rung at the saddle scale `d ≍ T²`

`N_d` is the number of non-real roots of the Jensen polynomial `R_d(Ξ) = Ξ(D) X^d`; a zero of `ξ` has
spectral point `γ + iδ`, `δ = ½ − Re ρ`.

* **Sector criterion** (`jensenNonrealCount_eq_zero_of_sector`). If every zero satisfies
  `(d − 1)δ² ≤ γ²`, then `N_d = 0`.
* **Rung** (`jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width`). If RH holds through `T ≥ 0` and
  `(d − 1) w² ≤ T²`, `w` the zero width, then `N_d = 0`. Since `w ≤ ½`, `d ≤ 4T² + 1` suffices
  (`jensenNonrealCount_eq_zero_of_rhVerifiedThrough_sq`).
* **Unconditionally** `N_d = 0` for `d ≤ 17957`, from the verified height `67`
  (`jensenNonrealCount_eq_zero_of_le`).
* **Sharpness** (`exists_pair_beyond_rung`). For `d > 4T² + 1` a single conjugate pair of height above
  `T` inside the critical strip has a Jensen polynomial with non-real roots: verification through `T`
  and the strip alone give no rung beyond `4T² + 1`.

The Hadamard approximants of `Ξ` are real polynomials whose roots are spectral points of zeros, so
the sector theorem applies to each of them, and the coefficient limit transfers the count.
-/

open Polynomial Filter Topology Complex Set
open GaloisForLFunctions.HTGeometry RHTower FiniteFreeProbability
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.VerifiedHeightRungs

noncomputable section

/-- The Hadamard approximants of `Ξ` have real-rooted Jensen polynomials of degree `d` once every
zero lies in the Jensen sector of degree `d`. -/
theorem splits_diffOp_xiRealApprox_of_sector {d : ℕ}
    (hsec : ∀ q : XiZeroCopy, InJensenSector d (xiSpectralPoint q)) (n : ℕ) :
    (diffOp (DeBruijn.xiRealApprox n) (X ^ d)).Splits := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ[X], t = (DeBruijn.exists_real_xiZeroPoly n).choose := ⟨_, rfl⟩
  have hspec : t.map Complex.ofRealHom =
      DeBruijn.xiZeroPoly (xiPairedCopyFinset (DeBruijn.xiConjClosedFinset n)) := by
    rw [ht]
    exact (DeBruijn.exists_real_xiZeroPoly n).choose_spec
  -- the approximant is normalized at the origin
  have ht0 : t.coeff 0 = 1 := by
    have h := congrArg (eval 0) hspec
    have h2 := eval_map_apply (p := t) (f := Complex.ofRealHom) (0 : ℝ)
    rw [map_zero] at h2
    rw [h2, DeBruijn.eval_xiZeroPoly] at h
    simp only [zero_div, sub_zero, Finset.prod_const_one] at h
    rw [coeff_zero_eq_eval_zero]
    rw [Complex.ofRealHom_eq_coe] at h
    exact_mod_cast h
  -- its roots are spectral points
  have hroots : ∀ ρ : ℂ, (t.map (algebraMap ℝ ℂ)).IsRoot ρ → InJensenSector d ρ := by
    intro ρ hρ
    have h1 : (DeBruijn.xiZeroPoly
        (xiPairedCopyFinset (DeBruijn.xiConjClosedFinset n))).eval ρ = 0 := by
      rw [← hspec]
      exact hρ
    rw [DeBruijn.eval_xiZeroPoly, Finset.prod_eq_zero_iff] at h1
    obtain ⟨q, -, hq⟩ := h1
    have hρq : ρ = xiSpectralPoint q :=
      (div_eq_one_iff_eq (xiSpectralPoint_ne_zero q)).1 (sub_eq_zero.1 hq).symm
    rw [hρq]
    exact hsec q
  rw [DeBruijn.xiRealApprox, ← ht, diffOp_C_mul_left]
  exact (splits_diffOp_X_pow_of_sector d t (by rw [ht0]; exact one_ne_zero) hroots).C_mul _

/-- **Sector criterion for `Ξ`.** If the spectral point `γ + iδ` of every zero of `ξ` satisfies
`(d − 1)δ² ≤ γ²`, then `R_d(Ξ)` has only real roots. -/
theorem jensenNonrealCount_eq_zero_of_sector {d : ℕ}
    (hsec : ∀ q : XiZeroCopy, InJensenSector d (xiSpectralPoint q)) :
    jensenNonrealCount d = 0 := by
  classical
  set S : ℕ → ℝ[X] := fun n => diffOp (DeBruijn.xiRealApprox n) (X ^ d) with hS
  have hSne : ∀ n, S n ≠ 0 := fun n h => by
    have hco := coeff_diffOp_X_pow (DeBruijn.xiRealApprox n) (le_refl d)
    rw [show diffOp (DeBruijn.xiRealApprox n) (X ^ d) = S n from rfl, h, coeff_zero] at hco
    simp only [Nat.sub_self, Nat.descFactorial_zero, Nat.cast_one, mul_one] at hco
    have h0 := eval_zero_xiRealApprox n
    rw [← coeff_zero_eq_eval_zero] at h0
    exact h0 hco.symm
  have hSdeg : ∀ n, (S n).natDegree ≤ d := fun n =>
    (natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d)
  have hcount : ∀ n, nonrealRootCount (S n) ≤ 0 := fun n => by
    rw [nonrealRootCount, (splits_diffOp_xiRealApprox_of_sector hsec n).natDegree_eq_card_roots,
      Nat.sub_self]
  -- the Jensen polynomials of the approximants converge coefficientwise
  rw [jensenNonrealCount_eq]
  refine Nat.le_zero.1 (nonrealRootCount_le_of_tendsto (xiJensenReal_ne_zero d) hSne hcount ?_)
  refine tendstoLocallyUniformly_eval_of_coeff (D := d)
    (fun n => natDegree_map_le.trans (hSdeg n))
    (natDegree_map_le.trans (natDegree_xiJensenReal d).le) fun j => ?_
  simp only [coeff_map]
  rcases le_or_gt j d with hj | hj
  · have hL : (xiJensenReal d).coeff j =
        realTaylorCoeff XiC (d - j) * (d.descFactorial (d - j) : ℝ) := by
      rw [xiJensenReal_eq, jensenRev_eq_sum, finsetSum_coeff, Finset.sum_eq_single (d - j)]
      · rw [coeff_C_mul_X_pow, if_pos (by omega), PowerSeries.coeff_mk]
      · intro i hi hij
        rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.1 hi; omega)]
      · intro h'
        exact absurd (Finset.mem_range.2 (by omega)) h'
    simp only [S, coeff_diffOp_X_pow _ hj, hL, Complex.ofRealHom_eq_coe]
    push_cast
    exact (tendsto_coeff_xiRealApprox (d - j)).mul_const _
  · have h1 : (xiJensenReal d).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_xiJensenReal]; exact hj)
    have h2 : ∀ n, (S n).coeff j = 0 := fun n =>
      coeff_eq_zero_of_natDegree_lt ((hSdeg n).trans_lt hj)
    simp only [h1, h2, map_zero, tendsto_const_nhds_iff]

/-- **Jensen rung, width form.** If RH holds through `T ≥ 0` and `(d − 1) w² ≤ T²` for the zero
width `w = sup |Re ρ − ½|`, then `R_d(Ξ)` has only real roots. -/
theorem jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width {T : ℝ} (hT : 0 ≤ T)
    (hRH : RHVerifiedThrough T) {d : ℕ} (hd : ((d : ℝ) - 1) * zetaZeroWidth ^ 2 ≤ T ^ 2) :
    jensenNonrealCount d = 0 := by
  refine jensenNonrealCount_eq_zero_of_sector fun q => ?_
  rw [InJensenSector]
  rcases le_or_gt |(xiSpectralPoint q).re| T with h | h
  · -- a verified zero is real
    rw [im_xiSpectralPoint_eq_zero hRH q h]
    nlinarith only [sq_nonneg (xiSpectralPoint q).re]
  · -- a zero above `T` has depth at most the width
    have hw : |(xiSpectralPoint q).im| ≤ zetaZeroWidth := by
      rw [im_xiSpectralPoint, abs_sub_comm]
      exact (BiScaleUncertainty.ChebyshevGauge.zetaZeroWidth_le_iff_xiZeroCopy_abs_re_sub_half_le
        zetaZeroWidth_nonneg).1 le_rfl q
    have h1 : (xiSpectralPoint q).im ^ 2 ≤ zetaZeroWidth ^ 2 := by
      rw [← sq_abs (xiSpectralPoint q).im]
      exact pow_le_pow_left₀ (abs_nonneg _) hw 2
    have h2 : T ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by
      rw [← sq_abs (xiSpectralPoint q).re]
      exact pow_le_pow_left₀ hT h.le 2
    rcases le_or_gt ((d : ℝ) - 1) 0 with h0 | h0
    · nlinarith only [h0, sq_nonneg (xiSpectralPoint q).im, sq_nonneg (xiSpectralPoint q).re]
    · exact (mul_le_mul_of_nonneg_left h1 h0.le).trans (hd.trans h2)

/-- **Jensen rung at the saddle scale.** If RH holds through `T ≥ 0` and `d ≤ 4T² + 1`, then
`R_d(Ξ)` has only real roots. -/
theorem jensenNonrealCount_eq_zero_of_rhVerifiedThrough_sq {T : ℝ} (hT : 0 ≤ T)
    (hRH : RHVerifiedThrough T) {d : ℕ} (hd : (d : ℝ) ≤ 4 * T ^ 2 + 1) :
    jensenNonrealCount d = 0 := by
  refine jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width hT hRH ?_
  have hw2 : zetaZeroWidth ^ 2 ≤ 1 / 4 := by
    nlinarith only [zetaZeroWidth_le_half, zetaZeroWidth_nonneg]
  rcases le_or_gt ((d : ℝ) - 1) 0 with h0 | h0
  · nlinarith only [h0, sq_nonneg zetaZeroWidth, sq_nonneg T]
  · nlinarith only [mul_le_mul_of_nonneg_left hw2 h0.le, hd]

/-- **The first `17957` Jensen polynomials of `Ξ` are real-rooted.** -/
theorem jensenNonrealCount_eq_zero_of_le {d : ℕ} (hd : d ≤ 17957) : jensenNonrealCount d = 0 := by
  refine jensenNonrealCount_eq_zero_of_rhVerifiedThrough_sq (T := 67) (by norm_num)
    HadamardBudget.rhVerifiedThrough_sixtySeven ?_
  calc (d : ℝ) ≤ 17957 := by exact_mod_cast hd
    _ = 4 * (67 : ℝ) ^ 2 + 1 := by norm_num

/-- **The rung `4T² + 1` is sharp for zero configurations.** For `d > 4T² + 1` there is a point `ρ`
of height above `T` in the strip `|Im ρ| < ½` whose conjugate pair alone has a Jensen polynomial of
degree `d` with non-real roots. -/
theorem exists_pair_beyond_rung {T : ℝ} (hT : 0 ≤ T) {d : ℕ} (hd : 4 * T ^ 2 + 1 < (d : ℝ)) :
    ∃ ρ : ℂ, T < ρ.re ∧ |ρ.im| < 1 / 2 ∧ ¬ (diffOp (pairSymbol ρ) (X ^ d)).Splits := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by nlinarith only [hd, sq_nonneg T]
  have hd2 : 2 ≤ d := by
    have : (1 : ℝ) < d := by linarith only [hd1]
    exact_mod_cast this
  -- a height `γ` with `T² < γ² < (d − 1)/4`
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (T ^ 2 + ((d : ℝ) - 1) / 4) / 2 := ⟨_, rfl⟩
  have hgT : T ^ 2 < g := by rw [hg]; linarith only [hd]
  have hgd : g < ((d : ℝ) - 1) / 4 := by rw [hg]; linarith only [hd]
  have hg0 : 0 < g := lt_of_le_of_lt (sq_nonneg T) hgT
  -- a depth `δ < ½` with `γ² < (d − 1) δ²`
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (g / ((d : ℝ) - 1) + 1 / 4) / 2 := ⟨_, rfl⟩
  have hge : g / ((d : ℝ) - 1) < 1 / 4 := by
    rw [div_lt_iff₀ hd1]
    linarith only [hgd]
  have he4 : e < 1 / 4 := by rw [he]; linarith only [hge]
  have heg : g / ((d : ℝ) - 1) < e := by rw [he]; linarith only [hge]
  have he0 : 0 < e := lt_trans (div_pos hg0 hd1) heg
  refine ⟨⟨Real.sqrt g, Real.sqrt e⟩, ?_, ?_, ?_⟩
  · exact (Real.lt_sqrt hT).2 hgT
  · rw [abs_of_nonneg (Real.sqrt_nonneg e), show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt he0.le he4
  · have hne : (⟨Real.sqrt g, Real.sqrt e⟩ : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [Complex.zero_re] at this
      exact (Real.sqrt_pos.2 hg0).ne' this
    rw [splits_diffOp_pairSymbol_iff hd2 hne, InJensenSector, Real.sq_sqrt hg0.le,
      Real.sq_sqrt he0.le, not_le]
    rw [div_lt_iff₀ hd1] at heg
    linarith only [heg]

end

end GaloisForLFunctions.VerifiedHeightRungs
