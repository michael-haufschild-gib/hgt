import GaloisForLFunctions.RHTower.DeckCuspidalLaplaceEigenbasis
import GaloisForLFunctions.RHTower.DeckConstantCuspidalOrthogonal

/-!
# Laplace eigenvalues of square-integrable deck eigenfunctions are nonnegative

Let `U ≠ 0` be a `C²` deck-equivariant square-integrable eigenfunction, `y²ΔU = −λU`.  If `λ < 0`
then `λ = s(1 − s)` for a real `s > 1`.  For a nonnegative unit-mass profile `k` positive near `0`,
Selberg's theorem gives `L_k U = h_k(s) U`, while Schur's bound gives `‖L_k‖ ≤ 1`, so `|h_k(s)| ≤ 1`.
But `h_k(s) = ∫ k(u(i,w)) (Im w)^s dμ(w)` exceeds `1`: Bernoulli's inequality
`y^s ≥ 1 + s(y − 1)` (strict for `y ≠ 1`) and the mean value `∫ k(u(i,w)) Im w dμ(w) = h_k(0) = 1`
(the harmonic function `Im` with `s = 0`) give `h_k(s) − 1 = ∫ k (y^s − 1 − s(y − 1)) > 0`.
Hence `λ ≥ 0` (`IsCuspLaplaceEigen.lam_nonneg`), and every eigenvalue of the cuspidal eigenbasis is
nonnegative (`cuspEigenBasis_lam_nonneg`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry HyperbolicPointPairCentre HyperbolicRotationMean
  HyperbolicPowerEigen

noncomputable section

variable {N : ℕ}

/-- The mean value of the harmonic function `Im` against a unit profile: `∫ k(u(i,w)) Im w dμ(w) = 1`. -/
theorem integral_pairKernel_mul_im {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hk0 : ∀ u, 0 ≤ k u) (hmass : ppKernelMass k = 1) (hkR : KernelSupport k R) :
    ∫ w, k (pairU UpperHalfPlane.I w) * w.im = 1 := by
  have h := integral_pairKernel_mul_eigen hkc hkR (powerEigen_smooth 1) (s := 0)
    (fun z => by rw [powerEigen_laplacian]; ring) UpperHalfPlane.I
  rw [powerEigen_I, one_mul, selbergTransform] at h
  simp only [show ∀ w : ℍ, powerEigen 0 w = 1 from fun w => by simp [powerEigen], mul_one] at h
  rw [integral_complex_ofReal, integral_pairKernel_eq_one hkc hk0 hmass, Complex.ofReal_one] at h
  have h2 : ∫ w, ((k (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * powerEigen 1 w =
      ((∫ w, k (pairU UpperHalfPlane.I w) * w.im : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp [powerEigen]
  rw [h2] at h
  exact_mod_cast h

/-- For real `s > 1` and a unit profile positive near `0`, the Selberg transform exceeds `1`. -/
theorem one_lt_selbergTransform_re {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hk0 : ∀ u, 0 ≤ k u) (hmass : ppKernelMass k = 1) (hkR : KernelSupport k R)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hkpos : ∀ u, |u| < R₀ → 0 < k u) {s : ℝ} (hs : 1 < s) :
    1 < (selbergTransform k s).re := by
  set F : ℍ → ℝ := fun w => k (pairU UpperHalfPlane.I w) *
    (w.im ^ s - 1 - s * (w.im - 1)) with hF
  have himc : Continuous fun w : ℍ => w.im := UpperHalfPlane.continuous_im
  have hpowc : Continuous fun w : ℍ => w.im ^ s :=
    himc.rpow_const fun w => Or.inl w.im_pos.ne'
  have hFc : Continuous F :=
    (hkc.comp (continuous_pairU_right _)).mul ((hpowc.sub continuous_const).sub
      (continuous_const.mul (himc.sub continuous_const)))
  have hB : ∀ w : ℍ, 0 ≤ w.im ^ s - 1 - s * (w.im - 1) := fun w => by
    have h := one_add_mul_self_le_rpow_one_add (s := w.im - 1) (by linarith [w.im_pos])
      hs.le
    rw [show 1 + (w.im - 1) = w.im by ring] at h
    linarith
  have hF0 : 0 ≤ F := fun w => mul_nonneg (hk0 _) (hB w)
  have hint_pow : Integrable fun w : ℍ => k (pairU UpperHalfPlane.I w) * w.im ^ s :=
    (integrable_pairKernel_smul' hkc hkR hpowc UpperHalfPlane.I).congr
      (Eventually.of_forall fun w => by simp [smul_eq_mul])
  have hint_im : Integrable fun w : ℍ => k (pairU UpperHalfPlane.I w) * w.im :=
    (integrable_pairKernel_smul' hkc hkR himc UpperHalfPlane.I).congr
      (Eventually.of_forall fun w => by simp [smul_eq_mul])
  have hint_k := integrable_pairKernel_real hkc hkR UpperHalfPlane.I
  have hFi : Integrable F := by
    have : F = fun w => k (pairU UpperHalfPlane.I w) * w.im ^ s - k (pairU UpperHalfPlane.I w) -
        s * (k (pairU UpperHalfPlane.I w) * w.im - k (pairU UpperHalfPlane.I w)) := by
      funext w; simp only [hF]; ring
    rw [this]
    exact (hint_pow.sub hint_k).sub ((hint_im.sub hint_k).const_mul s)
  -- a point where the integrand is positive
  set ε : ℝ := min R₀ 1 with hε
  have hε0 : 0 < ε := lt_min hR₀ one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  set w₀ : ℍ := ⟨((1 + ε : ℝ) : ℂ) * Complex.I, by simp; linarith⟩ with hw₀
  have hw₀im : w₀.im = 1 + ε := by simp [hw₀, UpperHalfPlane.im]
  have hu₀ : pairU UpperHalfPlane.I w₀ = ε ^ 2 / (4 * (1 + ε)) := by
    rw [pairU, Complex.dist_eq, hw₀im, UpperHalfPlane.I_im]
    have : ((UpperHalfPlane.I : ℍ) : ℂ) - (w₀ : ℂ) = ((-ε : ℝ) : ℂ) * Complex.I := by
      simp [hw₀]; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hu₀lt : |pairU UpperHalfPlane.I w₀| < R₀ := by
    rw [hu₀, abs_of_nonneg (by positivity)]
    have h1 : ε ^ 2 / (4 * (1 + ε)) < ε ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    have h2 : ε ^ 2 ≤ ε := by nlinarith
    have h3 : ε ≤ R₀ := min_le_left _ _
    linarith
  have hFw₀ : 0 < F w₀ := by
    refine mul_pos (hkpos _ hu₀lt) ?_
    have h := one_add_mul_self_lt_rpow_one_add (s := w₀.im - 1) (by linarith [w₀.im_pos])
      (by rw [hw₀im]; linarith) hs
    rw [show 1 + (w₀.im - 1) = w₀.im by ring] at h
    linarith
  have hpos : 0 < ∫ w, F w := by
    rw [integral_pos_iff_support_of_nonneg hF0 hFi]
    exact (hFc.isOpen_support).measure_pos _ ⟨w₀, hFw₀.ne'⟩
  have hsplit : ∫ w, F w = (∫ w, k (pairU UpperHalfPlane.I w) * w.im ^ s) - 1 := by
    have e1 : ∫ w, F w = ∫ w, ((k (pairU UpperHalfPlane.I w) * w.im ^ s -
        k (pairU UpperHalfPlane.I w)) - s * (k (pairU UpperHalfPlane.I w) * w.im -
          k (pairU UpperHalfPlane.I w))) :=
      integral_congr_ae (Eventually.of_forall fun w => by simp only [hF]; ring)
    rw [e1, integral_sub (f := fun w => k (pairU UpperHalfPlane.I w) * w.im ^ s -
        k (pairU UpperHalfPlane.I w))
      (g := fun w => s * (k (pairU UpperHalfPlane.I w) * w.im - k (pairU UpperHalfPlane.I w)))
      (hint_pow.sub hint_k) ((hint_im.sub hint_k).const_mul s),
      integral_sub hint_pow hint_k, integral_const_mul, integral_sub hint_im hint_k,
      integral_pairKernel_mul_im hkc hk0 hmass hkR, integral_pairKernel_eq_one hkc hk0 hmass]
    ring
  have hsel : selbergTransform k s = ((∫ w, k (pairU UpperHalfPlane.I w) * w.im ^ s : ℝ) : ℂ) := by
    rw [selbergTransform, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [powerEigen]
    rw [← Complex.ofReal_cpow w.im_pos.le]
    push_cast
    ring
  rw [hsel, Complex.ofReal_re]
  linarith

/-- **Nonnegativity of Laplace eigenvalues** of nonzero square-integrable deck eigenfunctions. -/
theorem IsCuspLaplaceEigen.lam_nonneg {lam : ℝ} {U : ℍ → DeckSpace N}
    (hU : IsCuspLaplaceEigen N lam U) (hU0 : toDeckL2 U hU.memLp ≠ 0) : 0 ≤ lam := by
  by_contra hlam
  push Not at hlam
  set r := Real.sqrt (1 / 4 - lam) with hr
  have hr2 : r ^ 2 = 1 / 4 - lam := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrh : 1 / 2 < r := by nlinarith
  set s : ℝ := 1 / 2 + r with hsdef
  have hs : 1 < s := by rw [hsdef]; linarith
  have hss : s * (1 - s) = lam := by rw [hsdef]; nlinarith
  obtain ⟨P, hP0, hPm, hPpos⟩ := exists_posUnitProfile (R := 1) one_pos
  have hc : Continuous P.toFun := P.contDiff.continuous
  have hEig : ∀ z, ppApply P.toFun U z = selbergTransform P.toFun s • U z := fun z =>
    ppApply_eigen hc P.kernelSupport hU.contDiffOn hU.equivariant (fun z => by
      rw [hU.eigen z]
      congr 1
      rw [← hss]
      push_cast
      ring) z
  have hM : ∀ u, |P.toFun u| ≤ P.pp.bound := P.pp.abs_le
  have hL2 : ppL2 hc hM P.radius_nonneg P.kernelSupport (toDeckL2 U hU.memLp) =
      selbergTransform P.toFun s • toDeckL2 U hU.memLp := by
    rw [ppL2_toDeckL2_eq, ← toDeckL2_smul]
    exact toDeckL2_congr _ _ (Eventually.of_forall fun z => hEig z)
  have hnorm : ‖ppL2 hc hM P.radius_nonneg P.kernelSupport (toDeckL2 U hU.memLp)‖ ≤
      (ppKernelMass P.toFun).toReal * ‖toDeckL2 U hU.memLp‖ :=
    norm_ppLinear_le hc hM P.radius_nonneg P.kernelSupport (toDeckL2 U hU.memLp)
  rw [hL2, norm_smul, hPm, ENNReal.toReal_one, one_mul] at hnorm
  have hFpos : 0 < ‖toDeckL2 U hU.memLp‖ := norm_pos_iff.mpr hU0
  have hle : ‖selbergTransform P.toFun s‖ ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  have hgt := one_lt_selbergTransform_re hc hP0 hPm P.kernelSupport one_pos hPpos hs
  linarith [Complex.re_le_norm (selbergTransform P.toFun s)]

/-- Every eigenvalue of the cuspidal eigenbasis is nonnegative. -/
theorem cuspEigenBasis_lam_nonneg (i : CuspEigenIndex N) : 0 ≤ i.1 := by
  obtain ⟨U, hU, hUb⟩ := cuspEigenBasis_spec i
  refine hU.lam_nonneg ?_
  rw [← hUb]
  intro h0
  have h1 := (cuspEigenBasis N).orthonormal.1 i
  have h2 : (cuspEigenBasis N i : CuspidalL2 N) = 0 := Subtype.ext h0
  rw [h2, norm_zero] at h1
  exact zero_ne_one h1

end

end GaloisForLFunctions.RHTower.DeckPointPair
