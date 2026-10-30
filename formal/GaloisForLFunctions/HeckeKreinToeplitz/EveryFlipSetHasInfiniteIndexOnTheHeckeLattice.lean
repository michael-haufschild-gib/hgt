import GaloisForLFunctions.HeckeKreinToeplitz.OnTheFiniteStratumEveryFlipHasInfiniteIndex
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryLowConductorSeesTheFlipSet
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.RHTower.BlindSymbolSlackPrimePowerPeriodization
import GaloisForLFunctions.RHTower.WeilFullConeSpectralConsistency
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing
import GaloisForLFunctions.HeckeKreinToeplitz.TheMarginIsTheWidthOfTheIndexOneWindow

/-!
# Every flip set has infinite index on the Hecke lattice

The Weil kernel of a weight `λ` on `ℚ_{>0}` (`weightKernel λ g`) is real for every real test: the
pole and prime parts are real, and the archimedean integral equals its conjugate because the Fourier
transform of a real function is conjugate-symmetric and the Gamma bracket is even
(`im_weilFullFunctional_ofReal`). Its Gram matrix on the horizon `{1, …, N}` is the twisted
complete Weil matrix of the atomic test `g`: both are `Re W_λ` of the combined test
(`hermQuad_gram_weightKernel_horizon`).

The conductor blocks give the `S`-flipped complete Weil matrix at large overlap any prescribed number
of negative eigenvalues (`exists_overlap_flip_negIndex_ge`). Their eigenvectors are real, the Gram
matrix is real, so complex combinations split into real and imaginary parts and stay negative.
Hence (`iSup_negIndex_weightKernel_finiteFlip_eq_top`)

`sup_g κ(K_{ω_S, g}) = ∞`

unconditionally, over real `C²` tests of compact support, for every nonempty finite set of primes
`S`. For `ζ` the same supremum is the number of zeros right of the line. A ceiling on the Weil-kernel
index that is uniform over test functions is therefore selective against every finite flip set:
it fails for the twins and holds for `ζ` exactly on the finite stratum.
-/

open Complex Finset Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate Real RealInnerProductSpace
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx weilGram hermQuad_weilGram)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (PrimeHorizonIndex
  primeHorizonExtension twistedCompleteWeilMatrix twistedCompleteWeilMatrix_isHermitian
  inner_twistedCompleteWeilMatrix finiteFlipWeight exists_overlap_flip_negIndex_ge atomDilate_facts)
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis (weilQuadTw atomDilate
  integral_atomDilate_sq tiltedUnitSpline contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
  integral_tiltedUnitSpline_sq_pos)
open GaloisForLFunctions.ArithmeticElectrostatics (atomicTest)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### Realness -/

/-- The Fourier transform of a real function is conjugate-symmetric. -/
theorem paperFT_ofReal_neg (r : ℝ → ℝ) (t : ℝ) :
    paperFT (fun u => (r u : ℂ)) ((-t : ℝ) : ℂ) = conj (paperFT (fun u => (r u : ℂ)) (t : ℂ)) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1
  funext u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **The explicit-formula functional is real on real tests.** -/
theorem im_weilFullFunctional_ofReal (lam : ℕ → ℝ) (r : ℝ → ℝ) :
    (RHTower.weilFullFunctional lam (fun u => (r u : ℂ))).im = 0 := by
  rw [RHTower.WeilSpectral.weilFullFunctional_eq_parts]
  have hpole : ∀ y : ℝ, (paperFT (fun u => (r u : ℂ)) (I * y)).im = 0 := by
    intro y
    have h : paperFT (fun u => (r u : ℂ)) (I * y) =
        ((∫ u : ℝ, r u * Real.exp (-(y * u))) : ℝ) := by
      unfold paperFT
      rw [← integral_complex_ofReal]
      congr 1
      funext u
      push_cast
      rw [show I * (I * (y : ℂ)) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) by
        push_cast; linear_combination (y * u : ℂ) * Complex.I_sq, ← Complex.ofReal_exp]
      push_cast
      ring
    rw [h, Complex.ofReal_im]
  have hp1 : (paperFT (fun u => (r u : ℂ)) (I / 2)).im = 0 := by
    have := hpole (1 / 2); rwa [show I * ((1 / 2 : ℝ) : ℂ) = I / 2 by push_cast; ring] at this
  have hp2 : (paperFT (fun u => (r u : ℂ)) (-I / 2)).im = 0 := by
    have := hpole (-1 / 2); rwa [show I * ((-1 / 2 : ℝ) : ℂ) = -I / 2 by push_cast; ring] at this
  have hprime : (RHTower.WeilSpectral.primePart lam (fun u => (r u : ℂ))).im = 0 := by
    have h : RHTower.WeilSpectral.primePart lam (fun u => (r u : ℂ)) =
        ((∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (r (Real.log n) + r (-Real.log n)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum, RHTower.WeilSpectral.primePart]
      congr 1
      funext n
      push_cast
      ring
    rw [h, Complex.ofReal_im]
  have harch : (RHTower.WeilSpectral.archPart (fun u => (r u : ℂ))).im = 0 := by
    have hJ : conj (∫ t : ℝ, paperFT (fun u => (r u : ℂ)) (t : ℂ) * (EF.gammaBracket t : ℂ)) =
        ∫ t : ℝ, paperFT (fun u => (r u : ℂ)) (t : ℂ) * (EF.gammaBracket t : ℂ) := by
      rw [← integral_conj]
      have h1 : (fun t : ℝ => conj (paperFT (fun u => (r u : ℂ)) (t : ℂ) *
          (EF.gammaBracket t : ℂ))) = fun t : ℝ =>
            paperFT (fun u => (r u : ℂ)) ((-t : ℝ) : ℂ) * (EF.gammaBracket (-t) : ℂ) := by
        funext t
        rw [map_mul, Complex.conj_ofReal, paperFT_ofReal_neg,
          RHTower.BlindPrimePowerSlack.gammaBracket_neg]
      rw [h1]
      exact integral_comp_neg (fun t : ℝ => paperFT (fun u => (r u : ℂ)) (t : ℂ) *
        (EF.gammaBracket t : ℂ))
    have hJim := congrArg Complex.im hJ
    rw [Complex.conj_im] at hJim
    rw [RHTower.WeilSpectral.archPart, Complex.mul_im,
      show (∫ t : ℝ, paperFT (fun u => (r u : ℂ)) (t : ℂ) * (EF.gammaBracket t : ℂ)).im = 0 by
        linarith,
      show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
    simp
  simp only [RHTower.WeilSpectral.polePart, Complex.add_im, Complex.sub_im, hp1, hp2, hprime, harch]
  norm_num

/-- **The Weil kernel of a weight is real on real tests.** -/
theorem im_weightKernel (lam : ℕ → ℝ) (g : ℝ → ℝ) (u : HeckeLattice) :
    (weightKernel lam g u).im = 0 := by
  have h : EF.weilTest (cx g) (shiftTest (scale heckeLogScale u) (cx g)) =
      fun x => ((RHTower.crossCorr g g (x + scale heckeLogScale u) : ℝ) : ℂ) :=
    funext fun x => weilTest_shift_eq_crossCorr g _ x
  rw [weightKernel, h]
  exact im_weilFullFunctional_ofReal lam _

/-! ### The Gram matrix on the horizon -/

/-- The Gram matrix of the weight kernel on `{1, …, N}` is the Weil Gram matrix of the translates. -/
theorem gram_weightKernel_horizon (lam : ℕ → ℝ) (g : ℝ → ℝ) (N : ℕ) :
    gram (weightKernel lam g) (horizonPoint N) =
      weilGram lam fun n : PrimeHorizonIndex N => shiftTest (Real.log (n : ℕ)) (cx g) := by
  ext a b
  have ha : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast (mem_Icc.mp a.2).1
  have hb : (0 : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast (mem_Icc.mp b.2).1
  have hscale : scale heckeLogScale ((horizonPoint N a)⁻¹ * horizonPoint N b) =
      Real.log (b : ℕ) - Real.log (a : ℕ) := by
    rw [scale_mul, scale_inv, scale_heckeLogScale, scale_heckeLogScale]
    simp only [horizonPoint]
    push_cast
    ring
  have h0 : shiftTest 0 (cx g) = cx g := funext fun v => by
    simp [ArithmeticCastelnuovoSeveri.translate]
  simp only [gram, weightKernel, weilGram]
  rw [hscale]
  congr 1
  funext x
  have hL := ArithmeticCastelnuovoSeveri.weilTest_translate 0 (Real.log (b : ℕ) - Real.log (a : ℕ))
    (cx g) (cx g) x
  rw [h0] at hL
  rw [hL, ArithmeticCastelnuovoSeveri.weilTest_translate]
  congr 1
  ring

/-- **The real form of the Gram matrix is the twisted Weil form of the atomic test.** -/
theorem hermQuad_gram_weightKernel_horizon (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (N : ℕ) (y : PrimeHorizonIndex N → ℝ) :
    hermQuad (gram (weightKernel lam g) (horizonPoint N)) (fun n => (y n : ℂ)) =
      weilQuadTw lam (atomicTest N (fun n => if h : n ∈ Icc 1 N then y ⟨n, h⟩ else 0) g) := by
  rw [gram_weightKernel_horizon, hermQuad_weilGram lam _
    (fun n => ArithmeticCastelnuovoSeveri.translate_contDiff
      (ArithmeticCastelnuovoSeveri.cx_contDiff hg) _)
    (fun n => ArithmeticCastelnuovoSeveri.translate_hasCompactSupport
      (ArithmeticCastelnuovoSeveri.cx_hasCompactSupport hgc) _)]
  have hF : (∑ n : PrimeHorizonIndex N, conj ((y n : ℂ)) • shiftTest (Real.log (n : ℕ)) (cx g)) =
      fun u => ((atomicTest N (fun n => if h : n ∈ Icc 1 N then y ⟨n, h⟩ else 0) g u : ℝ) : ℂ) := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.conj_ofReal, atomicTest,
      ArithmeticCastelnuovoSeveri.translate, cx]
    push_cast
    rw [← Finset.sum_coe_sort (Icc 1 N)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [dif_pos n.2]
  rw [hF]
  rfl

/-- On a matrix with real entries, the form of `α + iβ` is the sum of the forms of `α` and `β`. -/
theorem hermQuad_real_add_imag {ι : Type*} [Fintype ι] {H : Matrix ι ι ℂ}
    (hH : ∀ i j, (H i j).im = 0) (α β : ι → ℝ) :
    hermQuad H (fun i => (α i : ℂ) + (β i : ℂ) * I) =
      hermQuad H (fun i => (α i : ℂ)) + hermQuad H (fun i => (β i : ℂ)) := by
  simp only [hermQuad, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hHij : H i j = ((H i j).re : ℂ) := Complex.ext rfl (by simp [hH i j])
  rw [hHij]
  simp only [RCLike.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
    Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
    Complex.mul_im, Complex.neg_re, Complex.neg_im]
  ring

/-! ### Infinite index -/

/-- On the span of the negative eigenvectors of a real symmetric matrix the form is negative. -/
theorem inner_sum_negEigenvectors_neg {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}
    (hA : A.IsHermitian) (γ : (univ.filter fun i => hA.eigenvalues i < 0) → ℝ) (hγ : γ ≠ 0) :
    ⟪Matrix.toEuclideanLin A (∑ j, γ j • hA.eigenvectorBasis (j : I)),
      ∑ j, γ j • hA.eigenvectorBasis (j : I)⟫ < 0 := by
  set J := univ.filter fun i => hA.eigenvalues i < 0
  set x := ∑ j : J, γ j • hA.eigenvectorBasis (j : I)
  have hcoord : ∀ i, ⟪x, hA.eigenvectorBasis i⟫ = if h : i ∈ J then γ ⟨i, h⟩ else 0 := by
    intro i
    simp only [x, sum_inner, real_inner_smul_left]
    have hb : ∀ j : J, ⟪hA.eigenvectorBasis (j : I), hA.eigenvectorBasis i⟫ =
        if (j : I) = i then 1 else 0 := fun j =>
      orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal _ _
    simp only [hb, mul_ite, mul_one, mul_zero]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩ (fun j _ hj => if_neg fun h => hj (Subtype.ext h))
        (fun h => absurd (mem_univ _) h), if_pos rfl]
    · exact Finset.sum_eq_zero fun j _ => if_neg fun h => hi (h ▸ j.2)
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hγ
  have hj : γ j₀ ≠ 0 := hj₀
  rw [hermitianEnergy_eq_sum hA]
  calc ∑ i, hA.eigenvalues i * ⟪x, hA.eigenvectorBasis i⟫ ^ 2 < ∑ _i : I, (0 : ℝ) := by
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j₀, mem_univ _, ?_⟩
        · rw [hcoord]
          split_ifs with hi
          · exact mul_nonpos_of_nonpos_of_nonneg (mem_filter.mp hi).2.le (sq_nonneg _)
          · simp
        · rw [hcoord, dif_pos j₀.2]
          exact mul_neg_of_neg_of_pos (mem_filter.mp j₀.2).2
            (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj)))
    _ = 0 := sum_const_zero

/-- A complex vector `α + iβ` with real `α, β` in a negative real subspace of a real Hermitian form
is negative unless it vanishes. -/
theorem hermQuad_complexify_neg {ι κ : Type*} [Fintype ι] [Fintype κ] {H : Matrix ι ι ℂ}
    (hH : ∀ i j, (H i j).im = 0) (v : κ → ι → ℝ)
    (hv : ∀ γ : κ → ℝ, γ ≠ 0 → hermQuad H (fun m => ((∑ j, γ j * v j m : ℝ) : ℂ)) < 0)
    (a : κ → ℂ) (ha : a ≠ 0) :
    hermQuad H (fun m => ∑ j, a j * (v j m : ℂ)) < 0 := by
  have hsplit : (fun m => ∑ j, a j * (v j m : ℂ)) = fun m =>
      ((∑ j, (a j).re * v j m : ℝ) : ℂ) + ((∑ j, (a j).im * v j m : ℝ) : ℂ) * I := by
    funext m
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Complex.re_add_im (a j)]
    ring
  have hzero : hermQuad H (fun m => ((∑ j, (0 : κ → ℝ) j * v j m : ℝ) : ℂ)) = 0 := by
    simp [hermQuad]
  rw [hsplit, hermQuad_real_add_imag hH]
  by_cases hre : (fun j => (a j).re) = 0
  · have him : (fun j => (a j).im) ≠ 0 := fun him =>
      ha (funext fun j => Complex.ext (congrFun hre j) (congrFun him j))
    have h0 : hermQuad H (fun m => ((∑ j, (a j).re * v j m : ℝ) : ℂ)) = 0 := by
      rw [← hzero]; congr 3; funext m; congr 1; exact congrArg _ (funext fun j => by
        rw [show (a j).re = 0 from congrFun hre j]; rfl)
    linarith [hv _ him]
  · by_cases him : (fun j => (a j).im) = 0
    · have h0 : hermQuad H (fun m => ((∑ j, (a j).im * v j m : ℝ) : ℂ)) = 0 := by
        rw [← hzero]; congr 3; funext m; congr 1; exact congrArg _ (funext fun j => by
          rw [show (a j).im = 0 from congrFun him j]; rfl)
      linarith [hv _ hre]
    · linarith [hv _ hre, hv _ him]

/-- **Every nonempty finite flip set has infinite index over tests.** For every `n` there is a real
`C²` test of compact support whose `S`-flipped Weil kernel on `ℚ_{>0}` has at least `n` negative
squares. -/
theorem exists_test_le_negIndex_weightKernel_finiteFlip {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) (n : ℕ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (n : ℕ∞) ≤ negIndex (weightKernel (finiteFlipWeight S) g) := by
  classical
  obtain ⟨c, hc, hev⟩ := exists_overlap_flip_negIndex_ge contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hS hne n
  obtain ⟨N, hN, hN1⟩ := ((hev c le_rfl).and (eventually_ge_atTop 1)).exists
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN1)
  obtain ⟨hgd, -, hgc⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  have hG0 : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  set hA := twistedCompleteWeilMatrix_isHermitian (finiteFlipWeight S) tiltedUnitSpline c N
  set J := univ.filter fun i => hA.eigenvalues i < 0
  set H := gram (weightKernel (finiteFlipWeight S) (atomDilate tiltedUnitSpline (c / N)))
    (horizonPoint N)
  -- the real span of the negative eigenvectors is negative for the Gram form
  have hv : ∀ γ : J → ℝ, γ ≠ 0 → hermQuad H (fun m => ((∑ j, γ j *
      hA.eigenvectorBasis (j : PrimeHorizonIndex N) m : ℝ) : ℂ)) < 0 := by
    intro γ hγ
    have hx := inner_sum_negEigenvectors_neg hA γ hγ
    rw [inner_twistedCompleteWeilMatrix contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hc hN1]
      at hx
    have hq := (div_neg_iff.mp hx).resolve_left fun h => absurd h.2 (not_lt.mpr hG0.le)
    rw [hermQuad_gram_weightKernel_horizon _ hgd hgc N]
    convert hq.1 using 3
    funext k
    unfold primeHorizonExtension
    split_ifs <;> simp
  let L : (J → ℂ) →ₗ[ℂ] (PrimeHorizonIndex N → ℂ) :=
    { toFun := fun a m => ∑ j : J, a j * ((hA.eigenvectorBasis (j : PrimeHorizonIndex N) m : ℝ) : ℂ)
      map_add' := by intro a b; funext m; simp only [Pi.add_apply, add_mul, sum_add_distrib]
      map_smul' := by
        intro t a; funext m
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc] }
  have hcard := card_le_hermNegIndex_of_forall_neg H L
    (hermQuad_complexify_neg (fun i j => im_weightKernel _ _ _)
      (fun j m => hA.eigenvectorBasis (j : PrimeHorizonIndex N) m) hv)
  refine ⟨_, hgd, hgc, ?_⟩
  calc (n : ℕ∞) ≤ (Fintype.card J : ℕ∞) := by rw [Fintype.card_coe]; exact_mod_cast hN
    _ ≤ (hermNegIndex H : ℕ∞) := by exact_mod_cast hcard
    _ ≤ _ := hermNegIndex_gram_le_negIndex _ _

/-- **`sup_g κ(K_{ω_S, g}) = ∞`.** Over real `C²` tests of compact support, the Weil-kernel index of
every nonempty finite flip set is unbounded. -/
theorem iSup_negIndex_weightKernel_finiteFlip_eq_top {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) :
    (⨆ (g : ℝ → ℝ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g),
      negIndex (weightKernel (finiteFlipWeight S) g)) = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  obtain ⟨g, hg, hgc, h⟩ := exists_test_le_negIndex_weightKernel_finiteFlip hS hne n
  exact h.trans (le_iSup₂ (f := fun (g : ℝ → ℝ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g) =>
    negIndex (weightKernel (finiteFlipWeight S) g)) g ⟨hg, hgc⟩)

end GaloisForLFunctions.HeckeKreinToeplitz
