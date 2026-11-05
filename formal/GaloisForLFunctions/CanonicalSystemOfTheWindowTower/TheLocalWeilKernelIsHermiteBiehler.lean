import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ConjugationPreservesThePrecontactWeilSpace

/-!
# A Hermite–Biehler function from the exact local Weil kernel

Fourier evaluation has a nonzero Riesz vector `v_z`. Conjugation exchanges `v_z` and `v_conj(z)`.
The unitary between conjugate evaluation kernels identifies their projected Riesz vectors.
Their squared norms give the strict Hermite–Biehler identity for `(z+i)F(v_i)(z)`.
-/

open Complex
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

variable (a : PrecontactAperture)

/-- Riesz representative of the literal entire Fourier evaluation. -/
def evalVector (z : ℂ) : WeilHilbertBeforeContact a := (eval a z).adjoint 1

theorem inner_evalVector (z : ℂ) (x : WeilHilbertBeforeContact a) :
    inner ℂ (evalVector a z) x = eval a z x := by
  rw [evalVector, ContinuousLinearMap.adjoint_inner_left]
  simp

theorem evalVector_ne_zero (z : ℂ) : evalVector a z ≠ 0 := by
  intro h
  have he := inner_evalVector a z (evaluationNormalizer a z)
  rw [h, inner_zero_left, eval_normalizer] at he
  exact zero_ne_one he

theorem evalVector_self (z : ℂ) :
    eval a z (evalVector a z) = (‖evalVector a z‖ : ℂ) ^ 2 := by
  exact (inner_evalVector a z (evalVector a z)).symm.trans
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := WeilHilbertBeforeContact a) _)

theorem evalVector_symm (w z : ℂ) :
    (starRingEnd ℂ) (eval a w (evalVector a z)) = eval a z (evalVector a w) := by
  rw [← inner_evalVector, ← inner_evalVector]
  exact inner_conj_symm _ _

/-- Polarization of norm preservation gives the conjugated inner product. -/
theorem inner_sharp (x y : WeilHilbertBeforeContact a) :
    inner ℂ (sharp a x) (sharp a y) = (starRingEnd ℂ) (inner ℂ x y) := by
  have hplus : ‖sharp a x + sharp a y‖ = ‖x + y‖ := by
    rw [← map_add, LinearIsometryEquiv.norm_map]
  have hminus : ‖sharp a x - sharp a y‖ = ‖x - y‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hip : sharp a x + I • sharp a y = sharp a (x - I • y) := by
    rw [map_sub, map_smulₛₗ, Complex.conj_I, neg_smul, sub_neg_eq_add]
  have him : sharp a x - I • sharp a y = sharp a (x + I • y) := by
    rw [map_add, map_smulₛₗ, Complex.conj_I, neg_smul, sub_eq_add_neg]
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (E := WeilHilbertBeforeContact a),
    inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (E := WeilHilbertBeforeContact a)]
  change ((‖sharp a x + sharp a y‖ : ℂ) ^ 2 - (‖sharp a x - sharp a y‖ : ℂ) ^ 2 +
      ((‖sharp a x - I • sharp a y‖ : ℂ) ^ 2 -
        (‖sharp a x + I • sharp a y‖ : ℂ) ^ 2) * I) / 4 =
    (starRingEnd ℂ) (((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2 +
      ((‖x - I • y‖ : ℂ) ^ 2 - (‖x + I • y‖ : ℂ) ^ 2) * I) / 4)
  rw [hplus, hminus, hip, him]
  simp only [LinearIsometryEquiv.norm_map]
  simp only [map_div₀, map_add, map_sub, map_mul, map_pow, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  ring

theorem evalVector_sharp (z : ℂ) :
    sharp a (evalVector a z) = evalVector a ((starRingEnd ℂ) z) := by
  apply ext_inner_right ℂ
  intro x
  calc
    inner ℂ (sharp a (evalVector a z)) x =
        inner ℂ (sharp a (evalVector a z)) (sharp a (sharp a x)) := by
          rw [sharp_involutive]
    _ = (starRingEnd ℂ) (eval a z (sharp a x)) := by
      rw [inner_sharp, inner_evalVector]
    _ = eval a ((starRingEnd ℂ) z) x := by
      change (starRingEnd ℂ) (fourier a (sharp a x) z) = _
      rw [fourier_sharp, starRingEnd_self_apply]
      rfl
    _ = inner ℂ (evalVector a ((starRingEnd ℂ) z)) x :=
      (inner_evalVector a _ x).symm

theorem norm_evalVector_conj (z : ℂ) :
    ‖evalVector a ((starRingEnd ℂ) z)‖ = ‖evalVector a z‖ := by
  rw [← evalVector_sharp, LinearIsometryEquiv.norm_map]

/-- The reproducing kernel of the unshifted Weil space. -/
def kernel (w z : ℂ) : ℂ := fourier a (evalVector a w) z

theorem kernel_symm (w z : ℂ) :
    (starRingEnd ℂ) (kernel a w z) = kernel a z w := evalVector_symm a z w

theorem kernel_conj (w z : ℂ) :
    kernel a ((starRingEnd ℂ) w) z = (starRingEnd ℂ) (kernel a w ((starRingEnd ℂ) z)) := by
  rw [kernel, ← evalVector_sharp, fourier_sharp]
  rfl

/-- A scaled orthogonal projection of `v_z` onto the kernel of evaluation at `κ`. -/
def kernelNumerator (κ z : ℂ) : evaluationKernel a κ :=
  ⟨(‖evalVector a κ‖ : ℂ) ^ 2 • evalVector a z -
      eval a κ (evalVector a z) • evalVector a κ, by
    change eval a κ (_ - _) = 0
    rw [map_sub, map_smul, map_smul, evalVector_self]
    simp only [smul_eq_mul]
    ring⟩

theorem kernelNumerator_inner (κ z : ℂ) (x : evaluationKernel a κ) :
    inner ℂ (kernelNumerator a κ z) x =
      (‖evalVector a κ‖ : ℂ) ^ 2 * eval a z x := by
  change inner ℂ ((‖evalVector a κ‖ : ℂ) ^ 2 • evalVector a z -
      eval a κ (evalVector a z) • evalVector a κ) (x : WeilHilbertBeforeContact a) = _
  have hx : eval a κ (x : WeilHilbertBeforeContact a) = 0 := x.property
  rw [inner_sub_left (E := WeilHilbertBeforeContact a),
    inner_smul_left (E := WeilHilbertBeforeContact a),
    inner_smul_left (E := WeilHilbertBeforeContact a),
    inner_evalVector, inner_evalVector, hx]
  simp only [map_pow, Complex.conj_ofReal, mul_zero, sub_zero]

theorem kernelNumerator_inner_pair (κ z w : ℂ) :
    inner ℂ (kernelNumerator a κ z) (kernelNumerator a κ w) =
      (‖evalVector a κ‖ : ℂ) ^ 4 * kernel a w z -
        (‖evalVector a κ‖ : ℂ) ^ 2 * kernel a κ z * kernel a w κ := by
  rw [kernelNumerator_inner]
  change (‖evalVector a κ‖ : ℂ) ^ 2 * eval a z
    ((‖evalVector a κ‖ : ℂ) ^ 2 • evalVector a w -
      eval a κ (evalVector a w) • evalVector a κ) = _
  rw [map_sub, map_smul, map_smul]
  change (‖evalVector a κ‖ : ℂ) ^ 2 *
    ((‖evalVector a κ‖ : ℂ) ^ 2 * kernel a w z - kernel a w κ * kernel a κ z) = _
  ring

theorem kernelNumerator_norm_sq (κ z : ℂ) :
    ‖kernelNumerator a κ z‖ ^ 2 =
      ‖evalVector a κ‖ ^ 4 * ‖evalVector a z‖ ^ 2 -
        ‖evalVector a κ‖ ^ 2 * ‖kernel a κ z‖ ^ 2 := by
  have hi := kernelNumerator_inner a κ z (kernelNumerator a κ z)
  change inner ℂ (kernelNumerator a κ z) (kernelNumerator a κ z) =
    (‖evalVector a κ‖ : ℂ) ^ 2 * eval a z
      ((‖evalVector a κ‖ : ℂ) ^ 2 • evalVector a z -
        eval a κ (evalVector a z) • evalVector a κ) at hi
  rw [map_sub, map_smul, map_smul, evalVector_self, ← evalVector_symm a κ z] at hi
  simp only [smul_eq_mul] at hi
  have hmul := Complex.mul_conj (eval a κ (evalVector a z))
  have hnorm : ‖eval a κ (evalVector a z)‖ = ‖kernel a κ z‖ := by
    rw [← Complex.norm_conj, evalVector_symm]
    rfl
  have hc : (‖kernelNumerator a κ z‖ : ℂ) ^ 2 =
      (‖evalVector a κ‖ : ℂ) ^ 4 * (‖evalVector a z‖ : ℂ) ^ 2 -
        (‖evalVector a κ‖ : ℂ) ^ 2 * (‖kernel a κ z‖ : ℂ) ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := evaluationKernel a κ)] at hi
    rw [Complex.normSq_eq_norm_sq, hnorm, Complex.ofReal_pow] at hmul
    linear_combination hi - (‖evalVector a κ‖ : ℂ) ^ 2 * hmul
  exact_mod_cast hc

/-- Zero-moving intertwines the projected evaluation vectors, including at the two anchors. -/
theorem zeroMove_kernelNumerator (κ z : ℂ) :
    (starRingEnd ℂ) (z - κ) •
        (zeroMove a κ).symm (kernelNumerator a (star κ) z) =
      (starRingEnd ℂ) (z - star κ) • kernelNumerator a κ z := by
  apply ext_inner_right ℂ (E := evaluationKernel a κ)
  intro x
  have hU : inner ℂ ((zeroMove a κ).symm (kernelNumerator a (star κ) z)) x =
      inner ℂ (kernelNumerator a (star κ) z) (zeroMove a κ x) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      ((zeroMove a κ).inner_map_map
        ((zeroMove a κ).symm (kernelNumerator a (star κ) z)) x).symm
  rw [inner_smul_left (E := evaluationKernel a κ),
    inner_smul_left (E := evaluationKernel a κ),
    starRingEnd_self_apply, starRingEnd_self_apply,
    hU, kernelNumerator_inner, kernelNumerator_inner]
  change (z - κ) * (↑‖evalVector a ((starRingEnd ℂ) κ)‖ ^ 2 *
      fourier a (zeroMove a κ x) z) =
    (z - star κ) * (↑‖evalVector a κ‖ ^ 2 * fourier a x z)
  rw [norm_evalVector_conj]
  linear_combination (‖evalVector a κ‖ : ℂ) ^ 2 * zeroMove_fourier a κ z x

theorem kernelNumerator_norm_relation (κ z : ℂ) :
    ‖z - κ‖ ^ 2 * ‖kernelNumerator a (star κ) z‖ ^ 2 =
      ‖z - star κ‖ ^ 2 * ‖kernelNumerator a κ z‖ ^ 2 := by
  have h := congrArg (fun x : evaluationKernel a κ => ‖x‖ ^ 2)
    (zeroMove_kernelNumerator a κ z)
  simpa only [norm_smul, Complex.norm_conj, LinearIsometryEquiv.norm_map, mul_pow] using h

/-- The entire Hermite–Biehler function selected by the anchor `i`. -/
def hermiteBiehler (z : ℂ) : ℂ := (z + I) * kernel a I z

theorem differentiable_hermiteBiehler : Differentiable ℂ (hermiteBiehler a) :=
  (differentiable_id.add_const I).mul (differentiable_fourier a (evalVector a I))

theorem hermiteBiehler_sharp (z : ℂ) :
    (starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z)) =
      (z - I) * kernel a (-I) z := by
  rw [hermiteBiehler, map_mul, map_add, starRingEnd_self_apply, Complex.conj_I]
  rw [← kernel_conj, Complex.conj_I]
  rfl

/-- The local entire function reconstructs the full polarized Weil reproducing kernel. -/
theorem kernel_christoffelDarboux (w z : ℂ) :
    hermiteBiehler a z * (starRingEnd ℂ) (hermiteBiehler a w) -
        (starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z)) *
          hermiteBiehler a ((starRingEnd ℂ) w) =
      2 * I * (‖evalVector a I‖ : ℂ) ^ 2 * ((starRingEnd ℂ) w - z) * kernel a w z := by
  have h := congrArg₂ (fun x y : evaluationKernel a I => inner ℂ x y)
    (zeroMove_kernelNumerator a I z) (zeroMove_kernelNumerator a I w)
  simp only [inner_smul_left (E := evaluationKernel a I),
    inner_smul_right (E := evaluationKernel a I), starRingEnd_self_apply,
    (zeroMove a I).symm.inner_map_map, kernelNumerator_inner_pair,
    show star (I : ℂ) = -I from Complex.conj_I, map_sub, map_add, Complex.conj_I,
    map_neg, neg_neg, sub_neg_eq_add] at h
  have hk : ‖evalVector a (-I)‖ = ‖evalVector a I‖ := by
    simpa only [Complex.conj_I] using norm_evalVector_conj a I
  rw [hk] at h
  have hk0 : (‖evalVector a I‖ : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero a I)))
  have hsharpw : hermiteBiehler a ((starRingEnd ℂ) w) =
      ((starRingEnd ℂ) w + I) * kernel a w (-I) := by
    have he := congrArg (starRingEnd ℂ) (hermiteBiehler_sharp a w)
    simpa only [starRingEnd_self_apply, map_mul, map_sub, Complex.conj_I,
      sub_neg_eq_add, kernel_symm] using he
  rw [hermiteBiehler_sharp, hsharpw, hermiteBiehler, hermiteBiehler,
    map_mul, map_add, Complex.conj_I, kernel_symm]
  apply mul_left_cancel₀ hk0
  linear_combination h

/-- The diagonal kernel identity proves the strict Hermite–Biehler inequality. -/
theorem hermiteBiehler_norm_difference (z : ℂ) :
    ‖hermiteBiehler a z‖ ^ 2 -
        ‖(starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z))‖ ^ 2 =
      4 * z.im * ‖evalVector a I‖ ^ 2 * ‖evalVector a z‖ ^ 2 := by
  have h := kernelNumerator_norm_relation a I z
  simp only [show star (I : ℂ) = -I from Complex.conj_I, sub_neg_eq_add,
    kernelNumerator_norm_sq] at h
  have hk : ‖evalVector a (-I)‖ = ‖evalVector a I‖ := by
    simpa only [Complex.conj_I] using norm_evalVector_conj a I
  rw [hk] at h
  have hd : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  have hkpos : 0 < ‖evalVector a I‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero a I))
  rw [hermiteBiehler_sharp, hermiteBiehler, norm_mul, norm_mul, mul_pow, mul_pow]
  apply (mul_left_cancel₀ (ne_of_gt hkpos))
  linear_combination h + ‖evalVector a I‖ ^ 4 * ‖evalVector a z‖ ^ 2 * hd

theorem hermiteBiehler_strict {z : ℂ} (hz : 0 < z.im) :
    ‖(starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z))‖ <
      ‖hermiteBiehler a z‖ := by
  have hp : 0 < 4 * z.im * ‖evalVector a I‖ ^ 2 * ‖evalVector a z‖ ^ 2 := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hz)
      (sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero a I))))
      (sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero a z)))
  have hd := hermiteBiehler_norm_difference a z
  nlinarith only [hp, hd, norm_nonneg (hermiteBiehler a z),
    norm_nonneg ((starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z)))]

/-- Surjective real evaluation excludes a common real zero of the two entire components. -/
theorem hermiteBiehler_ne_zero_ofReal (x : ℝ) : hermiteBiehler a (x : ℂ) ≠ 0 := by
  intro hE
  have hk0 : (‖evalVector a I‖ : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero a I)))
  have hz0 (z : ℂ) (hz : z ≠ (x : ℂ)) : kernel a (x : ℂ) z = 0 := by
    have h := kernel_christoffelDarboux a (x : ℂ) z
    simp only [Complex.conj_ofReal, hE, map_zero, mul_zero, sub_zero] at h
    have hc : 2 * I * (‖evalVector a I‖ : ℂ) ^ 2 * ((x : ℂ) - z) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) hk0)
        (sub_ne_zero.mpr hz.symm)
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  have hf0 : kernel a (x : ℂ) = fun _ => 0 :=
    Continuous.ext_on (dense_compl_singleton (x : ℂ))
      (differentiable_fourier a (evalVector a (x : ℂ))).continuous continuous_const
      (fun z hz => hz0 z hz)
  exact evalVector_ne_zero a (x : ℂ)
    (eq_zero_of_fourier_eq_zero a _ (fun z => congrFun hf0 z))

#print axioms evalVector_sharp
#print axioms zeroMove_kernelNumerator
#print axioms differentiable_hermiteBiehler
#print axioms kernel_christoffelDarboux
#print axioms hermiteBiehler_norm_difference
#print axioms hermiteBiehler_strict
#print axioms hermiteBiehler_ne_zero_ofReal

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
