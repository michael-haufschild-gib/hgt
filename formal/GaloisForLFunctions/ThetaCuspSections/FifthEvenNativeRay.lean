import GaloisForLFunctions.ThetaCuspSections.FifthEvenThreeAtomRemainder
import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtom
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourThreeAtomModel
import GaloisForLFunctions.RHTower.FiniteDegreeReciprocalPerturbation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllRankNativeTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompensationNeutralAnchor
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The fifth even native source on the scale-five ray

The leading atom pairs retain a Gaussian quadratic reserve. The two remaining
unequal pairs and the infinite tail fit inside that reserve, and the other
pure atoms are positive. An invertible triangular change of coordinates
transfers the resulting strict sign to the native reflected jet matrix.
-/

noncomputable section
open Matrix _root_.RHTower _root_.RHTower.ThetaCuspThreeAtomCauchyTail
open _root_.RHTower.ThetaCuspOddFourThreeAtom
open _root_.RHTower.ThetaCuspGaussianLimit
open _root_.HTGeometry.SignedPoisson
namespace GaloisForLFunctions.ThetaCuspSections.FifthNativeRay
open FifthLeadingPair FifthRemainder FifthFirstAtom

/-- Gaussian congruence normalized by the common first-pair amplitude. -/
def normalizedGram (x : ℝ) (A : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j => A i j/
    (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^(i.val+j.val)))

/-- The complete native fifth even source in normalized Gaussian coordinates. -/
def sourceGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  normalizedGram x (nativeShiftedMatrix 5 0 x)

private def pureMatrix (n : ℕ) (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val)*thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) n n x

private def pureGram (n : ℕ) (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  normalizedGram x (pureMatrix n x)

/-- Triangular change from Gaussian coordinates to native moment coordinates. -/
def nativeBasis (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => gaussianBasis j i/q^i.val

theorem sourceUnit_pos {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) : 0 < sourceUnit x := by
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  unfold sourceUnit
  positivity

theorem normalizedGram_eq_congruence (x : ℝ) (A : Matrix (Fin 5) (Fin 5) ℝ) :
    normalizedGram x A = (1/sourceUnit x) •
      ((nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))ᴴ*A*
        nativeBasis (thetaCuspSingleAtomReflectionScale 1 x)) := by
  ext i j
  simp only [normalizedGram,gaussianGram,Matrix.mul_apply,Matrix.conjTranspose_apply,
    nativeBasis,star_trivial,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [pow_add]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

private theorem normalizedGram_posSemidef {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.PosSemidef) :
    (normalizedGram x A).PosSemidef := by
  rw [normalizedGram_eq_congruence]
  have hK := sourceUnit_pos hq
  exact (hA.conjTranspose_mul_mul_same _).smul (by positivity)

private theorem pureGram_posSemidef {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) {n : ℕ} (hn : 1 ≤ n) :
    (pureGram n x).PosSemidef := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hscale : 5 ≤ thetaCuspSingleAtomReflectionScale n x := by
    rw [scale_atom]
    nlinarith only [hq,hnR,sq_nonneg ((n : ℝ)-1),
      mul_nonneg (sub_nonneg.mpr hq) (sq_nonneg (n : ℝ))]
  exact normalizedGram_posSemidef hq (atom_even_five_posDef hscale).posSemidef

private theorem signed_threeAtom_decomposition (k : ℕ) (x : ℝ) :
    (-1 : ℝ)^k*thetaCuspThreeAtomReflectionJet (2*k) x =
      sourceUnit x*threeAtomOddEntry (thetaCuspSingleAtomReflectionScale 1 x) k+
      ((-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 2 2 x+
        (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 3 3 x) := by
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hpair (a b : ℕ) : (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b x =
      sourceUnit x*((a : ℝ)^2*(b : ℝ)^2*Real.exp (-(((a : ℝ)^2+(b : ℝ)^2)-2)*q)*
        (thetaPairRadialEvenPolynomial ((a : ℝ)^2*(b : ℝ)^2*q^2) k).eval
          (((a : ℝ)^2+(b : ℝ)^2)*q)) := by
    rw [signed_pair_even]
    have he : Real.exp (x-((a : ℝ)^2+(b : ℝ)^2)*q) =
        Real.exp (x-2*q)*Real.exp (-(((a : ℝ)^2+(b : ℝ)^2)-2)*q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    change _ = (4*q^2*Real.exp (x-2*q))*_
    ring
  rw [threeAtomJet_eq_sum]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  have p11 := hpair 1 1
  have p12 := hpair 1 2
  have p21 := hpair 2 1
  have p13 := hpair 1 3
  have p31 := hpair 3 1
  have p23 := hpair 2 3
  have p32 := hpair 3 2
  norm_num at p11 p12 p21 p13 p31 p23 p32
  unfold threeAtomOddEntry
  norm_num
  linear_combination p11+p12+p21+p13+p31+p23+p32

private theorem sourceGram_decomposition {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    sourceGram x =
      gaussianGram (leadingMatrix (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)))+
      remainderGram x+pureGram 2 x+pureGram 3 x := by
  have hK := sourceUnit_pos hq
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  unfold sourceGram pureGram normalizedGram remainderGram omittedPairGram pairGram tailGram
  rw [← gaussianGram_smul,← gaussianGram_smul]
  repeat rw [← gaussianGram_add]
  congr 1
  ext i j
  have ht := signed_threeAtom_decomposition (i.val+j.val) x
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,leadingMatrix,leadingMoment,
    pureMatrix,nativeShiftedMatrix,add_zero]
  unfold threeAtomOddEntry at ht
  simp only [one_mul] at ht
  field_simp [hK.ne',hq0.ne'] at ht ⊢
  linear_combination ht

private theorem leadingGram_coercive {q : ℝ} (hq : 5 ≤ q) (v : Fin 5 → ℝ) :
    (49/1000 : ℝ)*(∑ i, v i^2) ≤
      v ⬝ᵥ (gaussianGram (leadingMatrix q (Real.exp (-3*q))) *ᵥ v) := by
  have h := (source_floor_posSemidef hq).dotProduct_mulVec_nonneg v
  simp only [Matrix.sub_mulVec,dotProduct_sub,star_trivial,Matrix.smul_mulVec,
    Matrix.one_mulVec,dotProduct_smul,smul_eq_mul] at h
  have he : v ⬝ᵥ v=∑ i, v i^2 := by simp only [dotProduct,pow_two]
  rw [he] at h
  linarith only [h]

/-- The complete normalized fifth even source has a uniform positive quadratic floor. -/
theorem sourceGram_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (v : Fin 5 → ℝ) :
    (49/4000 : ℝ)*(∑ i, v i^2) ≤ v ⬝ᵥ (sourceGram x *ᵥ v) := by
  have hl := leadingGram_coercive hq v
  have hr := neg_le_of_abs_le (_root_.RHTower.abs_dotProduct_mulVec_le
    (remainderGram x) (by norm_num : (0 : ℝ) ≤ 147/20000)
    (remainderGram_bound hq) v)
  have hp2 := (pureGram_posSemidef hq (by norm_num : 1 ≤ 2)).dotProduct_mulVec_nonneg v
  have hp3 := (pureGram_posSemidef hq (by norm_num : 1 ≤ 3)).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hp2 hp3
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at hr
  rw [sourceGram_decomposition hq]
  simp only [Matrix.add_mulVec,dotProduct_add]
  linarith only [hl,hr,hp2,hp3]

/-- Retaining the leading mass gives a quadratic reserve growing with the reflection scale. -/
theorem sourceGram_growing_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (v : Fin 5 → ℝ) :
    (((2*thetaCuspSingleAtomReflectionScale 1 x-3)^2/1000-147/4000) : ℝ)*
      (∑ i, v i^2) ≤ v ⬝ᵥ (sourceGram x *ᵥ v) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hm : (2*q-3)^2 ≤ leadingMoment q (Real.exp (-3*q)) 0 := by
    have hb : 0 ≤ 16*q^2+9-30*q := by
      nlinarith only [hq,sq_nonneg (q-5)]
    have hz := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8)
      (Real.exp_pos (-3*q)).le) hb
    rw [show -3*q=-(3*q) by ring] at hz
    norm_num [leadingMoment,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
      radialCoeffs_0_0,radialCoeffs_0_1]
    nlinarith only [hz]
  have hl := (source_reserve_posSemidef hq).dotProduct_mulVec_nonneg v
  simp only [Matrix.sub_mulVec,dotProduct_sub,star_trivial,Matrix.smul_mulVec,
    Matrix.one_mulVec,dotProduct_smul,smul_eq_mul] at hl
  have he : v ⬝ᵥ v=∑ i, v i^2 := by simp only [dotProduct,pow_two]
  rw [he] at hl
  have hmass := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ ∑ i, v i^2 from Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hr := neg_le_of_abs_le (_root_.RHTower.abs_dotProduct_mulVec_le
    (remainderGram x) (by norm_num : (0 : ℝ) ≤ 147/20000)
    (remainderGram_bound hq) v)
  have hp2 := (pureGram_posSemidef hq (by norm_num : 1 ≤ 2)).dotProduct_mulVec_nonneg v
  have hp3 := (pureGram_posSemidef hq (by norm_num : 1 ≤ 3)).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hp2 hp3
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at hr
  rw [sourceGram_decomposition hq]
  simp only [Matrix.add_mulVec,dotProduct_add]
  change ((2*q-3)^2/1000-147/4000)*(∑ i, v i^2) ≤ _
  linarith only [hl,hmass,hr,hp2,hp3]

/-- Strict positivity holds for the complete normalized fifth source on the scale-five ray. -/
theorem sourceGram_posDef {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) : (sourceGram x).PosDef := by
  have hh : (sourceGram x).IsHermitian := by
    unfold sourceGram
    rw [normalizedGram_eq_congruence]
    have hm : ((nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))ᴴ*
        nativeShiftedMatrix 5 0 x*nativeBasis (thetaCuspSingleAtomReflectionScale 1 x)).IsHermitian := by
      apply Matrix.isHermitian_conjTranspose_mul_mul
      rw [Matrix.IsHermitian]
      ext i j
      simp [nativeShiftedMatrix,Nat.add_comm]
    exact hm.smul (by rfl)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hh fun v hv => ?_
  have hs : 0 < ∑ i, v i^2 := by
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i,Finset.mem_univ i,?_⟩
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hi) 2
  have hp : 0 < (49/4000 : ℝ)*(∑ i, v i^2) := mul_pos (by norm_num) hs
  simpa only [star_trivial] using hp.trans_le (sourceGram_coercive hq v)

private theorem nativeBasis_triangular (q : ℝ) : (nativeBasis q).BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num [nativeBasis,gaussianBasis]

private theorem nativeBasis_diagonal_pos {q : ℝ} (hq : 0 < q) (i : Fin 5) :
    0 < nativeBasis q i i := by
  have hb : 0 < gaussianBasis i i := by fin_cases i <;> norm_num [gaussianBasis]
  exact div_pos hb (pow_pos hq _)

theorem nativeBasis_det_pos {q : ℝ} (hq : 0 < q) : 0 < (nativeBasis q).det := by
  rw [Matrix.det_of_upperTriangular (nativeBasis_triangular q)]
  exact Finset.prod_pos fun i _ => nativeBasis_diagonal_pos hq i

private theorem nativeBasis_inverse {q : ℝ} (hq : 0 < q) :
    nativeBasis q*(nativeBasis q)⁻¹=1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (nativeBasis_det_pos hq).ne')

/-- The complete native fifth even reflected-jet matrix is positive from scale five onward. -/
theorem native_even_five_posDef {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (nativeShiftedMatrix 5 0 x).PosDef := by
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hp := (sourceGram_posDef hq).smul (sourceUnit_pos hq)
  have he : sourceUnit x • sourceGram x =
      (nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))ᴴ*nativeShiftedMatrix 5 0 x*
        nativeBasis (thetaCuspSingleAtomReflectionScale 1 x) := by
    unfold sourceGram
    rw [normalizedGram_eq_congruence,smul_smul]
    have hK := sourceUnit_pos hq
    rw [show sourceUnit x*(1/sourceUnit x)=1 by field_simp [hK.ne']]
    exact one_smul _ _
  rw [he] at hp
  have hinj : Function.Injective ((nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))⁻¹).mulVec := by
    intro v w h
    have hh := congrArg (fun u => nativeBasis (thetaCuspSingleAtomReflectionScale 1 x) *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec,nativeBasis_inverse hq0,Matrix.one_mulVec] using hh
  have hb := hp.conjTranspose_mul_mul_same hinj
  have hback : ((nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))⁻¹)ᴴ*
      ((nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))ᴴ*nativeShiftedMatrix 5 0 x*
        nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))*
      (nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))⁻¹=nativeShiftedMatrix 5 0 x := by
    calc
      _ = (nativeBasis (thetaCuspSingleAtomReflectionScale 1 x)*
          (nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))⁻¹)ᴴ*
          nativeShiftedMatrix 5 0 x*
          (nativeBasis (thetaCuspSingleAtomReflectionScale 1 x)*
            (nativeBasis (thetaCuspSingleAtomReflectionScale 1 x))⁻¹) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [nativeBasis_inverse hq0]; simp
  rwa [hback] at hb

/-- The unique positive compensation zero has a positive definite native fifth section. -/
theorem exists_strict_compensation_neutral_center :
    ∃ τ : ℝ, 0 < τ ∧ thetaCuspCenterCompensationSource τ=0 ∧
      (nativeShiftedMatrix 5 0 τ).PosDef ∧
      ∀ x : ℝ, 0 ≤ x → (thetaCuspCenterCompensationSource x=0 ↔ x=τ) := by
  obtain ⟨τ,hτ,hq,_,hs⟩ := exists_thetaCuspCompensationNeutralAnchor
  exact ⟨τ,hτ,(hs τ hτ.le).2.1.mpr rfl,native_even_five_posDef hq.le,
    fun x hx => (hs x hx).2.1⟩


end GaloisForLFunctions.ThetaCuspSections.FifthNativeRay
