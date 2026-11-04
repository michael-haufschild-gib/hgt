import GaloisForLFunctions.ThetaCuspSections.FifthEvenOriginObstruction
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Coupled zero-flux repair of the fifth even theta source

Two source loads annihilate the scale-seven direction. Their common kernel
is positive at the origin, so a positive coefficient repairs the full origin
form. Equal coefficients fail globally. An explicit unequal pair remains
positive near the origin and cofinally, preserving every integrated entry.
The sixth-degree directional capacity excludes large first coupled loads.
A smaller pair passes both Hermite tests but fails the full Schur direction,
also at every sufficiently small positive aperture.
-/

noncomputable section
open Matrix Filter Topology MeasureTheory Set
open RHTower RHTower.ThetaCuspGaussianLimit
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveCoherent
open EvenFiveOrigin

/-- The two coupled linear functionals. -/
def loadRows : Matrix (Fin 2) (Fin 5) ℝ :=
  !![0,0,1,420,0; 0,0,0,1,1568]

/-- Positive semidefinite correction annihilating the scale-seven vector. -/
def load : Matrix (Fin 5) (Fin 5) ℝ := loadRowsᴴ * loadRows

/-- The native fifth block with its coupled source correction. -/
def repair (C x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 x + (C * thetaCuspCenterCompensationSource x) • load

private def complement : Matrix (Fin 5) (Fin 2) ℝ :=
  !![0,0; 0,0; 1,-420; 0,1; 0,0]

private def basis : Matrix (Fin 5) (Fin 3 ⊕ Fin 2) ℝ :=
  fromCols coherentKernelBasis complement

private def inverseBasis : Matrix (Fin 3 ⊕ Fin 2) (Fin 5) ℝ :=
  fromRows !![1,0,0,0,0; 0,1,0,0,0; 0,0,0,0,-1568] loadRows

private theorem basis_inverse : basis * inverseBasis = 1 := by
  rw [basis, inverseBasis, fromCols_mul_fromRows]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coherentKernelBasis, complement, loadRows, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Matrix.one_apply]

private theorem loadRows_basis : loadRows * basis = fromCols 0 1 := by
  rw [basis, mul_fromCols]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [loadRows, coherentKernelBasis, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [loadRows, complement, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
        Matrix.one_apply]

private theorem native_hermitian (x : ℝ) : (nativeShiftedMatrix 5 0 x).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [nativeShiftedMatrix, add_comm]

private def border (x : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  coherentKernelBasisᴴ * nativeShiftedMatrix 5 0 x * complement

private def tail (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  complementᴴ * nativeShiftedMatrix 5 0 x * complement

/-- The two remaining source coordinates after eliminating the positive kernel. -/
def schur (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  tail x - (border x)ᴴ * (coherentKernel x)⁻¹ * border x

/-- Sum of absolute entries controlling the two-dimensional Schur form. -/
def schurBound : ℝ := |schur 0 0 0| + |schur 0 0 1| + |schur 0 1 1|

/-- A positive coefficient determined entirely by the actual origin source. -/
def coefficient : ℝ :=
  (schurBound + thetaCuspFullSource 0 ^ 2) / thetaCuspFullSource 0 ^ 2

private theorem schur_hermitian (x : ℝ) : (schur x).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · exact Matrix.isHermitian_conjTranspose_mul_mul complement (native_hermitian x)
  · exact Matrix.isHermitian_conjTranspose_mul_mul (border x)
      (Matrix.isHermitian_conjTranspose_mul_mul coherentKernelBasis (native_hermitian x)).inv

private theorem native_block (x : ℝ) : basisᴴ * nativeShiftedMatrix 5 0 x * basis =
    fromBlocks (coherentKernel x) (border x) (border x)ᴴ (tail x) := by
  rw [basis, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
  simp only [coherentKernel, border, tail, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    show (nativeShiftedMatrix 5 0 x)ᴴ = nativeShiftedMatrix 5 0 x from native_hermitian x,
    Matrix.mul_assoc]

private theorem load_block : basisᴴ * load * basis =
    fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have he : basisᴴ * load * basis = (loadRows * basis)ᴴ * (loadRows * basis) := by
    simp only [load, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, loadRows_basis, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
  simp

/-- The correction is positive semidefinite. -/
theorem load_posSemidef : load.PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self loadRows

/-- The source-selected coefficient is strictly positive. -/
theorem coefficient_pos : 0 < coefficient := by
  have hp := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  apply div_pos _ hp
  exact add_pos_of_nonneg_of_pos (by unfold schurBound; positivity) hp

private theorem two_posDef (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsHermitian)
    (p : ℝ) (hp : 0 < p) :
    (S + (3 * (|S 0 0| + |S 0 1| + |S 1 1| + p)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  let t := 3 * (|S 0 0| + |S 0 1| + |S 1 1| + p)
  have hs : S 1 0 = S 0 1 := by
    have h := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q 0 1) hS
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have h0 : |S 0 1| < S 0 0 + t := by
    dsimp [t]
    linarith only [neg_le_abs (S 0 0), abs_nonneg (S 0 0), abs_nonneg (S 0 1), abs_nonneg (S 1 1), hp]
  have h1 : |S 0 1| < S 1 1 + t := by
    dsimp [t]
    linarith only [neg_le_abs (S 1 1), abs_nonneg (S 0 0), abs_nonneg (S 0 1), abs_nonneg (S 1 1), hp]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hS.add ((Matrix.isHermitian_one).smul (by simp [IsSelfAdjoint])))
  intro y hy
  have hxy : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    ext i
    fin_cases i <;> simp [h]
  have hc : 0 ≤ |S 0 1| * ((y 0)^2 + (y 1)^2) + 2*S 0 1*y 0*y 1 := by
    by_cases hb : 0 ≤ S 0 1
    · rw [abs_of_nonneg hb]
      nlinarith only [mul_nonneg hb (sq_nonneg (y 0+y 1))]
    · rw [abs_of_neg (lt_of_not_ge hb)]
      nlinarith only [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hb)) (sq_nonneg (y 0-y 1))]
  have hd : 0 < (S 0 0+t-|S 0 1|)*(y 0)^2 + (S 1 1+t-|S 0 1|)*(y 1)^2 := by
    rcases hxy with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h0) (sq_pos_of_ne_zero h))
        (mul_nonneg (sub_pos.mpr h1).le (sq_nonneg _))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_pos.mpr h0).le (sq_nonneg _))
        (mul_pos (sub_pos.mpr h1) (sq_pos_of_ne_zero h))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Fin.isValue, Fin.reduceEq, if_true, if_false, mul_one, mul_zero, add_zero, hs]
  change 0 < y 0*((S 0 0+t)*y 0+S 0 1*y 1)+y 1*(S 0 1*y 0+(S 1 1+t)*y 1)
  nlinarith only [hc, hd]


private theorem repair_block (C x : ℝ) : basisᴴ * repair C x * basis =
    fromBlocks (coherentKernel x) (border x) (border x)ᴴ
      (tail x + (C * thetaCuspCenterCompensationSource x) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  simp only [repair, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    native_block, load_block]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

/-- Both coupled loads repair the full actual origin form. -/
theorem repair_zero_posDef : (repair coefficient 0).PosDef := by
  let A := coherentKernel 0
  let B := border 0
  let D := tail 0 + (coefficient * thetaCuspCenterCompensationSource 0) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have hA : A.PosDef := coherentKernel_zero_posDef
  letI : Invertible A := hA.isUnit.invertible
  have he : coefficient * thetaCuspCenterCompensationSource 0 =
      3 * (schurBound + thetaCuspFullSource 0 ^ 2) := by
    unfold coefficient thetaCuspCenterCompensationSource
    simp only [mul_zero, zero_mul, add_zero]
    field_simp [(thetaCuspFullSource_pos_all 0).ne']
  have hS : (D-Bᴴ*A⁻¹*B).PosDef := by
    have hs := two_posDef (schur 0) (schur_hermitian 0)
      (thetaCuspFullSource 0 ^ 2) (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))
    have hb : D-Bᴴ*A⁻¹*B = schur 0 +
        (3*(schurBound+thetaCuspFullSource 0^2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      dsimp only [D,A,B,schur]
      rw [he]
      abel
    rw [hb]
    exact hs
  have hP : (fromBlocks A B Bᴴ D).PosDef := by
    have hp := (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hS.posSemidef
    apply hp.posDef_iff_det_ne_zero.mpr
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    exact mul_ne_zero hA.det_pos.ne' hS.det_pos.ne'
  have htrans : (basisᴴ * repair coefficient 0 * basis).PosDef := by
    rw [repair_block]
    exact hP
  have hinj : Function.Injective inverseBasis.mulVec := by
    intro v w h
    have hh := congrArg (fun u => basis *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec, basis_inverse, Matrix.one_mulVec] using hh
  have hback := htrans.conjTranspose_mul_mul_same hinj
  have hb : inverseBasisᴴ * (basisᴴ * repair coefficient 0 * basis) * inverseBasis =
      repair coefficient 0 := by
    calc
      _ = (basis * inverseBasis)ᴴ * repair coefficient 0 * (basis * inverseBasis) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [basis_inverse]; simp
  rwa [hb] at hback

private theorem repair_hermitian (C x : ℝ) : (repair C x).IsHermitian :=
  (native_hermitian x).add (load_posSemidef.isHermitian.smul (by simp [IsSelfAdjoint]))

private theorem repair_continuous (C : ℝ) : Continuous (repair C) := by
  have hΦ : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold repair nativeShiftedMatrix thetaCuspCenterCompensationSource
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

/-- The coupled repair is strict throughout a nontrivial origin neighborhood. -/
theorem repair_posDef_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → (repair coefficient x).PosDef := by
  have ht (i j : Fin 5) : Tendsto (fun x => repair coefficient x i j)
      (𝓝 0) (𝓝 (repair coefficient 0 i j)) :=
    ((continuous_apply j).comp ((continuous_apply i).comp (repair_continuous coefficient))).continuousAt.tendsto
  have hp := posDef_eventually_of_tendsto repair_zero_posDef
    (Filter.Eventually.of_forall (repair_hermitian coefficient)) ht
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ,hδ,fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩


private theorem center_div_scale_three :
    Tendsto (fun x : ℝ => x/thetaCuspSingleAtomReflectionScale 1 x^3) atTop (𝓝 0) := by
  have h := (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop
    (b := (6 : ℝ)) (by norm_num) 1).const_mul ((Real.pi^3)⁻¹)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  have hp : Real.exp (6*x) = Real.exp (2*x)^3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
    mul_pow, Real.exp_neg, hp, div_eq_mul_inv]
  ring

private theorem source_four_limit :
    Tendsto (fun x : ℝ => thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^4)) atTop (𝓝 0) := by
  have hm := thetaCuspFullSource_div_firstAtom_tendsto_one
  have hs := thetaCuspFullSource_deriv_div_firstAtom_scale_tendsto
  have hi := thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have h := (((hm.pow 2).mul (hi.pow 4)).const_mul 3).add
    (((center_div_scale_three.mul hm).mul hs).const_mul 2)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
  unfold thetaCuspCenterCompensationSource
  field_simp [hq,hf]

private theorem source_limit (n : ℕ) (hn : 4 ≤ n) :
    Tendsto (fun x : ℝ => thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^n)) atTop (𝓝 0) := by
  have h := source_four_limit.mul (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow (n-4))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
  conv_rhs => rw [← Nat.sub_add_cancel hn, pow_add]
  field_simp [hq,hf]

private theorem load_support (i j : Fin 5) (h : i.val+j.val < 4) : load i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [load, loadRows, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

private def gaussianFive : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j : Fin 5 => gaussianMoment (i.val+j.val)

private theorem gaussianFive_posDef : gaussianFive.PosDef := by
  let A : Matrix (Fin 5) (Fin 5) ℝ :=
    _root_.HTGeometry.momentHankelMatrix (gammaShapeMoment (1/2)) 5
  let D : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i : Fin 5 => (16 : ℝ)^i.val)
  have hA : A.PosDef := gammaShapeMoment_momentHankelMatrix_posDef (by norm_num) 5
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (16 : ℝ) ≠ 0)) hi
  have he : gaussianFive = Dᴴ * A * D := by
    ext i j
    simp only [gaussianFive, gaussianMoment, D, A, diagonal_conjTranspose,
      star_trivial, diagonal_mul, mul_diagonal, _root_.HTGeometry.momentHankelMatrix, pow_add]
    ring
  rw [he]
  exact hA.conjTranspose_mul_mul_same hD

private def balancedRepair (C x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => thetaCuspNativeScaledEvenJet (i.val+j.val) x +
    C * load i j * (thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^(i.val+j.val)))

private theorem balancedRepair_limit (C : ℝ) (i j : Fin 5) :
    Tendsto (fun x => balancedRepair C x i j) atTop (𝓝 (gaussianFive i j)) := by
  have hn := native_scaled_jet_tendsto (i.val+j.val)
  rw [profile_signed_even_jet] at hn
  have hd : Tendsto (fun x => C * load i j * (thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^(i.val+j.val))))
      atTop (𝓝 0) := by
    by_cases hij : i.val+j.val < 4
    · simp only [load_support i j hij, mul_zero, zero_mul]
      exact tendsto_const_nhds
    · simpa using (source_limit (i.val+j.val) (by omega)).const_mul (C*load i j)
  simpa only [balancedRepair, gaussianFive, add_zero] using hn.add hd

/-- Every fixed coupled correction preserves the positive Gaussian tail. -/
theorem repair_posDef_eventually (C : ℝ) : ∀ᶠ x : ℝ in atTop, (repair C x).PosDef := by
  have hh (x : ℝ) : (balancedRepair C x).IsHermitian := by
    have hs (i j : Fin 5) : load i j = load j i := by
      have h := congrArg (fun Q : Matrix (Fin 5) (Fin 5) ℝ => Q j i) load_posSemidef.isHermitian
      simpa only [Matrix.conjTranspose_apply, star_trivial] using h
    rw [Matrix.IsHermitian]
    ext i j
    simp [balancedRepair, hs j i, add_comm]
  have hp := posDef_eventually_of_tendsto gaussianFive_posDef
    (Filter.Eventually.of_forall hh) (balancedRepair_limit C)
  filter_upwards [hp,eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let T : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i => f*q^i.val)
  have hq : q ≠ 0 := by dsimp [q,thetaCuspSingleAtomReflectionScale]; positivity
  have hf : f ≠ 0 := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hT : Function.Injective T.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [T,Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have he : repair C x = Tᴴ * balancedRepair C x * T := by
    ext i j
    simp only [T,diagonal_conjTranspose,star_trivial,diagonal_mul,mul_diagonal,
      repair,balancedRepair,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      nativeShiftedMatrix,thetaCuspNativeScaledEvenJet,add_zero]
    change (-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x +
      (C*thetaCuspCenterCompensationSource x)*load i j =
      (f*q^i.val) * (((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)/
        (f^2*q^(i.val+j.val)) + C*load i j*(thetaCuspCenterCompensationSource x/
        (f^2*q^(i.val+j.val)))) * (f*q^j.val)
    simp only [pow_add]
    field_simp [hf,hq]
  rw [he]
  exact hx.conjTranspose_mul_mul_same hT

/-- The actual coefficient gives positivity near zero and on a cofinal ray. -/
theorem repair_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ x : ℝ, 0 ≤ x → (x < δ ∨ R ≤ x) →
      (repair coefficient x).PosDef := by
  obtain ⟨δ,hδ,hnear⟩ := repair_posDef_near_zero
  obtain ⟨R,htail⟩ := Filter.eventually_atTop.mp (repair_posDef_eventually coefficient)
  refine ⟨δ,max R δ,hδ,le_max_right _ _,fun x hx h => ?_⟩
  rcases h with h | h
  · exact hnear x (by simpa [abs_of_nonneg hx] using h)
  · exact htail x ((le_max_left _ _).trans h)

/-- The literal weighted representative with a coupled zero-boundary flux. -/
def weightedRepair (a C r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (r*Real.sinh (a*r)) • nativeShiftedMatrix 5 0 (r/2) +
    (C*deriv (thetaCuspCenterCompensationFlux a) r) • load

/-- Every corrected mixed entry remains integrable. -/
theorem weightedRepair_integrable {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (C : ℝ) (i j : Fin 5) :
    IntegrableOn (fun r => weightedRepair a C r i j) (Ioi 0) := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  have hf := (integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul (C*load i j)
  apply (hi.add hf).congr
  filter_upwards with r
  simp only [Pi.add_apply,weightedRepair,nativeShiftedMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_zero]
  ring

/-- Coupled correction preserves the complete mixed matrix entry by entry. -/
theorem weightedRepair_integral {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (C : ℝ) (i j : Fin 5) :
    (∫ r in Ioi 0, weightedRepair a C r i j) =
      thetaCuspCenterMixedSignedJet a (2*(i.val+j.val)) := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  have hf := (integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul (C*load i j)
  have he : (fun r => weightedRepair a C r i j) =
      fun r => (-1 : ℝ)^(i.val+j.val)*(r*Real.sinh (a*r)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) (r/2)) +
        (C*load i j)*deriv (thetaCuspCenterCompensationFlux a) r := by
    funext r
    simp only [weightedRepair,nativeShiftedMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_zero]
    ring
  rw [he,integral_add hi hf,integral_const_mul,integral_const_mul,
    integral_deriv_thetaCuspCenterCompensationFlux habs,mul_zero,add_zero,
    thetaCuspCenterMixedSignedJet_even,iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet ha0 ha]

/-- Aperture weighting adds a nonnegative multiple of the same positive load. -/
theorem weightedRepair_posDef_of_source {a C r : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hr : 0 < r) (hs : (repair C (r/2)).PosDef) : (weightedRepair a C r).PosDef := by
  let w := r*Real.sinh (a*r)
  let d := deriv (thetaCuspCenterCompensationFlux a) r - w*thetaCuspCenterCompensationSource (r/2)
  have hw : 0 < w := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hd : 0 ≤ d := by
    apply sub_nonneg.mpr
    convert deriv_thetaCuspCenterCompensationFlux_lower ha.le hr.le using 1
    unfold w thetaCuspCenterCompensationSource
    ring
  have he : weightedRepair a C r = w • repair C (r/2) + (C*d) • load := by
    ext i j
    simp only [weightedRepair,repair,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    dsimp only [d,w]
    ring
  rw [he]
  exact (hs.smul hw).add_posSemidef (load_posSemidef.smul (mul_nonneg hC hd))

/-- A common origin neighborhood and tail work for every positive aperture. -/
theorem weightedRepair_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ a r : ℝ, 0 < a → 0 < r →
      (r < δ ∨ R ≤ r) → (weightedRepair a coefficient r).PosDef := by
  obtain ⟨δ,R,hδ,hR,hs⟩ := repair_compact_gap
  refine ⟨2*δ,2*R,by positivity,by linarith only [hR],fun a r ha hr h => ?_⟩
  apply weightedRepair_posDef_of_source ha coefficient_pos.le hr
  apply hs (r/2) (by positivity)
  rcases h with h | h
  · exact Or.inl (by linarith only [h])
  · exact Or.inr (by linarith only [h])

/-- Both linear loads vanish on the scale-seven direction. -/
theorem loadRows_witness : loadRows *ᵥ EvenFiveBoundary.witnessVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [loadRows,EvenFiveBoundary.witnessVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

/-- The positive correction annihilates the witness exactly. -/
theorem load_witness : load *ᵥ EvenFiveBoundary.witnessVector = 0 := by
  rw [load,← Matrix.mulVec_mulVec,loadRows_witness,Matrix.mulVec_zero]

private theorem native_energy (x : ℝ) :
    EvenFiveBoundary.witnessVector ⬝ᵥ (nativeShiftedMatrix 5 0 x *ᵥ EvenFiveBoundary.witnessVector) =
      EvenFiveBoundary.sourceEnergy x := by
  simp only [dotProduct,Matrix.mulVec,nativeShiftedMatrix,EvenFiveBoundary.sourceEnergy,add_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coupled source repair leaves the witness energy unchanged at every center. -/
theorem repair_witness_energy (C x : ℝ) :
    EvenFiveBoundary.witnessVector ⬝ᵥ (repair C x *ᵥ EvenFiveBoundary.witnessVector) =
      EvenFiveBoundary.sourceEnergy x := by
  simp only [repair,Matrix.add_mulVec,Matrix.smul_mulVec,load_witness,smul_zero,add_zero,native_energy]

/-- Unlike diagonal loads, coupled loads preserve the positive scale-seven direction. -/
theorem repair_witness_positive (C : ℝ) :
    0 < EvenFiveBoundary.witnessVector ⬝ᵥ
      (repair C EvenFiveBoundary.witnessCenter *ᵥ EvenFiveBoundary.witnessVector) := by
  rw [repair_witness_energy]
  exact EvenFiveBoundary.source_direction_positive

/-- The literal weighted correction also preserves this direction at every radius. -/
theorem weightedRepair_witness_energy (a C r : ℝ) :
    EvenFiveBoundary.witnessVector ⬝ᵥ (weightedRepair a C r *ᵥ EvenFiveBoundary.witnessVector) =
      (r*Real.sinh (a*r))*EvenFiveBoundary.sourceEnergy (r/2) := by
  simp only [weightedRepair,Matrix.add_mulVec,Matrix.smul_mulVec,load_witness,smul_zero,add_zero,
    dotProduct_smul,native_energy,smul_eq_mul]

/-- The weighted scale-seven witness stays positive for every positive aperture. -/
theorem weightedRepair_witness_positive {a : ℝ} (ha : 0 < a) (C : ℝ) :
    0 < EvenFiveBoundary.witnessVector ⬝ᵥ
      (weightedRepair a C (2*EvenFiveBoundary.witnessCenter) *ᵥ EvenFiveBoundary.witnessVector) := by
  have hx : 0 < EvenFiveBoundary.witnessCenter := by
    unfold EvenFiveBoundary.witnessCenter
    apply div_pos _ (by norm_num)
    apply Real.log_pos
    apply (one_lt_div Real.pi_pos).mpr
    linarith only [Real.pi_lt_d2]
  rw [weightedRepair_witness_energy]
  have he : 2*EvenFiveBoundary.witnessCenter/2=EvenFiveBoundary.witnessCenter := by ring
  rw [he]
  exact mul_pos (mul_pos (by positivity) (Real.sinh_pos_iff.mpr (by positivity)))
    EvenFiveBoundary.source_direction_positive


/-- The single last-pair coupled load cannot repair the origin, at any coefficient. -/
theorem single_load_fails (C : ℝ) :
    ¬ (nativeShiftedMatrix 5 0 0 + (C*thetaCuspCenterCompensationSource 0) •
      ((!![0,0,0,1,1568] : Matrix (Fin 1) (Fin 5) ℝ)ᴴ * (!![0,0,0,1,1568] : Matrix (Fin 1) (Fin 5) ℝ))).PosSemidef := by
  let U : Matrix (Fin 1) (Fin 5) ℝ := !![0,0,0,1,1568]
  have hz : U * singleCoherentKernelBasis = 0 := by
    ext i j
    fin_cases i
    fin_cases j <;>
      norm_num [U,singleCoherentKernelBasis,Matrix.mul_apply,Fin.sum_univ_succ,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  have he : singleCoherentKernelBasisᴴ * (Uᴴ*U) * singleCoherentKernelBasis = 0 := by
    calc
      _ = (U*singleCoherentKernelBasis)ᴴ * (U*singleCoherentKernelBasis) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hz]; simp
  intro h
  have hk := h.conjTranspose_mul_mul_same singleCoherentKernelBasis
  change (singleCoherentKernelBasisᴴ * (nativeShiftedMatrix 5 0 0 +
    (C*thetaCuspCenterCompensationSource 0) • (Uᴴ*U)) * singleCoherentKernelBasis).PosSemidef at hk
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,he,smul_zero,add_zero] at hk
  exact singleCoherentKernel_zero_not_posSemidef hk


private theorem coupledLoad_gram (C D : ℝ) : coupledLoad C D =
    loadRowsᴴ * diagonal (fun i : Fin 2 => ![C,D] i) * loadRows := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coupledLoad,loadRows,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.diagonal_apply,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.vecHead,Matrix.vecTail] <;> ring

/-- Both nonnegative coupled coefficients give a positive semidefinite load. -/
theorem coupledLoad_posSemidef {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (coupledLoad C D).PosSemidef := by
  rw [coupledLoad_gram]
  have hd : (diagonal (fun i : Fin 2 => ![C,D] i)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i
    · simpa using hC
    · simpa using hD
  exact hd.conjTranspose_mul_mul_same loadRows

private theorem coupledLoad_hermitian (C D : ℝ) : (coupledLoad C D).IsHermitian := by
  rw [coupledLoad_gram]
  apply Matrix.isHermitian_conjTranspose_mul_mul loadRows
  rw [Matrix.IsHermitian,diagonal_conjTranspose]
  simp only [star_trivial]

/-- Independent coefficients still annihilate the scale-seven vector. -/
theorem coupledLoad_witness (C D : ℝ) : coupledLoad C D *ᵥ EvenFiveBoundary.witnessVector=0 := by
  rw [coupledLoad_gram,← Matrix.mulVec_mulVec,loadRows_witness,Matrix.mulVec_zero]

private theorem coupledLoad_support (C D : ℝ) (i j : Fin 5) (h : i.val+j.val < 4) :
    coupledLoad C D i j=0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [coupledLoad,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

private theorem coupled_hermitian (C D x : ℝ) : (coupledRepair C D x).IsHermitian :=
  (native_hermitian x).add ((coupledLoad_hermitian C D).smul (by simp [IsSelfAdjoint]))

private theorem coupled_continuous (C D : ℝ) : Continuous (coupledRepair C D) := by
  have hΦ : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold coupledRepair nativeShiftedMatrix thetaCuspCenterCompensationSource
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

private theorem coupled_near_zero_of_posDef (C D : ℝ)
    (hzero : (coupledRepair C D 0).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → (coupledRepair C D x).PosDef := by
  have ht (i j : Fin 5) : Tendsto (fun x => coupledRepair C D x i j)
      (𝓝 0) (𝓝 (coupledRepair C D 0 i j)) :=
    ((continuous_apply j).comp ((continuous_apply i).comp
      (coupled_continuous C D))).continuousAt.tendsto
  have hp := posDef_eventually_of_tendsto hzero
    (Filter.Eventually.of_forall (coupled_hermitian C D)) ht
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ,hδ,fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

/-- The explicit unequal pair is strict throughout an origin neighborhood. -/
theorem coupledRepair_posDef_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      (coupledRepair 100000000 1000000000000 x).PosDef :=
  coupled_near_zero_of_posDef _ _ coupledRepair_unequal_zero_posDef

private def balancedCoupled (C D x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => thetaCuspNativeScaledEvenJet (i.val+j.val) x +
    coupledLoad C D i j * (thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^(i.val+j.val)))

private theorem balancedCoupled_limit (C D : ℝ) (i j : Fin 5) :
    Tendsto (fun x => balancedCoupled C D x i j) atTop (𝓝 (gaussianFive i j)) := by
  have hn := native_scaled_jet_tendsto (i.val+j.val)
  rw [profile_signed_even_jet] at hn
  have hd : Tendsto (fun x => coupledLoad C D i j * (thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^(i.val+j.val))))
      atTop (𝓝 0) := by
    by_cases hij : i.val+j.val < 4
    · simp only [coupledLoad_support C D i j hij,zero_mul]
      exact tendsto_const_nhds
    · simpa using (source_limit (i.val+j.val) (by omega)).const_mul (coupledLoad C D i j)
  simpa only [balancedCoupled,gaussianFive,add_zero] using hn.add hd

/-- Every fixed pair of coupled coefficients preserves the positive Gaussian tail. -/
theorem coupledRepair_posDef_eventually (C D : ℝ) :
    ∀ᶠ x : ℝ in atTop, (coupledRepair C D x).PosDef := by
  have hh (x : ℝ) : (balancedCoupled C D x).IsHermitian := by
    have hs (i j : Fin 5) : coupledLoad C D i j = coupledLoad C D j i := by
      have h := congrArg (fun Q : Matrix (Fin 5) (Fin 5) ℝ => Q j i) (coupledLoad_hermitian C D)
      simpa only [Matrix.conjTranspose_apply,star_trivial] using h
    rw [Matrix.IsHermitian]
    ext i j
    simp [balancedCoupled,hs j i,add_comm]
  have hp := posDef_eventually_of_tendsto gaussianFive_posDef
    (Filter.Eventually.of_forall hh) (balancedCoupled_limit C D)
  filter_upwards [hp,eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let T : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i => f*q^i.val)
  have hq : q ≠ 0 := by dsimp [q,thetaCuspSingleAtomReflectionScale]; positivity
  have hf : f ≠ 0 := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hT : Function.Injective T.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [T,Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have he : coupledRepair C D x = Tᴴ * balancedCoupled C D x * T := by
    ext i j
    simp only [T,diagonal_conjTranspose,star_trivial,diagonal_mul,mul_diagonal,
      coupledRepair,balancedCoupled,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      nativeShiftedMatrix,thetaCuspNativeScaledEvenJet,add_zero]
    change (-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x+
      thetaCuspCenterCompensationSource x*coupledLoad C D i j =
      (f*q^i.val)*(((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)/
        (f^2*q^(i.val+j.val))+coupledLoad C D i j*(thetaCuspCenterCompensationSource x/
        (f^2*q^(i.val+j.val))))*(f*q^j.val)
    simp only [pow_add]
    field_simp [hf,hq]
  rw [he]
  exact hx.conjTranspose_mul_mul_same hT

/-- Every entry of the independently corrected weighted source is integrable. -/
theorem coupledWeightedRepair_integrable {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (C D : ℝ) (i j : Fin 5) :
    IntegrableOn (fun r => coupledWeightedRepair a C D r i j) (Ioi 0) := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  have hf := (integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul (coupledLoad C D i j)
  apply (hi.add hf).congr
  filter_upwards with r
  simp only [Pi.add_apply,coupledWeightedRepair,nativeShiftedMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_zero]
  ring

/-- Independent coupled loads preserve every actual mixed integral. -/
theorem coupledWeightedRepair_integral {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (C D : ℝ) (i j : Fin 5) :
    (∫ r in Ioi 0, coupledWeightedRepair a C D r i j) =
      thetaCuspCenterMixedSignedJet a (2*(i.val+j.val)) := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  have hf := (integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul (coupledLoad C D i j)
  have he : (fun r => coupledWeightedRepair a C D r i j) =
      fun r => (-1 : ℝ)^(i.val+j.val)*(r*Real.sinh (a*r)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) (r/2))+
        coupledLoad C D i j*deriv (thetaCuspCenterCompensationFlux a) r := by
    funext r
    simp only [coupledWeightedRepair,nativeShiftedMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_zero]
    ring
  rw [he,integral_add hi hf,integral_const_mul,integral_const_mul,
    integral_deriv_thetaCuspCenterCompensationFlux habs,mul_zero,add_zero,
    thetaCuspCenterMixedSignedJet_even,iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet ha0 ha]

/-- Nonnegative coupled coefficients preserve positive aperture slack. -/
theorem coupledWeightedRepair_posDef_of_source {a C D r : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 < r) (hs : (coupledRepair C D (r/2)).PosDef) :
    (coupledWeightedRepair a C D r).PosDef := by
  let w := r*Real.sinh (a*r)
  let d := deriv (thetaCuspCenterCompensationFlux a) r-w*thetaCuspCenterCompensationSource (r/2)
  have hw : 0 < w := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hd : 0 ≤ d := by
    apply sub_nonneg.mpr
    convert deriv_thetaCuspCenterCompensationFlux_lower ha.le hr.le using 1
    unfold w thetaCuspCenterCompensationSource
    ring
  have he : coupledWeightedRepair a C D r = w • coupledRepair C D (r/2)+d • coupledLoad C D := by
    ext i j
    simp only [coupledWeightedRepair,coupledRepair,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    dsimp only [d,w]
    ring
  rw [he]
  exact (hs.smul hw).add_posSemidef ((coupledLoad_posSemidef hC hD).smul hd)

private theorem coupled_weighted_compact_gap_of_posDef (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hzero : (coupledRepair C D 0).PosDef) :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ a r : ℝ, 0 < a → 0 < r →
      (r < δ ∨ R ≤ r) → (coupledWeightedRepair a C D r).PosDef := by
  obtain ⟨δ,hδ,hnear⟩ := coupled_near_zero_of_posDef C D hzero
  obtain ⟨R,htail⟩ := Filter.eventually_atTop.mp (coupledRepair_posDef_eventually C D)
  refine ⟨2*δ,2*max R δ,by positivity,by linarith only [le_max_right R δ],fun a r ha hr h => ?_⟩
  apply coupledWeightedRepair_posDef_of_source ha hC hD hr
  rcases h with h | h
  · apply hnear (r/2)
    rw [abs_of_pos (by positivity : (0 : ℝ) < r/2)]
    linarith only [h]
  · apply htail (r/2)
    linarith only [le_max_left R δ,h]

/-- The explicit unequal pair gives a common origin neighborhood and tail at every positive aperture. -/
theorem coupledWeightedRepair_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ a r : ℝ, 0 < a → 0 < r →
      (r < δ ∨ R ≤ r) → (coupledWeightedRepair a 100000000 1000000000000 r).PosDef :=
  coupled_weighted_compact_gap_of_posDef _ _ (by norm_num) (by norm_num)
    coupledRepair_unequal_zero_posDef

/-- The unequal source repair keeps the witness energy exactly at every center. -/
theorem coupledRepair_witness_energy (C D x : ℝ) :
    EvenFiveBoundary.witnessVector ⬝ᵥ (coupledRepair C D x *ᵥ EvenFiveBoundary.witnessVector) =
      EvenFiveBoundary.sourceEnergy x := by
  simp only [coupledRepair,Matrix.add_mulVec,Matrix.smul_mulVec,coupledLoad_witness,
    smul_zero,add_zero,native_energy]

/-- The independently weighted representative also keeps the witness energy exactly. -/
theorem coupledWeightedRepair_witness_energy (a C D r : ℝ) :
    EvenFiveBoundary.witnessVector ⬝ᵥ (coupledWeightedRepair a C D r *ᵥ EvenFiveBoundary.witnessVector) =
      (r*Real.sinh (a*r))*EvenFiveBoundary.sourceEnergy (r/2) := by
  simp only [coupledWeightedRepair,Matrix.add_mulVec,Matrix.smul_mulVec,coupledLoad_witness,
    smul_zero,add_zero,dotProduct_smul,native_energy,smul_eq_mul]

private theorem common_load_eq (C : ℝ) : coupledLoad C C=C • load := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coupledLoad,load,loadRows,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] <;> ring

private theorem common_repair_eq (C x : ℝ) : repair C x=coupledRepair C C x := by
  rw [repair,coupledRepair,common_load_eq,smul_smul,mul_comm C]

private theorem common_weighted_eq (a C r : ℝ) : weightedRepair a C r=coupledWeightedRepair a C C r := by
  rw [weightedRepair,coupledWeightedRepair,common_load_eq,smul_smul,mul_comm C]

/-- The common coefficient cannot repair the entire native source. -/
theorem common_source_repair_fails (C : ℝ) :
    ¬ ∀ x : ℝ, 0 ≤ x → (repair C x).PosSemidef := by
  simpa only [common_repair_eq] using EvenFiveOrigin.coupled_common_source_fails C

/-- The common coefficient fails at every critical aperture as well. -/
theorem common_weighted_repair_fails {a : ℝ} (ha : 0 < a) (haU : a < 1/2) (C : ℝ) :
    ¬ ∀ r : ℝ, 0 < r → (weightedRepair a C r).PosSemidef := by
  simpa only [common_weighted_eq] using EvenFiveOrigin.coupled_common_weighted_fails ha haU C


/-- The sixth-degree test embedded in the full fifth even block. -/
def sixthWitness : Fin 5 → ℝ := ![-6272,336,-2,1/420,0]

private theorem sixth_native_energy (x : ℝ) :
    sixthWitness ⬝ᵥ (nativeShiftedMatrix 5 0 x *ᵥ sixthWitness) =
      EvenFiveBoundary.sixthEnergy x := by
  norm_num [sixthWitness,EvenFiveBoundary.sixthEnergy,EvenFiveBoundary.sixthVector,
    dotProduct,Matrix.mulVec,nativeShiftedMatrix,Fin.sum_univ_succ]
  ring

private theorem sixth_load_energy (C D : ℝ) :
    sixthWitness ⬝ᵥ (coupledLoad C D *ᵥ sixthWitness) = C+D/176400 := by
  norm_num [sixthWitness,coupledLoad,dotProduct,Matrix.mulVec,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  ring

/-- The sixth-degree direction reads one linear combination of the two loads. -/
theorem coupledRepair_sixth_energy (C D x : ℝ) :
    sixthWitness ⬝ᵥ (coupledRepair C D x *ᵥ sixthWitness) =
      EvenFiveBoundary.sixthEnergy x+(C+D/176400)*thetaCuspCenterCompensationSource x := by
  simp only [coupledRepair,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,
    dotProduct_smul,sixth_native_energy,sixth_load_energy,smul_eq_mul]
  ring

/-- The literal weighted representative reads the same coupled load combination. -/
theorem coupledWeightedRepair_sixth_energy (a C D : ℝ) :
    sixthWitness ⬝ᵥ (coupledWeightedRepair a C D EvenFiveBoundary.witnessRadius *ᵥ sixthWitness) =
      EvenFiveBoundary.witnessWeight a*EvenFiveBoundary.sixthEnergy EvenFiveBoundary.witnessCenter+
        (C+D/176400)*EvenFiveBoundary.weightedLoad a := by
  have hh : EvenFiveBoundary.witnessRadius/2=EvenFiveBoundary.witnessCenter := by
    unfold EvenFiveBoundary.witnessRadius
    ring
  simp only [coupledWeightedRepair,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,
    dotProduct_smul,sixth_native_energy,sixth_load_energy,smul_eq_mul,hh]
  unfold EvenFiveBoundary.witnessWeight EvenFiveBoundary.weightedLoad
  ring

/-- Exact half-plane preserving the actual sixth-degree source direction at scale seven. -/
theorem coupledRepair_sixth_positive_iff (C D : ℝ) :
    0 < sixthWitness ⬝ᵥ (coupledRepair C D EvenFiveBoundary.witnessCenter *ᵥ sixthWitness) ↔
      C+D/176400 < EvenFiveBoundary.sixthCapacity := by
  rw [coupledRepair_sixth_energy,EvenFiveBoundary.sixth_coupled_positive_iff]

/-- Exact half-plane for the actual weighted sixth-degree test. -/
theorem coupledWeightedRepair_sixth_positive_iff {a : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (C D : ℝ) :
    0 < sixthWitness ⬝ᵥ (coupledWeightedRepair a C D EvenFiveBoundary.witnessRadius *ᵥ sixthWitness) ↔
      C+D/176400 < EvenFiveBoundary.sixthWeightedCapacity a := by
  rw [coupledWeightedRepair_sixth_energy,EvenFiveBoundary.sixth_coupled_weighted_positive_iff ha haU]

/-- Large first coupled loads fail at scale seven, including the explicit positive-origin pair. -/
theorem coupledRepair_not_posSemidef_of_large_first {C D : ℝ}
    (hC : 100000000 ≤ C) (hD : 0 ≤ D) :
    ¬ (coupledRepair C D EvenFiveBoundary.witnessCenter).PosSemidef := by
  intro h
  have hh := h.dotProduct_mulVec_nonneg sixthWitness
  simp only [star_trivial,coupledRepair_sixth_energy] at hh
  exact (not_lt_of_ge hh) (EvenFiveBoundary.sixth_coupled_negative hC hD)

/-- The same large first-load region fails at every critical aperture. -/
theorem coupledWeightedRepair_not_posSemidef_of_large_first {a C D : ℝ}
    (ha : 0 < a) (haU : a < 1/2) (hC : 100000000 ≤ C) (hD : 0 ≤ D) :
    ¬ (coupledWeightedRepair a C D EvenFiveBoundary.witnessRadius).PosSemidef := by
  intro h
  have hh := h.dotProduct_mulVec_nonneg sixthWitness
  simp only [star_trivial,coupledWeightedRepair_sixth_energy] at hh
  exact (not_lt_of_ge hh) (EvenFiveBoundary.sixth_coupled_weighted_negative ha haU hC hD)

/-- Lowering the first coefficient preserves strict positivity of the sixth-degree test. -/
theorem reduced_coupledRepair_sixth_positive :
    0 < sixthWitness ⬝ᵥ
      (coupledRepair 10000000 1000000000000 EvenFiveBoundary.witnessCenter *ᵥ sixthWitness) := by
  apply (coupledRepair_sixth_positive_iff _ _).mpr
  exact (by norm_num : (10000000:ℝ)+1000000000000/176400 < 16000000).trans
    EvenFiveBoundary.sixthCapacity_bounds.1

/-- The reduced pair passes the sixth-degree test at every critical aperture. -/
theorem reduced_coupledWeightedRepair_sixth_positive {a : ℝ}
    (ha : 0 < a) (haU : a < 1/2) :
    0 < sixthWitness ⬝ᵥ
      (coupledWeightedRepair a 10000000 1000000000000 EvenFiveBoundary.witnessRadius *ᵥ sixthWitness) := by
  apply (coupledWeightedRepair_sixth_positive_iff ha haU _ _).mpr
  exact (by norm_num : (10000000:ℝ)+1000000000000/176400 < 16000000).trans
    (EvenFiveBoundary.sixthWeightedCapacity_bounds ha haU).1


/-- The reduced first coefficient gives a strict neighborhood of the actual origin. -/
theorem reduced_coupledRepair_posDef_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      (coupledRepair 10000000 1000000000000 x).PosDef :=
  coupled_near_zero_of_posDef _ _ coupledRepair_reduced_zero_posDef

/-- The reduced pair is strict near zero and cofinally at every positive aperture. -/
theorem reduced_coupledWeightedRepair_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ a r : ℝ, 0 < a → 0 < r →
      (r < δ ∨ R ≤ r) → (coupledWeightedRepair a 10000000 1000000000000 r).PosDef :=
  coupled_weighted_compact_gap_of_posDef _ _ (by norm_num) (by norm_num)
    coupledRepair_reduced_zero_posDef

private theorem coupled_direction_load_energy (C D : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (coupledLoad C D *ᵥ v) =
      C*(v 2+420*v 3)^2+D*(v 3+1568*v 4)^2 := by
  norm_num [coupledLoad,dotProduct,Matrix.mulVec,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  simp only [show (2 : Fin 4).succ = (3 : Fin 5) from rfl,
    show (2 : Fin 3).succ.succ = (4 : Fin 5) from rfl]
  ring

private theorem schur_native_energy (x : ℝ) :
    EvenFiveBoundary.schurWitness ⬝ᵥ
      (nativeShiftedMatrix 5 0 x *ᵥ EvenFiveBoundary.schurWitness) =
      EvenFiveBoundary.schurEnergy x := by
  simp only [EvenFiveBoundary.schurEnergy,dotProduct,Matrix.mulVec,
    nativeShiftedMatrix,add_zero,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The coupled source energy in the exact scale-seven Schur direction. -/
theorem coupledRepair_schur_energy (C D x : ℝ) :
    EvenFiveBoundary.schurWitness ⬝ᵥ
      (coupledRepair C D x *ᵥ EvenFiveBoundary.schurWitness) =
      EvenFiveBoundary.schurEnergy x+
        EvenFiveBoundary.schurLoad C D*thetaCuspCenterCompensationSource x := by
  simp only [coupledRepair,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,
    dotProduct_smul,schur_native_energy,coupled_direction_load_energy,smul_eq_mul]
  unfold EvenFiveBoundary.schurLoad
  ring

/-- The weighted source reads the same rational Schur-direction load. -/
theorem coupledWeightedRepair_schur_energy (a C D : ℝ) :
    EvenFiveBoundary.schurWitness ⬝ᵥ
      (coupledWeightedRepair a C D EvenFiveBoundary.witnessRadius *ᵥ EvenFiveBoundary.schurWitness) =
      EvenFiveBoundary.witnessWeight a*EvenFiveBoundary.schurEnergy EvenFiveBoundary.witnessCenter+
        EvenFiveBoundary.schurLoad C D*EvenFiveBoundary.weightedLoad a := by
  have hh : EvenFiveBoundary.witnessRadius/2=EvenFiveBoundary.witnessCenter := by
    unfold EvenFiveBoundary.witnessRadius
    ring
  simp only [coupledWeightedRepair,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,
    dotProduct_smul,schur_native_energy,coupled_direction_load_energy,smul_eq_mul,hh]
  unfold EvenFiveBoundary.schurLoad EvenFiveBoundary.witnessWeight EvenFiveBoundary.weightedLoad
  ring

/-- Positive origin and separate Hermite tests do not suffice for the reduced pair's full source sign. -/
theorem reduced_coupledRepair_not_posSemidef :
    ¬ (coupledRepair 10000000 1000000000000 EvenFiveBoundary.witnessCenter).PosSemidef := by
  intro h
  have hp := h.dotProduct_mulVec_nonneg EvenFiveBoundary.schurWitness
  simp only [star_trivial,coupledRepair_schur_energy] at hp
  exact (not_lt_of_ge hp) EvenFiveBoundary.reduced_schur_energy_negative

/-- The reduced pair also fails at every sufficiently small positive critical aperture. -/
theorem reduced_coupledWeightedRepair_not_posSemidef_small :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ∀ a : ℝ, 0 < a → a < δ →
      ¬ (coupledWeightedRepair a 10000000 1000000000000 EvenFiveBoundary.witnessRadius).PosSemidef := by
  obtain ⟨δ,hδ,hδU,hn⟩ := EvenFiveBoundary.reduced_schur_weighted_negative_small
  refine ⟨δ,hδ,hδU,fun a ha haδ h => ?_⟩
  have hp := h.dotProduct_mulVec_nonneg EvenFiveBoundary.schurWitness
  simp only [star_trivial,coupledWeightedRepair_schur_energy] at hp
  exact (not_lt_of_ge hp) (hn a ha haδ)

end GaloisForLFunctions.ThetaCuspSections.EvenFiveCoherent
