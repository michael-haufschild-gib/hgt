import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.GaussianSectionHeight
import GaloisForLFunctions.HTGeometry.GaussianThetaCharacteristics

/-!
# Positive Gaussian arithmetic height

The Gaussian log-count of an actual divisor quotient class lies between its quadratic
normal energy and its least integral section energy. An explicit full lattice extends the
divisor lattice by a rational normal direction. Actual integer coordinates split into a
normal integer and a quotient section; Poisson summation then supplies the lower bound.
Pairing opposite lattice sections supplies the upper bound. The error controls the actual
addition law, while the large-decay slope recovers the minimum integral section size.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticDegenerationTheory HTGeometry.IntegerLatticePoisson

private theorem gaussian_affine_sum_norm {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) (t : ℝ) (w : EuclideanSpace ℝ ι) :
    ‖∑' z : ι → ℤ, gaussianKernel t (B (euclideanIntegerPoint z)+w)‖ =
      ∑' z : ι → ℤ, Real.exp (-t*‖B (euclideanIntegerPoint z)+w‖^2) := by
  simp only [gaussianKernel_eq_ofReal,← Complex.ofReal_tsum,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le))]

/-- A shifted full-lattice Gaussian is maximal at the unshifted lattice. -/
private theorem gaussian_affine_sum_le {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ ι) :
    (∑' z : ι → ℤ, Real.exp (-t*‖B (euclideanIntegerPoint z)+w‖^2)) ≤
      ∑' z : ι → ℤ, Real.exp (-t*‖B (euclideanIntegerPoint z)‖^2) := by
  have hp := gaussian_lattice_poisson_with_characteristics B ht w 0
  simp only [gaussianModulation,latticePhase,inner_zero_right,mul_zero,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,sub_zero] at hp
  have ht' : 0 < Real.pi^2/t := div_pos (sq_pos_of_pos Real.pi_pos) ht
  have hn := norm_tsum_le_tsum_norm (summable_norm_dual_gaussian_phase B ht' w 0)
  simp only [sub_zero,norm_mul,norm_latticePhase,one_mul,norm_gaussianKernel] at hn
  have hf : 0 < gaussianFactor (ι := ι) t := by
    unfold gaussianFactor
    exact Real.rpow_pos_of_pos (div_pos Real.pi_pos ht) _
  have hs := gaussianLatticeSum_poisson B ht
  rw [gaussianLatticeSum,gaussianLatticeSum] at hs
  rw [← gaussian_affine_sum_norm B t w,hp]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (latticeScale_pos B),abs_of_pos hf]
  rw [hs,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (latticeScale_pos B).le
  apply mul_le_mul_of_nonneg_left _ hf.le
  simpa only [inverseAdjointEquiv_apply,latticePhase] using hn

private def divisorPoleReal (N : ℕ) (hN : 1 ≤ N) : Vertex N → ℝ :=
  Pi.single (poleVertex N hN) 1

private theorem divisorRealNormal_pole (N : ℕ) (hN : 1 ≤ N) :
    divisorRealNormal N (divisorPoleReal N hN) = 1 := by
  change (∑ i : Vertex N, (moebius i.val : ℝ)*(Pi.single (poleVertex N hN) (1 : ℝ) : Vertex N → ℝ) i)=1
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,if_true]
  simp only [poleVertex,moebius_apply_one,Int.cast_one]

private theorem divisorNormalVector_pole (N : ℕ) (hN : 1 ≤ N) :
    divisorNormalVector N (poleVertex N hN) = 1 := by
  simp [divisorNormalVector,poleVertex]

/-- The full-rank extension of the actual divisor lattice by its rational normal direction. -/
def divisorGaussianLatticeMap (N : ℕ) (hN : 1 ≤ N) : (Vertex N → ℝ) →ₗ[ℝ] (Vertex N → ℝ) where
  toFun x := x+(x (poleVertex N hN)/(divisorSquarefreeCount N : ℝ)) • divisorNormalVector N-
    divisorRealNormal N x • divisorPoleReal N hN
  map_add' x y := by
    simp only [Pi.add_apply,add_div,map_add,add_smul]
    abel
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,map_smul,smul_eq_mul,RingHom.id_apply]
    ring

private theorem divisorGaussianLatticeMap_normal (N : ℕ) (hN : 1 ≤ N) (x : Vertex N → ℝ) :
    divisorRealNormal N (divisorGaussianLatticeMap N hN x) = x (poleVertex N hN) := by
  have hq : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  change divisorRealNormal N (x+_ • divisorNormalVector N-_ • divisorPoleReal N hN)=_
  rw [map_sub,map_add,map_smul,map_smul,divisorRealNormal_vector,divisorRealNormal_pole,
    smul_eq_mul,smul_eq_mul,div_mul_cancel₀ _ hq,mul_one]
  ring

private theorem divisorGaussianLatticeMap_pole (N : ℕ) (hN : 1 ≤ N) (x : Vertex N → ℝ) :
    divisorGaussianLatticeMap N hN x (poleVertex N hN) =
      x (poleVertex N hN)+x (poleVertex N hN)/(divisorSquarefreeCount N : ℝ)-divisorRealNormal N x := by
  change (x+_ • divisorNormalVector N-_ • divisorPoleReal N hN) (poleVertex N hN)=_
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    divisorNormalVector_pole,divisorPoleReal,Pi.single_eq_same,mul_one]

private def divisorGaussianLatticeInverse (N : ℕ) (hN : 1 ≤ N) (y : Vertex N → ℝ) : Vertex N → ℝ :=
  y-(divisorRealNormal N y/(divisorSquarefreeCount N : ℝ)) • divisorNormalVector N+
    (divisorRealNormal N y-y (poleVertex N hN)+divisorRealNormal N y/(divisorSquarefreeCount N : ℝ)) •
      divisorPoleReal N hN

private theorem divisorGaussianLattice_leftInverse (N : ℕ) (hN : 1 ≤ N) (x : Vertex N → ℝ) :
    divisorGaussianLatticeInverse N hN (divisorGaussianLatticeMap N hN x)=x := by
  rw [divisorGaussianLatticeInverse,divisorGaussianLatticeMap_normal,divisorGaussianLatticeMap_pole]
  have hc : x (poleVertex N hN)-
      (x (poleVertex N hN)+x (poleVertex N hN)/(divisorSquarefreeCount N : ℝ)-divisorRealNormal N x)+
      x (poleVertex N hN)/(divisorSquarefreeCount N : ℝ)=divisorRealNormal N x := by ring
  rw [hc]
  change (x+_ • divisorNormalVector N-_ • divisorPoleReal N hN)-_ • divisorNormalVector N+
    _ • divisorPoleReal N hN=x
  abel

private theorem divisorGaussianLattice_rightInverse (N : ℕ) (hN : 1 ≤ N) (y : Vertex N → ℝ) :
    divisorGaussianLatticeMap N hN (divisorGaussianLatticeInverse N hN y)=y := by
  have hq : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  have hn : divisorRealNormal N (divisorGaussianLatticeInverse N hN y)=
      divisorRealNormal N y-y (poleVertex N hN)+divisorRealNormal N y/(divisorSquarefreeCount N : ℝ) := by
    rw [divisorGaussianLatticeInverse,map_add,map_sub,map_smul,map_smul,
      divisorRealNormal_vector,divisorRealNormal_pole,smul_eq_mul,smul_eq_mul,
      div_mul_cancel₀ _ hq,mul_one,sub_self,zero_add]
  have hp : divisorGaussianLatticeInverse N hN y (poleVertex N hN)=divisorRealNormal N y := by
    simp only [divisorGaussianLatticeInverse,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      divisorNormalVector_pole,divisorPoleReal,Pi.single_eq_same,mul_one]
    ring
  change divisorGaussianLatticeInverse N hN y+
    (divisorGaussianLatticeInverse N hN y (poleVertex N hN)/(divisorSquarefreeCount N : ℝ)) •
      divisorNormalVector N-divisorRealNormal N (divisorGaussianLatticeInverse N hN y) •
        divisorPoleReal N hN=y
  rw [hn,hp,divisorGaussianLatticeInverse]
  abel

/-- The rational normal extension is invertible because the pole coefficient of its primitive normal is one. -/
def divisorGaussianLatticeEquiv (N : ℕ) (hN : 1 ≤ N) : (Vertex N → ℝ) ≃ₗ[ℝ] (Vertex N → ℝ) where
  toLinearMap := divisorGaussianLatticeMap N hN
  invFun := divisorGaussianLatticeInverse N hN
  left_inv := divisorGaussianLattice_leftInverse N hN
  right_inv := divisorGaussianLattice_rightInverse N hN

/-- Complete an arbitrary integer vector to an actual section by changing only its pole coordinate. -/
def divisorSectionComplete (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN)
    (m : Vertex N → ℤ) : DivisorSection N hN c :=
  ⟨m+Pi.single (poleVertex N hN) (divisorSectionChargeEquiv N hN c-divisorNormal N hN m), by
    rw [divisorSection_mk_eq_iff,map_add,divisorNormal_pole]
    ring⟩

/-- Ambient integer coordinates are one free normal integer and one actual quotient section. -/
def divisorGaussianSectionEquiv (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    (Vertex N → ℤ) ≃ ℤ × DivisorSection N hN c where
  toFun m := (m (poleVertex N hN),divisorSectionComplete N hN c m)
  invFun zv := zv.2.val+Pi.single (poleVertex N hN) (zv.1-zv.2.val (poleVertex N hN))
  left_inv m := by
    funext i
    by_cases hi : i=poleVertex N hN
    · subst i
      simp only [divisorSectionComplete,Pi.add_apply,Pi.single_eq_same]
      ring
    · simp only [divisorSectionComplete,Pi.add_apply,Pi.single_apply,if_neg hi,add_zero]
  right_inv zv := by
    apply Prod.ext
    · simp only [Pi.add_apply,Pi.single_eq_same,add_sub_cancel]
    · apply Subtype.ext
      have hn : divisorNormal N hN zv.2.val=divisorSectionChargeEquiv N hN c :=
        (divisorSection_mk_eq_iff N hN zv.2.val c).mp zv.2.property
      funext i
      by_cases hi : i=poleVertex N hN
      · subst i
        simp only [divisorSectionComplete,Pi.add_apply,Pi.single_eq_same,map_add,divisorNormal_pole,hn]
        ring
      · simp only [divisorSectionComplete,Pi.add_apply,Pi.single_apply,if_neg hi,add_zero]

/-- The rational full-lattice extension in the actual Euclidean coordinate norm. -/
def divisorGaussianLattice (N : ℕ) (hN : 1 ≤ N) :
    EuclideanSpace ℝ (Vertex N) ≃L[ℝ] EuclideanSpace ℝ (Vertex N) :=
  ((WithLp.linearEquiv 2 ℝ (Vertex N → ℝ)).trans
    ((divisorGaussianLatticeEquiv N hN).trans
      (WithLp.linearEquiv 2 ℝ (Vertex N → ℝ)).symm)).toContinuousLinearEquiv

/-- The tangential part of the canonical pole representative of a class. -/
def divisorGaussianShift (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    EuclideanSpace ℝ (Vertex N) :=
  WithLp.toLp 2 ((divisorSectionChargeEquiv N hN c : ℝ) • divisorPoleReal N hN-
    ((divisorSectionChargeEquiv N hN c : ℝ)/(divisorSquarefreeCount N : ℝ)) • divisorNormalVector N)

private theorem divisorRealNormal_int (N : ℕ) (hN : 1 ≤ N) (m : Vertex N → ℤ) :
    divisorRealNormal N (fun i => (m i : ℝ)) = (divisorNormal N hN m : ℝ) := by
  have h := divisorNormal_apply N hN m
  change (∑ i, (moebius i.val : ℝ)*(m i : ℝ)) = _
  exact_mod_cast h.symm

private theorem divisorEuclideanSq_normal_add (N : ℕ) (v : Vertex N → ℝ) (a : ℝ) :
    divisorEuclideanSq N (v+a • divisorNormalVector N) =
      divisorEuclideanSq N v+2*a*divisorRealNormal N v+
        (divisorSquarefreeCount N : ℝ)*a^2 := by
  rw [← divisorNormalVector_square_sum N]
  change (∑ i, (v i+a*divisorNormalVector N i)^2) =
    (∑ i, (v i)^2)+2*a*(∑ i, (moebius i.val : ℝ)*v i)+
      (∑ i, (divisorNormalVector N i)^2)*a^2
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [divisorNormalVector]
  ring

private theorem divisorGaussian_section_vector (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (m : Vertex N → ℤ) :
    divisorGaussianLattice N hN (euclideanIntegerPoint m)+divisorGaussianShift N hN c =
      WithLp.toLp 2 ((fun i => ((divisorSectionComplete N hN c m).val i : ℝ))+
        (((m (poleVertex N hN) : ℝ)-(divisorSectionChargeEquiv N hN c : ℝ))/
          (divisorSquarefreeCount N : ℝ)) • divisorNormalVector N) := by
  ext i
  change (divisorGaussianLatticeMap N hN (fun j => (m j : ℝ))) i+
    ((divisorSectionChargeEquiv N hN c : ℝ)*divisorPoleReal N hN i-
      ((divisorSectionChargeEquiv N hN c : ℝ)/(divisorSquarefreeCount N : ℝ))*divisorNormalVector N i)=_
  change ((m i : ℝ)+((m (poleVertex N hN) : ℝ)/(divisorSquarefreeCount N : ℝ))*divisorNormalVector N i-
    divisorRealNormal N (fun j => (m j : ℝ))*divisorPoleReal N hN i)+_= _
  rw [divisorRealNormal_int N hN m]
  simp only [divisorSectionComplete,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Int.cast_add,
    Pi.single_apply,divisorPoleReal]
  by_cases hi : i=poleVertex N hN
  · simp only [if_pos hi,Int.cast_sub,mul_one]
    ring
  · simp only [if_neg hi,Int.cast_zero,mul_zero,add_zero,sub_zero]
    ring

/-- Orthogonality separates the free normal integer from the squared size of the actual section. -/
private theorem divisorGaussian_section_norm (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (m : Vertex N → ℤ) :
    ‖divisorGaussianLattice N hN (euclideanIntegerPoint m)+divisorGaussianShift N hN c‖^2 =
      (m (poleVertex N hN) : ℝ)^2/(divisorSquarefreeCount N : ℝ)+
        (divisorSectionEnergy N (divisorSectionComplete N hN c m).val : ℝ)-
          (divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ) := by
  rw [divisorGaussian_section_vector,EuclideanSpace.real_norm_sq_eq]
  change divisorEuclideanSq N ((fun i => ((divisorSectionComplete N hN c m).val i : ℝ))+_ •
    divisorNormalVector N)=_
  rw [divisorEuclideanSq_normal_add,
    divisorRealNormal_int N hN (divisorSectionComplete N hN c m).val,
    (divisorSection_mk_eq_iff N hN _ c).mp (divisorSectionComplete N hN c m).property]
  have he : divisorEuclideanSq N (fun i => ((divisorSectionComplete N hN c m).val i : ℝ))=
      (divisorSectionEnergy N (divisorSectionComplete N hN c m).val : ℝ) :=
    (divisorSectionEnergy_real N _).symm
  rw [he]
  have hq : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  field_simp [hq]
  ring

/-- The one-dimensional Gaussian weight in the added rational normal direction. -/
def divisorNormalGaussianWeight (N : ℕ) (t : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-t*(z : ℝ)^2/(divisorSquarefreeCount N : ℝ))

/-- The positive normal factor shared by every arithmetic section class. -/
def divisorNormalTheta (N : ℕ) (t : ℝ) : ℝ := ∑' z : ℤ, divisorNormalGaussianWeight N t z

private theorem summable_divisorNormalGaussianWeight (N : ℕ) (hN : 1 ≤ N)
    {t : ℝ} (ht : 0 < t) : Summable (divisorNormalGaussianWeight N t) := by
  have hq : (0 : ℝ) < divisorSquarefreeCount N := by
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have h := summable_one_add_natAbs_pow_mul_exp_neg_int_sq 0 (div_pos ht hq)
  simp only [pow_zero,one_mul] at h
  refine h.congr fun z => ?_
  dsimp only [divisorNormalGaussianWeight]
  congr 1
  ring

private theorem divisorNormalTheta_pos (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    0 < divisorNormalTheta N t := by
  have h := (summable_divisorNormalGaussianWeight N hN ht).le_tsum 0
    (fun _ _ => (Real.exp_pos _).le)
  have h1 : 1 ≤ divisorNormalTheta N t := by
    change 1 ≤ ∑' z : ℤ, divisorNormalGaussianWeight N t z
    simpa only [divisorNormalGaussianWeight,Int.cast_zero,zero_pow (by omega : 2 ≠ 0),
      mul_zero,zero_div,Real.exp_zero] using h
  exact zero_lt_one.trans_le h1

/-- The full-lattice sum factors into the normal Gaussian and the actual arithmetic section sum. -/
theorem divisorGaussianLattice_section_factor (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    (∑' m : Vertex N → ℤ,
      Real.exp (-t*‖divisorGaussianLattice N hN (euclideanIntegerPoint m)+
        divisorGaussianShift N hN c‖^2)) =
      divisorNormalTheta N t*Real.exp (t*(divisorSectionChargeEquiv N hN c : ℝ)^2/
        (divisorSquarefreeCount N : ℝ))*divisorSectionTheta N hN c t := by
  have hw (m : Vertex N → ℤ) :
      Real.exp (-t*‖divisorGaussianLattice N hN (euclideanIntegerPoint m)+
        divisorGaussianShift N hN c‖^2) =
      Real.exp (t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ))*
        (divisorNormalGaussianWeight N t (divisorGaussianSectionEquiv N hN c m).1*
          divisorGaussianWeight N t (divisorGaussianSectionEquiv N hN c m).2.val) := by
    rw [show (divisorGaussianSectionEquiv N hN c m).1=m (poleVertex N hN) from rfl,
      show (divisorGaussianSectionEquiv N hN c m).2=divisorSectionComplete N hN c m from rfl,
      divisorGaussian_section_norm]
    change Real.exp (-t*((m (poleVertex N hN) : ℝ)^2/(divisorSquarefreeCount N : ℝ)+
      (divisorSectionEnergy N (divisorSectionComplete N hN c m).val : ℝ)-
      (divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ))) =
      Real.exp _*(Real.exp _*Real.exp _)
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  simp_rw [hw]
  rw [tsum_mul_left]
  have hre := (divisorGaussianSectionEquiv N hN c).tsum_eq
    (fun zv : ℤ × DivisorSection N hN c =>
      divisorNormalGaussianWeight N t zv.1*divisorGaussianWeight N t zv.2.val)
  rw [hre]
  have hsN := summable_divisorNormalGaussianWeight N hN ht
  have hsC := summable_divisorSectionTheta N hN c ht
  have hprod := hsN.tsum_mul_tsum hsC
    (hsN.mul_of_nonneg hsC (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  rw [← hprod]
  change Real.exp _*(divisorNormalTheta N t*divisorSectionTheta N hN c t)=_
  ring

private theorem divisorGaussianShift_zero (N : ℕ) (hN : 1 ≤ N) :
    divisorGaussianShift N hN 0=0 := by
  simp [divisorGaussianShift]

/-- The corrected section count is bounded by the zero-class count, through actual lattice Poisson. -/
theorem divisorSectionTheta_normal_bound (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    Real.exp (t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ))*
      divisorSectionTheta N hN c t ≤ divisorSectionTheta N hN 0 t := by
  have h0 := divisorGaussianLattice_section_factor N hN 0 ht
  simp only [divisorGaussianShift_zero,add_zero,(divisorSectionChargeEquiv N hN).map_zero,
    Int.cast_zero,zero_pow (by omega : 2 ≠ 0),mul_zero,zero_div,Real.exp_zero,mul_one] at h0
  have hm := gaussian_affine_sum_le (divisorGaussianLattice N hN) ht (divisorGaussianShift N hN c)
  rw [divisorGaussianLattice_section_factor N hN c ht,h0,mul_assoc] at hm
  exact le_of_mul_le_mul_left hm (divisorNormalTheta_pos N hN ht)

private theorem exp_pair_lower (x y : ℝ) :
    2*Real.exp ((x+y)/2) ≤ Real.exp x+Real.exp y := by
  have h1 := Real.add_one_le_exp ((x-y)/2)
  have h2 := Real.add_one_le_exp ((y-x)/2)
  have hh : 2 ≤ Real.exp ((x-y)/2)+Real.exp ((y-x)/2) := by linarith only [h1,h2]
  calc
    _ = Real.exp ((x+y)/2)*2 := mul_comm _ _
    _ ≤ Real.exp ((x+y)/2)*(Real.exp ((x-y)/2)+Real.exp ((y-x)/2)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = _ := by
      rw [mul_add,← Real.exp_add,← Real.exp_add]
      congr 1 <;> congr 1 <;> ring

/-- Opposite integral translates obey the exact Euclidean parallelogram identity. -/
private theorem divisorSectionEnergy_pair (N : ℕ) (l v : Vertex N → ℤ) :
    (divisorSectionEnergy N (l+v) : ℝ)+(divisorSectionEnergy N (-l+v) : ℝ)=
      2*(divisorSectionEnergy N l : ℝ)+2*(divisorSectionEnergy N v : ℝ) := by
  simp only [divisorSectionEnergy_real,Pi.add_apply,Pi.neg_apply,Int.cast_add,Int.cast_neg,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A section translates the zero-class lattice bijectively onto its own class. -/
def divisorSectionAddEquiv (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN)
    (v : DivisorSection N hN c) : DivisorSection N hN 0 ≃ DivisorSection N hN c where
  toFun l := ⟨l.val+v.val,by rw [map_add,l.property,v.property,zero_add]⟩
  invFun w := ⟨w.val-v.val,by rw [map_sub,w.property,v.property,sub_self]⟩
  left_inv l := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv w := by apply Subtype.ext; exact sub_add_cancel _ _

private def divisorSectionNegZeroEquiv (N : ℕ) (hN : 1 ≤ N) :
    DivisorSection N hN 0 ≃ DivisorSection N hN 0 where
  toFun l := ⟨-l.val,by rw [map_neg,l.property,neg_zero]⟩
  invFun l := ⟨-l.val,by rw [map_neg,l.property,neg_zero]⟩
  left_inv l := by apply Subtype.ext; exact neg_neg _
  right_inv l := by apply Subtype.ext; exact neg_neg _

/-- Symmetric pairing bounds a translated arithmetic section count from below. -/
theorem divisorSectionTheta_translate_lower (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (v : DivisorSection N hN c) {t : ℝ} (ht : 0 < t) :
    divisorGaussianWeight N t v.val*divisorSectionTheta N hN 0 t ≤ divisorSectionTheta N hN c t := by
  let e := divisorSectionAddEquiv N hN c v
  let en := (divisorSectionNegZeroEquiv N hN).trans e
  let f : DivisorSection N hN c → ℝ := fun w => divisorGaussianWeight N t w.val
  have he : (∑' l : DivisorSection N hN 0, f (e l))=divisorSectionTheta N hN c t := e.tsum_eq f
  have hen : (∑' l : DivisorSection N hN 0, f (en l))=divisorSectionTheta N hN c t := en.tsum_eq f
  have hs := summable_divisorSectionTheta N hN c ht
  have hse : Summable (fun l : DivisorSection N hN 0 => f (e l)) := hs.comp_injective e.injective
  have hsen : Summable (fun l : DivisorSection N hN 0 => f (en l)) := hs.comp_injective en.injective
  have hp (l : DivisorSection N hN 0) :
      (2*divisorGaussianWeight N t v.val)*divisorGaussianWeight N t l.val ≤ f (e l)+f (en l) := by
    have h := exp_pair_lower (-t*(divisorSectionEnergy N (l.val+v.val) : ℝ))
      (-t*(divisorSectionEnergy N (-l.val+v.val) : ℝ))
    have hm : (-t*(divisorSectionEnergy N (l.val+v.val) : ℝ)-
        t*(divisorSectionEnergy N (-l.val+v.val) : ℝ))/2 =
        -t*(divisorSectionEnergy N v.val : ℝ)-t*(divisorSectionEnergy N l.val : ℝ) := by
      have hx := divisorSectionEnergy_pair N l.val v.val
      calc
        _ = -t*((divisorSectionEnergy N (l.val+v.val) : ℝ)+
          (divisorSectionEnergy N (-l.val+v.val) : ℝ))/2 := by ring
        _ = _ := by rw [hx]; ring
    change (2*Real.exp (-t*(divisorSectionEnergy N v.val : ℝ)))*
      Real.exp (-t*(divisorSectionEnergy N l.val : ℝ)) ≤
        Real.exp (-t*(divisorSectionEnergy N (l.val+v.val) : ℝ))+
          Real.exp (-t*(divisorSectionEnergy N (-l.val+v.val) : ℝ))
    rw [mul_assoc,← Real.exp_add]
    have hm' : (-t*(divisorSectionEnergy N (l.val+v.val) : ℝ)+
        -t*(divisorSectionEnergy N (-l.val+v.val) : ℝ))/2 =
        -t*(divisorSectionEnergy N v.val : ℝ)-t*(divisorSectionEnergy N l.val : ℝ) := by
      simpa only [sub_eq_add_neg,neg_mul] using hm
    rw [hm'] at h
    simpa only [sub_eq_add_neg,neg_mul] using h
  have hsum := ((summable_divisorSectionTheta N hN 0 ht).mul_left
    (2*divisorGaussianWeight N t v.val)).tsum_le_tsum hp (hse.add hsen)
  rw [tsum_mul_left,hse.tsum_add hsen,he,hen] at hsum
  change (2*divisorGaussianWeight N t v.val)*divisorSectionTheta N hN 0 t ≤
    divisorSectionTheta N hN c t+divisorSectionTheta N hN c t at hsum
  linarith only [hsum]

/-- The logarithmic count height never exceeds the size of an actual minimum section. -/
theorem divisorSectionLogHeight_le_minimum (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorSectionLogHeight N hN c t ≤ t*(divisorSectionMinimum N hN c : ℝ) := by
  obtain ⟨v,hv,he⟩ := divisorSectionMinimum_attained N hN c
  have h := Real.log_le_log (mul_pos (Real.exp_pos _) (divisorSectionTheta_pos N hN 0 ht))
    (divisorSectionTheta_translate_lower N hN c ⟨v,hv⟩ ht)
  change Real.log (Real.exp (-t*(divisorSectionEnergy N v : ℝ))*divisorSectionTheta N hN 0 t) ≤
    Real.log (divisorSectionTheta N hN c t) at h
  rw [Real.log_mul (Real.exp_pos _).ne'
    (divisorSectionTheta_pos N hN 0 ht).ne',Real.log_exp,he] at h
  unfold divisorSectionLogHeight
  linarith only [h]

/-- Both sides of the finite logarithmic height error follow from actual section counts. -/
theorem divisorSectionLogHeight_positive_error (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    0 ≤ divisorSectionLogHeight N hN c t-
        t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ) ∧
    divisorSectionLogHeight N hN c t-
        t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ) ≤
      t*(divisorSquarefreeCount N : ℝ)/4 := by
  have htheta := divisorSectionTheta_normal_bound N hN c ht
  have hc := divisorSectionTheta_pos N hN c ht
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) hc) htheta
  rw [Real.log_mul (Real.exp_pos _).ne' hc.ne',Real.log_exp] at hl
  refine ⟨?_, ?_⟩
  · unfold divisorSectionLogHeight
    linarith only [hl]
  · calc
      _ ≤ t*(divisorSectionMinimum N hN c : ℝ)-
          t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ) :=
        sub_le_sub_right (divisorSectionLogHeight_le_minimum N hN c ht) _
      _ = t*((divisorSectionMinimum N hN c : ℝ)-
          (divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ)) := by ring
      _ ≤ t*((divisorSquarefreeCount N : ℝ)/4) :=
        mul_le_mul_of_nonneg_left (divisorSectionMinimum_error_bounds N hN c).2 ht.le
      _ = _ := by ring

/-- The finite height error is bounded by the exact integral rounding cost. -/
theorem divisorSectionLogHeight_residue_upper (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorSectionLogHeight N hN c t-
        t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ) ≤
      t*((divisorSectionRemainder N hN c : ℝ)*
        ((divisorSquarefreeCount N : ℝ)-divisorSectionRemainder N hN c)/(divisorSquarefreeCount N : ℝ)) := by
  have h := divisorSectionLogHeight_le_minimum N hN c ht
  rw [divisorSectionMinimum_real_formula] at h
  calc
    _ ≤ t*((divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ)+
      (divisorSectionRemainder N hN c : ℝ)*
        ((divisorSquarefreeCount N : ℝ)-divisorSectionRemainder N hN c)/(divisorSquarefreeCount N : ℝ))-
          t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ) :=
      sub_le_sub_right h _
    _ = _ := by ring

theorem divisorSectionLogHeight_nonneg (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    0 ≤ divisorSectionLogHeight N hN c t := by
  have h := (divisorSectionLogHeight_positive_error N hN c ht).1
  have hq := div_nonneg (mul_nonneg ht.le (sq_nonneg (divisorSectionChargeEquiv N hN c : ℝ)))
    (Nat.cast_nonneg (divisorSquarefreeCount N) : (0 : ℝ) ≤ divisorSquarefreeCount N)
  linarith only [h,hq]

/-- The finite logarithmic section height vanishes exactly on the zero arithmetic class. -/
theorem divisorSectionLogHeight_eq_zero_iff (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorSectionLogHeight N hN c t=0 ↔ c=0 := by
  constructor
  · intro hh
    by_contra hc
    have hk : divisorSectionChargeEquiv N hN c ≠ 0 := by
      intro hk
      apply hc
      apply (divisorSectionChargeEquiv N hN).injective
      rw [hk,(divisorSectionChargeEquiv N hN).map_zero]
    have hkR : (divisorSectionChargeEquiv N hN c : ℝ) ≠ 0 := by exact_mod_cast hk
    have hq : (0 : ℝ) < divisorSquarefreeCount N := by
      exact_mod_cast divisorSquarefreeCount_pos N hN
    have hp : 0 < t*(divisorSectionChargeEquiv N hN c : ℝ)^2/(divisorSquarefreeCount N : ℝ) :=
      div_pos (mul_pos ht (sq_pos_of_ne_zero hkR)) hq
    have he := (divisorSectionLogHeight_positive_error N hN c ht).1
    rw [hh] at he
    linarith only [hp,he]
  · rintro rfl
    exact divisorSectionLogHeight_zero N hN t

/-- The actual gluing log-count dominates its squared signed displacement at every positive rate. -/
theorem divisorGluingClass_finiteHeight_lower (N : ℕ) (hN : 1 ≤ N)
    {t : ℝ} (ht : 0 < t) :
    t*divisorTransverseDistance N (integerGluingRealColumn N)^2 ≤
      divisorSectionLogHeight N hN (divisorGluingClass N hN) t := by
  have h := (divisorSectionLogHeight_positive_error N hN (divisorGluingClass N hN) ht).1
  rw [← divisorGluingClass_tateHeight N hN,divisorSectionTateHeight_eq]
  simpa only [mul_div_assoc] using sub_nonneg.mp h

/-- Positivity of the count error gives asymmetric bounds on the actual logarithmic addition defect. -/
theorem divisorSectionLogHeight_addition_bounds (N : ℕ) (hN : 1 ≤ N)
    (c d : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    -t*(divisorSquarefreeCount N : ℝ) ≤
      divisorSectionLogHeight N hN (c+d) t+divisorSectionLogHeight N hN (c-d) t-
        2*divisorSectionLogHeight N hN c t-2*divisorSectionLogHeight N hN d t ∧
    divisorSectionLogHeight N hN (c+d) t+divisorSectionLogHeight N hN (c-d) t-
        2*divisorSectionLogHeight N hN c t-2*divisorSectionLogHeight N hN d t ≤
      t*(divisorSquarefreeCount N : ℝ)/2 := by
  have hp := divisorSectionLogHeight_positive_error N hN (c+d) ht
  have hm := divisorSectionLogHeight_positive_error N hN (c-d) ht
  have hc := divisorSectionLogHeight_positive_error N hN c ht
  have hd := divisorSectionLogHeight_positive_error N hN d ht
  simp only [map_add,map_sub,Int.cast_add,Int.cast_sub] at hp hm
  have hquad : t*((divisorSectionChargeEquiv N hN c : ℝ)+
        (divisorSectionChargeEquiv N hN d : ℝ))^2/divisorSquarefreeCount N+
      t*((divisorSectionChargeEquiv N hN c : ℝ)-
        (divisorSectionChargeEquiv N hN d : ℝ))^2/divisorSquarefreeCount N =
      2*(t*(divisorSectionChargeEquiv N hN c : ℝ)^2/divisorSquarefreeCount N)+
      2*(t*(divisorSectionChargeEquiv N hN d : ℝ)^2/divisorSquarefreeCount N) := by ring
  constructor <;> linarith only [hp.1,hp.2,hm.1,hm.2,hc.1,hc.2,hd.1,hd.2,hquad]

/-- The actual finite log-count lies between its continuous quadratic height and integral minimum. -/
theorem divisorGluingClass_finiteHeight_bounds (N : ℕ) (hN : 1 ≤ N)
    {t : ℝ} (ht : 0 < t) :
    t*divisorTransverseDistance N (integerGluingRealColumn N)^2 ≤
        divisorSectionLogHeight N hN (divisorGluingClass N hN) t ∧
    divisorSectionLogHeight N hN (divisorGluingClass N hN) t ≤ t*(integerGluingCount N : ℝ) := by
  refine ⟨divisorGluingClass_finiteHeight_lower N hN ht, ?_⟩
  simpa only [divisorGluingClass_minimum_eq_count] using
    divisorSectionLogHeight_le_minimum N hN (divisorGluingClass N hN) ht

/-- Increasing Gaussian decay suppresses every section by at least the attained minimum energy. -/
theorem divisorSectionTheta_temperature_bound (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 1 ≤ t) :
    divisorSectionTheta N hN c t ≤
      Real.exp (-(t-1)*(divisorSectionMinimum N hN c : ℝ))*divisorSectionTheta N hN c 1 := by
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hp (v : DivisorSection N hN c) :
      divisorGaussianWeight N t v.val ≤
        Real.exp (-(t-1)*(divisorSectionMinimum N hN c : ℝ))*divisorGaussianWeight N 1 v.val := by
    have hv : (divisorSectionMinimum N hN c : ℝ) ≤ divisorSectionEnergy N v.val := by
      exact_mod_cast divisorSectionMinimum_le N hN c v.val v.property
    rw [divisorGaussianWeight,divisorGaussianWeight,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr ht)]
  have hs := (summable_divisorSectionTheta N hN c htp).tsum_le_tsum hp
    ((summable_divisorSectionTheta N hN c (by norm_num : (0 : ℝ) < 1)).mul_left _)
  rw [tsum_mul_left] at hs
  exact hs

/-- The full real-temperature slope approaches the actual minimum with an explicit reciprocal error. -/
theorem divisorSectionLogHeight_temperature_error (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ (divisorSectionMinimum N hN c : ℝ)-divisorSectionLogHeight N hN c t/t ∧
    (divisorSectionMinimum N hN c : ℝ)-divisorSectionLogHeight N hN c t/t ≤
      ((divisorSectionMinimum N hN c : ℝ)+Real.log (divisorSectionTheta N hN c 1))/t := by
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hu := divisorSectionLogHeight_le_minimum N hN c htp
  have hl := Real.log_le_log (divisorSectionTheta_pos N hN c htp)
    (divisorSectionTheta_temperature_bound N hN c ht)
  rw [Real.log_mul (Real.exp_pos _).ne'
    (divisorSectionTheta_pos N hN c (by norm_num : (0 : ℝ) < 1)).ne',Real.log_exp] at hl
  have hz := Real.log_nonneg (divisorSectionTheta_zero_ge_one N hN htp)
  have hlow : (t-1)*(divisorSectionMinimum N hN c : ℝ)-
      Real.log (divisorSectionTheta N hN c 1) ≤ divisorSectionLogHeight N hN c t := by
    unfold divisorSectionLogHeight
    linarith only [hl,hz]
  have he : (divisorSectionMinimum N hN c : ℝ)-divisorSectionLogHeight N hN c t/t =
      (t*(divisorSectionMinimum N hN c : ℝ)-divisorSectionLogHeight N hN c t)/t := by
    field_simp [htp.ne']
  rw [he]
  refine ⟨div_nonneg (sub_nonneg.mpr hu) htp.le, ?_⟩
  apply div_le_div_of_nonneg_right _ htp.le
  nlinarith only [hlow]

open Filter Topology

theorem tendsto_divisorSectionLogHeight_temperature (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    Tendsto (fun t : ℝ => divisorSectionLogHeight N hN c t/t) atTop
      (𝓝 (divisorSectionMinimum N hN c : ℝ)) := by
  have hg : Tendsto (fun t : ℝ =>
      ((divisorSectionMinimum N hN c : ℝ)+Real.log (divisorSectionTheta N hN c 1))/t)
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (divisorSectionMinimum N hN c : ℝ)+Real.log (divisorSectionTheta N hN c 1)) atTop
        (𝓝 ((divisorSectionMinimum N hN c : ℝ)+Real.log (divisorSectionTheta N hN c 1)))).mul
      tendsto_inv_atTop_zero
    simpa only [mul_zero,← div_eq_mul_inv] using h
  have he : Tendsto (fun t : ℝ =>
      (divisorSectionMinimum N hN c : ℝ)-divisorSectionLogHeight N hN c t/t) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hg
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact (divisorSectionLogHeight_temperature_error N hN c ht).1
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact (divisorSectionLogHeight_temperature_error N hN c ht).2
  have hf : (fun t : ℝ => (divisorSectionMinimum N hN c : ℝ)-
      ((divisorSectionMinimum N hN c : ℝ)-divisorSectionLogHeight N hN c t/t))=
      (fun t : ℝ => divisorSectionLogHeight N hN c t/t) := by funext t; ring
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (divisorSectionMinimum N hN c : ℝ))
    atTop (𝓝 (divisorSectionMinimum N hN c : ℝ))).sub he
  rw [hf,sub_zero] at h
  exact h

/-- The large-decay slope, defined from actual Gaussian counts rather than minimum energies. -/
def divisorSectionThermalHeight (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) : ℝ :=
  Filter.limUnder atTop (fun t : ℝ => divisorSectionLogHeight N hN c t/t)

theorem divisorSectionThermalHeight_eq (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    divisorSectionThermalHeight N hN c = (divisorSectionMinimum N hN c : ℝ) :=
  (tendsto_divisorSectionLogHeight_temperature N hN c).limUnder_eq

/-- The original integer quotient count is the large-decay slope of its actual Gaussian height. -/
theorem divisorGluingClass_thermalHeight (N : ℕ) (hN : 1 ≤ N) :
    divisorSectionThermalHeight N hN (divisorGluingClass N hN) = (integerGluingCount N : ℝ) := by
  rw [divisorSectionThermalHeight_eq,divisorGluingClass_minimum_eq_count]

#print axioms divisorGaussianLatticeEquiv
#print axioms divisorGaussianSectionEquiv
#print axioms divisorGaussianLattice
#print axioms divisorGaussian_section_norm
#print axioms divisorSectionTheta_translate_lower
#print axioms divisorSectionLogHeight_le_minimum
#print axioms divisorSectionLogHeight_residue_upper
#print axioms gaussian_affine_sum_le
#print axioms divisorGaussianLattice_section_factor
#print axioms divisorSectionTheta_normal_bound
#print axioms divisorSectionLogHeight_positive_error
#print axioms divisorSectionLogHeight_eq_zero_iff
#print axioms divisorGluingClass_finiteHeight_lower
#print axioms divisorSectionLogHeight_addition_bounds
#print axioms divisorGluingClass_finiteHeight_bounds
#print axioms divisorSectionTheta_temperature_bound
#print axioms divisorSectionLogHeight_temperature_error
#print axioms tendsto_divisorSectionLogHeight_temperature
#print axioms divisorGluingClass_thermalHeight

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
