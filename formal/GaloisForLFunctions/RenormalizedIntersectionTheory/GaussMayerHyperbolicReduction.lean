import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerUnimodularRationalCones

/-!
Positive-trace hyperbolic integral matrices have strictly positive unimodular
conjugates. Irrational expanding slopes have arbitrarily narrow unimodular
rational brackets, and the projective action maps a small bracket into itself.
-/

open Matrix
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolic

abbrev IntMatrix := Matrix (Fin 2) (Fin 2) ℤ

/-- The expanding root of a positive hyperbolic integral trace. -/
def expandingMultiplier (t : ℤ) : ℝ :=
  ((t : ℝ)+Real.sqrt ((t : ℝ)^2-4))/2

private theorem no_square_between {t k : ℤ} (ht : 2 < t) (hk : 0 ≤ k)
    (he : k^2 = t^2-4) : False := by
  have ht0 : 0 ≤ t := by omega
  have hkt : k < t := by
    by_contra hn
    have hle : t ≤ k := by omega
    have hs : t^2 ≤ k^2 := (sq_le_sq₀ ht0 hk).mpr hle
    linarith only [he,hs]
  have hle : k ≤ t-1 := by omega
  have hs : k^2 ≤ (t-1)^2 := (sq_le_sq₀ hk (by omega)).mpr hle
  have ht3 : 3 ≤ t := by omega
  nlinarith only [he,hs,ht3]

/-- The integral hyperbolic discriminant lies strictly between consecutive integer squares. -/
theorem discriminant_not_square {t : ℤ} (ht : 2 < t) : ¬ IsSquare (t^2-4) := by
  rintro ⟨k,hk⟩
  have he : k^2 = t^2-4 := by simpa only [pow_two] using hk.symm
  rcases le_or_gt 0 k with hk0 | hk0
  · exact no_square_between ht hk0 he
  · apply no_square_between (k := -k) ht (by omega)
    nlinarith only [he]

/-- The expanding multiplier is larger than one and satisfies the determinant-one quadratic. -/
theorem expandingMultiplier_spec {t : ℤ} (ht : 2 < t) :
    1 < expandingMultiplier t ∧
      expandingMultiplier t^2-(t : ℝ)*expandingMultiplier t+1 = 0 := by
  have ht' : (2 : ℝ) < t := by exact_mod_cast ht
  have hd : 0 ≤ (t : ℝ)^2-4 := by nlinarith only [ht',sq_nonneg ((t : ℝ)-2)]
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg ((t : ℝ)^2-4)
  constructor
  · dsimp [expandingMultiplier]
    nlinarith only [ht',hs0]
  · dsimp [expandingMultiplier]
    nlinarith only [hs]

/-- An integral determinant-one hyperbolic multiplier is irrational. -/
theorem expandingMultiplier_irrational {t : ℤ} (ht : 2 < t) :
    Irrational (expandingMultiplier t) := by
  have hd : (0 : ℤ) ≤ t^2-4 := by nlinarith only [ht,sq_nonneg (t-2)]
  have hs := (irrational_sqrt_intCast_iff_of_nonneg hd).mpr (discriminant_not_square ht)
  have he : ((t^2-4 : ℤ) : ℝ) = (t : ℝ)^2-4 := by push_cast; rfl
  rw [he] at hs
  rintro ⟨q,hq⟩
  apply hs
  refine ⟨2*q-(t : ℚ),?_⟩
  push_cast
  dsimp [expandingMultiplier] at hq
  linarith only [hq]

#print axioms discriminant_not_square
#print axioms expandingMultiplier_spec
#print axioms expandingMultiplier_irrational

/-- The attracting slope in the affine projective chart. -/
def expandingSlope (A : IntMatrix) : ℝ :=
  (expandingMultiplier (A 0 0+A 1 1)-(A 1 1 : ℝ))/(A 1 0 : ℝ)

/-- A positive-trace integral hyperbolic matrix has no rational vertical eigendirection. -/
theorem lowerLeft_ne_zero (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1) :
    A 1 0 ≠ 0 := by
  intro hc
  apply discriminant_not_square ht
  refine ⟨A 0 0-A 1 1,?_⟩
  rw [hc,mul_zero,sub_zero] at hdet
  nlinarith only [hdet]

/-- The denominator at the attracting ray equals the expanding multiplier. -/
theorem expandingSlope_denominator (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1) :
    (A 1 0 : ℝ)*expandingSlope A+A 1 1 = expandingMultiplier (A 0 0+A 1 1) := by
  have hc : (A 1 0 : ℝ) ≠ 0 := by exact_mod_cast lowerLeft_ne_zero A hdet ht
  dsimp [expandingSlope]
  field_simp [hc]
  ring

/-- The attracting ray of every positive-trace integral hyperbolic matrix is irrational. -/
theorem expandingSlope_irrational (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1) :
    Irrational (expandingSlope A) := by
  rintro ⟨q,hq⟩
  apply expandingMultiplier_irrational ht
  refine ⟨(A 1 0 : ℚ)*q+A 1 1,?_⟩
  push_cast
  have he := expandingSlope_denominator A hdet ht
  rw [← hq] at he
  exact he

/-- The literal integer matrix fixes its expanding projective ray. -/
theorem expandingSlope_eigen (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1) :
    (A 0 0 : ℝ)*expandingSlope A+A 0 1 =
      expandingMultiplier (A 0 0+A 1 1)*expandingSlope A := by
  have hc : (A 1 0 : ℝ) ≠ 0 := by exact_mod_cast lowerLeft_ne_zero A hdet ht
  have hd : (A 0 0 : ℝ)*A 1 1-(A 0 1 : ℝ)*A 1 0 = 1 := by exact_mod_cast hdet
  have hchar : expandingMultiplier (A 0 0+A 1 1)^2-
      ((A 0 0 : ℝ)+A 1 1)*expandingMultiplier (A 0 0+A 1 1)+1 = 0 := by
    simpa only [Int.cast_add] using (expandingMultiplier_spec ht).2
  have hden := expandingSlope_denominator A hdet ht
  have hcx : (A 1 0 : ℝ)*expandingSlope A =
      expandingMultiplier (A 0 0+A 1 1)-(A 1 1 : ℝ) := by linarith only [hden]
  have hz : (A 1 0 : ℝ)*((A 0 0 : ℝ)*expandingSlope A+A 0 1-
      expandingMultiplier (A 0 0+A 1 1)*expandingSlope A) = 0 := by
    calc
      _ = (A 0 0 : ℝ)*((A 1 0 : ℝ)*expandingSlope A)+(A 0 1 : ℝ)*A 1 0-
          expandingMultiplier (A 0 0+A 1 1)*((A 1 0 : ℝ)*expandingSlope A) := by ring
      _ = _ := by rw [hcx]; nlinarith only [hchar,hd]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)

/-- The numerator's transverse coefficient is the contracting multiplier. -/
theorem expandingSlope_coefficient (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1) :
    (A 0 0 : ℝ)-(A 1 0 : ℝ)*expandingSlope A =
      (expandingMultiplier (A 0 0+A 1 1))⁻¹ := by
  have hlam : expandingMultiplier (A 0 0+A 1 1) ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num) (expandingMultiplier_spec ht).1)
  have hchar : expandingMultiplier (A 0 0+A 1 1)^2-
      ((A 0 0 : ℝ)+A 1 1)*expandingMultiplier (A 0 0+A 1 1)+1 = 0 := by
    simpa only [Int.cast_add] using (expandingMultiplier_spec ht).2
  have hden := expandingSlope_denominator A hdet ht
  have hcx : (A 1 0 : ℝ)*expandingSlope A =
      expandingMultiplier (A 0 0+A 1 1)-(A 1 1 : ℝ) := by linarith only [hden]
  have hp : ((A 0 0 : ℝ)-(A 1 0 : ℝ)*expandingSlope A)*
      expandingMultiplier (A 0 0+A 1 1) = 1 := by
    rw [hcx]
    nlinarith only [hchar]
  calc
    _ = ((A 0 0 : ℝ)-(A 1 0 : ℝ)*expandingSlope A)*
        (expandingMultiplier (A 0 0+A 1 1)*(expandingMultiplier (A 0 0+A 1 1))⁻¹) := by
      rw [mul_inv_cancel₀ hlam,mul_one]
    _ = (((A 0 0 : ℝ)-(A 1 0 : ℝ)*expandingSlope A)*
        expandingMultiplier (A 0 0+A 1 1))*(expandingMultiplier (A 0 0+A 1 1))⁻¹ := by ring
    _ = _ := by rw [hp,one_mul]

/-- The fractional-linear action of the literal integral matrix. -/
def projectiveMap (A : IntMatrix) (y : ℝ) : ℝ :=
  ((A 0 0 : ℝ)*y+A 0 1)/((A 1 0 : ℝ)*y+A 1 1)

/-- Exact projective displacement about the attracting ray, retaining its contracting multiplier. -/
theorem projectiveMap_displacement (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1)
    {y : ℝ} (hy : (A 1 0 : ℝ)*y+A 1 1 ≠ 0) :
    projectiveMap A y-expandingSlope A =
      (expandingMultiplier (A 0 0+A 1 1))⁻¹*(y-expandingSlope A)/
        ((A 1 0 : ℝ)*y+A 1 1) := by
  have hz : (A 0 0 : ℝ)*expandingSlope A+A 0 1-
      expandingSlope A*((A 1 0 : ℝ)*expandingSlope A+A 1 1) = 0 := by
    rw [expandingSlope_denominator A hdet ht,expandingSlope_eigen A hdet ht]
    ring
  calc
    _ = (((A 0 0 : ℝ)*y+A 0 1)-expandingSlope A*((A 1 0 : ℝ)*y+A 1 1))/
        ((A 1 0 : ℝ)*y+A 1 1) := by
      rw [sub_div,mul_div_cancel_right₀ _ hy]
      rfl
    _ = (((A 0 0 : ℝ)-(A 1 0 : ℝ)*expandingSlope A)*(y-expandingSlope A)+
        ((A 0 0 : ℝ)*expandingSlope A+A 0 1-
          expandingSlope A*((A 1 0 : ℝ)*expandingSlope A+A 1 1)))/
        ((A 1 0 : ℝ)*y+A 1 1) := by
      congr 1
      ring
    _ = _ := by rw [hz,add_zero,expandingSlope_coefficient A hdet ht]

#print axioms lowerLeft_ne_zero
#print axioms expandingSlope_irrational
#print axioms expandingSlope_eigen
#print axioms expandingSlope_coefficient
#print axioms projectiveMap_displacement


open Filter Topology

private theorem projective_between_right (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1)
    {y : ℝ} (hy : expandingSlope A < y)
    (hden : (expandingMultiplier (A 0 0+A 1 1))⁻¹ < (A 1 0 : ℝ)*y+A 1 1) :
    expandingSlope A < projectiveMap A y ∧ projectiveMap A y < y := by
  have hroot : 0 < expandingMultiplier (A 0 0+A 1 1) :=
    lt_trans (by norm_num) (expandingMultiplier_spec ht).1
  have hmu : 0 < (expandingMultiplier (A 0 0+A 1 1))⁻¹ := inv_pos.mpr hroot
  have hd : 0 < (A 1 0 : ℝ)*y+A 1 1 := hmu.trans hden
  have he := projectiveMap_displacement A hdet ht (ne_of_gt hd)
  have hp : 0 < (expandingMultiplier (A 0 0+A 1 1))⁻¹*(y-expandingSlope A)/
      ((A 1 0 : ℝ)*y+A 1 1) := div_pos (mul_pos hmu (sub_pos.mpr hy)) hd
  have hm := mul_lt_mul_of_pos_right hden (sub_pos.mpr hy)
  have hl : (expandingMultiplier (A 0 0+A 1 1))⁻¹*(y-expandingSlope A)/
      ((A 1 0 : ℝ)*y+A 1 1) < y-expandingSlope A :=
    (div_lt_iff₀ hd).mpr (by nlinarith only [hm])
  constructor <;> linarith only [he,hp,hl]

private theorem projective_between_left (A : IntMatrix)
    (hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1) (ht : 2 < A 0 0+A 1 1)
    {y : ℝ} (hy : y < expandingSlope A)
    (hden : (expandingMultiplier (A 0 0+A 1 1))⁻¹ < (A 1 0 : ℝ)*y+A 1 1) :
    y < projectiveMap A y ∧ projectiveMap A y < expandingSlope A := by
  have hroot : 0 < expandingMultiplier (A 0 0+A 1 1) :=
    lt_trans (by norm_num) (expandingMultiplier_spec ht).1
  have hmu : 0 < (expandingMultiplier (A 0 0+A 1 1))⁻¹ := inv_pos.mpr hroot
  have hd : 0 < (A 1 0 : ℝ)*y+A 1 1 := hmu.trans hden
  have he : projectiveMap A y-expandingSlope A =
      -((expandingMultiplier (A 0 0+A 1 1))⁻¹*(expandingSlope A-y)/
        ((A 1 0 : ℝ)*y+A 1 1)) := by
    rw [projectiveMap_displacement A hdet ht (ne_of_gt hd)]
    ring
  have hp : 0 < (expandingMultiplier (A 0 0+A 1 1))⁻¹*(expandingSlope A-y)/
      ((A 1 0 : ℝ)*y+A 1 1) := div_pos (mul_pos hmu (sub_pos.mpr hy)) hd
  have hm := mul_lt_mul_of_pos_right hden (sub_pos.mpr hy)
  have hl : (expandingMultiplier (A 0 0+A 1 1))⁻¹*(expandingSlope A-y)/
      ((A 1 0 : ℝ)*y+A 1 1) < expandingSlope A-y :=
    (div_lt_iff₀ hd).mpr (by nlinarith only [hm])
  constructor <;> linarith only [he,hp,hl]

private theorem positive_coordinates (A : IntMatrix) (p q r s v w : ℤ)
    (hq : 0 < q) (hs : 0 < s) (hw : 0 < w)
    (hden : 0 < (A 1 0 : ℝ)*((v : ℝ)/w)+A 1 1)
    (hlo : (r : ℝ)/s < projectiveMap A ((v : ℝ)/w))
    (hhi : projectiveMap A ((v : ℝ)/w) < (p : ℝ)/q) :
    0 < s*(A 0 0*v+A 0 1*w)-r*(A 1 0*v+A 1 1*w) ∧
    0 < p*(A 1 0*v+A 1 1*w)-q*(A 0 0*v+A 0 1*w) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hwne : (w : ℝ) ≠ 0 := ne_of_gt hw'
  have hn : (A 0 0 : ℝ)*((v : ℝ)/w)+A 0 1 =
      ((A 0 0 : ℝ)*v+A 0 1*w)/(w : ℝ) := by field_simp [hwne]
  have hd : (A 1 0 : ℝ)*((v : ℝ)/w)+A 1 1 =
      ((A 1 0 : ℝ)*v+A 1 1*w)/(w : ℝ) := by field_simp [hwne]
  have hD : 0 < (A 1 0 : ℝ)*v+A 1 1*w := by
    rw [hd] at hden
    exact (div_pos_iff_of_pos_right hw').mp hden
  have he : projectiveMap A ((v : ℝ)/w) =
      ((A 0 0 : ℝ)*v+A 0 1*w)/((A 1 0 : ℝ)*v+A 1 1*w) := by
    rw [projectiveMap,hn,hd,div_div_div_cancel_right₀ hwne]
  rw [he] at hlo hhi
  have hl := (div_lt_div_iff₀ hs' hD).mp hlo
  have hu := (div_lt_div_iff₀ hD hq').mp hhi
  constructor
  · have hp : (0 : ℝ) < (s : ℝ)*((A 0 0 : ℝ)*v+A 0 1*w)-
        (r : ℝ)*((A 1 0 : ℝ)*v+A 1 1*w) := by nlinarith only [hl]
    exact_mod_cast hp
  · have hp : (0 : ℝ) < (p : ℝ)*((A 1 0 : ℝ)*v+A 1 1*w)-
        (q : ℝ)*((A 0 0 : ℝ)*v+A 0 1*w) := by nlinarith only [hu]
    exact_mod_cast hp

/-- Every positive-trace hyperbolic integral determinant-one matrix has a strictly positive
integral conjugate, with explicit unimodular inverse change-of-basis matrices. -/
theorem exists_positive_integral_conjugate (A : IntMatrix) (hA : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) :
    ∃ P Q : IntMatrix, P.det = 1 ∧ Q.det = 1 ∧ P*Q = 1 ∧ Q*P = 1 ∧
      ∀ i j, 0 < (Q*A*P) i j := by
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using hA
  have hroot := (expandingMultiplier_spec ht).1
  have hroot0 : 0 < expandingMultiplier (A 0 0+A 1 1) := lt_trans (by norm_num) hroot
  have hmu0 : 0 < (expandingMultiplier (A 0 0+A 1 1))⁻¹ := inv_pos.mpr hroot0
  have hmu1 : (expandingMultiplier (A 0 0+A 1 1))⁻¹ < 1 :=
    (inv_lt_one₀ hroot0).mpr hroot
  have hopen : IsOpen {y : ℝ | (expandingMultiplier (A 0 0+A 1 1))⁻¹ <
      (A 1 0 : ℝ)*y+A 1 1} :=
    isOpen_lt continuous_const ((continuous_const.mul continuous_id).add continuous_const)
  have hnear : ∀ᶠ y : ℝ in 𝓝 (expandingSlope A),
      (expandingMultiplier (A 0 0+A 1 1))⁻¹ < (A 1 0 : ℝ)*y+A 1 1 := by
    apply hopen.mem_nhds
    change (expandingMultiplier (A 0 0+A 1 1))⁻¹ <
      (A 1 0 : ℝ)*expandingSlope A+A 1 1
    rw [expandingSlope_denominator A hdet ht]
    exact hmu1.trans hroot
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨p,q,r,s,hq,hs,hps,hlo,hhi,hwidth⟩ :=
    exists_unimodular_rational_cone (expandingSlope A) (expandingSlope_irrational A hdet ht) δ hδ
  have hlowdist : dist ((r : ℝ)/s) (expandingSlope A) < δ := by
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hlo)]
    linarith only [hhi,hwidth]
  have hhighdist : dist ((p : ℝ)/q) (expandingSlope A) < δ := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hhi)]
    linarith only [hlo,hwidth]
  have hlowden := hball hlowdist
  have hhighden := hball hhighdist
  have hl := projective_between_left A hdet ht hlo hlowden
  have hu := projective_between_right A hdet ht hhi hhighden
  have hlower := positive_coordinates A p q r s r s hq hs hs
    (hmu0.trans hlowden) hl.1 (hl.2.trans hhi)
  have hupper := positive_coordinates A p q r s p q hq hs hq
    (hmu0.trans hhighden) (hlo.trans hu.1) hu.2
  refine ⟨!![p,r;q,s],!![s,-r;-q,p],?_,?_,?_,?_,?_⟩
  · rw [Matrix.det_fin_two]
    change p*s-r*q = 1
    exact hps
  · rw [Matrix.det_fin_two]
    change s*p-(-r)*(-q) = 1
    nlinarith only [hps]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith only [hps]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith only [hps]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    · nlinarith only [hupper.1]
    · nlinarith only [hlower.1]
    · nlinarith only [hupper.2]
    · nlinarith only [hlower.2]

#print axioms exists_positive_integral_conjugate

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolic
