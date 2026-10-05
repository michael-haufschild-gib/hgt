import GaloisForLFunctions.RHTower.ChiRamanujanCofactorPole

/-!
# Exact deformation of the complete critical Mellin source

The one-balanced boundary retains every prime label and both exclusions.
Every labelled term is its balanced value times the literal ratio
`q^(1-s)/r^(1-s)`. The complete source therefore reduces to two excluded
prime rows; no profile separability or omitted coincident label is used.
Its norm on the entire vertical boundary is bounded sharply by its balanced
norm, for every finite prime set and every real Mellin frequency.

Four exact normalized local rational identities retain all allowed tag
patterns for the joint growing-prime, near-pole problem. They expose the
leading responses and the summable local remainders. The growing joint
limit and the full physical signed cubic saving are not proved here.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RHTower.BAGTrace

private theorem local_base {z x : ℂ} (hz : z ≠ 0) (hx : x ≠ 0)
    (hz1 : 1-z ≠ 0) (hx1 : 1-x ≠ 0) :
    weightedEuler z x z = (1-z)⁻¹^2 := by
  unfold weightedEuler
  field_simp
  ring

private theorem local_first {z x : ℂ} (hz : z ≠ 0) (hx : x ≠ 0)
    (hz1 : 1-z ≠ 0) (hx1 : 1-x ≠ 0) :
    weightedConeEulerMinusOne z x z = x*(1-z)⁻¹^2 := by
  rw [weightedConeEulerMinusOne,local_base hz hx hz1 hx1]
  field_simp
  ring

private theorem local_pair {z x : ℂ} (hz : z ≠ 0) (hx : x ≠ 0)
    (hz1 : 1-z ≠ 0) (hx1 : 1-x ≠ 0) :
    weightedConeEulerMinusTwo z x z = x^2*(1-z)⁻¹^2 := by
  rw [weightedConeEulerMinusTwo,local_first hz hx hz1 hx1]
  field_simp
  ring

private theorem local_third {z x : ℂ} (hz : z ≠ 0) (hx : x ≠ 0)
    (hz1 : 1-z ≠ 0) (hx1 : 1-x ≠ 0) :
    weightedConeEuler z x z 1 = -(z/x)/(1-z)*(1-z)⁻¹^2 := by
  simp only [weightedConeEuler,show (1 : ℤ) ≠ -2 by omega,
    show (1 : ℤ) ≠ -1 by omega,show (1 : ℤ) ≠ 0 by omega,if_false]
  rw [local_base hz hx hz1 hx1]
  field_simp
  ring

def criticalPrimeMellinRatio (p : Nat.Primes) (s : ℂ) : ℂ :=
  cubicPrimeBase p s / cubicPrimeBase p 1

private theorem base_one (p : Nat.Primes) :
    cubicPrimeBase p 1 = ((1/(p : ℝ) : ℝ) : ℂ) := by
  simp [cubicPrimeBase,Complex.cpow_neg_one]

private theorem local_one_balanced (P : Finset Nat.Primes) (p q r ℓ : P)
    (hpr : p ≠ r) (hqr : q ≠ r) {s : ℂ} (hs : 0 < s.re) :
    (cubicPrimeBase ℓ s)^(-criticalLabelShift p ℓ) *
      (cubicPrimeBase ℓ 1)^(-criticalLabelShift q ℓ) *
      weightedConeEuler (cubicPrimeBase ℓ 1) (cubicPrimeBase ℓ s)
        (cubicPrimeBase ℓ 1)
        (criticalLabelShift r ℓ-criticalLabelShift p ℓ-criticalLabelShift q ℓ) =
      (if ℓ=q then criticalPrimeMellinRatio ℓ s else 1) *
      (if ℓ=r then -(criticalPrimeMellinRatio ℓ s)⁻¹ /
        (1-cubicPrimeBase ℓ 1) else 1) * (1-cubicPrimeBase ℓ 1)⁻¹^2 := by
  have hz := cubicPrimeBase_ne_zero ℓ 1
  have hx := cubicPrimeBase_ne_zero ℓ s
  have hz1 := one_sub_cubicPrimeBase_ne_zero ℓ (s := 1) (by norm_num)
  have hx1 := one_sub_cubicPrimeBase_ne_zero ℓ hs
  by_cases hr : ℓ=r
  · subst ℓ
    simp only [criticalLabelShift,Ne.symm hpr,Ne.symm hqr,if_false,if_true,
      sub_zero,neg_zero,zpow_zero,one_mul]
    rw [local_third hz hx hz1 hx1]
    simp [criticalPrimeMellinRatio,div_eq_mul_inv,mul_comm]
  · have hcr : criticalLabelShift r ℓ = 0 := by simp [criticalLabelShift,hr]
    by_cases hp : ℓ=p <;> by_cases hq : ℓ=q
    · have hcp : criticalLabelShift p ℓ = 1 := if_pos hp
      have hcq : criticalLabelShift q ℓ = 1 := if_pos hq
      simp only [hcr,hcp,hcq,if_pos hq,if_neg hr]
      norm_num only [weightedConeEuler,Int.reduceSub,Int.reduceNeg,
        Int.reduceEq,if_true,if_false,zpow_neg_one,mul_one]
      rw [local_pair hz hx hz1 hx1]
      unfold criticalPrimeMellinRatio
      field_simp
    · have hcp : criticalLabelShift p ℓ = 1 := if_pos hp
      have hcq : criticalLabelShift q ℓ = 0 := if_neg hq
      simp only [hcr,hcp,hcq,if_neg hq,if_neg hr]
      norm_num only [weightedConeEuler,Int.reduceSub,Int.reduceNeg,
        Int.reduceEq,if_true,if_false,zpow_neg_one,zpow_zero,mul_one,one_mul]
      rw [local_first hz hx hz1 hx1]
      field_simp
    · have hcp : criticalLabelShift p ℓ = 0 := if_neg hp
      have hcq : criticalLabelShift q ℓ = 1 := if_pos hq
      simp only [hcr,hcp,hcq,if_pos hq,if_neg hr]
      norm_num only [weightedConeEuler,Int.reduceSub,Int.reduceNeg,
        Int.reduceEq,if_true,if_false,zpow_neg_one,zpow_zero,mul_one,one_mul]
      rw [local_first hz hx hz1 hx1]
      unfold criticalPrimeMellinRatio
      field_simp
    · have hcp : criticalLabelShift p ℓ = 0 := if_neg hp
      have hcq : criticalLabelShift q ℓ = 0 := if_neg hq
      simp only [hcr,hcp,hcq,if_neg hq,if_neg hr]
      norm_num only [weightedConeEuler,Int.reduceSub,Int.reduceNeg,
        Int.reduceEq,if_true,if_false,zpow_zero,mul_one,one_mul]
      exact local_base hz hx hz1 hx1

theorem criticalWeightedLabelEuler_one_balanced (P : Finset Nat.Primes) (p q r : P)
    (hpr : p ≠ r) (hqr : q ≠ r) {s : ℂ} (hs : 0 < s.re) :
    criticalWeightedLabelEuler P p q r s 1 =
      ((-criticalPrimeNormalization P * criticalThirdLabelWeight r *
        criticalPrimeLabelWeight p * criticalPrimeLabelWeight q : ℝ) : ℂ) *
      criticalPrimeMellinRatio q s / criticalPrimeMellinRatio r s := by
  unfold criticalWeightedLabelEuler
  simp_rw [local_one_balanced P p q r _ hpr hqr hs]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,
    Finset.prod_ite_eq',Finset.prod_ite_eq',if_pos (Finset.mem_univ q),
    if_pos (Finset.mem_univ r),Finset.prod_pow,Finset.prod_inv_distrib]
  have hprod : (∏ ℓ : P, (1-cubicPrimeBase ℓ 1)) =
      (criticalPrimeNormalization P : ℂ) := by
    simp only [base_one,criticalPrimeNormalization]
    push_cast
    rfl
  rw [hprod,base_one]
  have hA : (criticalPrimeNormalization P : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalPrimeNormalization_pos P).ne'
  have hr0 : ((r : Nat.Primes) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.val.property.ne_zero
  have hr1 : (((r : Nat.Primes) : ℝ)-1) ≠ 0 := by
    have hh : (1 : ℝ) < ((r : Nat.Primes) : ℝ) := by exact_mod_cast r.val.property.one_lt
    linarith
  have hr1c : (((r : Nat.Primes) : ℂ)-1) ≠ 0 := by exact_mod_cast hr1
  unfold criticalThirdLabelWeight criticalPrimeLabelWeight
  push_cast
  field_simp

/-- The complete excluded second-label row at a moving first Mellin argument. -/
def criticalMellinLabelRow (P : Finset Nat.Primes) (r : P) (s : ℂ) : ℂ :=
  ∑ q : P, if q=r then 0 else
    (criticalPrimeLabelWeight q : ℂ)*criticalPrimeMellinRatio q s

theorem criticalWeightedConeEuler_one_balanced (P : Finset Nat.Primes)
    {s : ℂ} (hs : 0 < s.re) :
    criticalWeightedConeEuler P s 1 = -(criticalPrimeNormalization P : ℂ) *
      ∑ r : P, (criticalThirdLabelWeight r : ℂ)/criticalPrimeMellinRatio r s *
        (criticalLabelRow P r : ℂ)*criticalMellinLabelRow P r s := by
  rw [criticalWeightedConeEuler,Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [criticalLabelRow,criticalMellinLabelRow]
  push_cast
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p=r
  · simp [hp]
  by_cases hq : q=r
  · simp [hq]
  rw [if_neg (not_or.mpr ⟨hp,hq⟩),if_neg hp,if_neg hq,
    criticalWeightedLabelEuler_one_balanced P p q r hp hq hs]
  push_cast
  ring

/-- All imaginary moving parameters retain both actual label exclusions. -/
theorem criticalWeightedConeEuler_one_balanced_family (P : Finset Nat.Primes) (τ : ℝ) :
    criticalWeightedConeEuler P (1+(τ : ℂ)*Complex.I) 1 =
      -(criticalPrimeNormalization P : ℂ) *
        ∑ r : P, (criticalThirdLabelWeight r : ℂ)/
          criticalPrimeMellinRatio r (1+(τ : ℂ)*Complex.I) *
          (criticalLabelRow P r : ℂ)*
          criticalMellinLabelRow P r (1+(τ : ℂ)*Complex.I) :=
  criticalWeightedConeEuler_one_balanced P (by simp)

/-- Moving labels are the literal prime powers, with no independent cofactor. -/
theorem criticalPrimeMellinRatio_eq (p : Nat.Primes) (s : ℂ) :
    criticalPrimeMellinRatio p s = (p : ℂ)^(1-s) := by
  rw [criticalPrimeMellinRatio,cubicPrimeBase_div,cubicPrimeBase]
  congr 1
  ring

/-- The exact complex exponential form used on the growing logarithmic window. -/
theorem criticalPrimeMellinRatio_logScale (p : Nat.Primes) (u : ℂ) (L : ℝ) :
    criticalPrimeMellinRatio p (1+u/(L : ℂ)) =
      Complex.exp (-u*((Real.log (p : ℝ)/L : ℝ) : ℂ)) := by
  rw [criticalPrimeMellinRatio_eq,Complex.cpow_def_of_ne_zero
    (Nat.cast_ne_zero.mpr p.property.ne_zero)]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp,
    ← Complex.ofReal_log hp.le]
  push_cast
  congr 1
  ring

private theorem label_weight_nonneg (p : Nat.Primes) : 0 ≤ criticalPrimeLabelWeight p := by
  unfold criticalPrimeLabelWeight
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_le))
    (Nat.cast_nonneg _)

private theorem third_weight_nonneg (p : Nat.Primes) : 0 ≤ criticalThirdLabelWeight p := by
  unfold criticalThirdLabelWeight
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  exact div_nonneg (Real.log_nonneg hp.le) (sub_nonneg.mpr hp.le)

private theorem label_row_nonneg (P : Finset Nat.Primes) (r : P) :
    0 ≤ criticalLabelRow P r :=
  Finset.sum_nonneg fun q _ => by
    split_ifs
    · exact le_rfl
    · exact label_weight_nonneg q

theorem norm_criticalPrimeMellinRatio_vertical (p : Nat.Primes) (τ : ℝ) :
    ‖criticalPrimeMellinRatio p (1+(τ : ℂ)*Complex.I)‖ = 1 := by
  rw [criticalPrimeMellinRatio,norm_div]
  have he : ‖cubicPrimeBase p (1+(τ : ℂ)*Complex.I)‖ = ‖cubicPrimeBase p 1‖ := by
    simp only [norm_cubicPrimeBase]
    congr 1
    simp
  rw [he,div_self (norm_ne_zero_iff.mpr (cubicPrimeBase_ne_zero p 1))]

private theorem mellin_row_norm_le (P : Finset Nat.Primes) (r : P) (τ : ℝ) :
    ‖criticalMellinLabelRow P r (1+(τ : ℂ)*Complex.I)‖ ≤ criticalLabelRow P r := by
  unfold criticalMellinLabelRow criticalLabelRow
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : q=r
  · simp [h]
  · simp only [if_neg h,norm_mul,norm_criticalPrimeMellinRatio_vertical,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (label_weight_nonneg q)]

/-- A sharp bound on the entire vertical one-balanced source, uniform in the
moving Mellin frequency and retaining every distinguished label and mask. -/
theorem norm_criticalWeightedConeEuler_one_balanced_le (P : Finset Nat.Primes) (τ : ℝ) :
    ‖criticalWeightedConeEuler P (1+(τ : ℂ)*Complex.I) 1‖ ≤
      criticalPrimeNormalization P *
        ∑ r : P, criticalThirdLabelWeight r*criticalLabelRow P r^2 := by
  rw [criticalWeightedConeEuler_one_balanced_family,norm_mul,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (criticalPrimeNormalization_pos P)]
  apply mul_le_mul_of_nonneg_left _ (criticalPrimeNormalization_pos P).le
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul,norm_mul,norm_div,norm_criticalPrimeMellinRatio_vertical,div_one,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (third_weight_nonneg r),abs_of_nonneg (label_row_nonneg P r)]
  calc criticalThirdLabelWeight r*criticalLabelRow P r *
        ‖criticalMellinLabelRow P r (1+(τ : ℂ)*Complex.I)‖ ≤
      criticalThirdLabelWeight r*criticalLabelRow P r * criticalLabelRow P r :=
        mul_le_mul_of_nonneg_left (mellin_row_norm_le P r τ)
          (mul_nonneg (third_weight_nonneg r) (label_row_nonneg P r))
    _ = _ := by ring

/-- The balanced value attains the uniform vertical norm bound. -/
theorem criticalWeightedConeEuler_one_balanced_maximum (P : Finset Nat.Primes) (τ : ℝ) :
    ‖criticalWeightedConeEuler P (1+(τ : ℂ)*Complex.I) 1‖ ≤
      ‖criticalWeightedConeEuler P 1 1‖ := by
  have hsum : 0 ≤ ∑ r : P, criticalThirdLabelWeight r*criticalLabelRow P r^2 :=
    Finset.sum_nonneg fun r _ => mul_nonneg (third_weight_nonneg r) (sq_nonneg _)
  rw [criticalWeightedConeEuler_balanced,Complex.norm_real,Real.norm_eq_abs,
    neg_mul,abs_neg,abs_of_nonneg (mul_nonneg (criticalPrimeNormalization_pos P).le hsum)]
  exact norm_criticalWeightedConeEuler_one_balanced_le P τ

/-- Local base after removing both numerator cofactor factors. -/
theorem weightedEuler_normalized_deformation (z a b : ℂ) (_hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    (1-z*a)*(1-z*b)*weightedEuler z (z*a) (z*b) =
      1 + (z*(a+b-a^2-b^2)/(a*b)+z^2*(a+b-2))/(1-z)^2 := by
  unfold weightedEuler
  field_simp
  ring

theorem weightedFirst_normalized_deformation (z a b : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    (1-z*a)*(1-z*b)*(z*a)⁻¹*weightedConeEulerMinusOne z (z*a) (z*b) =
      ((a+b-1)+z*((a+b)*(a+b-a^2-b^2)/(a*b)-a*b-1)
        + z^2*(a*b-a-b+a^2+b^2))/(a*(1-z)^2) := by
  unfold weightedConeEulerMinusOne weightedEuler
  field_simp
  ring

theorem weightedThird_normalized_deformation (z a b : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    (1-z*a)*(1-z*b)*weightedConeEuler z (z*a) (z*b) 1 =
      (a*b-a-b+z*(2*(a+b)-a*b-1)-z^2*a*b)/(a*b*(1-z)^3) := by
  norm_num only [weightedConeEuler,Int.reduceEq,if_false]
  unfold weightedEuler
  field_simp
  ring

theorem weightedPair_normalized_deformation (z a b : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    let F := (a+b-a^2-b^2)/(a*b)
    let G := a+b-1-b/a-a/b+b^2/a+a^2/b
    (1-z*a)*(1-z*b)*(z*a)⁻¹*(z*b)⁻¹*
      weightedConeEulerMinusTwo z (z*a) (z*b) =
      (a^2+b^2+a*b-a-b+z*(a*b*(2-F-a-b)-(a+b)*G)+z^2*a*b*G)/
        (a*b*(1-z)^2) := by
  dsimp only
  unfold weightedConeEulerMinusTwo weightedConeEulerMinusOne weightedEuler
  field_simp
  ring


end RHTower.BAGTrace
