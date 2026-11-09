import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.IntegralSectionHeight
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability

/-!
# Gaussian counts of arithmetic sections

The Gaussian sum over actual integral representatives of a divisor quotient class converges
and is positive. Translation by the integral normal vector gives exact quasiperiodicity.
Reducing charge modulo the squarefree count bounds the logarithmic height error uniformly
in the class, with explicit conductor dependence. Normalized doubling therefore produces
a quadratic Tate height. On the arithmetic gluing class it is the squared transverse
distance times the Gaussian decay rate. A single dilation by the squarefree count already
has an exact quadratic logarithmic count.
-/

noncomputable section
open Finset ArithmeticFunction Filter Topology
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticDegenerationTheory

/-- All actual integral representatives of a divisor quotient class. -/
def DivisorSection (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :=
  {v : Vertex N → ℤ // (divisorRelationLattice N hN).mkQ v = c}

/-- The Gaussian weight of an actual integral vector, using its squared section size. -/
def divisorGaussianWeight (N : ℕ) (t : ℝ) (v : Vertex N → ℤ) : ℝ :=
  Real.exp (-t*(divisorSectionEnergy N v : ℝ))

theorem divisorSectionEnergy_real (N : ℕ) (v : Vertex N → ℤ) :
    (divisorSectionEnergy N v : ℝ) = ∑ i, (v i : ℝ)^2 := by
  exact_mod_cast divisorSectionEnergy_cast N v

theorem summable_divisorGaussianWeight (N : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (divisorGaussianWeight N t) := by
  have hs := summable_fintype_pi_polynomialGaussian (Vertex N) (fun _ => 0)
    (fun _ => t) (fun _ => ht)
  simp only [pow_zero, one_mul] at hs
  refine hs.congr fun v => ?_
  rw [divisorGaussianWeight, divisorSectionEnergy_real, ← Real.exp_sum, ← mul_sum]

/-- The Gaussian count of actual integral sections; the charge is absent from its definition. -/
def divisorSectionTheta (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) (t : ℝ) : ℝ :=
  ∑' v : DivisorSection N hN c, divisorGaussianWeight N t v.val

/-- The Gaussian sum over the ambient integral coordinate lattice. -/
def divisorAmbientTheta (N : ℕ) (t : ℝ) : ℝ := ∑' v, divisorGaussianWeight N t v

theorem summable_divisorSectionTheta (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    Summable (fun v : DivisorSection N hN c => divisorGaussianWeight N t v.val) :=
  (summable_divisorGaussianWeight N ht).comp_injective Subtype.val_injective

theorem divisorSectionTheta_weight_le (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) (v : DivisorSection N hN c) :
    divisorGaussianWeight N t v.val ≤ divisorSectionTheta N hN c t := by
  exact (summable_divisorSectionTheta N hN c ht).le_tsum v
    (fun _ _ => (Real.exp_pos _).le)

theorem divisorSectionTheta_pos (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    0 < divisorSectionTheta N hN c t := by
  obtain ⟨v, hv⟩ := (divisorRelationLattice N hN).mkQ_surjective c
  exact (Real.exp_pos _).trans_le (divisorSectionTheta_weight_le N hN c ht ⟨v,hv⟩)

theorem divisorSectionTheta_le_ambient (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorSectionTheta N hN c t ≤ divisorAmbientTheta N t := by
  exact tsum_comp_le_tsum_of_inj (summable_divisorGaussianWeight N ht)
    (fun _ => (Real.exp_pos _).le) (i := fun v : DivisorSection N hN c => v.val)
    Subtype.val_injective

theorem divisorSectionTheta_minimum_le (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    Real.exp (-t*(divisorSectionMinimum N hN c : ℝ)) ≤ divisorSectionTheta N hN c t := by
  obtain ⟨v,hv,he⟩ := divisorSectionMinimum_attained N hN c
  have h := divisorSectionTheta_weight_le N hN c ht ⟨v,hv⟩
  simpa only [divisorGaussianWeight, he] using h

theorem divisorSectionTheta_zero_ge_one (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    1 ≤ divisorSectionTheta N hN 0 t := by
  simpa only [divisorSectionMinimum_zero, Nat.cast_zero, mul_zero, Real.exp_zero] using
    divisorSectionTheta_minimum_le N hN 0 ht

/-- A genuine logarithmic count difference for the actual integral section sets. -/
def divisorSectionLogHeight (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) (t : ℝ) : ℝ :=
  Real.log (divisorSectionTheta N hN 0 t) - Real.log (divisorSectionTheta N hN c t)

/-- The integral normal vector scaled by an integer. -/
def divisorNormalSection (N : ℕ) (a : ℤ) : Vertex N → ℤ := fun i => a*moebius i.val

/-- The actual quotient class of an integral normal translate. -/
def divisorNormalClass (N : ℕ) (hN : 1 ≤ N) (a : ℤ) : DivisorSectionClass N hN :=
  (divisorRelationLattice N hN).mkQ (divisorNormalSection N a)

theorem divisorNormalClass_charge (N : ℕ) (hN : 1 ≤ N) (a : ℤ) :
    divisorSectionChargeEquiv N hN (divisorNormalClass N hN a) =
      (divisorSquarefreeCount N : ℤ)*a := by
  rw [divisorNormalClass, divisorSectionChargeEquiv_mk, divisorNormal_apply]
  calc
    _ = (∑ i : Vertex N, moebius i.val^2)*a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [divisorNormalSection]
      ring
    _ = _ := by rw [divisorNormal_square_sum]

/-- Translation by an integral normal vector is a bijection of actual section sets. -/
def divisorSectionTranslate (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) (a : ℤ) :
    DivisorSection N hN c ≃ DivisorSection N hN (c+divisorNormalClass N hN a) where
  toFun v := ⟨v.val+divisorNormalSection N a, by rw [map_add,v.property]; rfl⟩
  invFun v := ⟨v.val-divisorNormalSection N a, by
    rw [map_sub,v.property]
    change c+divisorNormalClass N hN a-divisorNormalClass N hN a=c
    exact add_sub_cancel_right _ _⟩
  left_inv v := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv v := by apply Subtype.ext; exact sub_add_cancel _ _

theorem divisorSectionEnergy_translate (N : ℕ) (hN : 1 ≤ N)
    (v : Vertex N → ℤ) (a : ℤ) :
    (divisorSectionEnergy N (v+divisorNormalSection N a) : ℤ) =
      (divisorSectionEnergy N v : ℤ)+2*a*divisorNormal N hN v+
        (divisorSquarefreeCount N : ℤ)*a^2 := by
  rw [divisorSectionEnergy_cast,divisorSectionEnergy_cast,divisorNormal_apply,
    ← divisorNormal_square_sum N]
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply,divisorNormalSection]
  ring

/-- Normal translation changes the section sum by its exact Gaussian energy factor. -/
theorem divisorSectionTheta_translate (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (a : ℤ) (t : ℝ) :
    divisorSectionTheta N hN (c+divisorNormalClass N hN a) t =
      Real.exp (-t*(2*(a : ℝ)*(divisorSectionChargeEquiv N hN c : ℝ)+
        (divisorSquarefreeCount N : ℝ)*(a : ℝ)^2))*divisorSectionTheta N hN c t := by
  rw [divisorSectionTheta,← (divisorSectionTranslate N hN c a).tsum_eq]
  have hw (v : DivisorSection N hN c) :
      divisorGaussianWeight N t ((divisorSectionTranslate N hN c a) v).val =
        Real.exp (-t*(2*(a : ℝ)*(divisorSectionChargeEquiv N hN c : ℝ)+
          (divisorSquarefreeCount N : ℝ)*(a : ℝ)^2))*divisorGaussianWeight N t v.val := by
    have he := divisorSectionEnergy_translate N hN v.val a
    rw [(divisorSection_mk_eq_iff N hN v.val c).mp v.property] at he
    have hR : (divisorSectionEnergy N (v.val+divisorNormalSection N a) : ℝ) =
        (divisorSectionEnergy N v.val : ℝ)+2*(a : ℝ)*(divisorSectionChargeEquiv N hN c : ℝ)+
          (divisorSquarefreeCount N : ℝ)*(a : ℝ)^2 := by exact_mod_cast he
    change Real.exp (-t*(divisorSectionEnergy N (v.val+divisorNormalSection N a) : ℝ)) = _
    rw [hR,divisorGaussianWeight,← Real.exp_add]
    congr 1
    ring
  simp_rw [hw]
  rw [tsum_mul_left]
  rfl

theorem divisorSectionLogHeight_translate (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (a : ℤ) {t : ℝ} (ht : 0 < t) :
    divisorSectionLogHeight N hN (c+divisorNormalClass N hN a) t =
      divisorSectionLogHeight N hN c t+
        t*(2*(a : ℝ)*(divisorSectionChargeEquiv N hN c : ℝ)+
          (divisorSquarefreeCount N : ℝ)*(a : ℝ)^2) := by
  rw [divisorSectionLogHeight,divisorSectionTheta_translate,
    Real.log_mul (Real.exp_pos _).ne' (divisorSectionTheta_pos N hN c ht).ne',Real.log_exp,
    divisorSectionLogHeight]
  ring

/-- The quotient class with charge equal to the Euclidean division remainder. -/
def divisorSectionResidueClass (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    DivisorSectionClass N hN :=
  (divisorSectionChargeEquiv N hN).symm (divisorSectionRemainder N hN c : ℤ)

theorem divisorSectionResidueClass_charge (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    divisorSectionChargeEquiv N hN (divisorSectionResidueClass N hN c) =
      (divisorSectionRemainder N hN c : ℤ) :=
  (divisorSectionChargeEquiv N hN).apply_symm_apply _

theorem divisorSectionResidueClass_minimum (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    divisorSectionMinimum N hN (divisorSectionResidueClass N hN c) =
      divisorSectionRemainder N hN c := by
  apply Int.ofNat_inj.mp
  rw [divisorSectionMinimum_eq_charge_of_nonneg N hN _ (by
    rw [divisorSectionResidueClass_charge]; exact Int.natCast_nonneg _) (by
    rw [divisorSectionResidueClass_charge]
    exact_mod_cast (divisorSectionRemainder_lt N hN c).le),divisorSectionResidueClass_charge]

theorem divisorSection_residue_decomposition (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    c = divisorSectionResidueClass N hN c + divisorNormalClass N hN (divisorSectionFloor N hN c) := by
  apply (divisorSectionChargeEquiv N hN).injective
  rw [map_add,divisorSectionResidueClass_charge,divisorNormalClass_charge,
    divisorSectionDivision N hN c]
  exact add_comm _ _

/-- Subtracting the quadratic normal energy leaves an error periodic in the charge. -/
theorem divisorSectionLogHeight_residue (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorSectionLogHeight N hN c t-
      t*(divisorSectionChargeEquiv N hN c : ℝ)^2/divisorSquarefreeCount N =
    divisorSectionLogHeight N hN (divisorSectionResidueClass N hN c) t-
      t*(divisorSectionRemainder N hN c : ℝ)^2/divisorSquarefreeCount N := by
  have he := divisorSectionLogHeight_translate N hN (divisorSectionResidueClass N hN c)
    (divisorSectionFloor N hN c) ht
  rw [← divisorSection_residue_decomposition,divisorSectionResidueClass_charge] at he
  have hd : (divisorSectionChargeEquiv N hN c : ℝ) =
      (divisorSquarefreeCount N : ℝ)*(divisorSectionFloor N hN c : ℝ)+
        (divisorSectionRemainder N hN c : ℝ) := by
    exact_mod_cast divisorSectionDivision N hN c
  have hq : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  rw [he,hd]
  push_cast
  field_simp [hq]
  ring

theorem divisorSectionLogHeight_residue_bounds (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    -Real.log (divisorAmbientTheta N t) ≤
        divisorSectionLogHeight N hN (divisorSectionResidueClass N hN c) t ∧
    divisorSectionLogHeight N hN (divisorSectionResidueClass N hN c) t ≤
        Real.log (divisorAmbientTheta N t)+t*(divisorSectionRemainder N hN c : ℝ) := by
  have hz := divisorSectionTheta_zero_ge_one N hN ht
  have hza := divisorSectionTheta_le_ambient N hN 0 ht
  have hcp := divisorSectionTheta_pos N hN (divisorSectionResidueClass N hN c) ht
  have hca := divisorSectionTheta_le_ambient N hN (divisorSectionResidueClass N hN c) ht
  have hmin := divisorSectionTheta_minimum_le N hN (divisorSectionResidueClass N hN c) ht
  rw [divisorSectionResidueClass_minimum] at hmin
  have hlower := Real.log_le_log (Real.exp_pos _) hmin
  rw [Real.log_exp] at hlower
  have hz0 := Real.log_nonneg hz
  have hlogza := Real.log_le_log (lt_of_lt_of_le zero_lt_one hz) hza
  have hlogca := Real.log_le_log hcp hca
  unfold divisorSectionLogHeight
  constructor <;> linarith only [hlower,hz0,hlogza,hlogca]

/-- An explicit conductor-dependent bound, uniform over all quotient classes. -/
def divisorGaussianHeightError (N : ℕ) (t : ℝ) : ℝ :=
  Real.log (divisorAmbientTheta N t)+t*(divisorSquarefreeCount N : ℝ)

theorem divisorGaussianHeightError_nonneg (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    0 ≤ divisorGaussianHeightError N t := by
  have hz := (divisorSectionTheta_zero_ge_one N hN ht).trans
    (divisorSectionTheta_le_ambient N hN 0 ht)
  exact add_nonneg (Real.log_nonneg hz) (mul_nonneg ht.le (Nat.cast_nonneg _))

/-- Ambient summability and an attained residue minimum bound the actual logarithmic error. -/
theorem divisorSectionLogHeight_error (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    |divisorSectionLogHeight N hN c t-
      t*(divisorSectionChargeEquiv N hN c : ℝ)^2/divisorSquarefreeCount N| ≤
        divisorGaussianHeightError N t := by
  rw [divisorSectionLogHeight_residue N hN c ht]
  have hb := divisorSectionLogHeight_residue_bounds N hN c ht
  have hr0 : (0 : ℝ) ≤ divisorSectionRemainder N hN c := Nat.cast_nonneg _
  have hrq : (divisorSectionRemainder N hN c : ℝ) ≤ divisorSquarefreeCount N := by
    exact_mod_cast (divisorSectionRemainder_lt N hN c).le
  have hq : (0 : ℝ) < divisorSquarefreeCount N := by
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have hsq : (divisorSectionRemainder N hN c : ℝ)^2 ≤
      (divisorSquarefreeCount N : ℝ)^2 := pow_le_pow_left₀ hr0 hrq 2
  have hs0 : 0 ≤ t*(divisorSectionRemainder N hN c : ℝ)^2/divisorSquarefreeCount N :=
    div_nonneg (mul_nonneg ht.le (sq_nonneg _)) hq.le
  have hsq' : t*(divisorSectionRemainder N hN c : ℝ)^2/divisorSquarefreeCount N ≤
      t*(divisorSquarefreeCount N : ℝ) := by
    apply (div_le_iff₀ hq).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hsq ht.le]
  have htr := mul_le_mul_of_nonneg_left hrq ht.le
  rw [abs_le]
  unfold divisorGaussianHeightError
  constructor <;> linarith only [hb.1,hb.2,hs0,hsq',htr]

theorem divisorSectionLogHeight_parallelogram_bound (N : ℕ) (hN : 1 ≤ N)
    (c d : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    |divisorSectionLogHeight N hN (c+d) t+divisorSectionLogHeight N hN (c-d) t-
      2*divisorSectionLogHeight N hN c t-2*divisorSectionLogHeight N hN d t| ≤
        6*divisorGaussianHeightError N t := by
  have hp := abs_le.mp (divisorSectionLogHeight_error N hN (c+d) ht)
  have hm := abs_le.mp (divisorSectionLogHeight_error N hN (c-d) ht)
  have hc := abs_le.mp (divisorSectionLogHeight_error N hN c ht)
  have hd := abs_le.mp (divisorSectionLogHeight_error N hN d ht)
  simp only [map_add,map_sub,Int.cast_add,Int.cast_sub] at hp hm
  have hquad : t*((divisorSectionChargeEquiv N hN c : ℝ)+
        (divisorSectionChargeEquiv N hN d : ℝ))^2/divisorSquarefreeCount N+
      t*((divisorSectionChargeEquiv N hN c : ℝ)-
        (divisorSectionChargeEquiv N hN d : ℝ))^2/divisorSquarefreeCount N =
      2*(t*(divisorSectionChargeEquiv N hN c : ℝ)^2/divisorSquarefreeCount N)+
      2*(t*(divisorSectionChargeEquiv N hN d : ℝ)^2/divisorSquarefreeCount N) := by ring
  rw [abs_le]
  constructor <;> linarith only [hp.1,hp.2,hm.1,hm.2,hc.1,hc.2,hd.1,hd.2,hquad]

/-- The quadratic normalization of a logarithm of actual Gaussian section counts. -/
def divisorGaussianTateSequence (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN)
    (t : ℝ) (j : ℕ) : ℝ := divisorSectionLogHeight N hN ((2^j : ℕ) • c) t/(4 : ℝ)^j

theorem divisorGaussianTateSequence_error (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    |divisorGaussianTateSequence N hN c t j-t*divisorSectionTateHeight N hN c| ≤
      divisorGaussianHeightError N t*(1/4 : ℝ)^j := by
  have hp : (0 : ℝ) < (4 : ℝ)^j := pow_pos (by norm_num) j
  have hq : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  have hpow : ((2 : ℝ)^j)^2 = (4 : ℝ)^j := by
    rw [← pow_mul,Nat.mul_comm j 2,pow_mul]
    norm_num
  have hz : divisorSectionChargeEquiv N hN ((2^j : ℕ) • c) =
      (2 : ℤ)^j*divisorSectionChargeEquiv N hN c := by
    rw [map_nsmul]
    simp only [nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hR : (divisorSectionChargeEquiv N hN ((2^j : ℕ) • c) : ℝ) =
      (2 : ℝ)^j*(divisorSectionChargeEquiv N hN c : ℝ) := by exact_mod_cast hz
  have he : divisorGaussianTateSequence N hN c t j-t*divisorSectionTateHeight N hN c =
      (divisorSectionLogHeight N hN ((2^j : ℕ) • c) t-
        t*(divisorSectionChargeEquiv N hN ((2^j : ℕ) • c) : ℝ)^2/
          divisorSquarefreeCount N)/(4 : ℝ)^j := by
    rw [divisorGaussianTateSequence,divisorSectionTateHeight_eq,hR,mul_pow,hpow]
    field_simp [hp.ne',hq]
  rw [he,abs_div,abs_of_pos hp]
  have hb := div_le_div_of_nonneg_right
    (divisorSectionLogHeight_error N hN ((2^j : ℕ) • c) ht) hp.le
  simpa only [div_eq_mul_inv,inv_pow,one_mul] using hb

theorem tendsto_divisorGaussianTateSequence (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    Tendsto (divisorGaussianTateSequence N hN c t) atTop
      (𝓝 (t*divisorSectionTateHeight N hN c)) := by
  have hg : Tendsto (fun j : ℕ => divisorGaussianHeightError N t*(1/4 : ℝ)^j)
      atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1/4 : ℝ)) (by norm_num)
    simpa only [mul_zero] using (tendsto_const_nhds.mul h :
      Tendsto (fun j : ℕ => divisorGaussianHeightError N t*(1/4 : ℝ)^j) atTop
        (𝓝 (divisorGaussianHeightError N t*0)))
  have he : Tendsto (fun j => divisorGaussianTateSequence N hN c t j-
      t*divisorSectionTateHeight N hN c) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hg
    intro j
    simpa only [Real.norm_eq_abs] using divisorGaussianTateSequence_error N hN c ht j
  have hf : (fun j => divisorGaussianTateSequence N hN c t j-
      t*divisorSectionTateHeight N hN c+t*divisorSectionTateHeight N hN c) =
      divisorGaussianTateSequence N hN c t := by funext j; ring
  have h := he.add_const (t*divisorSectionTateHeight N hN c)
  rw [hf,zero_add] at h
  exact h

/-- The limit of normalized actual logarithmic section counts. -/
def divisorGaussianTateHeight (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) (t : ℝ) : ℝ :=
  Filter.limUnder atTop (divisorGaussianTateSequence N hN c t)

theorem divisorGaussianTateHeight_eq (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorGaussianTateHeight N hN c t = t*divisorSectionTateHeight N hN c :=
  (tendsto_divisorGaussianTateSequence N hN c ht).limUnder_eq

theorem divisorGaussianTateHeight_parallelogram (N : ℕ) (hN : 1 ≤ N)
    (c d : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorGaussianTateHeight N hN (c+d) t+divisorGaussianTateHeight N hN (c-d) t =
      2*divisorGaussianTateHeight N hN c t+2*divisorGaussianTateHeight N hN d t := by
  simp only [divisorGaussianTateHeight_eq N hN _ ht]
  rw [← mul_add,divisorSectionTateHeight_parallelogram]
  ring

theorem divisorGaussianTateHeight_nsmul (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    divisorGaussianTateHeight N hN (m • c) t = (m : ℝ)^2*divisorGaussianTateHeight N hN c t := by
  rw [divisorGaussianTateHeight_eq N hN _ ht,divisorGaussianTateHeight_eq N hN _ ht,
    divisorSectionTateHeight_nsmul]
  ring

/-- The original gluing class has Gaussian Tate height equal to its squared transverse distance. -/
theorem divisorGluingClass_gaussianTateHeight (N : ℕ) (hN : 1 ≤ N)
    {t : ℝ} (ht : 0 < t) :
    divisorGaussianTateHeight N hN (divisorGluingClass N hN) t =
      t*divisorTransverseDistance N (integerGluingRealColumn N)^2 := by
  rw [divisorGaussianTateHeight_eq N hN _ ht,divisorGluingClass_tateHeight]

theorem divisorSectionLogHeight_zero (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    divisorSectionLogHeight N hN 0 t = 0 := sub_self _

/-- Scaling a class by the squarefree count makes its charge an integral normal translate. -/
theorem divisorSection_squarefree_smul (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    (divisorSquarefreeCount N : ℕ) • c =
      divisorNormalClass N hN (divisorSectionChargeEquiv N hN c) := by
  apply (divisorSectionChargeEquiv N hN).injective
  rw [map_nsmul,divisorNormalClass_charge,nsmul_eq_mul]

/-- A finite arithmetic dilation already has the exact quadratic logarithmic count. -/
theorem divisorSectionLogHeight_squarefree_smul (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorSectionLogHeight N hN ((divisorSquarefreeCount N : ℕ) • c) t =
      t*(divisorSquarefreeCount N : ℝ)*(divisorSectionChargeEquiv N hN c : ℝ)^2 := by
  have h := divisorSectionLogHeight_translate N hN 0 (divisorSectionChargeEquiv N hN c) ht
  simp only [zero_add,divisorSectionLogHeight_zero,
    (divisorSectionChargeEquiv N hN).map_zero,Int.cast_zero,mul_zero] at h
  rw [divisorSection_squarefree_smul,h]
  ring

#print axioms summable_divisorSectionTheta
#print axioms divisorSectionTheta_pos
#print axioms divisorSectionTheta_translate
#print axioms divisorSectionLogHeight_translate
#print axioms divisorSectionLogHeight_residue
#print axioms divisorSectionLogHeight_error
#print axioms divisorSectionLogHeight_parallelogram_bound
#print axioms divisorGaussianTateSequence_error
#print axioms tendsto_divisorGaussianTateSequence
#print axioms divisorGaussianTateHeight_parallelogram
#print axioms divisorGaussianTateHeight_nsmul
#print axioms divisorGluingClass_gaussianTateHeight
#print axioms divisorSectionLogHeight_squarefree_smul

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
