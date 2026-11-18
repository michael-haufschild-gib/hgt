import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Degree normalization of absolute heights

Ziegler (arXiv:2609.15487, §2) divides each local logarithm by the
ambient degree and then divides their sum by the degree a second time.
For embedded rationals the first normalization is already field-independent.
The twice-divided height of two decreases to zero in the dyadic cyclotomic
tower. The same local weights give the degree-th root of the absolute field
norm in the archimedean product.
-/

noncomputable section
open Height NumberField Real Finset Filter Topology
namespace GaloisForLFunctions.KodairaParshinAbc
variable (K : Type*) [Field K] [NumberField K]
local notation "d" => Module.finrank ℚ K

/-- Product over the archimedean places with local-degree weights divided by the global degree. -/
def weightedArchNorm (x : K) : ℝ :=
  ∏ v : InfinitePlace K, (v x)^((v.mult:ℝ)/d)

private theorem archNorm_nonneg (x : K) : 0 ≤ weightedArchNorm K x :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (apply_nonneg v x) _

/-- Taking the global-degree power of the weighted product recovers the ordinary absolute field norm. -/
theorem weightedArchNorm_pow (x : K) : (weightedArchNorm K x)^d = abs (Algebra.norm ℚ x) := by
  have hd : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [← InfinitePlace.prod_eq_abs_norm x,weightedArchNorm,← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Real.rpow_natCast,← Real.rpow_mul (apply_nonneg v x),div_mul_cancel₀ _ hd,Real.rpow_natCast]

/-- The product in the printed archimedean S-norm formula is the positive-degree root of the norm. -/
theorem weightedArchNorm_eq (x : K) :
    weightedArchNorm K x = ((abs (Algebra.norm ℚ x):ℚ):ℝ)^(1/(d:ℝ)) := by
  have hd : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [← weightedArchNorm_pow K x,← Real.rpow_natCast,← Real.rpow_mul (archNorm_nonneg K x),
    one_div,mul_inv_cancel₀ hd,Real.rpow_one]

/-- Every embedded rational has its ordinary absolute value as weighted archimedean product. -/
theorem weightedArchNorm_rational (q : ℚ) : weightedArchNorm K (q:K) = ‖q‖ := by
  apply (pow_left_inj₀ (n := d) (archNorm_nonneg K _) (norm_nonneg q) Module.finrank_pos.ne').1
  rw [weightedArchNorm_pow,← InfinitePlace.prod_eq_abs_norm (q:K)]
  simp only [InfinitePlace.map_ratCast,Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq]

/-- The rational integer two detects every ambient field in which the unrooted norm formula fails. -/
theorem weightedArchNorm_two_eq_norm_iff :
    weightedArchNorm K (2:K) = abs (Algebra.norm ℚ (2:K)) ↔ d = 1 := by
  have ht : weightedArchNorm K (2:K) = 2 := by
    have hn : ‖(2:ℚ)‖ = (2:ℝ) := by change |((2:ℚ):ℝ)| = 2; norm_num
    simpa only [Rat.cast_ofNat] using (weightedArchNorm_rational K (2:ℚ)).trans hn
  rw [← weightedArchNorm_pow,ht]
  constructor
  · intro h
    have hd : 0<d := Module.finrank_pos
    by_contra hn
    have hlt := pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) (show 1<d by omega)
    rw [pow_one,← h] at hlt
    exact lt_irrefl _ hlt
  · intro h; rw [h,pow_one]

/-- Local logarithms using weights [Kᵥ:ℚₚ]/[K:ℚ]. Mathlib's finite places
already include the unnormalized local degree in their absolute value. -/
def weightedLocalHeight (x : K) : ℝ :=
  (∑ v : InfinitePlace K, ((v.mult:ℝ)/d) * log⁺ (v x)) +
    ∑ᶠ v : FinitePlace K, log⁺ (v x) / d

/-- One division by the field degree converts mathlib's relative height to the weighted local sum. -/
theorem weightedLocalHeight_eq (x : K) : weightedLocalHeight K x = logHeight₁ x / d := by
  rw [NumberField.logHeight₁_eq,add_div,Finset.sum_div]
  unfold weightedLocalHeight
  congr 1
  · exact Finset.sum_congr rfl fun v _ => by ring
  · simp only [div_eq_mul_inv,finsum_mul]

/-- Primitive integer homogeneous coordinates have unit finite contribution even after base extension. -/
theorem primitiveTuple_finitePlace {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℤ)
    (hx : Finset.univ.gcd x = 1) (v : FinitePlace K) : (⨆ i, v (x i:K)) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have hle (z : ℤ) : v (z:K) ≤ 1 := IsNonarchimedean.apply_intCast_le_one hv
  obtain ⟨a,ha⟩ := Finset.gcd_eq_sum_mul .univ x
  have he := congrArg (fun z : ℤ => v (z:K)) ha
  simp only [hx,Int.cast_one,map_one,Int.cast_sum,Int.cast_mul] at he
  have hsum := he.trans_le hv.apply_sum_univ_le
  obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f := fun i => v ((x i:K)*(a i:K)))
  rw [← hi,map_mul] at hsum
  exact le_antisymm (ciSup_le fun j => hle (x j))
    (Finite.le_ciSup_of_le i (hsum.trans (mul_le_of_le_one_right (apply_nonneg v _) (hle _))))

/-- Every primitive rational projective tuple gains precisely the field degree
as an exponent in its unnormalized multiplicative height. -/
theorem primitiveTuple_height_baseChange {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℤ)
    (hx : Finset.univ.gcd x = 1) :
    mulHeight (fun i => (x i:K)) = mulHeight (fun i => (x i:ℚ)) ^ d := by
  have hn : (fun i => (x i:K)) ≠ 0 := by
    intro hz
    have he : x=0 := funext fun i => Int.cast_eq_zero.mp (congrFun hz i)
    rw [he,Finset.gcd_eq_zero_iff.mpr (by simp)] at hx
    exact zero_ne_one hx
  rw [NumberField.mulHeight_eq hn,finprod_eq_one_of_forall_eq_one (primitiveTuple_finitePlace K x hx),mul_one]
  have hr := Rat.mulHeight_eq_max_abs_of_gcd_eq_one hx
  change mulHeight (fun i => (x i:ℚ)) = _ at hr
  rw [hr]
  have hm (v : InfinitePlace K) : (⨆ i, v (x i:K)) = ((⨆ i, |x i| : ℤ):ℝ) := by
    rw [Finite.map_iSup_of_monotone _ Int.cast_mono]
    apply iSup_congr
    intro i
    rw [v.map_intCast,Int.norm_eq_abs,Int.cast_abs]
  simp only [hm,Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq]

private theorem height_num_den (F : Type*) [Field F] [CharZero F] [AdmissibleAbsValues F] (q : ℚ) :
    mulHeight₁ (q:F) = mulHeight (fun i : Fin 2 => ((![q.num,(q.den:ℤ)] i : ℤ):F)) := by
  rw [Rat.cast_def,mulHeight₁_div_eq_mulHeight]
  congr 1; funext i; fin_cases i <;> simp

/-- Logarithmic height of an arbitrary embedded rational in mathlib's relative convention. -/
theorem rational_relative_height_baseChange (q : ℚ) : logHeight₁ (q:K) = d * logHeight₁ q := by
  let x : Fin 2 → ℤ := ![q.num,q.den]
  have hx : Finset.univ.gcd x = 1 := by
    simpa [x,Finset.univ_fin2,Int.normalize_coe_nat,← Int.coe_gcd q.num q.den] using
      Int.isCoprime_iff_gcd_eq_one.mp (Rat.isCoprime_num_den q)
  have hK : mulHeight₁ (q:K) = mulHeight (fun i => (x i:K)) := height_num_den K q
  have hQ : mulHeight₁ q = mulHeight (fun i => (x i:ℚ)) := by
    simpa only [Rat.cast_id] using height_num_den ℚ q
  rw [logHeight₁_eq_log_mulHeight₁,logHeight₁_eq_log_mulHeight₁,hK,hQ,
    primitiveTuple_height_baseChange K x hx,Real.log_pow]

/-- On all rational elements the local sum itself is independent of the ambient number field. -/
theorem rational_weighted_local_height (q : ℚ) : weightedLocalHeight K (q:K) = logHeight₁ q := by
  rw [weightedLocalHeight_eq,rational_relative_height_baseChange]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')

/-- An additional division gives the printed expression in terms of the rational absolute height. -/
theorem twice_normalized_rational_height (q : ℚ) :
    weightedLocalHeight K (q:K) / d = logHeight₁ q / d := by rw [rational_weighted_local_height]

/-- In the full dyadic cyclotomic tower the twice-divided height falls by a factor of two per step. -/
theorem twice_normalized_cyclotomic (n : ℕ) (q : ℚ) :
    let L := CyclotomicField (2^(n+1)) ℚ
    weightedLocalHeight L (q:L) / Module.finrank ℚ L = logHeight₁ q / 2^n := by
  dsimp only
  let m := 2^(n+1)
  have hm : 0 < m := pow_pos zero_lt_two _
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero (m:ℚ) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  letI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) := CyclotomicField.isCyclotomicExtension m ℚ
  have hd := IsCyclotomicExtension.finrank (CyclotomicField m ℚ) (Polynomial.cyclotomic.irreducible_rat hm)
  have hdeg : Module.finrank ℚ (CyclotomicField m ℚ) = 2^n := by
    rw [hd,Nat.totient_prime_pow_succ Nat.prime_two]; simp
  rw [twice_normalized_rational_height,hdeg,Nat.cast_pow,Nat.cast_ofNat]

/-- For the fixed number two the extra division already fails after adjoining i. -/
theorem twice_normalized_height_gaussian :
    let L := CyclotomicField 4 ℚ
    weightedLocalHeight L (2:L) / Module.finrank ℚ L = Real.log 2 / 2 ∧
      weightedLocalHeight L (2:L) / Module.finrank ℚ L < weightedLocalHeight ℚ (2:ℚ) := by
  have he := twice_normalized_cyclotomic 1 (2:ℚ)
  have h₂ : logHeight₁ (2:ℚ) = Real.log 2 := Rat.logHeight₁_natCast 2
  dsimp only at he ⊢
  norm_num only [Nat.reduceAdd,Nat.reducePow,Rat.cast_ofNat,pow_one,h₂] at he
  have hr : weightedLocalHeight ℚ (2:ℚ) = Real.log 2 := by
    simpa only [Rat.cast_ofNat,h₂] using rational_weighted_local_height ℚ (2:ℚ)
  refine ⟨he,he.trans_lt ?_⟩
  rw [hr]; linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]

/-- For every rational of positive height the written expression can approach zero
through ambient fields while the normalized local sum stays fixed. -/
theorem twice_normalized_cyclotomic_tendsTo_zero (q : ℚ) :
    Tendsto (fun n : ℕ => let L := CyclotomicField (2^(n+1)) ℚ
      weightedLocalHeight L (q:L) / Module.finrank ℚ L) atTop (𝓝 0) := by
  simp_rw [twice_normalized_cyclotomic,div_eq_mul_inv,← inv_pow]
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹)
    (by norm_num : (2:ℝ)⁻¹<1)).const_mul (logHeight₁ q)

#print axioms weightedArchNorm_pow
#print axioms weightedArchNorm_eq
#print axioms weightedArchNorm_rational
#print axioms weightedArchNorm_two_eq_norm_iff
#print axioms twice_normalized_rational_height
#print axioms weightedLocalHeight_eq
#print axioms primitiveTuple_finitePlace
#print axioms primitiveTuple_height_baseChange
#print axioms rational_relative_height_baseChange
#print axioms rational_weighted_local_height
#print axioms twice_normalized_cyclotomic
#print axioms twice_normalized_height_gaussian
#print axioms twice_normalized_cyclotomic_tendsTo_zero

end GaloisForLFunctions.KodairaParshinAbc
