import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheExactCodebookSizeOfAZeroSample

/-!
# Growth of finite codebooks as precision increases

Each sampled point to the right contributes one factor of the inverse
tolerance. A uniform polynomial degree therefore counts *all* distinct
right-hand points, even when their displacements approach zero arbitrarily
fast. At fixed tolerance only points strictly deeper than that tolerance
contribute. These two different quantifiers distinguish approach from landing.
-/

noncomputable section
open Finset Set Zeta23 Filter Topology
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

private def cells (h : ℝ) (z : ℂ) := max 1 ⌈rightDisplacement z / h⌉₊

private theorem count_on_layer (S : Finset ℂ) {h : ℝ} (hh : 0 < h) :
    zeroSampleCodeCount S h = ∏ z ∈ S.filter (fun z => h < rightDisplacement z), cells h z := by
  classical
  apply (Finset.prod_subset (filter_subset _ _) ?_).symm
  intro z hz hn
  have hd := le_of_not_gt (fun H => hn (mem_filter.mpr ⟨hz,H⟩))
  exact max_eq_left ((Nat.ceil_le).mpr (by simpa only [Nat.cast_one] using (div_le_one hh).mpr hd))

private theorem depth_le_one (Z : ZeroConfig) {z : ℂ} (hz : z ∈ Z.carrier) : rightDisplacement z ≤ 1 := by
  apply max_le _ zero_le_one
  linarith only [(Z.strip z hz).2]

/-- Cardinalities of finite codebooks bounded uniformly over all finite samples. -/
def boundedSampleCodebooks (Z : ZeroConfig) (h : ℝ) : Prop :=
  ∃ b : ℕ, ∀ S : Finset ℂ, (S : Set ℂ) ⊆ Z.carrier → zeroSampleCodeCount S h ≤ b

/-- At positive radius, a uniform finite codebook bound exists exactly
when the strict depth layer is finite. -/
theorem bounded_codebooks_iff_at_depth (Z : ZeroConfig) {h : ℝ} (hh : 0 < h) :
    boundedSampleCodebooks Z h ↔ (rightOf Z h).Finite := by
  classical
  rw [finite_layer_iff_depth_budget Z hh.le]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,fun S hS => (sample_measurements_iff S hh.le b).mpr ?_⟩
    let T := S.filter (fun z => h < rightDisplacement z)
    have h2 (z : ℂ) (hz : z ∈ T) : 2 ≤ cells h z := by
      have hg : 1 < ⌈rightDisplacement z / h⌉₊ := (Nat.lt_ceil).mpr (by
        simpa only [Nat.cast_one] using (one_lt_div hh).mpr (mem_filter.mp hz).2)
      exact (show 2 ≤ ⌈rightDisplacement z / h⌉₊ from hg).trans (le_max_right _ _)
    have hp := Finset.prod_le_prod' (s:=T) h2
    simp only [Finset.prod_const] at hp
    have hcap := hb S hS
    rw [count_on_layer S hh] at hcap
    exact (Nat.lt_two_pow_self (n:=T.card)).le.trans (hp.trans hcap)
  · rintro ⟨k,hk⟩
    let m := max 1 ⌈1/h⌉₊
    refine ⟨m^k,fun S hS => ?_⟩
    let T := S.filter (fun z => h < rightDisplacement z)
    have hmax (z : ℂ) (hz : z ∈ T) : cells h z ≤ m := max_le_max_left _ (Nat.ceil_le_ceil
      (div_le_div_of_nonneg_right (depth_le_one Z (hS (mem_filter.mp hz).1)) hh.le))
    rw [count_on_layer S hh]
    exact (Finset.prod_le_prod' (s:=T) hmax).trans (by
      rw [Finset.prod_const]
      exact pow_le_pow_right₀ (le_max_left _ _) ((sample_measurements_iff S hh.le k).mp (hk S hS)))

/-- A polynomial bound with one constant for every sample and precision. -/
def polynomialCodebookGrowth (Z : ZeroConfig) (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℂ, (S : Set ℂ) ⊆ Z.carrier →
    (zeroSampleCodeCount S (1/(n:ℝ)):ℝ) ≤ C*(n:ℝ)^k

private theorem count_on_positive (S : Finset ℂ) (n : ℕ) :
    zeroSampleCodeCount S (1/(n:ℝ)) =
      ∏ z ∈ S.filter (fun z => 0 < rightDisplacement z), max 1 ⌈rightDisplacement z*n⌉₊ := by
  classical
  simp only [zeroSampleCodeCount,div_eq_mul_inv,one_mul,inv_inv]
  apply (Finset.prod_subset (filter_subset _ _) ?_).symm
  intro z hz hn
  have he : rightDisplacement z=0 := le_antisymm
    (le_of_not_gt (fun hp => hn (mem_filter.mpr ⟨hz,hp⟩))) (le_max_right _ _)
  simp [he]

/-- Beyond the exponent, the leading coefficient of the minimum codebook
size is exactly the product of all positive displacements in the sample. -/
theorem reciprocal_radius_codebook_content (S : Finset ℂ) :
    let T := S.filter (fun z => 0 < rightDisplacement z)
    Tendsto (fun n : ℕ => (zeroSampleCodeCount S (1/(n:ℝ)):ℝ)/(n:ℝ)^T.card) atTop
      (𝓝 (∏ z ∈ T, rightDisplacement z)) := by
  intro T
  have hlim (z : ℂ) (hz : z ∈ T) :
      Tendsto (fun n : ℕ => (max 1 ⌈rightDisplacement z*n⌉₊ : ℕ)/(n:ℝ)) atTop (𝓝 (rightDisplacement z)) := by
    let d := rightDisplacement z
    have hd : 0 < d := (mem_filter.mp hz).2
    have hupper := (tendsto_const_nhds (x:=d) (f:=atTop (α:=ℕ))).add
      (tendsto_natCast_atTop_atTop (R:=ℝ)).inv_tendsto_atTop
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x:=d)) (by
      simpa only [add_zero] using hupper)
    · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
      apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
    · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
      have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
      have hd' := mul_pos hd hn'
      have hm : 1 ≤ ⌈d*n⌉₊ := (Nat.lt_ceil.mpr (by simpa only [Nat.cast_zero] using hd'))
      change (max 1 ⌈d*n⌉₊:ℕ)/(n:ℝ) ≤ d+(n:ℝ)⁻¹
      rw [max_eq_right hm,div_le_iff₀ hn',add_mul,inv_mul_cancel₀ hn'.ne']
      exact (Nat.ceil_lt_add_one hd'.le).le
  have H := tendsto_finsetProd T hlim
  apply H.congr
  intro n
  rw [Finset.prod_div_distrib,Finset.prod_const,count_on_positive,Nat.cast_prod]

private theorem depth_product_lower (S : Finset ℂ) (n : ℕ) :
    (∏ z ∈ S, rightDisplacement z)*(n:ℝ)^S.card ≤ zeroSampleCodeCount S (1/(n:ℝ)) := by
  rw [← Finset.prod_const (s:=S) (b:=(n:ℝ)),← Finset.prod_mul_distrib,zeroSampleCodeCount,Nat.cast_prod]
  apply Finset.prod_le_prod (fun z _ => mul_nonneg (show 0 ≤ rightDisplacement z from le_max_right _ _) (Nat.cast_nonneg n))
  intro z _
  rw [show rightDisplacement z/(1/(n:ℝ)) = rightDisplacement z*n by simp only [div_eq_mul_inv,one_mul,inv_inv]]
  exact (Nat.le_ceil (rightDisplacement z*n)).trans (Nat.cast_le.mpr (le_max_right 1 _))

/-- The exact allowed polynomial degrees are the integers at least as
large as the total number of distinct points right of the critical line. -/
theorem polynomial_codebook_growth_iff (Z : ZeroConfig) (k : ℕ) :
    polynomialCodebookGrowth Z k ↔ depthMeasurementBudget Z 0 k := by
  classical
  constructor
  · rintro ⟨C,hC⟩ S hS
    apply (sample_measurements_iff S le_rfl k).mpr
    let T := S.filter (fun z => 0 < rightDisplacement z)
    let p := ∏ z ∈ T, rightDisplacement z
    have hp : 0 < p := Finset.prod_pos (fun z hz => (mem_filter.mp hz).2)
    by_contra! hcard
    have hk : k+1 ≤ T.card := hcard
    obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (C/p))
    have hn1 : 1 < (n:ℝ) := (le_max_left _ _).trans_lt hn
    have hn' : 1 ≤ n := by exact_mod_cast hn1.le
    have hc := (depth_product_lower T n).trans (hC n hn' T (fun _ hz => hS (mem_filter.mp hz).1))
    have hsmall : p*(n:ℝ)^(k+1) ≤ C*(n:ℝ)^k :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1.le hk) hp.le).trans hc
    have hle : p*(n:ℝ) ≤ C := by
      apply le_of_mul_le_mul_right (a:=(n:ℝ)^k) _ (by positivity)
      rw [pow_succ] at hsmall
      simpa only [mul_right_comm,mul_assoc,mul_comm,mul_left_comm] using hsmall
    exact (not_lt_of_ge hle) (by
      simpa only [mul_comm] using (div_lt_iff₀ hp).mp ((le_max_right _ _).trans_lt hn))
  · intro H
    refine ⟨1,fun n hn S hS => ?_⟩
    let T := S.filter (fun z => 0 < rightDisplacement z)
    have hc := (sample_measurements_iff S le_rfl k).mp (H S hS)
    have hmax (z : ℂ) (hz : z ∈ T) : max 1 ⌈rightDisplacement z*n⌉₊ ≤ n :=
      max_le hn (Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg _) (depth_le_one Z (hS (mem_filter.mp hz).1))))
    have hcard : zeroSampleCodeCount S (1/(n:ℝ)) ≤ n^k := by
      rw [count_on_positive]
      exact (Finset.prod_le_prod' (s:=T) hmax).trans (by rw [Finset.prod_const]; exact pow_le_pow_right₀ hn hc)
    rw [one_mul]
    exact_mod_cast hcard

/-- Approach is finite coding at every positive radius. Landing asks
whether that forces polynomial coding in the reciprocal radius. -/
theorem actual_landing_iff_polynomial_codebooks :
    GaloisForLFunctions.ExceptionalLayerTheory.ZetaLandingLaw ↔
      ((∀ h : ℝ, 0 < h → boundedSampleCodebooks zetaZeroConfig h) →
        ∃ k, polynomialCodebookGrowth zetaZeroConfig k) := by
  rw [actual_landing_iff_exact_measurements]
  simp_rw [polynomial_codebook_growth_iff]
  have he : (∀ h : ℝ, 0 < h → ∃ k, depthMeasurementBudget zetaZeroConfig h k) ↔
      (∀ h : ℝ, 0 < h → boundedSampleCodebooks zetaZeroConfig h) :=
    forall₂_congr fun _ hh => (finite_layer_iff_depth_budget _ hh.le).symm.trans
      (bounded_codebooks_iff_at_depth _ hh).symm
  rw [he]

#print axioms bounded_codebooks_iff_at_depth
#print axioms reciprocal_radius_codebook_content
#print axioms polynomial_codebook_growth_iff
#print axioms actual_landing_iff_polynomial_codebooks

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
