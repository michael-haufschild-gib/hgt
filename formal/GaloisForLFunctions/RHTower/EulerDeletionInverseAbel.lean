import GaloisForLFunctions.RHTower.EulerDeletionMobiusPrimitiveEnergy

/-!
# Inverse Abel comparison for the complete deletion current

The phase-weighted source retains the full primitive energy. A finite
Cesaro estimate and the literal current weights give a reverse bound
at every hypothetical off-line zero, uniform in the arithmetic cutoff.
Together with the existing forward bound this fixes the same growth
scale in both descriptions; it produces no arithmetic upper bound.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionInverseAbel
open DeletionMobiusPrimitive DeletionMobiusCurrent DeletionPrimitiveHardy
open DeletionMixedCurrent DeletionReflectedEnergy DeletionReflectedCurrent
open DeletionReflectedGram DeletionJointCirculation DeletionChronologicalLimit


private theorem transpose_energy (b : ℕ → ℝ) (L : ℕ) :
    (∑ k ∈ Finset.range L,
      (∑ n ∈ Finset.range L, tailKernel (3/4) n k*b n)^2) ≤
      25*∑ n ∈ Finset.range L, b n^2 := by
  let y k := ∑ n ∈ Finset.range L, tailKernel (3/4) n k*b n
  let z n := ∑ k ∈ Finset.range L, tailKernel (3/4) n k*y k
  let S := ∑ k ∈ Finset.range L, y k^2
  let B := ∑ n ∈ Finset.range L, b n^2
  have heq : S = ∑ n ∈ Finset.range L, b n*z n := by
    calc S = ∑ k ∈ Finset.range L,
        (∑ n ∈ Finset.range L, tailKernel (3/4) n k*b n)*y k := by
          simp only [S, y, pow_two]
         _ = _ := by
          simp only [Finset.sum_mul, z, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro k hk
          ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L) b z
  rw [← heq] at hc
  have ht := finite_tail_energy_le (by norm_num : (1/2:ℝ) < 3/4)
    (by norm_num : (3/4:ℝ) < 1) y L L
  norm_num [schurConstant] at ht
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh : S^2 ≤ B*(25*S) := hc.trans (mul_le_mul_of_nonneg_left ht hB)
  change S ≤ 25*B
  nlinarith

private theorem finite_cesaro_energy (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (L : ℕ) :
    (∑ k ∈ Finset.range L, ((∑ n ∈ Finset.range k, b n)/((k:ℝ)+1))^2) ≤
      25*∑ n ∈ Finset.range L, b n^2 := by
  have hterm {n k : ℕ} (hnk : n < k) :
      1/((k:ℝ)+1) ≤ tailKernel (3/4) n k := by
    have hn : (0:ℝ) < n+1 := by positivity
    have hk : (0:ℝ) < k+1 := by positivity
    have hnk' : (n:ℝ)+1 ≤ k+1 := by exact_mod_cast (Nat.add_le_add_right hnk.le 1)
    have h := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hn hnk' (by norm_num : (-1/4:ℝ) ≤ 0))
      (Real.rpow_nonneg hk.le (-3/4))
    rw [← Real.rpow_add hk] at h
    norm_num only [show (-1/4:ℝ)+ -3/4 = -1 by norm_num, Real.rpow_neg_one] at h
    simpa only [tailKernel, if_pos hnk.le, show (3/4:ℝ)-1 = -1/4 by norm_num, neg_div, one_div] using h
  have hpoint (k : ℕ) (hk : k ∈ Finset.range L) :
      (∑ n ∈ Finset.range k, b n)/((k:ℝ)+1) ≤
        ∑ n ∈ Finset.range L, tailKernel (3/4) n k*b n := by
    rw [Finset.sum_div]
    calc _ ≤ ∑ n ∈ Finset.range k, tailKernel (3/4) n k*b n := by
           apply Finset.sum_le_sum
           intro n hn
           simpa [div_eq_mul_inv, mul_comm] using
             mul_le_mul_of_nonneg_right (hterm (Finset.mem_range.mp hn)) (hb n)
         _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
           (Finset.range_mono (Finset.mem_range.mp hk).le)
           (fun n _ _ => by
             have hb0 := hb n
             unfold tailKernel
             split_ifs <;> positivity)
  calc _ ≤ ∑ k ∈ Finset.range L,
        (∑ n ∈ Finset.range L, tailKernel (3/4) n k*b n)^2 := by
         apply Finset.sum_le_sum
         intro k hk
         exact pow_le_pow_left₀
           (div_nonneg (Finset.sum_nonneg (fun n _ => hb n)) (by positivity)) (hpoint k hk) 2
       _ ≤ _ := transpose_energy b L

private theorem positive_increment {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    {x : ℝ} (hx : 0 < x) :
    ‖((x+1:ℝ):ℂ)^s-(x:ℂ)^s‖ ≤ ‖s‖*x^(s.re-1) := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  have hpos {t : ℝ} (ht : t ∈ Set.uIcc x (x+1)) : 0 < t := by
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact hx.trans_le ht.1
  have hderiv : ∀ t ∈ Set.uIcc x (x+1),
      HasDerivWithinAt (fun y : ℝ => (y:ℂ)^s)
        (s*(t:ℂ)^(s-1)) (Set.uIcc x (x+1)) t := by
    intro t ht
    exact (hasDerivAt_ofReal_cpow_const (hpos ht).ne' hsne).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc x (x+1),
      ‖s*(t:ℂ)^(s-1)‖ ≤ ‖s‖*x^(s.re-1) := by
    intro t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos ht)]
    simp only [Complex.sub_re, Complex.one_re]
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)) (norm_nonneg _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_uIcc _ _) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa using h

/-- The original arithmetic primitive is recovered from the entire phase-weighted prefix. -/
theorem primitive_inverse_abel (N k : ℕ) (s : ℂ) :
    primitive N (k+1)=(((k:ℝ)+1:ℝ):ℂ)^s*sourcePrefix N s (k+1)-
      ∑ n ∈ Finset.range k,
        ((((n:ℝ)+2:ℝ):ℂ)^s-(((n:ℝ)+1:ℝ):ℂ)^s)*sourcePrefix N s (n+1) := by
  have hp (n : ℕ) : sourcePath N 0 n=(((n:ℝ)+1:ℝ):ℂ)^s*sourcePath N s n := by
    simp only [sourcePath, mixedPath, eulerDeletionWeightedJump, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hn : (((n:ℝ)+1:ℝ):ℂ) ≠ 0 := by exact_mod_cast (show (n:ℝ)+1 ≠ 0 by positivity)
    simp only [neg_zero, Complex.cpow_zero, mul_one]
    calc _ = coefficient p*eulerDeletionDirichletCoefficient p n*
        ((((n:ℝ)+1:ℝ):ℂ)^s*(((n:ℝ)+1:ℝ):ℂ)^(-s)) := by
          rw [← Complex.cpow_add _ _ hn, add_neg_cancel, Complex.cpow_zero, mul_one]
         _ = _ := by ring
  have heq : primitive N (k+1)=∑ n ∈ Finset.range (k+1),
      (((n:ℝ)+1:ℝ):ℂ)^s*sourcePath N s n := by
    simp only [primitive, sourcePrefix, endpoint]
    exact Finset.sum_congr rfl (fun n _ => hp n)
  have h := Finset.sum_range_by_parts
    (fun n : ℕ => (((n:ℝ)+1:ℝ):ℂ)^s) (sourcePath N s) (k+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
  rw [heq, h]
  simp only [sourcePrefix, endpoint, add_assoc, one_add_one_eq_two]

private def normalizedSource (N : ℕ) (s : ℂ) (k : ℕ) : ℝ :=
  ((k:ℝ)+1)^(s.re-1)*‖sourcePrefix N s (k+1)‖

private theorem normalized_inverse_le (N k : ℕ) {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) :
    normalizedPrimitive N k ≤ normalizedSource N s k+
      ‖s‖*((∑ n ∈ Finset.range k, normalizedSource N s n)/((k:ℝ)+1)) := by
  have hx : (0:ℝ) < k+1 := by positivity
  have h := norm_sub_le
    ((((k:ℝ)+1:ℝ):ℂ)^s*sourcePrefix N s (k+1))
    (∑ n ∈ Finset.range k,
      ((((n:ℝ)+2:ℝ):ℂ)^s-(((n:ℝ)+1:ℝ):ℂ)^s)*sourcePrefix N s (n+1))
  rw [← primitive_inverse_abel] at h
  have hsum : ‖∑ n ∈ Finset.range k,
      ((((n:ℝ)+2:ℝ):ℂ)^s-(((n:ℝ)+1:ℝ):ℂ)^s)*sourcePrefix N s (n+1)‖ ≤
        ‖s‖*∑ n ∈ Finset.range k, normalizedSource N s n := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    have hb := mul_le_mul_of_nonneg_right
      (positive_increment hs hs' (x := (n:ℝ)+1) (by positivity))
      (norm_nonneg (sourcePrefix N s (n+1)))
    simpa [normalizedSource, add_assoc, one_add_one_eq_two, mul_assoc] using hb
  have hh := div_le_div_of_nonneg_right (h.trans (add_le_add_right hsum _)) hx.le
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx] at hh
  have heq : (((k:ℝ)+1)^s.re*‖sourcePrefix N s (k+1)‖+
      ‖s‖*∑ n ∈ Finset.range k, normalizedSource N s n)/((k:ℝ)+1) =
      normalizedSource N s k+
        ‖s‖*((∑ n ∈ Finset.range k, normalizedSource N s n)/((k:ℝ)+1)) := by
    rw [normalizedSource, Real.rpow_sub hx, Real.rpow_one]
    ring
  exact hh.trans_eq heq

private theorem finite_inverse_energy (N L : ℕ) {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) :
    (∑ k ∈ Finset.range L, normalizedPrimitive N k^2) ≤
      2*(1+25*‖s‖^2)*∑ k ∈ Finset.range L, normalizedSource N s k^2 := by
  let b := normalizedSource N s
  let c k := (∑ n ∈ Finset.range k, b n)/((k:ℝ)+1)
  have hb : ∀ k, 0 ≤ b k := fun k => by dsimp [b, normalizedSource]; positivity
  have hc : ∀ k, 0 ≤ c k := fun k =>
    div_nonneg (Finset.sum_nonneg (fun n _ => hb n)) (by positivity)
  have hpoint (k : ℕ) : normalizedPrimitive N k^2 ≤ 2*(b k^2+‖s‖^2*c k^2) := by
    have hp := normalized_inverse_le N k hs hs'
    change normalizedPrimitive N k ≤ b k+‖s‖*c k at hp
    have hn : 0 ≤ normalizedPrimitive N k := by unfold normalizedPrimitive; positivity
    have hm : 0 ≤ ‖s‖*c k := mul_nonneg (norm_nonneg _) (hc k)
    nlinarith [sq_nonneg (b k-‖s‖*c k)]
  have ht := finite_cesaro_energy b hb L
  calc _ ≤ ∑ k ∈ Finset.range L, 2*(b k^2+‖s‖^2*c k^2) :=
         Finset.sum_le_sum (fun k _ => hpoint k)
       _ = 2*((∑ k ∈ Finset.range L, b k^2)+‖s‖^2*∑ k ∈ Finset.range L, c k^2) := by
         rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
       _ ≤ 2*((∑ k ∈ Finset.range L, b k^2)+‖s‖^2*(25*∑ k ∈ Finset.range L, b k^2)) := by
         gcongr
       _ = _ := by ring

private theorem increment_lower {a x : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hx : 1 ≤ x) : a/2*x^(a-1) ≤ (x+1)^a-x^a := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy : 0 < x+1 := by linarith
  have hr : 0 ≤ 1-1/(x+1) := by
    have h := (div_le_one hy).2 (by linarith : 1 ≤ x+1)
    linarith
  have hb := rpow_one_add_le_one_add_mul_self
    (s := -1/(x+1)) (by rw [neg_div]; linarith) ha.le ha'.le
  have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy.le a)
  have hp : (x+1)*(1+-1/(x+1))=x := by field_simp; ring
  rw [← Real.mul_rpow hy.le (by rw [neg_div]; linarith), hp] at hm
  have he : (x+1)^a*(1+a*(-1/(x+1))) =
      (x+1)^a-a*(x+1)^(a-1) := by
    rw [Real.rpow_sub hy, Real.rpow_one]
    ring
  rw [he] at hm
  have hcompare : x^(a-1)/2 ≤ (x+1)^(a-1) := by
    rw [Real.rpow_sub hx0, Real.rpow_sub hy, Real.rpow_one, Real.rpow_one]
    calc x^a/x/2 = x^a/(2*x) := by ring
         _ ≤ x^a/(x+1) := by gcongr; linarith
         _ ≤ (x+1)^a/(x+1) := by gcongr; linarith
  have hmul := mul_le_mul_of_nonneg_left hcompare ha.le
  nlinarith

/-- Explicit reverse transfer from the full current to the original arithmetic energy. -/
theorem primitiveEnergy_le_current (N : ℕ) (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2 < rho.1.re) :
    primitiveEnergy N ≤ 4*(1+25*‖rho.1‖^2)/exponent rho.1*
      (sourceCurrent N rho.1).re := by
  have hs0 := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hs1 := RiemannGaussian.NontrivialZetaZero.re_lt_one rho
  have ha : 0 < exponent rho.1 := by unfold exponent; linarith
  have ha1 : exponent rho.1 < 1 := by unfold exponent; linarith
  have hpoint (k : ℕ) :
      exponent rho.1/2*normalizedSource N rho.1 k^2 ≤
        mixedEnergy (Finset.range N) coefficient rho.1 k := by
    have h := mul_le_mul_of_nonneg_right
      (increment_lower ha ha1 (x := (k:ℝ)+1)
        (by have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith))
      (sq_nonneg (‖sourcePrefix N rho.1 (k+1)‖))
    have he : normalizedSource N rho.1 k^2 =
        ((k:ℝ)+1)^(exponent rho.1-1)*‖sourcePrefix N rho.1 (k+1)‖^2 := by
      rw [normalizedSource, mul_pow, pow_two (((k:ℝ)+1)^(rho.1.re-1)),
        ← Real.rpow_add (show (0:ℝ) < (k:ℝ)+1 by positivity)]
      congr 2
      unfold exponent
      ring
    rw [he, ← mul_assoc]
    simpa only [mixedEnergy, weight, sourcePrefix, sourcePath, Nat.cast_add,
      Nat.cast_one, add_assoc] using h
  have hfinite (L : ℕ) :
      (∑ k ∈ Finset.range L, normalizedPrimitive N k^2) ≤
        4*(1+25*‖rho.1‖^2)/exponent rho.1*(sourceCurrent N rho.1).re := by
    have hsum : exponent rho.1/2*
        (∑ k ∈ Finset.range L, normalizedSource N rho.1 k^2) ≤
          (sourceCurrent N rho.1).re := by
      rw [Finset.mul_sum]
      exact (Finset.sum_le_sum (fun k _ => hpoint k)).trans
        (mixed_energy_prefix_le_current (Finset.range N) coefficient rho hs.le L)
    have hb : (∑ k ∈ Finset.range L, normalizedSource N rho.1 k^2) ≤
        2/exponent rho.1*(sourceCurrent N rho.1).re := by
      have hb : (∑ k ∈ Finset.range L, normalizedSource N rho.1 k^2) ≤
          (sourceCurrent N rho.1).re/(exponent rho.1/2) := by
        rw [le_div_iff₀ (by positivity : 0 < exponent rho.1/2)]
        nlinarith [hsum]
      convert hb using 1 <;> ring
    calc _ ≤ 2*(1+25*‖rho.1‖^2)*
          ∑ k ∈ Finset.range L, normalizedSource N rho.1 k^2 :=
            finite_inverse_energy N L hs0 hs1
         _ ≤ 2*(1+25*‖rho.1‖^2)*
          (2/exponent rho.1*(sourceCurrent N rho.1).re) := by gcongr
         _ = _ := by ring
  exact le_of_tendsto (summable_normalizedPrimitive_sq N).hasSum.tendsto_sum_nat
    (Eventually.of_forall hfinite)

/-- At every hypothetical off-line zero, the current and primitive energies have the same
cutoff growth up to positive constants. No arithmetic upper bound is assumed or produced. -/
theorem off_line_energy_comparison :
    ∀ rho : RiemannGaussian.NontrivialZetaZero, rho.1.re ≠ 1/2 →
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ N : ℕ,
        primitiveEnergy N ≤ C*|(sourceCurrent N rho.1).re| ∧
        |(sourceCurrent N rho.1).re| ≤ D*primitiveEnergy N := by
  intro rho hs
  obtain ⟨D,hD,hupper⟩ := exists_current_bound_by_primitiveEnergy rho
  have hright (r : RiemannGaussian.NontrivialZetaZero) (hr : 1/2 < r.1.re) :
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
        primitiveEnergy N ≤ C*|(sourceCurrent N r.1).re| := by
    have ha : 0 < exponent r.1 := by unfold exponent; linarith
    let C := 4*(1+25*‖r.1‖^2)/exponent r.1
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C,hC,fun N => (primitiveEnergy_le_current N r hr).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hC.le
  rcases lt_or_gt_of_ne hs with hleft | hright'
  · let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
    have hr : r.1=partner rho.1 := rfl
    have hrre : 1/2 < r.1.re := by
      rw [hr]
      simp only [partner, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
      linarith
    obtain ⟨C,hC,hlo⟩ := hright r hrre
    refine ⟨C,D,hC,hD,fun N => ⟨?_,hupper N⟩⟩
    simpa only [hr, sourceCurrent_partner, Complex.neg_re, abs_neg] using hlo N
  · obtain ⟨C,hC,hlo⟩ := hright rho hright'
    exact ⟨C,D,hC,hD,fun N => ⟨hlo N,hupper N⟩⟩

end RHTower.DeletionInverseAbel
end
