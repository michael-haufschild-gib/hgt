import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.PolynomialCountEulerFactors
import GaloisForLFunctions.HTGeometry.SparsePolynomialPositiveRoots
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Recovery of sparse point counts from extension degrees

Distinct extension sizes give positive roots of the difference of counting
polynomials. The sparse root bound gives unique recovery with errors, and an
alternating product gives sharp collisions.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial Finset
open scoped Classical
noncomputable section

/-- Degree samples on which two polynomial-count schemes give the same point count. -/
def agreeingDegrees (q : ℕ) (S : Finset ℕ) (P Q : ℤ[X]) :=
  S.filter fun n => P.eval (((q:ℤ)+2)^n) = Q.eval (((q:ℤ)+2)^n)

/-- Every agreeing sample gives a distinct positive root. The sparse bound
depends on the number of Tate degrees, independently of their magnitudes. -/
theorem agreeingDegrees_bound (q : ℕ) (S : Finset ℕ) {P Q : ℤ[X]} (hne : P ≠ Q) :
    (agreeingDegrees q S P Q).card+1 ≤ (P.support ∪ Q.support).card := by
  let b : ℤ := (q:ℤ)+2
  let f := Int.castRingHom ℝ
  let H := (P-Q).map f
  have hne' : H ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr (sub_ne_zero.mpr hne)
  let x (n : ℕ) := f (b^n)
  have hb : 1 < b := by dsimp [b]; omega
  have hi : Function.Injective x := Int.cast_injective.comp (pow_right_strictMono₀ hb).injective
  have hz : (agreeingDegrees q S P Q).image x ⊆ posRoots H := by
    intro u hu
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hu
    have hn' : P.eval (b^n)=Q.eval (b^n) := (mem_filter.mp hn).2
    apply (mem_posRoots hne').mpr
    refine ⟨by exact_mod_cast (pow_pos (zero_lt_one.trans hb) n),?_⟩
    change ((P-Q).map f).eval (f (b^n))=0
    rw [Polynomial.eval_map,Polynomial.eval₂_at_apply,Polynomial.eval_sub,hn',sub_self,map_zero]
  have hs : H.support ⊆ P.support ∪ Q.support := by
    intro j hj
    by_contra! h
    have hp := Polynomial.notMem_support_iff.mp h.1
    have hq := Polynomial.notMem_support_iff.mp h.2
    exact (Polynomial.mem_support_iff.mp hj) (by simp [H,Polynomial.coeff_map,hp,hq])
  have h₁ := card_le_card hz
  rw [card_image_of_injective _ hi] at h₁
  exact (Nat.succ_le_succ h₁).trans ((card_posRoots_succ_le hne').trans (card_le_card hs))

/-- Twice the sparsity suffices even for unknown exponent sets and
arbitrary distinct extension degrees. -/
theorem finiteSamples_determine_sparseCounts (q : ℕ) (S : Finset ℕ) (P Q : ℤ[X])
    (hsize : (P.support ∪ Q.support).card ≤ S.card) :
    (∀ n ∈ S, P.eval (((q:ℤ)+2)^n)=Q.eval (((q:ℤ)+2)^n)) ↔ P=Q := by
  constructor
  · intro h
    by_contra hn
    have hh := agreeingDegrees_bound q S hn
    have he : agreeingDegrees q S P Q = S := filter_eq_self.mpr h
    rw [he] at hh
    omega
  · rintro rfl n _
    rfl

/-- Adversarial errors in the reported extension counts are correctable
whenever twice the error budget fits beyond the number of possible Tate degrees. -/
theorem extensionSample_errorCorrection (q : ℕ) (S : Finset ℕ) (P Q : ℤ[X]) (v : ℕ → ℤ) (e : ℕ)
    (hp : (S.filter fun n => P.eval (((q:ℤ)+2)^n) ≠ v n).card ≤ e)
    (hq : (S.filter fun n => Q.eval (((q:ℤ)+2)^n) ≠ v n).card ≤ e)
    (hsize : (P.support ∪ Q.support).card + 2*e ≤ S.card) : P=Q := by
  by_contra hn
  have hh := agreeingDegrees_bound q S hn
  let E := (S.filter fun n => P.eval (((q:ℤ)+2)^n) ≠ v n) ∪
    (S.filter fun n => Q.eval (((q:ℤ)+2)^n) ≠ v n)
  have hs : S ⊆ agreeingDegrees q S P Q ∪ E := by
    intro n hx
    by_cases hp' : P.eval (((q:ℤ)+2)^n) = v n
    · by_cases hq' : Q.eval (((q:ℤ)+2)^n) = v n
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,hp'.trans hq'.symm⟩)
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hx,hq'⟩))
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hx,hp'⟩))
  have hcard := (card_le_card hs).trans (card_union_le _ _)
  have hE : E.card ≤ e+e := (card_union_le _ _).trans (add_le_add hp hq)
  omega

private theorem sum_pairs {R : Type*} [AddCommMonoid R] (f : ℕ → R) (s : ℕ) :
    ∑ j ∈ range (2*s), f j = ∑ i ∈ range s, (f (2*i)+f (2*i+1)) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show 2*(s+1)=(2*s+1)+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ,add_assoc]

/-- Sharpness at one fewer sample, even for nonnegative counts. The two models
are disjoint unions of affine spaces of even and odd dimensions, respectively.
Their difference factors at every prescribed sample size. -/
theorem evenOdd_sample_collision (s : ℕ) (b : Fin (2*s+1) → ℕ+) :
    ∃ a c : Fin (s+1) → ℕ, 0 < a 0 ∧
      ∀ j, (∑ i, a i*(b j).val^(2*i.val)) = ∑ i, c i*(b j).val^(2*i.val+1) := by
  let H : ℕ[X] := ∏ j, (X+C (b j).val)
  have hdeg : H.natDegree = 2*s+1 := by
    dsimp [H]
    rw [natDegree_prod_of_monic]
    · simp [natDegree_X_add_C]
    · exact fun i _ => monic_X_add_C _
  refine ⟨fun i => H.coeff (2*i.val),fun i => H.coeff (2*i.val+1),?_,?_⟩
  · change 0 < H.coeff 0
    have he : H.coeff 0 = ∏ j, (b j).val := by
      rw [← Polynomial.eval_zero]
      simp [H,eval_prod]
    rw [he]
    exact prod_pos fun j _ => (b j).property
  · intro j
    let x : ℤ := (b j).val
    have hz : H.eval₂ (Nat.castRingHom ℤ) (-x) = 0 := by
      rw [show H = ∏ j, (X+C (b j).val) by rfl,eval₂_finsetProd]
      apply prod_eq_zero (mem_univ j)
      simp [x]
    rw [eval₂_eq_sum_range' _ (show H.natDegree < 2*(s+1) by omega),sum_pairs,
      sum_add_distrib] at hz
    have he (i : ℕ) : (-x)^(2*i) = x^(2*i) := by simp [pow_mul]
    have ho (i : ℕ) : (-x)^(2*i+1) = -(x^(2*i+1)) := by rw [pow_succ,he,pow_succ]; ring
    simp only [Nat.castRingHom_apply,he,ho,mul_neg,sum_neg_distrib] at hz
    rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range]
    exact_mod_cast (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hz) :
      (∑ i ∈ range (s+1), (H.coeff (2*i):ℤ)*x^(2*i)) =
        ∑ i ∈ range (s+1), (H.coeff (2*i+1):ℤ)*x^(2*i+1))

open PowerSeries in
/-- Truncated normalized local factors determine all ghost components through
the same degree. Multiplying by a unit preserves the truncated congruence. -/
private theorem ghost_trunc_congr {F F' G G' : PowerSeries ℂ} (hF : HasGhost F G)
    (hF' : HasGhost F' G') (h₀ : PowerSeries.constantCoeff F = 1) (n : ℕ)
    (he : trunc n F = trunc n F') : trunc n G = trunc n G' := by
  have hcoeff (j : ℕ) (hj : j<n) : PowerSeries.coeff j F=PowerSeries.coeff j F' := by
    simpa only [coeff_trunc,if_pos hj] using congrArg (fun p : ℂ[X] => p.coeff j) he
  have hd : trunc n (F*G) = trunc n (F'*G') := by
    rw [← hF,← hF']
    ext j
    rw [coeff_trunc,coeff_trunc]
    split_ifs with hj
    · cases j with
      | zero => simp
      | succ j => rw [coeff_succ_X_mul,coeff_succ_X_mul,coeff_derivative,coeff_derivative,hcoeff _ hj]
    · rfl
  have hd' : trunc n (F*G) = trunc n (F*G') := by
    rw [hd,← trunc_trunc_mul (n := n) F' G',← he,trunc_trunc_mul]
  have hu : IsUnit F := PowerSeries.isUnit_iff_constantCoeff.mpr (h₀ ▸ isUnit_one)
  obtain ⟨u,rfl⟩ := hu
  have hh := congrArg (fun p : ℂ[X] => trunc n ((↑u⁻¹ : PowerSeries ℂ)*(p:PowerSeries ℂ))) hd'
  simpa only [trunc_mul_trunc,← mul_assoc,Units.inv_mul,one_mul] using hh

open PowerSeries in
/-- Finitely many Taylor coefficients of one local factor determine the
entire zeta function, with a bound in the number of Tate degrees alone. -/
theorem polynomialCountZeta_trunc_eq_iff (q : ℕ) (P Q : ℤ[X]) (N : ℕ)
    (hN : (P.support ∪ Q.support).card ≤ N) :
    trunc (N+1) (polynomialCountZeta P (((q:ℝ)+2:ℝ):ℂ)) =
      trunc (N+1) (polynomialCountZeta Q (((q:ℝ)+2:ℝ):ℂ)) ↔ P=Q := by
  refine ⟨fun he => ?_,fun h => h ▸ rfl⟩
  let S := (range N).image Nat.succ
  have hc : S.card=N := by simp [S,card_image_of_injective _ Nat.succ_injective]
  apply (finiteSamples_determine_sparseCounts q S P Q (hN.trans_eq hc.symm)).mp
  intro m hm
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
  have hm' : j+1<N+1 := Nat.succ_lt_succ (mem_range.mp hj)
  have hg := ghost_trunc_congr (polynomialCountZeta_hasGhost P _) (polynomialCountZeta_hasGhost Q _)
    (polynomialCountZeta_constant P _) (N+1) he
  have hh := congrArg (fun p : ℂ[X] => p.coeff (j+1)) hg
  simp only [coeff_trunc,if_pos hm',polynomialCountSeries,coeff_mk,Nat.succ_ne_zero,if_false] at hh
  let b : ℤ := (q:ℤ)+2
  have hb : (Int.castRingHom ℂ) b = (((q:ℝ)+2:ℝ):ℂ) := by simp [b]
  rw [← hb,← map_pow,eval₂_at_apply,eval₂_at_apply] at hh
  exact Int.cast_injective hh

end
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
