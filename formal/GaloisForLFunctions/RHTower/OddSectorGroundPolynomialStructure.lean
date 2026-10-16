import GaloisForLFunctions.RHTower.OddSectorPairedGroundDivision
import Mathlib.Algebra.Polynomial.Sequence

/-!
# One common entire factor for the arithmetic-corrected odd ground space

At every positive aperture the exact odd ground space has a polynomial
representation in squared frequency, with degree below its dimension. A single
nonzero odd ground transform generates the whole space, and its zeros lie on
the real or imaginary axis. Every blind minimizer is a uniquely determined
polynomial times this common factor.

The generator is obtained by simultaneous vanishing at finitely many off-axis
points and paired division. Distinct polynomial degrees give a basis. Another
off-axis zero of the generator would force a polynomial inverse of `X-z²`.
-/

open Complex MeasureTheory Set Filter Topology Polynomial
open scoped InnerProduct
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature

private def pairedDivisionPoint (k : ℕ) : ℂ := (k : ℂ)+1+I

private theorem pairedDivisionPoint_sq_im (k : ℕ) :
    (pairedDivisionPoint k ^ 2).im = 2*((k : ℝ)+1) := by
  simp [pairedDivisionPoint,pow_two]
  ring

private theorem pairedDivisionPoint_admissible (k : ℕ) :
    (pairedDivisionPoint k ^ 2).im ≠ 0 := by
  rw [pairedDivisionPoint_sq_im]
  positivity

private theorem pairedDivisionPoint_sq_injective :
    Function.Injective (fun k => pairedDivisionPoint k ^ 2) := by
  intro i j h
  have he := congrArg Complex.im h
  rw [pairedDivisionPoint_sq_im,pairedDivisionPoint_sq_im] at he
  have hij : (i : ℝ) = j := by linarith
  exact_mod_cast hij

private theorem exists_paired_div_prod (a : SuzukiPositiveAperture)
    {u : CCMArchimedeanFormDomain a} (hu : u ∈ oddArithmeticGroundSpace a) :
    ∀ k : ℕ,(∀ i < k,unitaryLaplace (timeRep a u) (pairedDivisionPoint i) = 0) →
      ∃ v : CCMArchimedeanFormDomain a,v ∈ oddArithmeticGroundSpace a ∧
        ∀ w : ℂ,unitaryLaplace (timeRep a u) w =
          (∏ i ∈ Finset.range k,(w^2-pairedDivisionPoint i^2))*
            unitaryLaplace (timeRep a v) w
  | 0,_ => ⟨u,hu,by simp⟩
  | k+1,hz => by
    obtain ⟨v,hv,hvw⟩ := exists_paired_div_prod a hu k (fun i hi => hz i (by omega))
    have hvz : unitaryLaplace (timeRep a v) (pairedDivisionPoint k) = 0 := by
      have h := hvw (pairedDivisionPoint k)
      rw [hz k (by omega)] at h
      apply (mul_eq_zero.mp h.symm).resolve_left
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply sub_ne_zero.mpr
      intro he
      have := pairedDivisionPoint_sq_injective he
      rw [Finset.mem_range] at hi
      omega
    obtain ⟨v',hv',hvw'⟩ := exists_oddArithmeticGround_div a hv hvz
      (pairedDivisionPoint_admissible k)
    refine ⟨v',hv',fun w => ?_⟩
    rw [hvw,hvw',Finset.prod_range_succ]
    ring

/-- A nonzero compact transform cannot annihilate a nonzero polynomial in squared frequency. -/
theorem polynomial_sq_mul_transform_injective (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : ccmArchimedeanFormToAperture a G ≠ 0)
    {P Q : ℂ[X]} (h : ∀ t : ℝ,P.eval ((t : ℂ)^2)*unitaryLaplace (timeRep a G) t =
      Q.eval ((t : ℂ)^2)*unitaryLaplace (timeRep a G) t) : P = Q := by
  have hz : ((P-Q).comp (X^2)) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine ((infinite_real_ne_zero a hG).image Complex.ofReal_injective.injOn).mono ?_
    rintro _ ⟨t,ht,rfl⟩
    simp only [Polynomial.IsRoot.def,Polynomial.eval_comp,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_sub]
    exact sub_eq_zero.mpr (mul_right_cancel₀ ht (h t))
  rcases Polynomial.comp_eq_zero_iff.mp hz with he | ⟨_,hc⟩
  · exact sub_eq_zero.mp he
  · have hd := congrArg Polynomial.natDegree hc
    simp at hd

private theorem cancel_polynomial_continuous {P : ℂ[X]} (hP : P ≠ 0)
    {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ w,P.eval w*f w = P.eval w*g w) : f = g := by
  have hd := dense_univ.sdiff_finite (Polynomial.finite_setOf_isRoot hP)
  apply Continuous.ext_on hd hf hg
  intro w hw
  exact mul_left_cancel₀ hw.2 (h w)

private def groundPolynomialSequence (d : ℕ) : Polynomial.Sequence ℂ where
  elems' k := if k<d then
    ∏ i ∈ Finset.Ico (d-1-k) (d-1),(X-C (pairedDivisionPoint i^2)) else X^k
  degree_eq' k := by
    by_cases hk : k<d
    · rw [if_pos hk]
      have hm : (∏ i ∈ Finset.Ico (d-1-k) (d-1),
          (X-C (pairedDivisionPoint i^2))).Monic :=
        Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
      rw [Polynomial.degree_eq_natDegree hm.ne_zero,
        Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero _]
      simp only [Polynomial.natDegree_X_sub_C,Finset.sum_const,Nat.card_Ico,smul_eq_mul,mul_one]
      congr 1
      omega
    · rw [if_neg hk]
      simp

private theorem groundPolynomialSequence_monic (d k : ℕ) :
    (groundPolynomialSequence d k).Monic := by
  change (if k<d then ∏ i ∈ Finset.Ico (d-1-k) (d-1),
    (X-C (pairedDivisionPoint i^2)) else X^k).Monic
  split_ifs
  · exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  · exact Polynomial.monic_X_pow k

/-- Exact polynomial structure of the entire corrected odd ground space. Both directions
are realized by actual form-domain vectors; the generator has no off-axis zeros. -/
theorem exists_oddArithmeticGround_generator (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a,G ∈ oddArithmeticGroundSpace a ∧
      ccmArchimedeanFormToAperture a G ≠ 0 ∧
      (∀ z : ℂ,unitaryLaplace (timeRep a G) z = 0 → z.re = 0 ∨ z.im = 0) ∧
      (∀ u : CCMArchimedeanFormDomain a,u ∈ oddArithmeticGroundSpace a →
        ∃! P : Polynomial.degreeLT ℂ (Module.finrank ℂ (oddArithmeticGroundSpace a)),
          ∀ w : ℂ,unitaryLaplace (timeRep a u) w =
            (P : ℂ[X]).eval (w^2)*unitaryLaplace (timeRep a G) w) ∧
      ∀ P : Polynomial.degreeLT ℂ (Module.finrank ℂ (oddArithmeticGroundSpace a)),
        ∃ u : CCMArchimedeanFormDomain a,u ∈ oddArithmeticGroundSpace a ∧
          ∀ w : ℂ,unitaryLaplace (timeRep a u) w =
            (P : ℂ[X]).eval (w^2)*unitaryLaplace (timeRep a G) w := by
  classical
  haveI := oddArithmeticGroundSpace_finiteDimensional a
  haveI := oddArithmeticGroundSpace_nontrivial a
  let S := oddArithmeticGroundSpace a
  let d := Module.finrank ℂ S
  have hd1 : 1 ≤ d := Module.finrank_pos
  let ψ : S →ₗ[ℂ] (Fin (d-1) → ℂ) :=
    LinearMap.pi fun i => (evalAt a (pairedDivisionPoint i)).comp S.subtype
  have hker : LinearMap.ker ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_fin_fun]
    change d-1<d
    omega)
  obtain ⟨u,huker,hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzu : ∀ i<d-1,unitaryLaplace (timeRep a u.1) (pairedDivisionPoint i) = 0 := by
    intro i hi
    have h := congrFun (LinearMap.mem_ker.mp huker) ⟨i,hi⟩
    simpa [ψ,evalAt_apply] using h
  have hJu : ccmArchimedeanFormToAperture a u.1 ≠ 0 := by
    intro h
    apply hune
    exact Subtype.ext (ccmArchimedeanFormToAperture_injective a
      (by rw [h,Submodule.coe_zero,map_zero]))
  have hchain : ∀ k : ℕ,∃ v : CCMArchimedeanFormDomain a,k ≤ d-1 →
      v ∈ S ∧ ∀ w : ℂ,unitaryLaplace (timeRep a u.1) w =
        (∏ i ∈ Finset.range k,(w^2-pairedDivisionPoint i^2))*unitaryLaplace (timeRep a v) w := by
    intro k
    by_cases hk : k ≤ d-1
    · obtain ⟨v,hv,hvw⟩ := exists_paired_div_prod a u.2 k (fun i hi => hzu i (by omega))
      exact ⟨v,fun _ => ⟨hv,hvw⟩⟩
    · exact ⟨0,fun h => absurd h hk⟩
  choose v hv using hchain
  obtain ⟨hG,hGw⟩ := hv (d-1) le_rfl
  let G := v (d-1)
  have hJG : ccmArchimedeanFormToAperture a G ≠ 0 := by
    intro hJ
    have hG0 : G = 0 := ccmArchimedeanFormToAperture_injective a (by rw [hJ,map_zero])
    obtain ⟨t,ht⟩ := exists_real_ne_zero a hJu
    apply ht
    rw [hGw t,show v (d-1) = G from rfl,hG0,unitaryLaplace_timeRep_zero,mul_zero]
  have hcont (x : CCMArchimedeanFormDomain a) : Continuous (unitaryLaplace (timeRep a x)) :=
    (CCMXiStrip.differentiable_unitaryLaplace a.2.le
      (integrable_timeRep a x) (supportedIn_timeRep a x)).continuous
  have hrel : ∀ k ≤ d-1,∀ w : ℂ,unitaryLaplace (timeRep a (v k)) w =
      (∏ i ∈ Finset.Ico k (d-1),(w^2-pairedDivisionPoint i^2))*
        unitaryLaplace (timeRep a G) w := by
    intro k hk
    have heq := cancel_polynomial_continuous
      (P := ∏ i ∈ Finset.range k,(X^2-C (pairedDivisionPoint i^2)))
      (Finset.prod_ne_zero_iff.mpr fun i _ =>
        (Polynomial.monic_X_pow_sub_C (pairedDivisionPoint i^2) two_ne_zero).ne_zero)
      (hcont (v k)) ((by fun_prop : Continuous fun w : ℂ =>
        ∏ i ∈ Finset.Ico k (d-1),(w^2-pairedDivisionPoint i^2)).mul (hcont G)) ?_
    · exact congrFun heq
    · intro w
      simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_pow,
        Polynomial.eval_X,Polynomial.eval_C]
      have h1 := (hv k hk).2 w
      have h2 := hGw w
      rw [← Finset.prod_range_mul_prod_Ico _ hk,mul_assoc] at h2
      exact h1.symm.trans h2
  let b : Fin d → S := fun k => ⟨v (d-1-k),(hv _ (by omega)).1⟩
  let seq := groundPolynomialSequence d
  have hb (k : Fin d) (w : ℂ) : unitaryLaplace (timeRep a (b k).1) w =
      (seq k).eval (w^2)*unitaryLaplace (timeRep a G) w := by
    rw [show (b k).1 = v (d-1-k) from rfl,hrel _ (by omega)]
    change _ = (if (k : ℕ)<d then
      ∏ i ∈ Finset.Ico (d-1-k) (d-1),(X-C (pairedDivisionPoint i^2))
      else X^(k : ℕ)).eval _ * _
    rw [if_pos k.isLt,Polynomial.eval_prod]
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  have hliP : LinearIndependent ℂ (fun k : Fin d => seq k) :=
    seq.linearIndependent.comp (fun k : Fin d => (k : ℕ)) Fin.val_injective
  have hli : LinearIndependent ℂ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hP : (∑ k : Fin d,c k • seq k) = 0 := by
      apply polynomial_sq_mul_transform_injective a hJG
      intro t
      have h0 := congrArg (fun x : S => evalAt a t x.1) hc
      simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,
        Submodule.coe_zero,map_zero,evalAt_apply,hb] at h0
      simpa only [Polynomial.eval_finsetSum,Polynomial.eval_smul,smul_eq_mul,
        Finset.sum_mul,mul_assoc,Polynomial.eval_zero,zero_mul] using h0
    exact (Fintype.linearIndependent_iff.mp hliP) c hP i
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin])
  have hseqmem (k : Fin d) : seq k ∈ Polynomial.degreeLT ℂ d := by
    rw [Polynomial.mem_degreeLT,seq.degree_eq]
    exact_mod_cast k.isLt
  have hstruct : ∀ u' : CCMArchimedeanFormDomain a,u' ∈ S →
      ∃ P : Polynomial.degreeLT ℂ d,∀ w : ℂ,unitaryLaplace (timeRep a u') w =
        (P : ℂ[X]).eval (w^2)*unitaryLaplace (timeRep a G) w := by
    intro u' hu'
    have hmem : (⟨u',hu'⟩ : S) ∈ Submodule.span ℂ (Set.range b) := by rw [hspan]; trivial
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    refine ⟨⟨∑ k : Fin d,c k • seq k,(Polynomial.degreeLT ℂ d).sum_mem
      fun k _ => (Polynomial.degreeLT ℂ d).smul_mem _ (hseqmem k)⟩,fun w => ?_⟩
    have h0 := congrArg (fun x : S => evalAt a w x.1) hc
    simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,
      evalAt_apply,hb] at h0
    simpa only [Polynomial.eval_finsetSum,Polynomial.eval_smul,smul_eq_mul,
      Finset.sum_mul,mul_assoc] using h0.symm
  have hsurj : ∀ P : Polynomial.degreeLT ℂ d,
      ∃ u' : CCMArchimedeanFormDomain a,u' ∈ S ∧ ∀ w : ℂ,
        unitaryLaplace (timeRep a u') w =
          (P : ℂ[X]).eval (w^2)*unitaryLaplace (timeRep a G) w := by
    intro P
    have hrange : Set.range (fun k : Fin d => seq k) = seq '' Set.Iio d := by
      ext p
      constructor
      · rintro ⟨k,rfl⟩
        exact ⟨k,k.isLt,rfl⟩
      · rintro ⟨k,hk,rfl⟩
        exact ⟨⟨k,hk⟩,rfl⟩
    have hsp : Submodule.span ℂ (Set.range (fun k : Fin d => seq k)) =
        Polynomial.degreeLT ℂ d := by
      rw [hrange]
      apply seq.span_degreeLT
      intro i _
      rw [(groundPolynomialSequence_monic d i).leadingCoeff]
      exact isUnit_one
    have hmem : (P : ℂ[X]) ∈ Submodule.span ℂ (Set.range (fun k : Fin d => seq k)) := by
      rw [hsp]
      exact P.2
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    let u' : S := ∑ k : Fin d,c k • b k
    refine ⟨u'.1,u'.2,fun w => ?_⟩
    change evalAt a w (∑ k : Fin d,c k • b k : S).1 = _
    simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,
      evalAt_apply,hb]
    rw [← hc,Polynomial.eval_finsetSum,Finset.sum_mul]
    simp only [Polynomial.eval_smul,smul_eq_mul,mul_assoc]
  have hcross : ∀ z : ℂ,unitaryLaplace (timeRep a G) z = 0 → z.re = 0 ∨ z.im = 0 := by
    intro z hz
    by_contra hn
    push Not at hn
    obtain ⟨G',hG',hG'w⟩ := exists_oddArithmeticGround_div a hG hz
      ((CCMEvenSector.im_sq_ne_zero_iff z).mpr hn)
    obtain ⟨P,hP⟩ := hstruct G' hG'
    have hone : (X-C (z^2))*(P : ℂ[X]) = 1 := by
      apply polynomial_sq_mul_transform_injective a hJG
      intro t
      have h := hG'w t
      rw [hP t] at h
      simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,
        Polynomial.eval_C,Polynomial.eval_one,one_mul]
      linear_combination -h
    have he := congrArg (Polynomial.eval (z^2)) hone
    simp at he
  refine ⟨G,hG,hJG,hcross,?_,hsurj⟩
  intro u' hu'
  obtain ⟨P,hP⟩ := hstruct u' hu'
  refine ⟨P,hP,fun Q hQ => ?_⟩
  apply Subtype.ext
  exact polynomial_sq_mul_transform_injective a hJG fun t => (hQ t).symm.trans (hP t)

/-- A generator is an actual nonzero odd ground vector whose transform divides
every ground transform by a polynomial in squared frequency. -/
def IsOddArithmeticGroundGenerator (a : SuzukiPositiveAperture)
    (G : CCMArchimedeanFormDomain a) : Prop :=
  G ∈ oddArithmeticGroundSpace a ∧ ccmArchimedeanFormToAperture a G ≠ 0 ∧
    ∀ u : CCMArchimedeanFormDomain a,u ∈ oddArithmeticGroundSpace a →
      ∃ P : ℂ[X],∀ w : ℂ,unitaryLaplace (timeRep a u) w =
        P.eval (w^2)*unitaryLaplace (timeRep a G) w

/-- The generating line is canonical: any two actual ground generators differ
by one uniquely determined nonzero scalar. No simplicity assumption is imposed. -/
theorem exists_canonical_oddArithmeticGround_generator (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a,IsOddArithmeticGroundGenerator a G ∧
      (∀ z : ℂ,unitaryLaplace (timeRep a G) z = 0 → z.re = 0 ∨ z.im = 0) ∧
      ∀ H : CCMArchimedeanFormDomain a,IsOddArithmeticGroundGenerator a H →
        ∃! c : ℂ,c ≠ 0 ∧ H = c • G := by
  obtain ⟨G,hG,hJG,hcross,hcoord,_⟩ := exists_oddArithmeticGround_generator a
  refine ⟨G,⟨hG,hJG,?_⟩,hcross,?_⟩
  · intro u hu
    obtain ⟨P,hP,_⟩ := hcoord u hu
    exact ⟨(P : ℂ[X]),hP⟩
  · intro H hH
    obtain ⟨Q,hQ,_⟩ := hcoord H hH.1
    obtain ⟨P,hP⟩ := hH.2.2 G hG
    have hPQ : P*(Q : ℂ[X]) = 1 := by
      apply polynomial_sq_mul_transform_injective a hJG
      intro t
      have h := hP t
      rw [hQ t] at h
      simp only [Polynomial.eval_mul,Polynomial.eval_one,one_mul]
      linear_combination -h
    have hP0 : P ≠ 0 := by
      intro hz
      simp [hz] at hPQ
    have hQ0 : (Q : ℂ[X]) ≠ 0 := by
      intro hz
      simp [hz] at hPQ
    have hdQ : (Q : ℂ[X]).natDegree = 0 := by
      have hd := congrArg Polynomial.natDegree hPQ
      rw [Polynomial.natDegree_mul hP0 hQ0,Polynomial.natDegree_one] at hd
      omega
    let c := (Q : ℂ[X]).coeff 0
    have hQc : (Q : ℂ[X]) = C c := Polynomial.eq_C_of_natDegree_eq_zero hdQ
    have hc : c ≠ 0 := by
      intro hz
      apply hQ0
      rw [hQc,hz,map_zero]
    have hHc : H = c • G := by
      apply eq_of_transform_eq a
      intro t
      rw [hQ t,hQc,Polynomial.eval_C,unitaryLaplace_timeRep_smul]
    refine ⟨c,⟨hc,hHc⟩,fun c' hc' => ?_⟩
    obtain ⟨t,ht⟩ := exists_real_ne_zero a hJG
    have he := congrArg (fun v : CCMArchimedeanFormDomain a =>
      unitaryLaplace (timeRep a v) t) (hc'.2.symm.trans hHc)
    simp only [unitaryLaplace_timeRep_smul] at he
    exact mul_right_cancel₀ ht he

/-- Every attained blind optimizer has one uniquely determined polynomial factor
over the same nonzero odd ground transform with no zeros off the two axes. -/
theorem exists_blind_optimizer_common_factor (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a,G ∈ oddArithmeticGroundSpace a ∧
      ccmArchimedeanFormToAperture a G ≠ 0 ∧
      (∀ z : ℂ,unitaryLaplace (timeRep a G) z = 0 → z.re = 0 ∨ z.im = 0) ∧
      (∃ u : BlindUnitSource a,ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a) ∧
      ∀ u : BlindUnitSource a,ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a →
        ∃! P : Polynomial.degreeLT ℂ (Module.finrank ℂ (oddArithmeticGroundSpace a)),
          ∀ w : ℂ,unitaryLaplace (timeRep a u.1) w =
            (P : ℂ[X]).eval (w^2)*unitaryLaplace (timeRep a G) w := by
  obtain ⟨G,hG,hJG,hcross,hcoord,_⟩ := exists_oddArithmeticGround_generator a
  refine ⟨G,hG,hJG,hcross,⟨blindMinimizer a,rfl⟩,fun u hu => ?_⟩
  exact hcoord u.1 ⟨(blind_minimum_iff_mem_arithmeticGroundSpace a u).mp hu,u.2.1⟩

end RHTower.OddSector
