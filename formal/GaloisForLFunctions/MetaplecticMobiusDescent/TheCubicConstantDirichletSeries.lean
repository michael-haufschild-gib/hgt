/-
Cubic constant Dirichlet series adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCubeDenominators

/-!
# The cubic constant term as an ideal zeta quotient

Cube support and ramified reindexing extend absolute convergence of the
constant Dirichlet series to `Re s > 4/3`. Summing the ramified geometric
factor gives the explicit quotient of unramified ideal zeta functions.
-/
noncomputable section
open MeasureTheory Set Filter UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

lemma constant_dirichlet_support (s : ℂ) :
    Function.support (arithmeticDirichletTerm s 0) ⊆
      {c : LevelLower | c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3} := by
  intro c hc
  change arithmeticDirichletTerm s 0 c ≠ 0 at hc
  by_cases hzero : c.1=0
  · simp [arithmeticDirichletTerm,hzero] at hc
  · refine ⟨hzero, ?_⟩
    have hA : arithmeticResidueSum 0 c.1 ≠ 0 := by
      intro hA
      apply hc
      simp only [arithmeticDirichletTerm,if_neg hzero,hA,mul_zero]
    exact (arithmeticResidueSum_ne_zero_iff_cube c.1 hzero c.2).mp hA

lemma totient_sum_good (s : ℂ) :
    (∑' I : GoodIdeal,(idealTotient I.1:ℂ)*unramifiedNormWeight s I.1)=unramifiedTotientSeries s := by
  unfold unramifiedTotientSeries
  apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryIdealGenerator I ≠ 0})
    (f := fun I : Ideal O => (idealTotient I:ℂ)*unramifiedNormWeight s I)
  intro I hI
  change (idealTotient I:ℂ)*unramifiedNormWeight s I ≠ 0 at hI
  change primaryIdealGenerator I ≠ 0
  intro hg
  apply hI
  rw [unramifiedNormWeight_of_bad _ I hg,mul_zero]

lemma norm_ramifiedRatio_lt_one (s : ℂ) (hs : 1<s.re) : ‖ramifiedRatio s‖<1 := by
  change ‖((3:ℝ):ℂ)^(3-3*s)‖<1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  norm_num
  linarith

theorem constantDirichlet_summable_norm (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    Summable (fun c : LevelLower => ‖arithmeticDirichletTerm s 0 c‖) := by
  have hs1 : 1<s.re := by linarith
  have hw : 2<(3*s-2).re := by norm_num; linarith
  have hq := norm_ramifiedRatio_lt_one s hs1
  have hqn : Summable (fun n : ℕ => ‖ramifiedRatio s^(n+1)‖) := by
    have hh := (summable_geometric_of_lt_one (norm_nonneg (ramifiedRatio s)) hq).mul_right
      ‖ramifiedRatio s‖
    simpa only [pow_succ,norm_mul,norm_pow] using hh
  have hi := (unramifiedTotientSeries_summable_norm (3*s-2) hw).subtype
    (fun I : Ideal O => primaryIdealGenerator I ≠ 0)
  have hni := hqn.mul_norm hi
  have hb : Summable (fun _ : Bool => ‖(1:ℂ)‖) := summable_of_hasFiniteSupport (Set.toFinite _)
  have hfull := hb.mul_norm hni
  have hp : Summable (fun p : Bool × ℕ × GoodIdeal =>
      ‖arithmeticDirichletTerm s 0 (cubeColumnMap p).1‖) := by
    apply hfull.congr
    rintro ⟨b,n,I⟩
    simp only [one_mul,cubeColumn_dirichletTerm]
  have hsub : Summable (fun c : CubeLower => ‖arithmeticDirichletTerm s 0 c.1‖) :=
    cubeColumnEquiv.summable_iff.mp hp
  have hind := (summable_subtype_iff_indicator
    (s := {c : LevelLower | c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3})
    (f := fun c => ‖arithmeticDirichletTerm s 0 c‖)).mp hsub
  apply hind.congr
  intro c
  by_cases hc : c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3
  · simp [Set.indicator,hc]
  · have hz : arithmeticDirichletTerm s 0 c=0 := by
      by_contra h
      exact hc (constant_dirichlet_support s h)
    simp [Set.indicator,hc,hz]

lemma ramified_geometric_sum (s : ℂ) (hs : 1<s.re) :
    (∑' n : ℕ,ramifiedRatio s^(n+1))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hn := norm_ramifiedRatio_lt_one s hs
  have hne : ramifiedRatio s ≠ 0 := by
    unfold ramifiedRatio
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (by norm_num)
  have hone : ramifiedRatio s ≠ 1 := by intro h; rw [h,norm_one] at hn; exact lt_irrefl 1 hn
  have hi : (3:ℂ)^(3*s-3)=(ramifiedRatio s)⁻¹ := by
    rw [ramifiedRatio,← Complex.cpow_neg]
    congr 1
    ring
  simp_rw [pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hn,hi]
  field_simp

theorem arithmeticDirichletSeries_zero_totient (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    arithmeticDirichletSeries s 0 =
      2*((3:ℂ)^(3*s-3)-1)⁻¹*unramifiedTotientSeries (3*s-2) := by
  have hc := (constantDirichlet_summable_norm s hs).of_norm
  have hsub : Summable (fun c : CubeLower => arithmeticDirichletTerm s 0 c.1) := hc.subtype _
  have hp := cubeColumnEquiv.summable_iff.mpr hsub
  change Summable (fun p : Bool × ℕ × GoodIdeal =>
    arithmeticDirichletTerm s 0 (cubeColumnMap p).1) at hp
  calc
    _ = ∑' c : CubeLower,arithmeticDirichletTerm s 0 c.1 :=
      (tsum_subtype_eq_of_support_subset (constant_dirichlet_support s)).symm
    _ = ∑' p : Bool × ℕ × GoodIdeal,arithmeticDirichletTerm s 0 (cubeColumnMap p).1 :=
      (cubeColumnEquiv.tsum_eq _).symm
    _ = ∑' b : Bool,∑' n : ℕ,∑' I : GoodIdeal,
        arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 := by
      rw [hp.tsum_prod]
      apply tsum_congr
      intro b
      exact (hp.prod_factor b).tsum_prod
    _ = ∑' b : Bool,∑' n : ℕ,∑' I : GoodIdeal,
        ramifiedRatio s^(n+1)*((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
      apply tsum_congr; intro b
      apply tsum_congr; intro n
      exact tsum_congr (fun I => cubeColumn_dirichletTerm s b n I)
    _ = ∑' _ : Bool,∑' n : ℕ,ramifiedRatio s^(n+1)*unramifiedTotientSeries (3*s-2) := by
      apply tsum_congr; intro b
      apply tsum_congr; intro n
      rw [tsum_mul_left,totient_sum_good]
    _ = ∑' _ : Bool,((3:ℂ)^(3*s-3)-1)⁻¹*unramifiedTotientSeries (3*s-2) := by
      apply tsum_congr; intro b
      rw [tsum_mul_right,ramified_geometric_sum s (by linarith)]
    _ = _ := by
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul]
      ring

theorem scatteringCoefficient_zero_zeta (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    scatteringCoefficient s 0 =
      (2/((9*Real.sqrt 3/2:ℝ):ℂ))*
      ((3:ℂ)^(3*s-3)-1)⁻¹ *
      (unramifiedIdealZeta (3*s-3)/unramifiedIdealZeta (3*s-2)) := by
  rw [scatteringCoefficient,arithmeticDirichletSeries_zero_totient s hs,
    unramifiedTotientSeries_quotient (3*s-2) (by
      norm_num
      linarith)]
  rw [show 3*s-2-1=3*s-3 by ring]
  ring

theorem eisensteinConstantCoefficient_zeta (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    eisensteinFourierCoefficient v hv s 0 = (v:ℂ)^s+
      (v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*
      ((2/((9*Real.sqrt 3/2:ℝ):ℂ))*((3:ℂ)^(3*s-3)-1)⁻¹*
        (unramifiedIdealZeta (3*s-3)/unramifiedIdealZeta (3*s-2))) := by
  rw [eisensteinConstantCoefficient_formula v hv s hs,scatteringCoefficient_zero_zeta s (by linarith)]


#print axioms constantDirichlet_summable_norm
#print axioms scatteringCoefficient_zero_zeta
#print axioms eisensteinConstantCoefficient_zeta
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
