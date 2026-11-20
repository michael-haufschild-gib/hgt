import GaloisForLFunctions.RepresentationLifting.Probability.PrimePowerRootCountsOfTheShear
import GaloisForLFunctions.RepresentationLifting.Probability.SplitQuadraticsAtEveryPadicPrecision
import GaloisForLFunctions.RHTower.FieldOnePadicUnitBallNormalizedHaar
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Split probability of a random monic p-adic quadratic

Marking a root replaces the two random coefficients by one random
separation. On valuation shell j below half precision its reciprocal root
count is 1/(2p^j). The merged ball supplies the remaining p^(-h).
This gives the exact finite probabilities and Lapid and Shusterman's
integral split density without a residue-characteristic exception.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset MeasureTheory Filter RHTower
open scoped Topology Classical
noncomputable section
variable (p : ℕ) [Fact p.Prime]

private instance residueNonzero (h : ℕ) : NeZero (p^h) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
private instance integralProbability : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

private def residueBall (h j : ℕ) : Finset (ZMod (p^h)) :=
  univ.filter fun z => PadicInt.toZModPow j (fieldOnePadicIntResidueRep p h z)=0

private theorem residueBall_mem {h j : ℕ} (z : ZMod (p^h)) :
    z∈residueBall p h j ↔ PadicInt.toZModPow j (fieldOnePadicIntResidueRep p h z)=0 := by
  simp only [residueBall,mem_filter,mem_univ,true_and]

private theorem residueBall_antitone (h : ℕ) : Antitone (residueBall p h) := by
  intro a b hab z hz
  rw [residueBall_mem] at hz ⊢
  simpa only [map_zero] using padic_congruence_mono p (x:=fieldOnePadicIntResidueRep p h z) (y:=0) hab
    (by simpa only [map_zero] using hz)

private theorem residueBall_fraction {j h : ℕ} (hj : j≤h) :
    ((residueBall p h j).card:ℝ)/(p:ℝ)^h=1/(p:ℝ)^j := by
  let f := PadicInt.toZModPow (p:=p) h
  let μ := fieldOnePadicIntNormalizedHaar p
  have ident : {x : ℤ_[p] | f x∈residueBall p h j} = Metric.closedBall 0 ((p:ℝ)^(-(j:ℤ))) := by
    rw [padic_root_ball_eq_residue]
    ext x
    have hh := padic_congruence_mono p hj (fieldOnePadicIntResidueRep_spec p h (f x))
    simp only [Set.mem_setOf_eq,residueBall_mem,map_zero,hh]
  have ht := haar_finite_quotient_probability μ f.toAddMonoidHom (ZMod.ringHom_surjective f)
    (fieldOnePadicInt_toZModPow_continuous p h) (· ∈ residueBall p h j)
  change μ.real {x | f x∈residueBall p h j}=_ at ht
  rw [ident,padic_linear_root_ball_mass,Nat.card_eq_finsetCard,Nat.card_zmod,Nat.cast_pow] at ht
  exact ht.symm

private theorem separated_count_from_shear (h : ℕ) (z : ZMod (p^h)) :
    separatedRootCount z=padicGapRootCount p h (fieldOnePadicIntResidueRep p h z) := by
  unfold padicGapRootCount
  rw [fieldOnePadicIntResidueRep_spec]
  apply Nat.card_congr
  refine { toFun := fun x => ⟨-x.val,?_⟩, invFun := fun x => ⟨-x.val,?_⟩,
           left_inv := fun x => Subtype.ext (neg_neg _), right_inv := fun x => Subtype.ext (neg_neg _) }
  · linear_combination -x.property
  · linear_combination -x.property

private theorem separated_count_on_shell {h j : ℕ} {z : ZMod (p^h)}
    (hj : j<(h+1)/2) (hz : z∈residueBall p h j \ residueBall p h (j+1)) :
    separatedRootCount z=2*p^j := by
  let a := fieldOnePadicIntResidueRep p h z
  obtain ⟨h₀,h₁⟩ := mem_sdiff.mp hz
  have low := (residueBall_mem p z).mp h₀
  have high : PadicInt.toZModPow (j+1) a≠0 := fun hh => h₁ ((residueBall_mem p z).mpr hh)
  have hn : a≠0 := fun he => high (by rw [he,map_zero])
  have far : PadicInt.toZModPow ((h+1)/2) a≠0 := fun hh =>
    h₁ ((residueBall_antitone p h hj) ((residueBall_mem p z).mpr hh))
  have hp : 1<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h₁ := (OperatorKernels.padicProjection_eq_zero_iff_norm_le p a j).mp low
  have h₂ := lt_of_not_ge (fun hh => high ((OperatorKernels.padicProjection_eq_zero_iff_norm_le p a (j+1)).mpr hh))
  rw [PadicInt.norm_eq_zpow_neg_valuation hn,zpow_le_zpow_iff_right₀ hp] at h₁
  rw [PadicInt.norm_eq_zpow_neg_valuation hn,zpow_lt_zpow_iff_right₀ hp] at h₂
  rw [separated_count_from_shear]
  change padicGapRootCount p h a=_
  rw [padicGapRootCount_eq,if_neg far,show a.valuation=j by omega]

/-- The uniform split probability at every finite precision. The last
term is the entire unresolved ball of near-coincident roots. -/
theorem finite_quadratic_split_probability (h : ℕ) :
    ((splitCoefficientLabels (ZMod (p^h))).card:ℝ)/((p:ℝ)^h)^2 =
      (1-(p:ℝ)⁻¹)/2*(∑ j ∈ range ((h+1)/2), ((p:ℝ)⁻¹^2)^j)+1/(p:ℝ)^h := by
  let J := (h+1)/2
  let B := residueBall p h
  let W (z : ZMod (p^h)) := (separatedRootCount z:ℝ)⁻¹
  let F (j : ℕ) := (∑ z ∈ B j, W z)/(p:ℝ)^h
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hJ : J≤h := by dsimp only [J]; omega
  have B₀ : B 0=univ := by
    haveI : Subsingleton (ZMod (p^0)) := by rw [pow_zero]; infer_instance
    ext z
    rw [residueBall_mem]
    simp only [mem_univ,iff_true]
    apply Subsingleton.elim
  have hF₀ : F 0=((splitCoefficientLabels (ZMod (p^h))).card:ℝ)/((p:ℝ)^h)^2 := by
    simpa only [F,B₀,W,ZMod.card,Nat.cast_pow] using
      (split_probability_as_mean_inverse_roots (R:=ZMod (p^h))).symm
  have terminal (z : ZMod (p^h)) (hz : z∈B J) : W z = ((p:ℝ)^(h/2))⁻¹ := by
    change (separatedRootCount z:ℝ)⁻¹=_
    rw [separated_count_from_shear,padicGapRootCount_eq,if_pos ((residueBall_mem p z).mp hz),Nat.cast_pow]
  have hfinal : F J=1/(p:ℝ)^h := by
    have hc := residueBall_fraction p hJ
    have hexp : (p:ℝ)^h=(p:ℝ)^J*(p:ℝ)^(h/2) := by
      rw [←pow_add,show J+h/2=h by dsimp only [J]; omega]
    calc
      F J = ((B J).card/(p:ℝ)^h)*((p:ℝ)^(h/2))⁻¹ := by
        dsimp only [F]
        rw [sum_congr rfl terminal,sum_const,nsmul_eq_mul]
        ring
      _ = _ := by rw [hc,hexp]; field_simp [hp]
  have step (j : ℕ) (hj : j<J) : F j-F (j+1)=
      (1-(p:ℝ)⁻¹)/2*(((p:ℝ)⁻¹)^2)^j := by
    have sub : B (j+1)⊆B j := residueBall_antitone p h (Nat.le_succ j)
    have hi (z : ZMod (p^h)) (hz : z∈B j \ B (j+1)) : W z=(2*(p:ℝ)^j)⁻¹ := by
      change (separatedRootCount z:ℝ)⁻¹=_
      rw [separated_count_on_shell p hj hz,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    have hd := sum_sdiff (f:=W) sub
    have hsplit : F j-F (j+1) = (∑ z ∈ B j \ B (j+1), W z)/(p:ℝ)^h := by
      dsimp only [F]
      rw [←sub_div]
      exact congrArg (·/(p:ℝ)^h) (by linarith only [hd])
    rw [hsplit,sum_congr rfl hi,sum_const,nsmul_eq_mul,card_sdiff_of_subset sub,
      Nat.cast_sub (card_le_card sub)]
    have h₁ := residueBall_fraction p (hj.le.trans hJ)
    have h₂ := residueBall_fraction p (hj.trans_le hJ : j+1≤h)
    change ((B j).card:ℝ)/(p:ℝ)^h=_ at h₁
    change ((B (j+1)).card:ℝ)/(p:ℝ)^h=_ at h₂
    have powers : (((p:ℝ)⁻¹)^2)^j = ((p:ℝ)^j)⁻¹*((p:ℝ)^j)⁻¹ := by rw [sq,mul_pow,inv_pow]
    rw [show (((B j).card:ℝ)-(B (j+1)).card)*(2*(p:ℝ)^j)⁻¹/(p:ℝ)^h =
      (((B j).card/(p:ℝ)^h)-(B (j+1)).card/(p:ℝ)^h)*(2*(p:ℝ)^j)⁻¹ by ring,h₁,h₂,
      pow_succ,powers]
    field_simp [hp]
  have telesc := sum_congr rfl (fun j hj => step j (mem_range.mp hj))
  rw [sum_range_sub',←mul_sum,hF₀,hfinal] at telesc
  linarith only [telesc]

/-- Lapid and Shusterman's split coefficient density on the whole
integral box, valid at p=2 as well. -/
theorem padic_quadratic_split_probability :
    let μ := fieldOnePadicIntNormalizedHaar p
    (μ.prod μ).real {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(z.1-x)=z.2} =
      (p:ℝ)/(2*((p:ℝ)+1)) := by
  let u := (p:ℝ)⁻¹
  have hp : 1<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp₀ := zero_lt_one.trans hp
  have hu₀ : 0<u := inv_pos.mpr hp₀
  have hu₁ : u<1 := (inv_lt_one₀ hp₀).mpr hp
  have hsq : u^2<1 := by nlinarith only [mul_pos (sub_pos.mpr hu₁) (add_pos hu₀ zero_lt_one)]
  have hJ : Tendsto (fun h : ℕ => (h+1)/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (2*j)] with h hh
    omega
  have hsum := (hasSum_geometric_of_lt_one (sq_nonneg u) hsq).tendsto_sum_nat.comp hJ
  have hz : Tendsto (fun h : ℕ => 1/(p:ℝ)^h) atTop (𝓝 0) := by
    simpa only [u,one_div,inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one hu₀.le hu₁
  have hh := (hsum.const_mul ((1-u)/2)).add hz
  have value : (1-u)/2*(1-u^2)⁻¹+0=(p:ℝ)/(2*((p:ℝ)+1)) := by
    rw [add_zero,←div_eq_mul_inv]
    have hc : 1-u^2≠0 := (sub_pos.mpr hsq).ne'
    have ha : (p:ℝ)+1≠0 := (add_pos hp₀ zero_lt_one).ne'
    rw [div_eq_div_iff hc (mul_ne_zero (by norm_num) ha)]
    dsimp only [u]
    field_simp [hp₀.ne']
    ring
  rw [value] at hh
  apply tendsto_nhds_unique (tendsto_split_coefficient_probability p)
  apply hh.congr
  intro h
  dsimp only [Function.comp_apply]
  rw [quadraticSplitTube_mass,show (p:ℝ)^(2*h)=((p:ℝ)^h)^2 by rw [←pow_mul,Nat.mul_comm]]
  exact (finite_quadratic_split_probability p h).symm

/-- A root of a monic integral quadratic over the fraction field is integral. -/
theorem quadratic_root_integral (t d : ℤ_[p]) :
    (∃ x : ℚ_[p], x*((t:ℚ_[p])-x)=(d:ℚ_[p])) ↔ ∃ x : ℤ_[p], x*(t-x)=d := by
  constructor
  · rintro ⟨x,hx⟩
    have small : ‖x‖≤1 := by
      by_contra! hbig
      have hdist : dist (t:ℚ_[p]) 0<dist 0 x := by
        rw [dist_zero_right,dist_zero_left]
        exact t.property.trans_lt hbig
      have hd := IsUltrametricDist.dist_eq_max_of_dist_ne_dist (t:ℚ_[p]) 0 x hdist.ne
      rw [max_eq_right hdist.le,dist_zero_left,dist_eq_norm] at hd
      have hc := congrArg norm hx
      rw [norm_mul,hd] at hc
      exact (not_lt_of_ge d.property) (calc
        1 < ‖x‖ := hbig
        _ ≤ ‖x‖*‖x‖ := le_mul_of_one_le_right (norm_nonneg x) hbig.le
        _ = ‖(d:ℚ_[p])‖ := hc)
    exact ⟨⟨x,small⟩,Subtype.ext hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,congrArg (fun z : ℤ_[p] => (z:ℚ_[p])) hx⟩

open Polynomial Matrix in
/-- Irreducibility of a monic quadratic is equivalent to absence of a factor pair. -/
theorem irreducible_quadratic_iff {K : Type*} [Field K] (b c : K) :
    Irreducible (X^2+C b*X+C c) ↔ ¬∃ x : K, x*(b-x)=c := by
  let A : Matrix (Fin 2) (Fin 2) K := !![-b,-c;1,0]
  have ht : A.trace= -b := by simp [A,trace_fin_two_of]
  have hd : A.det=c := by simp [A,det_fin_two_of]
  have hc : A.charpoly=X^2+C b*X+C c := by rw [charpoly_fin_two,ht,hd,map_neg,neg_mul,sub_neg_eq_add]
  have hdeg : A.charpoly.natDegree=2 := by simp [charpoly_natDegree_eq_dim]
  rw [←hc,A.charpoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  constructor
  · rintro h ⟨x,hx⟩
    apply h (-x)
    rw [mem_roots A.charpoly_monic.ne_zero,Polynomial.IsRoot,hc]
    simp only [eval_add,eval_mul,eval_pow,eval_X,eval_C]
    linear_combination -hx
  · intro h x hx
    rw [mem_roots A.charpoly_monic.ne_zero,Polynomial.IsRoot,hc] at hx
    simp only [eval_add,eval_mul,eval_pow,eval_X,eval_C] at hx
    exact h ⟨-x,by linear_combination -hx⟩

/-- The actual irreducibility probability over Q_p for coefficients in
Z_p. A monic quadratic root over the field already belongs to the integral ring. -/
theorem padic_monic_quadratic_irreducible_probability :
    let μ := fieldOnePadicIntNormalizedHaar p
    (μ.prod μ).real {z : ℤ_[p]×ℤ_[p] | Irreducible
      (Polynomial.X^2+Polynomial.C (z.1:ℚ_[p])*Polynomial.X+Polynomial.C (z.2:ℚ_[p]))} =
        ((p:ℝ)+2)/(2*((p:ℝ)+1)) := by
  let μ := fieldOnePadicIntNormalizedHaar p
  let S := {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(z.1-x)=z.2}
  have seteq : {z : ℤ_[p]×ℤ_[p] | Irreducible
      (Polynomial.X^2+Polynomial.C (z.1:ℚ_[p])*Polynomial.X+Polynomial.C (z.2:ℚ_[p]))} = Sᶜ := by
    ext z
    exact (irreducible_quadratic_iff _ _).trans (not_congr (quadratic_root_integral p z.1 z.2))
  rw [seteq]
  change (μ.prod μ).real Sᶜ=_
  rw [measureReal_compl (show MeasurableSet S from measurableSet_padic_quadratic_split p),probReal_univ]
  change 1-(μ.prod μ).real {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(z.1-x)=z.2}=_
  rw [padic_quadratic_split_probability]
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  field_simp [show (p:ℝ)+1≠0 from (add_pos hp zero_lt_one).ne']
  ring

open scoped ENNReal NNReal Pointwise in
/-- Multiplication by p pays one residue-class factor on every subset
of the integral ring, with the same normalization as finite quadrature. -/
theorem padic_integral_haar_prime_image (S : Set ℤ_[p]) :
    fieldOnePadicIntNormalizedHaar p ((fun x : ℤ_[p] => (p:ℤ_[p])*x) '' S) =
      (p:ℝ≥0∞)⁻¹*fieldOnePadicIntNormalizedHaar p S := by
  let f := fieldOnePadicIntCoeAddMonoidHom p
  let ν := fieldOnePadicUnitBallNormalizedHaar p
  have comap (T : Set ℤ_[p]) : fieldOnePadicIntNormalizedHaar p T=ν (f '' T) := by
    rw [←fieldOnePadicUnitBallNormalizedHaarIntComap_eq_normalized]
    exact PadicInt.isOpenEmbedding_coe.measurableEmbedding.comap_apply ν T
  rw [comap,comap]
  have he : f '' ((fun x : ℤ_[p] => (p:ℤ_[p])*x) '' S) = fieldOnePadicPrimeUnit p • (f '' S) := by
    ext x
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨f z,⟨z,hz,rfl⟩,by rfl⟩
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨_,⟨z,hz,rfl⟩,by rfl⟩
  rw [he,←distribHaarChar_mul ν,fieldOnePadicPrimeUnit_distribHaarChar,
    ENNReal.coe_inv (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),ENNReal.coe_natCast]

private theorem ramified_root_slice (b : ℤ_[p]) :
    {c : ℤ_[p] | ∃ x : ℤ_[p], x*((p:ℤ_[p])*b-x)=p*c} =
      (fun v : ℤ_[p] => (p:ℤ_[p])*v) '' {v | ∃ u : ℤ_[p], u*(b-u)=v} := by
  ext c
  constructor
  · rintro ⟨x,hx⟩
    have hres := congrArg (PadicInt.toZMod (p:=p)) hx
    simp only [map_mul,map_sub,map_natCast,ZMod.natCast_self,zero_mul,zero_sub,mul_neg,neg_eq_zero,
      mul_self_eq_zero] at hres
    have hd : (p:ℤ_[p])∣x := by
      rw [←Ideal.mem_span_singleton,←PadicInt.maximalIdeal_eq_span_p,←PadicInt.ker_toZMod,RingHom.mem_ker]
      exact hres
    obtain ⟨u,rfl⟩ := hd
    refine ⟨u*(b-u),⟨u,rfl⟩,?_⟩
    apply (mul_right_inj' (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p:ℤ_[p])≠0)).mp
    linear_combination hx
  · rintro ⟨_,⟨u,rfl⟩,rfl⟩
    exact ⟨(p:ℤ_[p])*u,by ring⟩

/-- Conditional split probability when both coefficients are uniform
in the maximal ideal. A root must be divisible by p. After division,
the constant coefficient pays one extra digit and the original polynomial
distribution returns. -/
theorem padic_ramified_quadratic_split_probability :
    let μ := fieldOnePadicIntNormalizedHaar p
    (μ.prod μ).real {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(p*z.1-x)=p*z.2} =
      1/(2*((p:ℝ)+1)) := by
  let μ := fieldOnePadicIntNormalizedHaar p
  let S := {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(z.1-x)=z.2}
  let T := {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(p*z.1-x)=p*z.2}
  have hs : MeasurableSet S := measurableSet_padic_quadratic_split p
  have ht : MeasurableSet T := hs.preimage
    (((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd) :
      Continuous (fun z : ℤ_[p]×ℤ_[p] => ((p:ℤ_[p])*z.1,(p:ℤ_[p])*z.2))).measurable)
  have sectionMass (b : ℤ_[p]) : μ (Prod.mk b ⁻¹' T)=(p:ENNReal)⁻¹*μ (Prod.mk b ⁻¹' S) := by
    change μ {c : ℤ_[p] | ∃ x : ℤ_[p], x*((p:ℤ_[p])*b-x)=p*c}=_
    rw [ramified_root_slice,padic_integral_haar_prime_image]
    rfl
  have hμ : (μ.prod μ) T=(p:ENNReal)⁻¹*(μ.prod μ) S := by
    rw [Measure.prod_apply ht,Measure.prod_apply hs]
    simp_rw [sectionMass]
    exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  have hh := congrArg ENNReal.toReal hμ
  change (μ.prod μ).real T=_
  rw [show (μ.prod μ).real T=(p:ℝ)⁻¹*(μ.prod μ).real S by
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast] using hh]
  rw [show (μ.prod μ).real S=(p:ℝ)/(2*((p:ℝ)+1)) from padic_quadratic_split_probability p]
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  ring_nf
  field_simp [hp]

/-- Lapid and Shusterman's second integral density, for independent
uniform coefficients in pZ_p. -/
theorem padic_ramified_quadratic_irreducible_probability :
    let μ := fieldOnePadicIntNormalizedHaar p
    (μ.prod μ).real {z : ℤ_[p]×ℤ_[p] | Irreducible
      (Polynomial.X^2+Polynomial.C (((p:ℤ_[p])*z.1:ℤ_[p]):ℚ_[p])*Polynomial.X+
        Polynomial.C (((p:ℤ_[p])*z.2:ℤ_[p]):ℚ_[p]))} =
          (2*(p:ℝ)+1)/(2*((p:ℝ)+1)) := by
  let μ := fieldOnePadicIntNormalizedHaar p
  let T := {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(p*z.1-x)=p*z.2}
  have ht : MeasurableSet T := (measurableSet_padic_quadratic_split p).preimage
    (((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd) :
      Continuous (fun z : ℤ_[p]×ℤ_[p] => ((p:ℤ_[p])*z.1,(p:ℤ_[p])*z.2))).measurable)
  have he : {z : ℤ_[p]×ℤ_[p] | Irreducible
      (Polynomial.X^2+Polynomial.C (((p:ℤ_[p])*z.1:ℤ_[p]):ℚ_[p])*Polynomial.X+
        Polynomial.C (((p:ℤ_[p])*z.2:ℤ_[p]):ℚ_[p]))}=Tᶜ := by
    ext z
    exact (irreducible_quadratic_iff _ _).trans (not_congr (quadratic_root_integral p _ _))
  rw [he]
  change (μ.prod μ).real Tᶜ=_
  rw [measureReal_compl ht,probReal_univ,
    show (μ.prod μ).real T=1/(2*((p:ℝ)+1)) from padic_ramified_quadratic_split_probability p]
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  field_simp [show (p:ℝ)+1≠0 from (add_pos hp zero_lt_one).ne']
  ring

#print axioms padic_integral_haar_prime_image
#print axioms padic_ramified_quadratic_split_probability
#print axioms padic_ramified_quadratic_irreducible_probability

#print axioms padic_quadratic_split_probability
#print axioms padic_monic_quadratic_irreducible_probability

#print axioms finite_quadratic_split_probability
end
end GaloisForLFunctions.RepresentationLifting
