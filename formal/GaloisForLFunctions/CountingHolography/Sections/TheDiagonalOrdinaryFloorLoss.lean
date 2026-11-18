import GaloisForLFunctions.CountingHolography.Sections.TheCoefficientIndependentPrimeMeshError
import GaloisForLFunctions.CountingHolography.Sections.PrimeMassOutsideThinFloorFibers
import GaloisForLFunctions.CountingHolography.Sections.TheOuterBandOfSquareContacts

/-!
# Ordinary floor loss at diagonal multiplicity

An interval where the outer profile has strictly negative derivative gives
an inverse bound on the width of each near-integer fiber. The original
mesh changes its reading by O(1/n). Brun–Titchmarsh then prevents these
fibers from carrying the whole prime mass at multiplicity n.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset AbsoluteGeometryOfSpecZ ArithmeticFunction
open ArithmeticWeightTheory ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open BiScaleUncertainty.ChebyshevGauge _root_.RHTower.WeilDeletion

private theorem outer_slope : ∃ u v λ : ℝ, outerSquareLeft ≤ u ∧ u < v ∧ v ≤ outerSquareRight ∧
    0 < λ ∧ ∀ x ∈ Set.Icc u v, ∀ y ∈ Set.Icc u v, x ≤ y →
      λ*(y-x) ≤ outerSquareProfile x-outerSquareProfile y := by
  obtain ⟨hu,huv,hc,hpos,hzero,_⟩ := outerSquareProfile_crosses
  have hlt : outerSquareLeft < outerSquareRight := lt_of_le_of_ne huv (fun h => by rw [h,hzero] at hpos; exact lt_irrefl _ hpos)
  have hc₁ : ContDiff ℝ 2 splineAutoCorr := Complex.reCLM.contDiff.comp
    (Zeta23.EF.weilTest_contDiff (cx_contDiff contDiff_cubicSpline)
      (cx_contDiff contDiff_cubicSpline).continuous (cx_hasCompactSupport hasCompactSupport_cubicSpline))
  have hdiff (x : ℝ) (hx : 0 < x) : ContDiffAt ℝ 1 outerSquareProfile x := by
    have hh : ContDiff ℝ 1 splineAutoCorr := hc₁.of_le (by decide)
    exact (contDiffAt_const.mul (hh.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne').neg)).div
      (Real.contDiffAt_sqrt hx.ne') (Real.sqrt_pos.mpr hx).ne'
  obtain ⟨z,hz,he⟩ := exists_deriv_eq_slope outerSquareProfile hlt hc (fun x hx =>
    ((hdiff x (zero_lt_one.trans_le (hu.trans hx.1.le))).differentiableAt (by decide)).differentiableWithinAt)
  have hz₀ := zero_lt_one.trans_le (hu.trans hz.1.le)
  have hneg : deriv outerSquareProfile z < 0 := by rw [he,hzero]; exact div_neg_of_neg_of_pos (by linarith only [hpos]) (sub_pos.mpr hlt)
  let λ := -deriv outerSquareProfile z/2
  have hλ : 0 < λ := by dsimp only [λ]; linarith only [hneg]
  have hcder := ((hdiff z hz₀).derivWithin (m := 0) (by decide)).continuousAt
  have hn : {x | x ∈ Set.Ioo outerSquareLeft outerSquareRight ∧ deriv outerSquareProfile x < -λ} ∈ 𝓝 z :=
    (Set.Ioo_mem_nhds hz.1 hz.2).inter (hcder.eventually_lt continuousAt_const (by dsimp only [λ]; linarith only [hneg]))
  obtain ⟨a,b,hab,hw⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let u := (a+z)/2
  let v := (b+z)/2
  have huv' : u < v := by dsimp only [u,v]; linarith only [hab.1,hab.2]
  have hmid {x : ℝ} (hx : x ∈ Set.Icc u v) : x ∈ Set.Ioo a b := by
    dsimp only [u,v] at hx
    exact ⟨by linarith only [hx.1,hab.1],by linarith only [hx.2,hab.2]⟩
  have hsub {x : ℝ} (hx : x ∈ Set.Icc u v) := hw (hmid hx)
  have hu' := (hsub (Set.left_mem_Icc.mpr huv'.le)).1.1.le
  have hv' := (hsub (Set.right_mem_Icc.mpr huv'.le)).1.2.le
  refine ⟨u,v,λ,hu',huv',hv',hλ,fun x hx y hy hxy => ?_⟩
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hh {q : ℝ} (hq : q ∈ Set.Icc x y) := hsub (show q ∈ Set.Icc u v from ⟨hx.1.trans hq.1,hq.2.trans hy.2⟩)
  obtain ⟨q,hq,hs⟩ := exists_deriv_eq_slope outerSquareProfile hxy
    (hc.mono (fun z hz' => (hh hz').1.le)) (fun z hz' =>
      ((hdiff z (zero_lt_one.trans_le (hu.trans (hh ⟨hz'.1.le,hz'.2.le⟩).1.1.le))).differentiableAt (by decide)).differentiableWithinAt)
  have hq' := (hh (show q ∈ Set.Icc x y from ⟨hq.1.le,hq.2.le⟩)).2
  rw [hs] at hq'
  linarith only [(div_lt_iff₀ (sub_pos.mpr hxy)).mp hq']

/-- The outer-band error is independent of multiplicity on the original
mesh. In the square conductor variable it is O(1/(2n+1)). -/
theorem successorSquare_outer_reading_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n m k : ℕ}, 4 ≤ n → 0 < m →
    let R := squareUpperRoot n
    let x := (k:ℝ)/R^2
    outerSquareLeft ≤ x → x ≤ outerSquareRight+1 →
    |successorSquareRawRow n m k + ((m:ℝ)^2/R)*outerSquareProfile x| ≤ C/R := by
  obtain ⟨C,hC,hquad⟩ := original_contact_quadrature
  obtain ⟨E,hE,hread⟩ := successorSquare_outer_reading
  refine ⟨C,hC,fun {n m k} hn hm => ?_⟩
  let R := squareUpperRoot n
  let x := (k:ℝ)/R^2
  let f := outerSquareProfile x
  let I := integratedContact (successorSquareTriple n) k
  change outerSquareLeft ≤ x → x ≤ outerSquareRight+1 → _
  intro hx hy
  have hR : 0 < R := by dsimp only [R,squareUpperRoot]; positivity
  have hk₂ := (hread (m := m) hn hm hx hy).1
  have hk : 0 < k := by omega
  have hroot : R ≤ Real.sqrt k := by
    have hB : R^2 ≤ (k:ℝ) := by
      have hh := (le_div_iff₀ (sq_pos_of_pos hR)).mp (outerSquareProfile_crosses.1.trans hx)
      simpa only [one_mul] using hh
    simpa only [Real.sqrt_sq hR.le] using Real.sqrt_le_sqrt hB
  have hrow (j : ℕ) : |successorSquareRawRow n j k-(j:ℝ)^2*I| ≤ C/R := by
    have hh := hquad _ (j • successorSquareTriple n) hk
    rw [integratedContact_nsmul] at hh
    exact hh.trans (div_le_div_of_nonneg_left hC hR hroot)
  have heq : I+f/R=0 := by
    by_contra hnz
    have hδ := abs_pos.mpr hnz
    obtain ⟨j,hj⟩ := exists_nat_gt (max 1 ((C/R+E/R)/|I+f/R|))
    have hj₁ := (le_max_left _ _).trans_lt hj
    have hj₀ : 0 < (j:ℝ) := zero_lt_one.trans hj₁
    have hlarge := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hj)
    have hjm := (hread (m := j) hn (Nat.cast_pos.mp hj₀) hx hy).2.2
    have hb : (j:ℝ)^2*|I+f/R| ≤ C/R+E*j/R := by
      calc _ = |(successorSquareRawRow n j k+((j:ℝ)^2/R)*f)-(successorSquareRawRow n j k-(j:ℝ)^2*I)| := by
              rw [← abs_of_nonneg (sq_nonneg (j:ℝ)),← abs_mul]; congr 1; ring
        _ ≤ _ := (abs_sub _ _).trans (by linarith only [hjm,hrow j])
    linarith only [hb,mul_lt_mul_of_pos_left hlarge hj₀,
      mul_le_mul_of_nonneg_right hj₁.le (div_nonneg hC hR.le)]
  change |successorSquareRawRow n m k+((m:ℝ)^2/R)*f| ≤ C/R
  have ident : (m:ℝ)^2*I = -(((m:ℝ)^2/R)*f) := by
    linarith only [congrArg (fun z => (m:ℝ)^2*z) heq]
  simpa only [ident,sub_neg_eq_add] using hrow m

/-- Every multiplicity comparable to the largest conductor's square root
loses a fixed proportion of the quadratic prime weight to the original
floors. The proportion may depend on the comparison factor K. -/
theorem successorSquare_floor_loss_at_linear_multiplicities {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      squareUpperRoot n ≤ K*(m:ℝ) → (m:ℝ) ≤ K*squareUpperRoot n →
      c*(n:ℝ)^2 ≤ ordinaryFloorLoss (m • successorSquareTriple n) := by
  obtain ⟨u,v,λ,hu,huv,hv,hλ,hslope⟩ := outer_slope
  obtain ⟨C,hC,hraw⟩ := successorSquare_outer_reading_uniform
  obtain ⟨_,_,hhorizon⟩ := successorSquare_outer_reading
  have hu₁ := outerSquareProfile_crosses.1.trans hu
  have hu₀ := zero_lt_one.trans_le hu₁
  have hK₀ := zero_lt_one.trans_le hK
  have hpos (x : ℝ) : 0 ≤ outerSquareProfile x := div_nonneg
    (mul_nonneg two_pos.le (splineAutoCorr_nonneg _)) (Real.sqrt_nonneg _)
  let A := K^2/λ
  let D := K^2*outerSquareProfile u+2
  have hA : 0 < A := div_pos (sq_pos_of_pos hK₀) hλ
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [mul_nonneg (sq_nonneg K) (hpos u)]
  obtain ⟨e,c,he,hc,hfib⟩ := prime_mass_outside_thin_floor_fibers hA (half_pos (sub_pos.mpr huv))
    hD (hu₁.trans huv.le)
  have hnR (n : ℕ) : (n:ℝ) ≤ squareUpperRoot n := by
    unfold squareUpperRoot; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have htop : Tendsto squareUpperRoot atTop atTop := tendsto_atTop_mono hnR tendsto_natCast_atTop_atTop
  have hBtop := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp htop
  refine ⟨c,hc,?_⟩
  filter_upwards [htop.eventually hfib,hBtop.eventually (proportional_prime_mass hu₀ huv),
    htop.eventually_ge_atTop C,htop.eventually_ge_atTop (2*C/e),eventually_ge_atTop 4] with n hn hmass hnC hne hn₄
  intro m hm hm₁ hm₂
  let R := squareUpperRoot n
  let B := R^2
  let t := (m:ℝ)^2/R
  let P := contactBandPrimes (u*B) (v*B)
  let X := successorSquareRawRow n m
  have hR₁ : 1 ≤ R := by dsimp only [R,squareUpperRoot]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hR := zero_lt_one.trans_le hR₁
  have hB : 0 < B := sq_pos_of_pos hR
  have ht₀ : 0 < t := div_pos (sq_pos_of_pos (Nat.cast_pos.mpr hm)) hR
  have ht₁ : R/K^2 ≤ t := (div_le_div_iff₀ (sq_pos_of_pos hK₀) hR).mpr (by
    linarith only [pow_le_pow_left₀ hR.le hm₁ 2])
  have ht₂ : t ≤ K^2*R := (div_le_iff₀ hR).mpr (by
    linarith only [pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) hm₂ 2])
  have hCe : 2*(C/R) ≤ e := by
    linarith only [(div_le_iff₀ he).mp hne,div_le_div_of_nonneg_right ((div_le_iff₀ he).mp hne) hR.le,
      show R*e/R=e by field_simp]
  have hC₁ : C/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa only [one_mul] using hnC)
  have hmem {p : ℕ} (hp : p ∈ P) : p.Prime ∧ (p:ℝ)/B ∈ Set.Icc u v := by
    obtain ⟨hpr,hl,hr⟩ := (mem_contactBandPrimes (mul_nonneg hu₀.le hB.le) (mul_nonneg (hu₀.trans huv).le hB.le)).mp hp
    exact ⟨hpr,(le_div_iff₀ hB).mpr hl.le,(div_le_iff₀ hB).mpr hr⟩
  have hraw' {p : ℕ} (hp : p ∈ P) : |X p+t*outerSquareProfile ((p:ℝ)/B)| ≤ C/R :=
    hraw hn₄ hm (hu.trans (hmem hp).2.1) ((hmem hp).2.2.trans (hv.trans (le_add_of_nonneg_right zero_le_one)))
  have hrow {p : ℕ} (hp : p ∈ P) : -(D*R) ≤ X p-1 ∧ X p-1 ≤ 0 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp (hraw' hp)
    have hp' := (hmem hp).2
    have hfall := hslope u (Set.left_mem_Icc.mpr huv.le) _ hp' hp'.1
    have hF : outerSquareProfile ((p:ℝ)/B) ≤ outerSquareProfile u :=
      by linarith only [hfall,mul_nonneg hλ.le (sub_nonneg.mpr hp'.1)]
    dsimp only [D]
    exact ⟨by linarith only [hlo,hC₁,hR₁,mul_le_mul ht₂ hF (hpos _) (mul_nonneg (sq_nonneg K) hR.le)],
      by linarith only [hhi,hC₁,mul_nonneg ht₀.le (hpos ((p:ℝ)/B))]⟩
  have hsep (p) (hp : p ∈ P) (q) (hq : q ∈ P) (hpq : p ≤ q) :
      (q:ℝ)-p ≤ A*R*((X q-1)-(X p-1)+e) := by
    have hxy : (p:ℝ)/B ≤ (q:ℝ)/B := div_le_div_of_nonneg_right (Nat.cast_le.mpr hpq) hB.le
    let l := λ*((q:ℝ)/B-(p:ℝ)/B)
    have hl : 0 ≤ l := mul_nonneg hλ.le (sub_nonneg.mpr hxy)
    have hd := hslope _ (hmem hp).2 _ (hmem hq).2 hxy
    have hcomp : (R/K^2)*l ≤ (X q-1)-(X p-1)+e := by
      linarith only [mul_le_mul_of_nonneg_right ht₁ hl,mul_le_mul_of_nonneg_left hd ht₀.le,
        (abs_le.mp (hraw' hp)).2,(abs_le.mp (hraw' hq)).1,hCe]
    calc (q:ℝ)-p = A*R*((R/K^2)*l) := by dsimp only [A,l,B]; field_simp [hR.ne',hK₀.ne',hλ.ne']; <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (mul_nonneg hA.le hR.le)
  have hsave := hn P (fun p => X p-1)
    (fun p hp => ⟨(hmem hp).1,(div_le_iff₀ hB).mp (hmem hp).2.2,hrow hp⟩) hmass hsep
  have hsub : P ⊆ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)) := by
    intro p hp
    have hw := hhorizon hn₄ hm (hu.trans (hmem hp).2.1) ((hmem hp).2.2.trans (hv.trans (le_add_of_nonneg_right zero_le_one)))
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hw.1,hw.2.1⟩,(hmem hp).1⟩
  calc c*(n:ℝ)^2 ≤ c*B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hnR n) 2) hc.le
    _ ≤ ∑ p ∈ P, Int.fract (X p-1)*Real.log p := hsave
    _ = ∑ p ∈ P, Int.fract (X p)*vonMangoldt p := by
      refine sum_congr rfl fun p hp => ?_
      have hpr := (hmem hp).1
      rw [Int.fract_sub_one,← log_contactBase,contactBase,if_pos hpr.isPrimePow,hpr.minFac_eq]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => mul_nonneg (Int.fract_nonneg _) vonMangoldt_nonneg)

/-- At the RH comparison multiplicity the ordinary floors contribute a
uniform quadratic saving on every sufficiently large square conductor. -/
theorem diagonal_ordinary_floor_loss : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c*(n:ℝ)^2 ≤ ordinaryFloorLoss (n • successorSquareTriple n) := by
  obtain ⟨c,hc,h⟩ := successorSquare_floor_loss_at_linear_multiplicities (K := 3) (by norm_num)
  refine ⟨c,hc,?_⟩
  filter_upwards [h,eventually_ge_atTop 1] with n hn hn₁
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  exact hn hn₁ (by unfold squareUpperRoot; linarith only [hn']) (by unfold squareUpperRoot; linarith only [hn'])

#print axioms successorSquare_outer_reading_uniform
#print axioms successorSquare_floor_loss_at_linear_multiplicities
#print axioms diagonal_ordinary_floor_loss

end GaloisForLFunctions.CountingHolography.Sections
