import GaloisForLFunctions.CountingHolography.Sections.TheCoefficientIndependentPrimeMeshError
import GaloisForLFunctions.CountingHolography.Sections.PrimeMassOutsideThinFloorFibers
import GaloisForLFunctions.CountingHolography.Sections.TheOuterBandOfSquareContacts
import GaloisForLFunctions.CountingHolography.Sections.TheCostsBeforeOrdinaryPrimeRounding

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
open ArithmeticScatteringHolography SquareRootThreshold
open BiScaleUncertainty.ChebyshevGauge _root_.RHTower.WeilDeletion

private theorem outer_slope : ∃ u v σ : ℝ, outerSquareLeft ≤ u ∧ u < v ∧ v ≤ outerSquareRight ∧
    0 < σ ∧ ∀ x ∈ Set.Icc u v, ∀ y ∈ Set.Icc u v, x ≤ y →
      σ*(y-x) ≤ outerSquareProfile x-outerSquareProfile y := by
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
  let σ := -deriv outerSquareProfile z/2
  have hσ : 0 < σ := by dsimp only [σ]; linarith only [hneg]
  have hcder := ((hdiff z hz₀).derivWithin (m := 0) (by decide)).continuousAt
  have hn : {x | x ∈ Set.Ioo outerSquareLeft outerSquareRight ∧ deriv outerSquareProfile x < -σ} ∈ 𝓝 z :=
    inter_mem (Ioo_mem_nhds hz.1 hz.2) (hcder.eventually_lt continuousAt_const (by dsimp only [σ]; linarith only [hneg]))
  obtain ⟨a,b,hab,hw⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let u := (a+z)/2
  let v := (b+z)/2
  have huv' : u < v := by dsimp only [u,v]; linarith only [hab.1,hab.2]
  have hmid {x : ℝ} (hx : x ∈ Set.Icc u v) : x ∈ Set.Ioo a b := by
    dsimp only [u,v] at hx
    exact ⟨by linarith only [hx.1,hab.1],by linarith only [hx.2,hab.2]⟩
  have hsub {x : ℝ} (hx : x ∈ Set.Icc u v) : x ∈ Set.Ioo outerSquareLeft outerSquareRight ∧ deriv outerSquareProfile x < -σ := hw (hmid hx)
  have hu' := (hsub (Set.left_mem_Icc.mpr huv'.le)).1.1.le
  have hv' := (hsub (Set.right_mem_Icc.mpr huv'.le)).1.2.le
  refine ⟨u,v,σ,hu',huv',hv',hσ,fun x hx y hy hxy => ?_⟩
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hh {q : ℝ} (hq : q ∈ Set.Icc x y) : q ∈ Set.Ioo outerSquareLeft outerSquareRight ∧ deriv outerSquareProfile q < -σ := hsub (show q ∈ Set.Icc u v from ⟨hx.1.trans hq.1,hq.2.trans hy.2⟩)
  obtain ⟨q,hq,hs⟩ := exists_deriv_eq_slope outerSquareProfile hxy
    (hc.mono (fun _ hz' => ⟨(hh hz').1.1.le,(hh hz').1.2.le⟩)) (fun z hz' =>
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
      calc _ = |(j:ℝ)^2*(I+f/R)| := by rw [abs_mul,abs_of_nonneg (sq_nonneg (j:ℝ))]
        _ = |(successorSquareRawRow n j k+((j:ℝ)^2/R)*f)-(successorSquareRawRow n j k-(j:ℝ)^2*I)| := by
              congr 1; ring
        _ ≤ _ := (abs_sub _ _).trans (by linarith only [hjm,hrow j])
    have hweak : C/R+E*j/R ≤ (j:ℝ)*(C/R+E/R) := by
      rw [mul_add,show E*(j:ℝ)/R=(j:ℝ)*(E/R) by ring]
      exact add_le_add_left (le_mul_of_one_le_left (div_nonneg hC hR.le) hj₁.le) _
    have hstrict := mul_lt_mul_of_pos_left hlarge hj₀
    rw [← mul_assoc,← sq] at hstrict
    exact (not_lt_of_ge (hb.trans hweak)) hstrict
  change |successorSquareRawRow n m k+((m:ℝ)^2/R)*f| ≤ C/R
  have ident : (m:ℝ)^2*I = -(((m:ℝ)^2/R)*f) := by
    rw [show I = -(f/R) by linarith only [heq]]; ring
  simpa only [ident,sub_neg_eq_add] using hrow m

/-- At every prescribed frequency bounded below, the quadratic prime
saving persists up to any fixed multiple of diagonal multiplicity. -/
theorem successorSquare_floor_loss_through_linear_scale {K d : ℝ} (hK : 1 ≤ K) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      d ≤ (m:ℝ)^2/squareUpperRoot n → (m:ℝ) ≤ K*squareUpperRoot n →
      c*(n:ℝ)^2 ≤ ordinaryFloorLoss (m • successorSquareTriple n) := by
  obtain ⟨u,v,σ,hu,huv,hv,hσ,hslope⟩ := outer_slope
  obtain ⟨C,hC,hraw⟩ := successorSquare_outer_reading_uniform
  obtain ⟨_,_,hhorizon⟩ := successorSquare_outer_reading
  have hu₁ := outerSquareProfile_crosses.1.trans hu
  have hu₀ := zero_lt_one.trans_le hu₁
  have hK₀ := zero_lt_one.trans_le hK
  have hpos (x : ℝ) : 0 ≤ outerSquareProfile x := div_nonneg
    (mul_nonneg two_pos.le (splineAutoCorr_nonneg _)) (Real.sqrt_nonneg _)
  let A := 1/σ
  let D := 1+outerSquareProfile u+2/d
  have hA : 0 < A := one_div_pos.mpr hσ
  have hd₂ : 0 < 2/d := div_pos two_pos hd
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [hd₂,hpos u]
  obtain ⟨e,c,he,hc,hfib⟩ := prime_mass_outside_thin_floor_fibers hA (half_pos (sub_pos.mpr huv))
    hD (hu₁.trans huv.le) hd (one_le_pow₀ hK : 1 ≤ K^2)
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
  have ht₂ : t ≤ K^2*R := (div_le_iff₀ hR).mpr (by
    linarith only [pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) hm₂ 2])
  have hCe : 2*(C/R) ≤ e := by
    rw [← mul_div_assoc,div_le_iff₀ hR]
    linarith only [(div_le_iff₀ he).mp hne]
  have hC₁ : C/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa only [one_mul] using hnC)
  have hmem {p : ℕ} (hp : p ∈ P) : p.Prime ∧ (p:ℝ)/B ∈ Set.Icc u v := by
    obtain ⟨hpr,hl,hr⟩ := (mem_contactBandPrimes (mul_nonneg hu₀.le hB.le) (mul_nonneg (hu₀.trans huv).le hB.le)).mp hp
    exact ⟨hpr,(le_div_iff₀ hB).mpr hl.le,(div_le_iff₀ hB).mpr hr⟩
  have hraw' {p : ℕ} (hp : p ∈ P) : |X p+t*outerSquareProfile ((p:ℝ)/B)| ≤ C/R :=
    hraw hn₄ hm (hu.trans (hmem hp).2.1) ((hmem hp).2.2.trans (hv.trans (le_add_of_nonneg_right zero_le_one)))
  have hrow {p : ℕ} (hp : p ∈ P) : -(D*t) ≤ X p-1 ∧ X p-1 ≤ 0 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp (hraw' hp)
    have hp' := (hmem hp).2
    have hfall := hslope u (Set.left_mem_Icc.mpr huv.le) _ hp' hp'.1
    have hF : outerSquareProfile ((p:ℝ)/B) ≤ outerSquareProfile u :=
      by linarith only [hfall,mul_nonneg hσ.le (sub_nonneg.mpr hp'.1)]
    dsimp only [D]
    exact ⟨by linarith only [hlo,hC₁,ht₀,mul_le_mul_of_nonneg_left hF ht₀.le,
          mul_le_mul_of_nonneg_left hm₁ hd₂.le,div_mul_cancel₀ (2:ℝ) hd.ne'],
      by linarith only [hhi,hC₁,mul_nonneg ht₀.le (hpos ((p:ℝ)/B))]⟩
  have hsep (p) (hp : p ∈ P) (q) (hq : q ∈ P) (hpq : p ≤ q) :
      (q:ℝ)-p ≤ (A*(R^2/t))*((X q-1)-(X p-1)+e) := by
    have hxy : (p:ℝ)/B ≤ (q:ℝ)/B := div_le_div_of_nonneg_right (Nat.cast_le.mpr hpq) hB.le
    let l := σ*((q:ℝ)/B-(p:ℝ)/B)
    have hd := hslope _ (hmem hp).2 _ (hmem hq).2 hxy
    have hcomp : t*l ≤ (X q-1)-(X p-1)+e := by
      linarith only [mul_le_mul_of_nonneg_left hd ht₀.le,
        (abs_le.mp (hraw' hp)).2,(abs_le.mp (hraw' hq)).1,hCe]
    calc (q:ℝ)-p = A*(R^2/t)*(t*l) := by dsimp only [A,l,B]; field_simp [hR.ne',ht₀.ne',hσ.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (mul_nonneg hA.le (div_nonneg (sq_nonneg R) ht₀.le))
  have hsave := hn hm₁ ht₂ P (fun p => X p-1)
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

/-- On the previously negative outer window, sufficiently low frequencies
put every reading strictly between minus one and zero. -/
private theorem low_frequency_floor_loss :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      (m:ℝ)^2/squareUpperRoot n ≤ d →
      (n:ℝ)^2/24 ≤ ordinaryFloorLoss (m • successorSquareTriple n) := by
  obtain ⟨A,hA,hsize⟩ := contactMultiplicity_size
  have hA₀ := zero_lt_one.trans_le hA
  let d := 1/(32*A)
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hA₀)
  have ht : Tendsto successorSquareWindowScale atTop atTop := tendsto_atTop_mono
    (fun n => (successorSquareWindowScale_bounds n).1)
    ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  refine ⟨d,hd,?_⟩
  filter_upwards [ht.eventually (proportional_prime_mass (u := 1/3) (v := 1/2) (by norm_num) (by norm_num)),
    eventually_ge_atTop 1] with n hmass hn
  intro m hm hfreq
  let W := successorSquareWindowScale n
  let R := squareUpperRoot n
  let P := contactBandPrimes (W/3) (W/2)
  let L := 3*windowEnd ((2*n+1)^2+1)
  let r := resolution (m • successorSquareTriple n)
  have hR : 0 < R := by dsimp only [R,squareUpperRoot]; positivity
  have hW := successorSquareWindowScale_bounds n
  have hw : W = Real.exp 8*R^2 := by simp only [W,successorSquareWindowScale,R,squareUpperRoot,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hW₀ : 0 < W := by rw [hw]; positivity
  have hL₀ : 9 ≤ windowEnd ((2*n+1)^2+1) := by exact_mod_cast hW.2.1.trans hW.2.2
  have hL : 11 ≤ L := by dsimp only [L]; omega
  have hP : W/12 ≤ ∑ p ∈ P, Real.log p := by
    simpa only [P,contactBandPrimes,one_div_mul_eq_div,show ((1:ℝ)/2-1/3)/2=1/12 by norm_num,W] using hmass
  have hpr {p : ℕ} (hp : p ∈ P) : p.Prime ∧ W/3 < p ∧ (p:ℝ) ≤ W/2 :=
    (mem_contactBandPrimes (by positivity) (by positivity)).mp hp
  have hf {p : ℕ} (hp : p ∈ P) : 1/2 ≤ Int.fract (successorSquareRawRow n m p) := by
    obtain ⟨_,hlo,hhi⟩ := hpr hp
    let y := contactMultiplicity (packet (successorSquareTriple n)) L r p
    have hx : successorSquareRawRow n m p = (m:ℝ)^2*y := by
      change contactMultiplicity (packet (m • successorSquareTriple n)) L r p = _
      rw [packet_smul,contactMultiplicity_scale]
    have hy : y < 0 := successorSquare_negative_window hn (hm.trans_le (successorSquare_resolution_ge n m)) hL hlo hhi
    have hroot : R ≤ Real.sqrt p := by
      have hsq : R^2 ≤ (p:ℝ) := by
        rw [hw] at hlo
        linarith only [hlo,mul_le_mul_of_nonneg_right (Real.add_one_le_exp (8:ℝ)) (sq_nonneg R)]
      simpa only [Real.sqrt_sq hR.le] using Real.sqrt_le_sqrt hsq
    have hb := hsize _ (successorSquareTriple n) L r p
    have hv := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2
    have hh : |y| ≤ 16*A/R := hb.trans (div_le_div₀ (by positivity)
      (by linarith only [mul_le_mul_of_nonneg_left hv hA₀.le]) hR hroot)
    have hcap : |successorSquareRawRow n m p| ≤ 1/2 := by
      rw [hx,abs_mul,abs_of_nonneg (sq_nonneg (m:ℝ))]
      refine (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans ?_
      calc _ = (16*A)*((m:ℝ)^2/R) := by ring
        _ ≤ (16*A)*d := mul_le_mul_of_nonneg_left hfreq (by positivity)
        _ = _ := by dsimp only [d]; field_simp [hA₀.ne']; ring
    have hneg : successorSquareRawRow n m p < 0 := hx ▸ mul_neg_of_pos_of_neg (sq_pos_of_pos (Nat.cast_pos.mpr hm)) hy
    have hfloor : ⌊successorSquareRawRow n m p⌋ = -1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith only [(abs_le.mp hcap).1,hneg]
    have he := Int.floor_add_fract (successorSquareRawRow n m p)
    rw [hfloor] at he
    push_cast at he
    linarith only [he,(abs_le.mp hcap).1]
  have hsub : P ⊆ ordinaryPrimeLags L := by
    intro p hp
    obtain ⟨hprime,_,hhi⟩ := hpr hp
    have hup : (p:ℝ) ≤ windowEnd ((2*n+1)^2+1) := by linarith only [hhi,hW.2.2,hW₀]
    have hup' : p ≤ windowEnd ((2*n+1)^2+1) := by exact_mod_cast hup
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.two_le,by dsimp only [L]; omega⟩,hprime⟩
  calc (n:ℝ)^2/24 ≤ (1/2:ℝ)*∑ p ∈ P, Real.log p := by linarith only [hP,hW.1]
    _ ≤ ∑ p ∈ P, Int.fract (successorSquareRawRow n m p)*vonMangoldt p := by
      rw [mul_sum]
      refine sum_le_sum fun p hp => ?_
      have hprime := (hpr hp).1
      have he : Real.log p = vonMangoldt p := by rw [← log_contactBase,contactBase,if_pos hprime.isPrimePow,hprime.minFac_eq]
      rw [he]; exact mul_le_mul_of_nonneg_right (hf hp) vonMangoldt_nonneg
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => mul_nonneg (Int.fract_nonneg _) vonMangoldt_nonneg)

/-- Every positive prescribed multiplicity through each fixed multiple of
diagonal multiplicity has quadratic original floor loss. -/
theorem all_multiplicities_through_diagonal_ordinary_floor_loss {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m → (m:ℝ) ≤ K*squareUpperRoot n →
      c*(n:ℝ)^2 ≤ ordinaryFloorLoss (m • successorSquareTriple n) := by
  obtain ⟨d,hd,hsmall⟩ := low_frequency_floor_loss
  obtain ⟨c,hc,hhigh⟩ := successorSquare_floor_loss_through_linear_scale hK hd
  refine ⟨min (1/24:ℝ) c,lt_min (by norm_num) hc,?_⟩
  filter_upwards [hsmall,hhigh] with n hn hs
  intro m hm htop
  rcases le_total ((m:ℝ)^2/squareUpperRoot n) d with hl | hl
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg (n:ℝ))).trans ((by
      linarith only [hn hm hl] : (1/24:ℝ)*(n:ℝ)^2 ≤ ordinaryFloorLoss (m • successorSquareTriple n)))
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg (n:ℝ))).trans (hs hm hl htop)

/-- At the RH comparison multiplicity the ordinary floors contribute a
uniform quadratic saving on every sufficiently large square conductor. -/
theorem diagonal_ordinary_floor_loss : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c*(n:ℝ)^2 ≤ ordinaryFloorLoss (n • successorSquareTriple n) := by
  obtain ⟨c,hc,h⟩ := all_multiplicities_through_diagonal_ordinary_floor_loss (K := 1) le_rfl
  refine ⟨c,hc,?_⟩
  filter_upwards [h,eventually_ge_atTop 1] with n hn hn₁
  exact hn hn₁ (by unfold squareUpperRoot; linarith only [Nat.cast_nonneg (α := ℝ) n])

/-- At diagonal multiplicity the normalized ordinary generator lies a
fixed distance below the signed integrated prime contact at every late
conductor. -/
theorem diagonal_log_generator_below_integrated_contact : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
    Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n) : ℝ) ≤
      (n:ℝ)^2*(ordinaryPrimeContact (successorSquareTriple n)-δ) := by
  obtain ⟨c,hc,hfloor⟩ := diagonal_ordinary_floor_loss
  obtain ⟨C,_,hmesh⟩ := successorSquare_floor_corrected_mesh_error
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hfloor,eventually_ge_atTop ⌈2*C/c⌉₊,eventually_ge_atTop 1] with n hf hn hn₁
  have he : 2*C/c ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hm := (abs_le.mp (hmesh hn₁ n)).2
  linarith only [hm,hf,mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp he) (Nat.cast_nonneg (α := ℝ) n)]

/-- Every prescribed multiplicity through the actual zero-width scale has
an exponentially small ordinary generator and exponentially many original
sections. -/
theorem all_square_sections_at_the_zero_width :
    ∃ K γ : ℝ, 1 ≤ K ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      K*(m:ℝ) ≤ ((n:ℝ)+1)^(1-zetaZeroWidth) → let a := m • successorSquareTriple n
      Real.log (ordinaryPrimeGenerator a : ℝ) ≤ -(γ*(n:ℝ)^2) ∧
      Real.log (generator a : ℝ)+γ*(n:ℝ)^2 ≤ radius a ∧
      2*⌊Real.exp (γ*(n:ℝ)^2)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨c,hc,hfloor⟩ := all_multiplicities_through_diagonal_ordinary_floor_loss (K := 1) le_rfl
  obtain ⟨E,hE,hcost⟩ := square_cost_before_ordinary_floors
  let D := 1+4*E/c
  have hE₀ : 0 ≤ 4*E := by linarith only [hE]
  have hD : 1 ≤ D := le_add_of_nonneg_right (div_nonneg hE₀ hc.le)
  have hED : 4*E ≤ D*c := (div_le_iff₀ hc).mp (le_add_of_nonneg_left zero_le_one)
  refine ⟨2*D,c/2,by linarith only [hD],half_pos hc,?_⟩
  filter_upwards [hfloor,eventually_ge_atTop 1] with n hn hn₁
  intro m hm hs
  let g := ((n:ℝ)+1)^zetaZeroWidth
  let a := m • successorSquareTriple n
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  have hn₀ := Nat.cast_nonneg (α := ℝ) n
  have hm₀ := Nat.cast_nonneg (α := ℝ) m
  have hX : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left hn₀
  have hg : 1 ≤ g := Real.one_le_rpow hX zetaZeroWidth_nonneg
  have hg₀ := zero_le_one.trans hg
  have hprod : ((n:ℝ)+1)^(1-zetaZeroWidth)*g=(n:ℝ)+1 := by
    unfold g; rw [← Real.rpow_add (zero_lt_one.trans_le hX),sub_add_cancel,Real.rpow_one]
  have hh := mul_le_mul_of_nonneg_right hs hg₀
  rw [hprod] at hh
  have hDm : D*((m:ℝ)*g) ≤ n := by linarith only [hh,hn']
  have hmle : (m:ℝ) ≤ (m:ℝ)*g := le_mul_of_one_le_right hm₀ hg
  have hmg : (m:ℝ)*g ≤ n := by linarith only [hDm,mul_le_mul_of_nonneg_right hD (mul_nonneg hm₀ hg₀)]
  have hEm : 4*E*((m:ℝ)*g) ≤ c*n := by
    linarith only [mul_le_mul_of_nonneg_right hED (mul_nonneg hm₀ hg₀),mul_le_mul_of_nonneg_right hDm hc.le]
  have hq := mul_le_mul hEm hmg (mul_nonneg hm₀ hg₀) (mul_nonneg hc.le hn₀)
  have hl := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hmle hE₀).trans hEm) hn₀
  have hf := hn hm (show (m:ℝ) ≤ 1*squareUpperRoot n by unfold squareUpperRoot; linarith only [hmle,hmg,hn₀])
  have hb := hcost hn₁ hm
  change max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a)+
    ordinaryFloorLoss a ≤ E*(((m:ℝ)*g)^2+(n:ℝ)*m) at hb
  have hfit : max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a) ≤ -((c/2)*(n:ℝ)^2) := by
    linarith only [hf,hb,hq,hl]
  obtain ⟨ho,hfull⟩ := max_le_iff.mp hfit
  refine ⟨ho,by linarith only [hfull],?_⟩
  have hpos : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  have hroom := Real.exp_le_exp.mpr (show (c/2)*(n:ℝ)^2 ≤ radius a-Real.log (generator a : ℝ) by linarith only [hfull])
  rw [Real.exp_sub,Real.exp_log hpos] at hroom
  rw [card_smallSections]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.floor_mono hroom)) 1

#print axioms successorSquare_outer_reading_uniform
#print axioms successorSquare_floor_loss_through_linear_scale
#print axioms all_multiplicities_through_diagonal_ordinary_floor_loss
#print axioms diagonal_ordinary_floor_loss
#print axioms diagonal_log_generator_below_integrated_contact
#print axioms all_square_sections_at_the_zero_width

end GaloisForLFunctions.CountingHolography.Sections
