import GaloisForLFunctions.RestrictedFactorizationCalculus.TransportAcrossOrderedFibres

/-!
# A positive-density subfamily on the three-prime scale

Three disjoint prime intervals at the cube root of the cutoff give a Cartesian
family of empty ordered fibres. The same largest-pair matching covers the
whole family, whose size is at least a constant times `X / log³ X`.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem eventually_eighth_window :
    ∀ᶠ y : ℝ in atTop, ∀ a : ℝ, 1 ≤ a → a ≤ 5/4 →
      y / (32 * Real.log y) ≤ ((windowPrimes (a*y) ((a+1/8)*y)).card : ℝ) := by
  obtain ⟨T,_,h⟩ := exists_card_windowPrimes_div_ge 1 (by norm_num : (0:ℝ)<1/2)
  filter_upwards [eventually_ge_atTop (max 2 T),
    Real.tendsto_log_atTop.eventually_ge_atTop 8] with y hy hlog a ha hb
  have hy2 : 2 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 < y := by linarith only [hy2]
  have hlog2 : Real.log (2*y) = Real.log 2 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hpos : 0 < Real.log (2*y) := by rw [hlog2]; linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  have hl := h (2*y) (by linarith [((le_max_right _ _).trans hy : T ≤ y)])
    2 (by norm_num) (by norm_num) (2*(a*y)) (2*((a+1/8)*y))
    (by nlinarith only [mul_le_mul_of_nonneg_right ha hy0.le]) (by linarith only [hy0])
    (by nlinarith only [mul_le_mul_of_nonneg_right hb hy0.le]) (by
      rw [Nat.cast_one, Real.rpow_one, div_le_iff₀ hpos]
      have h8 : 8 ≤ Real.log (2*y) := by rw [hlog2]; linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
      nlinarith only [mul_le_mul_of_nonneg_left h8 hy0.le])
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
      mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] at hl
  refine le_trans ?_ hl
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hh : Real.log (2*y) ≤ 2 * Real.log y := by
    rw [hlog2]; linarith only [Real.log_le_log (by norm_num : (0:ℝ)<2) hy2]
  nlinarith only [mul_le_mul_of_nonneg_left hh hy0.le]

private def box (y : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  windowPrimes y (9/8*y) ×ˢ (windowPrimes (9/8*y) (5/4*y) ×ˢ
    windowPrimes (5/4*y) (11/8*y))

private def value (a : ℕ × ℕ × ℕ) := a.1 * (a.2.1 * a.2.2)

private theorem box_factors {y : ℝ} (hy : 0 ≤ y) {p q r : ℕ} (h : (p,q,r) ∈ box y) :
    (p.Prime ∧ y < p ∧ (p:ℝ) ≤ 9/8*y) ∧
    (q.Prime ∧ 9/8*y < q ∧ (q:ℝ) ≤ 5/4*y) ∧
    (r.Prime ∧ 5/4*y < r ∧ (r:ℝ) ≤ 11/8*y) := by
  obtain ⟨a,b⟩ := mem_product.mp h
  obtain ⟨b,c⟩ := mem_product.mp b
  exact ⟨(mem_windowPrimes hy (by positivity)).1 a,
    (mem_windowPrimes (by positivity) (by positivity)).1 b,
    (mem_windowPrimes (by positivity) (by positivity)).1 c⟩

private theorem box_injective {y : ℝ} (hy : 0 ≤ y) : Set.InjOn value (box y) := by
  rintro ⟨p,q,r⟩ h ⟨a,b,d⟩ h' he
  obtain ⟨⟨hp,_,hp1⟩,⟨hq,hq0,hq1⟩,hr,hr0,_⟩ := box_factors hy h
  obtain ⟨⟨ha,_,ha1⟩,⟨hb,hb0,hb1⟩,hd,hd0,_⟩ := box_factors hy h'
  obtain ⟨hm,hn⟩ := stem_ordered_triple hp hq hr (by exact_mod_cast hp1.trans_lt hq0)
    (by exact_mod_cast hq1.trans_lt hr0)
  obtain ⟨hm',hn'⟩ := stem_ordered_triple ha hb hd (by exact_mod_cast ha1.trans_lt hb0)
    (by exact_mod_cast hb1.trans_lt hd0)
  change p*(q*r) = a*(b*d) at he
  rw [he,hn'] at hn
  subst a
  rw [he,hm'] at hm
  have heq := Nat.eq_of_mul_eq_mul_left hp.pos hm.symm
  subst b
  have her := Nat.eq_of_mul_eq_mul_left hq.pos (Nat.eq_of_mul_eq_mul_left hp.pos he)
  subst d
  rfl

/-- At every large dyadic cutoff one restricted matching transports
`≫ X/log³ X` negative vertices out of their empty ordered fibres. -/
theorem eventually_transported_empty_fibre_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        C * X / Real.log X ^ 3 ≤
          ((M.targets.filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅)).card : ℝ) := by
  obtain ⟨T,hT⟩ := exists_transport_covering_empty_fibres 3 0
  have hlim : Tendsto (fun X : ℕ => (X:ℝ)^(1/3:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine ⟨1/32^3,by norm_num,?_⟩
  filter_upwards [hlim.eventually_ge_atTop (max 2 (2*T)),
    hlim.eventually eventually_eighth_window] with X hx hcount
  let y := (X:ℝ)^(1/3:ℝ)
  have hy2 : 2 ≤ y := (le_max_left _ _).trans hx
  have hy0 : 0 < y := by linarith only [hy2]
  have hy3 : y^3 = (X:ℝ) := by
    dsimp [y]; rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]
    norm_num
  obtain ⟨M,hM⟩ := hT X (2*X)
  refine ⟨M,?_⟩
  have hsub : (box y).image value ⊆ M.targets.filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅) := by
    intro n hn
    obtain ⟨⟨p,q,r⟩,ha,rfl⟩ := mem_image.mp hn
    obtain ⟨⟨hp,hp0,hp1⟩,⟨hq,hq0,hq1⟩,hr,hr0,hr1⟩ := box_factors hy0.le ha
    have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
    have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
    have hpq : p < q := by exact_mod_cast hp1.trans_lt hq0
    have hqr : q < r := by exact_mod_cast hq1.trans_lt hr0
    have hnl : (X:ℝ) < (p:ℝ)*(q*r) := by
      rw [← hy3]
      calc y^3 = y*(y*y) := by ring
           _ < _ := mul_lt_mul_of_pos_right hp0 (mul_pos hy0 hy0) |>.trans_le
             (mul_le_mul_of_nonneg_left (mul_le_mul (by linarith only [hq0,hy0])
               (by linarith only [hr0,hy0]) hy0.le hqR.le) hpR.le)
    have hnu : (p:ℝ)*(q*r) ≤ 2*X := by
      rw [← hy3]
      calc _ ≤ (9/8*y)*((5/4*y)*(11/8*y)) := by gcongr
           _ ≤ 2*y^3 := by nlinarith only [pow_nonneg hy0.le 3]
    let s := Real.sqrt ((X:ℝ)/p)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s^2 = (X:ℝ)/p := Real.sq_sqrt (by positivity)
    have hsy : s ≤ y := by
      have hh : (X:ℝ)/p ≤ y^2 := (div_le_iff₀ hpR).2 (by
        rw [← hy3]; nlinarith only [mul_le_mul_of_nonneg_left hp0.le (sq_nonneg y)])
      by_contra! hlt
      have hg := mul_lt_mul_of_pos_right hlt (add_pos_of_pos_of_nonneg hy0 hs0)
      nlinarith only [hs2,hh,hg]
    have hys : y ≤ 2*s := by
      have hh : y^2/4 ≤ (X:ℝ)/p := (le_div_iff₀ hpR).2 (by
        rw [← hy3]; nlinarith only [mul_le_mul_of_nonneg_left hp1 (sq_nonneg y),pow_nonneg hy0.le 3])
      by_contra! hlt
      nlinarith only [hs2,hh,mul_lt_mul_of_pos_right hlt (show 0<y+2*s by linarith only [hy0,hs0])]
    have hl : (X:ℝ)/p/q < r := by
      rw [div_lt_iff₀ hqR, div_lt_iff₀ hpR]; linarith only [hnl]
    have hu : (r:ℝ) ≤ (2*X:ℕ)/ (p:ℝ)/q := by
      rw [le_div_iff₀ hqR, le_div_iff₀ hpR]; push_cast; linarith only [hnu]
    have hw : q*r ∈ productRow (↑(3:ℕ)+1) X (2*X) p := by
      apply mem_filter.mpr
      have hqlo : s / (↑(3:ℕ)+1) < q := by norm_num; linarith only [hsy,hq0,hy0]
      refine ⟨mem_biUnion.mpr ⟨q,(mem_windowPrimes (by positivity) (by positivity)).2
        ⟨hq,hqlo,by change (q:ℝ) ≤ (↑(3:ℕ)+1)*s; norm_num; linarith only [hys,hq1,hy0]⟩,
        mem_image.mpr ⟨r,(mem_windowPrimes (by positivity) (by positivity)).2 ⟨hr,hl,hu⟩,rfl⟩⟩,
        q,r,hq,hr,hqr,rfl,hqlo,?_⟩
      exact fun d hd => (Nat.le_of_dvd hp.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hpq
    have hpU : p ≤ 2*X := by
      have hle : p ≤ p*(q*r) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hq.pos hr.pos)
      exact hle.trans (by exact_mod_cast hnu)
    exact mem_filter.mpr (hM p (mem_Icc.mpr ⟨hp.pos,hpU⟩) (moebius_apply_prime hp) (q*r) hw
      (by change T ≤ s; linarith only [hys,((le_max_right _ _).trans hx : 2*T ≤ y)])
      le_rfl (by simp only [pow_zero, div_one, Nat.cast_mul, Nat.cast_ofNat]; ring_nf))
  have h1 := hcount 1 le_rfl (by norm_num)
  have h2 := hcount (9/8) (by norm_num) (by norm_num)
  have h3 := hcount (5/4) (by norm_num) le_rfl
  change y / (32 * Real.log y) ≤ _ at h1 h2 h3
  norm_num at h1 h2 h3
  have hlog : 0 < Real.log y := Real.log_pos (by linarith only [hy2])
  have hcard : y^3/(32*Real.log y)^3 ≤ ((box y).card:ℝ) := by
    rw [← div_pow]
    simp only [box, card_product, Nat.cast_mul]
    calc (y/(32*Real.log y))^3 = (y/(32*Real.log y)) *
                                 ((y/(32*Real.log y))*(y/(32*Real.log y))) := by ring
         _ ≤ _ := mul_le_mul h1 (mul_le_mul h2 h3 (by positivity) (by positivity)) (by positivity) (by positivity)
  have hlogX : Real.log X = 3 * Real.log y := by rw [← hy3,Real.log_pow]; norm_num
  have hmass : (1/32^3:ℝ) * X / Real.log X ^ 3 ≤ y^3/(32*Real.log y)^3 := by
    rw [hlogX,← hy3]
    field_simp
    positivity
  refine hmass.trans (hcard.trans ?_)
  exact_mod_cast ((card_image_of_injOn (box_injective hy0.le)).symm.le.trans (card_le_card hsub))

end GaloisForLFunctions.RestrictedFactorizationCalculus
