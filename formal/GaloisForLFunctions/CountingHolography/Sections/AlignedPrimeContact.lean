import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOnPrimePairs
import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.STruncatedExplicitTowers

/-!
# The prime row aligned with its two conductor atoms

At ratio p, the upper atom of the pair of conductors 1 and p aligns with
the lower atom. This contributes the full squared spline mass, independently
of the conductor. For log p greater than eight the other products vanish.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory AbsoluteGeometryOfSpecZ
open BiScaleUncertainty.ChebyshevGauge

private def center : ℝ := Real.log 3 + 5
private def atom (u : ℝ) : ℝ := cubicSpline (u-center)

private theorem atom_nonneg (u : ℝ) : 0 ≤ atom u := cubicSpline_nonneg _

private theorem atom_disjoint {u v : ℝ} (h : 8 < v-u) : atom u * atom v = 0 := by
  by_cases hu : atom u = 0
  · rw [hu,zero_mul]
  apply mul_eq_zero_of_right
  by_contra hv
  have hb {x : ℝ} (hx : atom x ≠ 0) : |x-center| ≤ 4 :=
    le_of_not_gt fun hh => hx (cubicSpline_eq_zero hh)
  linarith only [(abs_le.mp (hb hu)).1,(abs_le.mp (hb hv)).2,h]

private theorem packet_pair {p : ℕ} (hp : 0 < p) (u : ℝ) :
    packet (primePair p) u = atom (u-Real.log p) + atom u := by
  have he : ((p-1 : ℕ) : ℝ) + 1 = p := by rw [Nat.cast_sub hp]; push_cast; ring
  unfold packet splineSource primePair
  simp only [Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq, sum_ite_eq', mem_univ,
    if_true, Fin.val_zero, Nat.cast_zero, zero_add, Real.log_one, sub_zero, he]
  change cubicSpline (u-center-Real.log p) + cubicSpline (u-center) = _
  unfold atom
  rw [show u-center-Real.log p = u-Real.log p-center by ring]

private theorem aligned_product {p : ℕ} (hp : 0 < p) (u : ℝ) :
    atom u ^ 2 ≤ packet (primePair p) u * packet (primePair p) (u+Real.log p) := by
  rw [packet_pair hp,packet_pair hp,add_sub_cancel_right]
  calc atom u^2 = atom u * atom u := sq _
    _ ≤ _ := mul_le_mul (le_add_of_nonneg_left (atom_nonneg _))
      (le_add_of_nonneg_right (atom_nonneg _)) (atom_nonneg u)
      (add_nonneg (atom_nonneg _) (atom_nonneg _))

private theorem aligned_product_eq {p : ℕ} (hp : 0 < p) (h : 8 < Real.log p) (u : ℝ) :
    packet (primePair p) u * packet (primePair p) (u+Real.log p) = atom u ^ 2 := by
  rw [packet_pair hp,packet_pair hp,add_sub_cancel_right]
  have h₁ := atom_disjoint (show 8 < u-(u-Real.log p) by linarith only [h])
  have h₂ := atom_disjoint (show 8 < (u+Real.log p)-(u-Real.log p) by linarith only [h])
  have h₃ := atom_disjoint (show 8 < (u+Real.log p)-u by linarith only [h])
  rw [add_mul, mul_add, mul_add, h₁, h₂, h₃]
  ring

private theorem resolution_ray {p : ℕ} (hp : p.Prime) :
    Tendsto (fun m : ℕ => resolution (m • primePair p)) atTop atTop := by
  have hi : (⟨p-1, by omega⟩ : Fin (p+1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    have := hp.two_le
    change p-1 = 0 at hv
    omega
  have h₀ : primePair p 0 = 1 := by simp [primePair, Pi.single_apply, hi, Ne.symm hi]
  apply tendsto_resolution_ray
  intro hz
  have he := congrFun hz 0
  rw [h₀] at he
  exact one_ne_zero he

private def pairEnd (p : ℕ) := 3*windowEnd (p+1)

private def integratedPrimeRow (p : ℕ) : ℝ :=
  2/Real.sqrt p * ∫ u in (0:ℝ)..Real.log (1+(pairEnd p : ℝ)),
    packet (primePair p) u * packet (primePair p) (u+Real.log p)

private theorem pairEnd_bounds (p : ℕ) : p ≤ pairEnd p ∧ center+4 ≤ Real.log (1+(pairEnd p : ℝ)) := by
  let X := ((p+1 : ℕ) : ℝ)+1
  have hX : 1 ≤ X := by dsimp only [X]; linarith only [Nat.cast_nonneg (α := ℝ) (p+1)]
  have hcenter : 4 ≤ center := by
    dsimp only [center]; linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hK : 0 < windowEnd (p+1) := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hK' : (0 : ℝ) < windowEnd (p+1) := Nat.cast_pos.mpr hK
  have hlog : center + Real.log X + 5 ≤ Real.log (windowEnd (p+1)) :=
    (Real.le_log_iff_exp_le hK').mpr (Nat.le_ceil _)
  have hxK : X ≤ windowEnd (p+1) := (Real.log_le_log_iff (zero_lt_one.trans_le hX) hK').mp
    (by linarith only [hcenter,hlog])
  have hpK : p ≤ windowEnd (p+1) := by
    exact_mod_cast (show (p : ℝ) ≤ windowEnd (p+1) from
      le_trans (by dsimp [X]; push_cast; linarith) hxK)
  have hKL : (windowEnd (p+1) : ℝ) ≤ 1+(pairEnd p : ℝ) := by
    dsimp only [pairEnd]; push_cast; linarith only [hK']
  refine ⟨by dsimp only [pairEnd]; omega,?_⟩
  exact le_trans (by linarith only [hlog,Real.log_nonneg hX]) (Real.log_le_log hK' hKL)

private theorem atom_integral (p : ℕ) :
    (∫ u in (0:ℝ)..Real.log (1+(pairEnd p : ℝ)), atom u^2) = ∫ u, cubicSpline u^2 := by
  have hc : 4 < center := by
    dsimp only [center]; linarith only [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hR := (pairEnd_bounds p).2
  rw [intervalIntegral.integral_of_le (by linarith only [hc,hR])]
  calc (∫ u in Set.Ioc (0:ℝ) (Real.log (1+(pairEnd p : ℝ))), atom u^2) = ∫ u, atom u^2 := by
         apply setIntegral_eq_integral_of_forall_compl_eq_zero
         intro u hu
         have he : atom u = 0 := by
           apply cubicSpline_eq_zero
           obtain h | h := not_and_or.mp hu
           · linarith only [not_lt.mp h,hc,neg_le_abs (u-center)]
           · linarith only [not_le.mp h,hR,le_abs_self (u-center)]
         rw [he,zero_pow (by decide : 2 ≠ 0)]
    _ = _ := integral_sub_right_eq_self (fun u : ℝ => cubicSpline u^2) center

private theorem continuous_pair {p : ℕ} (hp : 0 < p) : Continuous (packet (primePair p)) := by
  rw [funext (packet_pair hp)]
  unfold atom
  exact (contDiff_cubicSpline.continuous.comp ((continuous_id.sub continuous_const).sub continuous_const)).add
    (contDiff_cubicSpline.continuous.comp (continuous_id.sub continuous_const))

private theorem integratedPrimeRow_bound {p : ℕ} (hp : p.Prime) :
    2/Real.sqrt p * (∫ u, cubicSpline u^2) ≤ integratedPrimeRow p := by
  rw [← atom_integral p]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h0 : 0 ≤ Real.log (1+(pairEnd p : ℝ)) := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) (pairEnd p)])
  apply intervalIntegral.integral_mono_on h0
    ((contDiff_cubicSpline.continuous.comp (continuous_id.sub continuous_const)).pow 2).intervalIntegrable
    ((continuous_pair hp.pos).mul ((continuous_pair hp.pos).comp (continuous_id.add continuous_const))).intervalIntegrable
  exact fun u _ => aligned_product hp.pos u

private theorem integratedPrimeRow_exact {p : ℕ} (hp : p.Prime) (h : 8 < Real.log p) :
    integratedPrimeRow p = 2/Real.sqrt p * (∫ u, cubicSpline u^2) := by
  unfold integratedPrimeRow
  simp only [aligned_product_eq hp.pos h,atom_integral]

/-- The actual exponent imposed by the ordinary p row. -/
def alignedExponent (p m : ℕ) : ℕ :=
  ⌊contactMultiplicity (packet (m • primePair p)) (pairEnd p) (resolution (m • primePair p)) p⌋₊

private theorem tendsto_alignedExponent {p : ℕ} (hp : p.Prime) :
    Tendsto (fun m : ℕ => (alignedExponent p m : ℝ)/(m : ℝ)^2) atTop (𝓝 (integratedPrimeRow p)) := by
  let X (m : ℕ) := contactMultiplicity (packet (m • primePair p)) (pairEnd p) (resolution (m • primePair p)) p
  have hL := hp.one_le.trans (pairEnd_bounds p).1
  have hlim := ((tendsto_contactRow (continuous_pair hp.pos) hL hp.one_le).const_mul (2/Real.sqrt p)).comp
    (resolution_ray hp)
  have hraw : Tendsto (fun m : ℕ => X m/(m : ℝ)^2) atTop (𝓝 (integratedPrimeRow p)) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with m hm
    change contactMultiplicity (packet (primePair p)) _ _ p = _
    dsimp only [X]
    rw [packet_smul,contactMultiplicity_scale,mul_div_cancel_left₀ _ (by positivity : (m : ℝ)^2 ≠ 0)]
  have hX (m : ℕ) : 0 ≤ X m := by
    have hpacket (u : ℝ) : 0 ≤ packet (m • primePair p) u := by
      rw [packet_smul,packet_pair hp.pos]
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (atom_nonneg _) (atom_nonneg _))
    unfold X contactMultiplicity
    exact mul_nonneg (by positivity) (sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (hpacket _) (hpacket _)) (Nat.cast_nonneg _))
  have hi : Tendsto (fun m : ℕ => 1/(m : ℝ)^2) atTop (𝓝 0) := by
    simp only [one_div]
    exact ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [sub_zero] using hraw.sub hi) hraw
  · filter_upwards with m
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    change X m-1 ≤ (⌊X m⌋₊ : ℝ)
    linarith only [Nat.lt_floor_add_one (X m)]
  · filter_upwards with m
    exact div_le_div_of_nonneg_right (Nat.floor_le (hX m)) (sq_nonneg _)

/-- At separated conductors the aligned row has precisely the squared
spline mass as its coefficient, with the unitary factor 2/√p. -/
theorem alignedExponent_tateLimit {p : ℕ} (hp : p.Prime) (h : 8 < Real.log p) :
    Tendsto (fun m : ℕ => (alignedExponent p m : ℝ)/(m : ℝ)^2) atTop
      (𝓝 (2/Real.sqrt p * (∫ u, cubicSpline u^2))) := by
  rw [← integratedPrimeRow_exact hp h]
  exact tendsto_alignedExponent hp

private theorem aligned_dvd {p : ℕ} (hp : p.Prime) (m : ℕ) :
    p^(alignedExponent p m) ∣ contactModulus (m • primePair p) := by
  have he : contactBase p = p := by rw [contactBase,if_pos hp.isPrimePow,hp.minFac_eq]
  unfold contactModulus
  have hh : p ∈ Icc 2 (pairEnd p) := mem_Icc.mpr ⟨hp.two_le,(pairEnd_bounds p).1⟩
  simpa only [he,alignedExponent,pairEnd] using dvd_prod_of_mem (fun k => contactBase k ^
    ⌊contactMultiplicity (packet (m • primePair p)) (pairEnd p) (resolution (m • primePair p)) k⌋₊) hh

/-- Beyond the diameter of the two supports, even the cross terms vanish
at each individual mesh point. -/
private theorem separated_row_zero {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hshift : 8 + Real.log p < Real.log k) (m L n : ℕ) :
    contactMultiplicity (packet (m • primePair p)) L n k = 0 := by
  by_cases hn : n = 0
  · simp [hn, contactMultiplicity]
  have hlogp := Real.log_natCast_nonneg p
  unfold contactMultiplicity
  rw [sum_eq_zero, mul_zero]
  intro j hj
  have hj' : 0 < j := (Nat.zero_le n).trans_lt (mem_Ioc.mp hj).1
  let u := Real.log ((j : ℝ)/n)
  have he : Real.log (((j*k : ℕ) : ℝ)/n) = u + Real.log k := by
    rw [Nat.cast_mul,show (j : ℝ)*k/n = (j/n)*k by ring,
      Real.log_mul (div_ne_zero (Nat.cast_ne_zero.mpr hj'.ne') (Nat.cast_ne_zero.mpr hn)) (Nat.cast_ne_zero.mpr hk.ne')]
  have h₁ := atom_disjoint (show 8 < (u+Real.log k-Real.log p)-(u-Real.log p) by linarith only [hshift,hlogp])
  have h₂ := atom_disjoint (show 8 < (u+Real.log k)-(u-Real.log p) by linarith only [hshift,hlogp])
  have h₃ := atom_disjoint (show 8 < (u+Real.log k-Real.log p)-u by linarith only [hshift])
  have h₄ := atom_disjoint (show 8 < (u+Real.log k)-u by linarith only [hshift,hlogp])
  simp only [degreeSample, packet_smul, he, ← show u = Real.log ((j : ℝ)/n) by rfl,
    packet_pair hp.pos]
  have hz : (atom (u-Real.log p)+atom u)*(atom (u+Real.log k-Real.log p)+atom (u+Real.log k)) = 0 := by
    rw [add_mul,mul_add,mul_add,h₁,h₂,h₃,h₄]
    norm_num
  calc _ = (m : ℝ)^2*((atom (u-Real.log p)+atom u)*(atom (u+Real.log k-Real.log p)+atom (u+Real.log k)))/j := by ring
    _ = 0 := by rw [hz,mul_zero,zero_div]

/-- At separated conductors the entire p-adic valuation of the actual
integer modulus is the aligned row, at every multiplicity. -/
theorem factorization_contactModulus_at_conductor {p : ℕ} (hp : p.Prime) (h : 8 < Real.log p)
    (m : ℕ) : (contactModulus (m • primePair p)).factorization p = alignedExponent p m := by
  let g (k : ℕ) := ⌊contactMultiplicity (packet (m • primePair p)) (pairEnd p) (resolution (m • primePair p)) k⌋₊
  let S := Icc 2 (pairEnd p)
  change (∏ k ∈ S, contactBase k ^ g k).factorization p = g p
  rw [Nat.factorization_prod (fun k _ => pow_ne_zero _ (contactBase_pos k).ne'), Finsupp.finsetSum_apply]
  have hpS : p ∈ S := mem_Icc.mpr ⟨hp.two_le,(pairEnd_bounds p).1⟩
  rw [sum_eq_single_of_mem p hpS]
  · rw [contactBase, if_pos hp.isPrimePow, hp.minFac_eq, Nat.factorization_pow_self hp]
  · intro k _ hkp
    by_cases hpp : IsPrimePow k
    · obtain ⟨q,r,hq,hr,rfl⟩ := (isPrimePow_nat_iff k).mp hpp
      have hb : contactBase (q^r) = q := by rw [contactBase,if_pos hpp,hq.pow_minFac hr.ne']
      rw [hb]
      by_cases he : q = p
      · subst q
        have hr₂ : 2 ≤ r := by
          by_contra! hr'
          have hr₁ : r = 1 := by omega
          exact hkp (by rw [hr₁,pow_one])
        have hshift : 8+Real.log p < Real.log ((p^r : ℕ) : ℝ) := by
          rw [Nat.cast_pow,Real.log_pow]
          have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr₂
          linarith only [h, mul_le_mul_of_nonneg_right hr' (Real.log_natCast_nonneg p)]
        have hz : g (p^r) = 0 := by
          simp only [g,separated_row_zero hp (pow_pos hp.pos _) hshift,Nat.floor_zero]
        simp only [hz,pow_zero,Nat.factorization_one,Finsupp.zero_apply]
      · simp [Nat.factorization_pow,hq.factorization,Finsupp.single_apply,he,Ne.symm he]
    · simp [contactBase,hpp]

theorem conductor_valuation_tateLimit {p : ℕ} (hp : p.Prime) (h : 8 < Real.log p) :
    Tendsto (fun m : ℕ => ((contactModulus (m • primePair p)).factorization p : ℝ)/(m : ℝ)^2)
      atTop (𝓝 (2/Real.sqrt p * (∫ u, cubicSpline u^2))) := by
  simpa only [factorization_contactModulus_at_conductor hp h] using alignedExponent_tateLimit hp h

/-- On each prime pair, paying even its single aligned residue condition
requires positive quadratic logarithmic size from any nonzero integral section. -/
theorem quadratic_cost_of_aligned_contact {p : ℕ} (hp : p.Prime) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop, ∀ z : ℕ, 0 < z →
      contactModulus (m • primePair p) ∣ z → c*(m : ℝ)^2 < Real.log z := by
  have hmass := AdelicKreinGeometry.TowerCoupling.integral_cubicSpline_sq_pos
  have hrow := (mul_pos (div_pos two_pos (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hp.pos))) hmass).trans_le
    (integratedPrimeRow_bound hp)
  have hp' : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨(integratedPrimeRow p/2)*Real.log p,mul_pos (half_pos hrow) hp',?_⟩
  filter_upwards [(tendsto_alignedExponent hp).eventually_const_lt (half_lt_self hrow),
    eventually_ge_atTop 1] with m hm hm1
  intro z hz hdiv
  have he := (lt_div_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp hm
  have hle := Nat.le_of_dvd hz ((aligned_dvd hp m).trans hdiv)
  have hl := Real.log_le_log (Nat.cast_pos.mpr (pow_pos hp.pos _)) (Nat.cast_le.mpr hle)
  rw [Nat.cast_pow,Real.log_pow] at hl
  linarith only [mul_lt_mul_of_pos_right he hp',hl]

#print axioms conductor_valuation_tateLimit
#print axioms alignedExponent_tateLimit
#print axioms quadratic_cost_of_aligned_contact

end GaloisForLFunctions.CountingHolography.Sections
