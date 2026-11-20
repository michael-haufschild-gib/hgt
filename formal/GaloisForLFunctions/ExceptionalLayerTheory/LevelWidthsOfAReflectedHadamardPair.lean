import GaloisForLFunctions.RHTower.XiHadamardPairSignLaw

/-!
# Level widths of a reflected Hadamard pair

Boudjemâa (arXiv:2611.21911, equations 14–15) obtains a Jeans cutoff by
solving a quadratic in squared wave number. For a line-conjugate pair of
resolvents the height below a prescribed negative level satisfies a
quadratic in squared ordinate displacement. Its positive root gives the
full chord. Zooming in at one pole also gives the finite contribution
of its reflected partner.
-/

noncomputable section
open Complex Filter Topology
open scoped NNReal
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Real part of the two resolvents in centred coordinates. -/
def reflectedPairReading (x δ y : ℝ) :=
  (x-δ)/((x-δ)^2+y^2)+(x+δ)/((x+δ)^2+y^2)

private def linearCoeff (L x δ : ℝ) := 2*L*(x^2+δ^2)+2*x
private def levelMass (L x δ : ℝ) := (δ^2-x^2)*(2*x-L*(δ^2-x^2))

/-- Squared half-width of the chord inside level −L. A negative
algebraic root gives an empty chord. -/
def reflectedPairWidthSq (L x δ : ℝ) :=
  (Real.sqrt (linearCoeff L x δ^2+4*L*levelMass L x δ)-linearCoeff L x δ)/(2*L)

private theorem pair_quartic {L x δ : ℝ} (hx : 0<x) (hδ : x<δ) (y : ℝ) :
    reflectedPairReading x δ y < -L ↔
      L*(y^2)^2+linearCoeff L x δ*y^2 < levelMass L x δ := by
  have h₁ : 0<(x-δ)^2+y^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hδ.ne)) (sq_nonneg _)
  have h₂ : 0<(x+δ)^2+y^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_pos (add_pos hx (hx.trans hδ))) (sq_nonneg _)
  rw [reflectedPairReading, _root_.RHTower.hadamardPair_re_formula h₁.ne' h₂.ne',
    div_lt_iff₀ (mul_pos h₁ h₂)]
  unfold linearCoeff levelMass
  constructor <;> intro h <;> linarith only [h]

/-- An upward quadratic in a nonnegative squared frequency lies below
its prescribed level exactly before the larger algebraic root. -/
theorem positive_quadratic_cutoff {L b : ℝ} (hL : 0<L) (hb : 0≤b) (c : ℝ)
    {q : ℝ} (hq : 0≤q) :
    L*q^2+b*q<c ↔ q<(Real.sqrt (b^2+4*L*c)-b)/(2*L) := by
  have h2 : 0<2*L := by positivity
  have hleft : 0≤2*L*q+b := by positivity
  rw [lt_div_iff₀ h2]
  have he : (2*L*q+b)^2-(b^2+4*L*c) = (4*L)*(L*q^2+b*q-c) := by ring
  constructor
  · intro h
    have hn := mul_neg_of_pos_of_neg (show 0<4*L by positivity) (sub_neg.mpr h)
    have hs : (2*L*q+b)^2 < b^2+4*L*c := by linarith only [he,hn]
    have hd := (sq_nonneg _).trans hs.le
    rw [←Real.sq_sqrt hd] at hs
    have ht := (sq_lt_sq₀ hleft (Real.sqrt_nonneg _)).mp hs
    linarith only [ht]
  · intro h
    have ht : 2*L*q+b < Real.sqrt (b^2+4*L*c) := by linarith only [h]
    have hd : 0<b^2+4*L*c := Real.sqrt_pos.mp (hleft.trans_lt ht)
    have hs := (sq_lt_sq₀ hleft (Real.sqrt_nonneg _)).mpr ht
    rw [Real.sq_sqrt hd.le] at hs
    have hn : 4*L*(L*q^2+b*q-c)<0 := by linarith only [he,hs]
    apply sub_neg.mp
    apply (mul_lt_mul_iff_right₀ (show 0<4*L by positivity)).mp
    simpa only [mul_zero] using hn

/-- Dimensionless Jeans instability interval for every nonnegative
coupling, including zero coupling. The endpoints are neutral. -/
theorem jeans_instability_band (coupling : ℝ≥0) (k : ℝ) :
    0<1-(coupling:ℝ)*k^2-k^4 ↔
      |k|<Real.sqrt ((Real.sqrt ((coupling:ℝ)^2+4)-coupling)/2) := by
  have hcut := positive_quadratic_cutoff (L:=1) one_pos coupling.coe_nonneg 1 (sq_nonneg k)
  have hd : (coupling:ℝ)^2<(coupling:ℝ)^2+4 := by linarith
  have hdisc := (sq_nonneg (coupling:ℝ)).trans hd.le
  have hroot : (coupling:ℝ)<Real.sqrt ((coupling:ℝ)^2+4) := by
    apply (sq_lt_sq₀ coupling.coe_nonneg (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt hdisc]
  have hwidth : 0≤(Real.sqrt ((coupling:ℝ)^2+4)-coupling)/2 :=
    div_nonneg (sub_nonneg.mpr hroot.le) (by norm_num)
  rw [←sq_lt_sq₀ (abs_nonneg k) (Real.sqrt_nonneg _),sq_abs,Real.sq_sqrt hwidth]
  norm_num only [one_mul,mul_one] at hcut
  rw [←hcut]
  constructor <;> intro h <;> linarith only [h]

/-- Complete negative level set of a line-conjugate resolvent pair. -/
theorem reflected_pair_negative_level {L : ℝ} (hL : 0<L) (s ρ : ℂ)
    (hx : 1/2<s.re) (hδ : s.re<ρ.re) :
    ((s-ρ)⁻¹).re+((s-(1-(starRingEnd ℂ) ρ))⁻¹).re < -L ↔
      (s.im-ρ.im)^2 < reflectedPairWidthSq L (s.re-1/2) (ρ.re-1/2) := by
  rw [_root_.RHTower.re_inv_sub_eq,_root_.RHTower.re_inv_sub_lineConj_eq]
  let x := s.re-1/2
  let δ := ρ.re-1/2
  let y := s.im-ρ.im
  change reflectedPairReading x δ y < -L ↔ _
  have hx' : 0<x := sub_pos.mpr hx
  have hd' : x<δ := sub_lt_sub_right hδ _
  rw [pair_quartic hx' hd',reflectedPairWidthSq]
  let b := linearCoeff L x δ
  let c := levelMass L x δ
  change L*(y^2)^2+b*y^2<c ↔ y^2<(Real.sqrt (b^2+4*L*c)-b)/(2*L)
  have hb : 0<b := by dsimp only [b,linearCoeff]; positivity
  exact positive_quadratic_cutoff hL hb.le c (sq_nonneg y)

/-- A horizontal cut meets the negative level exactly when its
on-axis reading is below that level. -/
theorem reflected_pair_level_onset {L x δ : ℝ} (hL : 0<L) (hx : 0<x) (hδ : x<δ) :
    (∃ y : ℝ, reflectedPairReading x δ y < -L) ↔ L*(δ^2-x^2)<2*x := by
  have hd := sub_pos.mpr ((sq_lt_sq₀ hx.le (hx.trans hδ).le).mpr hδ)
  have hb : 0<linearCoeff L x δ := by unfold linearCoeff; positivity
  constructor
  · rintro ⟨y,hy⟩
    have hc := (pair_quartic hx hδ y).mp hy
    have hzero : 0≤L*(y^2)^2+linearCoeff L x δ*y^2 := by positivity
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hd).mp (hzero.trans_lt hc))
  · intro h
    refine ⟨0,(pair_quartic hx hδ 0).mpr ?_⟩
    simpa only [zero_pow (by decide : 2≠0),mul_zero,add_zero,levelMass] using
      mul_pos hd (sub_pos.mpr h)

/-- At scale t around the right pole the leading term is
−u/[t(u²+v²)]. Subtracting it recovers the reflected pole at distance 2δ. -/
theorem reflected_pair_finite_remainder {δ : ℝ} (hd : 0<δ) (u v : ℝ) :
    Tendsto (fun t : ℝ => reflectedPairReading (δ-t*u) δ (t*v) +
      u/(t*(u^2+v^2))) (𝓝[≠] 0) (𝓝 (1/(2*δ))) := by
  have hh : ContinuousAt (fun t : ℝ => (2*δ-t*u)/((2*δ-t*u)^2+(t*v)^2)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp only [zero_mul,sub_zero,zero_pow (by decide : 2≠0),add_zero]
      positivity
  have hlim := hh.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  have hv : (2*δ-0*u)/((2*δ-0*u)^2+(0*v)^2)=1/(2*δ) := by
    field_simp [hd.ne']
    ring
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t≠0 := ht
  rw [reflectedPairReading,show δ-t*u-δ= -(t*u) by ring,
    show δ-t*u+δ=2*δ-t*u by ring,
    show (-(t*u))^2+(t*v)^2=t^2*(u^2+v^2) by ring]
  by_cases h : u^2+v^2=0
  · simp only [h,mul_zero,div_zero,zero_add,add_zero]
  · have he : -(t*u)/(t^2*(u^2+v^2)) = -(u/(t*(u^2+v^2))) := by
      field_simp [ht',h]
    rw [he]; abel

#print axioms positive_quadratic_cutoff
#print axioms jeans_instability_band
#print axioms reflected_pair_negative_level
#print axioms reflected_pair_level_onset
#print axioms reflected_pair_finite_remainder
end GaloisForLFunctions.ExceptionalLayerTheory
