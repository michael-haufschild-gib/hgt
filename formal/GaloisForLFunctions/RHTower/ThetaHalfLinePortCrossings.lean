import GaloisForLFunctions.RHTower.ThetaHalfLinePortOrientation
import GaloisForLFunctions.HTGeometry.RealZeroCrossingCount
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureBoundaryCapacity
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Alternating crossings of the real Xi function and the half-line port orientation

At every real point `Ξ(t) = (t - ζ)^m g(t)` near `ζ`, where `m` is the analytic order of `ΞC` at
`ζ`, `g` is continuous and `g(ζ) ≠ 0` (the local analytic factor is real on the real axis).  Hence
a zero is simple exactly when `Ξ'` does not vanish there, and between two simple up-crossings there
is a zero of odd order at which `Ξ` passes from positive to negative values: a simple down-crossing
or a critical zero of odd order at least three.  Separation counting gives
`|U(T) - V(T)| ≤ A(T) + 1` for the simple up/down-crossing counts `U, V` and the odd higher count
`A`, with `U + V = S` (simple critical zeros) and `S + 3A ≤ N` (all zeros with multiplicity).
Therefore `min(U, V) ≥ (4S - N)/6 - 1/2`, and the two-thirds theorem `S ≥ (2/3 - ε)N` gives
`U, V ≥ (5/18 - ε)N` eventually.  At simple crossings the normal derivative law of the port
imbalance has both signs, so neither `D > 0` nor `D < 0` holds throughout the right collar,
arbitrarily high and arbitrarily close to the critical boundary.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Local factorization of the real Xi function -/

theorem continuous_Xi' : Continuous Xi :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_Xi_thetaHalfLaplace t).continuousAt

theorem hasDerivAt_Xi_deriv (t : ℝ) : HasDerivAt Xi (deriv Xi t) t :=
  (hasDerivAt_Xi_thetaHalfLaplace t).differentiableAt.hasDerivAt

/-- The order of the real Xi function at `t`: the analytic order of `ΞC` at `t`. -/
def xiRealOrder (t : ℝ) : ℕ := (analyticOrderAt XiC (t : ℂ)).toNat

theorem exists_Xi_localZeroFactor (ζ : ℝ) : ∃ g, HasLocalZeroFactor Xi ζ (xiRealOrder ζ) g := by
  have hA : AnalyticAt ℂ XiC (ζ : ℂ) := XiC_differentiable.analyticAt _
  have hne := XiC_order_ne_top (ζ : ℂ)
  obtain ⟨G, hG, hG0, hGeq⟩ := (hA.analyticOrderAt_eq_natCast (n := xiRealOrder ζ)).mp (by
    rw [xiRealOrder, ENat.coe_toNat hne])
  have hreal : ∀ᶠ t : ℝ in 𝓝 ζ, XiC (t : ℂ) = ((t : ℂ) - ζ) ^ xiRealOrder ζ • G t :=
    (Complex.continuous_ofReal.tendsto ζ).eventually hGeq
  have hGc : ContinuousAt (fun t : ℝ => G (t : ℂ)) ζ :=
    hG.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hpow : ∀ t : ℝ, ((t : ℂ) - ζ) ^ xiRealOrder ζ = (((t - ζ) ^ xiRealOrder ζ : ℝ) : ℂ) := by
    intro t; push_cast; ring
  have him : (G ζ).im = 0 := by
    have hlim : Tendsto (fun t : ℝ => (G t).im) (𝓝[≠] ζ) (𝓝 (G ζ).im) :=
      (Complex.continuous_im.continuousAt.tendsto.comp hGc).mono_left nhdsWithin_le_nhds
    have h0 : ∀ᶠ t : ℝ in 𝓝[≠] ζ, (G (t : ℂ)).im = 0 := by
      filter_upwards [nhdsWithin_le_nhds hreal, self_mem_nhdsWithin] with t ht htne
      have hX : (XiC (t : ℂ)).im = 0 := by rw [XiC_ofReal, Complex.ofReal_im]
      rw [ht, smul_eq_mul, hpow, Complex.im_ofReal_mul] at hX
      exact (mul_eq_zero.mp hX).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr htne))
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (h0.mono fun t ht => ht.symm))
  refine ⟨fun t => (G t).re, Complex.continuous_re.continuousAt.comp hGc, ?_, ?_⟩
  · intro h; apply hG0; exact Complex.ext h him
  · filter_upwards [hreal] with t ht
    have := congrArg Complex.re ht
    rw [XiC_ofReal, Complex.ofReal_re, smul_eq_mul, hpow, Complex.re_ofReal_mul] at this
    exact this

/-- A zero of `Ξ` has order one exactly when `Ξ'` does not vanish there. -/
theorem xiRealOrder_eq_one_iff {ζ : ℝ} (h0 : Xi ζ = 0) : xiRealOrder ζ = 1 ↔ deriv Xi ζ ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_Xi_localZeroFactor ζ
  constructor
  · intro h1
    rw [h1] at hg
    rw [(hg.hasDerivAt_one).deriv]; exact hg.2.1
  · intro hd
    exact (hg.eq_one_of_hasDerivAt h0 (hasDerivAt_Xi_deriv ζ) hd).1

/-! ## Critical zeros and their real ordinates -/

theorem Xi_im_eq_zero_of_mem {T : ℝ} {z : ℂ} (hz : z ∈ stripFinsetPos T) (hre : z.re = 1 / 2) :
    Xi z.im = 0 := by
  have h := XiC_ofReal_im_eq_xi_of_re_eq_half hre
  rw [XiC_ofReal, (mem_stripFinsetPos.mp hz).2.2.2.2] at h
  exact_mod_cast h

theorem xiRealOrder_im_eq {z : ℂ} (hre : z.re = 1 / 2) :
    xiRealOrder z.im = (analyticOrderAt xi z).toNat := by
  rw [xiRealOrder, analyticOrderAt_XiC_ofReal_im_eq_xi_of_re_eq_half hre]

/-- The critical point with ordinate `ζ`. -/
def criticalPoint (ζ : ℝ) : ℂ := ⟨1 / 2, ζ⟩

theorem criticalPoint_mem {T ζ : ℝ} (h0 : 0 < ζ) (hT : ζ ≤ T) (hX : Xi ζ = 0) :
    criticalPoint ζ ∈ stripFinsetPos T := by
  have hxi : xi (criticalPoint ζ) = 0 := by
    have h := XiC_ofReal_im_eq_xi_of_re_eq_half (z := criticalPoint ζ) rfl
    rw [← h, show (criticalPoint ζ).im = ζ from rfl, XiC_ofReal, hX, Complex.ofReal_zero]
  exact mem_stripFinsetPos.mpr ⟨by simp [criticalPoint], by simp [criticalPoint]; norm_num, h0, hT,
    hxi⟩

theorem im_injOn_critical (s : Finset ℂ) :
    Set.InjOn Complex.im ((s.filter fun z => z.re = 1 / 2 ∧ True) : Set ℂ) := by
  intro z hz w hw h
  have h1 := (Finset.mem_filter.mp hz).2.1
  have h2 := (Finset.mem_filter.mp hw).2.1
  exact Complex.ext (h1.trans h2.symm) h

/-- `U(T)`: simple critical up-crossings with ordinate in `(0, T]`. -/
def xiSimpleUpCrossingCount (T : ℝ) : ℕ :=
  ((stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ 0 < deriv Xi z.im).card

/-- `V(T)`: simple critical down-crossings with ordinate in `(0, T]`. -/
def xiSimpleDownCrossingCount (T : ℝ) : ℕ :=
  ((stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ deriv Xi z.im < 0).card

/-- `A(T)`: non-simple odd-order critical zeros with ordinate in `(0, T]`. -/
def xiOddHigherCriticalCount (T : ℝ) : ℕ :=
  ((stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ 3 ≤ (analyticOrderAt xi z).toNat ∧ Odd (analyticOrderAt xi z).toNat).card

/-- `U + V = S`. -/
theorem xiSimpleUp_add_down (T : ℝ) :
    xiSimpleUpCrossingCount T + xiSimpleDownCrossingCount T = xiSimpleCriticalZeroCount T := by
  classical
  set F := (stripFinsetPos T).filter fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1
  have hU : xiSimpleUpCrossingCount T = (F.filter fun z => 0 < deriv Xi z.im).card := by
    rw [xiSimpleUpCrossingCount, Finset.filter_filter]; simp only [and_assoc]
  have hV : xiSimpleDownCrossingCount T = (F.filter fun z => ¬ 0 < deriv Xi z.im).card := by
    rw [xiSimpleDownCrossingCount, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun z hz => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, not_lt.mpr h3.le⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hX := Xi_im_eq_zero_of_mem hz h1
      have hd : deriv Xi z.im ≠ 0 := (xiRealOrder_eq_one_iff hX).mp (by rw [xiRealOrder_im_eq h1, h2])
      exact ⟨h1, h2, lt_of_le_of_ne (not_lt.mp h3) hd⟩
  rw [hU, hV, Finset.card_filter_add_card_filter_not]
  rfl

/-- `S + 3A ≤ N`. -/
theorem xiSimpleCritical_add_three_mul_oddHigher_le (T : ℝ) :
    xiSimpleCriticalZeroCount T + 3 * xiOddHigherCriticalCount T ≤ xiPosZeroCount T := by
  classical
  set Sf := (stripFinsetPos T).filter fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1
  set Af := (stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ 3 ≤ (analyticOrderAt xi z).toNat ∧ Odd (analyticOrderAt xi z).toNat
  have hdisj : Disjoint Sf Af := by
    rw [Finset.disjoint_filter]; intro z _ h1 h2; omega
  have hsub : Sf ∪ Af ⊆ stripFinsetPos T :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun z => (analyticOrderAt xi z).toNat) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_union hdisj] at hsum
  have hS : Sf.card ≤ ∑ z ∈ Sf, (analyticOrderAt xi z).toNat := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun z hz => le_of_eq (Finset.mem_filter.mp hz).2.2.symm
  have hA : 3 * Af.card ≤ ∑ z ∈ Af, (analyticOrderAt xi z).toNat := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_le_sum fun z hz => by simpa using (Finset.mem_filter.mp hz).2.2.1
  have e1 : xiSimpleCriticalZeroCount T = Sf.card := rfl
  have e2 : xiOddHigherCriticalCount T = Af.card := rfl
  have e3 : xiPosZeroCount T = ∑ z ∈ stripFinsetPos T, (analyticOrderAt xi z).toNat := rfl
  rw [e1, e2, e3]
  omega

/-! ## Alternation of crossings -/

theorem card_image_im_of_critical {s : Finset ℂ} (h : ∀ z ∈ s, z.re = 1 / 2) :
    (s.image Complex.im).card = s.card :=
  Finset.card_image_of_injOn fun z hz w hw hzw =>
    Complex.ext ((h z hz).trans (h w hw).symm) hzw

/-- A down-crossing zero of odd order between two simple up-crossings is a simple down-crossing
or an odd higher critical zero. -/
theorem xi_crossing_separation {T : ℝ} (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) {u u' : ℝ} (huu' : u < u')
    (hu0 : 0 < u) (hu'T : u' ≤ T) (hXu : Xi u = 0) (hXu' : Xi u' = 0)
    (hdu : 0 < σ * deriv Xi u) (hdu' : 0 < σ * deriv Xi u') :
    ∃ ζ ∈ Ioo u u', criticalPoint ζ ∈ (stripFinsetPos T).filter (fun z =>
      z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ σ * deriv Xi z.im < 0) ∪
      (stripFinsetPos T).filter (fun z => z.re = 1 / 2 ∧ 3 ≤ (analyticOrderAt xi z).toNat ∧
        Odd (analyticOrderAt xi z).toNat) := by
  set f : ℝ → ℝ := fun t => σ * Xi t with hf
  have hfc : Continuous f := continuous_const.mul continuous_Xi'
  have hfac : ∀ ζ, ∃ g, HasLocalZeroFactor f ζ (xiRealOrder ζ) g := by
    intro ζ
    obtain ⟨g, hg⟩ := exists_Xi_localZeroFactor ζ
    refine ⟨fun t => σ * g t, hg.1.const_mul σ, ?_, hg.2.2.mono fun t ht => ?_⟩
    · rcases hσ with h | h <;> simp [h, hg.2.1]
    · simp only [hf]; rw [ht]; ring
  have hder : ∀ t, HasDerivAt f (σ * deriv Xi t) t := fun t => (hasDerivAt_Xi_deriv t).const_mul σ
  obtain ⟨ζ, hζ, hfζ, hodd, g, hg, hgneg⟩ := exists_down_crossing_between hfc xiRealOrder hfac
    huu' (by simp [hf, hXu]) (hder u) hdu (by simp [hf, hXu']) (hder u') hdu'
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  have hXζ : Xi ζ = 0 := by
    have : σ * Xi ζ = 0 := hfζ
    exact (mul_eq_zero.mp this).resolve_left hσ0
  have hmem := criticalPoint_mem (lt_trans hu0 hζ.1) (le_trans hζ.2.le hu'T) hXζ
  have hre : (criticalPoint ζ).re = 1 / 2 := rfl
  have him : (criticalPoint ζ).im = ζ := rfl
  have hord : (analyticOrderAt xi (criticalPoint ζ)).toNat = xiRealOrder ζ := by
    rw [← xiRealOrder_im_eq hre, him]
  refine ⟨ζ, hζ, ?_⟩
  rcases eq_or_ne (xiRealOrder ζ) 1 with h1 | h1
  · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, hre, by rw [hord, h1], ?_⟩)
    rw [h1] at hg
    have hd := (hg.hasDerivAt_one).unique (hder ζ)
    rw [him, ← hd]; exact hgneg
  · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, hre, ?_, by rw [hord]; exact hodd⟩)
    rw [hord]
    obtain ⟨k, hk⟩ := hodd
    omega

theorem xiSimpleCrossing_le_aux {T : ℝ} (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ((stripFinsetPos T).filter fun z =>
        z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ 0 < σ * deriv Xi z.im).card ≤
      ((stripFinsetPos T).filter fun z =>
        z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ σ * deriv Xi z.im < 0).card +
        xiOddHigherCriticalCount T + 1 := by
  classical
  set Uf := (stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ 0 < σ * deriv Xi z.im
  set Vf := (stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ σ * deriv Xi z.im < 0
  set Af := (stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ 3 ≤ (analyticOrderAt xi z).toNat ∧ Odd (analyticOrderAt xi z).toNat
  have hUc : (Uf.image Complex.im).card = Uf.card :=
    card_image_im_of_critical fun z hz => (Finset.mem_filter.mp hz).2.1
  have hsep := card_le_card_add_one_of_separated (Uf.image Complex.im) ((Vf ∪ Af).image Complex.im)
    (by
      intro u hu u' hu' huu'
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hu'
      have hzs := (Finset.mem_filter.mp hz).1
      have hzs' := (Finset.mem_filter.mp hz').1
      obtain ⟨ζ, hζ, hmem⟩ := xi_crossing_separation σ hσ huu' (mem_stripFinsetPos.mp hzs).2.2.1
        (mem_stripFinsetPos.mp hzs').2.2.2.1 (Xi_im_eq_zero_of_mem hzs (Finset.mem_filter.mp hz).2.1)
        (Xi_im_eq_zero_of_mem hzs' (Finset.mem_filter.mp hz').2.1) (Finset.mem_filter.mp hz).2.2.2
        (Finset.mem_filter.mp hz').2.2.2
      exact ⟨ζ, Finset.mem_image.mpr ⟨criticalPoint ζ, hmem, rfl⟩, hζ.1, hζ.2⟩)
  have hW : ((Vf ∪ Af).image Complex.im).card ≤ Vf.card + Af.card :=
    Finset.card_image_le.trans (Finset.card_union_le _ _)
  have e : xiOddHigherCriticalCount T = Af.card := rfl
  rw [hUc] at hsep
  rw [e]
  omega

/-- **Alternation (5).** `U ≤ V + A + 1` and `V ≤ U + A + 1`. -/
theorem xiSimpleUp_le (T : ℝ) :
    xiSimpleUpCrossingCount T ≤ xiSimpleDownCrossingCount T + xiOddHigherCriticalCount T + 1 := by
  have h := xiSimpleCrossing_le_aux (T := T) 1 (Or.inl rfl)
  simp only [one_mul] at h
  exact h

theorem xiSimpleDown_le (T : ℝ) :
    xiSimpleDownCrossingCount T ≤ xiSimpleUpCrossingCount T + xiOddHigherCriticalCount T + 1 := by
  have h := xiSimpleCrossing_le_aux (T := T) (-1) (Or.inr rfl)
  simp only [neg_one_mul, neg_pos, neg_lt_zero] at h
  exact h

/-- **Quantitative split (6).** `min(U, V) ≥ (4S - N)/6 - 1/2`. -/
theorem xiSimpleUp_ge (T : ℝ) :
    (4 * (xiSimpleCriticalZeroCount T : ℝ) - xiPosZeroCount T) / 6 - 1 / 2 ≤
      xiSimpleUpCrossingCount T := by
  have h1 := xiSimpleUp_add_down T
  have h2 := xiSimpleDown_le T
  have h3 := xiSimpleCritical_add_three_mul_oddHigher_le T
  have h1' : (xiSimpleUpCrossingCount T : ℝ) + xiSimpleDownCrossingCount T =
      xiSimpleCriticalZeroCount T := by exact_mod_cast h1
  have h2' : (xiSimpleDownCrossingCount T : ℝ) ≤
      xiSimpleUpCrossingCount T + xiOddHigherCriticalCount T + 1 := by exact_mod_cast h2
  have h3' : (xiSimpleCriticalZeroCount T : ℝ) + 3 * xiOddHigherCriticalCount T ≤
      xiPosZeroCount T := by exact_mod_cast h3
  linarith

theorem xiSimpleDown_ge (T : ℝ) :
    (4 * (xiSimpleCriticalZeroCount T : ℝ) - xiPosZeroCount T) / 6 - 1 / 2 ≤
      xiSimpleDownCrossingCount T := by
  have h1 := xiSimpleUp_add_down T
  have h2 := xiSimpleUp_le T
  have h3 := xiSimpleCritical_add_three_mul_oddHigher_le T
  have h1' : (xiSimpleUpCrossingCount T : ℝ) + xiSimpleDownCrossingCount T =
      xiSimpleCriticalZeroCount T := by exact_mod_cast h1
  have h2' : (xiSimpleUpCrossingCount T : ℝ) ≤
      xiSimpleDownCrossingCount T + xiOddHigherCriticalCount T + 1 := by exact_mod_cast h2
  have h3' : (xiSimpleCriticalZeroCount T : ℝ) + 3 * xiOddHigherCriticalCount T ≤
      xiPosZeroCount T := by exact_mod_cast h3
  linarith

/-! ## Densities of both crossing directions (7) -/

theorem xiSimpleCritical_le_xiPosZeroCount (T : ℝ) :
    xiSimpleCriticalZeroCount T ≤ xiPosZeroCount T := by
  have := xiSimpleCritical_add_three_mul_oddHigher_le T; omega

theorem tendsto_xiPosZeroCount_atTop : Tendsto (fun T => (xiPosZeroCount T : ℝ)) atTop atTop := by
  have hTlog : Tendsto (fun T : ℝ => 1 / (72 * Real.pi) * T * Real.log T) atTop atTop := by
    have := (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).const_mul_atTop
      (show (0 : ℝ) < 1 / (72 * Real.pi) by positivity)
    exact this.congr fun T => by simp only [id]; ring
  refine tendsto_atTop_mono' atTop ?_ hTlog
  filter_upwards [eventually_superlinear_xiSimpleCriticalZeroCount] with T hT
  exact hT.trans (by exact_mod_cast xiSimpleCritical_le_xiPosZeroCount T)

/-- **Crossing densities (7).** For every `ε > 0`, eventually `U(T) ≥ (5/18 - ε) N(T)`. -/
theorem eventually_xiSimpleUp_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (5 / 18 - ε) * (xiPosZeroCount T : ℝ) ≤ xiSimpleUpCrossingCount T := by
  obtain ⟨T₀, hT₀⟩ := two_thirds_simpleCritical_epsilon ε hε
  filter_upwards [eventually_ge_atTop T₀,
    tendsto_xiPosZeroCount_atTop.eventually_ge_atTop (3 / (2 * ε))] with T hT hN
  have h1 := hT₀ T hT
  have h2 := xiSimpleUp_ge T
  have h3 : ε / 3 * (xiPosZeroCount T : ℝ) ≥ 1 / 2 := by
    rw [ge_iff_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul_of_nonneg_left hN (show 0 ≤ ε / 3 by positivity)
    rw [show ε / 3 * (3 / (2 * ε)) = 1 / 2 by field_simp] at this
    linarith
  nlinarith

/-- **Crossing densities (7).** For every `ε > 0`, eventually `V(T) ≥ (5/18 - ε) N(T)`. -/
theorem eventually_xiSimpleDown_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (5 / 18 - ε) * (xiPosZeroCount T : ℝ) ≤ xiSimpleDownCrossingCount T := by
  obtain ⟨T₀, hT₀⟩ := two_thirds_simpleCritical_epsilon ε hε
  filter_upwards [eventually_ge_atTop T₀,
    tendsto_xiPosZeroCount_atTop.eventually_ge_atTop (3 / (2 * ε))] with T hT hN
  have h1 := hT₀ T hT
  have h2 := xiSimpleDown_ge T
  have h3 : ε / 3 * (xiPosZeroCount T : ℝ) ≥ 1 / 2 := by
    rw [ge_iff_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul_of_nonneg_left hN (show 0 ≤ ε / 3 by positivity)
    rw [show ε / 3 * (3 / (2 * ε)) = 1 / 2 by field_simp] at this
    linarith
  nlinarith

theorem mem_stripFinsetPos_of_im_le {T T' : ℝ} {z : ℂ} (hz : z ∈ stripFinsetPos T') (hzT : z.im ≤ T) :
    z ∈ stripFinsetPos T := by
  obtain ⟨h1, h2, h3, _, h5⟩ := mem_stripFinsetPos.mp hz
  exact mem_stripFinsetPos.mpr ⟨h1, h2, h3, hzT, h5⟩

theorem exists_simpleCrossing_above (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (Γ : ℝ) :
    ∃ γ > Γ, Xi γ = 0 ∧ 0 < σ * deriv Xi γ := by
  classical
  set F : ℝ → Finset ℂ := fun T => (stripFinsetPos T).filter fun z =>
    z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 ∧ 0 < σ * deriv Xi z.im
  have hlarge : ∀ᶠ T in atTop, ((F Γ).card : ℝ) < (F T).card := by
    have hN := tendsto_xiPosZeroCount_atTop.eventually_gt_atTop (9 / 2 * ((F Γ).card : ℝ))
    rcases hσ with rfl | rfl
    · filter_upwards [eventually_xiSimpleUp_ge (ε := 1 / 18) (by norm_num), hN] with T h1 h2
      have e : (F T).card = xiSimpleUpCrossingCount T := by
        simp only [F, one_mul]; rfl
      rw [e]; nlinarith
    · filter_upwards [eventually_xiSimpleDown_ge (ε := 1 / 18) (by norm_num), hN] with T h1 h2
      have e : (F T).card = xiSimpleDownCrossingCount T := by
        simp only [F, neg_one_mul, neg_pos]; rfl
      rw [e]; nlinarith
  obtain ⟨T, hT⟩ := hlarge.exists
  obtain ⟨z, hzT, hzΓ⟩ := Finset.exists_mem_notMem_of_card_lt_card (by exact_mod_cast hT)
  obtain ⟨hzs, hre, hord, hd⟩ := Finset.mem_filter.mp hzT
  refine ⟨z.im, ?_, Xi_im_eq_zero_of_mem hzs hre, hd⟩
  by_contra hle
  exact hzΓ (Finset.mem_filter.mpr ⟨mem_stripFinsetPos_of_im_le hzs (not_lt.mp hle), hre, hord, hd⟩)

theorem exists_pos_of_hasDerivAt_pos {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (hd : 0 < d)
    (h0 : f 0 = 0) {ε : ℝ} (hε : 0 < ε) : ∃ α ∈ Ioo 0 ε, 0 < f α := by
  rw [hasDerivAt_iff_tendsto_slope] at hf
  have hlim := hf.mono_left (nhdsGT_le_nhdsNE 0)
  obtain ⟨α, hα1, hα2⟩ := ((hlim.eventually (lt_mem_nhds hd)).and (Ioo_mem_nhdsGT hε)).exists
  refine ⟨α, hα2, ?_⟩
  rw [slope_def_field, h0, sub_zero, sub_zero] at hα1
  exact (div_pos_iff_of_pos_right hα2.1).mp hα1

/-- **No fixed orientation.** Arbitrarily high and arbitrarily close to the critical boundary the
one-port imbalance takes positive values. -/
theorem exists_thetaHalfPortImbalance_pos (Γ ε : ℝ) (hε : 0 < ε) :
    ∃ γ > Γ, ∃ α ∈ Ioo 0 ε, 0 < thetaHalfPortImbalance γ α := by
  obtain ⟨γ, hγ, hX, hd⟩ := exists_simpleCrossing_above (-1) (Or.inr rfl) (max Γ 0)
  have hγ0 : 0 < γ := lt_of_le_of_lt (le_max_right _ _) hγ
  have hb := thetaHalfSineResponse_pos hγ0
  obtain ⟨α, hα, hpos⟩ := exists_pos_of_hasDerivAt_pos (hasDerivAt_thetaHalfPortImbalance hX)
    (by nlinarith) (thetaHalfPortImbalance_zero γ) hε
  exact ⟨γ, lt_of_le_of_lt (le_max_left _ _) hγ, α, hα, hpos⟩

/-- **No fixed orientation.** Arbitrarily high and arbitrarily close to the critical boundary the
one-port imbalance takes negative values. -/
theorem exists_thetaHalfPortImbalance_neg (Γ ε : ℝ) (hε : 0 < ε) :
    ∃ γ > Γ, ∃ α ∈ Ioo 0 ε, thetaHalfPortImbalance γ α < 0 := by
  obtain ⟨γ, hγ, hX, hd⟩ := exists_simpleCrossing_above 1 (Or.inl rfl) (max Γ 0)
  have hγ0 : 0 < γ := lt_of_le_of_lt (le_max_right _ _) hγ
  have hb := thetaHalfSineResponse_pos hγ0
  obtain ⟨α, hα, hpos⟩ := exists_pos_of_hasDerivAt_pos
    (hasDerivAt_thetaHalfPortImbalance hX).neg (by nlinarith)
    (by simp [thetaHalfPortImbalance_zero]) hε
  exact ⟨γ, lt_of_le_of_lt (le_max_left _ _) hγ, α, hα, by simpa using hpos⟩

end RHTower
