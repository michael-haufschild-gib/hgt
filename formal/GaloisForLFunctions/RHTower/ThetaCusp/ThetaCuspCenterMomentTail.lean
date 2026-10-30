import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailRepresentation

/-!
# The first-moment center tail of the signed theta hierarchy

With the first center moment kept in the tail, `V_k(r) = ∫_{s>r} s h_k(s/2) ds`, integration by
parts against `sinh(ar)` gives, at every order and every aperture `0 ≤ a < 1/2`,

`s_k(a) = a ∫_{r>0} cosh(ar) V_k(r) dr`.

The weight `s` vanishes at the self-dual seam. Unlike the unweighted tail, whose seam value is a
Plancherel square that vanishes at the zeros of `Φ̂`, this tail does not lose the seam boundary
flux at those zeros.
-/

open MeasureTheory Set Filter Topology Matrix
namespace RHTower
noncomputable section

private theorem integrableOn_mul_exp_neg_Ioi {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-s)) (Ioi r) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1)
    (by norm_num) le_rfl one_pos
  refine (hb.mono_set (Ioi_subset_Ioi hr)).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul, one_mul]

theorem integrableOn_mul_thetaCuspNativeSignedJet_half (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℝ => s * thetaCuspNativeSignedJet (s/2) k) (Ioi r) := by
  have hdom := (integrableOn_mul_exp_neg_Ioi hr).const_mul (thetaCuspNativeJetDecayConstant k)
  refine hdom.mono' ((continuous_id.mul (continuous_thetaCuspNativeSignedJet_half k)).aestronglyMeasurable)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := hr.trans (le_of_lt hs)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0]
  calc s * |thetaCuspNativeSignedJet (s/2) k|
      ≤ s * (thetaCuspNativeJetDecayConstant k * Real.exp (-s)) :=
        mul_le_mul_of_nonneg_left (abs_thetaCuspNativeSignedJet_half_le k hs0) hs0
    _ = _ := by ring

/-- The first-moment center tail of the order-`k` native signed jet. -/
def thetaCuspNativeSignedJetMomentTail (k : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Ioi r, s * thetaCuspNativeSignedJet (s/2) k

theorem abs_thetaCuspNativeSignedJetMomentTail_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    |thetaCuspNativeSignedJetMomentTail k r| ≤
      thetaCuspNativeJetDecayConstant k * ((r + 1) * Real.exp (-r)) := by
  set K := thetaCuspNativeJetDecayConstant k
  have hK := thetaCuspNativeJetDecayConstant_nonneg k
  have hf := integrableOn_mul_thetaCuspNativeSignedJet_half k hr
  have hg := (integrableOn_mul_exp_neg_Ioi hr).const_mul K
  have hval : (∫ s in Ioi r, s * Real.exp (-s)) = (r + 1) * Real.exp (-r) := by
    have hderiv : ∀ x ∈ Ici r, HasDerivAt (fun s => -(s + 1) * Real.exp (-s))
        (x * Real.exp (-x)) x := by
      intro x _
      have h2 : HasDerivAt (fun s : ℝ => -(s + 1) * Real.exp (-s))
          (-(1 : ℝ) * Real.exp (-x) + -(x + 1) * (Real.exp (-x) * -1)) x :=
        ((hasDerivAt_id' x).add_const 1).neg.mul
          ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id' x).neg)
      convert h2 using 1
      ring
    have hlim : Tendsto (fun s : ℝ => -(s + 1) * Real.exp (-s)) atTop (𝓝 0) := by
      have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos
      have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 1 one_pos
      have h := (h1.add h0).neg
      simp only [Real.rpow_one, Real.rpow_zero, one_mul, add_zero, neg_zero] at h
      refine h.congr fun s => ?_
      ring_nf
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_mul_exp_neg_Ioi hr) hlim]
    ring
  calc |thetaCuspNativeSignedJetMomentTail k r|
      ≤ ∫ s in Ioi r, |s * thetaCuspNativeSignedJet (s/2) k| := abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi r, K * (s * Real.exp (-s)) := by
        refine setIntegral_mono_on hf.abs hg measurableSet_Ioi fun s hs => ?_
        have hs0 : 0 ≤ s := hr.trans (le_of_lt hs)
        rw [abs_mul, abs_of_nonneg hs0]
        calc s * |thetaCuspNativeSignedJet (s/2) k|
            ≤ s * (K * Real.exp (-s)) :=
              mul_le_mul_of_nonneg_left (abs_thetaCuspNativeSignedJet_half_le k hs0) hs0
          _ = _ := by ring
    _ = _ := by rw [integral_const_mul, hval]

theorem hasDerivAt_thetaCuspNativeSignedJetMomentTail (k : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (thetaCuspNativeSignedJetMomentTail k)
      (-(r * thetaCuspNativeSignedJet (r/2) k)) r := by
  have hf : Continuous (fun s : ℝ => s * thetaCuspNativeSignedJet (s/2) k) :=
    continuous_id.mul (continuous_thetaCuspNativeSignedJet_half k)
  have hd : HasDerivAt (fun u => (∫ s in Ioi (0 : ℝ), s * thetaCuspNativeSignedJet (s/2) k) -
      ∫ s in (0 : ℝ)..u, s * thetaCuspNativeSignedJet (s/2) k)
      (-(r * thetaCuspNativeSignedJet (r/2) k)) r :=
    (hf.integral_hasStrictDerivAt 0 r).hasDerivAt.const_sub _
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hr] with u hu
  have h := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_mul_thetaCuspNativeSignedJet_half k le_rfl)
    (integrableOn_mul_thetaCuspNativeSignedJet_half k hu.le)
  unfold thetaCuspNativeSignedJetMomentTail
  linarith

/-- The `cosh`-weighted first-moment tail is integrable for every aperture below one. -/
theorem integrableOn_cosh_mul_thetaCuspNativeSignedJetMomentTail {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1) (k : ℕ) :
    IntegrableOn (fun r => Real.cosh (a*r) * thetaCuspNativeSignedJetMomentTail k r) (Ioi 0) := by
  set K := thetaCuspNativeJetDecayConstant k
  have hb : 0 < 1 - a := by linarith
  have h1 : IntegrableOn (fun r : ℝ => Real.exp (-(1-a) * r)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hb
  have h2 : IntegrableOn (fun r : ℝ => r * Real.exp (-(1-a) * r)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1-a)
      (by norm_num) le_rfl hb
    refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hcontV : ContinuousOn (thetaCuspNativeSignedJetMomentTail k) (Ioi 0) := fun r hr =>
    (hasDerivAt_thetaCuspNativeSignedJetMomentTail k hr).continuousAt.continuousWithinAt
  refine ((h2.add h1).const_mul K).mono'
    (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousOn.mul
      hcontV).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := le_of_lt hr
  have hV := abs_thetaCuspNativeSignedJetMomentTail_le k hr0
  have hc : Real.cosh (a*r) ≤ Real.exp (a*r) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(a*r)) ≤ Real.exp (a*r) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha0 hr0])
    linarith
  have hexp : Real.exp (a*r) * Real.exp (-r) = Real.exp (-(1-a) * r) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.cosh_pos _)]
  calc Real.cosh (a*r) * |thetaCuspNativeSignedJetMomentTail k r|
      ≤ Real.exp (a*r) * (K * ((r + 1) * Real.exp (-r))) :=
        mul_le_mul hc hV (abs_nonneg _) (Real.exp_pos _).le
    _ = K * (r * Real.exp (-(1-a) * r) + Real.exp (-(1-a) * r)) := by rw [← hexp]; ring

/-- **First-moment tail representation.** Every signed mixed jet is `a` times the `cosh`-weighted
integral of its aperture-free first-moment center tail. -/
theorem thetaCuspCenterMixedSignedJet_eq_integral_momentTail {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1/2) (k : ℕ) :
    thetaCuspCenterMixedSignedJet a k =
      a * ∫ r in Ioi 0, Real.cosh (a*r) * thetaCuspNativeSignedJetMomentTail k r := by
  rw [thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0 ha]
  set K := thetaCuspNativeJetDecayConstant k
  have hK := thetaCuspNativeJetDecayConstant_nonneg k
  have hb : 0 < 1 - a := by linarith
  let u : ℝ → ℝ := fun r => Real.sinh (a*r)
  let v := thetaCuspNativeSignedJetMomentTail k
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (a * Real.cosh (a*x)) x := by
    intro x _
    have h2 : HasDerivAt (fun y => Real.sinh (a*y)) (Real.cosh (a*x) * (a*1)) x :=
      (Real.hasDerivAt_sinh (a*x)).comp x ((hasDerivAt_id' x).const_mul a)
    convert h2 using 1
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (-(x * thetaCuspNativeSignedJet (x/2) k)) x :=
    fun x hx => hasDerivAt_thetaCuspNativeSignedJetMomentTail k hx
  have huv' : IntegrableOn (u * fun x => -(x * thetaCuspNativeSignedJet (x/2) k)) (Ioi 0) := by
    refine (integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha k).neg.congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    change -(x * Real.sinh (a*x) * thetaCuspNativeSignedJet (x/2) k) =
      Real.sinh (a*x) * -(x * thetaCuspNativeSignedJet (x/2) k)
    ring
  have hu'v : IntegrableOn ((fun x => a * Real.cosh (a*x)) * v) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_cosh_mul_thetaCuspNativeSignedJetMomentTail ha0 (by linarith) k).const_mul a)
      (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, v]
    ring
  have hcu : Continuous u := by fun_prop
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun x => (2 * K) * |u x|) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun x => (2 * K) * |u x|) := continuous_const.mul hcu.abs
      have h := hc.tendsto 0
      rw [show (2 * K) * |u 0| = 0 by simp [u]] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hV := abs_thetaCuspNativeSignedJetMomentTail_le k hx0
    have he : (x + 1) * Real.exp (-x) ≤ 2 := by
      have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [hx.2, Real.exp_pos (-x)]
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    have hVle : |v x| ≤ 2 * K := hV.trans (by nlinarith)
    nlinarith [abs_nonneg (u x), abs_nonneg (v x)]
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => K * (x ^ (1 : ℝ) * Real.exp (-(1-a) * x) +
        x ^ (0 : ℝ) * Real.exp (-(1-a) * x))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1-a) hb).add
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1-a) hb)).const_mul K
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with x hx0
    have hV := abs_thetaCuspNativeSignedJetMomentTail_le k hx0
    have hs : |Real.sinh (a*x)| ≤ Real.exp (a*x) := by
      rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hx0)), Real.sinh_eq]
      linarith [Real.exp_pos (a*x), Real.exp_pos (-(a*x))]
    have hexp : Real.exp (a*x) * Real.exp (-x) = Real.exp (-(1-a) * x) := by
      rw [← Real.exp_add]; ring_nf
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, Real.rpow_one, Real.rpow_zero]
    calc |u x| * |v x| ≤ Real.exp (a*x) * (K * ((x + 1) * Real.exp (-x))) :=
          mul_le_mul hs hV (abs_nonneg _) (Real.exp_pos _).le
      _ = K * (x * Real.exp (-(1-a) * x) + 1 * Real.exp (-(1-a) * x)) := by rw [← hexp]; ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
  have hneg : (∫ x in Ioi (0 : ℝ), u x * -(x * thetaCuspNativeSignedJet (x/2) k)) =
      -∫ x in Ioi (0 : ℝ), x * Real.sinh (a*x) * thetaCuspNativeSignedJet (x/2) k := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [u]
    ring
  have hpull : (∫ x in Ioi (0 : ℝ), a * Real.cosh (a*x) * v x) =
      a * ∫ x in Ioi (0 : ℝ), Real.cosh (a*x) * v x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  rw [hneg, hpull] at hibp
  linarith

/-- The finite first-moment tail Hankel form at one center. -/
def thetaCuspNativeMomentTailHankelForm {N : ℕ} (r : ℝ) (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i * v j * thetaCuspNativeSignedJetMomentTail (i.val + j.val) r

/-- **First-moment tail certificate.** Nonnegative first-moment tail forms at every positive
center give the size-`N` signed section at every critical aperture. -/
theorem thetaCuspCenterMixedSignedHankel_posSemidef_of_momentTail {N : ℕ}
    (htail : ∀ r : ℝ, 0 < r → ∀ v : Fin N → ℝ, 0 ≤ thetaCuspNativeMomentTailHankelForm r v)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a N).PosSemidef := by
  have hHerm : (thetaCuspCenterMixedSignedHankel a N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspCenterMixedSignedHankel, add_comm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
  have hint (i j : Fin N) : IntegrableOn (fun r => Real.cosh (a*r) *
      thetaCuspNativeSignedJetMomentTail (i.val + j.val) r) (Ioi 0) :=
    integrableOn_cosh_mul_thetaCuspNativeSignedJetMomentTail ha0 (by linarith) _
  have hform : star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a N *ᵥ v) =
      a * ∫ r in Ioi 0, Real.cosh (a*r) * thetaCuspNativeMomentTailHankelForm r v := by
    have hpoint (r : ℝ) : Real.cosh (a*r) * thetaCuspNativeMomentTailHankelForm r v =
        ∑ i : Fin N, ∑ j : Fin N, (v i * v j) *
          (Real.cosh (a*r) * thetaCuspNativeSignedJetMomentTail (i.val + j.val) r) := by
      simp only [thetaCuspNativeMomentTailHankelForm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (v i * v j))),
      Finset.mul_sum]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, thetaCuspCenterMixedSignedHankel,
      star_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (v i * v j)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, thetaCuspCenterMixedSignedJet_eq_integral_momentTail ha0 ha]
    ring
  rw [hform]
  refine mul_nonneg ha0 (setIntegral_nonneg measurableSet_Ioi fun r hr => ?_)
  exact mul_nonneg (Real.cosh_pos _).le (htail r hr v)

end
end RHTower
