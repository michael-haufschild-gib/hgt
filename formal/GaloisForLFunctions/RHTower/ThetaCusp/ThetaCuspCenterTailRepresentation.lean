import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSuccessorSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltedSchwartz

/-!
# Center-tail representation of the signed theta hierarchy

Let `h_k(x)` be the native signed reflection jet of the complete theta source and put
`U_k(r) = ∫_{s>r} h_k(s/2) ds`. Integrating the center weight `r sinh(ar)` by parts gives, at
every order `k` and every aperture `0 ≤ a < 1/2`,

`s_k(a) = ∫_{r>0} (sinh(ar) + ar cosh(ar)) U_k(r) dr`.

The new weight is nonnegative and the tails `U_k` do not depend on the aperture. One `a`-free
family of tail Hankel forms therefore certifies a signed section at every critical aperture at
once: the native fibre may be negative near the self-dual seam, provided the mass beyond each
center pays for it.
-/

open MeasureTheory Set Filter Topology Matrix
namespace RHTower
noncomputable section

/-- Decay constant of the order-`k` native reflection jet. -/
def thetaCuspNativeJetDecayConstant (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
    (thetaCuspDerivativeExpConstant i * thetaCuspDerivativeExpConstant (k-i))

theorem thetaCuspNativeJetDecayConstant_nonneg (k : ℕ) :
    0 ≤ thetaCuspNativeJetDecayConstant k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (thetaCuspDerivativeExpConstant_nonneg i)
      (thetaCuspDerivativeExpConstant_nonneg _))

/-- Every native reflection jet decays like `exp(-2|x|)`. -/
theorem abs_thetaCuspNativeReflectionJet_le (k : ℕ) (x : ℝ) :
    |thetaCuspNativeReflectionJet k x| ≤
      thetaCuspNativeJetDecayConstant k * Real.exp (-(2*|x|)) := by
  rw [thetaCuspNativeReflectionJet_eq, thetaCuspNativeJetDecayConstant, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs i x
  have h2 := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs (k-i) x
  have hprod := mul_le_mul h1 h2 (abs_nonneg _)
    (mul_nonneg (thetaCuspDerivativeExpConstant_nonneg i) (Real.exp_pos _).le)
  have he : Real.exp (-(2*|x|)) = Real.exp (-|x|) * Real.exp (-|x|) := by
    rw [← Real.exp_add]; ring_nf
  have hp : |(-1 : ℝ)^(k-i)| = 1 := by simp
  rw [abs_mul, abs_mul, abs_mul, hp, one_mul, Nat.abs_cast, he]
  calc (k.choose i : ℝ) * |iteratedDeriv i thetaCuspFullSource x| *
        |iteratedDeriv (k-i) thetaCuspFullSource x|
      = (k.choose i : ℝ) * (|iteratedDeriv i thetaCuspFullSource x| *
        |iteratedDeriv (k-i) thetaCuspFullSource x|) := by ring
    _ ≤ (k.choose i : ℝ) * ((thetaCuspDerivativeExpConstant i * Real.exp (-|x|)) *
        (thetaCuspDerivativeExpConstant (k-i) * Real.exp (-|x|))) :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The Fourier-signed native jets inherit the same decay. -/
theorem abs_thetaCuspNativeSignedJet_le (x : ℝ) (k : ℕ) :
    |thetaCuspNativeSignedJet x k| ≤
      thetaCuspNativeJetDecayConstant k * Real.exp (-(2*|x|)) := by
  unfold thetaCuspNativeSignedJet
  rw [abs_mul]
  have hre : |((-Complex.I)^k).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (by simp)
  calc |((-Complex.I)^k).re| * |thetaCuspNativeReflectionJet k x|
      ≤ 1 * (thetaCuspNativeJetDecayConstant k * Real.exp (-(2*|x|))) :=
        mul_le_mul hre (abs_thetaCuspNativeReflectionJet_le k x) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem continuous_thetaCuspNativeSignedJet_half (k : ℕ) :
    Continuous (fun s : ℝ => thetaCuspNativeSignedJet (s/2) k) := by
  unfold thetaCuspNativeSignedJet
  exact continuous_const.mul
    ((continuous_thetaCuspNativeReflectionJet k).comp (continuous_id.div_const 2))

/-- In the center variable `s = 2x`, the signed jets decay like `exp(-s)`. -/
theorem abs_thetaCuspNativeSignedJet_half_le (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |thetaCuspNativeSignedJet (s/2) k| ≤ thetaCuspNativeJetDecayConstant k * Real.exp (-s) := by
  have h := abs_thetaCuspNativeSignedJet_le (s/2) k
  rwa [abs_of_nonneg (by linarith : 0 ≤ s/2), show 2*(s/2) = s by ring] at h

theorem integrableOn_thetaCuspNativeSignedJet_half (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℝ => thetaCuspNativeSignedJet (s/2) k) (Ioi r) := by
  refine ((integrableOn_exp_neg_Ioi r).const_mul
    (thetaCuspNativeJetDecayConstant k)).mono'
      (continuous_thetaCuspNativeSignedJet_half k).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs]
  exact abs_thetaCuspNativeSignedJet_half_le k (hr.trans hs.le)

/-- The center tail of the order-`k` native signed jet; it carries no aperture. -/
def thetaCuspNativeSignedJetTail (k : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Ioi r, thetaCuspNativeSignedJet (s/2) k

theorem abs_thetaCuspNativeSignedJetTail_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    |thetaCuspNativeSignedJetTail k r| ≤
      thetaCuspNativeJetDecayConstant k * Real.exp (-r) := by
  have hf := integrableOn_thetaCuspNativeSignedJet_half k hr
  have hg := (integrableOn_exp_neg_Ioi r).const_mul (thetaCuspNativeJetDecayConstant k)
  calc |thetaCuspNativeSignedJetTail k r|
      ≤ ∫ s in Ioi r, |thetaCuspNativeSignedJet (s/2) k| := abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi r, thetaCuspNativeJetDecayConstant k * Real.exp (-s) :=
      setIntegral_mono_on hf.abs hg measurableSet_Ioi
        fun s hs => abs_thetaCuspNativeSignedJet_half_le k (hr.trans (le_of_lt hs))
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi]

/-- The tail is differentiable at every positive center with derivative `-h_k(r/2)`. -/
theorem hasDerivAt_thetaCuspNativeSignedJetTail (k : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (thetaCuspNativeSignedJetTail k) (-thetaCuspNativeSignedJet (r/2) k) r := by
  have hf := continuous_thetaCuspNativeSignedJet_half k
  have hd : HasDerivAt (fun u => (∫ s in Ioi (0 : ℝ), thetaCuspNativeSignedJet (s/2) k) -
      ∫ s in (0 : ℝ)..u, thetaCuspNativeSignedJet (s/2) k)
      (-thetaCuspNativeSignedJet (r/2) k) r := by
    exact (hf.integral_hasStrictDerivAt 0 r).hasDerivAt.const_sub _
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hr] with u hu
  have h := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_thetaCuspNativeSignedJet_half k le_rfl)
    (integrableOn_thetaCuspNativeSignedJet_half k hu.le)
  unfold thetaCuspNativeSignedJetTail
  linarith

/-- The aperture weight after integration by parts. -/
def thetaCuspCenterTailWeight (a r : ℝ) : ℝ :=
  Real.sinh (a*r) + a*r*Real.cosh (a*r)

theorem thetaCuspCenterTailWeight_nonneg {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    0 ≤ thetaCuspCenterTailWeight a r := by
  have har : 0 ≤ a*r := mul_nonneg ha hr
  unfold thetaCuspCenterTailWeight
  exact add_nonneg (Real.sinh_nonneg_iff.mpr har)
    (mul_nonneg har (Real.cosh_pos _).le)

theorem thetaCuspCenterTailWeight_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 < thetaCuspCenterTailWeight a r := by
  have har : 0 < a*r := mul_pos ha hr
  unfold thetaCuspCenterTailWeight
  exact add_pos (Real.sinh_pos_iff.mpr har) (mul_pos har (Real.cosh_pos _))

/-- On nonnegative centers the weight is at most `(1+ar) exp(ar)`. -/
theorem thetaCuspCenterTailWeight_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    thetaCuspCenterTailWeight a r ≤ (1 + a*r) * Real.exp (a*r) := by
  have har : 0 ≤ a*r := mul_nonneg ha hr
  have hs : Real.sinh (a*r) ≤ Real.exp (a*r) := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (a*r), Real.exp_pos (-(a*r))]
  have hc : Real.cosh (a*r) ≤ Real.exp (a*r) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(a*r)) ≤ Real.exp (a*r) := Real.exp_le_exp.mpr (by linarith)
    linarith
  unfold thetaCuspCenterTailWeight
  nlinarith [mul_le_mul_of_nonneg_left hc har]

/-- The weighted tail is absolutely integrable at every critical aperture. -/
theorem integrableOn_thetaCuspCenterTailWeight_mul_tail {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (k : ℕ) :
    IntegrableOn (fun r => thetaCuspCenterTailWeight a r * thetaCuspNativeSignedJetTail k r)
      (Ioi 0) := by
  set K := thetaCuspNativeJetDecayConstant k
  have hK := thetaCuspNativeJetDecayConstant_nonneg k
  have hb : 0 < 1 - a := by linarith
  have h1 : IntegrableOn (fun r : ℝ => Real.exp (-(1-a) * r)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hb
  have h2 : IntegrableOn (fun r : ℝ => r * Real.exp (-(1-a) * r)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1-a)
      (by norm_num) le_rfl hb
    refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hdom := (h1.add (h2.const_mul a)).const_mul K
  have hcontW : Continuous (thetaCuspCenterTailWeight a) := by
    unfold thetaCuspCenterTailWeight; fun_prop
  have hcontU : ContinuousOn (thetaCuspNativeSignedJetTail k) (Ioi 0) := fun r hr =>
    (hasDerivAt_thetaCuspNativeSignedJetTail k hr).continuousAt.continuousWithinAt
  refine hdom.mono' ((hcontW.continuousOn.mul hcontU).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := le_of_lt hr
  have hW0 := thetaCuspCenterTailWeight_nonneg ha0 hr0
  have hW := thetaCuspCenterTailWeight_le ha0 hr0
  have hU := abs_thetaCuspNativeSignedJetTail_le k hr0
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW0]
  have hexp : Real.exp (a*r) * Real.exp (-r) = Real.exp (-(1-a) * r) := by
    rw [← Real.exp_add]; ring_nf
  calc thetaCuspCenterTailWeight a r * |thetaCuspNativeSignedJetTail k r|
      ≤ ((1 + a*r) * Real.exp (a*r)) * (K * Real.exp (-r)) :=
        mul_le_mul hW hU (abs_nonneg _) (by positivity)
    _ = K * (Real.exp (-(1-a) * r) + a * (r * Real.exp (-(1-a) * r))) := by
        rw [← hexp]; ring

/-- **Center-tail representation.** Every signed mixed jet is the integral of its aperture-free
center tail against the nonnegative weight `sinh(ar)+ar cosh(ar)`. -/
theorem thetaCuspCenterMixedSignedJet_eq_integral_tail {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (k : ℕ) :
    thetaCuspCenterMixedSignedJet a k =
      ∫ r in Ioi 0, thetaCuspCenterTailWeight a r * thetaCuspNativeSignedJetTail k r := by
  rw [thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0 ha]
  set K := thetaCuspNativeJetDecayConstant k
  have hK := thetaCuspNativeJetDecayConstant_nonneg k
  let u : ℝ → ℝ := fun r => r * Real.sinh (a*r)
  let v := thetaCuspNativeSignedJetTail k
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (thetaCuspCenterTailWeight a x) x := by
    intro x _
    have h2 : HasDerivAt (fun y => y * Real.sinh (a*y))
        (1 * Real.sinh (a*x) + x * (Real.cosh (a*x) * (a*1))) x :=
      (hasDerivAt_id' x).mul ((Real.hasDerivAt_sinh (a*x)).comp x ((hasDerivAt_id' x).const_mul a))
    convert h2 using 1
    unfold thetaCuspCenterTailWeight
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (-thetaCuspNativeSignedJet (x/2) k) x :=
    fun x hx => hasDerivAt_thetaCuspNativeSignedJetTail k hx
  have huv' : IntegrableOn (u * fun x => -thetaCuspNativeSignedJet (x/2) k) (Ioi 0) := by
    refine (integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha k).neg.congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    change -(x * Real.sinh (a*x) * thetaCuspNativeSignedJet (x/2) k) =
      x * Real.sinh (a*x) * -thetaCuspNativeSignedJet (x/2) k
    ring
  have hu'v : IntegrableOn (thetaCuspCenterTailWeight a * v) (Ioi 0) :=
    integrableOn_thetaCuspCenterTailWeight_mul_tail ha0 ha k
  have hcu : Continuous u := by fun_prop
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun x => K * |u x|) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun x => K * |u x|) := continuous_const.mul hcu.abs
      have h := hc.tendsto 0
      rw [show K * |u 0| = 0 by simp [u]] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hU := abs_thetaCuspNativeSignedJetTail_le k hx0
    have he : K * Real.exp (-x) ≤ K :=
      mul_le_of_le_one_right hK (Real.exp_le_one_iff.mpr (by linarith))
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg (u x), abs_nonneg (v x)]
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    have hb : 0 < 1 - a := by linarith
    have hlim : Tendsto (fun x : ℝ => K * (x ^ (1 : ℝ) * Real.exp (-(1-a) * x))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1-a) hb).const_mul K
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with x hx0
    have hU := abs_thetaCuspNativeSignedJetTail_le k hx0
    have hs : |Real.sinh (a*x)| ≤ Real.exp (a*x) := by
      rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hx0)), Real.sinh_eq]
      linarith [Real.exp_pos (a*x), Real.exp_pos (-(a*x))]
    have hexp : Real.exp (a*x) * Real.exp (-x) = Real.exp (-(1-a) * x) := by
      rw [← Real.exp_add]; ring_nf
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, Real.rpow_one]
    calc |u x| * |v x| ≤ (x * Real.exp (a*x)) * (K * Real.exp (-x)) := by
          apply mul_le_mul _ hU (abs_nonneg _) (by positivity)
          simp only [u, abs_mul, abs_of_nonneg hx0]
          exact mul_le_mul_of_nonneg_left hs hx0
      _ = K * (x * Real.exp (-(1-a) * x)) := by rw [← hexp]; ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
  have hneg : (∫ x in Ioi (0 : ℝ), u x * -thetaCuspNativeSignedJet (x/2) k) =
      -∫ x in Ioi (0 : ℝ), x * Real.sinh (a*x) * thetaCuspNativeSignedJet (x/2) k := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [u]
    ring
  rw [hneg] at hibp
  linarith

/-- The finite tail Hankel form at one center. -/
def thetaCuspNativeTailHankelForm {N : ℕ} (r : ℝ) (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i * v j * thetaCuspNativeSignedJetTail (i.val + j.val) r

/-- Every finite signed section is the weighted center integral of its tail form. -/
theorem thetaCuspCenterMixedSignedHankelForm_eq_integral_tail {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1/2) {N : ℕ} (v : Fin N → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, v i * v j * thetaCuspCenterMixedSignedJet a (i.val + j.val)) =
      ∫ r in Ioi 0, thetaCuspCenterTailWeight a r * thetaCuspNativeTailHankelForm r v := by
  have hi (i j : Fin N) :=
    (integrableOn_thetaCuspCenterTailWeight_mul_tail ha0 ha (i.val + j.val)).const_mul (v i * v j)
  have hpoint (r : ℝ) : thetaCuspCenterTailWeight a r * thetaCuspNativeTailHankelForm r v =
      ∑ i : Fin N, ∑ j : Fin N, (v i * v j) *
        (thetaCuspCenterTailWeight a r * thetaCuspNativeSignedJetTail (i.val + j.val) r) := by
    simp only [thetaCuspNativeTailHankelForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, thetaCuspCenterMixedSignedJet_eq_integral_tail ha0 ha]

/-- **Tail certificate.** Nonnegative tail forms at every positive center give the signed
section of that size at every critical aperture simultaneously. -/
theorem thetaCuspCenterMixedSignedHankel_posSemidef_of_tail {N : ℕ}
    (htail : ∀ r : ℝ, 0 < r → ∀ v : Fin N → ℝ, 0 ≤ thetaCuspNativeTailHankelForm r v)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a N).PosSemidef := by
  have hHerm : (thetaCuspCenterMixedSignedHankel a N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspCenterMixedSignedHankel, add_comm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
  have hform : star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a N *ᵥ v) =
      ∑ i : Fin N, ∑ j : Fin N, v i * v j * thetaCuspCenterMixedSignedJet a (i.val + j.val) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, thetaCuspCenterMixedSignedHankel,
      star_trivial]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hform, thetaCuspCenterMixedSignedHankelForm_eq_integral_tail ha0 ha]
  refine setIntegral_nonneg measurableSet_Ioi fun r hr => ?_
  exact mul_nonneg (thetaCuspCenterTailWeight_nonneg ha0 (le_of_lt hr)) (htail r hr v)

end
end RHTower
