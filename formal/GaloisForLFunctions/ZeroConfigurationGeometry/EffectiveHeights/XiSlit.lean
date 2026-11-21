import GaloisForLFunctions.RHTower.XiLogDerivEventualPositivityAbscissa
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Multiplicity on a shrinking vertical segment left of a zero

The local resolvent comparison of Broucke and Révész can be observed on
a segment instead of at a point. Centering the segment one width to the
left gives a Cauchy profile. Its negative part has quantized limiting
mass, so a fixed subcritical threshold detects every high off-line zero.
-/

noncomputable section
open Complex Filter Metric Set MeasureTheory Topology RHTower RHTower.BacklundConverse
open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget
namespace GaloisForLFunctions.ZeroConfigurationGeometry

private def leftVector (u : ℝ) : ℂ := -1+(u:ℂ)*I

private theorem leftVector_ne (u : ℝ) : leftVector u ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simpa [leftVector,Complex.mul_re] using this

private theorem norm_leftVector (u : ℝ) : ‖leftVector u‖ ≤ 1+|u| := by
  simpa [leftVector,norm_mul] using norm_add_le (-1:ℂ) ((u:ℂ)*I)

/-- Vertical segment at horizontal distance h left of w, in units of h. -/
def leftSegment (w : ℂ) (h u : ℝ) := w+(h:ℂ)*leftVector u

/-- Negative horizontal logarithmic slope, including the change of scale. -/
def leftDensity (w : ℂ) (h u : ℝ) := max (-(h*(logDeriv xi (leftSegment w h u)).re)) 0

private theorem pole_re (m : ℕ) (u : ℝ) : ((m:ℂ)/leftVector u).re = -(m/(1+u^2)) := by
  rw [div_eq_mul_inv,Complex.mul_re,Complex.inv_re,Complex.normSq_apply]
  simp only [leftVector, Complex.add_re,Complex.neg_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,Complex.add_im,
    Complex.neg_im,Complex.one_im,Complex.mul_im,Complex.natCast_re,Complex.natCast_im]
  ring

/-- The Cauchy profile approximates the scaled negative part uniformly
on bounded segments, with an O(h) error even at a regular center. -/
theorem xi_left_profile (w : ℂ) {L : ℝ} (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ u : ℝ, |u|≤L →
        ContinuousAt (leftDensity w h) u ∧
        |leftDensity w h u - (analyticOrderAt xi w).toNat/(1+u^2)| ≤ h*C := by
  let m := (analyticOrderAt xi w).toNat
  obtain ⟨R,hR,g,ha,hg,hfact⟩ := xi_peel_ball w
  have hlog : ContinuousAt (logDeriv g) w := (ha w (mem_ball_self hR)).deriv.continuousAt.div
    (ha w (mem_ball_self hR)).continuousAt (hg w (mem_ball_self hR))
  let C := ‖logDeriv g w‖ + 1
  have hC : ‖logDeriv g w‖<C := by dsimp [C]; linarith
  have hb := hlog.norm.tendsto.eventually_lt_const hC
  obtain ⟨s,hs,hs'⟩ := Metric.eventually_nhds_iff.mp hb
  have hsmall : 0 < min R s/(1+L) := div_pos (lt_min hR hs) (by linarith)
  refine ⟨C,(norm_nonneg _).trans_lt hC,?_⟩
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hsmall).filter_mono nhdsWithin_le_nhds]
    with h hh₀ hh u hu
  have hh : 0<h := hh₀
  let z := leftSegment w h u
  have hd : z-w=(h:ℂ)*leftVector u := by dsimp only [z,leftSegment]; ring
  have hdist : dist z w < min R s := by
    rw [dist_eq_norm,hd,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
    exact (mul_le_mul_of_nonneg_left ((norm_leftVector u).trans (add_le_add_right hu 1)) hh.le).trans_lt
      ((lt_div_iff₀ (by linarith only [hL] : 0<1+L)).mp ‹h < min R s / (1+L)›)
  have hz : z ∈ ball w R := hdist.trans_le (min_le_left _ _)
  have hz' : z≠w := by
    apply sub_ne_zero.mp
    rw [hd]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne') (leftVector_ne u)
  have hxi : xi z ≠ 0 := by
    rw [hfact z hz]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz')) (hg z hz)
  have hax := xi_analyticOnNhd_univ z (mem_univ _)
  have hcl : ContinuousAt (logDeriv xi) z := hax.deriv.continuousAt.div hax.continuousAt hxi
  have hpath : Continuous (fun v => leftSegment w h v) := by unfold leftSegment leftVector; fun_prop
  have hc1 : ContinuousAt (fun v => logDeriv xi (leftSegment w h v)) u :=
    ContinuousAt.comp (f := fun v => leftSegment w h v) hcl hpath.continuousAt
  have hc2 : ContinuousAt (fun v => (logDeriv xi (leftSegment w h v)).re) u :=
    Complex.continuous_re.continuousAt.comp hc1
  refine ⟨show ContinuousAt (fun v => max (-(h*(logDeriv xi (leftSegment w h v)).re)) 0) u from
    (continuousAt_const.mul hc2).neg.max continuousAt_const,?_⟩
  have he : (h:ℂ)*logDeriv xi z=(m:ℂ)/leftVector u+(h:ℂ)*logDeriv g z := by
    rw [logDeriv_xi_eq_pole_add ha hg hfact hz hz',hd]
    dsimp only [m]
    field_simp [Complex.ofReal_ne_zero.mpr hh.ne',leftVector_ne u] <;> ring
  have hre := congrArg Complex.re he
  simp only [Complex.add_re,Complex.re_ofReal_mul,pole_re] at hre
  have hm₀ : 0 ≤ (m:ℝ)/(1+u^2) := by positivity
  have herr : |-(h*(logDeriv xi z).re)-(m:ℝ)/(1+u^2)| ≤ h*C := by
    rw [show -(h*(logDeriv xi z).re)-(m:ℝ)/(1+u^2) = -(h*(logDeriv g z).re) by linarith only [hre],
      abs_neg,abs_mul,abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hs' (hdist.trans_le (min_le_right _ _))).le) hh.le
  have hmax := abs_max_sub_max_le_abs (-(h*(logDeriv xi z).re)) ((m:ℝ)/(1+u^2)) 0
  rw [max_eq_left hm₀] at hmax
  exact hmax.trans herr

/-- Integrated negative slope on the left segment with endpoints at
relative heights a,b, written in the scaled ordinate. -/
def leftMass (w : ℂ) (h a b : ℝ) := ∫ u in a..b, leftDensity w h u

/-- The integrated mass on every relative interval converges to its angle
at the center times multiplicity. No assumption on the center is needed. -/
theorem xi_left_mass (w : ℂ) (a b : ℝ) :
    Tendsto (fun h => leftMass w h a b) (𝓝[>] 0)
      (𝓝 ((analyticOrderAt xi w).toNat*(Real.arctan b-Real.arctan a))) := by
  let m := (analyticOrderAt xi w).toNat
  let k := fun u : ℝ => (m:ℝ)*(1+u^2)⁻¹
  have hk : Continuous k := continuous_const.mul
    ((by fun_prop : Continuous fun u : ℝ => 1+u^2).inv₀ (fun u => by positivity))
  have hi : (∫ u in a..b,k u)=(m:ℝ)*(Real.arctan b-Real.arctan a) := by
    dsimp only [k]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    simpa using integral_inv_one_add_sq (a := a) (b := b)
  have hu (u : ℝ) (hx : u ∈ uIcc a b) : |u| ≤ max |a| |b| := by
    rw [abs_le]
    rcases le_total a b with h|h
    · rw [uIcc_of_le h] at hx
      exact ⟨by linarith only [hx.1,neg_abs_le a,le_max_left |a| |b|],
        hx.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
    · rw [uIcc_of_ge h] at hx
      exact ⟨by linarith only [hx.1,neg_abs_le b,le_max_right |a| |b|],
        hx.2.trans ((le_abs_self _).trans (le_max_left _ _))⟩
  obtain ⟨C,_,he⟩ := xi_left_profile w (L := max |a| |b|) ((abs_nonneg a).trans (le_max_left _ _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun h => h*C*|b-a|) (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [he] with h hh
    have hf : IntervalIntegrable (leftDensity w h) volume a b :=
      (show ContinuousOn (leftDensity w h) (uIcc a b) from fun u hx =>
        (hh u (hu u hx)).1.continuousWithinAt).intervalIntegrable
    rw [leftMass,←hi,←intervalIntegral.integral_sub hf (hk.intervalIntegrable a b)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hj
    simpa only [Real.norm_eq_abs,k,←div_eq_mul_inv,m] using (hh u (hu u (uIoc_subset_uIcc hj))).2
  · simpa only [zero_mul,id_eq] using
      (((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[>] (0:ℝ)) (𝓝 0)).mul_const C).mul_const |b-a|)

/-- On the symmetric segment each zero contributes exactly π/2 per copy. -/
theorem xi_left_mass_symmetric (w : ℂ) :
    Tendsto (fun h => leftMass w h (-1) 1) (𝓝[>] 0)
      (𝓝 ((analyticOrderAt xi w).toNat*(Real.pi/2))) := by
  have he := xi_left_mass w (-1) 1
  rwa [Real.arctan_neg,Real.arctan_one,show Real.pi/4- -(Real.pi/4)=Real.pi/2 by ring] at he

/-- A fixed threshold below the first quantized mass detects exactly
the regular centers, even when only cofinally small widths are sampled. -/
theorem low_left_mass_iff (w : ℂ) {c : ℝ} (hc : 0<c) (hπ : c<Real.pi/2) :
    (∃ᶠ h : ℝ in 𝓝[>] 0, leftMass w h (-1) 1 ≤ c) ↔ xi w ≠ 0 := by
  have he := xi_left_mass_symmetric w
  constructor
  · intro hf hz
    have hm := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hz)
    have hp : (1:ℝ) ≤ (analyticOrderAt xi w).toNat := by exact_mod_cast hm
    have ht := hπ.trans_le (le_mul_of_one_le_left (by positivity) hp)
    exact (hf.and_eventually (he.eventually_const_lt ht)).exists.elim fun _ ⟨h₁,h₂⟩ => h₂.not_ge h₁
  · intro hw
    have hm := (xi_analyticOnNhd_univ w (mem_univ _)).analyticOrderAt_eq_zero.mpr hw
    simp only [hm,ENat.toNat_zero,Nat.cast_zero,zero_mul] at he
    exact (he.eventually_lt_const hc).frequently.mono fun _ h => h.le

/-- Above a fixed depth, eventual positivity is equivalent to seeing
less than one zero's worth of integrated negative slope cofinally at
each high center. The widths may depend on the center and its height. -/
theorem finite_right_zeros_iff_low_segments {a c : ℝ} (ha : 0≤a) (hc : 0<c) (hπ : c<Real.pi/2) :
    {q : XiZeroCopy | 1/2+a < ((q.1:ℂ)).re}.Finite ↔
      ∃ T : ℝ, ∀ w : ℂ, 1/2+a<w.re → T≤|w.im| →
        ∃ᶠ h : ℝ in 𝓝[>] 0, leftMass w h (-1) 1 ≤ c := by
  constructor
  · intro hf
    obtain ⟨T,hT⟩ := (eventualHadamardPositivityRight_iff ha).mpr hf
    refine ⟨T,fun w hw ht => (low_left_mass_iff w hc hπ).mpr ?_⟩
    intro hz
    obtain ⟨h,_,hh,hneg⟩ := exists_re_logDeriv_xi_neg_near_zero hz
      (δ := w.re-(1/2+a)) (sub_pos.mpr hw)
    have hreal : 1/2+a<(w-(h:ℂ)).re := by
      rw [Complex.sub_re,Complex.ofReal_re]; linarith only [hh]
    exact hneg.not_ge (hT _ hreal (by simpa using ht))
  · rintro ⟨T,hT⟩
    refine (xiZeroBall (⌈|T|+1⌉₊)).finite_toSet.subset fun q hq => ?_
    simp only [Finset.mem_coe,mem_xiZeroBall]
    have hheight : |((q.1:ℂ)).im| < T := by
      by_contra! h
      exact (low_left_mass_iff _ hc hπ).mp (hT _ hq h) (xi_xiZeroCopy_eq_zero q)
    have h₁ := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    have h₂ := abs_spectral_im_lt_half q
    have h₃ := Nat.le_ceil (|T|+1)
    rw [spectral_re_eq] at h₁
    linarith only [h₁,h₂,h₃,hheight,le_abs_self T]

/-- A single height cutoff for all centers strictly right of the critical
line is exactly the finite off-line stratum. The angle threshold is fixed. -/
theorem finite_off_line_iff_low_segments {c : ℝ} (hc : 0<c) (hπ : c<Real.pi/2) :
    FiniteOffLine ↔ ∃ T : ℝ, ∀ w : ℂ, 1/2<w.re → T≤|w.im| →
      ∃ᶠ h : ℝ in 𝓝[>] 0, leftMass w h (-1) 1 ≤ c := by
  have h := finite_right_zeros_iff_low_segments (a := 0) le_rfl hc hπ
  simpa only [add_zero,finite_re_gt_half_iff_finiteOffLine] using h


end GaloisForLFunctions.ZeroConfigurationGeometry
