import GaloisForLFunctions.RHTower.SelbergMaassCurrentHeightContinuity
import GaloisForLFunctions.RHTower.SelbergMaassBoundaryForm
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Original Maass slice rigidity from modal Cauchy data and the full cusp boundary form

The actual Fourier-mode equation has a continuous scalar potential on the
positive height domain. Grönwall applied to its value/derivative pair along
an affine path propagates zero Cauchy data in either direction. Original
Parseval and continuity recover the physical source. Consequently no
nonzero Maass source can vanish on an entire open horizontal band, at any
real eigenvalue.

For an exceptional eigenvalue strictly between zero and one quarter, every
cusp tail has strictly positive hyperbolic mass. A whole zero horizontal
slice annihilates both the actual outgoing flux and the complete Bessel
boundary form. The existing spectral tail identity would then equate a
strictly negative mass term to a sum of nonnegative squares. Thus every
slice has strictly positive squared mass. Compact height bands have a
source-dependent integrated-mass floor, and actual zero means supply
separated positive-density directions at every positive height.

Whole-slice vanishing is different from having a common source zero on a
slice. No common flat node is excluded, no pointwise amplitude floor is
inferred from integrated mass, and no uniform quotient-area quarter bound
or full-Xi occurrence is proved here. RH remains unproved.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory ModularGroup
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity
noncomputable section

/-- Actual second-order Cauchy data propagate across the entire positive ray. -/
theorem second_order_cauchy_zero {u v c : ℝ → ℂ}
    (hc : ContinuousOn c (Ioi 0))
    (hu : ∀ t, 0 < t → HasDerivAt u (v t) t)
    (hv : ∀ t, 0 < t → HasDerivAt v (c t * u t) t)
    {Y : ℝ} (hY : 0 < Y) (huY : u Y=0) (hvY : v Y=0)
    {y : ℝ} (hy : 0 < y) : u y=0 ∧ v y=0 := by
  let p : ℝ → ℝ := fun t => Y+t*(y-Y)
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : p t ∈ Icc (min Y y) (max Y y) := by
    dsimp [p]
    constructor <;> by_cases h : Y ≤ y
    · rw [min_eq_left h]; nlinarith [ht.1]
    · rw [min_eq_right (le_of_not_ge h)]; nlinarith [ht.2]
    · rw [max_eq_right h]; nlinarith [ht.2]
    · rw [max_eq_left (le_of_not_ge h)]; nlinarith [ht.1]
  have hpos (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < p t :=
    (lt_min hY hy).trans_le (hp t ht).1
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (show Icc (min Y y) (max Y y) ⊆ Ioi 0 from fun t ht => (lt_min hY hy).trans_le ht.1))
  let w : ℝ → ℂ × ℂ := fun t => (u (p t),v (p t))
  let w' : ℝ → ℂ × ℂ := fun t => ((y-Y) • v (p t),(y-Y) • (c (p t)*u (p t)))
  have hw (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt w (w' t) t := by
    have hd : HasDerivAt p (y-Y) t := by
      simpa [p] using ((hasDerivAt_id t).mul_const (y-Y)).const_add Y
    exact ((hu (p t) (hpos t ht)).scomp t hd).prodMk ((hv (p t) (hpos t ht)).scomp t hd)
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) : ‖w' t‖ ≤ (|y-Y| *(1+|C|))*‖w t‖ := by
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hc' : ‖c (p t)‖ ≤ 1+|C| := (hC (p t) (hp t ht')).trans
      ((le_abs_self C).trans (by linarith))
    have h1 : ‖v (p t)‖ ≤ (1+|C|)*max ‖u (p t)‖ ‖v (p t)‖ := by
      calc
        _ ≤ max ‖u (p t)‖ ‖v (p t)‖ := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_left (le_trans (norm_nonneg _) (le_max_left _ _)) (by linarith [abs_nonneg C])
    have h2 : ‖c (p t)*u (p t)‖ ≤ (1+|C|)*max ‖u (p t)‖ ‖v (p t)‖ := by
      rw [norm_mul]
      exact mul_le_mul hc' (le_max_left _ _) (norm_nonneg _) (by positivity)
    change max ‖(y-Y) • v (p t)‖ ‖(y-Y) • (c (p t)*u (p t))‖ ≤ _
    rw [norm_smul,norm_smul,Real.norm_eq_abs]
    apply max_le
    · exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans_eq (by dsimp [w]; ring)
    · exact (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)).trans_eq (by dsimp [w]; ring)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (fun t ht => (hw t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hw t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (show w 0=0 by simp [w,p,huY,hvY]) hb 1 (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
  have h := Prod.mk.inj hz
  simpa [w,p] using h

open SelbergMaassMean SelbergMaassFourier SelbergMaassParseval SelbergMaassFlux
open SelbergMaassTailEnergy SelbergMaassTrace SelbergMaassBoundaryForm SelbergBoundaryOperator
open SelbergMaassUnipotentPaths
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The exact scalar potential of each original Fourier mode. -/
def modalPotential (n : ℤ) (y : ℝ) : ℂ :=
  ((signedFrequency (N+1:ℕ) n ^ (2 : ℕ) - lam / y^(2 : ℕ) : ℝ) : ℂ)

/-- The defining Maass equation in the coefficient form used by Cauchy uniqueness. -/
theorem maassCoefficient_second_eq (n : ℤ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (maassCoefficient N f n)) y =
      modalPotential (lam:=lam) N n y * maassCoefficient N f n y := by
  have h := maassCoefficient_modal_equation N f n hy
  have hyc : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  unfold modalPotential
  push_cast
  field_simp [hyc]
  simp only [Nat.cast_add,Nat.cast_one] at h
  linear_combination -h

/-- Original modal Cauchy data at one height determine that mode on the whole positive ray. -/
theorem maassCoefficient_cauchy_zero (n : ℤ) {Y : ℝ} (hY : 0 < Y)
    (h0 : maassCoefficient N f n Y=0) (h1 : deriv (maassCoefficient N f n) Y=0)
    {y : ℝ} (hy : 0 < y) :
    maassCoefficient N f n y=0 ∧ deriv (maassCoefficient N f n) y=0 := by
  apply second_order_cauchy_zero (c:=modalPotential (lam:=lam) N n) ?_
    (fun t ht => maassCoefficient_hasDerivAt N f n ht) ?_ hY h0 h1 hy
  · intro t ht
    unfold modalPotential
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.sub (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht.ne')))).continuousWithinAt
  · intro t ht
    simpa only [maassCoefficient_second_eq N f n ht] using maassCoefficient_second_hasDerivAt N f n ht

/-- Zero actual squared slice mass is exactly whole-slice vanishing, including all periodic copies. -/
theorem mass_eq_zero_iff_slice_zero {y : ℝ} (hy : 0 < y) :
    mass N f y=0 ↔ ∀ x : ℝ, (f.1.1 ∘ ofComplex) (point x y)=0 := by
  constructor
  · intro hm x
    have hp : Function.Periodic (fun t => (f.1.1 ∘ ofComplex) (point t y)) (N+1:ℕ) :=
      fun t => maass_periodic N f t hy
    obtain ⟨t,ht,he⟩ := hp.exists_mem_Ico₀ (by positivity : (0:ℝ)<(N+1:ℕ)) x
    rw [he]
    by_contra hn
    have hpos := intervalIntegral.integral_pos (by positivity : (0:ℝ)<(N+1:ℕ))
      (Complex.continuous_normSq.comp (slice_continuous f.2.2.1.1.continuousOn hy)).continuousOn
      (fun _ _ => Complex.normSq_nonneg _)
      ⟨t,⟨ht.1,ht.2.le⟩,Complex.normSq_pos.mpr hn⟩
    rw [mass_eq_integral N f hy] at hm
    have : 0 < ((N+1:ℕ):ℝ)⁻¹ * ∫ t in (0:ℝ)..(N+1:ℕ),
        Complex.normSq ((f.1.1 ∘ ofComplex) (point t y)) := mul_pos (by positivity) hpos
    linarith
  · intro h
    rw [mass_eq_integral N f hy]
    simp only [h,Complex.normSq_zero,intervalIntegral.integral_zero,mul_zero]

/-- Actual Parseval recovers a whole zero slice from vanishing of all original Fourier coordinates. -/
theorem slice_zero_of_coefficients_zero {y : ℝ} (hy : 0 < y)
    (h : ∀ n : ℤ, maassCoefficient N f n y=0) :
    ∀ x : ℝ, (f.1.1 ∘ ofComplex) (point x y)=0 := by
  apply (mass_eq_zero_iff_slice_zero N f hy).mp
  have hm := mass_hasSum N f hy
  simp only [h,Complex.normSq_zero] at hm
  exact hm.unique hasSum_zero

/-- The original nonzero Maass source cannot have zero Fourier coordinates at every positive height. -/
theorem not_all_coefficients_zero :
    ¬ (∀ y : ℝ, 0 < y → ∀ n : ℤ, maassCoefficient N f n y=0) := by
  intro h
  apply f.2.1
  apply Subtype.ext
  funext z
  change f.1.1 z=0
  have hz := slice_zero_of_coefficients_zero N f z.im_pos (h z.im z.im_pos) z.re
  simpa only [Function.comp_apply,ofComplex_point_self] using hz

/-- Every height has nonzero original modal Cauchy data. -/
theorem exists_nonzero_modal_cauchy {Y : ℝ} (hY : 0 < Y) :
    ∃ n : ℤ, maassCoefficient N f n Y ≠ 0 ∨ deriv (maassCoefficient N f n) Y ≠ 0 := by
  by_contra hn
  push Not at hn
  apply not_all_coefficients_zero N f
  intro y hy n
  exact (maassCoefficient_cauchy_zero N f n hY (hn n).1 (hn n).2 hy).1

/-- A whole zero horizontal slice annihilates every literal Fourier coordinate. -/
theorem coefficient_zero_of_slice_zero {y : ℝ}
    (h : ∀ x : ℝ, (f.1.1 ∘ ofComplex) (point x y)=0) (n : ℤ) :
    maassCoefficient N f n y=0 := by
  unfold maassCoefficient coefficient _root_.RHTower.deningerFourierCoeff
  simp only [h,mul_zero,intervalIntegral.integral_zero]

/-- Original source nonvanishing propagates into every open positive-height band. -/
theorem exists_nonzero_in_height_band {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ y ∈ Ioo a b, ∃ x : ℝ, (f.1.1 ∘ ofComplex) (point x y) ≠ 0 := by
  by_contra hn
  push Not at hn
  let Y := (a+b)/2
  have hY : 0 < Y := by dsimp [Y]; linarith
  have habY : Y ∈ Ioo a b := by dsimp [Y]; constructor <;> linarith
  have hc (n : ℤ) : maassCoefficient N f n =ᶠ[𝓝 Y] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds habY.1 habY.2] with y hy
    exact coefficient_zero_of_slice_zero N f (hn y hy) n
  obtain ⟨n,hn⟩ := exists_nonzero_modal_cauchy N f hY
  have h0 : maassCoefficient N f n Y=0 := (hc n).eq_of_nhds
  have h1 : deriv (maassCoefficient N f n) Y=0 := by simpa using (hc n).deriv_eq
  exact hn.elim (fun h => h h0) (fun h => h h1)

/-- Every positive-height band contains strictly positive original squared slice mass. -/
theorem exists_mass_pos_in_height_band {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ y ∈ Ioo a b, 0 < mass N f y := by
  obtain ⟨y,hy,x,hx⟩ := exists_nonzero_in_height_band N f ha hab
  refine ⟨y,hy,lt_of_le_of_ne (mass_nonneg N f (ha.trans hy.1)) ?_⟩
  intro he
  exact hx ((mass_eq_zero_iff_slice_zero N f (ha.trans hy.1)).mp he.symm x)

/-- Whole-slice vanishing also annihilates the actual outgoing flux, regardless of normal derivatives. -/
theorem flux_zero_of_slice_zero {y : ℝ} (hy : 0 < y)
    (h : ∀ x : ℝ, (f.1.1 ∘ ofComplex) (point x y)=0) : flux N f y=0 := by
  rw [flux,pairing_eq_integral _
    (directional_contDiffOn f.2.2.1.1 (m:=1) (by norm_num) Complex.I).continuousOn
    f.2.2.1.1.continuousOn hy]
  simp only [h,map_zero,mul_zero,Complex.zero_re,integral_zero]

/-- The actual Bessel boundary form vanishes on a whole zero source slice. -/
theorem boundaryForm_zero_of_slice_zero {y : ℝ} (hy : 0 < y)
    (h : ∀ x : ℝ, (f.1.1 ∘ ofComplex) (point x y)=0) :
    boundaryForm (Real.log (N+1:ℕ)) (Real.log y) (formTrace N f (Real.log y))=0 := by
  change (∑' n : ℤ, SelbergBesselModes.seam (Real.log (N+1:ℕ)) (Real.log y) n *
    Complex.normSq (maassCoefficient N f n (Real.exp (Real.log y))))=0
  simp only [Real.exp_log hy,coefficient_zero_of_slice_zero N f h,Complex.normSq_zero,mul_zero,tsum_zero]

variable (mu : Ioo (0:ℝ) (1/4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (mu:ℝ))

/-- Every actual exceptional Maass cusp tail has strictly positive hyperbolic mass. -/
theorem hyperbolic_tail_mass_pos {Y : ℝ} (hY : 0 < Y) :
    0 < ∫ y in Ioi Y, mass N g y / y^(2 : ℕ) := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi Y)] (fun y => mass N g y / y^(2 : ℕ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact div_nonneg (mass_nonneg N g (hY.trans hy)) (sq_nonneg _)
  have hp := integral_nonneg_of_ae hn
  apply lt_of_le_of_ne hp
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn (hyperbolicMass_tail_integrable N mu g hY)).mp he.symm
  have hc : ContinuousOn (fun y => mass N g y / y^(2 : ℕ)) (Ioi Y) := by
    intro y hy
    exact ((mass_hasDerivAt N g (hY.trans hy)).continuousAt.div
      (continuousAt_id.pow 2) (pow_ne_zero 2 (hY.trans hy).ne')).continuousWithinAt
  have hall := MeasureTheory.Measure.eqOn_open_of_ae_eq hz isOpen_Ioi hc continuousOn_const
  obtain ⟨y,hy,hm⟩ := exists_mass_pos_in_height_band N g (a:=Y) (b:=Y+1) hY (by linarith)
  have hzero := hall hy.1
  have hgt : 0 < mass N g y / y^(2 : ℕ) := div_pos hm (sq_pos_of_pos (hY.trans hy.1))
  simp only [hzero,Pi.zero_apply,lt_self_iff_false] at hgt

/-- Original spectral tail mass and nonnegative Bessel squares rule out a whole zero horizontal slice. -/
theorem exceptional_not_zero_slice {y : ℝ} (hy : 0 < y) :
    ¬ (∀ x : ℝ, (g.1.1 ∘ ofComplex) (point x y)=0) := by
  intro hz
  have hf := flux_zero_of_slice_zero N g hy hz
  have hb := boundaryForm_zero_of_slice_zero N g hy hz
  have he := maass_flux_boundary_identity N mu g (Real.log y)
  rw [Real.exp_log hy,hf,hb,neg_zero,zero_add] at he
  have hn : 0 ≤ ∑' n : ℤ, modeSquareTail N g (Real.log y) n :=
    tsum_nonneg (modeSquareTail_nonneg N g (Real.log y))
  have hp := hyperbolic_tail_mass_pos N mu g hy
  have hmu : (mu:ℝ) < 1/4 := mu.2.2
  nlinarith

/-- Every horizontal slice of an original exceptional Maass source has strictly positive squared mass. -/
theorem exceptional_slice_mass_pos {y : ℝ} (hy : 0 < y) : 0 < mass N g y := by
  apply lt_of_le_of_ne (mass_nonneg N g hy)
  intro h
  exact exceptional_not_zero_slice N mu g hy ((mass_eq_zero_iff_slice_zero N g hy).mp h.symm)

/-- Actual exceptional Maass source values are nonzero somewhere on every positive-height line. -/
theorem exceptional_exists_nonzero_on_slice {y : ℝ} (hy : 0 < y) :
    ∃ x : ℝ, (g.1.1 ∘ ofComplex) (point x y) ≠ 0 := by
  by_contra h
  push Not at h
  exact exceptional_not_zero_slice N mu g hy h

/-- Compact positive-height bands have a strictly positive actual squared-mass floor. -/
theorem exceptional_compact_slice_mass_floor {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ d : ℝ, 0 < d ∧ ∀ y ∈ Icc a b, d ≤ mass N g y := by
  have hc : ContinuousOn (mass N g) (Icc a b) :=
    fun y hy => (mass_hasDerivAt N g (ha.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨y,hy,hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  exact ⟨mass N g y,exceptional_slice_mass_pos N mu g (ha.trans_le hy.1),hm⟩

open SelbergMaassCongruenceTrace SelbergMaassTraceDirection SelbergMaassRegularizedCusp

/-- The complete original modular trace has a positive point in every unit period at every positive height. -/
theorem exceptional_density_pos_in_unit_period {y : ℝ} (hy : 0 < y) :
    ∃ x ∈ Icc (0:ℝ) 1, 0 < density N g (ofComplex (point x y)) := by
  obtain ⟨x,hx⟩ := exceptional_exists_nonzero_on_slice N mu g hy
  have hd : 0 < density N g (ofComplex (point x y)) :=
    (Complex.normSq_pos.mpr hx).trans_le (normSq_le_density N g _)
  obtain ⟨t,ht,he⟩ := (density_slice_periodic N g hy).exists_mem_Ico₀ (by norm_num) x
  exact ⟨t,⟨ht.1,ht.2.le⟩,by rwa [he] at hd⟩

/-- Actual zero means force separated positive-density directions on every positive-height line. -/
theorem exceptional_separated_directions_every_height {y : ℝ} (hy : 0 < y) :
    ∃ x t : ℝ, x ∈ Icc (0:ℝ) 1 ∧
      0 < density N g (ofComplex (point x y)) ∧
      0 < density N g (ofComplex (point t y)) ∧
      2 < directionDistanceSq N g (ofComplex (point x y)) (ofComplex (point t y)) := by
  obtain ⟨x,hx,hD⟩ := exceptional_density_pos_in_unit_period N mu g hy
  let z : ℍ := ofComplex (point x y)
  have hz : z.im=y := by
    change ((ofComplex (point x y):ℍ):ℂ).im=y
    rw [coe_ofComplex_point x hy]
    simp [point]
  obtain ⟨t,_ht,hDt,hsep⟩ := exists_separated_direction N mu g z hD
  rw [hz] at hDt hsep
  exact ⟨x,t,hx,hD,hDt,hsep⟩

end
end GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity
