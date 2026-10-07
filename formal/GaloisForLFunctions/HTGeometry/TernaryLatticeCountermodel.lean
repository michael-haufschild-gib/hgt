import GaloisForLFunctions.HTGeometry.TernaryLatticeSections
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor

/-!
# Entire integer-marked sources from cubic lattice geometry

Every member of the explicit rational family yields an entire reflected
source, a global cubic lift, real structure, and off-line zeros of exact
even order. These are differential-algebraic countermodels, not Xi.
-/

noncomputable section
open Complex Polynomial Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.TernaryLatticeCountermodel

open TernaryLatticeCubic TernaryLatticeSections
local notation "cubic" => ReflectedCubicExponentialModel.cubic

def scaled (L : ℝ) (s : ℂ) : ℂ := L*(s-1/2)/(Real.pi*I)
def unscaled (L : ℝ) (w : ℂ) : ℂ := 1/2+Real.pi*I*w/L
def markedLift (m : ℤ) (L : ℝ) (s : ℂ) : ℂ := lift m (scaled L s)
def source (m : ℤ) (L : ℝ) (s : ℂ) : ℂ := exp (L*s)*cubic (markedLift m L s)

theorem scaled_entire (L : ℝ) : Differentiable ℂ (scaled L) := by
  change Differentiable ℂ (fun s => (L : ℂ)*(s-1/2)/(Real.pi*I))
  fun_prop

theorem markedLift_entire (m : ℤ) (L : ℝ) : Differentiable ℂ (markedLift m L) :=
  (lift_entire m).comp (scaled_entire L)

theorem source_entire (m : ℤ) (L : ℝ) : Differentiable ℂ (source m L) := by
  have hh := markedLift_entire m L
  change Differentiable ℂ (fun s => exp (L*s)*
    ((markedLift m L s-2)*(markedLift m L s+1)^2/4))
  fun_prop

theorem scaled_reflection (L : ℝ) (s : ℂ) : scaled L (1-s)= -scaled L s := by
  dsimp [scaled]
  ring

theorem scaled_conj (L : ℝ) (s : ℂ) : scaled L (conj s)= -conj (scaled L s) := by
  simp [scaled, map_ofNat]
  ring

theorem mark_scaled (L : ℝ) (s : ℂ) :
    mark (scaled L s)=exp (-(2*L/3)*(s-1/2)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [mark, scaled, ReflectedCubicExponentialModel.seam]
  congr 1
  field_simp

theorem source_reflection (m : ℤ) (L : ℝ) (s : ℂ) :
    source m L (1-s)=source m L s := by
  have he : exp ((L : ℂ)*(1-s))=exp (L*s)*mark (scaled L s)^3 := by
    rw [mark_scaled, ← exp_nat_mul, ← exp_add]
    congr 1
    ring
  simp only [source, markedLift, scaled_reflection]
  rw [he, mul_assoc, cubic_lift_neg]

theorem source_conj (m : ℤ) (L : ℝ) (s : ℂ) :
    source m L (conj s)=conj (source m L s) := by
  simp [source, markedLift, scaled_conj, lift_neg_conj,
    ReflectedCubicExponentialModel.cubic, map_ofNat, ← exp_conj]

theorem source_marked (m : ℤ) (L : ℝ) (s : ℂ) :
    source m L s*exp (-L*s)=cubic (markedLift m L s) := by
  have he : exp ((L : ℂ)*s)*exp (-L*s)=1 := by
    rw [← exp_add, show (L : ℂ)*s + -L*s=0 by ring, exp_zero]
  dsimp [source]
  linear_combination cubic (markedLift m L s)*he

theorem scaled_unscaled {L : ℝ} (hL : L ≠ 0) (w : ℂ) :
    scaled L (unscaled L w)=w := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp [scaled, unscaled]
  field_simp
  ring

theorem unscaled_off_line {L : ℝ} (hL : L ≠ 0) {w : ℂ} (hw : w ≠ conj w) :
    (unscaled L w).re ≠ 1/2 := by
  intro hr
  have hs : conj (unscaled L w)=1-unscaled L w := by
    apply Complex.ext <;> simp [hr]
    ring
  have hc := congrArg (scaled L) hs
  rw [scaled_conj, scaled_reflection, scaled_unscaled hL] at hc
  exact hw (neg_injective hc).symm

theorem source_zero_at_pole (m : ℤ) {L : ℝ} (hL : L ≠ 0) (w : ℂ)
    (hw : (denominator m).eval w=0) : source m L (unscaled L w)=0 := by
  simp [source, markedLift, scaled_unscaled hL, lift_at_pole m w hw,
    ReflectedCubicExponentialModel.cubic]

theorem scaled_deriv (L : ℝ) (s : ℂ) :
    HasDerivAt (scaled L) ((L : ℂ)/((Real.pi : ℂ)*I)) s := by
  convert! (((hasDerivAt_id s).sub_const (1/2)).const_mul (L : ℂ)).div_const
    ((Real.pi : ℂ)*I) using 1
  simp

theorem source_order_at_pole (m : ℤ) {L : ℝ} (hL : L ≠ 0) (w : ℂ)
    (hw : (denominator m).eval w=0) :
    analyticOrderAt (source m L) (unscaled L w)=
      2*analyticOrderAt (fun z => (denominator m).eval z) w := by
  have hcubic : Differentiable ℂ (fun z => cubic (lift m z)) := by
    have hh := lift_entire m
    dsimp [ReflectedCubicExponentialModel.cubic]
    fun_prop
  have he : source m L=(fun s => exp ((L : ℂ)*s))*
      ((fun z => cubic (lift m z)) ∘ scaled L) := rfl
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hder : deriv (scaled L) (unscaled L w) ≠ 0 := by
    rw [(scaled_deriv L _).deriv]
    exact div_ne_zero hLc (mul_ne_zero hp I_ne_zero)
  have hexp : analyticOrderAt (fun s => exp ((L : ℂ)*s)) (unscaled L w)=0 := by
    apply (show AnalyticAt ℂ (fun s => exp ((L : ℂ)*s)) _ by fun_prop).analyticOrderAt_eq_zero.mpr
    exact exp_ne_zero _
  rw [he, analyticOrderAt_mul (by fun_prop)
    ((hcubic.comp (scaled_entire L)).analyticAt _), hexp, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero ((scaled_entire L).analyticAt _) hder,
    scaled_unscaled hL, cubic_order_at_pole m w hw]

theorem source_reflected_order (m : ℤ) (L : ℝ) (s : ℂ) :
    analyticOrderAt (source m L) (1-s)=analyticOrderAt (source m L) s := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1-z) (1-s) := by fun_prop
  have hder : deriv (fun z : ℂ => 1-z) (1-s) ≠ 0 := by
    have he : deriv (fun z : ℂ => 1-z) (1-s)= -1 := by
      simpa only [id_eq] using ((hasDerivAt_id (1-s)).const_sub 1).deriv
    rw [he]
    norm_num
  have he : source m L ∘ (fun z => 1-z)=source m L := funext (source_reflection m L)
  have ho := analyticOrderAt_comp_of_deriv_ne_zero (f := source m L) hg hder
  rw [he] at ho
  simpa using ho

theorem denominator_one_ne_zero (m : ℤ) : (denominator m).eval 1 ≠ 0 := by
  have hn := (complete_fiber_omega m 1).mpr (Or.inl rfl)
  intro h
  exact no_common_zero m 1 ⟨by simpa [h] using hn,h⟩

theorem denominator_order_at_root (m : ℤ) (w : ℂ)
    (hw : (denominator m).eval w=0) :
    ∃ k : ℕ, k ≠ 0 ∧ analyticOrderAt (fun z => (denominator m).eval z) w=k := by
  obtain ⟨k,g,hk,hg,hgw,hfactor⟩ := exists_positive_pow_factor_of_entire_root
    (f := fun z => (denominator m).eval z)
    (fun z _ => (denominator m).differentiable.analyticAt z) hw
    ⟨1,denominator_one_ne_zero m⟩
  refine ⟨k, Nat.ne_of_gt hk, ?_⟩
  apply ((denominator m).differentiable.analyticAt w).analyticOrderAt_eq_natCast.mpr
  exact ⟨g,hg w (by simp),hgw,Eventually.of_forall (fun z => by
    simpa [smul_eq_mul] using hfactor z)⟩

/-- Every cubic parameter yields a reflected real entire source with integer mark two,
an entire cubic lift, and a reflected pair of off-line zeros of exact nonzero even order. -/
theorem reflected_integer_marked_family (m : ℤ) :
    Differentiable ℂ (source m (Real.log 2)) ∧
    Differentiable ℂ (markedLift m (Real.log 2)) ∧
    (∀ s, source m (Real.log 2) (1-s)=source m (Real.log 2) s) ∧
    (∀ s, source m (Real.log 2) (conj s)=conj (source m (Real.log 2) s)) ∧
    (∀ s, source m (Real.log 2) s*exp (-(Real.log 2 : ℂ)*s)=
      cubic (markedLift m (Real.log 2) s)) ∧
    ∃ (ρ : ℂ) (k : ℕ), k ≠ 0 ∧ ρ.re ≠ 1/2 ∧ (1-ρ).re ≠ 1/2 ∧
      source m (Real.log 2) ρ=0 ∧ source m (Real.log 2) (1-ρ)=0 ∧
      analyticOrderAt (source m (Real.log 2)) ρ=2*(k : ℕ∞) ∧
      analyticOrderAt (source m (Real.log 2)) (1-ρ)=2*(k : ℕ∞) := by
  have hL : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
  obtain ⟨w,hw,hnr⟩ := exists_nonreal_pole m
  obtain ⟨k,hk,hord⟩ := denominator_order_at_root m w hw
  let ρ := unscaled (Real.log 2) w
  have hρ : ρ.re ≠ 1/2 := unscaled_off_line hL hnr
  have hρ' : (1-ρ).re ≠ 1/2 := by
    intro h
    apply hρ
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have hz : source m (Real.log 2) ρ=0 := source_zero_at_pole m hL w hw
  have ho : analyticOrderAt (source m (Real.log 2)) ρ=2*(k : ℕ∞) := by
    rw [source_order_at_pole m hL w hw, hord]
  exact ⟨source_entire m _,markedLift_entire m _,source_reflection m _,
    source_conj m _,source_marked m _,ρ,k,hk,hρ,hρ',hz,
    by rwa [source_reflection],ho,by rwa [source_reflected_order]⟩

end GaloisForLFunctions.HTGeometry.TernaryLatticeCountermodel
