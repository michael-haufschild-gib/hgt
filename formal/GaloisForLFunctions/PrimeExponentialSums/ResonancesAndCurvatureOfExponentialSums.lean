import GaloisForLFunctions.PrimeExponentialSums.RationalPhaseStability
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiBlaschkePhaseDispersion
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization
import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Resonance lattice and sharp quadratic loss of a finite exponential sum

For nonnegative coefficients the squared amplitude loss is a sum of
nonnegative two-frequency defects. Integer frequencies attain full
coherence exactly on the dual of their active difference lattice. The
quadratic loss at the origin is determined by the weighted variance.
-/

noncomputable section
open Finset Complex Filter GaloisForLFunctions.LogarithmicChowla
open scoped Topology
namespace GaloisForLFunctions.PrimeExponentialSums.PhaseStability
variable {ι : Type*}

def mass (s : Finset ι) (w : ι → NNReal) : ℝ := ∑ i ∈ s, (w i : ℝ)

def amplitude (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) (x : ℝ) : ℝ :=
  ‖sumAt s (fun i => ((w i : ℝ) : ℂ)) f x‖

private theorem inner_phase (A B u v : ℝ) :
    (inner ℂ ((A : ℂ)*ex u) ((B : ℂ)*ex v)).re = A*B*Real.cos (2*Real.pi*(u-v)) := by
  rw [RCLike.inner_apply,map_mul,Complex.conj_ofReal,conj_ex]
  have he : (B : ℂ)*ex v*((A : ℂ)*ex (-u)) = ((A*B : ℝ) : ℂ)*ex (-(u-v)) := by
    rw [show -(u-v)=v+(-u) by ring,ex_add,Complex.ofReal_mul]
    ring
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,ex_re,
    mul_neg,Real.cos_neg]

/-- The exact contribution of every pair of occupied frequencies to the loss of amplitude. -/
theorem pair_dispersion (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) (x : ℝ) :
    mass s w^2 - amplitude s w f x^2 =
      ∑ i ∈ s, ∑ j ∈ s, (w i : ℝ)*(w j : ℝ)*(1-Real.cos (2*Real.pi*((f i-f j)*x))) := by
  let u (i : ι) := ((w i : ℝ) : ℂ)*ex (f i*x)
  have hu (i : ι) : ‖u i‖ = (w i : ℝ) := by
    change ‖((w i : ℝ) : ℂ)*ex (f i*x)‖ = _
    rw [norm_mul,norm_ex,mul_one,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_nonneg (w i).property
  have h := RiemannGaussian.finiteComplexPhaseDispersion_eq_variation_sq_sub_norm_sum_sq s u
  simp only [hu] at h
  rw [show mass s w^2-amplitude s w f x^2 = RiemannGaussian.finiteComplexPhaseDispersion s u from h.symm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [hu,hu,show (inner ℂ (u i) (u j)).re = _ from inner_phase _ _ _ _,← sub_mul (f i) (f j) x]
  ring

private theorem integral_cos (y : ℝ) :
    Real.cos (2*Real.pi*y)=1 ↔ ∃ k : ℤ, (k : ℝ)=y := by
  rw [Real.cos_eq_one_iff]
  refine exists_congr fun k => ?_
  rw [mul_comm (k : ℝ),mul_right_inj' (mul_ne_zero two_ne_zero Real.pi_ne_zero)]

/-- Full amplitude is equivalent to integrality of all pairwise active phase gaps. -/
theorem full_amplitude_iff (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) (x : ℝ) :
    amplitude s w f x = mass s w ↔
      ∀ i ∈ s, 0 < (w i : ℝ) → ∀ j ∈ s, 0 < (w j : ℝ) → ∃ k : ℤ, (k : ℝ)=(f i-f j)*x := by
  let D (i j : ι) := (w i : ℝ)*(w j : ℝ)*(1-Real.cos (2*Real.pi*((f i-f j)*x)))
  have hd (i j : ι) : 0 ≤ D i j := mul_nonneg (mul_nonneg (w i).property (w j).property)
    (sub_nonneg.mpr (Real.cos_le_one _))
  have he : mass s w^2-amplitude s w f x^2 = ∑ i ∈ s, ∑ j ∈ s,D i j := pair_dispersion s w f x
  have hm : 0 ≤ mass s w := sum_nonneg fun i _ => (w i).property
  constructor
  · intro h i hi hwi j hj hwj
    rw [h,sub_self] at he
    have hrow := (sum_eq_zero_iff_of_nonneg (fun t _ => sum_nonneg fun b _ => hd t b)).1 he.symm i hi
    have hp := (sum_eq_zero_iff_of_nonneg (fun b _ => hd i b)).1 hrow j hj
    have hz := (mul_eq_zero.mp hp).resolve_left (mul_pos hwi hwj).ne'
    exact (integral_cos _).1 (sub_eq_zero.mp hz).symm
  · intro h
    have hzero : ∑ i ∈ s, ∑ j ∈ s,D i j = 0 := by
      apply sum_eq_zero
      intro i hi
      apply sum_eq_zero
      intro j hj
      by_cases h₁ : (w i : ℝ)=0
      · simp [D,h₁]
      by_cases h₂ : (w j : ℝ)=0
      · simp [D,h₂]
      have hc := (integral_cos _).2 (h i hi (lt_of_le_of_ne (w i).property (Ne.symm h₁))
        j hj (lt_of_le_of_ne (w j).property (Ne.symm h₂)))
      simp only [D,hc,sub_self,mul_zero]
    rw [hzero] at he
    exact (sq_eq_sq₀ (norm_nonneg _) hm).mp (sub_eq_zero.mp he).symm

private theorem gcd_integral {α : Type*} (t : Finset α) (g : α → ℤ) (x : ℝ) :
    (∀ b ∈ t, ∃ k : ℤ, (k : ℝ)=(g b : ℝ)*x) ↔
      ∃ k : ℤ, (k : ℝ)=((t.gcd g : ℤ) : ℝ)*x := by
  classical
  constructor
  · intro h
    obtain ⟨c,hc⟩ := t.gcd_eq_sum_mul g
    let k (i : α) := if hi : i ∈ t then (h i hi).choose else 0
    refine ⟨∑ i ∈ t,k i*c i,?_⟩
    rw [hc,Int.cast_sum,Int.cast_sum,sum_mul]
    apply sum_congr rfl
    intro i hi
    simp only [Int.cast_mul,k,dif_pos hi,(h i hi).choose_spec]
    ring
  · rintro ⟨k,hk⟩ i hi
    obtain ⟨j,hj⟩ := Finset.gcd_dvd (f := g) hi
    exact ⟨k*j,by rw [Int.cast_mul,hk,hj,Int.cast_mul]; ring⟩

/-- Greatest common divisor of all differences between integer frequencies
having positive mass. The gcd of an empty set of differences is zero. -/
def differenceGcd (s : Finset ι) (w : ι → NNReal) (f : ι → ℤ) : ℤ :=
  let t := s.filter (fun i => 0 < (w i : ℝ))
  (t ×ˢ t).gcd (fun p => f p.1-f p.2)

/-- The complete resonance set is an arithmetic lattice, including the
degenerate case of one occupied frequency when every phase resonates. -/
theorem resonance_lattice (s : Finset ι) (w : ι → NNReal) (f : ι → ℤ) (x : ℝ) :
    amplitude s w (fun i => (f i : ℝ)) x = mass s w ↔
      ∃ k : ℤ, (k : ℝ)=(differenceGcd s w f : ℝ)*x := by
  rw [full_amplitude_iff,differenceGcd,← gcd_integral]
  simp only [Prod.forall,mem_product,mem_filter,Int.cast_sub,and_imp]
  exact ⟨fun h i j hi hwi hj hwj => h i hi hwi j hj hwj,
    fun h i hi hwi j hj hwj => h i j hi hwi hj hwj⟩

/-- The normalized squared-amplitude defect with its removable singularity filled. -/
def curvature (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) (x : ℝ) : ℝ :=
  2*Real.pi^2 * ∑ i ∈ s, ∑ j ∈ s, (w i : ℝ)*(w j : ℝ)*(f i-f j)^2*
    Real.sinc (Real.pi*(f i-f j)*x)^2

private theorem cos_sinc (y x : ℝ) :
    1-Real.cos (2*Real.pi*(y*x)) =
      x^2*(2*Real.pi^2)*(y^2*Real.sinc (Real.pi*y*x)^2) := by
  by_cases hx : x=0
  · simp [hx]
  have h := HTGeometry.sq_mul_sinc_sq_eq_normalized_cosDefect (m := 1) one_ne_zero hx (2*Real.pi*y)
  rw [show 2*Real.pi*y/2=Real.pi*y by ring,show 2*Real.pi*y*x=2*Real.pi*(y*x) by ring] at h
  field_simp [hx] at h
  rw [← mul_assoc (2*Real.pi) y x,← h]
  ring

theorem squared_loss_exact (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) (x : ℝ) :
    mass s w^2-amplitude s w f x^2 = x^2*curvature s w f x := by
  rw [pair_dispersion,curvature,← mul_assoc,mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [cos_sinc]
  ring

theorem curvature_continuous (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) :
    Continuous (curvature s w f) := by unfold curvature; fun_prop

/-- Exact second-order coefficient of the squared amplitude in terms of
the zeroth, first, and second frequency moments. -/
theorem curvature_at_zero (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) :
    curvature s w f 0 = 4*Real.pi^2*
      (mass s w*(∑ i ∈ s, (w i : ℝ)*(f i)^2) - (∑ i ∈ s, (w i : ℝ)*f i)^2) := by
  have he : 2*mass s w*(∑ i ∈ s,(w i : ℝ)*(f i)^2) =
      2*(∑ i ∈ s,(w i : ℝ)*f i)^2 +
        ∑ i ∈ s, ∑ j ∈ s,(w i : ℝ)*(w j : ℝ)*(f i-f j)^2 := by
    simpa only [mass,pow_two,mul_assoc] using
      _root_.RHTower.two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion s
        (fun i => (w i : ℝ)) f f
  simp only [curvature,mul_zero,Real.sinc_zero,one_pow,mul_one]
  linear_combination -2*Real.pi^2*he

/-- The normalized loss of amplitude tends to twice pi squared times the
unnormalized weighted variance. -/
theorem amplitude_loss_limit (s : Finset ι) (w : ι → NNReal) (f : ι → ℝ) (hm : 0 < mass s w) :
    Tendsto (fun x => (mass s w-amplitude s w f x)/x^2) (𝓝[≠] (0 : ℝ))
      (𝓝 (2*Real.pi^2*((∑ i ∈ s,(w i : ℝ)*(f i)^2) -
        (∑ i ∈ s,(w i : ℝ)*f i)^2/mass s w))) := by
  have ha : Continuous (amplitude s w f) := by unfold amplitude sumAt ex; fun_prop
  have h₀ : amplitude s w f 0 = mass s w := by
    apply (full_amplitude_iff _ _ _ _).2
    exact fun _ _ _ _ _ _ => ⟨0,by simp⟩
  have ht : ContinuousAt (fun x => curvature s w f x/(mass s w+amplitude s w f x)) 0 :=
    (curvature_continuous s w f).continuousAt.div ((continuous_const.add ha).continuousAt)
      (show mass s w+amplitude s w f 0 ≠ 0 by rw [h₀]; positivity)
  have H : Tendsto (fun x => curvature s w f x/(mass s w+amplitude s w f x)) (𝓝[≠] 0)
      (𝓝 (curvature s w f 0/(mass s w+amplitude s w f 0))) := ht.continuousWithinAt.tendsto
  rw [show curvature s w f 0/(mass s w+amplitude s w f 0) =
      2*Real.pi^2*((∑ i ∈ s,(w i : ℝ)*(f i)^2)-(∑ i ∈ s,(w i : ℝ)*f i)^2/mass s w) by
        rw [curvature_at_zero,h₀]; field_simp [hm.ne']; ring] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  have hd : mass s w+amplitude s w f x ≠ 0 := (add_pos_of_pos_of_nonneg hm (norm_nonneg _)).ne'
  change curvature s w f x/(mass s w+amplitude s w f x) = _
  apply (div_eq_div_iff hd (pow_ne_zero 2 hx')).2
  have h := squared_loss_exact s w f x
  linarith only [h]

end GaloisForLFunctions.PrimeExponentialSums.PhaseStability
