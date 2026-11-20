import GaloisForLFunctions.RHTower.PoissonSummationPiecewise

/-!
# Half-endpoint charge of a clipped dilation

The kernel is constant below one half and smooth from one half to
one. The lower lattice count cancels the moving sawtooth at the join.
The remaining constant is exactly half the negative plateau height.
Two integrations by parts give a uniform inverse-scale error.
-/

noncomputable section
open Filter MeasureTheory GaloisForLFunctions.RHTower
open scoped Topology
namespace GaloisForLFunctions.ClippedLattice

/-- Sum over the plateau followed by the dilated smooth part. -/
def reading (h : ℝ → ℝ) (t : ℝ) :=
  (⌊t/2⌋:ℝ)*h (1/2) + ∑ j ∈ Finset.Ioc ⌊t/2⌋ ⌊t⌋, h ((j:ℝ)/t)

/-- Continuum density per unit dilation. -/
def density (h : ℝ → ℝ) := h (1/2)/2 + ∫ x in (1/2:ℝ)..1,h x

private def remainder (h' h'' : ℝ → ℝ) (t : ℝ) :=
  -(sawPrimitive t*h' 1)+sawPrimitive (t/2)*h' (1/2)+
    ∫ x in (1/2:ℝ)..1,sawPrimitive (x*t)*h'' x

/-- The exact endpoint charge and the bounded periodic remainder. -/
theorem clipped_lattice_expansion {h h' h'' : ℝ → ℝ}
    (h₁ : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt h (h' x) x)
    (h₂ : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt h' (h'' x) x)
    (hc : ContinuousOn h'' (Set.Icc (1/2:ℝ) 1)) {t : ℝ} (ht : 0<t) :
    reading h t = t*density h-h (1/2)/2+h 1*sawUnit t+remainder h' h'' t/t := by
  have he := em_dilated (a:=(1/2:ℝ)) (b:=1) (u:=t⁻¹) (by norm_num) (inv_pos.mpr ht) h₁ h₂ hc
  simp only [div_inv_eq_mul,one_mul,one_div,inv_inv] at he
  rw [show (2:ℝ)⁻¹*t=t/2 by ring] at he
  rw [reading]
  simp only [div_eq_mul_inv] at he ⊢
  rw [he]
  simp only [density,remainder,sawUnit,Int.fract,div_eq_mul_inv]
  ring

/-- The inverse-scale error holds uniformly over all positive real
dilations, including arbitrarily close to either endpoint lattice. -/
theorem clipped_lattice_error {h h' h'' : ℝ → ℝ}
    (h₁ : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt h (h' x) x)
    (h₂ : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt h' (h'' x) x)
    (hc : ContinuousOn h'' (Set.Icc (1/2:ℝ) 1)) :
    ∃ K : ℝ, 0≤K ∧ ∀ {t : ℝ}, 0<t →
      |reading h t-t*density h+h (1/2)/2-h 1*sawUnit t| ≤ K/t := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let K := (|h' 1|+|h' (1/2)|+|D|)/8
  refine ⟨K,by dsimp only [K]; positivity,fun {t} ht => ?_⟩
  rw [clipped_lattice_expansion h₁ h₂ hc ht,show
    t*density h-h (1/2)/2+h 1*sawUnit t+remainder h' h'' t/t-t*density h+h (1/2)/2-h 1*sawUnit t
      = remainder h' h'' t/t by ring,abs_div,abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  have hs (x : ℝ) (hx : x∈Set.Icc (1/2:ℝ) 1) :
      ‖sawPrimitive (x*t)*h'' x‖ ≤ (1/8)*|D| := by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (abs_sawPrimitive_le _) ((hD x hx).trans (le_abs_self _))
      (abs_nonneg _) (by norm_num)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1/2) (b := 1) fun x hx =>
    hs x (Set.Ioc_subset_Icc_self (by rwa [Set.uIoc_of_le (by norm_num : (1/2:ℝ)≤1)] at hx))
  rw [Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0≤(1:ℝ)-1/2)] at hi
  have term₁ : |sawPrimitive t*h' 1| ≤ (1/8)*|h' 1| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (abs_sawPrimitive_le _) (abs_nonneg _)
  have term₂ : |sawPrimitive (t/2)*h' (1/2)| ≤ (1/8)*|h' (1/2)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (abs_sawPrimitive_le _) (abs_nonneg _)
  dsimp only [remainder,K]
  apply (abs_add_le _ _).trans
  have ht' := abs_add_le (-(sawPrimitive t*h' 1)) (sawPrimitive (t/2)*h' (1/2))
  rw [abs_neg] at ht'
  linarith only [ht',term₁,term₂,hi,abs_nonneg D]

/-- At a vanishing terminal endpoint the half-plateau correction is
the actual constant term, through all real dilations. -/
theorem clipped_lattice_constant {h h' h'' : ℝ → ℝ}
    (h₁ : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt h (h' x) x)
    (h₂ : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt h' (h'' x) x)
    (hc : ContinuousOn h'' (Set.Icc (1/2:ℝ) 1)) (he : h 1=0) :
    Tendsto (fun t : ℝ => reading h t-t*density h) atTop (𝓝 (-(h (1/2)/2))) := by
  obtain ⟨K,_,hK⟩ := clipped_lattice_error h₁ h₂ hc
  have lim := (tendsto_const_nhds (x:=K)).div_atTop (tendsto_id (α:=ℝ) (x:=atTop))
  have err : Tendsto (fun t : ℝ => |reading h t-t*density h+h (1/2)/2|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ lim
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    simpa only [he,zero_mul,sub_zero,id_eq] using hK ht
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  simpa only [Real.norm_eq_abs,sub_neg_eq_add] using err

#print axioms clipped_lattice_error
#print axioms clipped_lattice_constant
end GaloisForLFunctions.ClippedLattice
