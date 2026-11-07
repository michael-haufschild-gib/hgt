import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinChannel
import GaloisForLFunctions.BlackHoleRingdown.TheCuspChannel

/-!
# The cosine family of the modular horizon

Every square-integrable function on `PSL₂(ℤ)\ℍ` splits as a constant, an element of the closure `𝓦` of the fields `𝓕_h(0)` of
compact pulses, and a cuspidal part. On `𝓦` the assignment `𝓕_h(0) ↦ ½(𝓕_h(τ) + 𝓕_h(-τ))` extends to a strongly continuous
contractive cosine family: it is well defined because pulses form a vector space and the bound holds for each one.
Together with the cuspidal family this is the wave evolution of general horizon data, and it is contractive on the
orthogonal complement of the constants.
-/

open Complex MeasureTheory Set Filter Topology ModularGroup EisensteinSeries
open scoped ContDiff InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower (mem_window_self)
open GaloisForLFunctions.RHTower.DeckPointPair
  GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet GaloisForLFunctions.RHTower.MaassCongruenceL2

/-! ### Extension of a contraction -/

/-- **A linear map dominated by another extends to a contraction.** -/
theorem exists_contraction_of_norm_le {V H : Type*} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A B : V →ₗ[ℂ] H) (hB : ∀ v, ‖B v‖ ≤ ‖A v‖) :
    ∃ C : H →L[ℂ] H, (∀ x, ‖C x‖ ≤ ‖x‖) ∧ ∀ v, C (A v) = B v := by
  set R := LinearMap.range A with hR
  set W := R.topologicalClosure with hW
  haveI : CompleteSpace W := (Submodule.isClosed_topologicalClosure R).completeSpace_coe
  have hker : LinearMap.ker A ≤ LinearMap.ker B := fun v hv => by
    have h1 := hB v
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hv, norm_zero] at h1
    exact norm_le_zero_iff.mp h1
  set L₀ : R →ₗ[ℂ] H := ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap with hL₀
  have hL₀v : ∀ v, L₀ ⟨A v, LinearMap.mem_range_self A v⟩ = B v := fun v => by
    change (LinearMap.ker A).liftQ B hker (A.quotKerEquivRange.symm ⟨A v, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hbd : ∀ x : R, ‖L₀ x‖ ≤ 1 * ‖x‖ := by
    rintro ⟨_, v, rfl⟩
    rw [one_mul, hL₀v]
    exact hB v
  set L : R →L[ℂ] H := L₀.mkContinuous 1 hbd with hL
  set incl : R →L[ℂ] W := (Submodule.inclusion (Submodule.le_topologicalClosure R)).mkContinuous 1
    (fun x => by
      rw [one_mul]
      exact le_of_eq rfl) with hincl
  have hdense : DenseRange incl := by
    intro y
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, mem_preimage]
    have hsub : (R : Set H) ⊆ Subtype.val '' Set.range incl :=
      fun f hf => ⟨incl ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
    refine closure_mono hsub ?_
    have h : (W : Set H) = closure (R : Set H) := Submodule.topologicalClosure_coe _
    rw [← h]
    exact y.2
  have hind : IsUniformInducing incl :=
    (AddMonoidHomClass.isometry_of_norm incl fun _ => rfl).isUniformInducing
  set Ext := L.extend incl with hExtdef
  have hExt : ∀ x : R, Ext (incl x) = L x := L.extend_eq hdense hind
  have hExtBound : ∀ y : W, ‖Ext y‖ ≤ ‖y‖ := by
    intro y
    refine hdense.induction_on (p := fun y => ‖Ext y‖ ≤ ‖y‖) y
      (isClosed_le Ext.continuous.norm continuous_norm) fun x => ?_
    rw [hExt]
    have h1 : ‖L x‖ ≤ 1 * ‖x‖ := LinearMap.mkContinuous_apply L₀ 1 hbd x ▸ hbd x
    rw [one_mul] at h1
    exact h1
  refine ⟨Ext.comp W.orthogonalProjectionOnto, fun x => ?_, fun v => ?_⟩
  · have hP : ‖W.orthogonalProjectionOnto x‖ ≤ ‖x‖ := by
      have := W.orthogonalProjectionOnto.le_of_opNorm_le (Submodule.orthogonalProjectionOnto_norm_le W) x
      rwa [one_mul] at this
    exact (hExtBound _).trans hP
  · have hmem : A v ∈ W := Submodule.le_topologicalClosure R (LinearMap.mem_range_self A v)
    have h1 := W.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A v, hmem⟩
    change Ext (W.orthogonalProjectionOnto (A v)) = B v
    have h2 : (⟨A v, hmem⟩ : W) = incl ⟨A v, LinearMap.mem_range_self A v⟩ := rfl
    have h3 : W.orthogonalProjectionOnto (A v) = (⟨A v, hmem⟩ : W) := h1
    rw [h3, h2, hExt]
    exact (LinearMap.mkContinuous_apply L₀ 1 hbd _).trans (hL₀v v)

/-! ### Linearity in the pulse -/

section Linearity

variable (c : ℂ) {h g k : CompactPulse} (hk : ∀ S, k S = c * h S + g S)

include hk

theorem imageField_lin (τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    imageField k τ x Y = c * imageField h τ x Y + imageField g τ x Y := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_box h τ x hY
  obtain ⟨S₂, h₂⟩ := exists_finset_box g τ x hY
  have hmem : |τ - τ| ≤ 1 ∧ |x - x| ≤ 1 ∧ Y ∈ Icc (Y / 2) (2 * Y) := ⟨by simp, by simp, mem_window_self hY⟩
  have hz1 : ∀ p ∉ S₁ ∪ S₂, imageTerm h (rowC p) (rowD p) τ x Y = 0 := fun p hp => by
    simp only [Finset.mem_union, not_or] at hp
    exact h₁ τ x Y hmem.1 hmem.2.1 hmem.2.2 p hp.1
  have hz2 : ∀ p ∉ S₁ ∪ S₂, imageTerm g (rowC p) (rowD p) τ x Y = 0 := fun p hp => by
    simp only [Finset.mem_union, not_or] at hp
    exact h₂ τ x Y hmem.1 hmem.2.1 hmem.2.2 p hp.2
  have hterm : ∀ p : gammaSet 1 1 0, imageTerm k (rowC p) (rowD p) τ x Y =
      c * imageTerm h (rowC p) (rowD p) τ x Y + imageTerm g (rowC p) (rowD p) τ x Y := fun p => by
    simp only [imageTerm, pulseF, hk]
    ring
  rw [imageField, imageField, imageField, tsum_eq_sum (s := S₁ ∪ S₂) fun p hp => by
      rw [hterm, hz1 p hp, hz2 p hp]
      simp,
    tsum_eq_sum (s := S₁ ∪ S₂) hz1, tsum_eq_sum (s := S₁ ∪ S₂) hz2]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem pulseAmplitude_lin (w : ℂ) :
    pulseAmplitude k w = c * pulseAmplitude h w + pulseAmplitude g w := by
  have hsplit : (∫ S : ℝ, k S * Complex.exp (-(I * w * (S : ℂ)))) =
      c * (∫ S : ℝ, h S * Complex.exp (-(I * w * (S : ℂ)))) +
        ∫ S : ℝ, g S * Complex.exp (-(I * w * (S : ℂ))) := by
    rw [← integral_const_mul, ← integral_add ((h.integrable_mul_cexp w).const_mul c)
      (g.integrable_mul_cexp w)]
    refine integral_congr_ae (Eventually.of_forall fun S => ?_)
    simp only [hk]
    ring
  simp only [pulseAmplitude]
  rw [hsplit]
  ring

theorem pulseField_lin (τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    pulseField k τ x Y = c * pulseField h τ x Y + pulseField g τ x Y := by
  simp only [pulseField, meanCoefficient]
  rw [imageField_lin c hk τ x hY, pulseAmplitude_lin c hk]
  ring

theorem pulseL2_lin (τ : ℝ) (N : ℕ) :
    pulseL2 k τ N = c • pulseL2 h τ N + pulseL2 g τ N := by
  apply Lp.ext
  filter_upwards [pulseL2_coeFn k τ N, Lp.coeFn_add (c • pulseL2 h τ N) (pulseL2 g τ N),
    Lp.coeFn_smul c (pulseL2 h τ N), pulseL2_coeFn h τ N, pulseL2_coeFn g τ N] with z a1 a2 a3 a4 a5
  rw [a1, a2, Pi.add_apply, a3, Pi.smul_apply, a4, a5, pulseField_lin c hk τ z.re z.im_pos]
  module

end Linearity

/-! ### Time translation -/

namespace CompactPulse

/-- The translated pulse `S ↦ h(τ + S)`. -/
def shift (τ : ℝ) (h : CompactPulse) : CompactPulse where
  toFun S := h (τ + S)
  smooth := h.smooth.comp (contDiff_const.add contDiff_id)
  compact := h.compact.comp_homeomorph (Homeomorph.addLeft τ)

theorem pulseAmplitude_shift (τ : ℝ) (h : CompactPulse) (w : ℂ) :
    pulseAmplitude (h.shift τ) w = Complex.exp (I * w * (τ : ℂ)) * pulseAmplitude h w := by
  have hsub : (∫ S : ℝ, (h.shift τ) S * Complex.exp (-(I * w * (S : ℂ)))) =
      ∫ S : ℝ, Complex.exp (I * w * (τ : ℂ)) * (h S * Complex.exp (-(I * w * (S : ℂ)))) := by
    rw [← integral_add_left_eq_self (fun S : ℝ => Complex.exp (I * w * (τ : ℂ)) *
      (h S * Complex.exp (-(I * w * (S : ℂ))))) τ]
    refine integral_congr_ae (Eventually.of_forall fun S => ?_)
    change h (τ + S) * _ = _ * (h (τ + S) * _)
    have he : Complex.exp (-(I * w * (S : ℂ))) = Complex.exp (I * w * (τ : ℂ)) *
        Complex.exp (-(I * w * ((τ + S : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  simp only [pulseAmplitude]
  rw [hsub, integral_const_mul]
  ring

theorem pulseField_shift (τ σ : ℝ) (h : CompactPulse) (x Y : ℝ) :
    pulseField (h.shift τ) σ x Y = pulseField h (τ + σ) x Y := by
  have hI : imageField (h.shift τ) σ x Y = imageField h (τ + σ) x Y := by
    simp only [imageField, imageTerm, pulseF]
    congr 2
    funext p
    change _ * h (τ + (σ + _)) = _ * h (τ + σ + _)
    rw [add_assoc]
  rw [pulseField, pulseField, hI, meanCoefficient, meanCoefficient, pulseAmplitude_shift]
  have hI2 : I * (-I * (1 / 2)) = (1 / 2 : ℂ) := by linear_combination (-1 / 2 : ℂ) * I_sq
  rw [hI2]
  have he : Complex.exp ((1 / 2 : ℂ) * (τ : ℂ)) * Complex.exp ((σ : ℂ) / 2) =
      Complex.exp (((τ + σ : ℝ) : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

theorem pulseL2_shift (τ σ : ℝ) (h : CompactPulse) (N : ℕ) :
    pulseL2 (h.shift τ) σ N = pulseL2 h (τ + σ) N := by
  apply Lp.ext
  filter_upwards [pulseL2_coeFn (h.shift τ) σ N, pulseL2_coeFn h (τ + σ) N] with z a1 a2
  rw [a1, a2, pulseField_shift]

end CompactPulse

/-! ### The pulses as a vector space -/

/-- The space of pulses. -/
def pulseSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hx => ⟨contDiff_const.smul hx.1, hx.2.smul_left (f := fun _ => c)⟩

/-- A vector of the space as a pulse. -/
def toPulse (f : pulseSpace) : CompactPulse := ⟨f.1, f.2.1, f.2.2⟩

/-- A pulse as a vector of the space. -/
def ofPulse (h : CompactPulse) : pulseSpace := ⟨h.toFun, h.smooth, h.compact⟩

/-- The field at time `τ` as a linear map on pulses. -/
def fieldAt (τ : ℝ) : pulseSpace →ₗ[ℂ] DeckL2 0 where
  toFun f := pulseL2 (toPulse f) τ 0
  map_add' f g := by
    have h1 := pulseL2_lin (k := toPulse (f + g)) (h := toPulse f) (g := toPulse g) 1
      (fun S => by simp [toPulse]) τ 0
    rw [h1, one_smul]
  map_smul' c f := by
    have h0 : (0 : pulseSpace) = 0 := rfl
    have hz : pulseL2 (toPulse 0) τ 0 = 0 := by
      apply Lp.ext
      have hF : ∀ x Y : ℝ, 0 < Y → pulseField (toPulse (0 : pulseSpace)) τ x Y = 0 := fun x Y hY => by
        have := pulseField_lin (k := toPulse (0 : pulseSpace)) (h := toPulse (0 : pulseSpace))
          (g := toPulse (0 : pulseSpace)) 1 (fun S => by simp [toPulse]) τ x hY
        simpa using this
      filter_upwards [pulseL2_coeFn (toPulse (0 : pulseSpace)) τ 0, Lp.coeFn_zero (DeckSpace 0) 2 cellMeasure]
        with z a1 a2
      rw [a1, a2, hF z.re z.im z.im_pos]
      simp
    have h1 := pulseL2_lin (k := toPulse (c • f)) (h := toPulse f) (g := toPulse 0) c
      (fun S => by simp [toPulse]) τ 0
    rw [h1, hz, add_zero]
    rfl

theorem fieldAt_ofPulse (τ : ℝ) (h : CompactPulse) : fieldAt τ (ofPulse h) = pulseL2 h τ 0 := rfl

theorem toPulse_ofPulse (h : CompactPulse) : toPulse (ofPulse h) = h := rfl

/-- The even part of the field. -/
def evenField (τ : ℝ) : pulseSpace →ₗ[ℂ] DeckL2 0 := (1 / 2 : ℂ) • (fieldAt τ + fieldAt (-τ))

theorem norm_evenField_le (τ : ℝ) (f : pulseSpace) : ‖evenField τ f‖ ≤ ‖fieldAt 0 f‖ :=
  norm_even_pulseL2_le (toPulse f) τ

/-- **The Eisenstein channel of the horizon**: the closure of the fields of the pulses. -/
def horizonChannel : Submodule ℂ (DeckL2 0) := (LinearMap.range (fieldAt 0)).topologicalClosure

theorem isClosed_horizonChannel : IsClosed (horizonChannel : Set (DeckL2 0)) :=
  Submodule.isClosed_topologicalClosure _

theorem fieldAt_mem (τ : ℝ) (f : pulseSpace) : fieldAt τ f ∈ horizonChannel := by
  have h1 : fieldAt τ f = fieldAt 0 (ofPulse ((toPulse f).shift τ)) := by
    rw [fieldAt_ofPulse, CompactPulse.pulseL2_shift, add_zero]
    rfl
  rw [h1]
  exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)

/-- The closed-set principle on the channel. -/
theorem horizonChannel_induction {P : DeckL2 0 → Prop} (hP : IsClosed {x | P x})
    (hbase : ∀ f, P (fieldAt 0 f)) {x : DeckL2 0} (hx : x ∈ horizonChannel) : P x := by
  have hsub : (horizonChannel : Set (DeckL2 0)) ⊆ {x | P x} := by
    change ((LinearMap.range (fieldAt 0)).topologicalClosure : Set (DeckL2 0)) ⊆ _
    rw [Submodule.topologicalClosure_coe]
    refine closure_minimal ?_ hP
    rintro _ ⟨f, rfl⟩
    exact hbase f
  exact hsub hx

/-! ### The cosine family -/

/-- **The cosine family of the Eisenstein channel.** -/
def channelCos (τ : ℝ) : DeckL2 0 →L[ℂ] DeckL2 0 :=
  Classical.choose (exists_contraction_of_norm_le (fieldAt 0) (evenField τ) (norm_evenField_le τ))

theorem norm_channelCos_le (τ : ℝ) (x : DeckL2 0) : ‖channelCos τ x‖ ≤ ‖x‖ :=
  (Classical.choose_spec (exists_contraction_of_norm_le (fieldAt 0) (evenField τ)
    (norm_evenField_le τ))).1 x

theorem channelCos_field (τ : ℝ) (f : pulseSpace) : channelCos τ (fieldAt 0 f) = evenField τ f :=
  (Classical.choose_spec (exists_contraction_of_norm_le (fieldAt 0) (evenField τ)
    (norm_evenField_le τ))).2 f

/-- **On a pulse the family is the average of the two time translates.** -/
theorem channelCos_pulse (τ : ℝ) (h : CompactPulse) :
    channelCos τ (pulseL2 h 0 0) = (1 / 2 : ℂ) • (pulseL2 h τ 0 + pulseL2 h (-τ) 0) :=
  channelCos_field τ (ofPulse h)

theorem channelCos_field_at (τ σ : ℝ) (f : pulseSpace) :
    channelCos τ (fieldAt σ f) = (1 / 2 : ℂ) • (fieldAt (σ + τ) f + fieldAt (σ + -τ) f) := by
  have h1 : fieldAt σ f = fieldAt 0 (ofPulse ((toPulse f).shift σ)) := by
    rw [fieldAt_ofPulse, CompactPulse.pulseL2_shift, add_zero]
    rfl
  rw [h1, channelCos_field]
  change (1 / 2 : ℂ) • (fieldAt τ _ + fieldAt (-τ) _) = _
  rw [fieldAt_ofPulse, fieldAt_ofPulse, CompactPulse.pulseL2_shift, CompactPulse.pulseL2_shift]
  rfl

theorem channelCos_zero {x : DeckL2 0} (hx : x ∈ horizonChannel) : channelCos 0 x = x := by
  refine horizonChannel_induction (P := fun x => channelCos 0 x = x)
    (isClosed_eq (channelCos 0).continuous continuous_id) (fun f => ?_) hx
  rw [channelCos_field]
  change (1 / 2 : ℂ) • (fieldAt 0 f + fieldAt (-0) f) = _
  rw [neg_zero, ← two_smul ℂ (fieldAt 0 f), smul_smul]
  norm_num

/-- The family preserves the channel. -/
theorem channelCos_mem (τ : ℝ) {x : DeckL2 0} (hx : x ∈ horizonChannel) :
    channelCos τ x ∈ horizonChannel := by
  refine horizonChannel_induction (P := fun x => channelCos τ x ∈ horizonChannel)
    (isClosed_horizonChannel.preimage (channelCos τ).continuous) (fun f => ?_) hx
  rw [channelCos_field]
  change (1 / 2 : ℂ) • (fieldAt τ f + fieldAt (-τ) f) ∈ _
  exact horizonChannel.smul_mem _ (horizonChannel.add_mem (fieldAt_mem _ _) (fieldAt_mem _ _))

/-- **D'Alembert's law on the channel.** -/
theorem channelCos_add_sub (τ σ : ℝ) {x : DeckL2 0} (hx : x ∈ horizonChannel) :
    channelCos (τ + σ) x + channelCos (τ - σ) x = (2 : ℂ) • channelCos τ (channelCos σ x) := by
  refine horizonChannel_induction
    (P := fun x => channelCos (τ + σ) x + channelCos (τ - σ) x = (2 : ℂ) • channelCos τ (channelCos σ x))
    (isClosed_eq ((channelCos _).continuous.add (channelCos _).continuous)
      (((channelCos τ).continuous.comp (channelCos σ).continuous).const_smul (2 : ℂ))) (fun f => ?_) hx
  rw [channelCos_field, channelCos_field, channelCos_field]
  change (1 / 2 : ℂ) • (fieldAt (τ + σ) f + fieldAt (-(τ + σ)) f) +
    (1 / 2 : ℂ) • (fieldAt (τ - σ) f + fieldAt (-(τ - σ)) f) =
    (2 : ℂ) • channelCos τ ((1 / 2 : ℂ) • (fieldAt σ f + fieldAt (-σ) f))
  rw [map_smul, map_add, channelCos_field_at, channelCos_field_at]
  have e1 : σ + τ = τ + σ := add_comm _ _
  have e2 : σ + -τ = -(τ - σ) := by ring
  have e3 : -σ + τ = τ - σ := by ring
  have e4 : -σ + -τ = -(τ + σ) := by ring
  rw [e1, e2, e3, e4]
  module

/-! ### Strong continuity -/

/-- The field is continuous in time, in `L²`. -/
theorem continuous_pulseL2 (h : CompactPulse) : Continuous fun τ : ℝ => pulseL2 h τ 0 := by
  refine continuous_iff_continuousAt.mpr fun τ₀ => ?_
  obtain ⟨Ca, hCa, ha⟩ := h.rapidAmplitude.exists_mul_poly_le 0 0
  have hN : 2 ≤ 2 := le_rfl
  have hscat : ∀ t : ℝ, ‖scatExt (onesVec 2) (_root_.RHTower.linePt (-t))‖ = ‖onesVec 2‖ := fun t =>
    norm_scatExt_line hN isCuspVec_onesVec (-t)
  have hat : ∀ s : ℝ, ‖pulseAmplitude h (s : ℂ)‖ ≤ Ca * ((1 + |s|) ^ 2)⁻¹ := fun s => by
    have := ha (s : ℂ) (by simp)
    simpa using this
  -- the transform varies continuously, with an integrable majorant
  set G : ℝ → ℝ := fun t => (2 * (4 * Real.pi * Ca * ‖onesVec 2‖ * ((1 + |t|) ^ 2)⁻¹)) ^ 2 with hG
  have hGi : Integrable G := by
    have hb : Integrable fun t : ℝ => (2 * (4 * Real.pi * Ca * ‖onesVec 2‖)) ^ 2 * ((1 + |t|) ^ 2)⁻¹ :=
      integrable_inv_one_add_abs_sq.const_mul _
    have hc : Continuous G := by
      refine (continuous_const.mul (continuous_const.mul
        (Continuous.inv₀ (by fun_prop) fun t => by positivity))).pow 2
    refine hb.mono' hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have h0 : 0 ≤ ((1 + |t|) ^ 2)⁻¹ := by positivity
    have h1 : ((1 + |t|) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [abs_nonneg t]))
    simp only [hG]
    rw [Real.norm_of_nonneg (by positivity)]
    have e : (2 * (4 * Real.pi * Ca * ‖onesVec 2‖ * ((1 + |t|) ^ 2)⁻¹)) ^ 2 =
        (2 * (4 * Real.pi * Ca * ‖onesVec 2‖)) ^ 2 * (((1 + |t|) ^ 2)⁻¹ * ((1 + |t|) ^ 2)⁻¹) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((1 + |t|) ^ 2)⁻¹ * ((1 + |t|) ^ 2)⁻¹ ≤ ((1 + |t|) ^ 2)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  have hbound : ∀ (τ t : ℝ), ‖eisTransform (h.pulseProfile τ) (onesVec 2) t‖ ≤
      4 * Real.pi * Ca * ‖onesVec 2‖ * ((1 + |t|) ^ 2)⁻¹ := fun τ t => by
    rw [eisTransform_pulse]
    have e1 : ‖Complex.exp ((t : ℂ) * I * (τ : ℂ))‖ = 1 := by
      have : (t : ℂ) * I * (τ : ℂ) = ((t * τ : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have e2 : ‖Complex.exp (-((t : ℂ) * I * (τ : ℂ)))‖ = 1 := by
      have : -((t : ℂ) * I * (τ : ℂ)) = ((-(t * τ) : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hkey : ∀ (c x : ℂ) (v : DeckSpace 2), ‖c‖ = 1 →
        ‖((2 : ℂ) * (Real.pi : ℂ) * c * x) • v‖ = 2 * Real.pi * (‖x‖ * ‖v‖) := fun c x v hc => by
      rw [norm_smul, norm_mul, norm_mul, norm_mul, hc, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      simp only [Complex.norm_ofNat, mul_one]
      ring
    refine (norm_add_le _ _).trans ?_
    rw [hkey _ _ _ e1, hkey _ _ _ e2, hscat t]
    have h3 := hat t
    have h4 := hat (-t)
    rw [abs_neg] at h4
    have hon := norm_nonneg (onesVec 2)
    have hπ := Real.pi_pos
    have h5 := mul_le_mul_of_nonneg_right h3 hon
    have h6 := mul_le_mul_of_nonneg_right h4 hon
    have h7 := mul_le_mul_of_nonneg_left (add_le_add h5 h6) (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hcontT : ∀ t : ℝ, Continuous fun τ : ℝ => eisTransform (h.pulseProfile τ) (onesVec 2) t := fun t => by
    simp_rw [eisTransform_pulse]
    fun_prop
  have hlim : Tendsto (fun τ : ℝ => ∫ t : ℝ, ‖eisTransform (h.pulseProfile τ) (onesVec 2) t -
      eisTransform (h.pulseProfile τ₀) (onesVec 2) t‖ ^ 2) (𝓝 τ₀) (𝓝 (∫ _t : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence G (Eventually.of_forall fun τ => ?_)
      (Eventually.of_forall fun τ => Eventually.of_forall fun t => ?_) hGi
      (Eventually.of_forall fun t => ?_)
    · have h1 := (memLp_eisTransform hN (h.pulseProfile τ) (h.contDiff_pulseProfile τ) isCuspVec_onesVec).sub
        (memLp_eisTransform hN (h.pulseProfile τ₀) (h.contDiff_pulseProfile τ₀) isCuspVec_onesVec)
      exact (h1.aestronglyMeasurable.norm.pow 2)
    · rw [Real.norm_of_nonneg (by positivity)]
      simp only [hG]
      have h1 := (norm_sub_le _ _).trans (add_le_add (hbound τ t) (hbound τ₀ t))
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      refine h2.trans (le_of_eq ?_)
      ring
    · have hc : Continuous fun τ : ℝ => ‖eisTransform (h.pulseProfile τ) (onesVec 2) t -
          eisTransform (h.pulseProfile τ₀) (onesVec 2) t‖ ^ 2 :=
        (((hcontT t).sub continuous_const).norm).pow 2
      have := hc.tendsto τ₀
      simpa using this
  rw [integral_zero] at hlim
  -- the Parseval identity for the difference at level two
  have hdiff : ∀ τ : ℝ, ‖pulseL2 h τ 2 - pulseL2 h τ₀ 2‖ ^ 2 =
      Real.pi⁻¹ * ∫ t : ℝ, ‖eisTransform (h.pulseProfile τ) (onesVec 2) t -
        eisTransform (h.pulseProfile τ₀) (onesVec 2) t‖ ^ 2 := fun τ => by
    have hin : ⟪pulseL2 h τ 2 - pulseL2 h τ₀ 2, onesL2 2⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_pulseL2_ones, inner_pulseL2_ones, sub_zero]
    have h1 := norm_sq_of_inner_ones_eq_zero hN (pulseFE h τ 2 - pulseFE h τ₀ 2) hin
    have hT : eisTransformE hN (pulseFE h τ 2 - pulseFE h τ₀ 2) =
        genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2) := by
      rw [map_sub, eisTransformE_pulseFE, eisTransformE_pulseFE]
    have hL : ‖genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2)‖ ^ 2 =
        ∫ t : ℝ, ‖eisTransform (h.pulseProfile τ) (onesVec 2) t -
          eisTransform (h.pulseProfile τ₀) (onesVec 2) t‖ ^ 2 := by
      have hi := L2.inner_def (𝕜 := ℂ) (genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2))
        (genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2))
      rw [inner_self_eq_norm_sq_to_K] at hi
      simp_rw [inner_self_eq_norm_sq_to_K] at hi
      have hr : (∫ t : ℝ, ((‖((genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2) :
          Lp (DeckSpace 2) 2 (volume : Measure ℝ)) : ℝ → DeckSpace 2) t‖ ^ 2 : ℝ) : ℂ)) =
          ((∫ t : ℝ, ‖((genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2) :
            Lp (DeckSpace 2) 2 (volume : Measure ℝ)) : ℝ → DeckSpace 2) t‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
      have hc : ((‖genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2)‖ ^ 2 : ℝ) : ℂ) =
          ((∫ t : ℝ, ‖((genTrans hN (pulseGen h τ 2) - genTrans hN (pulseGen h τ₀ 2) :
            Lp (DeckSpace 2) 2 (volume : Measure ℝ)) : ℝ → DeckSpace 2) t‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hr]
        push_cast
        exact hi
      have hc' := Complex.ofReal_injective hc
      rw [hc']
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (genTrans hN (pulseGen h τ 2)) (genTrans hN (pulseGen h τ₀ 2)),
        genTrans_coeFn hN (pulseGen h τ 2), genTrans_coeFn hN (pulseGen h τ₀ 2)] with t a1 a2 a3
      rw [a1, Pi.sub_apply, a2, a3]
      rfl
    have hco : ((pulseFE h τ 2 - pulseFE h τ₀ 2 : eisSpace 2) : DeckL2 2) = pulseL2 h τ 2 - pulseL2 h τ₀ 2 := rfl
    rw [hco, hT, hL] at h1
    exact h1
  -- transfer to the modular horizon
  have htrans : ∀ τ : ℝ, ‖pulseL2 h τ 0 - pulseL2 h τ₀ 0‖ ^ 2 =
      (‖onesVec 0‖ ^ 2 / ‖onesVec 2‖ ^ 2) * ‖pulseL2 h τ 2 - pulseL2 h τ₀ 2‖ ^ 2 := fun τ => by
    have hae : ∀ N : ℕ, ((pulseL2 h τ N - pulseL2 h τ₀ N : DeckL2 N) : UpperHalfPlane → DeckSpace N)
        =ᵐ[cellMeasure] fun z => (2 * (pulseField h τ z.re z.im - pulseField h τ₀ z.re z.im)) • onesVec N := fun N => by
      filter_upwards [Lp.coeFn_sub (pulseL2 h τ N) (pulseL2 h τ₀ N), pulseL2_coeFn h τ N,
        pulseL2_coeFn h τ₀ N] with z a1 a2 a3
      rw [a1, Pi.sub_apply, a2, a3]
      module
    rw [norm_sq_of_ae (hae 0), norm_sq_of_ae (hae 2)]
    have hne : ‖onesVec 2‖ ≠ 0 := norm_ne_zero_iff.mpr (onesVec_ne_zero 2)
    field_simp
  have hzero : Tendsto (fun τ : ℝ => ‖pulseL2 h τ 0 - pulseL2 h τ₀ 0‖ ^ 2) (𝓝 τ₀) (𝓝 0) := by
    simp_rw [htrans, hdiff]
    have := (hlim.const_mul Real.pi⁻¹).const_mul (‖onesVec 0‖ ^ 2 / ‖onesVec 2‖ ^ 2)
    simpa using this
  have hroot : Tendsto (fun τ : ℝ => ‖pulseL2 h τ 0 - pulseL2 h τ₀ 0‖) (𝓝 τ₀) (𝓝 0) := by
    have h1 := hzero.sqrt
    simp only [Real.sqrt_zero] at h1
    refine h1.congr fun τ => ?_
    exact Real.sqrt_sq (norm_nonneg _)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hroot

/-- **Strong continuity on the channel.** -/
theorem continuous_channelCos {x : DeckL2 0} (hx : x ∈ horizonChannel) :
    Continuous fun τ : ℝ => channelCos τ x := by
  have hbase : ∀ f, Continuous fun τ : ℝ => channelCos τ (fieldAt 0 f) := fun f => by
    have h1 : (fun τ : ℝ => channelCos τ (fieldAt 0 f)) =
        fun τ => (1 / 2 : ℂ) • (fieldAt τ f + fieldAt (-τ) f) := by
      funext τ
      rw [channelCos_field]
      rfl
    rw [h1]
    have h2 := continuous_pulseL2 (toPulse f)
    have h3 : Continuous fun τ : ℝ => fieldAt τ f := h2
    exact ((h3.add (h3.comp continuous_neg)).const_smul (1 / 2 : ℂ))
  refine continuous_iff_continuousAt.mpr fun τ₀ => Metric.continuousAt_iff.mpr fun ε hε => ?_
  have hxc : x ∈ closure (LinearMap.range (fieldAt 0) : Set (DeckL2 0)) := by
    have h0 : x ∈ ((LinearMap.range (fieldAt 0)).topologicalClosure : Set (DeckL2 0)) := hx
    rwa [Submodule.topologicalClosure_coe] at h0
  obtain ⟨y, ⟨f, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp hxc (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp (hbase f).continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun τ hτ => ?_⟩
  have hsplit : ∀ σ : ℝ, dist (channelCos σ x) (channelCos σ (fieldAt 0 f)) < ε / 3 := fun σ => by
    rw [dist_eq_norm, ← map_sub]
    exact (norm_channelCos_le σ _).trans_lt (by rwa [dist_eq_norm] at hy)
  have h1 := hsplit τ
  have h2 := hδε hτ
  have h3 := hsplit τ₀
  rw [dist_comm] at h3
  calc dist (channelCos τ x) (channelCos τ₀ x)
      ≤ dist (channelCos τ x) (channelCos τ (fieldAt 0 f)) +
        (dist (channelCos τ (fieldAt 0 f)) (channelCos τ₀ (fieldAt 0 f)) +
          dist (channelCos τ₀ (fieldAt 0 f)) (channelCos τ₀ x)) :=
        (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ < ε := by linarith

end GaloisForLFunctions.BlackHoleRingdown

end
