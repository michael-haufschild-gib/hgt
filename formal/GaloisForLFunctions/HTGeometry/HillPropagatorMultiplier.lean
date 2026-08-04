import GaloisForLFunctions.HTGeometry.HillSpeedData
import GaloisForLFunctions.HTGeometry.WienerSymbolMultiplication

/-!
# The propagator as a multiplier on the frequency space

The Duhamel equation of the driven evolution lives in the Banach space of bounded continuous
functions of the frequency, and its kernel multiplies by the propagator. This file packages the
symbols as elements of that space and proves what the Volterra theory consumes: a bound on every
window of times, and — the delicate point — continuity of the family in the times, in the *sup* norm.

Continuity is not automatic: the undamped cosine family is not sup-norm continuous, since at a fixed
time difference the oscillation `cos(tω)` covers a full period as the frequency grows. What saves
both families here is that their time derivatives are bounded uniformly in the frequency: the free
term because it carries one power of damping, and the propagator because the frequency of the
velocity cancels against the frequency gained by the sine.
-/

namespace GaloisForLFunctions.HTGeometry

namespace HillSpeed

open BoundedContinuousFunction

section Multiplier

variable {E : Type*} [NormedAddCommGroup E] (a : HillSpeed)

/-- The pointwise size of the propagator symbol at a pair of times. -/
noncomputable def propNorm (a : HillSpeed) (t s : ℝ) : ℝ :=
  2 * (a.ratio * a.mass⁻¹) * (Real.exp (a.logBound * |t|) * Real.exp (a.logBound * |s|))

/-- The pointwise size of the damped free symbol at a time. -/
noncomputable def coscNorm (a : HillSpeed) (t : ℝ) : ℝ :=
  a.ratio * a.mass⁻¹ * Real.exp (a.logBound * |t|)

theorem propNorm_nonneg (t s : ℝ) : 0 ≤ a.propNorm t s := by
  have h1 : (0 : ℝ) ≤ a.ratio * a.mass⁻¹ :=
    mul_nonneg a.ratio_nonneg (le_of_lt (inv_pos.mpr a.mass_pos))
  rw [propNorm]
  positivity

theorem coscNorm_nonneg (t : ℝ) : 0 ≤ a.coscNorm t := by
  have h1 : (0 : ℝ) ≤ a.ratio * a.mass⁻¹ :=
    mul_nonneg a.ratio_nonneg (le_of_lt (inv_pos.mpr a.mass_pos))
  rw [coscNorm]
  positivity

/-- The propagator symbol, as a bounded continuous function of the frequency. -/
noncomputable def propBCF (a : HillSpeed) (t s : ℝ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ : E => ((a.propSymbol t s ξ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (a.continuous_propSymbol_freq t s)) (a.propNorm t s)
    (fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact a.abs_propSymbol_le t s ξ)

/-- The damped free symbol, as a bounded continuous function of the frequency. -/
noncomputable def coscBCF (a : HillSpeed) (t : ℝ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ : E => ((a.coscSymbol t ξ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (a.continuous_coscSymbol_freq t)) (a.coscNorm t)
    (fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact a.abs_coscSymbol_le t ξ)

theorem propBCF_apply (t s : ℝ) (ξ : E) :
    a.propBCF t s ξ = ((a.propSymbol t s ξ : ℝ) : ℂ) := rfl

theorem coscBCF_apply (t : ℝ) (ξ : E) :
    a.coscBCF t ξ = ((a.coscSymbol t ξ : ℝ) : ℂ) := rfl

theorem norm_propBCF_le_window {T t s : ℝ} (ht : |t| ≤ T) (hs : |s| ≤ T) :
    ‖a.propBCF (E := E) t s‖ ≤ a.propSize T := by
  refine (BoundedContinuousFunction.norm_le (a.propSize_nonneg T)).mpr fun ξ => ?_
  rw [propBCF_apply, Complex.norm_real, Real.norm_eq_abs]
  exact a.abs_propSymbol_le_window ht hs ξ

theorem norm_coscBCF_le_window {T t : ℝ} (ht : |t| ≤ T) :
    ‖a.coscBCF (E := E) t‖ ≤ a.coscSize T := by
  refine (BoundedContinuousFunction.norm_le (a.coscSize_nonneg T)).mpr fun ξ => ?_
  rw [coscBCF_apply, Complex.norm_real, Real.norm_eq_abs]
  exact a.abs_coscSymbol_le_window ht ξ

/-! ## Lipschitz continuity in the times -/

theorem mem_Icc_of_abs_le {T t : ℝ} (ht : |t| ≤ T) : t ∈ Set.Icc (-T) T := by
  have hpair := abs_le.mp ht
  exact ⟨hpair.1, hpair.2⟩

theorem abs_propSymbol_sub_time_le {T t t' s : ℝ} (ht : |t| ≤ T) (ht' : |t'| ≤ T) (hs : |s| ≤ T)
    (ξ : E) : |a.propSymbol t s ξ - a.propSymbol t' s ξ| ≤ a.propLip T * |t - t'| := by
  have hbound : ∀ x ∈ Set.Icc (-T) T, ‖a.propSymbolTimeDeriv x s ξ‖ ≤ a.propLip T := by
    intro x hx
    have hxT : |x| ≤ T := abs_le.mpr ⟨hx.1, hx.2⟩
    rw [Real.norm_eq_abs]
    exact a.abs_propSymbolTimeDeriv_le_window hxT hs ξ
  have hderiv : ∀ x ∈ Set.Icc (-T) T,
      HasDerivWithinAt (fun r : ℝ => a.propSymbol r s ξ) (a.propSymbolTimeDeriv x s ξ)
        (Set.Icc (-T) T) x := fun x _ =>
    (a.hasDerivAt_propSymbol_time s ξ x).hasDerivWithinAt
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc (-T) T) (mem_Icc_of_abs_le ht') (mem_Icc_of_abs_le ht)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmain
  exact hmain

theorem abs_propSymbol_sub_base_le {T t s s' : ℝ} (ht : |t| ≤ T) (hs : |s| ≤ T) (hs' : |s'| ≤ T)
    (ξ : E) : |a.propSymbol t s ξ - a.propSymbol t s' ξ| ≤ a.propLip T * |s - s'| := by
  have hbound : ∀ x ∈ Set.Icc (-T) T, ‖a.propSymbolBaseDeriv t x ξ‖ ≤ a.propLip T := by
    intro x hx
    have hxT : |x| ≤ T := abs_le.mpr ⟨hx.1, hx.2⟩
    rw [Real.norm_eq_abs]
    exact a.abs_propSymbolBaseDeriv_le_window ht hxT ξ
  have hderiv : ∀ x ∈ Set.Icc (-T) T,
      HasDerivWithinAt (fun r : ℝ => a.propSymbol t r ξ) (a.propSymbolBaseDeriv t x ξ)
        (Set.Icc (-T) T) x := fun x _ =>
    (a.hasDerivAt_propSymbol_base t ξ x).hasDerivWithinAt
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc (-T) T) (mem_Icc_of_abs_le hs') (mem_Icc_of_abs_le hs)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmain
  exact hmain

theorem abs_coscSymbol_sub_le {T t t' : ℝ} (ht : |t| ≤ T) (ht' : |t'| ≤ T) (ξ : E) :
    |a.coscSymbol t ξ - a.coscSymbol t' ξ| ≤ Real.exp (a.logBound * T) * |t - t'| := by
  have hbound : ∀ x ∈ Set.Icc (-T) T, ‖a.coscSymbolDeriv x ξ‖ ≤ Real.exp (a.logBound * T) := by
    intro x hx
    have hxT : |x| ≤ T := abs_le.mpr ⟨hx.1, hx.2⟩
    rw [Real.norm_eq_abs]
    exact a.abs_coscSymbolDeriv_le_window hxT ξ
  have hderiv : ∀ x ∈ Set.Icc (-T) T,
      HasDerivWithinAt (fun r : ℝ => a.coscSymbol r ξ) (a.coscSymbolDeriv x ξ)
        (Set.Icc (-T) T) x := fun x _ => (a.hasDerivAt_coscSymbol ξ x).hasDerivWithinAt
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc (-T) T) (mem_Icc_of_abs_le ht') (mem_Icc_of_abs_le ht)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmain
  exact hmain

theorem norm_propBCF_sub_time_le {T t t' s : ℝ} (ht : |t| ≤ T) (ht' : |t'| ≤ T) (hs : |s| ≤ T) :
    ‖a.propBCF (E := E) t s - a.propBCF t' s‖ ≤ a.propLip T * |t - t'| := by
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (a.propLip_nonneg T) (abs_nonneg _))).mpr fun ξ => ?_
  have hval : (a.propBCF (E := E) t s - a.propBCF (E := E) t' s) ξ
      = ((a.propSymbol t s ξ - a.propSymbol t' s ξ : ℝ) : ℂ) := by
    rw [BoundedContinuousFunction.sub_apply, propBCF_apply, propBCF_apply, Complex.ofReal_sub]
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  exact a.abs_propSymbol_sub_time_le ht ht' hs ξ

theorem norm_propBCF_sub_base_le {T t s s' : ℝ} (ht : |t| ≤ T) (hs : |s| ≤ T) (hs' : |s'| ≤ T) :
    ‖a.propBCF (E := E) t s - a.propBCF t s'‖ ≤ a.propLip T * |s - s'| := by
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (a.propLip_nonneg T) (abs_nonneg _))).mpr fun ξ => ?_
  have hval : (a.propBCF (E := E) t s - a.propBCF (E := E) t s') ξ
      = ((a.propSymbol t s ξ - a.propSymbol t s' ξ : ℝ) : ℂ) := by
    rw [BoundedContinuousFunction.sub_apply, propBCF_apply, propBCF_apply, Complex.ofReal_sub]
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  exact a.abs_propSymbol_sub_base_le ht hs hs' ξ

theorem norm_coscBCF_sub_le {T t t' : ℝ} (ht : |t| ≤ T) (ht' : |t'| ≤ T) :
    ‖a.coscBCF (E := E) t - a.coscBCF t'‖ ≤ Real.exp (a.logBound * T) * |t - t'| := by
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (le_of_lt (Real.exp_pos _)) (abs_nonneg _))).mpr fun ξ => ?_
  have hval : (a.coscBCF (E := E) t - a.coscBCF (E := E) t') ξ
      = ((a.coscSymbol t ξ - a.coscSymbol t' ξ : ℝ) : ℂ) := by
    rw [BoundedContinuousFunction.sub_apply, coscBCF_apply, coscBCF_apply, Complex.ofReal_sub]
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  exact a.abs_coscSymbol_sub_le ht ht' ξ

/-! ## Continuity in the times -/

theorem continuous_coscBCF : Continuous fun t : ℝ => a.coscBCF (E := E) t := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  set T : ℝ := |t₀| + 1 with hT
  have hTpos : 0 < T := by
    rw [hT]
    positivity
  have hW : {t : ℝ | |t| ≤ T} ∈ nhds t₀ := by
    have hopen : IsOpen {t : ℝ | |t| < T} := isOpen_lt continuous_abs continuous_const
    have hmem : t₀ ∈ {t : ℝ | |t| < T} := by
      simp only [Set.mem_setOf_eq, hT]
      linarith
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) fun t ht => ?_
    simp only [Set.mem_setOf_eq] at ht ⊢
    exact le_of_lt ht
  have hlip : LipschitzOnWith (Real.toNNReal (Real.exp (a.logBound * T)))
      (fun t : ℝ => a.coscBCF (E := E) t) {t : ℝ | |t| ≤ T} := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _)), dist_eq_norm, Real.dist_eq]
    exact a.norm_coscBCF_sub_le hp hq
  exact hlip.continuousOn.continuousAt hW

theorem continuous_propBCF : Continuous fun p : ℝ × ℝ => a.propBCF (E := E) p.1 p.2 := by
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  obtain ⟨t₀, s₀⟩ := p₀
  set T : ℝ := |t₀| + |s₀| + 1 with hT
  have hW : {p : ℝ × ℝ | |p.1| ≤ T ∧ |p.2| ≤ T} ∈ nhds ((t₀, s₀) : ℝ × ℝ) := by
    have hopen : IsOpen {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T} :=
      (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
    have hmem : ((t₀, s₀) : ℝ × ℝ) ∈ {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T} := by
      constructor
      · show |t₀| < T
        rw [hT]
        have := abs_nonneg s₀
        linarith
      · show |s₀| < T
        rw [hT]
        have := abs_nonneg t₀
        linarith
    exact Filter.mem_of_superset (hopen.mem_nhds hmem)
      fun p hp => ⟨le_of_lt hp.1, le_of_lt hp.2⟩
  have hlip : LipschitzOnWith (Real.toNNReal (2 * a.propLip T))
      (fun p : ℝ × ℝ => a.propBCF (E := E) p.1 p.2) {p : ℝ × ℝ | |p.1| ≤ T ∧ |p.2| ≤ T} := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    have hLnn : (0 : ℝ) ≤ 2 * a.propLip T := by
      have := a.propLip_nonneg T
      linarith
    rw [Real.coe_toNNReal _ hLnn, dist_eq_norm]
    have hsplit : a.propBCF (E := E) p.1 p.2 - a.propBCF (E := E) q.1 q.2
        = (a.propBCF (E := E) p.1 p.2 - a.propBCF (E := E) q.1 p.2) +
          (a.propBCF (E := E) q.1 p.2 - a.propBCF (E := E) q.1 q.2) := by
      abel
    have h1 := a.norm_propBCF_sub_time_le (E := E) hp.1 hq.1 hp.2
    have h2 := a.norm_propBCF_sub_base_le (E := E) hq.1 hp.2 hq.2
    have hdist1 : |p.1 - q.1| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hdist2 : |p.2 - q.2| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    calc ‖a.propBCF (E := E) p.1 p.2 - a.propBCF (E := E) q.1 q.2‖
        ≤ ‖a.propBCF (E := E) p.1 p.2 - a.propBCF (E := E) q.1 p.2‖ +
            ‖a.propBCF (E := E) q.1 p.2 - a.propBCF (E := E) q.1 q.2‖ := by
          rw [hsplit]
          exact norm_add_le _ _
      _ ≤ a.propLip T * |p.1 - q.1| + a.propLip T * |p.2 - q.2| := add_le_add h1 h2
      _ ≤ a.propLip T * dist p q + a.propLip T * dist p q :=
          add_le_add (mul_le_mul_of_nonneg_left hdist1 (a.propLip_nonneg T))
            (mul_le_mul_of_nonneg_left hdist2 (a.propLip_nonneg T))
      _ = 2 * a.propLip T * dist p q := by ring
  exact hlip.continuousOn.continuousAt hW

end Multiplier

end HillSpeed

end GaloisForLFunctions.HTGeometry
