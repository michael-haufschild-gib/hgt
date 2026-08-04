import GaloisForLFunctions.HTGeometry.FiniteRegularitySlice

/-!
# The decay functional of a curve of slices is bounded and Lipschitz

A potential of finite regularity, cut off to a compactly supported function of the event, gives a
curve of spatial potentials whose decay functional must be bounded uniformly in time and Lipschitz
in time. Both follow from the corresponding statements for the full derivatives of the cut-off
function: the derivative of a slice is dominated by the derivative of the function at the same
event, the derivatives are continuous with compact support, and an `L¹` norm over a fixed compact
set is bounded by the supremum times the volume.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The `L¹` norm over a compact support -/

theorem integral_norm_le_of_support_gen {F : Type*} [NormedAddCommGroup F] {f : E → F}
    {K : Set E} (hKmeas : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    (hf : Integrable f (volume : Measure E)) (hsupp : ∀ x : E, x ∉ K → f x = 0) {C : ℝ}
    (hC : ∀ x : E, ‖f x‖ ≤ C) :
    (∫ x : E, ‖f x‖) ≤ C * (volume K).toReal := by
  have hzero : ∀ x : E, x ∉ K → ‖f x‖ = 0 := by
    intro x hx
    rw [hsupp x hx, norm_zero]
  have hrestrict : (∫ x : E, ‖f x‖) = ∫ x in K, ‖f x‖ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [hrestrict]
  have hmono : (∫ x in K, ‖f x‖) ≤ ∫ _x in K, C := by
    refine setIntegral_mono_on hf.norm.integrableOn ?_ hKmeas fun x _ => hC x
    exact integrableOn_const hKfin
  refine hmono.trans_eq ?_
  rw [setIntegral_const, smul_eq_mul, measureReal_def]
  ring

theorem derivL1_le_of_bound {i : ℕ} {n : WithTop ℕ∞} {g : E → ℂ} (hg : ContDiff ℝ n g)
    (hi : (i : WithTop ℕ∞) ≤ n) {K : Set E} (hKcompact : IsCompact K) (hKmeas : MeasurableSet K)
    (hzero : ∀ x : E, x ∉ K → g x = 0) {B : ℝ} (hB : ∀ x : E, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    derivL1 i g ≤ B * (volume K).toReal := by
  have hsupp : HasCompactSupport g := HasCompactSupport.intro hKcompact hzero
  have hcont : Continuous (iteratedFDeriv ℝ i g) := hg.continuous_iteratedFDeriv hi
  have hint : Integrable (iteratedFDeriv ℝ i g) (volume : Measure E) :=
    hcont.integrable_of_hasCompactSupport (hsupp.iteratedFDeriv i)
  have hzero' : ∀ x : E, x ∉ K → iteratedFDeriv ℝ i g x = 0 := by
    intro x hx
    have hev : g =ᶠ[nhds x] fun _ : E => (0 : ℂ) :=
      Filter.eventually_of_mem (hKcompact.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hzero y hy
    have hiter := Filter.EventuallyEq.iteratedFDeriv ℝ hev i
    rw [hiter.self_of_nhds]
    simp
  exact integral_norm_le_of_support_gen hKmeas hKcompact.measure_lt_top.ne hint hzero' hB

/-! ## The two bounds -/

section Bounds

variable {j : ℕ} {H : ℝ × E → ℂ}

/-- **The decay functional of the slices of a compactly supported `C^{2j+1}` function of the event
is bounded uniformly in time and Lipschitz in time.** -/
theorem exists_contDiffDecay_bounds
    (hH : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) H) (hsupp : HasCompactSupport H)
    {K : Set E} (hKcompact : IsCompact K) (hKmeas : MeasurableSet K)
    (hzero : ∀ (t : ℝ) (x : E), x ∉ K → H (t, x) = 0) :
    ∃ M L : ℝ, 0 ≤ L ∧ (∀ t : ℝ, contDiffDecay j (fun x : E => H (t, x)) ≤ M) ∧
      ∀ t t' : ℝ, contDiffDecay j ((fun x : E => H (t, x)) - fun x : E => H (t', x))
        ≤ L * |t - t'| := by
  have hvol : (0 : ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
  -- the two orders that enter the decay functional
  have horder : ∀ i : ℕ, i ≤ 2 * j → ((i : ℕ) : WithTop ℕ∞) ≤ ((2 * j + 1 : ℕ) : WithTop ℕ∞) := by
    intro i hi
    exact_mod_cast Nat.le_succ_of_le hi
  have hsliceCd : ∀ t : ℝ, ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) fun x : E => H (t, x) := by
    intro t
    have hmap : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) fun x : E => ((t, x) : ℝ × E) := by
      fun_prop
    exact hH.comp hmap
  have hsliceZero : ∀ t : ℝ, ∀ x : E, x ∉ K → H (t, x) = 0 := fun t x hx => hzero t x hx
  -- sup bounds for the full derivatives
  have hsup : ∀ i : ℕ, i ≤ 2 * j → ∃ C : ℝ, ∀ p : ℝ × E, ‖iteratedFDeriv ℝ i H p‖ ≤ C := by
    intro i hi
    have hcont : Continuous (iteratedFDeriv ℝ i H) :=
      hH.continuous_iteratedFDeriv (horder i hi)
    exact hcont.bounded_above_of_compact_support (hsupp.iteratedFDeriv i)
  -- Lipschitz bounds in time for the full derivatives
  have hlip : ∀ i : ℕ, i ≤ 2 * j → ∃ L : ℝ, 0 ≤ L ∧ ∀ (t t' : ℝ) (x : E),
      ‖iteratedFDeriv ℝ i H (t, x) - iteratedFDeriv ℝ i H (t', x)‖ ≤ L * |t - t'| := by
    intro i hi
    have hcd : ContDiff ℝ (1 : ℕ) (iteratedFDeriv ℝ i H) := by
      refine hH.iteratedFDeriv_right ?_
      have : ((1 : ℕ) : WithTop ℕ∞) + ((i : ℕ) : WithTop ℕ∞)
          = ((1 + i : ℕ) : WithTop ℕ∞) := by push_cast; ring
      rw [this]
      exact_mod_cast by omega
    exact exists_lipschitz_time hcd (hsupp.iteratedFDeriv i)
  obtain ⟨C₀, hC₀⟩ := hsup 0 (Nat.zero_le _)
  obtain ⟨C₁, hC₁⟩ := hsup (2 * j) le_rfl
  obtain ⟨L₀, hL₀0, hL₀⟩ := hlip 0 (Nat.zero_le _)
  obtain ⟨L₁, hL₁0, hL₁⟩ := hlip (2 * j) le_rfl
  set c : ℝ := ((2 * Real.pi) ^ (2 * j))⁻¹ with hc
  have hc0 : (0 : ℝ) ≤ c := by positivity
  refine ⟨2 ^ j * (C₀ * (volume K).toReal + c * (C₁ * (volume K).toReal)),
    2 ^ j * (L₀ * (volume K).toReal + c * (L₁ * (volume K).toReal)),
    by positivity, fun t => ?_, fun t t' => ?_⟩
  · -- the uniform bound
    have h0 : derivL1 0 (fun x : E => H (t, x)) ≤ C₀ * (volume K).toReal := by
      refine derivL1_le_of_bound (hsliceCd t) (horder 0 (Nat.zero_le _)) hKcompact hKmeas
        (hsliceZero t) fun x => ?_
      exact le_trans (norm_iteratedFDeriv_slice_le hH (horder 0 (Nat.zero_le _)) t x) (hC₀ (t, x))
    have h1 : derivL1 (2 * j) (fun x : E => H (t, x)) ≤ C₁ * (volume K).toReal := by
      refine derivL1_le_of_bound (hsliceCd t) (horder (2 * j) le_rfl) hKcompact hKmeas
        (hsliceZero t) fun x => ?_
      exact le_trans (norm_iteratedFDeriv_slice_le hH (horder (2 * j) le_rfl) t x) (hC₁ (t, x))
    rw [contDiffDecay]
    refine mul_le_mul_of_nonneg_left (add_le_add h0 ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left h1 hc0
  · -- the Lipschitz bound
    have habs : (0 : ℝ) ≤ |t - t'| := abs_nonneg _
    have hdiffCd : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞)
        ((fun x : E => H (t, x)) - fun x : E => H (t', x)) := (hsliceCd t).sub (hsliceCd t')
    have hdiffZero : ∀ x : E, x ∉ K →
        ((fun x : E => H (t, x)) - fun x : E => H (t', x)) x = 0 := by
      intro x hx
      show H (t, x) - H (t', x) = 0
      rw [hzero t x hx, hzero t' x hx, sub_zero]
    have hbound : ∀ i : ℕ, i ≤ 2 * j → ∀ Li : ℝ,
        (∀ (s s' : ℝ) (y : E),
          ‖iteratedFDeriv ℝ i H (s, y) - iteratedFDeriv ℝ i H (s', y)‖ ≤ Li * |s - s'|) →
        derivL1 i ((fun x : E => H (t, x)) - fun x : E => H (t', x))
          ≤ Li * |t - t'| * (volume K).toReal := by
      intro i hi Li hLi
      refine derivL1_le_of_bound hdiffCd (horder i hi) hKcompact hKmeas hdiffZero fun x => ?_
      have hsub : iteratedFDeriv ℝ i ((fun x : E => H (t, x)) - fun x : E => H (t', x)) x
          = iteratedFDeriv ℝ i (fun x : E => H (t, x)) x
            - iteratedFDeriv ℝ i (fun x : E => H (t', x)) x :=
        iteratedFDeriv_sub_apply ((hsliceCd t).of_le (horder i hi)).contDiffAt
          ((hsliceCd t').of_le (horder i hi)).contDiffAt
      rw [hsub]
      exact le_trans (norm_iteratedFDeriv_slice_sub_le hH (horder i hi) t t' x) (hLi t t' x)
    have h0 := hbound 0 (Nat.zero_le _) L₀ hL₀
    have h1 := hbound (2 * j) le_rfl L₁ hL₁
    rw [contDiffDecay]
    have hstep : derivL1 0 ((fun x : E => H (t, x)) - fun x : E => H (t', x))
          + c * derivL1 (2 * j) ((fun x : E => H (t, x)) - fun x : E => H (t', x))
        ≤ L₀ * |t - t'| * (volume K).toReal
          + c * (L₁ * |t - t'| * (volume K).toReal) :=
      add_le_add h0 (mul_le_mul_of_nonneg_left h1 hc0)
    calc 2 ^ j * (derivL1 0 ((fun x : E => H (t, x)) - fun x : E => H (t', x))
          + c * derivL1 (2 * j) ((fun x : E => H (t, x)) - fun x : E => H (t', x)))
        ≤ 2 ^ j * (L₀ * |t - t'| * (volume K).toReal
            + c * (L₁ * |t - t'| * (volume K).toReal)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 ^ j * (L₀ * (volume K).toReal + c * (L₁ * (volume K).toReal)) * |t - t'| := by ring

end Bounds

end GaloisForLFunctions.HTGeometry
