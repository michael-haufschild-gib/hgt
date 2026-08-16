import GaloisForLFunctions.HTGeometry.OscillatorRecessiveLimits

/-!
# The energy of a square-integrable oscillator solution vanishes at infinity

Past the turning point the oscillator energy `E = v′² − (ξ²−μ)v²` is nonincreasing, and square
integrability keeps it nonnegative.  So it has a limit.  If that limit were a positive `b`, then
`v′² ≥ b` from the turning point on, so `v′` is continuous and nowhere zero, hence of one sign, and
the fundamental theorem of calculus makes `|v|` grow at least linearly — which no square-integrable
function does.

The vanishing of the energy is the decay statement the recessive analysis needs: it says the
solution settles onto the balance `v′² = (ξ²−μ)v²` rather than retaining a residue of kinetic
energy.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The energy tends to zero.**  For a square-integrable solution past the turning point. -/
theorem tendsto_oscillatorMonotoneEnergy_zero {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu < a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hint : IntegrableOn (fun x => v x ^ 2) (Ici a) volume) :
    Tendsto (oscillatorMonotoneEnergy mu v v') atTop (𝓝 0) := by
  have hcv : Continuous v := Differentiable.continuous fun x => (hv x).differentiableAt
  have hcv' : Continuous v' := Differentiable.continuous fun x => (hv' x).differentiableAt
  have hnn := oscillatorMonotoneEnergy_nonneg_of_integrableOn ha hmu hv hv' hint
  have hanti := antitoneOn_oscillatorMonotoneEnergy (le_of_lt ha) hv hv'
  -- past `a` the turning-point factor is positive
  have hturn : ∀ x ∈ Ici a, 0 < x ^ 2 - mu := by
    intro x hx
    have hax : a ≤ x := mem_Ici.1 hx
    nlinarith [ha, hmu, hax]
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_ge_atTop a] with x hx
    exact lt_of_lt_of_le hb (hnn x (mem_Ici.2 hx))
  · -- find one point where the energy is below `b`; antitonicity does the rest
    obtain ⟨x₀, hx₀a, hx₀⟩ : ∃ x₀, a ≤ x₀ ∧ oscillatorMonotoneEnergy mu v v' x₀ < b := by
      by_contra hcon
      rw [not_exists] at hcon
      have hall : ∀ x, a ≤ x → b ≤ oscillatorMonotoneEnergy mu v v' x := by
        intro x hx
        have := hcon x
        rw [not_and, not_lt] at this
        exact this hx
      -- the derivative stays away from zero
      have hbig : ∀ x ∈ Ici a, b ≤ v' x ^ 2 := by
        intro x hx
        have h1 := hall x (mem_Ici.1 hx)
        have h2 : 0 ≤ (x ^ 2 - mu) * v x ^ 2 :=
          mul_nonneg (le_of_lt (hturn x hx)) (sq_nonneg _)
        rw [oscillatorMonotoneEnergy] at h1
        linarith
      have hsqrtb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
      have habs : ∀ x ∈ Ici a, Real.sqrt b ≤ |v' x| := by
        intro x hx
        have h1 := hbig x hx
        rw [show |v' x| = Real.sqrt (v' x ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
        exact Real.sqrt_le_sqrt h1
      have hnz : ∀ x ∈ Ici a, v' x ≠ 0 := by
        intro x hx hzero
        have := habs x hx
        rw [hzero, abs_zero] at this
        linarith
      -- one sign, so `|v|` grows at least linearly
      have hgrow : ∀ x ∈ Ici a, Real.sqrt b * (x - a) ≤ |v x - v a| := by
        rcases sign_locally_const_of_ne_zero hcv' hnz with hpos | hneg
        · intro x hx
          have hax : a ≤ x := mem_Ici.1 hx
          have hFTC : v x - v a = ∫ t in a..x, v' t :=
            (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hv t)
              (hcv'.intervalIntegrable a x)).symm
          have hlow : (∫ t in a..x, Real.sqrt b) ≤ ∫ t in a..x, v' t := by
            refine intervalIntegral.integral_mono_on hax
              (intervalIntegrable_const) (hcv'.intervalIntegrable a x) fun t ht => ?_
            have h1 := hpos t (mem_Ici.2 ht.1)
            have h2 := habs t (mem_Ici.2 ht.1)
            rwa [abs_of_pos h1] at h2
          rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
          have hge : Real.sqrt b * (x - a) ≤ v x - v a := by
            rw [hFTC]
            linarith [hlow]
          exact le_trans hge (le_abs_self _)
        · intro x hx
          have hax : a ≤ x := mem_Ici.1 hx
          have hFTC : v x - v a = ∫ t in a..x, v' t :=
            (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hv t)
              (hcv'.intervalIntegrable a x)).symm
          have hup : (∫ t in a..x, v' t) ≤ ∫ t in a..x, -Real.sqrt b := by
            refine intervalIntegral.integral_mono_on hax (hcv'.intervalIntegrable a x)
              (intervalIntegrable_const) fun t ht => ?_
            have h1 := hneg t (mem_Ici.2 ht.1)
            have h2 := habs t (mem_Ici.2 ht.1)
            rw [abs_of_neg h1] at h2
            linarith
          rw [intervalIntegral.integral_const, smul_eq_mul] at hup
          have hle : v x - v a ≤ -(Real.sqrt b * (x - a)) := by
            rw [hFTC]
            linarith [hup]
          have : Real.sqrt b * (x - a) ≤ -(v x - v a) := by linarith
          exact le_trans this (neg_le_abs _)
      -- so the square is eventually above one, contradicting integrability
      obtain ⟨R, hRa, hR⟩ : ∃ R, a ≤ R ∧ ∀ x ∈ Ici R, (1 : ℝ) ≤ v x ^ 2 := by
        refine ⟨a + (1 + |v a|) / Real.sqrt b,
          le_add_of_nonneg_right (by positivity), fun x hx => ?_⟩
        have hxR : a + (1 + |v a|) / Real.sqrt b ≤ x := mem_Ici.1 hx
        have hxa : a ≤ x := by
          have : (0 : ℝ) ≤ (1 + |v a|) / Real.sqrt b := by positivity
          linarith
        have hg := hgrow x (mem_Ici.2 hxa)
        have hstep : 1 + |v a| ≤ Real.sqrt b * (x - a) := by
          have h1 : (1 + |v a|) / Real.sqrt b ≤ x - a := by linarith
          rw [div_le_iff₀ hsqrtb] at h1
          nlinarith [h1]
        have habsv : 1 + |v a| ≤ |v x - v a| := le_trans hstep hg
        have h1 : (1 : ℝ) ≤ |v x| := by
          have hsub : |v x - v a| ≤ |v x| + |v a| := abs_sub _ _
          linarith [habsv, hsub]
        nlinarith [h1, abs_nonneg (v x), sq_abs (v x)]
      exact not_integrableOn_Ici_of_le (a := R) one_pos hR
        (hint.mono_set (Ici_subset_Ici.2 hRa))
    filter_upwards [eventually_ge_atTop x₀] with x hx
    exact lt_of_le_of_lt (hanti (mem_Ici.2 hx₀a) (mem_Ici.2 (le_trans hx₀a hx)) hx) hx₀

end GaloisForLFunctions.HTGeometry
