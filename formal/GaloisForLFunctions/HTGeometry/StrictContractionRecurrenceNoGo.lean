import GaloisForLFunctions.HTGeometry.OperatorPowerTelescope

/-!
# Strict contraction cannot carry a recurrent completion clock

This file separates two dynamics which must not be identified in a completion argument.  A
geometrically decaying orbit cannot return cofinally to a nonzero initial state.  In particular, a
strictly contractive self-map cannot itself be the recurrent clock on any nonzero source sector.

The positive survivor is a change of carrier: irreversible radial completion and reversible phase
recurrence may coexist only as different directions or as maps between different positive
topologies.  A later source construction must provide their compatibility; one fixed-carrier real
clock cannot do both jobs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- **Geometric-decay recurrence no-go.**  If an orbit decays to zero at a strict geometric rate
and a cofinal reparametrization of the same orbit returns to `x`, then `x` is zero.  No linearity,
finite dimensionality, or spectral decomposition is used. -/
theorem eq_zero_of_geometric_decay_of_cofinal_return
    {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (x : E) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (hdecay : ∀ n, ‖u n‖ ≤ c ^ n * ‖x‖)
    (hreturn : Tendsto (fun j => u (phi j)) atTop (𝓝 x)) :
    x = 0 := by
  have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hc0] using hc1)
  have hbound : Tendsto (fun j => c ^ phi j * ‖x‖) atTop (𝓝 0) := by
    simpa using (hpow.comp hphi).mul_const ‖x‖
  have hzero : Tendsto (fun j => u (phi j)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun j => hdecay (phi j)) hbound
  exact tendsto_nhds_unique hreturn hzero

/-- **Strict-contraction clock no-go.**  A self-map which contracts norm by one fixed factor below
one has no nonzero cofinally recurrent orbit.  This is the fixed-carrier obstruction needed when a
radial completion shift is proposed as the same clock as a recurrent phase action. -/
theorem eq_zero_of_strictContraction_of_cofinal_iterate_return
    {E : Type*} [NormedAddCommGroup E]
    (T : E → E) (x : E) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hT : ∀ y, ‖T y‖ ≤ c * ‖y‖)
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (hreturn : Tendsto (fun j => T^[phi j] x) atTop (𝓝 x)) :
    x = 0 := by
  apply eq_zero_of_geometric_decay_of_cofinal_return
    (fun n => T^[n] x) x c hc0 hc1 hphi
  · intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc
          ‖T (T^[n] x)‖ ≤ c * ‖T^[n] x‖ := hT _
          _ ≤ c * (c ^ n * ‖x‖) := mul_le_mul_of_nonneg_left ih hc0
          _ = c ^ (n + 1) * ‖x‖ := by rw [pow_succ]; ring
  · exact hreturn

end

end GaloisForLFunctions.HTGeometry
