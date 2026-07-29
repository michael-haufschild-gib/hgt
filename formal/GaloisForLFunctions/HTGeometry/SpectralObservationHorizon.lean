import GaloisForLFunctions.HTGeometry.DisconnectedAffineSpectralLaw

/-!
# From spectral birth depth to observation time

An interaction packet whose detuning is `O(|g|^r)` cannot produce a finite-window phase change
along any observation horizon `T(g)` with `T(g)|g|^r → 0`. This is the exact analytic bridge from
generator depth to operational time.
-/

open Filter Topology Asymptotics
open IncidenceAlgebra

namespace GaloisForLFunctions.HTGeometry

/-- A detuning dominated by a scale remains unresolved whenever the observation horizon times
that scale tends to zero. -/
theorem observationPhase_tendsto_one_of_isBigO
    {α : Type*} {l : Filter α}
    {detuning scale horizon : α → ℂ}
    (hdetuning : detuning =O[l] scale)
    (hunresolved :
      Tendsto (fun x => horizon x * scale x) l (𝓝 0)) :
    Tendsto
      (fun x => Complex.exp (-Complex.I * (horizon x * detuning x)))
      l (𝓝 1) := by
  have hproduct :
      Tendsto (fun x => horizon x * detuning x) l (𝓝 0) :=
    ((isBigO_refl horizon l).mul hdetuning).trans_tendsto hunresolved
  have hphaseArgument :
      Tendsto (fun x => -Complex.I * (horizon x * detuning x))
        l (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : α => -Complex.I) l (𝓝 (-Complex.I)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul hproduct
  have hexp :=
    Complex.continuous_exp.continuousAt.tendsto.comp hphaseArgument
  simpa using hexp

/-- **Packet birth-depth/observation-horizon law.** For every analytic response on a finite
interaction-coordinate space, every packet remains phase-indistinguishable from its uncoupled
value along every horizon growing strictly slower than the inverse packet power. -/
theorem AnalyticAt.posetMobiusProbe_observationPhase_tendsto_one
    {E : Type*} [Fintype E] [DecidableEq E]
    {f : (E → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (z : E → ℂ) (packet : Finset E)
    (horizon : ℂ → ℂ)
    (hunresolved :
      Tendsto
        (fun g : ℂ =>
          horizon g * (‖g‖ ^ packet.card : ℂ))
        (𝓝 0) (𝓝 0)) :
    Tendsto
      (fun g : ℂ =>
        Complex.exp
          (-Complex.I *
            (horizon g *
              posetMobiusProbe (R := ℂ) packet
                (fun active =>
                  f (g • restrictInteractionPacket active z)))))
      (𝓝 0) (𝓝 1) := by
  let detuning : ℂ → ℂ :=
    fun g =>
      posetMobiusProbe (R := ℂ) packet
        (fun active =>
          f (g • restrictInteractionPacket active z))
  let scale : ℂ → ℂ :=
    fun g => (‖g‖ ^ packet.card : ℂ)
  have hdetuningReal :
      detuning =O[𝓝 0] fun g : ℂ => ‖g‖ ^ packet.card := by
    exact AnalyticAt.posetMobiusProbe_couplingRay_isBigO
      hf z packet
  have hdetuningNorm :
      detuning =O[𝓝 0] fun g : ℂ => ‖scale g‖ := by
    simpa [scale] using hdetuningReal
  have hdetuning : detuning =O[𝓝 0] scale :=
    hdetuningNorm.of_norm_right
  exact observationPhase_tendsto_one_of_isBigO
    hdetuning (by simpa [scale] using hunresolved)

end GaloisForLFunctions.HTGeometry
