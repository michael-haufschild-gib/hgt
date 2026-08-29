# C5 refined projective-cone no-go (2026-08-29)

Qualifying result: formal route kill in `GaloisForLFunctions.HTGeometry.ExactCompletedC5RefinedParabolicConeNoGo`.

Exact ray:
- `R=10`, `z=s`, `v=131s/320`
- source-positive state `U=131s/32`, `B=63s/32`, `gap=100(1-s²)`
- for sufficiently small `s>0`: `0<z<3/10`, refined clock inequalities `(13/32+z²/32)z<v<(33/80+z²/16)z`, scale floor `191/10+(37/5)z²<R²`, exact reconstruction, and `Q>0`.
- at `s=0`, state equals source-positive seam `X=100`; existing theorem gives strict negative corrected C5 slope. Polynomial continuity moves negativity into open refined chamber.

Closed theorems:
- `exists_refinedParabolicClockCone_c5ExactCompletedSeamSlope_neg`
- `not_forall_refinedParabolicClockCone_c5ExactCompletedSeamSlope_nonneg`

Interpretation:
- kills refined projective clock/scale inequalities as a standalone C5 first-contact barrier.
- does NOT kill joint capped-refined chamber because witness gap is near 100, not <20.
- prior adapted no-go kills source positivity + lower clock + gap<20 but omits refined scale/projective floor.
- strongest surviving static premise is exact corrected-slope positivity on joint chamber imposing both gap<20 and refined projective/scale laws; actual-orbit history is alternative.

RH chain killed:
refined projective cone ⇒ corrected-slope positivity ⇒ global exact completed C5 orientation growth ⇒ direct fixed-action orientation ⇒ compact/tail rank-four/Ptolemy assembly ⇒ CLG/TTF or Weil positivity ⇒ RH.

Verification:
- direct `lake env lean` passed.
- targeted `lake build GaloisForLFunctions.HTGeometry.ExactCompletedC5RefinedParabolicConeNoGo` passed.
- axioms only `propext`, `Classical.choice`, `Quot.sound`.
- global lint failure only pre-existing/concurrent unreachable modules; new module is wired into HTGeometry umbrella.
- no heartbeat increase; no own Lean process left.

Docs:
- failed route card `docs/drafts/pipeline/5-failed/theta-cusp-c5-refined-projective-cone-no-go.md`
- result appended to `docs/drafts/pipeline/1-in-progress/theta-cusp-c5-orbit-first-contact.md`
- corrected prior overclaim in adapted no-go module/card: that result tests capped lower-clock cone, not every known pointwise inequality.
- frontier map untouched.

Literature audit: Planat–Solé arXiv:2608.19160 treats lower-order second-level theta concavity; Salazar arXiv:2606.31647 treats order-moment Hankel transport. Neither states this C5 counter-ray/no-go.