# Cycle 13: the condensation law is now TWO-SIDED (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-13 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsCurrentGap.lean`, wired, built, no sorry,
axioms clean.

## The identities (exact, every coupling, every finite S, NO stability hypothesis)
  ‖J_S(x)‖ = e^{−x·m} · ∏_ζ ‖1+ζ‖      (`norm_gibbs_current_eq`)
  ‖Z_S(x)‖ = e^{−x·m} · ∏_ζ ‖1−ζ‖      (`norm_gibbs_partition_eq`)
with m = ∏S and the product over the gas zeros with multiplicity (leadingCoeff = e^{−xm}
via `gibbsPoly_leadingCoeff`).

## T1/T2 — the missing converse
- T1 `norm_gibbs_current_ge_of_gap`: all zeros at distance ≥ δ from −1 ⟹
  ‖J_S(x)‖ ≥ e^{−x·m}·δ^{|S|}.
- T2 `exists_zero_near_parity_of_small_current`: ‖J_S(x)‖ < e^{−x·m}·δ^{|S|} ⟹ SOME zero
  lies within δ of the parity point.
Cycle 10 gave confinement ⟹ cancellation; T2 gives cancellation ⟹ confinement, with
matching rates. IMPORTANT: no stability hypothesis is used — this survives the cycle-11
falsification of sector stability.

Arithmetic reading: to make the Möbius–Laplace current anomalously small one MUST drag a
gas zero onto the parity point, at an explicit rate. No mechanism can produce cancellation
without producing condensation.

Consistency: W4 (‖J_S‖ ≈ φ(m)x) forces δ ≲ (φ(m)x e^{xm})^{1/k}, matching W2's confinement
radius 2(mx)^{1/k} up to constants.

## Lean note
`Multiset.map_map` leaves goals of the shape `map ((fun w => ‖w‖) ∘ f) s = map (fun ζ => ‖f ζ‖) s`
— close with `congr 2` (definitional), or `Multiset.map_congr rfl` + `Function.comp_apply`
when the inner function must also be rewritten.
