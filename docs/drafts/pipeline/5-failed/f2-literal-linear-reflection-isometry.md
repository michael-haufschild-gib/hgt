# Literal linear identification of window and PM reflections

- **Stage:** 5-failed
- **Verdict:** No real-linear form isometry intertwines window Serre duality with the bare PM Krein reflection, on any positive-length window.
- **Scope:** This literal identification only; the corrected F2 correspondence remains active.

## Obstruction

For every `A>0` there is a smooth test supported in `[−A,0]` with

`σ_AH=−H`, `∫H²=1`, `Q(H)≥1/4`.

But `Θ_PM v=−v` implies `[v,v]_PM=−⟨v,v⟩⁺≤0`. A real-linear map preserving the quadratic forms and intertwining the two involutions would send the positive odd test to a nonpositive odd vector, a contradiction. Injectivity is not needed.

## Strong positive survivor

The odd window sector contains a uniformly positive unit vector at every stage. Take the existing normalized smooth odd bump at radius `r=min(A/2,1/2000)`. Translate it into a window of length `2r`; short-window coercivity gives `Q≥1/4`. Translate its center to `−A/2`. Translation preserves complete Weil energy and square mass, and oddness gives the claimed Serre eigenvalue.

The correct Mellin reflection retains both operations missing from the failed identification:

`Φ_(σ_AH)(s,1)=exp(−A(2s−1/2)) conjugate(Φ_H(1/2−conjugate(s),1))`.

Its paper proof and Lean formalization are complete in [the Mellin correspondence](../3-formalized/f2-hecke-window-mellin-correspondence.md). This semilinear relation is compatible with the positive odd sector; it does not assert Weil positivity for arbitrary tests.

## Lean audit

`MayerScattering/WindowSerreDualityIsNotTheKreinReflection.lean`:

- `exists_windowInvolution_odd_weilQuad_pos`
- `mayerKreinForm_nonpos_of_reflection_neg`
- `no_weil_isometric_krein_reflection_intertwiner`

Final individual check passed. Audited endpoints use only `propext`, `Classical.choice`, `Quot.sound`; umbrella import added.
