# Passive Wilson reciprocity and active EWQ orientation lift

- **ID:** NW-EWQ-SURVIVOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** arXiv:2607.18215 · EWQ-V · Hedenmalm moving-horizon source · rational Wilson Gram anomaly
- **Statement:** Non-Abelianity does not imply directional nonreciprocity; passive PSD links have conjugate reverse Wilson traces, while an active signed Pauli contrast linearizes the EWQ reflected crossing and remains faithful after completed-jet landing.

## `[PROVED HERE]` theorem package

For arbitrary square complex link matrices satisfying `L(j,i)=L(i,j)ᴴ`, reverse plaquette trace is
the complex conjugate of forward trace.  Hence real part and modulus are orientation invariant.
Every PSD normalized block kernel satisfies this reciprocity.  The explicit rational Wilson Gram
sector supplies the strict separation: its Wilson loops do not commute, yet every directional real
contrast vanishes.

For real `z`, the independently ordered Pauli words

`Y · iI · zX · Z` and `iI · Y · Z · zX`

equal `zI` and `-zI`.  Signed trace contrast is `4z`; magnitude contrast is zero; reverse-adjoint
reciprocity holds iff `z=0`.  With the literal EWQ--Hedenmalm amplitude `a_p(q)`,

`reflectedCrossing(p,q) = -(log p / 4) · contrast(p,q)^2`.

The complete pre-divisor EWQ interaction jet gives a function-valued non-erasing landing:
its weighted contrast family is zero iff `a_p(q)=0`, equivalently `Re(q)=1/2`.  Global family
annihilation is therefore equivalent to RH, not an unconditional proof of it.

## Lean certificate

- `GaloisForLFunctions.HTGeometry.DirectionalWilsonReciprocity`
- `GaloisForLFunctions.RHTower.EulerSquarefreeWickNonreciprocalWilsonOrientation`
- Direct `lake env lean` checks: PASS
- New-declaration axiom audit: `propext`, `Classical.choice`, `Quot.sound` only
- Umbrella imports wired; umbrella builds intentionally not run

## Route consequence

Paper's mechanism contributes a route-wide firewall and exact EWQ orientation square root, but no
producer.  CCM, Weil/Connes, Deninger/Green, Sonin, shifted-Hankel, Wold/Hilbert, and other passive
PSD landings cannot acquire signed orientation merely from noncommuting links.  A viable fusion must
derive active reverse-adjoint breaking from an independent arithmetic source before divisor
selection; scalar feedback/projective normalization can preserve that signal but cannot create it.
