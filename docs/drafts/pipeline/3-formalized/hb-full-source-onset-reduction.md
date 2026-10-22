# HB: exact onset remainder of the original mixed source

Status: source identity formalized; complete Einstein Peierls extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Result

The original, unprojected scalar potential of the mixed Einstein stream has an explicit decomposition

```
F = L Phi + R,
R = 2 (b' H + ell' Q) chi'(tau+t) exp(2s(tau+t)).
```

Here `L = partial_tau² - partial_t² - (1-u²) Delta`, `u=-tanh(t)`, and all quantities are source-built:

```
alpha = (2s+1)(2s+2),       k = s(s-1)/4,
Q = fullSquarePotential q,
H = fullAngularField q branch,
r(t) = a² (1+u)^(2s),      b(t) = r(t) u,
ell(t) = -k r(t) u³,
Phi = (b H + ell Q) chi(tau+t) exp(2s(tau+t)).
```

`H` is the corpus's existing global modular inverse, satisfying `Delta H = alpha(H+Q)`. Its cusp correction and all angular derivatives are retained. The result supplies no new angular-inverse premise. The original source `F` is exactly `timeOriginalForcing`, including the full gradient energy.

Lean states the decomposition through the actual waves of its two explicit summands. The final theorem `timeOriginalForcing_full_onset_decomposition` quantifies over every actual Xi copy, either source branch, arbitrary amplitude, both real times, and the original upper half-plane point. It needs no equation, inverse, source-cancellation, or RH hypothesis. The nonzero normalizer `alpha` follows from the already-constructed physical angular parameter.

## Analytical mechanism

The original reduced polynomial has the exact free-frequency identity

```
reducedPolynomial(s,w,u)
  = -alpha (1-u²)u
    + s(s-1)/2 (w-2s)(1-u)u² [3+(2s+3)u].
```

The steady source inverse already exists in `fullAngular_master_current`. The new work carries that inverse through actual independent-frequency differentiation and the fixed smooth onset. It does not replace the target frequency by `2s`.

The two second onset derivatives cancel between the time and radial derivatives. Combining the global angular equation with the original gradient lift leaves precisely `chi'`, with the coefficient above. The pulse vanishes outside `0 <= tau+t <= 1`. This is localization in ingoing time; the strip is not compact in spacetime.

## Boundary information retained in the hard conjecture

Both explicit summands vanish at the AdS endpoint, and vanish before their ingoing onset. These properties do not justify deleting their horizon contribution from a causal pairing.

Analytically, along fixed ingoing time `v=tau+t` and `t -> -infinity`,

```
Phi -> a² 2^(2s) (H-kQ) chi(v) exp(2sv).
```

The incoming angular profile is therefore the explicit `H-kQ`. This limit and its integrated physical boundary current are not formalized in the new module. Neither this profile nor the pulse is asserted to vanish.

The current cancellation conjecture is now testable against two specified quantities: the causal response to `R` and the incoming horizon profile `H-kQ`. The complete scalar-scalar and vector-vector Einstein channels, their causal corrections, and the final spin-two/left-QNM pairing still have to participate. The scalar identity alone does not prove cancellation of that full quantity.

## Validation

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceOnsetReduction`.

The source passed `lake env lean` in scratch and an isolated `lake build` of this single module using cached dependencies. No umbrella or dependency rebuild was run. The module contains actual derivative proofs and source identities; it uses no numerical experiment or computational certificate.

All 21 new public theorems passed the scratch axiom audit with exactly `propext`, `Classical.choice`, and `Quot.sound`. The audited source and compiled artifacts were installed byte-for-byte, and the module was wired into `RHTower.lean` without building that umbrella.

Formal lint passed with existing large-file warnings. Generated indexes were refreshed. Owned scratch files and audit caches were removed; no owned Lean process remains.
