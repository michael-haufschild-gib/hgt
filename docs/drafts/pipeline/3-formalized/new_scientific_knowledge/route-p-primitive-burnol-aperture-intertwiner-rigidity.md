# Route P primitive Burnol aperture-intertwiner rigidity

- **ID:** `route-p-primitive-burnol-aperture-intertwiner-rigidity`
- **Stage:** 3-formalized
- **Type:** FALSIFIED with exact positive anomaly law
- **Label:** `P-G196`
- **Source:** P-G187 weighted aperture semigroup, P-G186 primitive columns, P-G182 strict-right Xi
  conormals, P-G195 spectral-rate gap
- **Statement:** No linear operator commuting with one positive P-G187 aperture step can map a
  primitive P-G186 column to an actual strict-right Xi conormal. Every such landing instead has a
  forced nonzero commutator equal to the aperture-eigencharacter gap times the target column.

## Conjecture loop

P-G195 excluded fixed scalar mixing of P-G194's three channels but left arbitrary nonlocal
operators open. `C196-A` asked whether radius-nonlocality alone suffices if the operator remains
covariant under P-G187 aperture evolution.

Restrict the literal columns to the positive ray and write `S_c` for P-G187's weighted shift. Lean
constructs `S_c` as a complex-linear endomorphism of the full function space. For every positive
`c`, primitive and strict-right columns are nonzero eigenvectors:

```text
S_c phi_(pe,kappa) = exp[-c(lambda_pe+i kappa)] phi_(pe,kappa),
S_c psi_q          = exp[-c(rho_q-1/2)] psi_q.
```

Their eigenvalues differ because

```text
Re(rho_q-1/2) < 1/2 < log 2 <= lambda_pe.
```

Any linear `A` commuting with `S_c` preserves eigenspaces. Thus `A phi=psi_q` would equate the two
eigencharacters, contradiction. No boundedness, locality, integral-kernel, or finite-rank premise
is used.

## Exact positive survivor

Dropping commutation gives more than a negation. Every proposed landing `A phi=psi_q` obeys

```text
A(S_c phi) - S_c(A phi)
  = (exp[-c(lambda_pe+i kappa)] - exp[-c(rho_q-1/2)]) psi_q != 0.   (1)
```

Therefore successful completion must carry a quantitatively prescribed aperture anomaly. This is
the new producer specification: construct the source-derived polar--Gamma operator whose
commutator realizes `(1)` while its augmented visible/defect colligation remains contractive.

Corpus alignment is nonaccidental. `HedenmalmPrimeTranslationAnomaly.lean` already exhibits a
rank-one source commutator, while `DilationFrobeniusShift.lean` identifies dilation as the
noncommuting direction that shifts abscissa. P-G196 says Route P's missing rate changer must use
that anomaly/noncommuting layer; translation-covariant nonlocality cannot work.

## No-go closure

- **Exact killing mechanism:** aperture intertwiners preserve P-G187 eigencharacters, while every
  primitive/strict-right pair has unequal real spectral rate.
- **Strongest positive survivor:** exact nonzero commutator law `(1)`.
- **Scope:** excludes every complex-linear aperture intertwiner, including unbounded and nonlocal
  ones. It does not exclude operators with the forced anomaly, nonlinear transports, or augmented
  colligations whose source commutator is retained as a defect channel.

## Hostile novelty audit

Corpus contains generic preservation of generalized eigenspaces by commuting endomorphisms,
finite-shift exponential-type rigidity, P-G187's individual eigenvector formulas, and unrelated
Burnol co-Poisson intertwiners. It did not apply the semigroup spectrum to the actual P-G186/P-G182
landing, exclude all linear aperture-covariant maps, or compute the exact forced commutator `(1)`.
P-G196 strictly extends P-G195 beyond constant three-channel mixing.

The Möbius--Gamma Hardy transport was also audited as a candidate rate changer. Its strict-right
factor is defined directly from `XiRightZeroCopy`; its derivative landing is mathematically exact
but target-fed, so it cannot serve as W-H184's source-derived producer without a new source-only
factorization theorem.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolApertureIntertwinerRigidity.lean
```

Capstones:

- `routePBurnolApertureIntertwiner_preserves_eigenvalue`;
- `routePBurnolLanding_commutator_eq_eigenvalueGap`;
- `routePBurnolLanding_commutator_ne_zero`;
- `not_exists_routePBurnolApertureIntertwiner_eq_strictRightConormal`.

Verification:

- `/tmp/pg196.lean`: `lake env lean /tmp/pg196.lean` passed cleanly;
- exact leaf build passed; no full or umbrella build run;
- `/tmp/pg196_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration and diff checks clean;
- umbrella import wired without building umbrella.

## Gates

- [x] arbitrary linear aperture-intertwiner class tested
- [x] strict source/target eigencharacter separation proved
- [x] intertwining landing excluded without boundedness or locality premises
- [x] exact forced nonzero commutator extracted
- [x] target-fed Möbius--Gamma candidate audited
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] realize forced commutator from source-only polar--Gamma data
- [ ] augment P-G194 conservation by this anomaly channel and prove contraction
- [ ] instantiate W-H184 and prove unconditional RH
