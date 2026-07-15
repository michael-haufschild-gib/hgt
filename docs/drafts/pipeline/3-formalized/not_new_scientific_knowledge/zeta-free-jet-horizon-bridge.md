# Zeta hypertranscendence supplies the free jets required by HT horizon geometry

- **ID:** `zeta-free-jet-horizon-bridge`
- **Stage:** 3-formalized
- **Type:** DEFINITIONAL BRIDGE / RIEMANN-ZETA SPECIALIZATION
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/HypertranscendentalFunctionJetFreeness.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ZetaJetFreeness.lean`

## Theorem

For any `f : C -> C`, the repository's function-level predicate

```text
Hypertranscendental f
```

implies

```text
AlgebraicIndependent C (fun j : N => iteratedDeriv j f).  (1)
```

Applying the unconditional theorem `hypertranscendental_riemannZeta` gives

```text
AlgebraicIndependent C
  (fun j : N => iteratedDeriv j riemannZeta).             (2)
```

Thus the complete Riemann-zeta derivative family is formally certified as a free jet family over
the constant field.

## Proof

For a finite initial family, a nonzero polynomial relation among
`f,f',...,f^(n)` is renamed into the derivative slots of a differential polynomial whose point
slot is unused. Pointwise evaluation makes it an algebraic differential equation for `f`,
contradicting hypertranscendence.

An arbitrary multivariable polynomial uses finitely many derivative indices. Rename it from a
finite index type, bound those indices by their finite supremum, and inject them into one initial
jet family. Algebraic independence of that initial family kills the polynomial. This proves `(1)`;
`(2)` is direct specialization.

## Lean declarations

```text
Hypertranscendental.algebraicIndependent_initialJets
Hypertranscendental.algebraicIndependent_iteratedDeriv
algebraicIndependent_riemannZeta_initialJets
algebraicIndependent_riemannZeta_iteratedDeriv
```

## Verification

- scratch proof against the pinned toolchain: passed
- targeted builds of both bridge leaves: passed
- axiom audit of all four declarations: only `propext`, `Classical.choice`, and `Quot.sound`
- no full build was run

## Scientific status

This is a formal consequence of the existing definition and zeta hypertranscendence theorem, not
a new mathematical result. Its role is load-bearing: it removes the previous informal gap between
analytic function hypertranscendence and the algebraically free derivative jets assumed by the
projective-horizon theorems.

## RH impact audit

`[EXACT SPECIALIZATION; NOT RH PROGRESS]` The bridge makes the scalar projective-horizon phase law
applicable to `zeta` without adding a conjectural freeness assumption. It still says nothing about
where the zero level of `zeta` lies, because algebraic jet freeness is divisor-blind.

