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

The exact finite-rank capacity consequence is now exposed at the same source interface.  If a
finite-dimensional function space `V` contains zeta derivatives at every order in a finite set
`S`, then

```text
card(S) <= finrank_C(V).                                  (3)
```

Taking `S={0,...,finrank(V)}` gives a bounded witness:

```text
there exists n <= finrank_C(V) with zeta^(n) notin V.     (4)
```

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
riemannZeta_iteratedDeriv_mem_finset_card_le_finrank
exists_riemannZeta_iteratedDeriv_not_mem_le_finrank
riemannZeta_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
exists_riemannZeta_finiteReporterConditionalInformation_dataProcessing_collapse
exists_riemannZeta_isometricReporterRecovery_collapse
riemannZeta_finiteDerivativeReporterMap_postcomp_newBlindPacket
```

## Verification

- scratch proof against the pinned toolchain: passed
- targeted builds of both bridge leaves: passed
- axiom audit of all four declarations: only `propext`, `Classical.choice`, and `Quot.sound`
- no full build was run

The two capacity declarations were subsequently checked directly, built through the exact cached
module target, and audited with the same standard-only axiom profile.

The finite-family reporter capstone further identifies singular fused zeta-jet information with
one genuinely nonzero derivative packet erased by every network member.  It is the strongest
finite-network form; a separate single-panel wrapper is unnecessary.

The downstream capstone selects one derivative order no larger than reporter dimension which is
new in the zeta source yet redundant both before and after every linear decoder.  It specializes a
new generic same-witness theorem shared with the Xi logarithmic-derivative source.

For an isometric decoder between complete Hilbert spaces, the stronger recovery specialization
retains that same source-new/reporter-redundant witness and proves that the decoder adjoint exactly
recovers the original reporter.  Thus representation recovery is perfect even though no
downstream operation recreates the zeta derivative direction already erased before encoding.

At arbitrary finite resolution, every coefficient direction newly erased by a decoder now has an
explicit zeta interpretation: its synthesized derivative packet is nonzero, its original reported
value is nonzero, and only the downstream decoded value vanishes.

## Scientific status

This is a formal consequence of the existing definition and zeta hypertranscendence theorem, not
a new mathematical result. Its role is load-bearing: it removes the previous informal gap between
analytic function hypertranscendence and the algebraically free derivative jets assumed by the
projective-horizon theorems.

## RH impact audit

`[EXACT SPECIALIZATION; NOT RH PROGRESS]` The bridge makes the scalar projective-horizon phase law
applicable to `zeta` without adding a conjectural freeness assumption. It still says nothing about
where the zero level of `zeta` lies, because algebraic jet freeness is divisor-blind.

## Log

- 2026-07-21 -- connected the unconditional zeta source to the generic exact finite-rank
  jet-capacity and bounded-escape laws.
- 2026-07-21 -- connected zeta to the exact finite reporter-network Gram/common-blind-packet
  alternative.
- 2026-07-21 -- connected zeta to the generic same-witness conditional-information collapse under
  arbitrary downstream linear data processing.
- 2026-07-21 -- connected zeta to the generic isometric-recovery collapse: adjoint recovery is
  exact while the same bounded-order source direction remains reporter-blind.
- 2026-07-21 -- discharged the exact decoder-created blind-packet witness for zeta at every finite
  jet resolution.
