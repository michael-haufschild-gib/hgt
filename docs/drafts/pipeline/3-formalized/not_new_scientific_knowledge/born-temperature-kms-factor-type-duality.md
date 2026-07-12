# Born temperature aligns the critical line with the Bost--Connes factor-type transition

- **ID:** `born-temperature-kms-factor-type-duality`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** prime coherent scale factor; Bost--Connes KMS classification; separate from RHTower
  Routes A--D
- **Statement:** For the prime-number wavefunction `n^(-s)`, the physical inverse temperature is
  `beta=2 Re(s)` by the Born rule, uniquely even projectively. Functional-equation reflection
  becomes `beta -> 2-beta`, and the two reflected Bost--Connes GNS sectors carry the same factor
  type exactly at `beta=1`, i.e. `Re(s)=1/2`; RH is equivalent to reflected-phase matching at
  every `xi` zero. The conjectured source-derived normal duality of the reflected sectors
  **collapses**: its necessary phase condition holds exactly where the reflection is already the
  identity, so the duality asserted at every zero is verbatim RH and contains no independent
  construction target.

## Goal

Replace the older dictionary `beta=Re(s)`, which leaves an unexplained mismatch between FE
self-duality at `1/2` and the Bost--Connes phase transition at `1`, by the temperature actually seen
by the Hilbert-space state. Then decide whether the completed Euler--Gamma constraint supplies a
normal duality of the two reflected KMS sectors at its zeros. Decision reached: it cannot supply one
with content — see Section 4.

## Gates

- [x] 0 -> 1 in-progress: normalization, factor-type invariant, RH equivalence, source requirement,
  and failure tests are explicit.
- [x] 1 -> 2 fully-proven: original-source audit of the Bost--Connes KMS classification completed
  (verbatim quotes in Section 2); the composition proof is complete with the representation-level
  meaning of every step fixed in Section 1 (the Born dictionary is a distribution-level label, not a
  claim that the vector state is KMS).
- [x] 2 -> 3 formalized: Born-temperature forcing, normalizability wall, phase-type selector, RH
  equivalence, and the collapse theorem are formalized in
  `formal/GaloisForLFunctions/RHTower/BornTemperatureFactorType.lean`; the von Neumann factor
  classification enters only as an explicit hypothesis on an abstract label function, never as an
  axiom; build, formal lint, and axiom audit pass.
- [x] 3 -> 4 publication-ready: CLOSED NEGATIVE as new science. The required source-derived normal
  FE duality is proven contentless (Section 4): the phase-matched locus is exactly the fixed locus
  of the reflection, so the duality demanded at the zeros is the identity wherever it can exist and
  its existence is verbatim RH. The card terminates as BRIDGE / not new scientific knowledge.

## 1. The normalization correction `[PROVED HERE + FORMALIZED]`

On the integer basis, let

```text
Psi_s = sum_(n>=1) n^(-s) |n>.
```

Its Born weights are `w_s(n) = |n^(-s)|^2 = n^(-2 sigma)` with `sigma=Re(s)`. For the Bost--Connes
Hamiltonian `H|n>=(log n)|n>`, a Gibbs weight at inverse temperature `beta` is
`exp(-beta log n)=n^(-beta)`.

**Theorem 1 (Born forcing).** The Born weights of `Psi_s` coincide with the Gibbs weights at
inverse temperature `beta` on every level `n>=1` — even only projectively, allowing an overall
normalization `c>0` — iff

```text
beta = 2 sigma.                                       (1)
```

*Proof.* At `n=1` both weights are `1`, so any proportionality constant is `c=1`. At `n=2` the
equality `2^(-2 sigma)=2^(-beta)` gives, after taking logarithms and cancelling `log 2 != 0`,
`beta=2 sigma`. Conversely `beta=2 sigma` matches all levels exactly. ∎

The factor `2` is the Born rule converting an amplitude exponent into a probability exponent; it is
not a chosen rescaling, because the Hamiltonian `log n` is pinned by the Bost--Connes dynamics
`sigma_t(mu_n)=n^(it) mu_n`.

**Representation-level meaning (fixed).** The dictionary is a distribution-level label: the
diagonal (Born) distribution of the vector state `Psi_s` equals the diagonal of the `KMS_beta`
Gibbs state iff `beta=2 sigma`. No claim is made that the vector state itself is KMS on the full
algebra. The factor-type wall of Section 2 lives on the Bost--Connes side at the labelled
temperature.

**Normalizability wall.** `||Psi_s||^2 = sum n^(-2 sigma) = zeta(2 sigma)` converges iff
`sigma > 1/2` iff `beta > 1`. Under (1) three walls coincide exactly: Born normalizability of the
wavefunction, existence of the trace-class Gibbs state (partition function `zeta(beta) < infinity`),
and the Bost--Connes transition temperature. The old `{0,1/2,1}` mismatch was caused by identifying
an amplitude exponent with a probability exponent.

Under FE--Schwarz reflection `tau(s)=1-conj(s)`,

```text
beta(tau(s)) = 2(1-sigma) = 2-beta(s),               (2)
```

a reflection of the temperature axis with unique fixed point `beta=1`.

## 2. Factor-type wall `[PUBLISHED INPUT (SOURCE-AUDITED) + PROVED COMPOSITION + FORMALIZED]`

The Bost--Connes KMS phase diagram supplies the faithful categorical invariant:

```text
0 < beta <= 1 : the unique KMS_beta GNS factor is type III_1;
beta > 1      : extremal KMS_beta states are type I and symmetry is spontaneously broken.
```

**Source audit (2026-07-12, verbatim).**

- [Neshveyev, arXiv:0907.1456](https://arxiv.org/abs/0907.1456), abstract: "We show that the
  KMS_beta-states of Bost-Connes type systems for number fields in the region 0<beta\le 1 ... have
  type III_1."
- [Abouamal, arXiv:2211.07778](https://arxiv.org/abs/2211.07778), introduction, p. 1: "it exhibits
  a phase transition at inverse temperature β = 1. ... For β > 1, the system admits ζ(β) as its
  partition function and the extremal KMS_β states have type I while for 0 < β ≤ 1 it admits a
  unique KMS_β states of type III_1." (The classification itself is Bost--Connes 1995; Laca--Larsen
  --Neshveyev, arXiv:0710.3452, gives the complete phase-transition description for number fields.)

**Theorem 2 (selector).** For `0<beta<2`, put `beta*=2-beta`. Any label function that is constant
with one value on `0<beta<=1` and constant with a different value on `beta>1` — in particular the
factor type, which is preserved by normal spatial isomorphism and unitary equivalence — satisfies

```text
label(beta) = label(beta*)   iff   beta = 1.          (3)
```

*Proof.* If `beta<1` then `beta*>1`: the labels are the two distinct values. If `beta>1` then
`0<beta*<1`: same mismatch. At `beta=1` the two parameters coincide. ∎

At `beta=1` equivalence of the sectors is the identity. Hence the `beta` and `beta*` KMS sectors
can be normally equivalent iff `beta=1`, conditional only on the published KMS classification —
which enters the formalization as the stated hypothesis on the label function, not as an axiom.

## 3. RH reformulation `[PROVED COMPOSITION + FORMALIZED]`

Every `xi` zero lies in the open strip `0<Re(rho)<1` (formalized from `xi(1-s)=xi(s)` and
nonvanishing on `Re(s)>=1`), so its Born temperature lies in `(0,2)`. Combining `(1)`--`(3)`:

```text
RH
  iff
for every rho with xi(rho)=0, the Bost--Connes KMS sectors at
beta=2 Re(rho) and beta*=2-2 Re(rho) have no factor-type mismatch.
```

This is pointwise and therefore is not the measured-trace route killed by
`f1-hodge-riemann-modular-route`: one hypothetical off-line zero already pairs a type-I factor with a
type-`III_1` factor and is detected.

## 4. Collapse of the source-forcing conjecture `[PROVED HERE + FORMALIZED]`

The former Section 4 conjectured a source-derived normal clock-perspective equivalence between the
KMS reductions at `beta` and `2-beta` at every `xi` zero. This conjecture collapses; there is no
object to construct.

**Theorem 3 (fixed locus).** `tau(s)=1-conj(s)` fixes `s` iff `Re(s)=1/2`; the imaginary parts of
`s` and `tau(s)` agree identically, so the reflection moves only `Re(s)`.

**Theorem 4 (collapse).** For every `s`, the reflected phases at `beta(s)` and `2-beta(s)` match
iff `tau(s)=s`. Hence at any point where the necessary phase condition for a normal equivalence
holds, the change of clock perspective is already the identity of a single sector; at any other
point, the factor types differ and no normal equivalence exists. Consequently:

```text
"a normal duality of the reflected KMS sectors exists at every xi zero"
   iff   RH,
```

and when it holds, every asserted duality is the identity. The conjecture is RH verbatim; it names
no intermediate object whose construction could be easier than RH.

**Theorem 5 (Born-invisibility of the completion).** Multiplying every amplitude by one fixed
nonzero scalar — the effect of the archimedean `Gamma`-completion `Lambda(s)=Gamma_R(s) zeta(s)` on
the wavefunction at fixed `s` — changes no Born datum: the projective Gibbs comparison still pins
`beta=2 sigma`. The completed Euler--Gamma constraint therefore cannot transmit any temperature or
sector information through the Born (diagonal) channel; any source-forcing mechanism would need an
FE action on the off-diagonal Bost--Connes algebra, whose symmetry group `R_+ x Zhat*` contains no
`s -> 1-s` reflection.

## 5. Kill tests — resolved

- A scalar equality of partition functions is insufficient; analytic continuation does not preserve
  positivity or GNS factor type. **Confirmed** and superseded by Theorem 5: the completion is
  Born-invisible.
- Group-averaging an off-line reflected pair gives an invariant superposition but not a normal
  equivalence of its type-I and type-`III_1` fibers. **Confirmed** by Theorem 2.
- A measured modular trace remains density-blind; factor type is used pointwise instead.
  **Maintained.**
- Simply declaring FE to be a gauge symmetry is circular. **Sharpened** by Theorem 4: the demanded
  functor is the identity wherever it can exist, so there is nothing non-circular to build.
- The result is a selector, not a proof of RH. **Final status:** selector, proven and formalized.

## 6. Novelty status — final verdict

The `beta=2 sigma` correction, the three-wall coincidence (Born normalizability = Gibbs existence =
phase transition), and the exact alignment

```text
FE self-duality = BC phase transition = prime-clock metric wall
```

repair a concrete normalization defect in the older project KMS card
(`0-backlog/kms-modular-temperature.md`, whose `{0,1/2,1}` reconciliation question this answers).
They were not found in the initial literature search. Nevertheless `(1)` is the Born rule, `(3)` is
a two-case composition of the published phase classification with invariance of factor type, and
Theorems 3--5 are elementary once posed. Every step is parent-routine after the question is asked.
**Grade: BRIDGE / not new scientific knowledge.** The formalized selector is real, reusable
infrastructure; the card ships no new-science claim.

## 7. Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/BornTemperatureFactorType.lean` (wired into the
`GaloisForLFunctions.RHTower` umbrella). Focused build, formal lint, and axiom audit pass; every
theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

- `bornWeight_eq_gibbsWeight_iff`, `bornWeight_propto_gibbsWeight_iff` — Theorem 1.
- `scaled_bornWeight_propto_gibbsWeight_iff` — Theorem 5.
- `summable_bornWeight_iff`, `summable_bornWeight_iff_one_lt_bornBeta` — the normalizability wall.
- `bornBeta_reflect` — equation (2).
- `reflectedPhaseMatch_iff`, `factorLabel_reflect_eq_iff` — Theorem 2 (concrete and generic label).
- `xi_zero_re_mem_open_unit`, `bornBeta_xi_zero_mem` — the strip input to Section 3.
- `riemannHypothesis_iff_xiZero_reflectedPhaseMatch`,
  `riemannHypothesis_iff_xiZero_factorLabel_match` — Section 3.
- `fe_reflection_fixed_iff`, `reflectedPhaseMatch_iff_reflection_fixed`,
  `riemannHypothesis_iff_xiZero_reflection_fixed` — Theorems 3--4.

## 8. What this opens `[CONJECTURE]`

The collapse localizes the residue precisely: the Born channel is diagonal, and the Bost--Connes
symmetry group `R_+ x Zhat*` has no `beta -> 2-beta` element, so no existing arithmetic
quantum-statistical system carries the functional equation natively. The forward object is a
**self-dual completed Bost--Connes system**: a C*-dynamical system whose partition function is the
completed `Lambda(beta)=pi^(-beta/2) Gamma(beta/2) zeta(beta)` — the discrete prime modes welded to
one continuous archimedean scale mode contributing `Gamma(beta/2)` — built so that `beta -> 2-beta`
is a duality of the system itself, not of scalar values. `[CONJECTURE]` Such a system exists, its
phase diagram is symmetric about `beta=1`, and the Kramers--Wannier-type functor exchanging its two
phases degenerates on the fixed line into the type-`III_1` sector — making the completed functional
equation an operator-algebra duality rather than an identity of analytic continuations. The open
question it must answer to escape this card's collapse: the duality has to act on the off-diagonal
algebra, where Theorem 5 does not apply.

## Log

- 2026-07-11 — opened from the user's claim that an inner scale factor forces the external clock.
  Corrected the physical temperature to `beta=2 Re(s)`, aligned FE self-duality with the
  Bost--Connes transition at `beta=1`, and isolated normal KMS-sector duality at `xi` zeros as the
  source-forcing conjecture.
- 2026-07-12 — proved Born forcing (projective uniqueness), the three-wall coincidence, the generic
  label selector, and the RH reformulation; source audit of the KMS classification passed with
  verbatim quotes (Neshveyev 0907.1456; Abouamal 2211.07778 introduction). Proved the collapse
  theorems: phase match iff reflection fixed, source-forcing conjecture iff RH with identity
  dualities, Born-invisibility of the Gamma-completion. Formalized all of it in
  `BornTemperatureFactorType.lean` (build + lint + axiom audit clean). Final grade BRIDGE /
  not new scientific knowledge; card moved to 3-formalized. Successor object seeded in Section 8.
