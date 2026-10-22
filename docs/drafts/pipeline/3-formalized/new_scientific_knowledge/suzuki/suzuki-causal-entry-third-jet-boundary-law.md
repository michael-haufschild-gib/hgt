# Suzuki causal-entry third-jet boundary law

- **ID:** `suzuki-causal-entry-third-jet-boundary-law`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-causal-entry-third-jet-boundary-law-formalized.md`
- **Type:** RH-FRONTIER SOURCE TRANSPORT THEOREM / FAILED PRODUCER / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `suzuki-affine-sewn-weil-robin-far-tail-factorization.md`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki, arXiv:2206.03682v4, Theorem 1.1; M. Suzuki,
  arXiv:2606.09096v1, equations (1.3), (2.9)--(2.11), and Sections 6, 8.2--8.3

## Exact frontier attacked

The current open core `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED` asks for eventual lower
semiboundedness of the explicit source Ward defect after universal far von-Mangoldt tail,
near-entry Robin currents, and polar--Gamma channel are assembled.  Exact Green--Gram equality is
no longer required.  A tempting mechanism is nevertheless an instantaneous positive rank-one
update when a prime delay crosses the aperture wall `ell=2a`.  The theorem below tests that
mechanism on the exact delayed-hinge exterior already derived from Suzuki's source and identifies
the only discrete entry reporter that can contribute to the rectangular defect.

## Setup

Fix `a>0`, spectral variable `z`, and a continuously differentiable compact source `v` on
`[-a,a]`.  For `0<ell<2a`, put `c=a-ell` and

```text
B(ell)=integral_(-a)^c v(y)dy,
A(ell)=integral_(-a)^c (c-y)v(y)dy,
H(ell,z)=integral_c^a v(y)exp(i z y)dy,
W(z)=integral_(-a)^a v(y)exp(i z y)dy.                 (1)
```

After the canonical `z^2` denominator cancellation, the near and far delayed-hinge channels are

```text
F_near(ell,z)
 =exp(i a z)(i z A(ell)-B(ell))-exp(i z ell)H(ell,z),  (2)

F_far(ell,z)=-exp(i z ell)W(z),       ell>=2a.         (3)
```

These are exactly `z^2` times the causal Weil--Robin law, not a model replacement.

## Theorem A: moving-boundary density cancels twice `[PAPER-PROVED]`

On `0<ell<2a`, Leibniz differentiation gives

```text
B'=-v(c),       A'=-B,       H'=exp(i z c)v(c).         (4)
```

The phase identity `ell+c=a` makes every point-evaluation term in the first derivative cancel:

```text
F_near'
 =-i z [exp(i a z)B+exp(i z ell)H].                    (5)
```

Differentiating the bracket in `(5)` produces a second cancellation,

```text
[exp(i a z)B+exp(i z ell)H]'
 =i z exp(i z ell)H.                                   (6)
```

Consequently the complete transport chain is

```text
F_near'' =z^2 exp(i z ell)H,                            (7)

F_near'''=i z^3 exp(i z ell)H
             +z^2 exp(i a z)v(a-ell).                  (8)
```

### Proof

Equations `(4)` are the fundamental theorem of calculus and the Leibniz rule.  Differentiate
`(2)`.  The two evaluation terms are

```text
+exp(i a z)v(c),       -exp(i z ell)exp(i z c)v(c),
```

and cancel because `ell+c=a`, proving `(5)`.  The identical pair cancels in the derivative of
the bracket, proving `(6)`.  Equations `(7)--(8)` follow by one and two further product rules.
No sign, zero location, or positivity premise is used.

## Theorem B: prime entry is a third-jet event `[PAPER-PROVED]`

At the entry wall `ell=2a`, one has

```text
A=B=0,       H=W.                                      (9)
```

The far channel has jets

```text
F_far'  =-i z exp(i z ell)W,
F_far'' = z^2 exp(i z ell)W,
F_far'''= i z^3 exp(i z ell)W.                         (10)
```

Using `(5)--(10)`, the near-left and far-right jets agree through order two:

```text
F_near^(j)(2a-,z)=F_far^(j)(2a+,z),       j=0,1,2.     (11)
```

Their first possible defect is the exact endpoint trace

```text
F_near'''(2a-,z)-F_far'''(2a+,z)
 =z^2 exp(i a z)v(-a).                                 (12)
```

Thus a delayed von-Mangoldt hinge does **not** enter as a value jump, slope jump, or curvature
jump of the denominator-matched exterior.  It enters first through a third jet, and its complete
coefficient is the zero-extension endpoint trace already responsible for Suzuki's deficiency
endpoint atoms.  If `v(-a)=0` (the Dirichlet form domain), the seam is at least `C^3`; deficiency
states need not satisfy that boundary condition.

## Theorem C: affine-sewn third-jet trace `[PAPER-PROVED]`

Let `v_alpha,v_beta` be two shifted source states with endpoint traces
`tau_alpha=v_alpha(-a)`, `tau_beta=v_beta(-a)` and characteristics `W_alpha,W_beta`.  For target
shift `gamma`, apply Suzuki's affine sewing

```text
S_gamma(C_alpha,C_beta)
 =(beta-gamma)W_beta C_alpha-(alpha-gamma)W_alpha C_beta. (13)
```

Linearity and `(11)--(12)` show that sewn near and far channels still agree through order two.
Their third-jet defect is

```text
Delta_3 S_gamma(z)
 =z^2 exp(i a z)
   [(beta-gamma)W_beta(z)tau_alpha
    -(alpha-gamma)W_alpha(z)tau_beta].                 (14)
```

With `P=(beta-alpha)W_alpha W_beta`, wherever the displayed divisions are legal,

```text
Delta_3 S_gamma/P
 =z^2 exp(i a z)
  [ (beta-gamma)/(beta-alpha) * tau_alpha/W_alpha
   -(alpha-gamma)/(beta-alpha) * tau_beta/W_beta].     (15)
```

Equation `(15)` is a marked barycentric endpoint trace.  It is the first shift-dependent
departure from the universal far common channel.  In particular, even a common normalized trace
`tau_alpha/W_alpha=tau_beta/W_beta=m` survives with coefficient `m`; affine sewing does not
cancel it.

## Hostile verdict and positive survivor

### Instantaneous entry Cholesky update `[FALSIFIED]`

Any proposed Schur--Ward proof assigning a positive rank-one **jump of the completed kernel** to
each prime wall has the wrong source order: `(11)` proves no such jump exists through curvature.
The universal far atom is converted continuously into a near Robin/tail channel.

### `SUZUKI-BOUNDARY-TRACE-RECTANGULAR-WARD` `[CONJECTURE]`

At one recurrence-selected aperture and admissible shift pair:

1. use the marked normalized endpoint trace `(15)` as the discrete prime-entry reporter;
2. pair it with the already constructed critical Gamma/aperture quarter-shift current before any
   Hilbert square or prime completion;
3. include the polar--Gamma continuous third-jet current and rank-one Neumann holonomy;
4. reconstruct the near-entry Ward contribution by triple integration from the entry wall and
   prove its contribution to the rectangular Ward defect is uniformly lower bounded after exact
   midpoint debt `d^2` and holonomy Schur tax are included.

This is strictly sharper than the previous “near-entry channel” placeholder.  The discrete input
is forced to be `(15)`; no fitted leakage coordinate remains.  One mismatch between the actual
quarter-shift current and `(15)`, or a sequence of admissible logarithmic apertures driving the
assembled Ward defect to `-infinity`, falsifies the conjecture.  Uniform lower semiboundedness
feeds the existing rectangular connector directly and proves RH; exact Gram equality is not
needed.

## Novelty audit

- Leibniz transport is classical `[BRIDGE]`.
- Suzuki 2022 supplies the delayed von-Mangoldt hinges; Suzuki 2026 supplies the finite-aperture
  operator, deficiency endpoint states, and real-zero characteristic functions.
- Neither primary paper states the denominator-matched entry-wall jet chain `(5)--(12)`, its
  affine-sewn trace `(14)--(15)`, or the resulting exclusion of instantaneous entry Cholesky.
- Internal corpus search found the value-level boundary--tail law and far common-factor theorem,
  but no aperture-wall derivative or third-jet trace theorem.

The source-specific synthesis is `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`; priority is unverified.

## Formalization gates

- [x] exact paper derivation and sign audit
- [x] entry-wall order and endpoint coefficient
- [x] affine-sewn marked trace
- [x] Lean formalization of transport algebra and wall jets
- [x] moving-cut derivative laws `(4)` discharged in Lean for a continuous source, so the whole
      transport chain and the entry-wall classification are hypothesis-free
- [ ] actual endpoint-trace/quarter-shift source identification
- [ ] rectangular third-jet Ward-defect lower bound and RH

Lean modules:
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalEntryThirdJetBoundaryLaw.lean` (transport algebra
and wall jets) and
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalEntryMovingCutRealization.lean` (the moving-cut
integrals `A`, `B`, `H`, `W`, their three derivative laws `(4)` for a continuous source, and the
resulting hypothesis-free jet chain and third-jet entry law).
