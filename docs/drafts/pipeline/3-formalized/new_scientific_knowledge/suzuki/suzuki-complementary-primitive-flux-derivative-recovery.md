# Complementary primitive flux recovers Suzuki's weighted derivative

- **ID:** `suzuki-complementary-primitive-flux-derivative-recovery`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT COMPLEMENTARY-FLUX CANCELLATION / WEAK DERIVATIVE THEOREM
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Lean:** `GaloisForLFunctions.RHTower.SuzukiPrimitiveFluxNonnormalGraphReduction`
- **Inputs:** `suzuki-coordinate-cutoff-primitive-flux-identity.md`,
  `suzuki-flat-primitive-flux-volterra-liouville.md`,
  `suzuki-gamma-weighted-tail-coercivity.md`

## 1. Algebraic cancellation

Let

```text
A=2L I+C,        C=R-B,                                 (1)
N=A partial_L+Z.                                        (2)
```

For a coordinate cutoff \(M\), put \(Q=I-M\) and

```text
G_M=[C,M]F,
G_Q=[C,Q]F=-G_M.                                       (3)
```

Define the two primitive fluxes

```text
Y_M=A(MF)-G_M,
Y_Q=A(QF)-G_Q.                                         (4)
```

Then, exactly,

```text
Y_M=M A F,
Y_Q=Q A F,
Y_M+Y_Q=A F.                                           (5)
```

Indeed,

```text
A(MF)-[C,M]F
 =2L MF+CMF-(CMF-MCF)
 =M(2L F+CF)=MAF.                                      (6)
```

The identity for \(Q\) is identical, and \(M+Q=I\) gives the sum.

This is stronger than viewing \(G_M'\) as an admissible rough source. It says the primitive
subtraction exactly restores the cutoff of the **uncut flux**.

## 2. Complementary cutoff equations

Suppose the literal uncut paired equation is

```text
N F=S                                                   (7)
```

with its already classified zero-order physical source \(S\). The complete cutoff identity gives

```text
N(MF)=G_M'+H_M,                                        (8)

H_M=M S+M'AF+[Z,M]F.                                   (9)
```

For \(Q=I-M\),

```text
N(QF)=G_Q'+H_Q,                                        (10)

H_Q=Q S-M'AF-[Z,M]F.                                   (11)
```

Thus

```text
H_M+H_Q=S.                                             (12)
```

The primitive-flux reduction applied to `(8)` and `(10)` gives

```text
Y_M'=(2I-Z)MF+H_M,
Y_Q'=(2I-Z)QF+H_Q.                                     (13)
```

Adding `(13)` and using `(5)`--`(12)` gives the tautologically correct but analytically decisive
identity

```text
(AF)'=(2I-Z)F+S.                                       (14)
```

Unlike differentiating \(AF\) directly, the proof of weighted membership of the two terms on the
left uses disjoint source mechanisms:

```text
M branch: zero-charge terminal flatness and Volterra Liouville;
Q branch: pre-event recurrence summability.             (15)
```

The rough prime primitives cancel only after both mechanisms have paid their own norms.

## 3. Weighted derivative recovery from the full flux derivative

Fix \(0<\sigma<1\), put

```text
V=exp(sigma L)F,
U=exp(sigma L)F'=V'-sigma V,

A_sigma=2L I+R_sigma-B.                                (16)
```

Since \((AF)'=AF'+2F\),

```text
exp(sigma L)(AF)'
 =A_sigma U+2V.                                        (17)
```

Hence

```text
A_sigma U=exp(sigma L)(Y_M'+Y_Q')-2V.                  (18)
```

On a terminal ray, the shifted Gamma numerical range and arbitrary bounded \(B\) give

```text
Re inner(A_sigma u,u)
 >=[2L_0-kappa_sigma-||B||]||u||^2.                    (19)
```

Therefore, if

```text
V,
exp(sigma L)Y_M',
exp(sigma L)Y_Q' in L2                                 (20)
```

and

```text
2L_0>kappa_sigma+||B||,                                (21)
```

then the Friedrichs-mollifier argument from the Gamma weighted-tail theorem applies to `(18)` and
proves

```text
U=exp(sigma L)F' in L2.                                (22)
```

No derivative of either primitive is estimated separately.

## 4. Why both flux derivatives have the required norm

### Terminal branch

Choose \(M_\nu\) to turn on after the last physical-boundary event required for the \(\nu\)-th
terminal paired chart. After finite conormal charges are subtracted, \(MF\) is all-orders flat.
At finite recurrence type, the primitive theorem gives \(G_M,H_M\) in every prescribed weight
below one. `suzuki-flat-primitive-flux-volterra-liouville.md` therefore gives

```text
exp(sigma L)MF,
exp(sigma L)Y_M,
exp(sigma L)Y_M' in L2                                 (23)
```

at every strictly smaller \(\sigma\).

### Pre-event complement

For each valuation label \(\nu\), \(Q_\nu F_\nu\) is supported before a unit enlargement of its
event time \(\tau_\nu\). Boundedness of the completed mode gives

```text
||exp(sigma L)Q_nu F_nu||_2
 <=C w(nu)exp(sigma tau_nu)(1+tau_nu)^(1/2).            (24)
```

The finite-recurrence budget, with the exponential valuation weight chosen strictly above
\(\sigma\tau_\nu/|\nu|\), makes the square sum of `(24)` finite. The same estimate, with a fixed
extra polynomial, was already proved for:

```text
Q S,
M'AF,
[Z,M]F.                                                (25)
```

Equations `(11)`, `(13)`, and `(25)` therefore give

```text
exp(sigma L)QF,
exp(sigma L)H_Q,
exp(sigma L)Y_Q' in L2.                                (26)
```

Combining `(23)` and `(26)` proves `(20)`.

## 5. Suzuki consequence

Assume:

1. the literal infinite paired-orbit equation `(7)` is constructed from a completed zero mode;
2. its two physical half-log traces vanish;
3. its physical-root value/dipole flux charges vanish in the exact two-port matching;
4. the aperture has finite recurrence type.

The finite-grade indicial theorem removes every interior conormal charge. The residual terminal
state is all-orders flat. Sections 1--4 and primitive-flux Volterra Liouville then give, for every
strictly smaller source weight \(0<\sigma<1\),

```text
exp(sigma L)F' in L2.                                  (27)
```

Taking \(1/2<\sigma<1\) gives the physical derivative estimate

```text
integral exp(L)||F'(L)||^2 dL<infinity.                (28)
```

Root projection has norm one, so both physical endpoint profiles belong to \(H^1(dr)\). Interior
coverage is separate: one must prove that finitely many realized paired charts, together with the
small-aperture scalar interior equation, cover the compact middle without assuming derivative
regularity. Consequently the proved implication is

```text
literal paired assembly
+ zero physical value/dipole flux charges
+ finite recurrence
 -> both physical endpoint collars lie in H1.           (29)
```

The endpoint derivative obstruction is closed. Literal source assembly, physical-root flux
matching, and finite interior coverage remain source-bearing gates; none is assumed away.

## 6. Exact frontier movement

```text
raw event-cutoff commutator [M,B]F':
  no zero-order estimate;                               [NO-GO]

one primitive flux:
  weighted value/flux but not derivative;               [CLOSED]

complementary M and I-M fluxes:
  rough primitives cancel in derivative of full flux;   [PAPER-PROVED]

arbitrary bounded nonnormal B:
  costs only ||B|| in terminal coercivity;              [PAPER-PROVED]

finite-recurrence trace-zero H1:
  reduced to literal paired source equation and exact
  physical-root flux matching plus interior coverage.   [OPEN SOURCE CORE]   (30)
```

Neither degree-\(m\) source moments nor Hatano--Nelson dichotomy are required by this flux route.

## 7. Hostile audit

1. **No estimate of \([M,B]F'\).** Opposite primitives cancel algebraically before coercivity.
2. **No deletion of pre-event state.** \(QF\) is retained and pays the recurrence norm `(24)`.
3. **No nonnormal symmetry.** Equation `(19)` uses only \(\|B\|\).
4. **No derivative premise.** `(22)` follows by the same weak mollifier closure as the proved
   Gamma coercivity theorem.
5. **No value-to-derivative leap.** The derivative comes from `(18)`, not from weighted \(F\).
6. **No source assembly theatre.** The theorem is conditional on the literal equation `(7)` and
   physical-root flux matching; those are now the only finite-type source gates.
7. **No all-aperture claim.** Recurrence-infinite apertures remain.
8. **No interior-coverage claim.** Endpoint collars are proved; compact-middle coverage remains.
9. **No RH claim.** Raw Evans injectivity and nonzero-trace return remain.

## 8. Novelty boundary

Partition of unity, complementary commutators, and numerical-range coercivity are classical
separately. Candidate-new source knowledge is the exact Suzuki cancellation

```text
A(MF)-[C,M]F=MAF,
A(QF)-[C,Q]F=QAF,
Y_M'+Y_Q'=(AF)'
 -> weighted F' without differentiating either rough
    prime cutoff primitive.                             (31)
```

External priority remains unaudited.

## 9. Lean status

The existing primitive-flux module now proves:

```text
primitiveFlux_eq_cut_flux;
primitiveFlux_cutoffComplement_sum.
```

These are the exact algebraic identities `(5)`--`(6)`.

Section 3's weighted derivative recovery is now formal too.  Its content is that a numerical-range
lower bound turns into weighted membership, and that step is

```text
formal/GaloisForLFunctions/HTGeometry/GraphFluxStabilityEstimate.lean
  norm_le_of_coercive        c‖u‖² ≤ ⟪u, w⟫  ⟹  c‖u‖ ≤ ‖w‖
  neg_norm_mul_normSq_le_inner_neg_apply   (19)'s bounded-nonnormal half:
                             Re⟪-Bv, v⟫ ≥ -‖B‖‖v‖², Cauchy-Schwarz alone
formal/GaloisForLFunctions/RHTower/SuzukiGammaShiftKappa.lean
  neg_suzukiGammaShiftKappa_le_integral    (19)'s shifted-Gamma half
```

Applied to `(18)`, `norm_le_of_coercive` gives exactly the card's conclusion: under `(20)` and
`2L₀ > κ_σ + ‖B‖`, the weighted derivative `U = exp(σL) F'` is in `L²` with

```text
[2L₀ - κ_σ - ‖B‖] ‖U‖ ≤ ‖exp(σL)(Y_M' + Y_Q')‖ + 2‖V‖.
```

Hypothesis `(20)` is the card's own, about the two branch fluxes; it is not a disguised form of the
conclusion, and the two branches pay their norms by the disjoint mechanisms of `(15)`.

## Gates

- [x] prove primitive flux equals cutoff of uncut flux
- [x] prove complementary primitive cancellation
- [x] prove full-flux derivative recovery
- [x] prove pre-event complement recurrence summability
- [x] prove arbitrary-nonnormal weak derivative coercivity
- [x] formalize complementary-flux algebra in Lean
- [ ] construct literal infinite paired-orbit source equation
- [ ] verify physical-root value/dipole flux matching
- [ ] prove finite paired-chart/small-aperture interior coverage
- [ ] pass recurrence-infinite apertures
- [ ] prove raw Evans injectivity or whole-Connes no-go
