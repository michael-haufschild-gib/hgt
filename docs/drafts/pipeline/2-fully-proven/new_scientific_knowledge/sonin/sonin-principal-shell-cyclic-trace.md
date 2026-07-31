# Canonical cyclic trace law for faithful Sonin principal shells

- **ID:** `sonin-principal-shell-cyclic-trace`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / source-specific principal finite-part descent
- **Scientific status:** `[CORPUS-NEW] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:** `CCMSoninFiniteWordNormalForm.lean`,
  `CCMSoninFiniteWordFaithfulness.lean`, `SoninLogShellCocycle.lean`,
  `SoninSemilocalRelativeTrace.lean`

## Theorem

Fix aperture `a>0`. A live canonical Sonin normal state is a window

```text
d=(C,F,x),   a <= F < C,   x>0,   a <= xF.
```

Define

```text
tau_a(0)=0,
tau_a(d)=1_(x=1) [log C-log F].                           (1)
```

For the exact tropical state product already proved to represent multiplication of the genuine
Sonin principal operators modulo compacts,

```text
tau_a(s*t)=tau_a(t*s)                                    (2)
```

for all zero/live states. The value is invariant under compact congruence of represented
operators. Its finite-support bilinear extension is cyclic.

For a genuine CCM Gram factor with source `r>1` and target `q>1`,

```text
tau_a(Gram(r,q)) = if r=q then log r else 0.              (3)
```

In particular, for `r=p^m`, the trace is `m log p`, independently of aperture. Multiplication by
the Euler-logarithm coefficient `p^(-m/2)/m` yields

```text
log(p) p^(-m/2),                                         (4)
```

the exact unsquared nonarchimedean Connes/Weil orbital coefficient.

## Proof

If the product displacement is not one, both sides of `(2)` vanish. Suppose the first scale is
`x`, the second is `y`, and `xy=1`. The exact normal-state composition formulas give

```text
C_(t*s)=x C_(s*t),
F_(t*s)=x F_(s*t).                                       (5)
```

The floor formula includes the Sonin base-cutoff normalization. Under `xy=1`, both input domain
conditions force the raw overlap floor above `a`, so this normalization is inert. Positive
dilation preserves strict overlap; therefore the two products are simultaneously live or zero.
When live, `(5)` and `log(xz)=log x+log z` give equal logarithmic widths. This proves `(2)`.

Faithful zero/live normal-form classification says two state operators are compact-congruent iff
their states agree, proving Calkin invariance. Summing `(2)` coefficientwise proves cyclicity of
the finite-support pairing.

For `Gram(r,q)`, exact normal data have displacement `r^(-1)q`. This equals one iff `r=q`.
On the diagonal the floor is `a`, the ceiling is `ra`, and `(1)` is
`log(ra)-log a=log r`, proving `(3)` and `(4)`.

## Theorem G: cyclic extension across the exact principal-relative ideal

Let `I_a` be the concrete Sonin principal-relative ideal (exact projection corrections and finite
physical/Fourier time-band blocks; every member is Schatten-1).  Call

```text
T = s.operator + K,    s a canonical window state,   K in I_a           (5)
```

a *principal-relative operator*.  Define

```text
tilde_tau(T) = tau_a(s) + Tr(K).                                        (6)
```

Then, unconditionally for every aperture `a>0`:

1. **Directness.**  The presentation `(5)` is unique, so `(6)` depends only on `T`.
2. **Restriction.**  `tilde_tau` is `tau_a` on principal shells and the ordinary trace on `I_a`.
3. **Closure.**  Principal-relative operators are closed under the genuine operator product; the
   exact residual
   ```text
   R(s,t) = s.operator * t.operator - (s*t).operator                    (7)
   ```
   lies in `I_a`, so `s.operator * t.operator =_r (s*t).operator` — a relative-ideal congruence,
   not merely a compact congruence.
4. **Cyclicity.**  `tilde_tau(TT') = tilde_tau(T'T)`, and its finite-support bilinear extension is
   symmetric.
5. **Single-corner anomaly formula.**  For a genuine CCM Gram factor `g=(r,q)` at aperture `a`,
   ```text
   tilde_tau(Gram_a(r,q)) = (if r=q then log r else 0) + Tr(Gram_a(r,q) - W_a(g)),  (8)
   ```
   where `W_a(g)` is the canonical live window of `g`.

### Proof

*Directness.*  Every member of `I_a` is compact, so two presentations of the same operator have
compact-congruent principal parts.  Faithfulness of the zero/live normal form forces the states to
be equal, and cancellation then forces the relative parts to be equal.

*Closure and the exact residual.*  The physical and the Fourier branch each multiply **exactly**:
same-polarization products are again window translations with the composed ceiling, floor, and
displacement, and the trailing central complement normalizes exactly.  Hence

```text
R(s,t) = P_s F_t + F_s P_t,                                             (9)
```

the sum of the two cross-polarization products, with no error term.  Each cross product carries a
physical band on one side and a Fourier band on the other; moving the dilation across turns it into
a finite time-band block times a bounded factor, so both summands lie in `I_a`.

*Cyclicity.*  Only one new input is needed, namely

```text
Tr(P F) = Tr(F P)                                                       (10)
```

for a physical window `P` and a Fourier window `F`.  Neither factor is compact, so bounded
cyclicity does not apply directly.  Let `G` and `H` be the physical band of `P` and the Fourier
band of `F`; they are idempotent and act as left units, `GP=P`, `HF=F`.  Put

```text
alpha = P H,    beta = F G.                                             (11)
```

Both lie in `I_a`, hence are Schatten-1 and therefore Hilbert--Schmidt, and

```text
alpha beta = P F G,     beta alpha = F P H.                             (12)
```

Since `PF` and `FP` are trace class and `GP=P`, `HF=F`, bounded cyclicity gives
`Tr(alpha beta)=Tr(PF)` and `Tr(beta alpha)=Tr(FP)`, while Hilbert--Schmidt cyclicity gives
`Tr(alpha beta)=Tr(beta alpha)`.  This proves `(10)`.  Applying `(10)` to both summands of `(9)`
gives `Tr R(s,t) = Tr R(t,s)`.  Expanding `TT'` and `T'T` leaves only that residual pair, three
bounded/trace-class commutations, and the already-proved state cyclicity `(2)`, so `(6)` is
cyclic.  Summing coefficientwise gives the finite-support bilinear statement.

*Single-corner formula.*  The quadratic Gram corner is relative-ideal congruent to its mixed shell
translation, which is exactly the canonical live window of `g` after normalization; `(3)` then
evaluates the principal term.

No zero location, asymptotic estimate, numerical experiment, or RH premise is used.  The
Hilbert--Schmidt pair `(11)` is the whole mechanism: the two orders of a noncompact cross product
are recovered from one Hilbert--Schmidt product taken in the two orders.

## Theorem H: one-sided aperture flag law for the extended trace

Fix a strict crossing flag

```text
0 < a < b < c < r*a,   r > 1.                                          (13)
```

Each aperture defect `Delta(u,v;r)` is a principal-relative operator whose principal part is the
scale-one lost shell `S(r*u, r*v)`.  Because `c <= r*a <= r*b`, **all three** defects of the flag
are presented at the single base aperture `c`, so one extended trace reads all of them.  Then

```text
tilde_tau(Delta(a,c;r))
  = tilde_tau(Delta(a,b;r)) + tilde_tau(Delta(b,c;r)) + Tr Kappa(a,b,c;r),  (14)
```

and, using the already-proved curvature energy law,

```text
Re tilde_tau(Delta(a,c;r))
  = Re tilde_tau(Delta(a,b;r)) + Re tilde_tau(Delta(b,c;r))
      - ||Z(a,b,c;r)||_HS^2,                                            (15)
```

where `Z` is the coupling between the two successive lost layers.  Hence

```text
Re tilde_tau(Delta(a,c;r))
  <= Re tilde_tau(Delta(a,b;r)) + Re tilde_tau(Delta(b,c;r)),            (16)
```

with equality exactly when `Kappa(a,b,c;r)=0`.

### Proof

The logarithmic weights are `log c - log a`, `log b - log a`, `log c - log b`, an exact
coboundary, so the principal parts of `(14)` cancel identically.  The shell residuals telescope
because `S(r*a,r*c) = S(r*a,r*b) + S(r*b,r*c)` holds as an operator identity, leaving exactly
`Kappa`.  All three residuals and `Kappa` are Schatten-1, so ordinary trace is additive on them.
Equation `(15)` is `(14)` plus the curvature energy law, and `(16)` is nonnegativity of a squared
Hilbert--Schmidt norm.

The content of `(16)` is that the completed finite part, **before** any archimedean term, is
already one-sided along aperture flags — but in the *subadditive* direction.  A uniform lower floor
therefore cannot be produced by aperture refinement alone: refining a flag can only decrease the
real extended trace, by exactly the successive-layer coupling energy.  Any surviving weld must
obtain its lower bound from the archimedean conductor, not from the aperture tower.

## Frontier effect

Closed:

- cyclicity of canonical principal Sonin shell value;
- aperture-independent diagonal orbital response;
- finite-place identification with exact von-Mangoldt flux;
- ambiguity from compact-congruent normal representatives;
- extension of the trace across the exact principal-relative ideal, with ordinary trace on its
  trace-class part, unique presentation, and full cyclicity for the genuine operator product.

Still open:

- attach Burnol archimedean conductor finite part;
- prove completed one-sided lower floor and RH.

Newly ruled out: obtaining the lower floor from the aperture tower.  By `(16)` the real extended
trace is subadditive along every strict aperture flag, with defect exactly minus the successive
lost-layer coupling energy, so refinement can only push it down.  The floor, if it exists, is an
archimedean statement.

Settled negatively elsewhere: aperture-restriction compatibility of the relative extension fails at
every strict aperture pair (`sonin-aperture-area-rigidity-and-restriction-defect`, Theorem D), so
the surviving route must carry the aperture cocycle rather than assume invariance.

## Novelty audit

Internal corpus search found the crossed-product trace law and faithful tropical normal form, but
no theorem connecting them; this theorem is corpus-new. Targeted inspection of the primary
Connes--Consani--Moscovici semilocal prolate paper found the Sonin Hilbertian isomorphism and
semilocal operator program, not the tropical normal-state trace `(1)`--`(3)`. External novelty is
provisional pending expert/literature review.

## Gates

- [x] dependency-closed paper proof
- [x] zero and nonidentity-displacement cases
- [x] exact reciprocal-scale overlap covariance
- [x] live/zero equivalence under cyclic swap
- [x] Calkin invariance from faithful normal form
- [x] finite-support cyclic pairing
- [x] exact CCM diagonalization
- [x] exact prime-power flux coefficient
- [x] relative-ideal trace extension
- [x] unconditional Lean formalization of `(1)`--`(4)` and Theorem G
- [x] one-sided aperture flag law for the extended trace (Theorem H)
- [x] proof that the aperture tower alone cannot supply the lower floor
- [ ] Burnol completion and completed lower floor

## Lean

| Statement | Declaration |
|---|---|
| `(2)` state cyclicity | `soninWindowStateCyclicLogTrace_compose_comm` |
| `(3)` Gram diagonalization | `soninGramFactorPrincipalCyclicTrace_eq_ite` |
| `(4)` prime-power flux | `soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient` |
| `(7)` relative-ideal closure | `soninWindowState_operator_mul_principalRelativeEq` (pre-existing) |
| `(9)` exact cross residual | `soninWindowStateResidual_live_eq_cross` |
| `(10)` cross-trace symmetry | `opTrace_physicalWindow_mul_fourierWindow_comm` |
| residual trace symmetry | `opTrace_soninWindowStateResidual_comm` |
| G.1 directness | `SoninPrincipalRelativeOperator.toOperator_injective` |
| G.2 restriction | `SoninPrincipalRelativeOperator.extendedTrace_ofState` / `..._ofRelative` |
| G.3 product realization | `SoninPrincipalRelativeOperator.toOperator_compose` |
| G.4 cyclicity | `SoninPrincipalRelativeOperator.extendedTrace_compose_comm` |
| G.4 bilinear cyclicity | `soninPrincipalRelativePairTrace_comm` |
| `(8)` single-corner anomaly | `SoninPrincipalRelativeOperator.extendedTrace_ofGramFactor` |
| aperture defect as presentation | `soninApertureRestrictionDefectPresentation` |
| aperture defect value | `extendedTrace_soninApertureRestrictionDefectPresentation` |
| `(14)` flag law | `extendedTrace_soninApertureRestrictionDefect_flag` |
| `(15)` exact scalar defect | `re_extendedTrace_soninApertureRestrictionDefect_flag` |
| `(16)` one-sided law | `re_extendedTrace_soninApertureRestrictionDefect_flag_le` |
| equality case | `re_extendedTrace_soninApertureRestrictionDefect_flag_eq_iff` |

Files: `formal/GaloisForLFunctions/RHTower/SoninPrincipalShellCyclicTrace.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeCyclicExtension.lean`,
`formal/GaloisForLFunctions/RHTower/SoninApertureExtendedTraceFlagLaw.lean`.
All declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

Novelty split for Theorem G: `(7)` was already in the corpus
(`SoninApertureRestrictionDefect.lean`) and is reused, not reproved.  New here are the exact
cross-polarization identity `(9)`, the cross-trace symmetry `(10)` and its Hilbert--Schmidt band
mechanism `(11)`--`(12)`, the directness/uniqueness of the presentation, the glued functional, its
cyclicity, and the single-corner formula `(8)`.

## Log

- 2026-07-31 — one-sided aperture flag law proved and formalized.  All three defects of a strict
  flag are presented at one base aperture, the logarithmic weights cancel as a coboundary, and the
  whole scalar defect is minus the successive-layer coupling energy.  Consequence: the aperture
  tower is subadditive, so it cannot supply the completed lower floor; that debt is archimedean.
- 2026-07-31 — relative-ideal trace extension closed and formalized.  New mechanism: a physical
  window and a Fourier window, each cut down to its own band, form a Hilbert--Schmidt pair whose
  two products recover the two orders of the noncompact cross product, giving `Tr(PF)=Tr(FP)`.
  This upgrades the previous compact congruence to an exact relative-ideal congruence and makes the
  glued functional a genuine cyclic trace.

