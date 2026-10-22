# Suzuki's exterior multiplier is a one-sided Carleman sheet, not a bilateral Fourier transform

- **ID:** `suzuki-one-sided-carleman-exterior-seam`
- **Stage:** 3-formalized
- **Type:** SOURCE CORRECTION / CONJECTURE / FRONTIER REPLACEMENT
- **Primary sources:** Suzuki 2023, arXiv:2206.03682v4, Theorem 1.1(1), equation (1.2),
  and Section 10; Suzuki 2026, arXiv:2606.09096v1, Section 8.3
- **Parents:** `suzuki-exterior-pole-tomography-neumann-boundary`,
  `suzuki-projected-continuous-deficiency-channel`
- **RH used:** no
- **Computation used:** no

## Corpus frontier under audit

> **Coordinate correction (2026-07-22).** Source-native `M` below is
> `i*suzukiShiftedXiMultiplier 0` in corpus `XiC` coordinate.  Consequently Lean specialization
> `G_eta W-I` represents `(-i)` times physical sheet and consumes `I=-iT_phys`; exact real form
> shift is `eta=-i lambda/2`.  See `suzuki-one-sided-coordinate-phase-normalization.md`.  Sheet
> splitting and RH criterion remain valid after uniform normalization; statements identifying
> Lean interval input directly with physical triangle are superseded.

The current Suzuki corpus treats

```text
M(z)=z^(-2) xi'(1/2-iz)/xi(1/2-iz)                     (1)
```

as the Fourier multiplier of the real even screw kernel `g`, then defines one global exterior
remainder `M W-I`.  This interpretation feeds exterior pole tomography and two-shift sewing.

Suzuki's cited 2023 formula does not state a bilateral Fourier transform.  It states explicitly

```text
integral_0^infinity g(t)e^(izt)dt=M(z),   Im z>1/2,     (2)
```

after `g=-Psi`.  The negative half-line transform converges in the disjoint lower half-plane and
continues as

```text
M_-(z)=M(-z)=-M(z).                                    (3)
```

Equation `(3)` follows from the functional equation.  It is also forced by parity: `g` is even,
whereas the meromorphic function `(1)` is odd.  Therefore `(1)` cannot be one ordinary bilateral
Fourier transform.

## Competing conjectures

### C1. Bilateral-multiplier reading

> The full transform of `g*v` is `M(z)V(z)` and subtracting the finite-interval transform leaves
> one physical exterior transform.

**Falsifier:** even `g` versus odd `M`; at phase `q=1`, both `M` and Suzuki's characteristic `W`
are odd, so `MW` is even, while the corrected projected interval bracket `2A sin(az)` is odd and
nonzero when `aA!=0`.  Thus the claimed global identity cannot hold nontrivially.

### C2. Two-sheet triangular decomposition `[ACTIVE]`

> Cutting the convolution at the aperture produces two Carleman sheets.  Each sheet equals its
> one-sided multiplier times the compact source transform minus one triangular compact correction.
> The two meromorphic multiplier terms have opposite signs and cancel in the bilateral sheet sum.

This conjecture is source-compatible and has a direct Fubini proof.  Its exact equations and RH
consequence are the current proof target.

### C3. Automatic seam crossing

> Positivity of one finite-aperture shifted source automatically continues the upper sheet from
> `Im z>1/2` through the whole upper half-plane.

**Hostile test required:** rational FE--Schwarz orbit insertion preserves the local positive
source shell but inserts a Carleman pole.  Any proof using only abstract finite-aperture positivity
fails this test.  A survivor must use the distinguished Euler--Gamma source marking.

## Theorem A: exact two-triangle convolution law `[PROVED HERE]`

Let `v` be integrable and supported in `[-a,a]`, let `g` be even, and put

```text
h(x)=integral_(-a)^a g(x-y)v(y)dy,
V(z)=integral_(-a)^a v(y)e^(izy)dy.                      (4)
```

In a high upper half-plane where absolute convergence permits Fubini, define

```text
M_+(z)=integral_0^infinity g(t)e^(izt)dt,
R(z)=integral_a^infinity h(x)e^(izx)dx,                  (5)

T_R(z)=integral_(-a)^a v(y)e^(izy)
         integral_0^(a-y)g(t)e^(izt)dt dy.               (6)
```

The change of variables `x=t+y` partitions the positive kernel half-line into `x>a` and
`-a<=x<=a`, giving

```text
M_+(z)V(z)=R(z)+T_R(z).                                  (7)
```

In a low lower half-plane define

```text
M_-(z)=integral_(-infinity)^0 g(t)e^(izt)dt,
L(z)=integral_(-infinity)^(-a)h(x)e^(izx)dx,             (8)

T_L(z)=integral_(-a)^a v(y)e^(izy)
         integral_(-a-y)^0 g(t)e^(izt)dt dy.             (9)
```

The same partition gives

```text
M_-(z)V(z)=L(z)+T_L(z).                                 (10)
```

Both triangles are entire: every integration variable in `(6)` and `(9)` stays in a compact
set.  Splitting the finite square according to `x>=y` and `x<=y` proves

```text
T_R(z)+T_L(z)=I(z),
I(z)=integral_(-a)^a h(x)e^(izx)dx.                     (11)
```

No transform of a nonintegrable bilateral kernel was taken in `(7)`--`(11)`.

## Theorem B: Suzuki's two sheets cancel bilaterally `[PROVED HERE]`

Evenness gives `M_-(z)=M_+(-z)` on their respective domains.  Suzuki 2023 equation (1.2), with
`g=-Psi`, identifies

```text
M_+(z)=M(z)=z^(-2)xi'(1/2-iz)/xi(1/2-iz),
Im z>1/2.                                                (12)
```

The Xi functional equation gives the meromorphic continuation law

```text
M_+(-z)=-M_+(z).                                       (13)
```

Consequently `(7)` and `(10)` continue as two distinct sheets:

```text
R^c(z)= M(z)V(z)-T_R(z),
L^c(z)=-M(z)V(z)-T_L(z).                               (14)
```

Adding and subtracting, then using `(11)`, yields

```text
R^c+L^c=-I,                                            (15)

R^c-L^c=2MV-(T_R-T_L).                                (16)
```

Equation `(15)` is decisive: every Xi pole cancels in the bilateral sheet sum before RH enters.
Therefore bilateral exterior holomorphy is automatic and cannot be an RH criterion.  Equation
`(16)` shows where the divisor actually lives: opposite residues on the two one-sided sheets.

The finite form shift adds an even rational `z^(-2)` term.  It changes neither conclusion about
nonreal Xi poles: reflection obeys

```text
M_eta(-z)=-M_(-eta)(z),                                (17)
```

and the arithmetic pole principal parts remain opposite.

## Theorem C: parity independently kills the bilateral reading `[PROVED HERE]`

At zero shift, `M` is odd.  Suzuki's reflection-normalized phase-one characteristic `W_1` is odd,
so

```text
M(z)W_1(z) is even.                                    (18)
```

The projected interval theorem proves that the corresponding nonzero central bracket is

```text
I_1(z)=2A sin(az),                                     (19)
```

which is odd.  Hence a proposed global identity `MW_1=I_1` forces `(19)` to vanish identically.
For `a!=0` and `A!=0`, evaluation at `z=i` contradicts the complex sine zero classification.
This falsifier uses only source parity and is independent of convergence details.

## Theorem D: corrected one-sheet RH criterion `[PROVED HERE]`

Let `W` be one entire Suzuki characteristic with only real zeros, and let `T_R` be the entire
right triangle in `(6)`.  Define

```text
E_R(z)=M_eta(z)W(z)-T_R(z).                             (20)
```

If RH holds, `M_eta` has no upper-half-plane Xi pole, so `(20)` is holomorphic there.  Conversely,
at an upper-half-plane Xi zero `z_0`, `W(z_0)!=0` and `T_R` is entire, so `(20)` has a simple pole
with the already computed multiplicity-weighted principal coefficient.  Centered Xi evenness
reflects every lower-half-plane zero into the upper half-plane.  Therefore

```text
RH
 iff E_R is holomorphic at every z with Im z>0.          (21)
```

The old abstract exterior-remainder algebra survives exactly after this semantic correction:
its `intervalPart` must be the one-sided triangle `T_R`, not the full interval transform `I`, and
its observable is one Carleman sheet, not a bilateral exterior sum.

## Impact on the preceding Suzuki corpus

1. Pole tomography and arbitrary two-shift affine sewing remain algebraically correct for a
   selected one-sided sheet.
2. Their previous description as a global/bilateral Fourier exterior is false.
3. The projected sine clock determines `T_R+T_L`; it does not identify `T_R` separately.
4. Bilateral sheet sums cannot prove RH because `(15)` removes the Xi multiplier identically.
5. The source-exact producer problem is now the continuation of `E_R` from the unconditional
   convergence region `Im z>1/2` through the strip `0<Im z<=1/2`.

Thus actual corpus frontier is

```text
construct actual admissible compact deficiency source
 -> form its right convolution triangle T_R by (6)
 -> identify right Carleman sheet E_R in Im z>1/2
 -> prove source-marked holomorphic continuation of E_R through 0<Im z<=1/2
 -> RH by (21).                                         (22)
```

No estimate-free algebra can replace last arrow: rational FE--Schwarz orbit insertion leaves the
finite-aperture Hilbert shell and parity pattern intact while inserting an upper-sheet Carleman
pole.  The required continuation theorem must use distinguished Euler--Gamma source marking and
must fail on that orbit-inserted countermodel.

## Novelty boundary

One-sided Fourier--Laplace splitting, Fubini triangles, and Fourier--Carleman transforms are
classical.  Candidate novelty is limited to the source-specific diagnosis and synthesis:

- Suzuki 2023 explicitly labels `(12)` one-sided and later uses a Fourier--Carleman quotient;
- Suzuki 2026 Section 8.3 instead writes an ordinary full transform of `g*v` and does not split
  the two exterior sheets;
- the current corpus previously corrected the repeated-`vhat` substitution and finite-Neumann
  flux, but not this transform-category mismatch;
- targeted arXiv searches found no paper deriving `(14)`--`(16)`, the parity contradiction
  `(18)`--`(19)`, or the corrected one-sheet criterion `(21)` for Suzuki's 2026 construction.

Priority remains externally unaudited.  No novelty is claimed for generic Carleman theory.

## Formalization

`GaloisForLFunctions.RHTower.Suzuki.SuzukiOneSidedCarlemanSeam` proves:

```text
suzukiCarlemanSheet_sum
suzukiCarlemanSheet_difference
suzukiZeroShiftMultiplier_odd
suzukiShiftedXiMultiplier_neg
suzukiZeroShiftCarlemanSheet_sum
suzukiZeroShiftBilateralMultiplierChannel_ne_projectedSineClock
riemannHypothesis_iff_suzukiRightCarlemanExterior_analytic_upper
```

The physical Fubini identities `(7)`--`(11)` are not replaced by abstract Lean hypotheses; the
formal module proves their dependency-closed analytic algebra and exact RH consumer.  Half-line
Fourier--Carleman integration is absent from current Lean libraries.

## Gates

- [x] corpus-wide collision search
- [x] cited 2023 formula checked in raw TeX
- [x] one-sided domain and parity discrepancy identified
- [x] prove triangular two-sheet decomposition
- [x] prove exact bilateral cancellation and one-sheet pole law
- [x] classify impact on prior exterior tomography and affine sewing
- [x] formalize dependency-closed algebraic core in Lean; exact module build, SOTA check, lint,
  and axiom audit passed
- [ ] identify a source-marked seam-crossing theorem strong enough to prove RH

## Log

- 2026-07-21 -- raw 2023 source confirms equation `(1.2)` is a one-sided transform on `t>=0`.
- 2026-07-21 -- even-kernel/odd-multiplier and `q=1` parity falsifiers found.
- 2026-07-21 -- exact Fubini triangles and opposite-sheet continuation proved.
- 2026-07-21 -- bilateral sum proved pole-free; right-sheet upper-half-plane RH criterion proved.
- 2026-07-21 -- dependency-closed Lean module, exact build, SOTA check, lint, and axiom audit pass.
