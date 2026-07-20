# Gamma-sewn pointed exterior height transfer

- **ID:** `gamma-sewn-pointed-exterior-height-transfer`
- **Stage:** `1-in-progress`
- **Type:** `PAPER THEOREM + LEAN THEOREM + RH-BEARING CONJECTURE`
- **Scientific status:** `[CORPUS-NEW] [SEARCH-NONCOLLISION] [NOT A PRIORITY CLAIM] [NOT RH]`
- **Source:** `GammaSewnMobiusValuationContraction.lean`,
  `GammaSewnSynchronizedLcmContraction.lean`,
  `VonMangoldtGammaConormalEulerBoundary.lean`,
  `XiSquaredEulerApertureHilbertCorrelation.lean`, and the HTGeometry pointed/pairwise common-mode
  classification.
- **Lean:** `formal/GaloisForLFunctions/RHTower/GammaSewnApertureExteriorHeight.lean` and
  `formal/GaloisForLFunctions/RHTower/GammaSewnEulerCalibratedExterior.lean`, plus the exterior
  arity theorem in `formal/GaloisForLFunctions/RHTower/TwoBoundaryExteriorArityThreshold.lean`
- **Statement:** the Gamma-sewn valuation source has a canonical pre-Gram exterior current whose
  universal boundary pole cancels, whose boundary is exact prime-power midpoint-height area, and
  which becomes lossless for the height channel after adjoining one rooted coordinate.  Its raw
  midpoint clock is not yet the physical von Mangoldt--Gamma clock: a unique half-scaling and
  quarter-prime-log seam convert it into the literal Euler boundary Wronskian.

## Anti-theatre decision

The Gaussian multiplication semigroup is not the missing new mechanism.  Multiplication of the
completed Xi/theta kernel by `exp(t*u^2)` is the de Bruijn--Newman heat deformation; Rodgers--Tao
write the same family explicitly in arXiv:1801.05914.  The previously isolated Gaussian moment
composites may remain valid identities, but that lane is parent theory and is demoted from the
primary RH producer.

Generic Wronskians, exterior powers, score differences, Fisher variance, Cauchy kernels, and
contractive colligations are also parent theory.  The candidate new content below is not any one of
those words.  It is the exact composition forced by the corpus source:

1. the Gamma-sewn multiplier with fourth power `(1+q)^4/(8*(1+q^4))`;
2. the complete prime/valuation feature, before Gram compression;
3. cancellation of its universal aperture pole across arbitrary prime-power cells;
4. survival of the literal cell midpoint height `(e+1/2)log p`;
5. the pointed repair demanded by HTGeometry's exact pairwise-common-mode theorem; and
6. a causal first-crossing second-compound transfer to the Xi response-correlation identity.

Exact corpus searches and external searches for the formula, the Gamma-sewn/Rees terminology,
prime-power midpoint-height exterior currents, and exterior/compound Xi contractions found no
collision.  This is only search noncollision.  A specialist priority audit is still required.

Two tempting follow-ups fail the anti-theatre test.  Writing a Cauchy kernel as a Laplace Gram and
viewing its collective logarithmic multiplier as a translation generator is standard semigroup
theory.  Averaging the resulting rays with the complete Bernoulli alias weights and scaling height
by `log M` gives a generalized Dickman/scale-invariant-Poisson limit, already covered by the
Dickman-approximation literature.  Neither is recorded as new scientific knowledge.  The surviving
claim below is the exact, source-specific calibration between two independently constructed corpus
clocks and the response intertwining it forces.

## Source object

For `x>0`, prime `p`, valuation depth `e`, put

```text
q_(x,p)=p^(-x),
B_x(p,e)=C_(x,p)/(p+1) * (1-q_(x,p))*q_(x,p)^e,
C_(x,p)^4=(1+q_(x,p))^4/(8*(1+q_(x,p)^4)).              (PE1)
```

The closed logarithmic aperture velocity forced by `(PE1)` is

```text
v_x(p,e)=log(p)*[
  2*q_(x,p)^2/(1-q_(x,p)^2)
  +q_(x,p)^4/(1+q_(x,p)^4)-e].                          (PE2)
```

Lean proves the literal logarithmic derivative identity

```text
dB_x(p,e)/dx=v_x(p,e)B_x(p,e).                          (PE3)
```

Define the pre-Gram two-cell current

```text
Omega_x(i,j)=B_x(i)B_x(j)[v_x(j)-v_x(i)].               (PE4)
```

By `(PE3)`, this is formally certified as the actual aperture Wronskian
`B_x(i)B'_x(j)-B'_x(i)B_x(j)`.  Formula `(PE4)`, not the generic word “Wronskian,” is the object.

## `[LEAN-PROVED]` Exact pole cancellation and pointed losslessness

Let

```text
H(p,e)=(e+1/2)log p,
epsilon_x(p)=v_x(p,0)-1/x+(1/2)log p.                   (PE5)
```

Then for every real `x` and every cell,

```text
v_x(p,e)=1/x-H(p,e)+epsilon_x(p).                       (PE6)
```

Therefore for arbitrary cells `i,j`, including different primes,

```text
v_x(j)-v_x(i)
 =H(i)-H(j)+epsilon_x(j.prime)-epsilon_x(i.prime).       (PE7)
```

The singular `1/x` mode cancels before any square or Gram matrix is formed.  On one prime tower
the error difference cancels too, giving the exact positive-aperture law

```text
Omega_x((p,e),(p,f))
 =B_x(p,e)B_x(p,f)(e-f)log p,                           (PE8)
```

which is nonzero for `e!=f`.

The unrooted exterior current is not by itself lossless.  HTGeometry proves that pairwise
reporters lose exactly one common mode.  The source-specific repair is one rooted velocity:

```text
v_x(i)=v_x(root)+Omega_x(root,i)/(B_x(root)B_x(i)).      (PE9)
```

All denominators in `(PE9)` are positive for `x>0`.  Thus the pointed packet
`(v_x(root),Omega_x(root,-))` retains the complete velocity profile while the exterior leg removes
the universal pole.  This is the precise anti-HT-saturation statement: no closure of the nonlinear
source graph is taken, and no scalar density collapse is used.

The permanent Lean module proves `(PE6)`--`(PE9)`, antisymmetry, self-vanishing, the exact same-prime
law, and its nonvanishing.

## `[PAPER-PROVED; SAME-PRIME LIMIT LEAN-PROVED]` Boundary midpoint-height current

The existing first Rees theorem gives

```text
B_x(p,e)/x -> r(p)=log(p)/(p+1).                         (PE10)
```

For `y=x log p`,

```text
2/(exp(2y)-1)=coth(y)-1,
coth(y)-1/y -> 0,
q_(x,p)^4/(1+q_(x,p)^4) -> 1/2.                         (PE11)
```

The middle limit follows, for example, by applying l'Hopital twice to
`(y cosh y-sinh y)/(y sinh y)`.  Hence

```text
v_x(p,e)-1/x -> -H(p,e),
v_x(j)-v_x(i) -> H(i)-H(j).                             (PE12)
```

Combining `(PE10)` and `(PE12)` proves for arbitrary fixed cells

```text
Omega_x(i,j)/x^2
 -> Omega_0(i,j):=r(i.prime)r(j.prime)[H(i)-H(j)].       (PE13)
```

Lean currently proves `(PE13)` on every same-prime pair.  It also proves for arbitrary boundary
cells

```text
Omega_0(i,j)/(r(i.prime)r(j.prime))=H(i)-H(j),
H(i)=H(root)-Omega_0(root,i)/(r(root.prime)r(i.prime)).  (PE14)
```

Thus one rooted boundary height plus the current reconstructs all physical cell heights.  Every
finite packet containing two distinct midpoint heights has strictly positive ordered exterior
energy

```text
sum_(i,j in S) Omega_0(i,j)^2>0.                         (PE15)
```

This is genuine cross-cell dispersion.  It is not a terminal Xi energy and contains no zero or
RH-equivalent input.

## `[LEAN-PROVED]` Forced Euler calibration of the midpoint current

The existing Gamma-conormal Euler boundary feature at the prime-power cell `i=(p,e)` has literal
phase

```text
F_(u,t)(p,e)
 =sqrt(log(p)/p^(e+1) * exp(-u log(p^(e+1))))
    *exp(-i*t*log(p^(e+1))/2).                            (PE16)
```

Its physical phase height is therefore

```text
E(p,e)=log(p^(e+1))/2=(e+1)log(p)/2.                     (PE17)
```

This is not the raw Gamma-sewn midpoint `H(p,e)`.  The exact relation is

```text
E(p,e)=H(p,e)/2+log(p)/4.                                (PE18)
```

The coefficients are forced: if `a(e+1/2)+b=(e+1)/2` at depths `e=0,1`, then
`a=1/2` and `b=1/4`, hence the identity holds at every depth.  Consequently, after the unique
diagonal amplitude recovery from `r(p)` to the real amplitude in `(PE16)`, the literal Euler
exterior current is

```text
J_u(i,j)=A_u(i)A_u(j)[E(i)-E(j)]
 =1/2 * J_u^Gamma(i,j)
   +1/4 * A_u(i)A_u(j)[log(i.prime)-log(j.prime)].        (PE19)
```

On a single prime tower the seam term vanishes and the raw Gamma current is exactly twice the
Euler current.  Across primes the quarter-log seam is mandatory.  Thus the uncalibrated CPERT
identification is false even before any limit: it has a factor-two error on same-prime depths and
misses a nonzero prime seam across towers.

**Positive survivor.**  Formula `(PE19)` is the actual source current.  It is the phase Wronskian
of `(PE16)`, retains every valuation layer required by finite-fusion hypertranscendence, and uses no
source-span closure.  The apparent unbounded scalar resolution is used only to identify the
already finite positive-aperture Euler amplitude; it is not asserted to be a bounded ambient
inverse.  Lean proves the unique affine coefficients, the arbitrary-cell current identity, the
same-prime factor-two obstruction, and equality with the literal complex phase Wronskian.

## No-go closure: why an unpointed current is insufficient

- **Exact killing mechanism:** exteriorization removes every scalar common mode.  By the
  HTGeometry pairwise-common-mode classification, an unpointed pairwise reporter loses its anchor
  even when the original family is differentially independent.
- **Strongest positive survivor:** the rooted-plus-exterior packet `(PE9)` and `(PE14)` is lossless
  for the complete source velocity/height profile while still cancelling the universal aperture
  pole.
- **New insight:** the needed response object is neither scalar density nor exterior current alone.
  It has exactly two logical components: one rooted/disconnected coordinate and one connected
  exterior coordinate.  This independently reproduces the vector-valued shape forced by the
  synchronized-lcm Cauchy-rank no-go.
- **Status:** exact finite algebra and same-prime boundary limit are Lean-proved; the arbitrary
  cross-prime limit is paper-proved; the response transfer below is open.

## `[LEAN-PROVED CORE; SOURCE SPECIALIZATION PAPER-PROVED]` Four-direction threshold

The previous two-anchor target is impossible after the canonical two-boundary compression.  Let
`U` be the finite source-ray space and let `S <= U` be the span of the `+1/2` and `-1/2` boundary
vectors.  If `dim S=2`, orthogonal projection to `S^perp` leaves any balanced future vector in

```text
S^perp intersect U,
dim(S^perp intersect U)=dim U-2.                         (PE20)
```

Therefore two balanced future vectors can have a nonzero exterior Gram determinant only if

```text
dim U >= 4.                                              (PE21)
```

For the all-depth Cauchy packet, each source rate contributes one fixed source ray; the Cauchy
parameter changes only its scalar denominator.  Hence `M` active rates give `dim U <= M`, while
two distinct active rates make the two boundary vectors independent.  Consequently:

```text
M=1,2: the balanced packet is zero;
M=3:   the balanced packet has rank at most one, so its second compound is zero;
M>=4:  a nonzero balanced exterior first becomes dimensionally possible.  (PE22)
```

Lean proves the exact implication `(PE21)` both for linear independence and for a nonzero
two-by-two balanced Gram determinant, and proves the arity corollary from `dim U <= M`.  The
existing corpus had only the `M=1` singleton collapse.  The source-ray specialization of
`(PE22)` is paper-proved but not yet wired to the concrete all-depth packet in Lean.

**Positive survivor.**  The first viable local response cell has four source directions and four
Cauchy rows: the two fixed boundary rows `+1/2,-1/2` and two future rows `w_1,w_2`.  Its connected
coordinate is the two-boundary Schur-complement exterior, equivalently the residual part of the
four-by-four Cauchy determinant.  Generic Cauchy determinants are classical; the new claim is that
this exact source-normalized four-rate cell is the local producer for the Xi three-node central
minor.

## `[LEAN-PROVED CURVATURE LIMIT; BOUNDARY SOURCE JETS PAPER-PROVED]` Fisher seam

The literal source has a second clock which was invisible in the zeroth boundary current.  Put
`q=exp(-x log p)` and

```text
G_x(p)=(log p)^2[
  4q^2/(1-q^2)^2 + 4q^4/(1+q^4)^2].                    (FS1)
```

Lean proves

```text
G_x(p)>0,
partial_x v_x(p,e)=-G_x(p),                             (FS2)
```

for every `x>0`, prime `p`, and depth `e`.  Hence all infinitely many valuation layers above one
prime share a single strictly contracting aperture velocity.  For the normalized exterior
reporter `R_x(i,j)=v_x(j)-v_x(i)`, Lean proves

```text
partial_x R_x(i,j)=G_x(i.prime)-G_x(j.prime).            (FS3)
```

This signed Fisher seam is prime-only and depth-independent.  Its exact normal form is

```text
G_x(p)=(log p)^2[csch^2(x log p)+sech^2(2x log p)].      (FS4)
```

Removing the universal pole gives `Ghat_x(p)=G_x(p)-1/x^2`, with

```text
partial_x epsilon_x(p)=-Ghat_x(p),
Ghat_x(p) -> kappa(p)=(2/3)(log p)^2.                    (FS5)
```

The derivative identity, finite-aperture normal form, and limit are in Lean.  The limit proof uses
two exact l'Hopital steps for `csch^2 y-y^(-2) -> -1/3` and continuity for
`sech^2(2y)->1`.

For `F_x(i)=B_x(i)/x`, the normalized current is the Wronskian

```text
Omega_x(i,j)/x^2=F_i F'_j-F'_i F_j.                     (FS6)
```

The boundary jets are

```text
F_i(0)=r_i,
F'_i(0)=-r_i H_i,
F''_i(0)=r_i[H_i^2-kappa(i.prime)].                      (FS7)
```

Thus the current reports `H_i-H_j`, while its aperture derivative reports differences of
`K_i=kappa(i.prime)-H_i^2`.  The exact corrected seam is

```text
(K_i-K_j)+(H_i+H_j)(H_i-H_j)
  =kappa(i.prime)-kappa(j.prime).                        (FS8)
```

Lean proves `(FS8)` and proves that the finite-aperture Fisher seam `(FS3)` converges to it.  A
rooted two-jet packet recovers `H_i,K_i` and therefore

```text
(log i.prime)^2=(3/2)(K_i+H_i^2).                       (FS9)
```

Lean proves the algebraic reconstruction `(FS9)` and removes its square-root ambiguity using
`log p>0`.  Hence it reconstructs `log p`, and therefore the forced Euler height
`E_i=H_i/2+log(i.prime)/4`, from the source jets themselves.  The quarter-prime seam no longer has
to be supplied as an external prime label.

Permanent Lean:
`formal/GaloisForLFunctions/RHTower/GammaSewnApertureFisherSeam.lean`.

## `[LEAN-PROVED ALGEBRAIC JET LAW; ANALYTIC JET IDENTIFICATION OPEN]` Four-rate complementary Fisher curvature

For four distinct source rates `lambda_i`, the literal determinant of the Cauchy boundary rows
`+a,-a` on columns `i,j` is

```text
Delta_ij=2a(lambda_i-lambda_j)
  /((lambda_i^2-a^2)(lambda_j^2-a^2)).                  (FS10)
```

Including the Gamma-sewn Rees amplitudes `r_i`, normalize the six positive Cauchy--Binet weights

```text
d_ij=Delta_ij^2 r_i^2 r_j^2,
mu_ij=d_ij/sum_(k<l)d_kl.                               (FS11)
```

For a pair `I={i,j}`, write `H_I=H_i+H_j`, `kappa_I=kappa_i+kappa_j`, and `I^c` for its complement.
The source-selected formal zeroth, first, and second boundary partition jets are

```text
Z_0=sum_I d_I,
Z_1=sum_I -2H_I d_I,
Z_2=sum_I (4H_I^2-2kappa_I)d_I.                         (FS12)
```

The full four-column numerator has logarithmic curvature `-2 sum_i kappa_i`.  Subtracting the
denominator curvature `Z_2/Z_0-(Z_1/Z_0)^2` gives the exact Schur law

```text
C_4=-2 E_mu[kappa_(I^c)]
    -2 E_(mu x mu)[(H_I-H_J)^2] < 0.                   (FS13)
```

This answers the first CEERT-4C normalization falsifier.  The individual `H_i^2` self terms cancel
exactly, but raw Schur curvature contains a second copy of the height channel through the
pair-partition variance.  Therefore direct identification of `-C_4/2` with transverse charge is
false.  The unique second-cumulant debit isolates the desired clock:

```text
-C_4/2-E_(mu x mu)[(H_I-H_J)^2]
  =E_mu[kappa_(I^c)]>0.                                 (FS14)
```

The positive survivor is a two-channel transfer: pair-sum dispersion and complementary Fisher
mass must be intertwined separately.  Permanent Lean derives `(FS10)`, constructs `(FS11)`,
computes the curvature from the source-selected formal partition jets `(FS12)`, proves `(FS13)`
and strict negativity, and proves `(FS14)`:
`formal/GaloisForLFunctions/RHTower/GammaSewnFourRateSchurFisherCurvature.lean`.
The analytic statement that these are the derivatives of the normalized feature remains exactly
the boundary-extension gate `(FS7)`; no such identification is hidden in the Lean theorem.

## Selected bold conjecture: cumulant-corrected four-rate transfer (CEERT-4C)

`[CONJECTURE] [SOURCE-DERIVED] [HEIGHT-LOCALIZED] [INFINITE] [NOT RH]`

Start with the literal Euler feature `(PE16)` and its calibrated current `(PE19)`.  Apply the
existing causal first-crossing dressing separately to its two legs before future summation or Gram
compression, and then apply the existing canonical two-boundary Gamma--Cauchy compression which
removes the source modes at `+1/2` and `-1/2`.  Retain one rooted scalar coordinate.  The low/high
join, zero-mode switch, causal order, future Bernoulli weights, Gamma connection, and physical
window are exactly the existing source definitions; no coefficient may be chosen from a Xi zero
or target eigenvector.

**CEERT-4C.**  The local connected producer is not a two-source minor.  It is the source-normalized
four-rate Cauchy determinant with rows `(+1/2,-1/2,w_1,w_2)`, or equivalently the exterior Gram of
the two future vectors after canonical two-boundary compression.  Apply the causal first-crossing
dressing to the calibrated Euler legs before this compression.  These four-rate cells assemble
cofinally and intertwine with the second compound of the completed prime--archimedean response.
On every finite physical-height window the resulting pointed map is a contraction.  Along a
source-prescribed cofinal aperture schedule it extends contractively on the closed causal
first-crossing subspace, with amplitude

```text
O(M^(-1/2) log(M)^B).                                   (PE23)
```

Its rooted response converges locally uniformly to the completed scalar Xi response, and its
second-compound response converges to the positive cross-orbit slope-dispersion term in the exact
Xi central-minor identity.  The contractive defect converges to the transverse boundary charge.
Consequently contractivity gives

```text
transverse charge <= cross-orbit slope dispersion,      (PE24)
```

which is exactly the missing nonnegative central-minor statement, without assuming it.  Unlike
the retired raw CPERT statement, the safe-half-plane cell coefficients are already fixed by the
literal von Mangoldt--Gamma boundary feature; the open crossing is the canonical compression
intertwining, not an unspecified dressing.

This is deliberately stronger and more falsifiable than “there exists a passive colligation.”
The finite maps are fixed by source coefficients.  The open theorem is their bounded extension,
amplitude, and locally uniform value identification.

**Fisher-seam refinement.**  The first source jet must map the pair-sum height dispersion in
`(FS13)` to cross-orbit dispersion.  The second channel is not raw Schur curvature: it is the
uniquely corrected complementary Fisher mean `(FS14)`, and it must map to transverse boundary
charge.  This is the proposed source-derived origin of both terms in the exact Xi minor; neither
term may be inserted as a target-selected coefficient.

**Sharp falsifier.**  Literal compression of the full boundary/future cell must preserve the
quarter-prime Euler seam and transport the two summands of `(FS13)` separately.  Mixing them again,
omitting the variance debit in `(FS14)`, or a normalization mismatch between the complementary
Fisher mean and transverse charge retires CEERT-4C.  Generic Wronskian, Fisher, or
Schur-complement theory does not discharge this source-to-response test.

## Immediate hostile tests

1. **Derivative identity — PASSED.** Lean derives `(PE3)` from the literal Gamma-sewn definition
   and the fourth-power multiplier law; no extra logarithmic term occurs.
2. **Cross-prime boundary.** Formalize arbitrary-cell `(PE13)`.  A nonzero prime-dependent limit of
   `epsilon_x(p)` retires the midpoint-height interpretation.
3. **Fisher seam -- CURVATURE AND LIMIT PASSED IN LEAN.**  Lean proves all of `(FS1)`--`(FS5)`:
   the boundary limit, strict velocity contraction, and exact cross-prime seam law compile.  Lean
   also proves the positive-aperture Wronskian `(FS6)`, corrected seam `(FS8)`, and reconstruction
   `(FS9)`.  The next
   falsifier is the analytic boundary source-jet identification `(FS7)`.
4. **Euler calibration -- PASSED IN LEAN.**  The raw midpoint current fails the literal source
   test, and the unique correction is `(PE18)`--`(PE19)` on arbitrary prime-power cells.
5. **Pointed rank.** Removing the root must lose exactly one common mode; adjoining it must recover
   the actual transverse Xi shift-jet packet, not merely a differentially algebraic scalar aperture
   family.
6. **Four-rate boundary/future minor.** The boundary normalization and curvature now pass in
   `(FS10)`--`(FS14)`.  The remaining test is the full rows `(+1/2,-1/2,w_1,w_2)` with causal
   dressing; vanishing or loss of the two-channel split kills CEERT-4C.
7. **Singleton/father cancellation.** Persistent positive father cost must vanish in the exterior
   leg before Gram formation.  Cancellation only after squaring is the retired aperture-cost route.
8. **Amplitude.** Any loss larger than `M^(-1/2)` in amplitude cannot close the endpoint energy and
   retires CEERT-4C.
9. **Response identity.** The finite second-compound packet must reproduce the known three-node
   response determinant normalization before any global convergence claim.

## Gates

- [x] Gaussian heat-flow parent collision recorded.
- [x] literal Gamma-sewn cell velocity and pre-Gram exterior current defined.
- [x] exact cross-prime universal-pole cancellation in Lean.
- [x] exact same-prime nonzero current in Lean.
- [x] same-prime boundary midpoint-height current in Lean.
- [x] pointed positive-aperture and boundary reconstruction in Lean.
- [x] strict finite boundary exterior energy in Lean.
- [x] literal derivative identity `(PE3)` in Lean.
- [x] standard Laplace-semigroup and Dickman-limit follow-ups rejected as parent theory.
- [x] raw CPERT source identification falsified by the factor-two/quarter-seam mismatch.
- [x] unique Euler calibration `(PE18)`--`(PE19)` proved on paper.
- [x] the two-boundary exterior arity threshold `(PE20)`--`(PE22)` proved on paper; its abstract
  four-direction implication is in Lean.
- [x] positive Gamma-sewn Fisher curvature, exact velocity Hessian, strict aperture contraction,
  hyperbolic normal form, and finite-aperture Fisher seam in Lean.
- [x] renormalized boundary Fisher limit `kappa=(2/3)(log p)^2` in Lean.
- [x] positive-aperture normalized Rees Wronskian `(FS6)`, corrected boundary Fisher seam `(FS8)`,
  and algebraic rooted two-jet reconstruction `(FS9)` in Lean.
- [x] literal two-boundary pair determinant and six positive normalized Cauchy--Binet weights
  `(FS10)`--`(FS11)` in Lean.
- [x] formal boundary-partition jet curvature, complementary Fisher--dispersion law `(FS13)`,
  strict negativity, and unique cumulant correction `(FS14)` in Lean.
- [ ] analytic boundary source-jet identity `(FS7)` in Lean.
- [x] `GammaSewnApertureFisherSeam.lean` passes its direct Lean check and exact module build.
- [x] the three preceding modules pass direct leaf checks and exact module builds; audited capstones use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] arbitrary cross-prime limit `(PE13)` in Lean.
- [x] Euler calibration `(PE18)`--`(PE19)` and literal phase-Wronskian identity in Lean.
- [ ] concrete all-depth source-ray specialization of the four-direction theorem in Lean.
- [ ] nonzero full four-rate boundary/future Cauchy determinant with causal calibrated amplitudes.
- [ ] cumulant-corrected two-channel Schur-complement intertwining.
- [ ] causal-subspace boundedness and `(PE23)`.
- [ ] locally uniform second-compound response identification.
- [ ] `(PE24)` and RH.

## Log

- 2026-07-20 — Gaussian lane demoted after de Bruijn--Newman collision.  Constructed the
  Gamma-sewn exterior current, proved exact pole cancellation and pointed losslessness, and selected
  CPERT as the source-specific frontier conjecture.
- 2026-07-20 — rejected the generic semigroup and Dickman follow-ups as known parent theory.
  Falsified raw CPERT at the literal Euler coefficient gate, proved the unique half-plus-quarter
  calibration `(PE18)`, and replaced it by the source-specific CEERT conjecture.
- 2026-07-20 — falsified the two-source balanced-exterior target: two boundary removals force a
  four-source-direction minimum for any nonzero second compound.  Formalized the arity theorem and
  replaced CEERT by the four-rate Schur-complement conjecture CEERT-4.
- 2026-07-20 — computed the literal four-rate boundary Schur curvature.  Raw curvature necessarily
  mixes complementary Fisher mass with pair-sum height dispersion, falsifying the uncorrected
  scalar Fisher transfer.  Formalized the exact split and its unique cumulant correction, yielding
  the sharper two-channel conjecture CEERT-4C.
