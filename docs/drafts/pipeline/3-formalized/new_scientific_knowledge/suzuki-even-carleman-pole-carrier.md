# Suzuki's projected clock is exactly the harmless odd half of the right Carleman sheet

> **Coordinate correction (2026-07-22).** Every carrier formula using centered
> `G_eta=XiC'/z^2XiC-eta/z^2` is in Xi-real Weyl normalization.  Its right/left triangle inputs
> are `-i` times physical Suzuki Volterra triangles; physical multiplier is `iG_eta` and exact
> one-sided real-shift coordinate is `eta=-i lambda/2`.  Parity, sheet-jump, pole, and RH
> equivalences survive.  Earlier physical interpretation of central flux, and resulting scalar
> phase no-go, are retracted by `suzuki-one-sided-coordinate-phase-normalization.md`.

- **ID:** `suzuki-even-carleman-pole-carrier`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CONJECTURE / FRONTIER REDUCTION
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SOURCE-SPECIFIC SYNTHESIS]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF] [NO NUMERICAL EVIDENCE]`
- **Primary sources:** Suzuki 2023, arXiv:2206.03682v4, Theorem 1.1(1) and Section 10;
  Suzuki 2026, arXiv:2606.09096v1, Sections 6 and 8.3
- **Parents:** `suzuki-one-sided-carleman-exterior-seam`,
  `suzuki-projected-continuous-deficiency-channel`
- **Statement:** For Suzuki's odd phase-one compact source, reflection fixes the odd part of its
  right convolution triangle to one half of the projected sine clock.  The right sheet's odd part
  is therefore the explicit entire function `-A sin(az)`; all possible Xi poles and the complete
  RH obstruction lie in one even Volterra carrier.
- **RH used:** no
- **Computation used:** no

> **Admissibility correction (2026-07-21).**  The single zero-shift phase-one theorem below is a
> valid algebraic specialization, but zero need not lie below Suzuki's finite-aperture spectral
> floor.  It is therefore not the unconditional source producer.  Two arbitrary distinct shifts
> below that floor are always available.  Affine sewing of their odd phase-one channels produces
> an **even** characteristic and reverses the carrier parity.  The dependency-closed actual-source
> replacement is Theorem D below: an odd sheet-jump carrier with an exact RH criterion.  C4 remains
> a useful one-source model, not the terminal admissible conjecture.

> **Scalar-positivity correction (2026-07-22).**  Earlier global falsification of C4 mixed
> Suzuki's physical triangle with Xi-real multiplier.  In correct one-sided coordinate physical
> multiplier is `iG_eta`, centered input is `-iT_phys`, and normalized central flux is real; C4
> remains open for a source-selected shift pair.  New large-negative-shift analysis falsifies
> **uniform-over-all-admissible-pairs** version: sufficiently negative dyadic pairs at small
> aperture violate mandatory central residue sign.  Scalar route therefore needs an intrinsic
> nonescaping shift law.  Parallel observable `J[m](z)=z*(z*m'(z)-m(z))` still removes irrelevant
> central pole and reduces RH to one independently analytic prime--Gamma source germ.

## Goal

Replace the still-undifferentiated right triangle in the corrected one-sheet frontier by its exact
reflection decomposition.  This determines which half of the physical right sheet is already
closed by the projected source calculation and which half still requires Euler--Gamma input.

## Actual corpus frontier

The corpus now proves, for a selected right sheet,

```text
E_R(z)=M(z)W_1(z)-T_R(z),
RH iff E_R is holomorphic for Im z>0.                         (1)
```

It also proves the complete projected interval law

```text
T_R(z)+T_L(z)=I_1(z)=2A sin(az).                             (2)
```

What it does not determine is `T_R` separately.  Suzuki 2023 Section 10 does not close this gap:
its global Fourier--Carleman formula is a quotient by a half-line transform and equals the same
meromorphic logarithmic derivative.  At a Xi zero the denominator vanishes and the quotient has
the pole already detected by `(1)`.  Mean periodicity supplies a global meromorphic identity, not
holomorphic seam crossing.

## Competing conjectures and hostile tests

### C1. Mean periodicity crosses the seam `[FALSIFIED]`

> The unconditional equation `g*eta'=0` turns the high-half-plane one-sided transform into a
> holomorphic function on the complete upper half-plane.

**Killing mechanism.**  Suzuki's Fourier--Carleman identity is explicitly a quotient of two
half-line transforms and equals `z^(-2) xi'/xi(1/2-iz)`.  It is meromorphic for all `z`, with the
same Xi poles.  At every nonreal Xi zero the all-real characteristic `W_1` is nonzero, so neither
the actual triangle nor mean periodicity cancels its principal part.

**Positive survivor.**  Mean periodicity certifies that the remaining obstruction is a genuine
divisor obstruction rather than a convergence artifact.  It must live in one reflection parity
of the right sheet; the theorem below identifies that parity exactly.

### C2. The projected sine clock controls the whole right triangle `[FALSIFIED]`

> Equation `(2)` determines `T_R`.

**Killing mechanism.**  `(2)` determines only a reflection difference once physical source parity
is imposed.  An arbitrary even entire summand can still be added to `T_R` and subtracted from
`T_L` without changing `(2)` or the reflection law.

### C3. Pair the even carrier with the even phase `[FALSIFIED]`

Let

```text
C_R(z)=M(z)W_1(z) - (T_R(z)+T_R(-z))/2.                    (3)
```

> Pairing `C_R` with the even characteristic `W_(-1)` makes `C_R/W_(-1)` a Weyl function.

**Killing mechanism.**  Both numerator and denominator are even, so the quotient is even.  It is
also Schwarz-real for the actual source.  If an even Schwarz-real function `q` were Herglotz on
the upper half-plane, then for every upper point `z`, the point `-conjugate(z)` would also be upper
and

```text
q(-conjugate(z))=q(conjugate(z))=conjugate(q(z)).
```

Herglotz positivity at both points forces `Im q(z)=0`; holomorphic openness then makes `q`
constant.  In particular an even quotient cannot have Donoghue normalization `q(i)=i`.  The
initial even-phase Weyl producer is impossible before arithmetic enters.

**Strongest positive survivor.**  A Weyl quotient carrying an even numerator must use an odd
denominator.  Suzuki parity uniquely selects the phase-one characteristic `W_1`, not `W_(-1)`.

### C4. Phase-corrected exterior Weyl completion `[OPEN FOR SOURCE-SELECTED SHIFTS]`

Define the phase-corrected exterior quotient

```text
m_ext(z)=-C_R(z)/W_1(z)
        =-M(z)+(T_R)_even(z)/W_1(z).                       (4a)
```

It is reflection-odd, as an even-measure Weyl function must be.  Since `W_1` has no nonreal zero,
holomorphy of `m_ext` in the upper half-plane is equivalent to holomorphy of `C_R` there and hence
to RH.  The exact source Gram target is

```text
K_ext(z,w)
 =(W_1(z) conjugate(C_R(w))-C_R(z) conjugate(W_1(w)))
   /(z-conjugate(w)).                                      (4)
```

Positive semidefiniteness of `(4)` is equivalent, by the nonvanishing `W_1` gauge, to the Pick
kernel of `m_ext`.  It would therefore prove RH by Theorem C.

The pole signs pass a nontrivial first hostile test.  At a real Xi zero `gamma!=0` where
`W_1(gamma)!=0`, exact pole tomography gives

```text
Res_gamma m_ext=-ord_gamma(XiC)/gamma^2<0,                (4b)
```

the required Herglotz atom orientation, independent of source normalization.  At a simple real
zero `x` of `W_1` away from the Xi divisor, the extra residue is

```text
Res_x m_ext=(T_R)_even(x)/W_1'(x).                        (4c)
```

Thus the remaining concrete boundary test is the source flux orientation
`(T_R)_even(x)/W_1'(x)<=0` at every odd-extension eigenvalue, followed by the full off-boundary
Gram identity `(4)`.  This is where the restricted Euler--Gamma operator must enter.

**Falsifier.**  A rational functional-equation--Schwarz orbit insertion preserves the local
all-real characteristic pair and the sine clock but inserts a nonreal pole in `C_R`.  Therefore
`(4)` fails for that countermodel.  Any proof of C4 must visibly use the Euler prime atoms and
Gamma/theta completion, not only abstract Hermite--Biehler or finite-aperture positivity.

## Theorem A: physical triangle reflection `[PROVED HERE]`

Let `g` be even, let `v` be an odd compact source supported in `[-a,a]`, and define the two
triangular interval responses

```text
h_R(x)=integral_(-a)^x g(x-y)v(y)dy,
h_L(x)=integral_x^a    g(x-y)v(y)dy.                       (5)
```

Then

```text
h_R(-x)=-h_L(x).                                          (6)
```

Indeed, substitute `y=-u`, use `v(-u)=-v(u)` and `g(-r)=g(r)`, and reverse the endpoints.  Taking
compact Fourier transforms gives

```text
T_L(z)=-T_R(-z).                                          (7)
```

The phase-one Suzuki characteristic is odd by the already formalized source involution.  Equation
`(7)` is therefore the physical triangle reflection belonging to that phase.  The same argument
applies distributionally to the compact effective source obtained after the first-order spectral
bracket; endpoint atoms are exchanged by reflection.

### Hostile source audit

Suzuki's minimal operator acts as `i d/dx`, so interval reflection anticommutes with it and sends
the `+i` deficiency line to the `-i` deficiency line.  The two deficiency vectors have equal norm;
their free phases may therefore be chosen so that `v_-(x)=v_+(-x)`.  In the phase-one boundary
bracket, multiplication by `z-i` and `z+i` turns this reflected pair into an odd compact effective
distribution, exactly as certified by the corpus theorem
`suzukiCharacteristicPencil_one_odd`.  Reflection exchanges derivative endpoint atoms in pairs.
The triangle diagonal contributes no anomalous atom because Suzuki's screw kernel satisfies
`g(0)=0`.  Hence `(7)` has the stated minus sign with no missing boundary correction.

## Theorem B: exact parity allocation `[PROVED HERE]`

For any function `F`, put

```text
F_even(z)=(F(z)+F(-z))/2,
F_odd (z)=(F(z)-F(-z))/2.                                 (8)
```

Combining `(2)` and `(7)` gives

```text
I_1(z)=T_R(z)-T_R(-z)=2 (T_R)_odd(z),
(T_R)_odd(z)=A sin(az).                                   (9)
```

At zero shift both `M` and `W_1` are odd, hence `MW_1` is even.  From `(1)` and `(9)`,

```text
(E_R)_odd(z)=-A sin(az),
(E_R)_even(z)=M(z)W_1(z)-(T_R)_even(z)=C_R(z),
E_R(z)=C_R(z)-A sin(az).                                 (10)
```

Thus the entire projected clock is exactly the odd half of the physical sheet, with the opposite
sign.  Every pole lies in the even carrier `C_R`.  This is stronger than saying that `(2)` does not
determine `T_R`: it classifies the undetermined freedom and the complete divisor carrier.

## Theorem C: even-carrier RH criterion `[PROVED HERE]`

The sine term in `(10)` is entire.  Therefore at every `z`,

```text
E_R analytic at z  iff  C_R analytic at z.                (11)
```

Applying the existing one-sheet theorem to `(11)` yields

```text
RH iff C_R is analytic at every z with Im z>0.             (12)
```

No positivity premise, estimate, computation, or RH assumption enters Theorems A--C.  They do not
prove the right side of `(12)`.  They show exactly where a successful proof must act: the even
Volterra boundary trace in `(3)`, not the projected sine clock, the bilateral sheet sum, or the
mean-periodic quotient.

## Theorem D: unconditional admissible sewing reverses the carrier parity `[PROVED HERE]`

At a fixed aperture, choose any two distinct actual form shifts `alpha,beta` below Suzuki's
spectral floor.  Such a pair exists for every real floor; no sign condition on the floor and no
zero-shift source are required.  Write the two phase-one characteristics and physical triangles as

```text
W_alpha, W_beta,
R_alpha,L_alpha, R_beta,L_beta.
```

Each characteristic is odd and each physical source is odd, hence

```text
W_eta(-z)=-W_eta(z),
L_eta(z)=-R_eta(-z).                                    (13)
```

Affine sewing to target shift zero gives

```text
P(z)=(beta-alpha)W_alpha(z)W_beta(z),
J_R(z)= beta W_beta(z)R_alpha(z)-alpha W_alpha(z)R_beta(z),
J_L(z)= beta W_beta(z)L_alpha(z)-alpha W_alpha(z)L_beta(z). (14)
```

The two minus signs in `(13)` cancel across each sewn term.  Therefore

```text
P(-z)=P(z),
J_L(z)=J_R(-z).                                         (15)
```

This is the parity transfer missed by the one-source model: the effective sewn source is even.
Affine sewing also commutes exactly with the physical triangle sum,

```text
J_R+J_L
 = beta W_beta(R_alpha+L_alpha)
   -alpha W_alpha(R_beta+L_beta).                        (16)
```

Using the already-proved projected clocks
`R_eta+L_eta=2A_eta sin(az)`, `(16)` becomes

```text
J_R(z)+J_L(z)
 =2sin(az)[beta W_beta(z)A_alpha-alpha W_alpha(z)A_beta]. (17)
```

Thus `(17)` computes the total sewn compact interval, not a one-sided triangle.  By `(15)` it is
exactly twice the reflection-even part of `J_R`.

The zero-shift multiplier `M_0` is odd while `P` is even, so `M_0P` is odd.  Define

```text
C_odd(z)=M_0(z)P(z)-(J_R(z)-J_R(-z))/2.                  (18)
```

Then `C_odd` is odd and the actual sewn right sheet has exact decomposition

```text
E_R(z)=M_0(z)P(z)-J_R(z)
      =C_odd(z)-(J_R(z)+J_L(z))/2.                       (19)
```

The second term is entire.  Existing admissible-pair pole tomography plus `(19)` proves

```text
RH iff C_odd is analytic at every nonreal point.          (20)
```

This is unconditional as a theorem about actual admissible source data.  It neither assumes zero
is admissible nor assumes RH.

## Theorem E: the RH carrier is the normalized Carleman sheet jump `[PROVED HERE]`

For arbitrary physical triangles define

```text
C_jump=M W-(R-L)/2.                                      (21)
```

Directly from the two continued sheets,

```text
2C_jump=E_R-E_L.                                         (22)
```

Odd one-source reflection makes `(21)` equal the even carrier `(3)`; even sewn reflection makes it
equal the odd carrier `(18)`.  Hence one invariant covers both parity presentations.  The actual
admissible Weyl candidate is

```text
m_ext(z)=-C_odd(z)/P(z)=-(E_R(z)-E_L(z))/(2P(z)).         (23)
```

Where `P` is nonzero, `(23)` is also exactly the negative reflection-odd part of the corpus's
projectively normalized affine exterior observable.  It is odd.  At every Xi zero not shared by
`P`, its meromorphic leading coefficient is

```text
TC_z(m_ext)=-ord_z(XiC)/z^2,                             (24)
```

independent of both shifts, both source gauges, and both triangles.  At a real nonzero Xi zero,
`(24)` has the negative residue orientation required of a Herglotz atom.

## Theorem F: exact central flux threshold `[PROVED HERE]`

The source divisor itself supplies a sharper hostile test that is invisible at nonzero Xi zeros.
Assume the two odd source characteristics have simple central zeros and write

```text
a_alpha=W_alpha'(0),  a_beta=W_beta'(0),
r_alpha=R_alpha(0),   r_beta=R_beta(0).                  (25)
```

Then the sewn characteristic has a forced double zero,

```text
P(z)/z^2 -> (beta-alpha)a_alpha a_beta,                  (26)
```

while the odd part of the sewn right triangle has first coefficient

```text
(J_R)_odd(z)/z
 -> beta a_beta r_alpha-alpha a_alpha r_beta.            (27)
```

Define the central source flux

```text
Phi_(alpha,beta)
 =(beta a_beta r_alpha-alpha a_alpha r_beta)
   /((beta-alpha)a_alpha a_beta)
 =1/(beta-alpha)
   [beta r_alpha/a_alpha-alpha r_beta/a_beta].           (28)
```

Centered Xi evenness and `XiC(0)!=0` give the exact multiplier residue

```text
z M_0(z) -> XiC''(0)/XiC(0).                             (29)
```

Consequently the mandatory central pole of the actual jump quotient has residue

```text
Res_0 m_ext
 =-XiC''(0)/XiC(0)+Phi_(alpha,beta).                     (30)
```

The corpus theta-cusp theorem proves unconditionally

```text
XiC''(0)/XiC(0)<0,  hence  -XiC''(0)/XiC(0)>0.           (31)
```

For any Herglotz function, the real part of a residue at a real pole is nonpositive: along
`z=x+iy`,

```text
Re[(z-x)m(z)]=-y Im m(z)<=0,
```

and passage to `y downarrow 0` gives the residue sign.  Applying this to `(30)` yields the new
necessary source law

```text
Re Phi_(alpha,beta)
 <= XiC''(0)/XiC(0) < 0.                                (32)
```

This is substantially stronger than asking for an unspecified negative source residue.  The
finite-aperture boundary flux must overcompensate the fixed positive Xi curvature by an exact
amount.  In particular any proposed Euler--Gamma colligation with nonnegative, zero, or merely
weakly negative central flux is falsified before any global Pick-kernel calculation.

Equation `(32)` is not RH in disguise: its left side uses only source derivatives and right
triangle boundary values.  What the corpus still cannot do is derive `(32)` from Suzuki's actual
prime-power/Gamma screw source.  The projected clock fixes the even part of `J_R` and has zero
first jet at the center; it contains no information about the odd coefficient `(27)`.  Canonical
finite Donoghue positivity also does not supply it: its quotient uses the opposite characteristic
divisor and is a different meromorphic function.

## Theorem G: the Neumann comparison channel cancels from the central flux `[PROVED HERE]`

The threshold can be localized further.  Let `nu_lambda` be the compact odd phase-one source
whose Fourier transform is `W_lambda`, and write its moments as

```text
mu_j(lambda)=<nu_lambda,y^j>.
```

This notation covers the ordinary integrable source and the compact distribution obtained after
the first-order spectral bracket.  Oddness gives `mu_0=mu_2=0`, while the Fourier convention gives

```text
W_lambda'(0)=i mu_1(lambda).                            (N1)
```

For the global Neumann representative `r_0(t)=-|t|/2`, its positive-half primitive is
`H_0(s)=-s^2/4` for `s>=0`.  The central value of its right convolution triangle is therefore

```text
T_(r0,R,lambda)(0)
 =-1/4 <nu_lambda,(a-y)^2>
 =(a/2)mu_1(lambda).                                   (N2)
```

The physical shifted kernel is `k_lambda=g-lambda r_0`.  If

```text
q_lambda=R_lambda(0)/W_lambda'(0),
q_lambda^EG=R_(g,lambda)(0)/W_lambda'(0),
```

then `(N1)--(N2)` give the exact decomposition

```text
q_lambda=q_lambda^EG+i(a/2)lambda.                     (N3)
```

No limiting argument occurs: `nu_lambda` may depend nonlinearly on `lambda`; only the explicit
Neumann kernel contribution is evaluated.  The sewn flux `(28)` is the affine-interpolation
value of `q` at target shift zero,

```text
Phi_(alpha,beta)
 =[beta q_alpha-alpha q_beta]/(beta-alpha).             (N4)
```

Every common linear shift channel lies in the kernel of this interpolation.  Substitution of
`(N3)` into `(N4)` cancels the two terms `i(a/2)alpha beta` exactly and leaves

```text
Phi_(alpha,beta)
 =[beta q_alpha^EG-alpha q_beta^EG]/(beta-alpha).       (N5)
```

This falsifies the conjecture that positivity of the finite Neumann comparison operator might
force the central residue sign.  That channel contributes identically zero to the **central source
flux**, even though it is the operator used to make every chosen finite shift positive.  The
threshold `(32)` is a pure Euler--Gamma edge invariant.  Shift dependence remains through the
actual resolvent-selected sources `nu_alpha,nu_beta`.

The later full-frequency audit shows this cancellation is not an identity of spectral functions.
Away from the center the Neumann triangle leaves the exact projective holonomy

```text
alpha beta sin(az)/(2z(beta-alpha))
 [W_alpha'(0)/W_alpha(z)-W_beta'(0)/W_beta(z)].         (N6)
```

Its universal central pole cancels, giving `(N5)`, but its higher jets generally survive.  See
`../../3-formalized/new_scientific_knowledge/suzuki/suzuki-full-frequency-neumann-holonomy-survivor.md`.

## Active frontier conjecture and decisive tests

The exact source Gram target is now the admissible jump kernel

```text
K_jump(z,w)
 =(P(z) conjugate(C_odd(w))-C_odd(z) conjugate(P(w)))
   /(z-conjugate(w)).                                    (33)
```

Because `P` has only real zeros, positive semidefiniteness of `(33)` on the upper half-plane is
equivalent through the nonvanishing `P` gauge to the Pick kernel of `(23)`.  Proving `(33)` from a
manifestly positive Euler--Gamma source colligation proves `(20)`, hence RH.  Positivity is not
avoided: its pole-exclusion consequence closes the RH-equivalent analyticity problem.  At present
full positivity may be strictly stronger because it also imposes signs at the real source divisor;
those flux signs are part of the construction, not silently attributed to RH.

Two scientific tests prevent a circular shortcut:

1. **Finite Donoghue equality is false.**  Suzuki's canonical finite Donoghue ratio has poles on
   one self-adjoint-extension divisor.  The jump quotient `(23)` additionally carries the Xi
   divisor by `(24)`.  They cannot be the same fixed-aperture meromorphic function.  Required
   object is a larger prime--Gamma dilation whose compression contains the finite interval
   operator, not relabeling the finite Donoghue quotient.
2. **Local-shell positivity is insufficient.**  Functional-equation--Schwarz orbit insertion can
   preserve the all-real finite characteristic family and projected clocks while inserting a
   nonreal jump pole.  Therefore a proof of `(33)` must use the distinguished global Euler prime
   atoms and Gamma completion.  Abstract Hermite--Biehler theory alone cannot prove it.

**[REOPENED -- COORDINATE CORRECTION]** Earlier falsification fed physical `T_phys` directly into
centered `G_eta W-I`.  Physical multiplier is `iG_eta`; canonical Xi-real sheet uses
`I=-iT_phys` and exact one-sided parameter `eta=-i lambda/2`.  Source quadrature makes physical
flux purely imaginary but normalized flux real, with `Re Phi_norm=Im Phi_phys`; it does not force
threshold `(32)` to fail.  Euler--Gamma jump colligation `(33)` is again live.  Centered Euler
source seam `D_src=J[m_ext]` remains an independent parallel conjecture.

**[FULL-FREQUENCY CORRECTION]** The first proposed square incorrectly discarded the Neumann
channel using central theorem `(N5)`.  Formula `(N6)` proves a prime--Gamma-only square cannot be
the full kernel.  Correct producer must factor Euler--Gamma curvature together with this centered
projective holonomy.  The holonomy has an exact finite-resolvent tangent formula, so it remains a
source-before-divisor term rather than an ad hoc repair.

## Novelty audit

Internal collision search found the one-sided seam theorem and the projected sine clock, but no
reflection-parity decomposition of `T_R`, no identification `(10)`, and no even-carrier criterion
`(12)`.  It also found no admissible two-shift parity transfer `(15)`, sheet-jump identity `(22)`,
or normalized odd-projection law `(23)`.  Targeted arXiv search found Suzuki 2023 and 2026 but no
source deriving these decompositions.
Generic Volterra reflection algebra is classical.  Candidate novelty is only the source-specific
allocation of Suzuki's projected clock and Xi divisor to opposite parities, plus the resulting
phase selection, universal residue orientation `(4b)`, Weyl producer `(4)`, and central
curvature-overcompensation law `(32)`.  The exact Neumann cancellation `(N2)--(N5)` further
separates comparison positivity from the RH-bearing Euler--Gamma edge flux.  Internal search found
no prior computation of the two-shift jump quotient's mandatory central residue or this
source-specific cancellation.  Priority remains unverified.

## Formalization

`GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanEvenPoleCarrier` proves the exact
dependency-closed theorem batch:

```text
suzukiRightTriangle_oddPart_eq_half_interior
suzukiEvenCarlemanPoleCarrier_even
suzukiEvenCarlemanPoleCarrier_eq_evenPart_rightSheet
suzukiCarlemanRightSheet_eq_evenPoleCarrier_sub_halfInterior
analyticAt_suzukiCarlemanRightSheet_iff_evenPoleCarrier
suzukiRightTriangle_evenPart_eq_half_interior
suzukiOddCarlemanPoleCarrier_odd
suzukiCarlemanRightSheet_eq_oddPoleCarrier_sub_halfInterior
analyticAt_suzukiCarlemanRightSheet_iff_oddPoleCarrier
suzukiCarlemanJumpPoleCarrier_eq_oddPoleCarrier
suzukiAffineSewnCharacteristic_even_of_odd
suzukiAffineSewnTriangle_reflection_of_odd
suzukiAffineSewnCarlemanInteriorPart_projectedSineClock
suzukiAffineSewnRightTriangle_evenPart_eq_half_projectedSineClock
riemannHypothesis_iff_suzukiAffineSewnOddCarlemanPoleCarrier_analytic_offReal
suzukiAffineSewnExteriorWeylQuotient_eq_neg_oddPart_normalizedExterior
meromorphicTrailingCoeffAt_suzukiAffineSewnExteriorWeylQuotient_of_XiC_zero
suzukiZeroShiftPhaseOneRightSheet_eq_evenPoleCarrier_sub_sine
riemannHypothesis_iff_suzukiEvenCarlemanPoleCarrier_analytic_upper
even_schwarz_value_I_ne_I
suzukiPhaseOneExteriorWeylQuotient_odd
suzukiExteriorWeylGram_eq_gauged_pick
meromorphicTrailingCoeffAt_suzukiPhaseOneExteriorWeylQuotient_of_XiC_zero
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanCentralFlux` proves the exact central hostile test:

```text
residue_re_nonpos_of_upperHalfPlane_im_nonneg
tendsto_z_mul_suzukiZeroShiftMultiplier
tendsto_suzukiAffineSewnCharacteristic_div_sq
tendsto_suzukiAffineSewnRightOddPart_div
suzukiAffineSewnCentralSourceFlux
suzukiAffineSewnCentralSourceFlux_centered_eq
suzukiNeumannRightTriangleCentralMoment
suzukiNeumannRightTriangleCentralMoment_of_odd
suzukiNeumannRightTriangleCentralMoment_div_fourierFirstJet
suzukiAffineSewnCentralSourceFlux_eq_normalized_intercept
suzukiAffineSewnCentralSourceFlux_linear_shift_channel_cancels
suzukiAffineSewnCentralSourceFlux_neumann_channel_cancels
tendsto_z_mul_suzukiAffineSewnExteriorWeylQuotient
suzukiAffineSewnCentralSourceFlux_re_le_XiC_curvature_of_herglotz
XiC_secondDeriv_div_center_re_neg
suzukiAffineSewnCentralSourceFlux_re_neg_of_herglotz
```

The physical integral reflection is represented by its exact source equation
`TLeft z = -TRight (-z)`; the paper proof above derives it from odd source/even kernel reflection.
The formal result does not replace that equation by an unrelated analytic premise.  Exact module
build, SOTA import check, formal lint, and axiom audit passed.  Every theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1: corpus frontier, source convention, competing conjectures, and falsifiers isolated
- [x] paper proof of physical reflection and exact parity allocation
- [x] paper proof of even-carrier RH equivalence from existing one-sheet theorem
- [x] 1 -> 2: hostile audit of distributional endpoint reflection and all sign conventions
- [x] 2 -> 3: exact Lean theorem batch and RH connector
- [x] falsify even-phase Weyl pairing and select the unique parity-compatible phase
- [x] verify universal Xi-pole orientation of the corrected quotient
- [x] remove zero-shift admissibility by exact two-shift parity transfer and odd jump carrier
- [x] identify actual Weyl candidate with normalized Carleman sheet jump and odd projective part
- [x] compute mandatory central source residue and exact curvature-overcompensation threshold `(32)`
- [x] prove direct Neumann comparison channel cancels identically from central flux `(N2)--(N5)`
- [x] retract mixed-coordinate `Re Phi=0` falsification after one-sided phase audit
- [x] falsify uniform scalar positivity on the large-negative dyadic escape cone
- [x] construct intrinsic source-selected shifts outside that cone via screw-Cesaro curvature
      recurrence
- [ ] prove normalized scalar Euler--Gamma Gram identity `(33)`
- [ ] construct analytic prime--Gamma source germ for `J[m_ext]`
- [ ] specialist novelty/priority review
- [ ] RH

## Log

- 2026-07-21 -- created after mean-periodicity was tested and rejected as a holomorphic seam
  mechanism; exact even/odd right-sheet allocation proved on paper.
- 2026-07-21 -- raw 2026 source audit verified deficiency-line reflection, phase normalization,
  and distributional endpoint sign; promoted to Stage 2.
- 2026-07-21 -- formal theorem batch, exact RH connector, SOTA import, lint, axiom audit, and
  targeted 8998-job module build passed; promoted to Stage 3.
- 2026-07-21 -- even-phase Weyl conjecture falsified by parity; positive survivor uniquely selects
  `m_ext=-C_R/W_1`, whose real Xi residues have the correct universal Herglotz sign.
- 2026-07-21 -- corrected the remaining source-admissibility gap: two odd phase-one source shifts
  sew to an even characteristic, a plus-reflected triangle pair, and an odd RH pole carrier.
- 2026-07-21 -- identified the carrier as half the physical Carleman sheet jump, proved its exact
  projective odd-part law and source-independent Xi-pole coefficient, and isolated the
  Euler--Gamma jump-colligation conjecture as the live RH step.
- 2026-07-21 -- computed the forced central pole exactly.  Herglotz positivity requires the
  finite-aperture source flux to lie below `XiC''(0)/XiC(0)<0`; the projected clock and finite
  Donoghue quotient do not control this missing odd source jet.  Formal residue and sign theorems
  added in `SuzukiCarlemanCentralFlux`.
- 2026-07-22 -- retracted mixed-coordinate phase no-go.  Exact physical multiplier is `iG_eta`,
  normalized interval input is `-iT_phys`, and one-sided coordinate is `eta=-i lambda/2`.
  Scalar jump Herglotz/Gram route is reopened; centered Euler observable remains parallel.
- 2026-07-22 -- proved large-negative-shift obstruction in correct coordinate.  At sufficiently
  small aperture, sufficiently negative dyadic pairs have central flux above Xi curvature and
  cannot be Herglotz.  Uniform C4 is false; source-selected nonescaping C4 remains open.
- 2026-07-22 -- screw-Cesaro recurrence supplied source-selected central-valid dyadic pairs.
  Full-frequency audit then proved direct Neumann cancellation is central-only and extracted exact
  projective-holonomy survivor `(N6)`; corrected Gram target couples it to Euler--Gamma response.
