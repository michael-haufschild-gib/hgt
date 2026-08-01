# Suzuki--Donoghue defect spectral-measure law

- **Status:** fully proved on paper; exact analytic connectors formalized separately
- **Claimed delta:** Suzuki's normalized finite-aperture Herglotz carrier is exactly the
  Donoghue transform of the spectral probability of the normalized positive deficiency vector
  for the canonical even extension.  Its Nevanlinna measure has zero linear mass and explicit
  atomic weights given by restricted-Weil resolvent projections.
- **Unconditional:** yes; fix `a>0` and any admissible shift `lambda<lambda_a`
- **Numerics/computation:** none
- **RH:** not assumed and not proved
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096

## 1. Source setup

Fix `a>0` and `lambda<lambda_a`.  Write

```text
T=A_a-lambda I > 0,
H_T=completion of C_c^infty(-a,a) in <u,v>_T=<Tu,v>_L2,
D=i d/dx on its minimal domain in H_T.
```

Suzuki proves that `D` is densely defined symmetric with deficiency indices `(1,1)`.  For every
`z in C`, its adjoint eigenvector `v_z` is uniquely fixed by

```text
T v_z=e^{-izx}.                                           (1)
```

Put `v_+=v_i`, `v_-=v_{-i}` and

```text
F(z)=int_{-a}^a v_+(x)e^{izx} dx,
A(z)=(z-i)F(z),
E(z)=(z+i)F(-z),
W_u(z)=A(z)+uE(z),       |u|=1.                           (2)
```

Reality and parity of the restricted-Weil kernel give `v_- (x)=v_+(-x)`.  Suzuki's boundary-form
calculation gives

```text
<v_z,v_+>_T=F(-z),
<v_z,v_->_T=F(z),
Theta(z)=A(z)/E(z)
        =(z-i)/(z+i) * <v_z,v_->_T/<v_z,v_+>_T.           (3)
```

The already proved all-angle Hermite--Biehler theorem gives `|Theta(z)|<1` on the upper half-plane
and `Theta(i)=0`.  The reference extension selected by the normalized deficiency basis is

```text
L=D_pi,    Dom(L) contains v_+-v_-,                       (4)
```

because `u=-1` is Suzuki's canonical even phase.  Its eigenvalues are exactly the zeros of
`W_{-1}=A-E`.

Define

```text
m(z)=i(1+Theta(z))/(1-Theta(z))
    =-i W_1(z)/W_{-1}(z).                                 (5)
```

Then `m(i)=i`, `m(-z)=-m(z)`, and `m` is Herglotz on the upper half-plane.

## 2. Exact Donoghue identity

Let

```text
N=||v_+||_T^2=F(-i)>0,
g=v_+/sqrt(N),
nu(B)=||1_B(L)g||_T^2.                                   (6)
```

Thus `nu` is the spectral probability measure of the normalized positive deficiency vector for
the canonical even extension.  Equations `(3)`--`(4)` are exactly Livsic's normalized
characteristic function for the pair `(D,L)`.  The Livsic--Donoghue Cayley relation therefore
gives, for `Im z>0`,

```text
m(z)
 = z+(z^2+1)<(L-zI)^{-1}g,g>_T
 = int_R (tz+1)/(t-z) dnu(t)
 = int_R [1/(t-z)-t/(1+t^2)] (1+t^2)dnu(t).              (7)
```

The second equality is the spectral theorem; the last uses the exact kernel identity

```text
(tz+1)/(t-z)=(1+t^2)/(t-z)-t.                            (8)
```

Consequently the complete normalized Nevanlinna data are

```text
linear coefficient at infinity: 0,
affine constant:                 0,
finite-plane measure:            dmu(t)=(1+t^2)dnu(t).    (9)
```

The first zero is structural, not an asymptotic estimate: a densely defined deficiency-`(1,1)`
operator produces a Donoghue-class function, whose representation has no linear term.  Oddness of
`m` forces the affine constant to vanish and makes `nu` and `mu` even.

This closes items 1--2 of the measure construction requested in the Suzuki handover.  The measure
is not an abstract existence object: `(6)` identifies it as a concrete restricted-Weil resolvent
spectral probability.

## 3. Pure-point formula and source weights

The functions `A` and `E` are entire because the source interval is compact.  Hence `(5)` is a
meromorphic Herglotz function.  Its measure is therefore pure point.  The source minimal operator
is prime: if a vector is orthogonal to every `v_z`, `(1)` makes its compactly supported Fourier
transform vanish identically, hence the vector is zero.  Thus `g` is cyclic for `L`, no extension
eigenvalue is invisible, and common real zeros of `A` and `E` do not occur.

For an eigenvalue `x` of `L`, normalize

```text
phi_x=v_x/||v_x||_T.
```

The spectral probability and Nevanlinna weights are

```text
p_x := nu({x})
     = |<v_+,phi_x>_T|^2/N
     = |F(-x)|^2/(N ||v_x||_T^2),                        (10)

mu_x := mu({x})
      = (1+x^2)p_x
      = (1+x^2)|F(-x)|^2/(N ||v_x||_T^2).                (11)
```

In particular,

```text
p_x>0,      p_{-x}=p_x,      sum_x p_x=1.                (12)
```

Formula `(11)` is the concrete source identity missing from the previous frontier.  It expresses
every finite-aperture Clark/Nevanlinna atom using only Suzuki's Fourier deficiency channel and the
norm of the actual extension eigenvector.

## 4. Residues, phase speed, and canonical interlacing

Write `Theta(x)=e^{i phi(x)}` on a real interval avoiding poles.  At a pole of `m`, equivalently
`Theta(x)=1` or `W_{-1}(x)=0`, equations `(5)` and `(11)` give

```text
Res_{z=x} m(z)=-mu_x,
phi'(x)=2/mu_x
       =2N||v_x||_T^2/((1+x^2)|F(-x)|^2)>0.              (13)
```

Thus the extension phase has an exact Wigner--Smith speed equal to the reciprocal source spectral
weight.  Between consecutive poles of `m`,

```text
m'(x)=int_R (1+t^2)/(t-x)^2 dnu(t)>0.                    (14)
```

The function rises from `-infinity` to `+infinity`, so it has exactly one zero in each pole gap.
The poles are the zeros of the even member `W_{-1}` and the zeros of `m` are the zeros of the odd
member `W_1`.  Therefore these two canonical Suzuki extension spectra strictly interlace.  Parity
puts the forced central eigenvalue `0` in the odd spectrum and no zero at the center in the even
spectrum.

This is stronger than Suzuki's separate real-zero theorem: it orders the two canonical divisors
and assigns every even-extension point its exact positive source weight.

## 5. Free-boundary consistency check

For the far-negative free interval, the even-extension poles are

```text
x_k=(k+1/2)pi/a.
```

Substitution of `T=cI`, `v_+(s)=c^{-1}e^s`, and `v_x(s)=c^{-1}e^{-ixs}` into `(11)` gives

```text
mu_{x_k}=coth(a)/a,
p_{x_k}=coth(a)/(a(1+x_k^2)).                            (15)
```

Hence `(7)` recovers exactly the previously derived free measure

```text
mu_a=(coth(a)/a) sum_{k in Z} delta_{x_k}.                (16)
```

This is a symbolic specialization, not a numerical check.  It fixes all signs and the factor
`1+x^2` in `(11)`.

**The cancellation that makes `(15)` come out constant is formal**, in
`formal/GaloisForLFunctions/HTGeometry/HyperbolicModulus.lean`:

- `normSq_sinh_sub_mul_I`: on a vertical line the squared modulus of `sinh` separates as
  `sinh^2 a cos^2 θ + cosh^2 a sin^2 θ`.
- `cos_quarterPeriod_eq_zero`, `normSq_sinh_sub_mul_I_of_cos_eq_zero`: at the quarter-period
  frequencies `x_k = (k+1/2)pi/a` the cosine vanishes, so the modulus is exactly `cosh^2 a` —
  independent of the mode.
- `quarterPeriod_weight_const`: **the free-clock cancellation** — the `1+x^2` of the weight is
  exactly cancelled by `|1 - i x|^2`, leaving `cosh^2 a` with no dependence on `x`.

That is the mechanism behind flat free-clock weights, and it is what `(15)` uses to fix the factor
`1+x^2`: the constancy is not a coincidence of the aperture but the identity `|1-ix|^2 = 1+x^2`
meeting a vanishing cosine.

The two normalizations and the final value are formal in the same module:

- `integral_exp_two_mul`: the deficiency normalization is `N = sinh(2a)`.
- `integral_one_symm`: the eigenvector normalization is the aperture length `2a`.
- `freeClockWeight_eq_coth`: **`(15)`'s value** — `4 cosh^2 a / (2a sinh 2a) = coth(a)/a`, by the
  double-angle identity.

The deficiency transform itself is formal too:

- `integral_exp_mul_symm`: the symmetric exponential integral `int_{-a}^{a} e^{w s} ds` is
  `2 sinh(w a)/w`, so the free model's `F` is an explicit hyperbolic sine over the spectral factor.
- `normSq_freeDeficiencyTransform`: **the free-model weight is flat** — at a quarter-period frequency
  the squared modulus against `1 + x^2` is `4 cosh^2 a`, independent of the mode.

So `(15)`'s constant is formal end to end: the deficiency transform, its constant modulus, the two
normalizing integrals, and the double-angle identity.  Only the identification of the free model's
`v_+` and `v_x` with the explicit exponentials remains, and that is the same operator identification
the rest of the card waits on.

## 6. Consequences for the live RH route

The cofinal Suzuki state is no longer an unspecified Clark measure.  It is the probability
`nu_{a,lambda}` in `(6)`, and every possible degeneration is visible as spectral mass movement of
one explicit normalized vector:

```text
ground escape:      nu loses tightness toward the projective point at infinity;
free homogenization: mu-atoms flatten to the constant clock weights in (15);
divisor survival:   an infinite tight atomic part of nu remains and its support converges;
Xi identification:  the support and weights satisfy the global de Branges spectral law. (17)
```

Common rescaling of the two deficiency vectors cancels from `(10)`, so `nu` is the correct
projective state for an intrinsic shift selector.  A quantile or tightness normalization must be
imposed on `nu`, not on an unnormalized residue or on one defect jet.

The exact non-clock observable is now also clear.  The free clock has constant Nevanlinna weights,
equivalently constant boundary phase speed.  For the actual source the deviation is

```text
(1+x^2)|F(-x)|^2/||v_x||_T^2,                            (18)
```

up to the common factor `N`.  Proving persistent non-flatness on an expanding family of atoms is a
source-level route to exclude clock homogenization.  A finite number of unequal weights is not
enough and is not claimed to be enough.

## 7. Hostile audit

1. **No hidden `lambda=0`.**  The proof uses only `lambda<lambda_a`, so `T>0` unconditionally.
2. **Reference-extension sign.**  Livsic's reference domain contains `g_+-g_-`; this is exactly
   Suzuki's `u=-1` extension.  Its zeros are poles of `(5)`.  The free specialization `(15)` checks
   the sign and phase.
3. **Inner-product orientation.**  Suzuki's boundary calculation gives
   `<v_x,v_+>_T=F(-x)` for real `x`; absolute squares remove the remaining conjugation convention.
4. **No linear mass smuggled away.**  Formula `(7)` is the Donoghue resolvent formula itself, not a
   generic Herglotz representation normalized after the fact.  Its spectral measure is a
   probability and its linear coefficient is identically zero.
5. **Atomicity.**  It follows from meromorphic continuation of `(5)`, not from an assumed compact
   resolvent.  Primeness/cyclicity rules out invisible self-adjoint summands and common zeros.
6. **No clock overclaim.**  Equation `(18)` identifies the full weight field.  Excluding its clock
   limit still requires a cofinal, infinite-atom source theorem.
7. **No RH conclusion.**  Tightness, intrinsic shift selection, and Xi divisor identification
   remain open.

## 8. Literature and priority audit

The abstract ingredients are classical and are not claimed as new:

- Donoghue's Weyl function for a pair `(D,L)` is
  `z+(z^2+1)P_i(L-z)^{-1}P_i` and has zero linear Nevanlinna term.
- Livsic theory gives `Theta=(m-i)/(m+i)`.
- Clark theory identifies boundary atoms with inverse angular derivatives.

Belyi--Makarov--Tsekanovskii, *Conservative L-systems and the Livsic function*
(arXiv:1406.2399), records the exact scalar Cayley relation and Donoghue representation.  Gesztesy
et al., *Donoghue m-functions for singular Sturm--Liouville operators* (arXiv:2107.09832), records
the operator formula `zI+(z^2+1)P_i(L-zI)^{-1}P_i`.

Suzuki's June 2026 paper constructs `(1)`--`(4)` and proves real zeros for every angle, but does not
form `(5)`, identify `(6)`--`(11)`, prove zero linear mass, compute the atomic weights, or extract
the strict canonical interlacing.  Searches through 2026-07-21 found no Suzuki follow-up doing so.
The candidate novelty is this exact restricted-Weil source identification and its frontier
consequences, not Donoghue/Clark theory itself.  Specialist priority review remains required.

## 9. Lean target

Do not formalize generic spectral or Clark theory without the source operator.  Formalize only the
dependency-closed analytic connectors used by this theorem:

1. the exact two-angle identity `m=-i W_1/W_{-1}`;
2. oddness of the normalized Herglotz quotient from `SuzukiParityPair`;
3. pole-residue/phase-weight transfer at a simple `Theta=1` point;
4. the exact Donoghue kernel decomposition `(8)` and atomic scaling `(1+x^2)p_x`.

These connectors are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/SuzukiDonoghueSpectralMeasure.lean` as

```text
suzukiHerglotz_eq_twoAngleDonoghueQuotient
suzukiHerglotz_neg_of_parity
suzukiDonoghueKernel_eq_mobius
suzukiDonoghueKernel_eq_nevanlinna
suzukiUpperCayleyInv_residue_at_one
suzukiUpperCayleyInv_phase_residue_at_one
```

The actual operator equality `(7)` remains a paper theorem in general, but **its pure-point case is
formal** — and the card itself proves the measure is pure point (section 3).  For an operator with an
orthonormal eigenbasis the resolvent pairing is the Cauchy combination of spectral masses
(`inner_spectralResolvent`), and then in `SuzukiDonoghueInterlacing.lean`:

- `sum_spectralMass_eq_normSq`: **Parseval** — the squared eigenbasis coefficients of a unit vector
  total one, which is `(12)`'s third clause.
- `donoghueResolvent_eq_kernelSum`: **`(7)`'s first two equalities** — `z + (z^2+1)(resolvent
  pairing)` is the sum of Donoghue kernels against the masses.  The affine term `z` is absorbed
  precisely because the masses are a probability, so the normalization of the deficiency vector is
  what makes the kernel's constant come out right.

Composed with `donoghuePurePoint_eq_cauchySum` this gives all three equalities of `(7)` for a
pure-point spectral measure.  What is still missing is the identification of Suzuki's concrete `L`
with an operator carrying such an eigenbasis.

**`(14)`, the canonical interlacing, is formal** — it was not among the connectors above, and its
conclusion is carried by a "Therefore" in section 4.  In
`formal/GaloisForLFunctions/RHTower/SuzukiDonoghueInterlacing.lean`:

- `nevanlinnaWeight`, `nevanlinnaWeight_pos`: the atom weight `(1+t²)p`, positive when the mass is.
- `donoghuePurePoint_eq_cauchySum`: **the pure-point Donoghue transform is a positive-weight Cauchy
  combination** — termwise the kernel splits as the Nevanlinna kernel minus the node, and the
  subtracted part sums to zero exactly when the first moment vanishes, which the evenness of `nu`
  supplies.
- `strictMonoOn_donoghuePurePoint`: strictly increasing off the atoms, needing no ordering.
- `existsUnique_zero_in_atomGap`: **exactly one zero between consecutive atoms**, hence the poles
  (even-extension spectrum) and the zeros (odd) strictly interlace.
- `cauchySum_nevanlinna_ne_zero_of_im_ne_zero`: and there are no nonreal zeros, so the interlacing
  accounts for the whole zero set.

Once the transform is recognized as a positive-weight Cauchy combination the interlacing needs no
new analysis: it is the same strict-monotonicity-plus-blow-up argument already proved for the
anti-Pick card, applied to the Nevanlinna weights.

The parity clause of `(9)` and the displayed derivative of `(14)` are formal in the same module:

- `sum_eq_zero_of_symmetric_odd`: a reflection-odd family sums to zero, the single parity argument
  behind both clauses below.
- `sum_moment_eq_zero_of_symmetric`: **parity kills the first moment** — pairing each atom with its
  reflection makes `sum t p` its own negative.  So the vanishing linear part is not an extra
  hypothesis but exactly the evenness the card derives from oddness of `m`.
- `cauchySum_eq_zero_at_center`: **the centre lies in the odd spectrum** — a reflection-symmetric
  transform vanishes at the origin, which is section 4's "parity puts the forced central eigenvalue
  `0` in the odd spectrum".
- `donoghuePurePoint_eq_cauchySum_of_symmetric`: hence the Cauchy form holds from parity alone.
- `hasDerivAt_donoghuePurePoint`, `deriv_donoghuePurePoint_pos`: `(14)`'s displayed derivative
  `sum (1+t^2) p/(t-x)^2` and its positivity.

Section 4's identification of the two divisors is algebra on the two-angle quotient:

- `suzukiHerglotz_eq_zero_iff`: **the carrier vanishes exactly where the odd pencil `W_1` does.**
- `pencil_common_zero_iff`: **the two pencils share a zero exactly where `A` and `E` do.**  So the
  primeness of the source operator — which section 3 uses to exclude common zeros of `A` and `E` — is
  precisely what keeps the pole and zero divisors disjoint.  The card states these as consequences of
  `(5)`; they are, and the derivation is two lines of algebra once the quotient form is available.

## Gates

- [x] exact Suzuki source pair and reference extension identified
- [x] Donoghue resolvent identity derived
- [x] zero linear coefficient and even measure derived
- [x] atomic projection weights derived
- [x] residue and phase-speed law derived
- [x] canonical strict interlacing derived
- [x] free-clock specialization checked symbolically
- [x] RH circularity and topology attacks recorded
- [x] current primary-literature collision audit
- [x] Lean analytic connectors
- [ ] specialist novelty review
- [ ] cofinal tightness/intrinsic shift selector
- [ ] persistent infinite-atom non-clock theorem
- [ ] Xi divisor identification
- [ ] RH

## Log

- 2026-07-21 — created after the generic Clark compactification route was rejected as bridge-only;
  exact normalized defect spectral probability and atomic source weights derived.
- 2026-07-21 — hostile proof and primary-literature audit closed; dependency-closed two-angle,
  parity, Donoghue-kernel, and residue/phase connectors formalized in Lean.
- 2026-08-01 — `(14)` formalized (`SuzukiDonoghueInterlacing.lean`).  The card's Lean-target list
  named six connectors and all six do exist in the repo, but `(14)` — the canonical interlacing — was
  not among them, and its conclusion sits behind a "Therefore these two canonical Suzuki extension
  spectra strictly interlace", the pattern that hides claims from a connector-by-connector audit.
  The proof needs no new analysis: `donoghuePurePoint_eq_cauchySum` recognizes the pure-point
  transform as a positive-weight Cauchy combination (the subtracted linear part vanishes precisely by
  evenness of `nu`), after which the strict monotonicity and one-zero-per-gap theorems already proved
  for `suzuki-shift-spectral-monotone-likelihood-transfer` apply verbatim to the Nevanlinna weights.
  Five new declarations, targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(14)`'s derivative formula and the parity clause of `(9)` formalized.
  `sum_moment_eq_zero_of_symmetric` shows the vanishing first moment is not an extra hypothesis of
  `donoghuePurePoint_eq_cauchySum` but precisely the evenness the card derives from oddness of `m`:
  pairing each atom with its reflection makes the moment its own negative, and the fixed-point case
  is handled by the node being zero there.  With it the Cauchy form holds from parity alone
  (`donoghuePurePoint_eq_cauchySum_of_symmetric`), and `(14)`'s displayed derivative and positivity
  follow from the corresponding Cauchy-combination theorems.  Four new declarations, targeted build
  green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — section 4's parity clause formalized (`cauchySum_eq_zero_at_center`): a
  reflection-symmetric pure-point transform vanishes at the origin, which is the card's "parity puts
  the forced central eigenvalue `0` in the odd spectrum" — a claim carried by a sentence rather than
  a displayed equation, and so invisible to an audit of the numbered list alone.  It and the
  first-moment vanishing are the same fact, so both now go through one lemma
  (`sum_eq_zero_of_symmetric_odd`): a reflection-odd family sums to zero, with the fixed-point case
  discharged by oddness forcing the summand to vanish there.  Three declarations (one new, two
  refactored through it), targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — section 4's divisor identification formalized: `suzukiHerglotz_eq_zero_iff` (the
  carrier vanishes exactly where the odd pencil does) and `pencil_common_zero_iff` (the two pencils
  share a zero exactly where `A` and `E` do).  The second makes precise what primeness of the source
  operator buys: it excludes common zeros of `A` and `E`, and that is exactly the condition keeping
  the pole and zero divisors disjoint, so the interlacing statement has no hidden coincidence case.
  Two new declarations, targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — first foundational piece of the source operator built:
  `formal/GaloisForLFunctions/HTGeometry/PositiveOperatorInner.lean`, the inner product `<u,v>_T =
  <Tu,v>` induced by a positive symmetric operator.  Symmetry, bilinearity, and Cauchy–Schwarz from
  the discriminant of the nonnegative quadratic along a line — no completeness or definiteness used,
  so it applies to `T = A_a - lambda I` before `H_T` is completed.  The key item for this card is
  `tInner_eq_inner_of_apply`: **solving `T v = e` removes the operator from the pairing**, so the
  `T`-pairings `<v_z, v_+>_T` of `(3)` are plain pairings of the right-hand sides `e^{-izx}` — which
  is the mechanism of the boundary-form calculation the card cites, isolated from the deficiency
  theory.  Five new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(7)`'s pure-point case formalized.  The card proves in section 3 that the measure is
  pure point, and for an eigenbasis operator the resolvent pairing is already the Cauchy combination
  of spectral masses (`inner_spectralResolvent`, built for the monotone-likelihood card).  Adding
  `sum_spectralMass_eq_normSq` (Parseval, giving `(12)`'s `sum p = 1`) and
  `donoghueResolvent_eq_kernelSum` closes `(7)`'s first two equalities, and composing with
  `donoghuePurePoint_eq_cauchySum` gives the third.  Worth recording *why* the affine term works out:
  `z` is absorbed exactly because the masses total one, so the normalization of the deficiency vector
  is not cosmetic — it is what makes the Donoghue kernel's constant correct.  Two new declarations,
  targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(10)`/`(11)`'s normalization content formalized in `PositiveOperatorInner.lean`.
  `inner_normalize_sq` gives the spectral mass of two normalized vectors as the squared pairing over
  the two squared norms — which is `(10)`'s `p_x = |<v_+,phi_x>|^2/N = |F(-x)|^2/(N ||v_x||^2)` once
  the boundary-form identity `tInner_eq_inner_of_apply` supplies `<v_x,v_+>_T = F(-x)`, and `(11)` is
  then `nevanlinnaWeight` by definition.  The identity needs no nonvanishing hypothesis: in the
  degenerate case both sides are zero, since Lean's inverse of the zero norm is zero and the quotient
  has zero numerator.  `tInner_smul_smul` and `tInner_normalize_sq` give the same for the induced
  form.  Three new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(15)`'s cancellation formalized (`HyperbolicModulus.lean`).  The free-clock weights
  are flat because two things meet: on a vertical line `|sinh(a - i θ)|^2 = sinh^2 a cos^2 θ +
  cosh^2 a sin^2 θ`, which at the quarter-period frequencies collapses to `cosh^2 a`; and the
  weight's `1 + x^2` is exactly `|1 - i x|^2`, the denominator it divides.  So
  `quarterPeriod_weight_const` gives `cosh^2 a` with no dependence on the mode.  This is the content
  the card cites as "fixes the factor `1+x^2` in `(11)`" — the constancy is an identity, not an
  accident of the aperture.  Four new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(15)`'s value formalized: `integral_exp_two_mul` (`N = sinh 2a`),
  `integral_one_symm` (eigenvector norm `2a`) and `freeClockWeight_eq_coth`
  (`4 cosh^2 a/(2a sinh 2a) = coth(a)/a` by the double-angle identity).  With the constant modulus
  from the previous entry, `(15)` is now formal end to end apart from identifying the free model's
  `v_+` and `v_x` with the explicit exponentials — the same operator identification the rest of the
  card waits on.  The card calls `(15)` a symbolic specialization that fixes all signs and the factor
  `1+x^2`; that role is now discharged by proof rather than by inspection.  Three new declarations,
  targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the free model's deficiency transform formalized: `integral_exp_mul_symm` evaluates
  the symmetric exponential integral to `2 sinh(w a)/w`, and `normSq_freeDeficiencyTransform` then
  gives `(1+x^2)|F(-x)|^2 = 4 cosh^2 a` at every quarter-period frequency.  With the two normalizing
  integrals and the double-angle identity this makes `(15)`'s value `coth(a)/a` a proved computation
  rather than a stated specialization — the flatness of the free clock is now established, not
  assumed, which is what section 6 needs if deviation from flatness is to serve as the non-clock
  observable.  Two new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
