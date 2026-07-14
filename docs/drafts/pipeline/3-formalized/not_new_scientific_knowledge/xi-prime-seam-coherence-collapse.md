# Xi prime-seam coherence collapses to zero

- **ID:** `xi-prime-seam-coherence-collapse`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / TOP-DOWN SONIN INTERFACE DISCHARGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamCoherenceCollapse.lean`
- **Finite-energy continuation:**
  `formal/GaloisForLFunctions/RHTower/XiPrimeSeamPairEnergy.lean`
- **Paper parent:** `sonin-two-particle-prime-coherence`

## Statement

For a point `rho` in the open critical strip and every positive scale `x`, define the canonical
FE--Schwarz seam potential

```text
C_x(rho) = log(x) * (x^(-conj rho) - x^(-(1-rho))).
```

Lean proves unconditionally

```text
C_x(rho) -> 0 as x -> infinity.
```

Consequently, if the values `C_p(rho)` are equal at every prime, then their common value is zero.
Equivalently,

```text
all prime seam potentials at rho are coherent
  iff Re(rho)=1/2.
```

Over the complete Xi divisor, the same condition satisfies

```text
XiPrimeSeamChargesCoherent
  iff XiFirstPrimeSeamChargesVanish
  iff xiHurwitzOrientationEnergy = 0
  iff RH.
```

The implication from coherence to vanishing uses cofinal prime decay, not an assumed
archimedean normalization.

## Proof

If `0 < Re(rho) < 1`, both real decay exponents `Re(rho)` and `1-Re(rho)` are positive.  The
standard estimate

```text
log(x) * x^(-a) -> 0,  a>0,
```

together with the exact norm formula for complex powers on the positive real axis shows that both
summands in `C_x(rho)` tend to zero.  Restriction to integer scales preserves this limit.  If all
prime values equal one scalar `c`, arbitrarily large primes place the constant subsequence inside
every neighbourhood of zero, hence `c=0`.  The prime `2` member is exactly the already formalized
first-prime seam charge, whose vanishing is equivalent to `Re(rho)=1/2`.  Existing orientation
energy theorems globalize the pointwise statement over the Xi divisor.

## Top-down consequence

The stage-2 tensor-square Sonin theorem proves that a uniform finite-section Calkin bound for
difference coefficients `a_p-a_q` forces the potentials `a_p` to be constant.  Specializing to
the canonical Xi seam potentials now gives the sharper prospective chain

```text
uniform two-particle Sonin Calkin bound for the canonical differences
  -> all C_p(rho) are equal
  -> all C_p(rho) vanish                       [formalized here]
  -> C_2(rho)=0
  -> the FE--Schwarz Hurwitz pair is dependent
  -> Re(rho)=1/2.
```

Applied to every Xi divisor point, this proves RH.  The previously listed extra assertion that an
archimedean normalization must kill the common charge is therefore removed.

## Exact remaining problem

Prove, from the actual prime--Gamma/Sonin source and without zero-location input, that for every Xi
divisor point the canonical coefficients

```text
C_p(rho)-C_q(rho)
```

produce uniformly bounded finite tensor-square Sonin sections modulo compact operators.  The
arithmetic middle is now formalized separately: uniform boundedness of the finite
reciprocal-prime pair energies is equivalent to coherence, and its Xi-divisor specialization is
equivalent to RH.  What remains unformalized from the paper parent is specifically the actual
tensor-square Sonin Calkin lower estimate, not the reciprocal-prime passage.

The existing all-prime Hilbert--Schmidt theorems do not discharge this input.  They assemble the
principal-subtracted prime-power residual beginning at exponent `p^(k+2)`.  The divergent linear
prime shell is explicitly deleted there, whereas the two-particle theorem detects precisely the
Calkin class of that principal Euler shell.  Thus residual Hilbert--Schmidt summability controls a
compact correction, not the required principal tensor-square family.

## Literature boundary

Connes--Moscovici place the relevant prolate eigenfunctions in Sonin space in
[Prolate spheroidal operator and Zeta](https://arxiv.org/abs/2112.05500), and
Connes--Consani--Moscovici construct the semilocal Sonin/prolate framework in
[Zeta zeros and prolate wave operators](https://arxiv.org/abs/2310.18423).
Larsen--Li give the general automorphic-dilation parent for semigroup crossed products in
[Dilations of semigroup crossed products as crossed products of dilations](https://arxiv.org/abs/1009.5842).
A targeted search of these primary-source neighbourhoods and tensor/essential-norm literature did
not locate the actual-Sonin tensor-square coefficient lower bound, the reciprocal-prime coherence
consequence, or the present canonical-seam specialization.  This is not treated as a novelty
certificate: the cofinal-decay discharge itself is elementary and is classified as a bridge.

## Principal declarations

- `orbitwiseScaleSeamCharge`
- `tendsto_orbitwiseScaleSeamCharge`
- `tendsto_orbitwiseNatPrimeSeamCharge`
- `common_eq_zero_of_primeSeamCharge_eq`
- `orbitwisePrimeSeamChargesCoherent_iff_re_eq_half`
- `xiPrimeSeamChargesCoherent_iff_firstPrimeSeamChargesVanish`
- `xiPrimeSeamChargesCoherent_iff_orientationEnergy_zero`
- `xiPrimeSeamChargesCoherent_iff_riemannHypothesis`
- `riemannHypothesis_of_xiPrimeSeamChargesCoherent`

## Gates

- [x] arbitrary-scale seam defined
- [x] open-strip cofinal decay formalized
- [x] prime coherence shown to force zero common value
- [x] global orientation-energy and RH interfaces formalized
- [ ] stage-2 tensor-square Sonin lower bound formalized
- [ ] source-pure uniform bound for the canonical pair differences

## Sparse one-ended refinement

The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/xi-prime-seam-one-ended-cofinal-edge-collapse.md`
strictly weakens the coherence hypothesis needed at this endpoint.  On any fixed preconnected
one-ended graph whose vertices are the primes, it is enough that the canonical seam charge differ
across only finitely many edges.  The charge then has finite range, the formal finite-valued
one-ended reconstruction applies to that range, and the cofinal decay formalized here kills the
eventual common value.  Thus the complete-graph condition can be replaced on paper by

```text
finite edge variation on one cofinal one-ended prime skeleton
  -> eventual seam coherence
  -> eventual seam vanishing
  -> RH.
```

In operator form, it is enough to prove compactness of the canonical two-prime coboundary corner on
all but finitely many edges of that skeleton.  On the increasing-prime ray these are only adjacent
prime pairs.  Formalizing the arbitrary-label finite-range reduction is the remaining graph-level
step; the cofinal-decay and RH endpoint are already supplied by this card.
