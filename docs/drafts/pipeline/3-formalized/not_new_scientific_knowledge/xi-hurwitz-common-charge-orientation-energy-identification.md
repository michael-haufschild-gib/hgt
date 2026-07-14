# Xi Hurwitz common charge is the orientation-energy zero locus

- **ID:** xi-hurwitz-common-charge-orientation-energy-identification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PROVED BRIDGE] [NOT AN RH PROOF] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** cross-interface synthesis of the first-prime seam, Hurwitz orientation energy, and regular-Cauchy source closure

## Statement

For an Xi divisor point `rho`, let

```text
C_2(rho) = log(2) [2^(-conj rho) - 2^(-(1-rho))]
```

be the common limit of the normalized Hurwitz anchor seam and the translated all-prime flux seam.
Lean proves:

```text
C_2(1-conj rho) = -C_2(rho),

C_2(rho)=0
  <-> xiHurwitzOrientationDefect(rho)=0,

(forall rho in Z_Xi, C_2(rho)=0)
  <-> E_Xi=0,

XiHurwitzAnchorPrimeTwoSeamsVanish
  <-> E_Xi=0.
```

Therefore the common-charge assertion is not a new hypothesis beyond the scalar orientation
energy.  The existing source-closure theorem gives the exact chain

```text
Weil nonnegativity on the algebraic regular-Cauchy source core
  -> E_Xi=0
  -> every common first-prime seam vanishes
  -> RH.
```

The first implication remains open.  Closure membership has already been discharged; no separate
common-charge producer is needed once source-core positivity is proved.

## Why reflection alone does not prove vanishing

The charge is reflection-odd, but the functional equation supplies both `C_2(rho)` and
`-C_2(rho)` without choosing an orientation.  A pointed-cone argument would work only after a
source theorem placed both reflected charges in one pointed chamber.  Stated merely on Xi-zero
charges, that chamber condition is itself equivalent to `E_Xi=0`; it is not an independent proof.

The local corpus rules out the obvious substitutes:

- first-prime transport is an exact coboundary, so every forward--reverse loop is flat off the
  line as well as on it;
- finite Euler mirror defects can reach both signs;
- scalar reflected local-factor modulus balance has exact off-line neutral phases;
- bounded-support one-point Weil tests cannot isolate an individual off-line orbit from the
  unknown critical-line tail;
- the archimedean theta functional does not factor through prime-log samples, even nonlinearly.

## Literature gate

No unconditional literature theorem found in the audit supplies the missing pointed source
chamber.

- [Connes--Consani](https://arxiv.org/abs/2008.10974) prove that an individual
  nonarchimedean local-factor ratio is not quasi-inner;
  quasi-innerness appears only after archimedean compensation and finite semilocal multiplication.
  It therefore does not orient the isolated `p=2` charge.
- [Suzuki's meromorphic-inner/canonical-system theorem](https://arxiv.org/abs/1204.1827) is
  unconditional only in a shifted zero-free
  range.  Extending the construction down to every positive shift is itself the RH boundary.
- [Archimedean Weil positivity](https://arxiv.org/abs/2006.13771) is not the required global
  semilocal positivity; the latter is the RH-bearing step.
- [Recent Gaussian--Perron local-profile work](https://arxiv.org/abs/2607.04316) assumes RH for
  its critical-line selected-zero
  asymptotic and retains explicit damping and contour hypotheses, so it does not force this charge
  to vanish.

## Lean surface

Module:

```text
GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoOrientationEnergy
```

Declarations:

```text
orbitwiseFirstPrimeSeamCharge_lineReflect
orbitwiseFirstPrimeSeamCharge_eq_zero_iff_orientationDefect_zero
XiFirstPrimeSeamChargesVanish
xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero
xiHurwitzAnchorPrimeTwoSeamsVanish_iff_firstPrimeSeamChargesVanish
xiHurwitzAnchorPrimeTwoSeamsVanish_iff_orientationEnergy_zero
xiHurwitzAnchorPrimeTwoSeamsVanish_of_cauchyCore_nonnegative
```

## Gates

- [x] 0 -> 1: exact common-charge/orientation-energy splice identified
- [x] 1 -> 2: reflection, pointwise zero-locus, global energy, and source-core implications proved
- [x] 2 -> 3: formalized in Lean
- [ ] 3 -> 4: not a publication target by itself

## Verification

- [x] exact file typecheck
- [x] no forbidden declarations
- [x] formal lint
- [x] generated index refresh

## Dyadic finite-value replacement for zero charge

The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/xi-rational-hurwitz-dyadic-refinement-square-law.md`
replaces the direct assertion `C_2(rho)=0` by a relation between two finite absolutely convergent
Hurwitz packets.  For the normalized reflection energies `H_2,H_4`,

```text
H_4(rho) - 4*H_2(rho) = 4*H_2(rho)^2.
```

Consequently `H_4=4*H_2` is equivalent pointwise to vanishing of the common first-prime seam.
Globally,

```text
linear modulus-2-to-4 finite-Hurwitz refinement
  -> all common first-prime charges vanish
  -> xiHurwitzOrientationEnergy=0
  -> RH.
```

The positive square identity is unconditional; proving the linear refinement from a source Ward,
finite-coefficient, or graded-trace constraint remains open.
