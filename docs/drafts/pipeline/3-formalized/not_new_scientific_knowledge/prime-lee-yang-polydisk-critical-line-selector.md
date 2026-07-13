# Prime Lee--Yang fields identify the centered critical line with the common unit torus

- **ID:** `prime-lee-yang-polydisk-critical-line-selector`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[FINITE CONSUMER] [POSITIVE BASELINE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeLeeYangPolydisk.lean`
- **Consumer:** `../../1-in-progress/prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`

## Theorem

In the centered coordinate `XiC(z)=xi(1/2+I z)`, assign to every prime `p` the inhomogeneous
Lee--Yang activity

```text
u_p(z)=exp(-log(p) I z).
```

Lean proves

```text
|u_p(z)|=exp(log(p) Im z),
|u_p(z)|<1  <-> Im z<0,
|u_p(z)|=1  <-> Im z=0,
|u_p(z)|>1  <-> Im z>0.
```

Consequently the centered critical line is exactly the common unit torus of every prime activity;
the two off-line half-planes are the common open polydisk and common exterior.

## Positive independent-spin baseline

For a finite set of primes `P`, define

```text
F_P(z)=product_(p in P) (1+u_p(z)).
```

Lean proves `F_P(z)=0 -> Im z=0`.  This is the zero-interaction prime-spin partition function.
It establishes that the incommensurable logarithmic prime fields already have the exact finite
Lee--Yang geometry required by RH.

The result does not approximate `XiC` and therefore is not an RH proof.  Its positive content is to
replace the artificial one-common-fugacity/Cayley model by a source-native multivariate field.  The
remaining scientific theorem is a functorial interacting ferromagnetic construction, including a
zero-free archimedean normalization, which converges locally uniformly to a zero-free factor times
`XiC`.

## Formal certificate

The module proves:

- `norm_centeredPrimeLeeYangField`;
- `norm_centeredPrimeLeeYangField_lt_one_iff`;
- `norm_centeredPrimeLeeYangField_eq_one_iff`;
- `one_lt_norm_centeredPrimeLeeYangField_iff`;
- `independentPrimeLeeYangPartition_ne_zero_of_im_lt_zero`;
- `independentPrimeLeeYangPartition_ne_zero_of_im_gt_zero`;
- `independentPrimeLeeYangPartition_zero_im`.

The exact module and the `RHTower` umbrella build.  Axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] centered prime activity defined
- [x] common polydisk/torus/exterior trichotomy proved
- [x] independent finite partition zero localization proved
- [x] exact module build
- [x] umbrella build
- [x] accepted-axiom audit
