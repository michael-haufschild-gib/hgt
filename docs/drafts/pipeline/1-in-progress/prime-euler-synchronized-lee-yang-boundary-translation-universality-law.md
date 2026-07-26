# Prime Euler synchronized Lee-Yang boundary-translation universality law

Status: **Stage 3 — formalized in Lean**

## Discovery

Whole-corpus theorem-posting closure joined:

- `PrimeEulerLeeYangAmplitudeNoGo`: each physical Euler field is the centered prime Lee-Yang field
  multiplied by its square-root amplitude `p⁻¹/²`; and
- `PrimeWordSynchronizedCluster`: every finite synchronized centered cluster has all zeros on
  `Im z = 0`.

The shared prime logarithmic character shows that the square-root amplitude is exactly one common
vertical spectral translation, uniformly over every finite support. No cluster-level physical
transport or zero classification occurs in either module or in the corpus research index.

## Universal law

For every finite prime support `P`, define

`F_P^phys(z) = ∏_{p∈P} physicalCenteredEulerLeeYangField p z`

and `Z_P^phys(z)=1+F_P^phys(z)`. Then

`F_P^phys(z) = synchronizedPrimeClusterField P (z - I/2)`

and hence

`Z_P^phys(z) = synchronizedPrimeClusterPartition P (z - I/2)`.

Consequently, if `P` is nonempty, every zero of `Z_P^phys` satisfies `Im z = 1/2`. The Euler
square-root amplitude therefore translates the full synchronized Lee-Yang zero wall rigidly from
the centered critical line to the original strip boundary; support size and prime composition do
not change the displacement.

## Dependency-closed paper proof

1. By definition,

   `physicalCenteredEulerLeeYangField p z
      = exp(-log(p)/2) · exp(-log(p)·I·z)`.

2. Since `I²=-1`,

   `-log(p)·I·(z-I/2) = -log(p)·I·z - log(p)/2`.

   Exponential additivity therefore identifies the physical field with
   `centeredPrimeLeeYangField p (z-I/2)`.
3. Taking the finite product over `P` proves field transport; adding `1` proves partition
   transport.
4. A physical zero is thus a centered synchronized-cluster zero at `z-I/2`.
5. `synchronizedPrimeClusterPartition_zero_im` gives `Im(z-I/2)=0` for nonempty `P`.
6. Complex arithmetic gives `Im z=1/2`.

No RH premise, computation, limiting argument, or new physical assumption enters.

## Formal targets

- `physicalCenteredEulerLeeYangField_eq_centered_shift`
- `physicalSynchronizedPrimeClusterField`
- `physicalSynchronizedPrimeClusterPartition`
- `physicalSynchronizedPrimeClusterField_eq_centered_shift`
- `physicalSynchronizedPrimeClusterPartition_eq_centered_shift`
- `physicalSynchronizedPrimeClusterPartition_zero_im`
- `primeEuler_synchronizedLeeYang_boundaryTranslationUniversality`

## Novelty audit

Post-proof searches covered `Lee-Yang synchronized cluster + inhomogeneous activities`,
`common amplitude scaling + zero translation`, and `Euler prime square-root activity`. Classical
Lee-Yang sources put ferromagnetic zeros on a unit circle, and modern work extends the Lee-Yang
property to broader measures. None states the arithmetic prime-indexed identity in which every
Euler factor `p⁻¹/²` combines into the same support-independent spectral shift `z ↦ z-I/2`, nor
the resulting physical cluster wall `Im z=1/2`. Representative adjacent sources:

- [Statistical Theory of Equations of State and Phase Transitions. I](https://doi.org/10.1103/PhysRev.87.404)
- [Statistical Theory of Equations of State and Phase Transitions. II](https://doi.org/10.1103/PhysRev.87.410)
- [Lee-Yang Property and Gaussian Multiplicative Chaos](https://doi.org/10.1007/s00220-019-03453-0)
- [Yang-Lee zeros of certain antiferromagnetic models](https://arxiv.org/abs/2309.14562)

No exact collision found in this scoped audit. **[NOVELTY UNVERIFIED]**

## Lean formalization

Formal source:
`formal/GaloisForLFunctions/RHTower/PrimeEulerSynchronizedLeeYangBoundaryTranslationUniversalityLaw.lean`.

Verified with:

`lake env lean GaloisForLFunctions/RHTower/PrimeEulerSynchronizedLeeYangBoundaryTranslationUniversalityLaw.lean`

Umbrella:
`formal/GaloisForLFunctions/RHTower.lean`.
