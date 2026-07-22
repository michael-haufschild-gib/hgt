# Boundary zeta zeros force divergence of Möbius Gamma--Hankel energy

- **ID:** `mobius-gamma-hankel-boundary-zero-energy-divergence`
- **Stage:** 3-formalized
- **Type:** THEOREM / SHARP BOUNDARY LAW
- **Scientific status:** `[PROVED HERE] [NEW TO CORPUS] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Lean cores:**
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceGammaHankelBoundaryPole.lean` and
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceMellinPlancherelBridge.lean`
- **Parents:** Möbius--Laplace Mellin wall; Gamma--Hankel localization wall

## Statement

Put

```text
Phi(x) = sum_(n>=1) mu(n) exp(-n x),
E_sigma = integral_0^infinity x^(2 sigma-1) |Phi(x)|^2 dx.
```

### Boundary-zero theorem

Let `rho=beta+i gamma` be a nontrivial zero of `zeta`, with `0<beta<1`. Then

```text
E_beta = infinity.                                               (BZ1)
```

More strongly, if `E_sigma<infinity` for some `sigma>0`, then zeta has no zero in the closed
half-plane

```text
Re(s) >= sigma.                                                  (BZ2)
```

The existing Mellin-continuation argument gave only the open half-plane `Re(s)>sigma` directly.
The new content is exclusion of zeros on the boundary line by a uniform Hardy-line norm and local
pole-energy blowup.

### Unconditional critical consequence

Hardy's theorem supplies infinitely many zeros on `Re(s)=1/2`. Therefore

```text
integral_0^infinity |Phi(x)|^2 dx = infinity.                    (BZ3)
```

Indeed, `E_sigma=infinity` for every `0<sigma<=1/2`. If RH holds, the previously proved converse
energy estimate gives `E_sigma<infinity` for every `sigma>1/2`. Thus under RH the energy abscissa is
exactly `1/2`, and the endpoint is not attained.

## Proof

Assume `E_sigma<infinity`. Define, initially for `Re(s)>sigma`,

```text
G(s) = integral_0^infinity Phi(x) x^(s-1) dx.                    (BZ4)
```

For every compact substrip strictly right of `sigma`, Cauchy--Schwarz on `(0,1)` gives a common
integrable majorant. The already formalized exponential tail of `Phi` handles `(1,infinity)`.
Hence `G` is analytic on `Re(s)>sigma`.

The denominator-free classical identity is

```text
G(s) zetaResidueUnit(s) = Gamma(s) (s-1),                       (BZ5)

zetaResidueUnit(s) = (s-1) zeta(s).
```

It holds first on `Re(s)>1` and then on the connected half-plane `Re(s)>sigma` by identity
continuation. Since `Gamma` has no zeros, `(BZ5)` excludes zeta zeros in the open half-plane.

It remains to exclude a boundary zero. Let

```text
rho = sigma+i gamma,
zeta(s) = (s-rho)^m u(s),   m>=1,   u(rho) != 0.                (BZ6)
```

For points to the right of the boundary, `(BZ5)` gives

```text
G(s) = H(s)/(s-rho)^m,                                         (BZ7)
```

where `H` is analytic and nonzero at `rho`. Choose `delta,c>0` such that `|H(s)|>=c` whenever
`|s-rho|<delta`.

Mellin--Plancherel on the line `Re(s)=sigma+r` gives

```text
integral_R |G(sigma+r+i t)|^2 dt
  = 2 pi integral_0^infinity x^(2(sigma+r)-1) |Phi(x)|^2 dx.    (BZ8)
```

For `0<r<=r0`, the right side is uniformly bounded. On `(0,1)`, `x^(2r)<=1`, so this part is at
most `2 pi E_sigma`. On `(1,infinity)`, the exponential tail of `Phi` dominates the extra factor
`x^(2r)` uniformly for `r<=r0`.

For `0<r<delta/sqrt(2)` and `|t-gamma|<=r`, `(BZ7)` instead gives

```text
|G(sigma+r+i t)|^2
  >= c^2 / (r^2+(t-gamma)^2)^m
  >= c^2 / (2^m r^(2m)).                                      (BZ9)
```

Integration over `[gamma-r,gamma+r]` yields

```text
integral_R |G(sigma+r+i t)|^2 dt
  >= 2^(1-m) c^2 r^(1-2m),                                    (BZ10)
```

which tends to infinity because `m>=1`. This contradicts the uniform upper bound from `(BZ8)`.
Therefore no boundary zero exists, proving `(BZ2)`. Taking `sigma=beta` proves `(BZ1)`.

For `(BZ3)`, apply `(BZ1)` to any zero supplied by Hardy's theorem. For `0<sigma<1/2`, finiteness
of `E_sigma` would already make `G` analytic across the critical-line zero, so the same conclusion
also follows from the open-half-plane part of the argument.

## Formal certificate

The local pole law is formalized without any zeta-zero or RH assumption. For the principal part at
distance `r_n=(n+1)^(-1)`, Lean proves

```text
integral_R |c/(r_n+i(t-gamma))|^2 dt
  = pi |c|^2 (n+1),                                           (BZ11)
```

then proves convergence of these energies to `+infinity`, crossing of every proposed ceiling, and
nonexistence of a uniform bound.

Verified declarations:

```text
boundaryPoleApproachProfile
integral_norm_sq_boundaryPoleApproachProfile
tendsto_integral_norm_sq_boundaryPoleApproachProfile
exists_integral_norm_sq_boundaryPoleApproachProfile_gt
not_exists_uniform_boundaryPoleApproachEnergy_bound
```

The exact infinite-aperture Mellin--Plancherel instantiation `(BZ8)` is formalized. Lean derives
its `L1 ∩ L2` premises on every right-shifted line from one finite base energy `E_sigma`, proves a
uniform source ceiling for `0<r<=r0`, and transfers it to a uniform full Mellin-line ceiling.
The actual connector is now formalized as well: analytic order factors a boundary zero, continuity
of `Gamma/p` supplies a nonzero window floor, and an interval-energy lemma forces `2*c^2/r`
growth. The resulting closed-half-plane theorem is

```text
riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed.
```

Finite Gamma--Hankel localization and exact principal-pole integral remain compiled dependencies.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceGammaHankelBoundaryPole.lean  PASS
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceMellinPlancherelBridge.lean   PASS
```

The three principal theorem endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile audit

1. **No boundary analyticity is assumed.** `G` is analytic only for `Re(s)>sigma`. The contradiction
   uses norms on interior lines approaching the boundary.
2. **No point evaluation of an `L2` boundary value is used.** The local meromorphic factorization is
   evaluated at `r>0`; the blowup is integrated over an interval of width `2r`.
3. **A holomorphic remainder cannot cancel the pole.** It is absorbed into the analytic numerator
   `H`, which is bounded below near `rho` because `H(rho)!=0`.
4. **Multiplicity strengthens the obstruction.** A zero of order `m` gives growth
   `r^(1-2m)`; the weakest case `m=1` already diverges like `1/r`.
5. **The tail bound is uniform.** On `x>=1`, fix `r0`; polynomial weight
   `x^(2r0)` is dominated by the proved exponential decay of `Phi`.
6. **No simple-zero hypothesis enters.** `(BZ6)` uses the finite positive analytic order `m`.
7. **This does not prove RH.** It proves a necessary divergence law at every zeta-zero abscissa.
   The missing RH-producing estimate remains finiteness of `E_sigma` for all `sigma>1/2`, or the
   equivalent Möbius--Laplace continuation source.

## Corpus and literature boundary

Corpus search found the open-half-plane Gamma--Hankel RH criterion and a general exact Cauchy-pole
energy profile, but not their boundary-zero synthesis or unconditional critical Möbius--Laplace
energy divergence.

Targeted literature search covered discrete Möbius Laplace transforms, reciprocal-zeta Hardy-space
criteria, Mellin--Plancherel zeta formulas, and boundary-pole `H2` arguments. Liflandsky's 2026
paper gives the pointwise `O(x^(-1/2))` implication and a conditional explicit zero formula, not
`(BZ1)--(BZ3)`. Lima's Müntz-type paper supplies adjacent Mellin/zeta identities, not the Möbius
energy boundary law. Hardy--Littlewood supplies the classical critical-line zero input. No exact
matching statement was located. This is an audit result, not a priority claim; status remains
`NOVELTY UNVERIFIED`.

Primary sources:

- S. Liflandsky, [Explicit formula for the discrete Laplace transform of the Möbius function](https://arxiv.org/abs/2607.09797), 2026.
- H. Lima, [On Müntz-type formulas related to the Riemann zeta function](https://arxiv.org/abs/1705.09386), 2017.
- G. H. Hardy and J. E. Littlewood,
  [Contributions to the theory of the Riemann zeta-function and the theory of the distribution of primes](https://projecteuclid.org/journals/acta-mathematica/volume-41/issue-none/Contributions-to-the-theory-of-the-riemann-zeta-function-and/10.1007/BF02422942.pdf),
  Acta Mathematica 41 (1918).

## Gates

- [x] internal corpus audit
- [x] targeted primary-literature audit
- [x] complete paper proof of boundary-zero energy divergence
- [x] hostile cancellation and multiplicity audit
- [x] exact local pole-energy core formalized in Lean
- [x] conditional concrete infinite-aperture Möbius Mellin--Plancherel theorem formalized
- [x] base-energy-to-uniform-interior-source transport formalized
- [x] uniform infinite-aperture Mellin-line ceiling formalized
- [x] actual `Gamma/zeta` boundary-zero factorization connected to pole lower bound
- [x] closed-half-plane zero exclusion formalized
- [ ] external novelty review
