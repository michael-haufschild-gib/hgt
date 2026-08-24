# C5 finite-prime Jensen kernel and critical-line logarithm obstruction

- **ID:** `c5-jensen-finite-prime-kernel-survivor`
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-GO POSITIVE SURVIVOR, `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** retired route `c5-jensen-prime-kernel.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/C5JensenPrimeKernelClosure.lean`
- **Statement:** Actual polynomial--Gamma jets give exact finite single-prime Jensen kernels and
  simple-root velocities. No global pointwise critical-line logarithm of zeta exists, and critical
  prime amplitudes have neither absolute nor square summability.

## Exact theorem

Let

```text
A(z) = [s(s-1)/2] Gamma_R(s),   s=1/2+iz,
a_p  = p^(-1/2),
A_j(t) = d^j A/dz^j evaluated at z=t.
```

For degree `d`, define the finite prime kernel

```text
K_(d,t,p)(X)
 = a_p sum_(i=1)^d (-i log p)^i B_i(X;t),

B_i(X;t)
 = sum_(j=i)^d binom(d,j) binom(j,i) A_(j-i)(t) X^j / j!.
```

Then:

1. `A(t) != 0` and
   `Xi(t) = A(t) zeta(1/2+it)` for every real `t`.
2. There is no function `P : R -> C` satisfying
   `exp(P(t)) = zeta(1/2+it)` for every real `t`.
3. `sum_p a_p` and `sum_p a_p^2` are not summable.
4. For every simple root `r0` of the actual archimedean Jensen section, the one-prime linear
   perturbation has a local analytic root branch `r(epsilon)` with

```text
r(0)=r0,
r'(0) = -K_(d,t,p)(r0) / J_arch'(r0).
```

Simplicity is an internal universally quantified domain condition, not a premise of the closed
capstone theorem.

## Proof

The factorization follows from the completed-zeta identity away from `0` and `1`; on the critical
line both points are excluded by real part `1/2`. The polynomial factors and `Gamma_R` are nonzero
there. Hardy's theorem gives a positive real `t` with `Xi(t)=0`, hence
`zeta(1/2+it)=0`. Since a complex exponential never vanishes, a global pointwise `P` is impossible.

Euler's divergence of the reciprocal-prime sum gives nonsummability at exponents `1/2` and `1`.
The coefficient identities reduce `Lambda(p)/log(p) p^(-1/2)` to `p^(-1/2)` and the prime-power
coefficient to `p^(-k/2)/k`. Finite Leibniz collection gives displayed polynomial kernel. Complex
implicit-function theorem at a simple polynomial root gives exact analytic branch and velocity.

## No-go boundary

The retired card treated distributional boundary values of `log zeta` as pointwise derivatives at
Jensen base points. Distributional continuation does not provide that operation. Finite-frequency
kernel remains exact; infinite critical-line displacement requires a separately specified and
proved distribution-to-jet regularization.

## Lean certificate

Premise-free endpoint:

```text
GaloisForLFunctions.RHTower.c5JensenPrimeKernelClosure_capstone
```

Supporting endpoints include:

```text
XiC_eq_c5XiArchimedeanFactor_mul_riemannZeta
not_exists_c5GlobalCriticalLineLogZeta
not_summable_c5CriticalPrimeAmplitude
not_summable_sq_c5CriticalPrimeAmplitude
c5JensenFirstOrderSection_actualPrime
exists_c5ActualPrimeJensenRootBranch
```

Targeted checks passed:

```text
lake env lean GaloisForLFunctions/RHTower/C5JensenPrimeKernelClosure.lean
lake build GaloisForLFunctions.RHTower.C5JensenPrimeKernelClosure
```

Endpoint axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired
into `formal/GaloisForLFunctions/RHTower.lean`; umbrella was not built.

## Gates

- [x] exact finite arithmetic coefficient identities
- [x] exact finite Leibniz/log-frequency kernel
- [x] analytic simple-root perturbation
- [x] actual polynomial--Gamma jet specialization
- [x] unconditional critical-line logarithm no-go
- [x] absolute and square-summability obstructions
- [x] premise-free Lean capstone
- [x] targeted source check, targeted module build, axiom audit, umbrella wiring

## Log

- 2026-08-24 — extracted from falsified infinite pointwise route, formalized, audited, and moved to
  stage 3 as strongest positive survivor.
