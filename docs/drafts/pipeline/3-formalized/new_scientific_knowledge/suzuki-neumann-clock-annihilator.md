# Exact annihilation of Suzuki's finite-Neumann boundary clock

- **ID:** `suzuki-neumann-clock-annihilator`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-BOUNDARY ELIMINATION / FRONTIER REDUCTION
- **Scientific status:** `[FORMALIZED] [FULLY PROVEN ON PAPER] [SOURCE-SPECIFIC] [NOVELTY NOT EXTERNALLY AUDITED] [NOT AN RH PROOF]`
- **Parent:** `suzuki-shifted-xi-target-flat-pencil`
- **Corpus frontier addressed:** finite-Neumann-boundary control in `(S23.9)` of
  `docs/handover/sota-suzuki.md`
- **Lean:** `GaloisForLFunctions.RHTower.SuzukiExteriorPoleTomography`

## Actual corpus frontier

Corpus already supplies:

```text
finite-aperture all-real characteristic circle
  -> anchored Schur normal family
  -> free and ground erasing-boundary classifications
  -> exact Clark probability and compactified phase holography
  -> finite-shift flat holonomy
  -> complete shifted Xi target pencil.
```

What it still cannot produce is:

```text
intrinsic non-erasing cofinal schedule
  + common-gauge parity-pair normality with no escaped linear mass
  + source identification of a cluster pair with (z^2 XiC,D_eta).
```

The handover listed finite-Neumann-boundary control as a separate analytic estimate inside the last
item. The theorem below removes that separate estimate: boundary flux is an exactly annihilable
rank-two differential module.

## Scientific-method branch decision

### C1. Boundary decay `[FALSIFIED AS A NECESSARY STRATEGY]`

One must estimate the endpoint term and prove it tends to zero.

False as a structural necessity. Endpoint coefficients may grow arbitrarily; the complete clock
containing them can be killed exactly.

### C2. Distinguished-phase cancellation `[INSUFFICIENT]`

Suzuki's phase `q=-1` cancels known interior plateau forcing, so endpoint flux also vanishes.

False in this strength. Plateau cancellation leaves two independent endpoint coefficients. Phase
selection does not kill both.

### C3. Polynomial clock annihilator `[PROVED]`

Every endpoint flux belongs to a two-dimensional clock module that is the exact kernel of one
polynomial second-order operator. This survivor is proved below.

## 1. Exact Neumann boundary clock

Use Fourier convention

```text
F(z)=int_(-a)^a f(x)e^(izx)dx,
U(z)=int_(-a)^a (-f''(x))e^(izx)dx,
f'(a)=f'(-a)=0.
```

Two integrations by parts give

```text
U(z)-z^2F(z)=iz[f(a)e^(iaz)-f(-a)e^(-iaz)].             (1)
```

Euler's identity rewrites the right side as

```text
C_(a,A,B)(z)=z[A cos(az)+B sin(az)],                    (2)
A=i(f(a)-f(-a)),
B=-(f(a)+f(-a)).                                        (3)
```

No zero-mean condition, explicit Neumann kernel, or bound on `f(+-a)` is used.

## 2. Exact annihilator

Define

```text
L_a H(z)=z^2H''(z)-2zH'(z)+(2+a^2z^2)H(z).             (4)
```

Then

```text
L_a C_(a,A,B)=0                                        (5)
```

for every complex `A,B` and every aperture `a`.

### Proof

Put

```text
h(z)=A cos(az)+B sin(az).
```

Then `h''=-a^2h`, while `C=zh` gives

```text
C'=h+zh',
C''=2h'+zh''.
```

Substitution into `(4)` yields

```text
L_a C
 =z^2(2h'+zh'')-2z(h+zh')+(2+a^2z^2)zh
 =z^3(h''+a^2h)
 =0.
```

There is no division by `z`; `(4)` is entire at the origin.

Combining `(1)--(5)` gives the exact source-side elimination law

```text
L_a(U-z^2F)=0.                                         (6)
```

Equivalently, by linearity,

```text
L_aU=L_a(z^2F).                                        (7)
```

This holds before any aperture limit and regardless of endpoint growth.

## 3. Boundary-free output and cofinal limit

Direct differentiation gives

```text
L_a(z^2F)
 =z^4F''+2z^3F'+a^2z^4F
 =a^2z^2 [z^2F+a^(-2)(2zF'+z^2F'')].                  (8)
```

Define the corrected inverse symbol

```text
Q_aF(z)=z^2F(z)+a^(-2)[2zF'(z)+z^2F''(z)].             (9)
```

Suppose `a_n -> infinity` and an entire family `F_n` converges locally uniformly to `F`. The
Weierstrass derivative theorem gives locally uniform convergence of `F_n'` and `F_n''`. On every
compact set those two derivative families are eventually bounded, while `a_n^(-2)->0`. Hence

```text
Q_(a_n)F_n -> z^2F                                     (10)
```

locally uniformly. Therefore exact annihilation changes no boundary-free cluster target once the
source pair is compact-open normal.

This is not an endpoint decay estimate: coefficients `(3)` never appear in `(8)--(10)`.

## 4. Frontier consequence

The previous open core was

```text
intrinsic non-erasing schedule
  -> common-gauge pair normality and zero linear mass
  -> finite-Neumann endpoint estimates
  -> identify (z^2XiC,D_eta).
```

The corrected open core is

```text
intrinsic non-erasing schedule
  -> apply L_a to the ungauged source identity
  -> common-gauge normality of the annihilated parity pair and zero linear mass
  -> identify (z^2XiC,D_eta).                            (11)
```

Finite-Neumann boundary control is no longer an independent asymptotic premise. Remaining hard
producer is common-gauge/source convergence plus schedule selection and global Xi identification.

## Hostile audit

1. **Fourier sign:** `(iz)^2=-z^2`, so bulk term in `(1)` is `+z^2F`.
2. **Full endpoint rank:** both sum and difference of endpoint values occur; no phase is claimed to
   erase both.
3. **No mean-zero shortcut:** theorem uses arbitrary endpoint values.
4. **No singular division:** annihilator `(4)` has polynomial coefficients and is defined at zero.
5. **No coefficient bounds:** `(5)` holds for arbitrary complex `A,B`.
6. **Topology:** limit statement uses compact-open holomorphic convergence, hence convergence of
   first two derivatives. Pointwise convergence is insufficient and is not used.
7. **Gauge order:** `L_a` is applied before a zero-free common gauge. It is not commuted through an
   arbitrary varying gauge. A gauge-covariant theorem would need logarithmic-gauge control.
8. **Does not preserve characteristic zeros:** `L_a` is a source-identification device, not a new
   real-zero approximant. Suzuki's original characteristic family remains the zero carrier.
9. **Novelty scope:** the ODE calculation is classical. Candidate novelty is identifying the exact
   finite-Neumann obstruction in Suzuki's RH limit as this annihilable module, thereby deleting a
   stated convergence premise. Specialist priority audit remains required.

## Formal status

Lean proves:

```text
neumannFourierBoundaryLaw
suzukiNeumannBoundaryFlux_eq_clock
neumannFourierBoundaryDifference_eq_clock
suzukiNeumannBoundaryAnnihilator_clock
suzukiNeumannBoundaryAnnihilator_fourierDefect_eq_zero
suzukiNeumannBoundaryAnnihilator_sq_mul
```

No axiom, `sorry`, computation, or RH premise is used. Direct Lean check, exact module build,
formal lint, and axiom audit all pass.

## Gates

- [x] 0 -> 1: corpus wall, competing conjectures, and falsifiers recorded
- [x] 1 -> 2: `(1)--(10)` proved and hostile audit passed
- [x] 2 -> 3: direct Lean check, exact module build, lint, and axiom audit passed
- [ ] 3 -> 4: external novelty/source-priority audit
