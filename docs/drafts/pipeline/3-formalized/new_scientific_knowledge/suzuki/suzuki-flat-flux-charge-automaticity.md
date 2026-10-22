# Flat Suzuki primitive flux has no independent terminal charge

- **ID:** `suzuki-flat-flux-charge-automaticity`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-HYPOTHESIS DISCHARGE / PHYSICAL-ENDPOINT INDICIAL CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Lean:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiFlatFluxChargeAutomatic`
- **Inputs:** `suzuki-flat-primitive-flux-volterra-liouville.md`,
  `suzuki-paired-seam-carleman-logistic-normal-form.md`,
  `suzuki-interior-seam-indicial-dipole-exclusion.md`

## 1. Correction and result

The flat primitive-flux theorem listed

```text
Y has no terminal constant flux charge
```

as a separate premise.  That premise is redundant.  The theorem already assumes that the value
blocks are superpolynomially flat and that the primitive source is exponentially small.  The
defining flux equation then forces every terminal flux block to zero.  Any strong terminal limit
is therefore zero.

There is a second, source-specific version of the same correction at a physical endpoint.  With
the exterior orientation equal to the literal zero extension, the one-sided indicial coefficient
has only the half-log root.  The borderline `1/log` dipole produces an uncancelled logarithmic
source and is impossible against Suzuki's bounded completed source.  Thus physical-root dipole
matching is not an additional datum after the half-log trace is zero.

Precisely:

```text
all-orders-flat value block
+ localized Gamma remainder tending to zero
+ primitive source tending to zero
+ exact primitive-flux equation
 -> terminal flux charge =0;                            (1)

bounded literal physical-endpoint source
+ zero exterior orientation
 -> unique conormal root tau=1/2
    and no nonzero tau=1 dipole.                         (2)
```

This removes one analytic hypothesis from finite-recurrence E assembly.  It does not construct
the literal infinite paired equation, prove arbitrary finite-order expansion, cover the compact
middle, pass recurrence-infinite apertures, prove Evans positivity, or prove RH.

## 2. Automatic zero charge in block norm

Let (X) be a Hilbert space, (I_n=[n,n+1]), and write

```text
f_n=||F||_(L2(I_n;X)),
y_n=||Y||_(L2(I_n;X)),
g_n=||G||_(L2(I_n;X)).                                  (3)
```

The first primitive-flux equation is

```text
(2L I+R-B)F-Y=G.                                       (4)
```

The proved Gamma localization estimate gives, for some (mu>0),

```text
||(R F)||_(L2(I_n))
 <=C (E_mu f)_n,

(E_mu f)_n=sum_m exp(-mu|n-m|)f_m.                     (5)
```

Consequently `(4)` yields

```text
y_n
 <=2(n+1)f_n+C(E_mu f)_n+||B||f_n+g_n.                 (6)
```

Assume, as in the flat theorem,

```text
for every N,  f_n=O_N(n^(-N)),
g_n=O(exp(-delta n)).                                  (7)
```

Taking (N=2) already gives

```text
n f_n ->0.                                             (8)
```

Exponential convolution preserves superpolynomial decay.  Indeed split `(5)` into

```text
m<n/2,       n/2<=m<=2n,       m>2n.                   (9)
```

On the middle range use (f_m=O_N(n^{-N})) and sum the exponential kernel.  On the two outer
ranges (|n-m|ge n/2), so the exponential factor is (O(e^{-mu n/2})); summability of (f),
which follows from `(7)` with (N=2), controls the remaining mass.  Therefore

```text
(E_mu f)_n=O_N(n^(-N))
```

for every (N).  Equations `(6)`--`(8)` imply

```text
y_n ->0.                                               (10)
```

The second flux equation has integrable derivative in the flat class, so the original proof
already gives a strong limit

```text
Y(L)->Y_infinity.                                      (11)
```

Strong convergence on unit blocks implies

```text
y_n^2=integral_n^(n+1)||Y(L)||^2dL ->||Y_infinity||^2. (12)
```

Combining `(10)` and `(12)` gives (Y_infty=0).  Thus the backward Volterra identity follows
without an independent charge premise:

```text
Y(L)=-integral_L^infinity [D F(t)-H(t)]dt.              (13)
```

The rest of the flat Volterra proof is unchanged.  `QED`

## 3. Physical endpoint has no dipole charge

At a physical endpoint retain the interior profile

```text
F(L)=u(a-exp(-L))
```

and the exterior profile (F_{m out}=0).  Suzuki's exact one-sided logarithmic jump is the
specialization of the paired normal form

```text
J_phys F
 =[2L+q(L)]F(L)-integral_0^L F(t)dt+(R F)(L),
q(L)=O(exp(-L)).                                       (14)
```

For a conormal profile

```text
F(L)=beta L^(-tau)+o(L^(-tau)),       0<tau<1,          (15)
```

the Gamma remainder is lower by two inverse-log orders, while

```text
2L F-integral_0^L F
 =[(1-2tau)/(1-tau)] beta L^(1-tau)
   +o(L^(1-tau)).                                      (16)
```

Thus a bounded source permits a nonzero coefficient only when

```text
tau=1/2.                                               (17)
```

This is exactly the physical half-log trace.  At the borderline

```text
F(L)=beta/L+o(1/L),                                    (18)
```

the same exact calculation gives

```text
J_phys F=-beta log L+O(1)+o(log L).                    (19)
```

There is no opposite-orientation Carleman term at a physical endpoint: it is identically zero.
Every other literal term in the completed Suzuki source is bounded there.  Hence `(19)` forces

```text
beta=0.                                                (20)
```

So zero half-log trace removes the only subunit physical root, and the physical endpoint admits
no independent `1/log` dipole/constant-flux channel.  This is distinct from an interior seam,
where the two orientations can form an antisymmetric dipole before source continuity kills it.
`QED`

## 4. Exact frontier movement

```text
flat primitive flux:
  terminal zero charge is automatic;                   [CLOSED]

physical endpoint finite charges:
  half-log root only; one-sided dipole impossible;      [CLOSED]

interior finite charges:
  common value and antisymmetric dipole already killed; [CLOSED]

literal infinite paired source equation:
  assembled with rooted signs and source bounds;       [CLOSED]

arbitrary finite-order expansion / flat remainder:
  not yet proved for every completed mode;              [OPEN]

compact-middle coverage:
  closed by formalized dyadic orbit charts;

exceptional apertures:
  not yet proved.                                      [OPEN]               (21)
```

The corrected finite-type chain is therefore

```text
literal paired assembly
+ arbitrary finite-order expansion
+ zero physical half-log traces
+ finite recurrence
 -> automatic zero finite/flat charges
 -> weighted endpoint derivative.                     (22)
```

No separate physical-root dipole/flux matching theorem remains in `(22)`.

## 5. Hostile audit

1. **No pointwise flatness substitution.**  Section 2 uses only unit-block (L^2) norms.
2. **No hidden zero-charge premise.**  It is derived from `(4)`--`(12)`.
3. **No claim that trace zero implies arbitrary expansion.**  The expansion gate remains open.
4. **No deletion of low-frequency return.**  Boundary counterterms remain part of literal source
   assembly; only terminal dipole/flux matching is discharged.
5. **No exceptional-aperture claim.**  Recurrence-infinite apertures remain outside this theorem.
6. **No Evans/RH claim.**  Nonzero-trace return and square-Evans positivity remain untouched.

## 6. Lean certificate

The unconditional formal core is in

```text
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFlatFluxChargeAutomatic.lean
```

It proves:

```text
tendsto_natCast_mul_of_superpolynomiallyFlat
flat_flux_terminal_charge_automatic
physicalEndpointIndicialCoefficient_eq_zero_iff
physicalEndpointDipoleLogCoefficient_eq_zero_iff
```

The first two declarations formalize `(8)` and the exact squeeze from `(6)` to `(10)`.  The last
two formalize the source-normalized indicial coefficients `(16)` and `(19)`: the unique nonzero
subunit root is `tau=1/2`, and a vanishing logarithmic dipole coefficient is exactly a zero dipole.
The existing `SuzukiFlatPrimitiveFluxAssembly` module supplies the backward Volterra and
exponential-decay steps after the now-derived zero limit.

## 7. Novelty boundary

Polynomial decay under a linear weight, preservation of rapid decay by an exponentially decaying
convolution kernel, and one-sided regular-singular indicial calculations are classical.  The new
source knowledge is the correction that Suzuki's exact flat primitive-flux hypotheses already
annihilate the terminal charge, together with the physical-zero-extension specialization showing
that no separate endpoint dipole matching survives.  Corpus search found no prior statement of
this discharge.  External priority remains unverified.

## Gates

- [x] derive block flux bound from the exact primitive equation
- [x] prove `n f_n ->0` from superpolynomial flatness
- [x] prove exponential envelope preserves superpolynomial flatness
- [x] prove terminal flux charge is automatic
- [x] classify the one-sided physical indicial root
- [x] exclude the physical `1/log` dipole
- [x] formalize exact sequence and indicial cores in Lean
- [x] construct literal infinite paired-orbit source equation
- [ ] prove arbitrary finite-order expansion for every completed mode
- [x] prove compact-middle coverage by dyadic orbit charts
- [ ] pass recurrence-infinite apertures
- [ ] prove completed Evans injectivity
- [ ] prove RH or whole-Connes no-go
