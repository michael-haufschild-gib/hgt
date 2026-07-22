# Suzuki critical apex-vacuum capacity no-go

- **ID:** `suzuki-critical-apex-vacuum-capacity-no-go`
- **Stage:** 2 — fully proved on paper
- **Type:** UNIVERSAL EXTREMAL LAW / SOURCE-CLASS NO-GO
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOT RH]`
  `[APPLICATION NOVELTY UNVERIFIED]`
- **Stage-1 audit:**
  `../../1-in-progress/suzuki-critical-apex-vacuum-capacity-no-go.md`
- **RH used:** no
- **Computation used:** no

## Statement

At Suzuki width two, let

```text
c_a=4a-4,
H_a=2 exp(a-1),
A_a(t)=suzukiRectangularPositiveArchSampleChannel(2,a,t),
K_a(t)=suzukiRectangularCompletedArchLagKernel(2,a,t).
```

There are explicit positive source measures satisfying the sharp cumulative band

```text
t-2 <= source([0,t]) <= t                                  (1)
```

whose `A_a` quadrature exceeds Lebesgue `A_a` mass by at least `H_a/128`.  Meanwhile

```text
integral_0^infinity (K_a-A_a)-(gamma+log pi)4              (2)
```

is bounded above independently of `a`.  Therefore, for cofinally large `a`, these sources violate
the completed-lag domination despite satisfying `(1)` and agreeing with Lebesgue measure on the
entire decreasing flank.  Cumulative log-Haar capacity and an unbounded apex-relative flank
surplus cannot by themselves prove Suzuki's RH-bearing quadrature inequality.

## Proof

### 1. Capacity-band sources

For `c>=2`, move Lebesgue mass of `(c-2,c)` to a mass-two atom at `c`:

```text
nu_c=1_([0,infinity)\(c-2,c))dt+2 delta_c.
```

Its cumulative mass is `t` before `c-2`, `c-2` inside the gap, and `t` from `c` onward.  It is
nondecreasing and satisfies `(1)`.  Direct integration gives

```text
integral Phi dnu_c-integral Phi dt
 =2Phi(c)-integral_(c-2)^c Phi(t)dt.                        (3)
```

For an atomless version, use density one outside `(c-2,c)`, zero on `(c-2,c-1/4)`, and eight on
`(c-1/4,c)`.  Call the resulting measure `mu_c`.  Its cumulative deficit is zero before the gap,
rises with slope one to `7/4`, then falls with slope seven to zero.  Thus `(1)` holds, and

```text
integral Phi dmu_c-integral Phi dt
 =8 integral_(c-1/4)^c Phi(t)dt-integral_(c-2)^c Phi(t)dt. (4)
```

### 2. Critical apex amplification

Put

```text
phi(x)=exp(x/2)(1-|x|/2),  -2<=x<=2.
```

On `[-1,-1/2]`, `exp(x/2)<=1` and `1+x/2<=3/4`; on `[-1/2,0]`, both factors are at most one.
Therefore

```text
integral_(-1)^0 phi <= (1/2)(3/4)+(1/2)=7/8.              (5)
```

The already-proved exact Suzuki connector says, for `a>=3`,

```text
A_a(c_a+2x)=H_a phi(x),  -2<=x<=2.                         (6)
```

Equations `(3),(5),(6)` imply the atomic excess is at least `H_a/4`.

For `x in [-1/8,0]`, convexity of the exponential gives

```text
exp(x/2)>=1+x/2>=15/16,
phi(x)>=225/256.                                           (7)
```

Using `t=c_a+2x` in `(4)`, then `(5),(7)`, gives

```text
integral A_a dmu_(c_a)-integral A_a dt
 >=16H_a(1/8)(225/256)-2H_a(7/8)
 =H_a/128.                                                 (8)
```

### 3. Uniform completed reserve

Write `C_a(h)=rectangularTwoEdgeAutocorrelation(2,a,h)`.  Since

```text
K_a(t)-A_a(t)=exp(-t/4)C_a(t/2)
               +rectangularGammaCancellationKernel(2,a,t),
```

subtracting the fixed boundary charge yields

```text
R_a=integral_0^infinity exp(-t/4)C_a(t/2)dt
    +rectangularGammaPolarCorrection(2,a).                 (9)
```

The sharp autocorrelation contraction already in the corpus gives

```text
0<=C_a(t/2)<=C_a(0)=4
```

for every positive lag.  Since `integral_0^infinity exp(-t/4)dt=4`,

```text
integral_0^infinity exp(-t/4)C_a(t/2)dt<=16.                (10)
```

The corpus uniform Gamma--polar theorem gives

```text
|rectangularGammaPolarCorrection(2,a)|
 <=rectangularGammaPolarUniformBound(2).                   (11)
```

Consequently

```text
R_a<=B_*:=16+rectangularGammaPolarUniformBound(2)           (12)
```

for every `a>=3`.

### 4. Cofinal violation

Since `H_a/128=exp(a-1)/64` tends to infinity, choose `a>=3` with `H_a/128>B_*`.  Equations
`(8),(12)` then give

```text
integral A_a dmu_(c_a)+(gamma+log pi)4
 >integral_0^infinity K_a(t)dt.                             (13)
```

The source `mu_(c_a)` is atomless, satisfies `(1)`, and equals Lebesgue measure on
`(c_a,c_a+4)`.  Its decreasing-flank apex deficit is positive and proportional to `H_a`, so even
an unbounded untouched right-flank surplus coexists with `(13)`.  This proves the claim.  QED.

## Hostile verdict and exact scope

- The result is not a counterexample to RH and does not model the full von Mangoldt source.
- It applies to every proposed proof whose arithmetic information factors only through cumulative
  band `(1)`, even if atomlessness or unbounded opposite-flank surplus is added.
- It does not exclude a genuinely source-specific restricted-Weil/Robin identity that distinguishes
  actual Mangoldt mass from the explicit extremizers.
- It kills interpreting S69 apex-relative block surplus as unused capacity.  Target multiplicity
  or an independent arithmetic commutator sign remains necessary.

## Positive survivor

**Apex-vacuum amplification law.**  A uniformly bounded cumulative displacement can create
unbounded quadrature excess at a moving exponentially tilted apex while leaving the entire
opposite flank unchanged.  This is the exact extremal obstruction that common-shift overlap alone
did not expose.

## Gates

- [x] dependency-closed paper proof
- [x] atomic objection removed by explicit atomless source
- [x] reflected-polar, Gamma, and fixed-charge reserve included
- [x] scope limited to capacity/flank-surplus information class
- [ ] exact Lean theorem
- [ ] actual-Mangoldt source discriminator or RH
