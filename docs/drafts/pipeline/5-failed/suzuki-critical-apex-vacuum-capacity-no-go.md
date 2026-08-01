# Suzuki critical apex-vacuum capacity no-go

- **ID:** `suzuki-critical-apex-vacuum-capacity-no-go`
- **Stage:** 5 — failed capacity/flank producer; positive survivor formalized
- **Type:** UNIVERSAL EXTREMAL LAW / SOURCE-CLASS NO-GO
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL] [NOT RH]`
- **Parents:** `suzuki-mangoldt-log-haar-bicausal-transport.md`,
  `suzuki-bicausal-no-free-splice-classification.md`
- **Failed producer:** `suzuki-mangoldt-macroscopic-prime-block-surplus.md` when its
  apex-relative flank surplus is treated as unused target capacity
- **RH used:** no
- **Computation used:** no

**Terminal note.** This historical attack is closed.  Its cofinal tail strengthening and exact
universal-class negation are formalized in
`formal/GaloisForLFunctions/RHTower/SuzukiCriticalApexVacuumCapacityNoGo.lean`.  The former
`SUZUKI-SOURCE-COMMUTATOR-GRAM` successor was later retired as a stale label: commutator/Gram
infrastructure already exists, and remaining signed/cofinal operator floor belongs to Route G.

## Exact frontier attacked

S67 supplies only the cumulative band

```text
t-2 <= F(t) <= t.                                           (1)
```

S69 supplies an unbounded apex-relative right-flank surplus.  Neither statement records whether
the right-flank continuum capacity is already consumed.  The live question is whether `(1)`, even
augmented by arbitrarily large untouched right-flank surplus, forces Suzuki's completed-lag
quadrature inequality.  The theorem below says no.

## Capacity-band extremizer

For `c>=2`, let `nu_c` be Lebesgue measure on the positive axis after all mass of `(c-2,c)` is
moved to one atom at `c`:

```text
nu_c = 1_([0,infinity) \ (c-2,c)) dt + 2 delta_c.            (2)
```

Its cumulative mass is

```text
F_c(t)=t,        0<=t<=c-2,
       c-2,      c-2<t<c,
       t,        c<=t.                                      (3)
```

Hence `F_c` is nondecreasing, has total capacity one away from one evacuated gap, and satisfies
`(1)` sharply.  For every integrable profile `Phi`,

```text
integral Phi dnu_c - integral_0^infinity Phi(t)dt
 =2 Phi(c)-integral_(c-2)^c Phi(t)dt.                        (4)
```

This is the exact extremal quantity hidden by cumulative capacity bookkeeping.

The atomic extremizer is not essential.  An atomless regularization moves the same gap mass into
the last quarter-unit before the apex:

```text
dmu_c/dt =1 outside (c-2,c),
           0 on (c-2,c-1/4),
           8 on (c-1/4,c).                                (5)
```

Its cumulative deficit `t-mu_c([0,t])` rises from `0` to `7/4`, then falls linearly to `0`, so it
also lies in `[0,2]`.  It has no atoms and

```text
integral Phi dmu_c-integral_0^infinity Phi(t)dt
 =8 integral_(c-1/4)^c Phi(t)dt-integral_(c-2)^c Phi(t)dt. (6)
```

## Theorem A: critical tilted-apex amplification `[PAPER-PROVED]`

Let

```text
phi(x)=exp(x/2)(1-|x|/2),  -2<=x<=2.
```

For `x in [-1,-1/2]`, `phi(x)<=3/4`; for `x in [-1/2,0]`, `phi(x)<=1`.  Therefore

```text
integral_(-1)^0 phi(x)dx <= 7/8.                            (7)
```

For Suzuki width `L=2`, aperture `a>=3`, moving apex

```text
c_a=4a-4,    H_a=2exp(a-1),
```

the corpus identity gives

```text
A_(2,a)(c_a+2x)=H_a phi(x),  -2<=x<=2.                      (8)
```

Substitution `t=c_a+2x` in `(4)` and `(7)` gives the sharp-enough atomic lower bound

```text
integral A_(2,a) dnu_(c_a)-integral_0^infinity A_(2,a)(t)dt
 =2H_a-2H_a integral_(-1)^0 phi(x)dx
 >=H_a/4.                                                  (9)
```

The atomless source is still cofinally bad.  On `[-1/8,0]`, both
`exp(x/2)>=1+x/2` and `1+x/2>=15/16`, so `phi(x)>=225/256`.  Equations `(6)--(8)` give

```text
integral A_(2,a) dmu_(c_a)-integral_0^infinity A_(2,a)(t)dt
 >=16H_a(1/8)(225/256)-2H_a(7/8)
 =H_a/128.                                                (10)
```

Both excesses tend to infinity with `a`.  Thus neither a uniform atom bound nor atomlessness
repairs capacity-only domination.

## Theorem B: Suzuki completed reserve is uniformly bounded `[PAPER-PROVED]`

Put

```text
R_a=integral_0^infinity (K_(2,a)(t)-A_(2,a)(t))dt
    -(gamma+log pi)4.                                     (11)
```

The original common-lag decomposition, not the later positive split, gives

```text
R_a=integral_0^infinity exp(-t/4)C_(2,a)(t/2)dt
    +GammaPolarCorrection(2,a).                           (12)
```

The corpus sharp autocorrelation contraction gives

```text
0<=C_(2,a)(t/2)<=C_(2,a)(0)=4
```

for every positive lag.  Since `integral_0^infinity exp(-t/4)dt=4`,

```text
integral_0^infinity exp(-t/4)C_(2,a)(t/2)dt <=16.          (13)
```

The corpus Gamma--polar theorem proves

```text
|GammaPolarCorrection(2,a)|<=GammaPolarUniformBound(2).   (14)
```

Thus, with the aperture-independent constant

```text
B_*=16+GammaPolarUniformBound(2),
```

one has `R_a<=B_*` for every `a>=3`.

## Theorem C: capacity-only completed-lag domination fails cofinally `[PAPER-PROVED]`

Because `H_a/128=exp(a-1)/64` is unbounded, there is `a>=3` with `H_a/128>B_*`.  Combining
`(10)--(14)` gives even for the atomless source

```text
integral A_(2,a) dmu_(c_a)+(gamma+log pi)4
  > integral_0^infinity K_(2,a)(t)dt.                     (15)
```

Nevertheless `mu_(c_a)` satisfies the exact S67 band `(1)`.  It also agrees with Lebesgue measure
on the complete decreasing/right flank `(c_a,c_a+4)`.  Consequently its right-flank
apex-relative surplus is positive and grows proportionally to `H_a`; that surplus coexists with,
rather than repairs, the completed-lag violation `(15)`.

## Hostile attack

1. **Not a counterexample to RH or Mangoldt.** `nu_c` and `mu_c` are adversarial sources in the class
   described by S67's cumulative information.  The theorem proves insufficiency of that
   information, not failure for actual von Mangoldt mass.
2. **Not limited to common displacement.** `(2)--(6)` make no cell or transport choice.  Every
   argument whose arithmetic input factors only through `(1)` must also accept these sources.
   The atomless model removes the objection that one width-two atom is unlike Mangoldt weights.
3. **S69 survives only as consumed surplus.** Right-flank surplus can be unbounded while the
   global inequality fails; apex-relative source surplus is not free capacity.
4. **Completed channel included.** Uniform reserve `(11)--(14)` includes reflected polar and Gamma
   channels plus the fixed boundary charge; the countermodel does not drop them.
5. **Exact scope.** Source-specific identities beyond cumulative capacity may distinguish Mangoldt
   mass from `nu_c`.  Restricted-Weil/Robin operator structure remains open.

## Relentless-interrogation verdict

Verdict is `FALSE` for the conjecture that S67 capacity plus S69-style
unbounded flank surplus can produce completed-lag domination.  Strongest positive survivor is the
universal apex-vacuum amplification law `(4),(9),(10)`: bounded cumulative displacement can create
unbounded quadrature error at a moving exponential apex while leaving the opposite flank intact.

Stronger surviving conjecture:

`SUZUKI-SOURCE-COMMUTATOR-GRAM` — actual Mangoldt mass must be distinguished from the extremizer by
an exact source identity controlling the signed displacement commutator, not by capacity,
apex-relative deficit, or block abundance alone.  A restricted-Weil/Robin Gram identity is useful
only if constructed from the actual source before the target deficit is known.

## Literature boundary

Strassen/Hall transport duality and rearrangement extremizers are classical background.  Suzuki's
2022 and 2026 screw-function papers formulate Weil positivity and finite-interval operator limits
but do not provide this log-Haar capacity countermodel.  Candidate contribution is exact
Suzuki-channel obstruction and its uniform completed-reserve comparison; priority remains
unverified.

## Gates

- [x] internal corpus and failed-route collision audit
- [x] current Suzuki and transport-theory source audit
- [x] exact falsifiable statement
- [x] hostile paper proof closes with all measure and integral boundaries checked
- [x] Stage 2 theorem status earned; archival copy pending exact Lean statement lock
- [x] exact Lean formalization, including every-threshold countermodels
- [x] capacity/flank scalar class retired
- [ ] source-specific operator floor / RH — tracked only under Route G
