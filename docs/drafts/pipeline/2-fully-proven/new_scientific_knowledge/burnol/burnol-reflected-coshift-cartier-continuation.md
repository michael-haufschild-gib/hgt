# Burnol reflected co-shift Cartier continuation

- **ID:** `burnol-reflected-coshift-cartier-continuation`
- **Stage:** 2-fully-proven
- **Type:** `[PROVED HERE] [BRIDGE] [ROUTE R FRONTIER]`
- **Exact claim:** the divergent reflected co-shift at `1-rho` has a unique bounded,
  coefficient-faithful critical-line continuation equal to the negative forward divided shift;
  at every right-half Xi divisor it sends the fixed co-Poisson atom to an actual zero-divided
  extended-Sonin source and its fixed-source port is strictly negative.

## Goal

Replace the unspecified “opposite Stokes sign” in Route R by a constructed source object.  The
remaining source theorem must compare the forward physical port with this fixed reflected Cartier
continuation.  It no longer gets to choose an auxiliary vector, representation, or sign convention.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure operator and Xi-zero landing isolated; corpus and
  primary-literature audits complete
- [x] 1 -> 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [ ] 2 -> 3 formalized: exact Lean module, umbrella wiring, targeted build, lint, and axiom audit
- [ ] 3 -> 4 publication-ready: standalone exposition and external mathematical review

## Conjecture loop

1. `[FALSIFIED]` Pair the completed Euler--Gamma Stokes output at `rho` with the fixed atom.
   Existing transgression makes that output zero at every Xi zero, so it contains no horizontal
   sign.
2. `[FALSIFIED]` Identify the completed-Mellin zero evaluator with the divided shift.  Existing
   quantitative separation proves the evaluator is source-orthogonal while the divided shift has
   nonzero retained source projection.
3. `[FALSIFIED]` Read the desired nonpositive port from a positive atomic Gamma jump form.  Atomic
   and von-Mangoldt jump energies are nonnegative, hence have the wrong orientation.
4. `[SURVIVES]` Continue the reflected co-shift from the left half-plane as a bounded multiplier.
   Its coefficient is forced to be the negative forward Cauchy coefficient.  Existing Burnol
   zero-division then places its value on the fixed atom in the actual extended Sonin source.

## Definitions

On the critical Mellin line `w = 1/2 + i t`, put

```text
m_rho(t) = 1 / (rho - w),
r_sigma(t) = 1 / (w + sigma - 1).
```

For `Re rho > 1/2`, `m_rho` is the forward divided-shift multiplier.  For
`Re sigma < 1/2`, the physical integral defining the reflected co-shift is divergent, but
`r_sigma` is bounded on the critical line.  Define its Cartier continuation by the bounded Mellin
multiplier `R_sigma = U^{-1} M_(r_sigma) U`, where `U` is the corpus Mellin unitary.

## Paper proof

### Lemma 1: bounded left-half continuation

If `Re sigma < 1/2`, then for every critical-line `w`,

```text
|w + sigma - 1| >= 1/2 - Re sigma > 0.
```

Consequently

```text
|r_sigma(t)| <= (1/2 - Re sigma)^(-1),
```

so multiplication by `r_sigma` is bounded on Mellin `L2`.  This constructs `R_sigma` without a
zero, divisor, or RH premise.

### Lemma 2: exact reflection and sign

For every `rho` with `Re rho > 1/2`, take `sigma = 1-rho`.  Pointwise on the critical line,

```text
r_(1-rho)(t)
  = 1 / (w-rho)
  = -1 / (rho-w)
  = -m_rho(t).                                           (1)
```

Thus, by coefficient-faithfulness of multiplication and unitarity,

```text
R_(1-rho) = -M_rho.                                      (2)
```

More generally,

```text
Re r_sigma(t) = (Re sigma-1/2) |r_sigma(t)|^2.
```

Hence for every `f`,

```text
Re <f,R_sigma f>
  = (Re sigma-1/2) ||R_sigma f||^2 <= 0.                 (3)
```

The multiplier never vanishes, so `R_sigma` is injective.  Therefore `(3)` is strict for nonzero
`f`.

### Lemma 3: coefficient-faithful uniqueness

Suppose `T` is a bounded operator on the even physical space and, after Mellin transport, `T f`
has representative `r_sigma(t) U(f)(t)` for every `f`.  Then `U(Tf)=U(R_sigma f)` for every `f`.
Injectivity of `U` gives `Tf=R_sigma f`, hence `T=R_sigma`.  No alternative bounded continuation
with the same Cartier coefficient exists.

### Lemma 4: actual Xi-zero divided-source landing

Let `rho` be an Xi-divisor point with `Re rho>1/2`, and let `f0` be the fixed `[1/2,1]`
co-Poisson sub-window atom.  Since `xi(rho)=0`, `rho != 1`, and `Re rho>0`, the standard Xi--zeta
comparison gives `zeta(rho)=0`; in particular `Re rho<1`.

The explicit sub-window Mellin formula gives

```text
integral_0^infinity f0(x) x^(-rho) dx = 0.               (4)
```

Burnol's divided-shift preservation theorem applied to `(4)` shows

```text
M_rho f0 belongs to the extended Sonin space at aperture 1/2.  (5)
```

Combining `(2)` and `(5)`,

```text
R_(1-rho) f0 = -M_rho f0
```

is an actual extended-Sonin source vector.  It is not a formal negative channel added after
specialization; it is the zero-divided source already forced by the pre-divisor co-Poisson family.

### Theorem: fixed negative Cartier port

Define

```text
Pi_ref(rho) = <f0,R_(1-rho) f0>.
```

Equations `(2)`--`(3)` and nonvanishing of `f0` give

```text
Pi_ref(rho) = -Pi(rho),
Re Pi_ref(rho) < 0                                      (6)
```

throughout the open right half-plane.  At Xi divisors, Lemma 4 additionally proves the output is
the actual zero-divided Sonin source.

## Route R delta

Before this theorem, a source proof had to manufacture an unexplained nonpositive scalar.  After
it, the opposite orientation is a fixed, unique, coefficient-faithful source object:

```text
forward physical port Pi(rho)
        versus
reflected Cartier port Pi_ref(rho) = -Pi(rho).
```

It is now sufficient to prove, from pre-divisor Euler--Gamma--Stokes sewing, that the forward
physical lift and the reflected zero-divided source have the same fixed-source boundary reading at
an Xi divisor.  Equality and `(6)` imply `Re Pi(rho)<=0`, so the existing endpoint closes RH.

This comparison is still `[OPEN CORE]`; it is not assumed or hidden in the construction.

## Hostile audit

- This does **not** prove RH.  Forward/reflected Stokes sewing at Xi zeros remains unproved.
- Equation `(1)` is elementary operator theory; no novelty is claimed for the scalar identity.
- New corpus content is the exact synthesis: independent left-half Cartier continuation,
  coefficient-faithful uniqueness, fixed negative port, and landing of that negative continuation
  on the literal Xi-zero-divided Burnol source.
- Direct evaluator landing remains impossible by the existing separation theorem.
- A positive jump-form pairing alone remains insufficient; successful sewing must use the signed
  reflected boundary orientation constructed here.

## Literature boundary

Burnol's Sonine/co-Poisson papers provide Mellin division and Fourier reciprocity.  Standard
semigroup resolvent theory provides bounded half-plane multipliers.  Targeted searches found no
statement combining the left-half reflected continuation, the fixed `[1/2,1]` co-Poisson atom,
the actual Xi-divisor landing, and the Route R physical port.

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Theorie des Nombres de Bordeaux 16 (2004), 65--94.
- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007), 525--602.

## Log

- 2026-08-07 — conjecture loop completed; dependency-closed paper proof and hostile audit passed.
