# Theta-source global conservative current sewing law

- **ID:** ULF-ODTM-6
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ULF-ODTM-4, ULF-ODTM-5, dependent Hilbert sums
- **Statement:** Canonically normalized theta-source conormal currents sew into one bounded global
  operator with exact local recovery; source reflection lifts to a global unitary whose conjugation
  law retains the complete fibre current with the Jordan-depth parity character.

## Goal

Construct one global object containing every nonzero theta-source root history without choosing a
zero enumeration, suppressing multiplicity, or losing functional-equation orientation.  This is a
conservative formation law, not an RH selection claim.

## Gates

- [x] 0 → 1 in-progress: bounded assembly and reflection law identified
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem/module and targeted audit
- [ ] 3 → 4 publication-ready: standalone exposition and external audit

## Construction

For every nonzero theta-source spectral point `mu`, let `G_mu`, `C_mu`, and `d_mu` be its complete
root block, conormal current, and complex dimension.  Put

```text
a_mu = (1 + ||C_mu||)^(-1),
D_mu = a_mu C_mu.
```

Then `0 < a_mu`, `D_mu != 0`, `range D_mu = range C_mu`, and

```text
||D_mu|| = ||C_mu|| / (1 + ||C_mu||) <= 1.
```

Direct dependent reindexing by `mu -> -mu` is mathematically legitimate but forces irrelevant
transport casts between propositionally equal root-block types.  Instead internalize each reflected
orbit in its oriented Hilbert double

```text
P_mu = G_mu direct-sum^2 G_(-mu).
```

Then define

```text
G = direct-sum^2_{mu in Spec(B) minus {0}} P_mu,
D = direct-sum_mu (D_mu direct-sum D_(-mu)) : G -> G.
```

No enumeration or choice of orbit representatives is used.  The redundant orientation is
intentional: it is the minimal closed observer in which reflection is internal and exact recovery
of either open orientation remains visible.  Uniform contractivity makes `D` bounded.

Let `sigma(mu)=-mu`.  ULF-ODTM-5 supplies unitary maps

```text
R_mu : G_mu -> G_sigma(mu).
```

Reflection is the fibrewise swap-transport

```text
R_mu^pair(v,w) = (R_mu^(-1) w, R_mu v),
(R f)_mu = R_mu^pair(f_mu).
```

Define the depth character by

```text
chi_mu = (-1)^(d_mu-1).
```

and let `Chi` be its diagonal unitary on `G`.

## Theorem

1. `D` is a contraction.
2. Every fibre is recovered exactly:

   ```text
   D(single_mu(v,w)) = single_mu(D_mu v, D_(-mu) w),
   first(coordinate_mu(D(single_mu(v,0)))) = D_mu v.
   ```

   Multiplication by the known factor `1+||C_mu||` recovers `C_mu v` exactly.  Consequently no
   nonzero local conormal current disappears globally.
3. `R` is a unitary involution and `Chi` is a unitary involution.
4. Reflection preserves the canonical normalization:

   ```text
   a_sigma(mu) = a_mu.
   ```

5. The exact global conservation identity is

   ```text
   R D R = Chi D.
   ```

6. At a fibre arising from an actual Xi divisor point `rho`,

   ```text
   chi_mu = (-1)^(xiSupportMultiplicity(rho)-1).
   ```

Thus the global closed observer retains every local rank-one recovered eigenline and records the
parity of the open Jordan history.  Functional-equation sewing is information-neutral.

## Proof [PROVED HERE]

Positivity of `1+||C_mu||` gives `a_mu != 0`.  Nonzero scalar multiplication preserves
nonvanishing and range.  The norm formula follows from the operator norm under scalar
multiplication; `x/(1+x)<=1` for `x>=0` proves uniform contractivity.  The standard dependent
`ell^2` diagonal construction therefore defines `D` with norm at most one.  Its single-coordinate
identity proves both recovery formulas and global faithfulness.

The map `sigma` is involutive because the nonzero source spectrum is reflection stable.  On the
oriented double, `R_mu^pair` is unitary: it applies the two inverse local unitaries and swaps the
two `L2` summands.  It squares literally to the identity.  Componentwise assembly on the dependent
`ell^2` sum is therefore a global unitary involution, without any dependent equality transport.

ULF-ODTM-5 gives `||C_sigma(mu)||=||C_mu||`; hence `a_sigma(mu)=a_mu`.  Its local covariance law
therefore also holds for normalized currents:

```text
D_sigma(mu) R_mu = chi_mu R_mu D_mu.
```

Evaluate `R D R` on `(v,w)` in `P_mu`.  Its first component is
`R_mu^(-1) D_(-mu) R_mu v = chi_mu D_mu v`.  Its second component follows from the same covariance
applied to `R_mu^(-1)w` and `chi_mu^2=1`.  Coordinate extensionality proves `R D R=Chi D`.
Both `chi_mu^2=1` and `|chi_mu|=1` are immediate, so `Chi` is a unitary involution.  Finally,
`d_mu=xiSupportMultiplicity(rho)` on the recovered Xi-support fibre, proving the last formula.
QED.

## Universal-law interpretation

Bounded global formation is not obtained by discarding large local histories.  It is obtained by
projectivizing their amplitudes while retaining range, rank, depth parity, and exact coordinate
recovery.  This supplies a genuine global conservation object.  It also sharpens the remaining RH
gate: any successful properness law must constrain which source fibres occur, because generic
bounded sewing, positivity, and reflection are now all available unconditionally.

## Scope

No RH consequence is asserted.  The known generic-properness no-go still applies.  Remaining
selection mechanism must couple this global source current to arithmetic formation depth or an
equivalent source-occurrence budget.

## Log

- 2026-08-31 — complete paper proof; promoted directly to Stage 2
- 2026-08-31 — replaced dependent reindex presentation by equivalent oriented `L2` orbit double;
  conservation and exact recovery are now literal fibrewise laws
- 2026-08-31 — formalized in
  `RHTower.HedenmalmThetaSourceGlobalConormalCurrentSewing`; direct elaboration, targeted leaf
  build, axiom audit, forbidden-declaration scan, and diff check pass
