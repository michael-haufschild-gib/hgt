# Completed-seam theta Green-square boundary law

- **ID:** `completed-seam-theta-green-square-boundary-law`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE LOOP] [ROUTE-P/C1 CROSS-ROUTE PRODUCER] [NO COMPUTATION]`
- **Parent route:** `completed-seam-thorin-subordinator-rh.md`
- **Source operator:** `hedenmalm-theta-source-compressed-inverse-determinant.md`
- **Boundary normal form:** `hedenmalm-quantile-volterra-universal-boundary-defect.md`

## Frozen question

Can Route P's positive compact carrier be produced from the fixed Hedenmalm theta source inverse,
rather than postulated as a measure or read from Xi zeros?

Let `B` be the Hilbert--Schmidt source inverse constructed from the positive theta density, let
`G` be its canonical singular positive quantile metric, and let `R_2=C^*+C` be the universal
rank-two pinned boundary form. Existing source theorems give

```text
G B - B^* G = i R_2.                                      (1)
```

Define the squared-seam spectral positivity predicate

```text
forall mu in spectrum(B), mu != 0 ->
  exists r>0, mu^2=r.                                     (2)
```

The frozen conjectural producer is:

> `[CONJECTURE P-GREEN]` Completed prime--polar--Gamma transport neutralizes the rank-two boundary
> current in `(1)` before Hilbert scalarization, so the nonzero spectrum of the source-built
> trace-class Green square `B^2` lies in `(0,infinity)`. Its algebraic spectral measure is the
> unique compact Route P carrier.

No theorem may define the neutralization from Xi zeros, the target moments, the desired measure,
or a positive part of the target operator.

## Conjecture loop

### P-G1 -- a fixed Witten diffusion carrier

`[FALSIFIED AS A PRODUCER]` The theta Born--Witten and thermal-Krylov corpus already supplies
positive diffusion/KMS carriers. Identifying their moment tower with
`normalizedPrimeArchMoment` is RH; degree one is the faithful transverse reflection-defect
energy. A fixed diffusion operator without a new source intertwiner only renames the target.

**Positive survivor.** Hedenmalm's `B` is different: it is source-defined before zeros and its
entire determinant is exactly `XiC/XiC(0)`.

### P-G2 -- total positivity of the universal Volterra bulk

`[FALSIFIED AS A SOURCE-SUFFICIENT PRINCIPLE]` Quantile conjugation writes

```text
B = i M_q C,
```

where `C` is the universal pinned primitive and all theta dependence is the positive speed `q`.
This normal form holds for arbitrary positive even densities whose Fourier transforms can have
nonreal zeros. Brownian/Monge or Volterra total positivity of the universal bulk therefore cannot
force theta spectral reality. The existing Brownian--Monge failed-route audit independently shows
that ordered-minor positivity does not orient the arithmetic response.

**Positive survivor.** The failure is not infinite-dimensional bulk. Equation `(1)` proves it is
one universal rank-two boundary current.

### P-G3 -- decoupled positive boundary repair

`[FALSIFIED]` `R_2` has inertia `(1,1)`. Adding only a decoupled positive scalar channel cannot
cancel it, while squaring first gives the positive Witten operator and deletes the Xi divisor
section. A legal repair must couple incoming and outgoing source amplitudes before positivity and
retain algebraic multiplicity.

**Positive survivor.** Right multiplication of `(1)` by `B` gives the exact Green-square law

```text
G B^2 = B^* G B + i R_2 B.                               (3)
```

The first term is a positive bulk square. Every obstruction to Route P spectral positivity is in
the rank-two correction `i R_2 B`.

## Dependency-closed theorem target

The current pass targets the unconditional part, not the open neutralization:

1. prove `(3)` as an operator identity;
2. prove `(2) <-> RH` using the exact nonzero spectrum of `B` and positivity of every reciprocal
   square's real part;
3. compose with the existing capstones to prove

   ```text
   (2)
   <-> PrimeArchCompactMarkovGermRepresentation
   <-> PrimeArchCompactThorinExponentRepresentation
   <-> RH;                                                (4)
   ```

4. retain the genuine open core as source-side neutralization of `i R_2 B`, not construction of
   another abstract carrier.

This changes Route P's ontology. Source operator and reciprocal-square spectral nodes already
exist. Missing compact measure is the positive spectralization of one concrete Green square, and
its complete failure is localized to a two-channel boundary law.

## Paper proof of the unconditional cross-route law

`[PROVED HERE]` Multiply `(1)` on the right by `B`. Associativity gives

```text
(G B-B^* G)B=i R_2 B,
G B^2-B^* G B=i R_2 B,
```

which is `(3)`. Since `G` is multiplication by the strictly positive theta metric symbol,

```text
<B^* G B f,f>=<G Bf,Bf>>=0.
```

Thus no bulk sign is missing: the unique correction is `i R_2 B`, whose range has dimension at
most two.

The exact Hedenmalm divisor theorem identifies every nonzero spectral point of `B` as `-z^(-1)`
for a centered Xi zero `z`, and the squared-seam theorem identifies its square with the canonical
reciprocal-square Route P node. It remains to prove the pointwise algebra behind `(2)`.

If `mu` is real and nonzero, `mu^2` is strictly positive real. Conversely, write `mu=a+ib` and
suppose `mu^2=r>0`. Imaginary parts give `2ab=0`. If `a=0`, real parts give
`r=-b^2<=0`, contradiction. Hence `a!=0`, so `b=0` and `mu` is real. Therefore

```text
every nonzero spectral mu has mu^2 in (0,infinity)
  <-> every nonzero spectral mu is real
  <-> RH.
```

The existing Route P capstones give compact Markov representation iff RH and compact Thorin
representation iff RH, proving `(4)` without a compactness, simplicity, support, or zero-location
hypothesis added to the source operator.

**New knowledge delta.** P and C1 do not have independent producer cores. Their first missing
theorems are two scalarizations of the same source boundary-neutrality law: C1 asks for real
nonzero spectrum of `B`; P asks for positive nonzero spectrum of `B^2`. Equation `(3)` proves the
entire difference from unconditional positive bulk is the universal incoming/outgoing rank-two
current. Future work should attack that current before scalar completion, not build another
measure, diffusion, or continuous theta reporter.

## Falsifiers

- If `(3)` has any additional bulk term after exact operator multiplication, rank-two reduction
  fails.
- If a nonzero theta spectral point can have a positive real square without being real, `(2)` does
  not imply RH.
- If Route P's canonical nodes differ from squared eigenvalues of `B`, cross-route identification
  fails.
- If the proposed source neutralization factors through `B^*B`, `A^*A`, target moment positivity,
  or zero-selected Riesz fibres, it is circular or divisor-blind.

## Gates

- [x] internal Route P, Route Q, thermal-Krylov, Hedenmalm, and failed-route collision audit
- [x] current Thorin/GGC and Hedenmalm literature boundary checked
- [x] conjecture frozen before proof engineering
- [x] Witten-carrier, universal-total-positivity, and positive-boundary-repair shortcuts attacked
- [x] dependency-closed paper proof of `(3)`--`(4)`
- [ ] Lean formalization and umbrella wiring
- [ ] exact source construction neutralizing `i R_2 B`
- [ ] positive compact carrier
- [ ] RH
