# Suzuki rectangular positive archimedean lag completion

- **ID:** `suzuki-rectangular-positive-arch-lag-completion`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT SOURCE COMPLETION / POSITIVE MANGOLDT QUADRATURE / FRONTIER REDUCTION
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.Suzuki.SuzukiRectangularPositiveArchLagCompletion`
- **RH used:** no
- **Computation used:** no

## Formal theorem package

For the sharp two-edge autocorrelation `C(h)=R_(L,a)(h)`, Lean proves unconditionally:

1. `0<=C(h)<=C(0)=2L` for `0<=L<=a` and `h>=0`;
2. the common-lag polar--Gamma kernel

   ```text
   K(t)=2 cosh(t/4)C(t/2)
        +[exp(-t)C(0)-exp(-t/4)C(t/2)]/[1-exp(-t)]
   ```

   has exact split

   ```text
   K(t)=exp(t/4)C(t/2)
     +exp(-t)/[1-exp(-t)] [C(0)-exp(-t/4)C(t/2)];
   ```

3. `K(t)>=0` for `t>0`, and `K(t)>0` when `L>0`;
4. `K` is integrable and its integral is normalized archimedean mass plus fixed
   `(gamma+log pi)2L` boundary charge;
5. the finite prime wall is nonnegative and the full Weil value is exactly completed lag mass
   minus twice prime-wall mass and boundary charge;
6. every sharp prime cell is an exact sample of first positive channel
   `A(t)=exp(t/4)C(t/2)`:

   ```text
   Lambda(n)/sqrt(n) C(log n)=Lambda(n)/n A(2 log n);
   ```

7. hence whole prime wall is exact finite Mangoldt quadrature of `A` and is bounded by same-node
   quadrature of `K`;
8. on every admissible logarithmic tail, RH is equivalent to Lebesgue mass of `K` dominating this
   explicit Mangoldt atomic quadrature plus fixed boundary charge.

## Principal declarations

```text
rectangularTwoEdgeAutocorrelation_le_zeroLag
suzukiRectangularCompletedArchLagKernel_eq_positive_split
suzukiRectangularCompletedArchLagKernel_nonneg
suzukiRectangularCompletedArchLagKernel_pos
integral_suzukiRectangularCompletedArchLagKernel
vonMangoldt_primeCell_eq_positiveArchSample
rectangularPrimeAutocorrelationSum_eq_positiveArchMangoldtQuadrature
rectangularPrimeAutocorrelationSum_le_completedArchMangoldtQuadrature
xiWeilPolarization_rectangular_add_boundaryCharge_eq_completedLagMass_sub_primeWall
riemannHypothesis_iff_positiveArchMangoldtQuadrature_le_completedLagMass_tail
```

## Frontier reduction

Gamma sign ambiguity is closed: Gamma and polar terms form one pointwise positive lag kernel.
Prime-source identification is also closed at aggregate level: the prime wall is exact logarithmic
sampling of first positive channel, not merely an analogous positive sum.  Remaining RH-bearing
statement is one restricted-family positive quadrature discrepancy

```text
2 sum Lambda(n)/n A(2 log n)+(gamma+log pi)2L <= integral K.
```

Corpus seam no-go rules out proving this by universal reconstruction from integer-log samples.
Needed new theorem must exploit sharp rectangular family and restricted-Weil/Robin transport.

## Novelty boundary

Autocorrelation bounds, hyperbolic identities, and generic quadrature language are classical.
Candidate novelty is exact Suzuki sharp-source weld: polar--Gamma common-lag positivity together
with identity of finite von-Mangoldt wall as samples of first positive split channel.  Internal
search found separate Gamma, polar, dyadic quadrature, and sampling no-go modules but no matching
synthesis.  Current Suzuki/Groskin primary-source audit found no collision; independent priority
audit remains open.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiRectangularPositiveArchLagCompletion.lean` — PASS;
- final targeted build:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` — PASS, `9512/9512`;
- axiom surface of eight capstones: `propext`, `Classical.choice`, `Quot.sound` only;
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- repository lint reaches module; current errors are 21 unrelated shared-tree unreachable modules.

## Gates

- [x] 0 -> 1: source-pure conjecture and hostile falsifiers
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean formalization
- [ ] independent primary-literature priority audit
- [ ] positive restricted-family Mangoldt quadrature domination
- [ ] RH
