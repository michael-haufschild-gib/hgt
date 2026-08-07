# Suzuki parity two-edge complementarity and odd-floor amplification

- **ID:** `suzuki-parity-two-edge-complementarity`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [FORMALIZATION IN PROGRESS] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096;
  `smooth-regularization-transverse-weil-floor-amplification.md`;
  `CCMRectangularTwoSidedOscillation.lean`
- **Statement:** Symmetric and antisymmetric fixed-width two-edge trials have aperture-independent
  total Xi--Weil energy. Consequently false RH forces exponential excursions of both signs in
  each parity sector and exponential negative-floor amplification in the odd restricted-Weil
  block as well as the already known even block.

## Goal

Replace generic parity comparison by a literal source theorem for Suzuki's restricted-Weil
operator. The result must say something unavailable from self-adjointness, positivity of shifted
resolvents, or target moments: it must use the exact two-edge arithmetic Weil source and separate
the even and odd operator blocks before scalarization.

## Exact parity pair

Fix `L>0`, an aperture `a>=L`, and write

```text
A_L(w)=(1-exp(-Lw))/w,
R_(L,a)(w)=exp(aw)A_L(w),
S_(L,a)(w)=exp(-aw)A_L(-w).
```

The sharp even and odd physical edge packets are

```text
h_e=1_[a-L,a]+1_[-a,-a+L],
h_o=1_[a-L,a]-1_[-a,-a+L],
```

with bilateral transforms

```text
F_e(w)=R_(L,a)(w)+S_(L,a)(w),
F_o(w)=R_(L,a)(w)-S_(L,a)(w).                         (1)
```

In the centered Xi spectral coordinate put

```text
E_(L,a)(z)=F_e(iz),
O_(L,a)(z)=F_o(iz).
```

Real evenness gives `E#=E`; real oddness gives `O#=-O`, where
`G#(z)=conj(G(conj z))`. Therefore their diagonal multiplicity-exact Xi--Weil energies are

```text
Q_e(L,a)=sum_q E_(L,a)(z_q)^2,
Q_o(L,a)=-sum_q O_(L,a)(z_q)^2.                        (2)
```

All series converge absolutely because every window amplitude is `O_L(1/|z_q|)` on the centered
critical strip and `sum_q |z_q|^(-2)<infinity`.

## The complementarity identity

Pointwise,

```text
E_(L,a)(z)^2-O_(L,a)(z)^2
 =4 R_(L,a)(iz)S_(L,a)(iz)
 =4 A_L(iz)A_L(-iz).                                  (3)
```

The exponentials cancel exactly. Hence the absolutely convergent trace

```text
K_L=4 sum_q A_L(iz_q)A_L(-iz_q)                       (4)
```

is independent of `a`, and `(2)--(3)` give

```text
Q_e(L,a)+Q_o(L,a)=K_L,
Q_o(L,a)=K_L-Q_e(L,a).                                 (5)
```

This is stronger than the generic operator identity `Q_even=T+H`, `Q_odd=T-H`: on the literal
fixed-width boundary ray, the Toeplitz/self-edge contribution is the constant `K_L/2`, while the
entire aperture dependence is parity-antisymmetric.

## False-RH parity oscillation

Let `delta_*` be the right-transverse Xi supremum. Existing source-side Landau theory proves that
under false RH, for every `0<=alpha<delta_*`, every `C>=0`, and every starting index `N_0`, there
are arbitrarily late logarithmic apertures `a_n=(1/2)log n` with

```text
Q_e(L,a_n)> C n^alpha                                  (6+)
```

and arbitrarily late apertures with

```text
Q_e(L,a_n)<-C n^alpha.                                 (6-)
```

Apply `(6+)` with coefficient `C+|K_L|`. Since `n^alpha>=1`, `(5)` gives

```text
Q_o(L,a_n)
 <= |K_L|-(C+|K_L|)n^alpha
 <= -C n^alpha.                                       (7-)
```

Apply `(6-)` with the same enlarged coefficient to obtain

```text
Q_o(L,a_n)
 >= -|K_L|+(C+|K_L|)n^alpha
 >= C n^alpha.                                        (7+)
```

Thus both parity trial energies have cofinal excursions above and below every subcritical
transverse power. Their leading oscillations are forced to be opposite, not merely unrelated.

## Odd restricted-floor amplification

Use inward averaging at both edges, with a plus sign for the even packet and a minus sign for the
odd packet. The odd smoothed packet is continuous, piecewise linear, supported in `[-a,a]`,
vanishes at both endpoints, belongs to `H^1_0(-a,a)`, and is reflection-odd. Its two supports are
disjoint and signs disappear after squaring, so

```text
||h_(o,L,a,epsilon)||_2^2
 =2(L-epsilon/3) -> 2L.                                (8)
```

Its transform is obtained from `(1)` by multiplying the right and left amplitudes by the inward
factors `m_epsilon(w)` and `m_epsilon(-w)`. The same uniform strip majorant as in the even proof
gives dominated convergence of the Xi--Weil polarization:

```text
Q_W^a(h_(o,L,a,epsilon)) -> Q_o(L,a).                  (9)
```

Let `lambda_o(a)` be the bottom of the closed restricted-Weil form on the odd subspace and
`eta_o(a)=max(0,-lambda_o(a))`. Variationality and `(8)--(9)` give the sharp odd bridge

```text
Q_o(L,a)>=2L lambda_o(a),
Q_o(L,a)^-<=2L eta_o(a).                               (10)
```

Combining `(7-)` and `(10)` proves: if RH is false, then for every
`0<=alpha<delta_*`, `C>=0`, and `N_0`, some `n>=N_0` satisfies

```text
eta_o((1/2)log n)>C n^alpha.                            (11)
```

The already formalized symmetric trial gives the same statement for the even floor. Therefore
false RH is not a one-parity instability: both literal Suzuki parity blocks acquire
exponentially deep negative spectra, though generally on different cofinal aperture subsequences.

## What this changes at the Route-G frontier

1. A proof cannot treat the odd block as a harmless comparison channel. False RH forces its own
   exponential floor evacuation.
2. A fixed-width two-edge profile cannot prove the ground-reflection cone by a one-sided parity
   sign: its even and odd energies are exact affine complements and exchange large positive and
   negative excursions.
3. The live Suzuki selector must use information beyond one fixed boundary ray: spectral
   projection geometry, a varying/non-tight boundary profile, or the full measure-level
   credit/debt transport.
4. The theorem does **not** prove that the actual global ground parity alternates. A negative
   trial is only an upper bound for one parity floor; comparison of the two true floors remains
   open. Claiming ground alternation would be theatre.

This advances the literal source problem but does not close Route G. The remaining first source
question is now narrower: compare the two true centered parity spectral measures/floors after both
are known to evacuate exponentially under false RH, then prove or refute the reflection cone or
interior excursion on a source-selected cofinal family.

## Novelty audit

- Suzuki proves parity invariance and constructs the restricted operator, but does not state the
  fixed-width even/odd complementarity trace `(5)` or odd-floor amplification `(11)`.
- Generic parity splitting and the algebraic difference of squares are classical and receive no
  novelty credit.
- The existing project result proves two-sided oscillation only for the symmetric rectangular
  observable and floor amplification only for the unrestricted/even-tested floor. Repository
  searches found no odd two-edge Xi--Weil transform, aperture-independent parity trace, or odd
  restricted-floor amplification theorem.
- Targeted arXiv searches found no paper stating this exact Suzuki/Weil parity consequence. This
  is a priority audit, not independent expert certification.

## Gates

- [x] 0 → 1 in-progress: literal source object, exact proof, Route-G consequence, hostile scope
- [ ] 1 → 2 fully-proven: independent line-by-line paper audit and exact operator-domain wording
- [ ] 2 → 3 formalized: `SuzukiParityTwoEdgeFloorAmplification.lean`, target check, axioms, lint,
  targeted module build, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone article and external novelty review

## Log

- 2026-08-07 — Discovered aperture-independent even/odd trace `(5)` by combining the literal
  symmetric two-edge source with its antisymmetric companion. Derived opposite two-sided
  transverse oscillation and odd-floor amplification without computation or RH assumptions.
