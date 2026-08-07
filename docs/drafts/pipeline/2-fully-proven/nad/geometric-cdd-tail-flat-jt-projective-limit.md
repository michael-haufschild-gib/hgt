# The deep geometric CDD tail has a flat-JT projective limit

- **ID:** `geometric-cdd-tail-flat-jt-projective-limit`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (Lean 4) / QFT-TO-TOPOLOGICAL-GRAVITY BRIDGE / ASYMPTOTIC SOURCE LAW
- **Scientific status:** `[PROVED HERE] [FORMALIZED IN LEAN, AXIOMS CLEAN]`
  `[NOVELTY UNVERIFIED] [SIGNIFICANCE GATE OPEN]`
- **Scope:** general hypertranscendental elastic QFT; no RH or distinguished special-function
  input
- **Parent:** `hausdorff-positive-higher-spin-cdd-cone.md`
- **Statement:** After deleting the first `N` geometric CDD shells and normalizing the remaining
  coupling measure by its total mass, the tail converges to the zero-shell extreme ray.  Its
  higher-spin vector therefore converges to the pure `T bar T` direction and its phase germ
  converges locally uniformly to the flat-JT gravitational dressing.

## Goal

Find an exact, non-metaphorical connection between the geometric HT scattering law and a known
topological-gravity source.  The connection must not claim that ordinary `T bar T` already equals
the HT product: an entire one-spin dressing is differentially algebraic and has no CDD divisor.

The correct statement is projective and asymptotic.  The full q-ladder remains HT, but its deep
large-scale shell tail approaches the `T bar T` ray after the unique normalization supplied by
the positive coupling measure.

## Geometric shell measure

Fix `0<q<1` and `C>1`, and put

```text
B_j=C q^(-j)=cosh(eta_j),
r_j=exp(-eta_j)=B_j-sqrt(B_j^2-1),       0<r_j<1.           (1)
```

The sequence `B_j` is strictly increasing and unbounded, so `r_j` is strictly decreasing to
zero.  The paired-shell phase is

```text
Sigma_j(theta)=4 arctan(sinh(theta)/B_j).                   (2)
```

Its Hausdorff source atom is

```text
nu_j=r_j delta_(r_j^2).                                    (3)
```

The full coupling measure and its tail are

```text
nu=sum_(j>=0) nu_j,
nu_>=N=sum_(j>=N) nu_j,
M_N=nu_>=N([0,1])=sum_(j>=N) r_j.                          (4)
```

The elementary estimate

```text
r_j=1/(B_j+sqrt(B_j^2-1)) <= 1/B_j=q^j/C                  (5)
```

proves that every `M_N` is finite and positive and that `M_N` tends to zero.

## Theorem A -- normalized tail measures collapse to the zero-shell ray `[PROVED]`

Define the probability measure

```text
hat(nu)_N=M_N^(-1) nu_>=N.                                 (6)
```

Its support lies in `[0,r_N^2]`.  Since `r_N` tends to zero, for every continuous function `f`
on `[0,1]`,

```text
|integral f d hat(nu)_N - f(0)|
  <= sup_(0<=y<=r_N^2) |f(y)-f(0)| -> 0.                  (7)
```

Therefore

```text
hat(nu)_N -> delta_0                                      (8)
```

in the weak-star topology of finite measures.

This is not a statistical or numerical limit.  It is forced only by positivity and the nested
support intervals.

## Theorem B -- all normalized higher-spin directions except spin one vanish `[PROVED]`

Let

```text
b_m^(N)=integral y^m d hat(nu)_N(y).                        (9)
```

Then

```text
b_0^(N)=1,
0 <= b_m^(N) <= r_N^(2m) -> 0       for every m>=1.        (10)
```

The normalized odd-spin couplings are

```text
hat(alpha)_(2m+1)^(N)
  = 8 (-1)^m b_m^(N)/(2m+1).                               (11)
```

Consequently

```text
hat(alpha)_1^(N)=8,
hat(alpha)_(2m+1)^(N) -> 0          for every m>=1.        (12)
```

Thus the projective direction of the entire deep tail converges coefficientwise to the unique
spin-one current--current deformation.

## Theorem C -- the normalized phase converges to T bar T / flat JT `[PROVED]`

Let the Hausdorff phase kernel be

```text
K(y,theta)
  = 4/sqrt(y) [arctan(sqrt(y)e^theta)
               - arctan(sqrt(y)e^(-theta))],
K(0,theta)=8 sinh(theta).                                  (13)
```

Define the tail phase and its projective normalization by

```text
Sigma_>=N(theta)=integral K(y,theta) d nu_>=N(y)
               =sum_(j>=N) Sigma_j(theta),

hat(Sigma)_N(theta)=M_N^(-1) Sigma_>=N(theta)
                   =integral K(y,theta) d hat(nu)_N(y).    (14)
```

On every compact rapidity set contained in a fixed neighborhood of the origin, `K(y,theta)` is
jointly continuous down to `y=0` and analytic in `theta`.  Since the support of `hat(nu)_N`
shrinks uniformly to zero, `(7)` applied uniformly in `theta` gives

```text
hat(Sigma)_N(theta) -> 8 sinh(theta)                       (15)
```

locally uniformly.  Hence

```text
exp(i hat(Sigma)_N(theta)) -> exp(i 8 sinh(theta)).         (16)
```

Up to the conventional sign and mass normalization of the coupling, the right side of `(16)` is
the universal `T bar T` CDD phase obtained by coupling the matter theory to flat JT gravity.

The unnormalized statement is different:

```text
Sigma_>=N(theta) -> 0,
exp(i Sigma_>=N(theta)) -> 1.                              (17)
```

Thus the tail becomes weak in absolute size while its **projective shape** converges to the
topological-gravity direction.

## Universal form -- the zero-shell attractor does not see the geometric law `[PROVED]`

Theorems A--C use nothing about `q` and `C`.  Call `(w_j, y_j)_{j >= 0}` a **positive Hausdorff
shell family** when

```text
w_j>0,  sum_j w_j<infinity,
0<=y_j<=1,  y antitone,  y_j -> 0.                          (U1)
```

Then, with `M_N=sum_{j>=N} w_j`, `nu_>=N=sum_{j>=N} w_j delta_{y_j}` and
`hat(nu)_N=M_N^{-1} nu_>=N`:

```text
hat(nu)_N -> delta_0 weak-star,
b_0^{(N)}=1,  0<=b_m^{(N)}<=y_N^m -> 0   (m>=1),
|hat(Sigma)_N(theta)-8 sinh(theta)| <= (8/3) y_N cosh(3 theta),
Sigma_>=N(theta) -> 0.                                      (U2)
```

The geometric family is the instance `w_j=r_j`, `y_j=r_j^2`; `(5)` and the strict decrease of
`r_j` are exactly the verification of `(U1)`.  The estimate in `(U2)` is *sharper* than the
qualitative statement in Theorem C: it exhibits an explicit modulus, linear in the deepest
surviving source point and exponential in the rapidity window.

Thus the zero-shell projective attractor is a property of nested shrinking positive shell supports,
not of the `q`-ladder.  Any positive Hausdorff CDD divisor whose shells accumulate only at `y=0`
has the same flat-JT tangent ray.

## Exact relation to the q-boundary product

The tail interaction factor is also

```text
P_>=N(t)
  = product_(j>=N) ((1-q^j t)/(1+q^j t))^2
  = P_q(q^N t).                                            (18)
```

Equation `(18)` is the exact decimation orbit of the affine q-boundary constraint.  Equations
`(8)`--`(16)` identify its tangent direction at the trivial endpoint: after normalization by the
positive first coupling, the orbit approaches flat-JT dressing.

This does **not** identify `q^N` with a physical RG time.  It is a theorem about nested divisor
tails and their coupling-measure geometry.

## Physical interpretation

The geometric HT completion has three simultaneous layers:

```text
each finite shell:             rational/DA paired CDD factor,
projectively normalized tail:  T bar T / flat-JT direction,
full one-sided completion:     hypertranscendental.         (19)
```

Hypertranscendence is therefore not present in the elementary shell or in the projective tail
fixed ray.  It lives in the global boundary completion that assembles all finite scales while
retaining the infrared endpoint.

The theorem gives a precise QFT interpretation of the founding constraint principle.  Ordinary
topological gravitational dressing is the asymptotic tangent of the shell constraint, while the
HT object records the nontrivial global integration of that constraint across all scales.

## What is not proved

1. No flat-JT action for the full geometric measure has been constructed.
2. The normalized phase in `(16)` is a projective local germ.  Since the normalization changes
   atomic multiplicities continuously, it need not be a globally meromorphic CDD product for
   finite `N`.
3. No Wilsonian RG flow, ultraviolet fixed point, or continuum scaling limit is asserted.
4. The result does not prove that all positive Hausdorff CDD measures have a JT-type microscopic
   realization.
5. The result does not make the full HT phase differentially algebraic; the limit and the global
   completion have different differential-algebraic types.

## Anti-theatre and novelty gate

Parent results:

- ordinary `T bar T` multiplies the S-matrix by an exponential `sinh(theta)` CDD phase;
- that phase has a flat-JT topological-gravity construction;
- limits of repeated elementary CDD factors can yield the ordinary `T bar T` exponential;
- Hausdorff moment measures and weak convergence on a compact interval are classical.

The new candidate is not the statement that CDD factors approximate an exponential.  It is the
canonical, source-positive tail theorem `(6)`--`(16)` for the geometric HT divisor: normalization
by its own total coupling mass forces weak convergence to the zero-shell measure, annihilates
every higher-spin direction, and selects the flat-JT ray.

Focused searches in the generalized `T bar T`, CDD, and topological-gravity literature found the
known repeated-identical-factor limit but not this geometric-tail/Hausdorff-measure statement.
That is negative evidence, not a completed novelty proof.

The theorem is significant because it supplies an exact QFT--topological-gravity bridge without
collapsing the HT completion to ordinary `T bar T`.  It becomes Fields/Nobel-scale only if a
positive functor integrates the entire source measure and explains why the q-boundary law selects
this one-sided completion.

## Lean status

Three modules, all with `#print axioms` equal to `[propext, Classical.choice, Quot.sound]`:

| Module | Content |
|---|---|
| `HTGeometry/HausdorffCDDPhaseKernel.lean` | cubic arctangent control and the phase kernel `(13)` |
| `HTGeometry/HausdorffShellTailProjectiveAttractor.lean` | the **universal** law `(U1)`–`(U2)` |
| `HTGeometry/GeometricCDDTailProjectiveLimit.lean` | the geometric shell geometry and the instance |

The universal module carries Theorems A, B, C and `(17)` for an arbitrary `PositiveShellFamily`:
`tendsto_shellTailProbability_diracProba`, `tendsto_integral_shellNormalizedTailMeasure`,
`shellTailMoment_zero`/`_nonneg`/`_le`, `tendsto_shellTailMoment`,
`shellNormalizedSpinCoupling_zero`, `tendsto_shellNormalizedSpinCoupling`,
`abs_shellNormalizedTailPhase_sub_flat_le`, `tendsto_shellNormalizedTailPhase`,
`tendstoUniformlyOn_shellNormalizedTailPhase`, `tendsto_exp_shellNormalizedTailPhase`,
`abs_shellTailPhase_le`, `tendsto_shellTailPhase`, `tendsto_exp_shellTailPhase`, together with the
measure-level bridges `shellNormalizedTailMeasure_eq_smul`, `integral_pow_...`,
`integral_cddPhaseKernel_...`.

`positiveShellFamily_cddShellRadius` is the single verification `(U1)` for the geometric divisor;
every geometric statement below is its instance.  Everything is unconditional for
`0 < q < 1`, `C > 1`.

Shell geometry `(1)`–`(5)`:

- `cddShellThreshold`, `cddShellRadius`, `cddShellConjugate` — `B_j = C q^{-j}`,
  `r_j = B_j − sqrt(B_j² − 1)`, `B_j + sqrt(B_j² − 1)`;
- `one_lt_cddShellThreshold`, `cddShellThreshold_strictMono`, `tendsto_cddShellThreshold_atTop` —
  `B_j > 1`, strictly increasing, unbounded;
- `cddShellRadius_pos`, `cddShellRadius_lt_one`, `cddShellRadius_strictAnti`,
  `tendsto_cddShellRadius` — `0 < r_j < 1`, strictly decreasing to zero;
- `cddShellRadius_mul_conjugate` (`r_j (B_j + sqrt(B_j²−1)) = 1`) and
  `one_add_cddShellRadius_sq` (`1 + r_j² = 2 B_j r_j`, i.e. `B_j = cosh η_j`, `r_j = exp(−η_j)`);
- `cddShellRadius_le_pow_div` — the estimate `(5)`, `r_j ≤ q^j/C`;
- `cddTailMass`, `cddTailMass_pos`, `cddTailMass_le`, `tendsto_cddTailMass` — `M_N` finite,
  positive, and `M_N ≤ q^N/(C(1−q)) → 0`.

Measures `(3)`, `(4)`, `(6)`:

- `cddTailMeasure = ∑_{j ≥ N} r_j δ_{r_j²}` as a `Measure ℝ` (built from the corpus
  `HTGeometry.countableWeightedDirac`), with `cddTailMeasure_univ = ofReal M_N`;
- `cddNormalizedTailMeasure`, `cddNormalizedTailMeasure_eq_smul` (`ν̂_N = M_N⁻¹ ν_{≥N}`),
  `isProbabilityMeasure_cddNormalizedTailMeasure`, and the bundled `cddTailProbability`.

**Theorem A** `(7)`–`(8)`:

- `cddNormalizedTailMeasure_compl_Icc` — `ν̂_N` is carried by `[0, r_N²]`;
- `tendsto_integral_cddNormalizedTailMeasure` — `∫ f dν̂_N → f(0)` for every continuous `f`;
- `tendsto_cddTailProbability_diracProba` — `ν̂_N → δ_0` in the weak topology on
  `ProbabilityMeasure ℝ`.

**Theorem B** `(9)`–`(12)`:

- `cddTailMoment`, `integral_pow_cddNormalizedTailMeasure` (`b_m^{(N)} = ∫ y^m dν̂_N`);
- `cddTailMoment_zero` (`b_0 = 1`), `cddTailMoment_nonneg`, `cddTailMoment_le`
  (`b_m ≤ r_N^{2m}`), `tendsto_cddTailMoment` (`b_m → 0` for `m ≥ 1`);
- `cddNormalizedSpinCoupling` with `cddNormalizedSpinCoupling_zero = 8` and
  `tendsto_cddNormalizedSpinCoupling` — every higher-spin direction collapses, the spin-one
  direction is fixed at `8`.

**Theorem C** `(13)`–`(16)`:

- `cddPhaseKernel` — the kernel `(13)` with its zero-shell value `8 sinh θ`;
- `arctan_sub_arctan_exp` and `cddShellRadius_mul_cddPhaseKernel` — the exact shell identity
  `r_j K(r_j²,θ) = 4 arctan(q^j sinh θ / C)`, i.e. the `j`-th summand of the corpus
  `geometricCDDTruncationPhase`;
- `abs_cddPhaseKernel_sub_flat_le` — the explicit modulus `|K(y,θ) − 8 sinh θ| ≤ (8/3)|y| cosh 3θ`,
  proved from the new cubic arctangent control `sub_arctan_le_cube_div_three` /
  `abs_arctan_sub_self_le_cube`; hence `continuous_cddPhaseKernel`;
- `cddNormalizedTailPhase`, `integral_cddPhaseKernel_cddNormalizedTailMeasure` (`(14)`);
- `abs_cddNormalizedTailPhase_sub_flat_le` — the sharp estimate
  `|Σ̂_N(θ) − 8 sinh θ| ≤ (8/3) r_N² cosh 3θ`;
- `tendsto_cddNormalizedTailPhase` and `tendstoUniformlyOn_cddNormalizedTailPhase` — `(15)`,
  locally uniform on every window `[−T,T]`;
- `tendsto_exp_cddNormalizedTailPhase` — `(16)`, `exp(i Σ̂_N) → exp(8 i sinh θ)`.

Unnormalized statement `(17)`:

- `cddTailPhase`, `cddTailPhase_eq_shellSum`, `abs_cddTailPhase_le`, `tendsto_cddTailPhase`,
  `tendsto_exp_cddTailPhase`;
- `geometricCDDTruncationPhase_add_sub` and `tendsto_geometricCDDTruncationPhase_sub` tie
  `Σ_{≥N}` to the corpus finite CDD phase as its deleted-shell increment.

Decimation `(18)`:

- `geometricCDDStep_add_eq_scale` and `geometricCDDTail_prod_eq` —
  `∏_{k<M} step_q(t, N+k) = P_q(q^N t)` at every finite depth, on the corpus `geometricCDDStep`.

Connector to the parent Hausdorff cone:

- `cddTailFiniteCoupling_completelyMonotone` places every finite shell truncation of the
  normalized tail coupling sequence in the completely monotone cone of
  `HausdorffPositiveCddCone.cddCoupling_completelyMonotone`.

Reusable infrastructure added to `HTGeometry/CountableWeightedDirac.lean`:
`countableWeightedDirac_univ_ofReal`, `integrable_countableWeightedDirac`,
`integral_countableWeightedDirac`, `countableWeightedDirac_const_mul`.

Still outside Lean: the identification of `exp(8 i sinh θ)` with the flat-JT gravitational
dressing, which is a physics interface statement rather than a mathematical assertion, and the
open gates below.

## Primary literature

- F. A. Smirnov and A. B. Zamolodchikov, *On space of integrable quantum field theories*,
  <https://arxiv.org/abs/1608.05499>.
- S. Dubovsky, V. Gorbenko, and G. Hernandez-Chifflet, *T bar T Partition Function from
  Topological Gravity*, <https://arxiv.org/abs/1805.07386>.
- G. Hernandez-Chifflet, S. Negro, and A. Sfondrini, *Flow equations for generalised T bar T
  deformations*, <https://arxiv.org/abs/1911.12233>.
- F. Hausdorff, *Summationsmethoden und Momentfolgen I*,
  <https://doi.org/10.1007/BF01378337>.

## Gates

- [x] tail measure finite and positive
- [x] normalized tail weak-star convergence proved
- [x] coefficientwise collapse to the spin-one direction proved
- [x] locally uniform phase-kernel convergence proved
- [x] flat-JT / ordinary T bar T endpoint identified at source level
- [x] projective limit separated from literal global meromorphic products and Wilsonian RG
- [x] Theorem A formalized in Lean (`tendsto_cddTailProbability_diracProba`,
  `tendsto_integral_cddNormalizedTailMeasure`)
- [x] Theorem B formalized in Lean (`cddTailMoment_le`, `tendsto_cddTailMoment`,
  `cddNormalizedSpinCoupling_zero`, `tendsto_cddNormalizedSpinCoupling`)
- [x] Theorem C formalized in Lean (`abs_cddNormalizedTailPhase_sub_flat_le`,
  `tendstoUniformlyOn_cddNormalizedTailPhase`, `tendsto_exp_cddNormalizedTailPhase`)
- [x] unnormalized triviality `(17)` and decimation identity `(18)` formalized in Lean
- [x] axiom audit (`[propext, Classical.choice, Quot.sound]`)
- [x] universality theorem for the zero-shell projective attractor beyond the geometric family
  (`PositiveShellFamily` + the whole `shell*` law; the geometric case is
  `positiveShellFamily_cddShellRadius`)
- [ ] formula-level specialist novelty audit
- [ ] positive action or operator-flow integration of the full geometric measure

## Log

- 2026-07-26 -- Theorems A, B, C together with `(17)` and `(18)` formalized unconditionally in
  `GaloisForLFunctions.HTGeometry.GeometricCDDTailProjectiveLimit`.  The two pieces of
  infrastructure that were genuinely missing are (i) cubic Taylor control of the arctangent,
  `|arctan t − t| ≤ |t|³/3`, which yields the sharp kernel modulus
  `|K(y,θ) − 8 sinh θ| ≤ (8/3)|y| cosh 3θ` and hence continuity of the Hausdorff phase kernel down
  to the zero shell, and (ii) Bochner integration against a countable weighted Dirac family, added
  to `HTGeometry/CountableWeightedDirac.lean`.  Everything else reuses the existing corpus: the
  atomic measure `countableWeightedDirac`, the weak-convergence criterion
  `tendsto_diracProba_of_eventually_measure_nhds_eq_one`, the shell phase inside
  `geometricCDDTruncationPhase`, the factor `geometricCDDStep`, and the Hausdorff positivity cone.
  Axioms clean; module builds and is wired into the `HTGeometry` umbrella.
- 2026-07-26 -- Open gate "universality beyond the geometric family" closed. The three theorems were
  re-proved for an arbitrary positive Hausdorff shell family `(U1)` in
  `GaloisForLFunctions.HTGeometry.HausdorffShellTailProjectiveAttractor`, and the geometric case is
  now literally the instance `positiveShellFamily_cddShellRadius`, so no statement is proved twice.
  The phase kernel and the cubic arctangent control were split into
  `GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel`, which both modules import. The
  universal estimate `|Sigma_N - 8 sinh| <= (8/3) y_N cosh(3 theta)` is strictly sharper than the
  original Theorem C, since it names the modulus. Axioms clean on all three modules; the
  `HTGeometry` umbrella builds green.
