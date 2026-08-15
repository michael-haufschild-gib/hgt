# CCM cofinal Weil spectral-floor criterion

- **ID:** `ccm-cofinal-weil-spectral-floor-criterion`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Weil's positivity criterion and the min--max principle
- **Statement:** Convergence of the bottom of the continuous restricted Weil form to zero along
  any cofinal aperture sequence already implies RH. If RH is false, one compactly supported
  negative test keeps every later spectral floor uniformly below zero.

## Setup

Let `D_lambda` be the form domain of the Weil form restricted to

```text
H_lambda=L2([lambda^(-1),lambda],d*u),
```

with the spaces embedded by zero extension. Put

```text
epsilon(lambda)
 =inf{QW(f,f): f in D_lambda, ||f||_2=1}.              (1)
```

The CCM compact-resolvent theorem identifies `epsilon(lambda)` with the lowest eigenvalue of the
continuous restricted Weil operator.

## Theorem

If there is a cofinal sequence `lambda_j->infinity` such that

```text
epsilon(lambda_j)->0,                                  (2)
```

then RH holds.

Equivalently, if RH is false, there are `lambda_0>1` and `delta>0` such that

```text
epsilon(lambda)<=-delta   for every lambda>=lambda_0.  (3)
```

### Proof

Fix any compactly supported Weil test `f`. For all sufficiently large `j`, its support lies in the
`lambda_j` aperture. The variational definition `(1)` gives

```text
QW(f,f)>=epsilon(lambda_j)||f||_2^2.
```

Letting `j->infinity` and using `(2)` proves `QW(f,f)>=0`. Since this holds for every test in the
Weil criterion, RH follows.

Conversely, if RH is false, Weil's criterion supplies a compactly supported test `f` with
`QW(f,f)<0`. Choose `lambda_0` containing its support and put

```text
delta=-QW(f,f)/||f||_2^2>0.
```

The same vector is admissible in every later aperture, so `(1)` gives `(3)`.

## Exact consequence for the prolate comparison

Let `d_1(lambda)` be the positive fixed-mode prolate concentration deficit from
`constrained-prolate-two-mode-ground-state.md`; Fuchs asymptotics give `d_1(lambda)->0`. Any theorem
of the form

```text
epsilon(lambda)=c d_1(lambda)+o(d_1(lambda))           (4)
```

on a cofinal sequence, for any finite real constant `c`, proves RH immediately by `(2)`. The same
is true of an absolute estimate `epsilon(lambda)=o(1)`.

This separates two CCM completion branches.

```text
spectral-floor branch:
  epsilon(lambda_j)->0
  => cofinal Weil positivity
  => RH;

determinant branch:
  projective true-ground/prolate comparison at the growing Mellin rate
  => locally uniform normalized determinants carrying the Xi divisor
  => RH.
```

The determinant branch is completed by a cofinal divisor-carrying limit. The spectral-floor branch
is completed by cofinal Weil positivity. These are the two positive global certificates attached to
the CCM comparison.

## Route consequence

The source-specific Schur--Feshbach problem should no longer be described as a harmless preliminary
spectral estimate. If it transfers the positive constrained-prolate floor to the **true** Weil
floor with even an `o(1)` absolute error, it has already proved RH. The stronger eigenvector rate
needed for Mellin determinant convergence is only necessary if the argument does not control the
true floor itself.

In particular:

- `[RH-SUFFICIENT CORE]` Prove `(4)` or merely `(2)`.
- `[ALTERNATIVE RH-SUFFICIENT CORE]` Prove the projective ground-vector rate and locally uniform
  determinant convergence to `Xi`.
- `[REQUIRED COFINAL CERTIFICATE]` Supply either the spectral-floor limit or the locally uniform
  divisor-carrying determinant limit in addition to finite real zeros.

## Novelty and significance verdict

The theorem is the nested-aperture form of Weil's classical positivity criterion and follows in one
line from the variational definition. It is not new scientific knowledge. Its value is route
discipline: it shows exactly when a proposed prolate-to-Weil eigenvalue comparison has silently
absorbed the whole RH burden and when divisor-preserving determinant convergence is still needed.

## References

- A. Weil, *Sur les formules explicites de la theorie des nombres premiers*, 1952.
- E. Bombieri, *The Riemann hypothesis -- official problem description*, Clay Mathematics
  Institute.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean status

**Superseded, 2026-08-03.**  Both proved halves of the criterion are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMCofinalFloorCriterion.lean`, on the nested-floor layer of
`CCMNestedFloorNoEvacuation.lean`.

The previous objection was that there is "no exhaustion by CCM apertures".  The exhaustion is
supplied by representing the aperture domains as subsets of one fixed function space,
`apertureDomain a = {v | ∀ x, v x ≠ 0 → x ∈ (-a, a)}`, so zero extension is literal inclusion and a
compactly supported test lies in every later aperture by `apertureDomain_mono`.

- **`nonneg_of_rayleighFloor_tendsto_zero`** — equation `(2)`: if the floor tends to zero along any
  apertures tending to infinity, then the energy is nonnegative on every trial domain.  This is the
  variational argument of the card, and it needs the nonemptiness of the trial set only at the one
  aperture where the conclusion is drawn.
- **`exists_uniform_negative_rayleighFloor`** — equation `(3)`: one trial vector with negative energy
  produces an explicit `δ = -QW(f,f)/||f||²  > 0` with `epsilon(lambda) ≤ -δ` for every later
  aperture.
- `diffBilinForm_nonneg_of_restrictedKernelFloor_tendsto_zero` and
  `exists_uniform_negative_restrictedKernelFloor` — the same two statements for the concrete
  restricted kernel form `QW(v,v) = diffBilinForm K v v` with mass `sqMass v = ∫ v²`, whose trial set
  is proved nonempty at every positive aperture by a bump function.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and not a theorem of this card: Weil's criterion itself (the equivalence between
positivity of `QW` on all admissible tests and RH), and the CCM compact-resolvent identification of
`epsilon(lambda)` with a lowest eigenvalue.  The Lean statements deliver exactly the variational
content — "cofinal floor limit zero implies form positivity", and its quantitative converse — with
the RH translation left where the card leaves it, in Weil's criterion.

## Gates

- [x] cofinal spectral-floor criterion proved
- [x] quantitative `not RH` alternative proved
- [x] determinant and spectral-floor branches separated
- [x] Lean: cofinal criterion `(2)` and quantitative alternative `(3)` unconditional
- [x] Lean: both instantiated on the restricted kernel form with a nonempty trial set
- [ ] prove the true CCM floor tends to zero, or prove divisor-preserving determinant convergence
