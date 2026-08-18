# Suzuki's screw characteristic limit must be meromorphic, not entire-compact

- **ID:** `suzuki-screw-characteristic-meromorphic-limit-correction`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / ROUTE CORRECTION / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096, Corollary 1.6.
- **Statement:** The proposed convergence to `z^2 xi(1/2-iz)/xi'(1/2-iz)` cannot hold as ordinary
  uniform convergence on every compact subset of `C`, because the target has an unconditional real
  pole. The meaningful repair is meromorphic convergence on compacta avoiding the pole set, or an
  explicitly spherical formulation with an admissible normalization.

## Source statement

Suzuki constructs, for every aperture `a>0` and extension angle `theta`, an entire characteristic
function `W(a,theta;z)` whose zeros are the simple real spectrum of a self-adjoint extension. The
paper's Corollary 1.6 assumes that one can choose `theta=theta(a)` and a finite exponential
normalization so that

```text
exp(phi(a,z)) W(a,theta;z)
  -> z^2 xi(1/2-iz)/xi'(1/2-iz)                            (1)
```

uniformly on every compact subset of `C`.

## The target has a pole `[PROVED]`

Put

```text
X(z)=xi(1/2-iz).                                           (2)
```

The function `X` is real-valued on the real axis. Hardy's theorem supplies infinitely many distinct
positive real zeros of `X`. Choose two consecutive distinct positive real zeros `gamma_1<gamma_2`.
Then `X` is nonzero on `(gamma_1,gamma_2)`. Rolle's theorem gives a point

```text
c in (gamma_1,gamma_2) with X'(c)=0.                       (3)
```

Because `X(c)!=0` and `c>0`, and because

```text
X'(c)=-i xi'(1/2-ic),                                     (4)
```

the function

```text
R(z)=z^2 xi(1/2-iz)/xi'(1/2-iz)                           (5)
```

has a pole at `c`; the factor `z^2` does not cancel it.

## Consequence for the stated limit

Under the ordinary meaning of uniform convergence of complex-valued functions on compact sets, the
right side of `(1)` must be finite and continuous on every such compact set. Equation `(5)` is not
even complex-valued at the compact point `{c}`. If the normalizing factor is holomorphic and
nonvanishing, the left side is entire and any ordinary locally uniform limit would in addition be
entire by Weierstrass's theorem. Either reading contradicts the pole at `c`.

Therefore Corollary 1.6's convergence hypothesis is impossible as written in the ordinary
entire-compact topology.

## Corrected route boundary

The natural corrected target is one of:

```text
locally uniform convergence on compact subsets of C\Pole(R),          (6)
```

with a specified holomorphic nonvanishing normalization, or a precisely stated spherical
meromorphic convergence theorem that controls both zeros and poles.

The corrected meromorphic version would still imply RH. If `z_0` is any off-real zero of `X` of
multiplicity `m>=1`, then `X/X'` has a simple zero at `z_0`, including when `X'` shares the zero.
The point is not a pole of `R`. Locally uniform convergence in a small pole-free disc and Hurwitz's
theorem would force zeros of the real-zero characteristic functions near `z_0`, impossible.

Thus the correction does not kill Suzuki's self-adjoint-extension lane. It changes its analytic gate
from an impossible entire limit to a meromorphic zero-and-pole convergence theorem. No such theorem
is proved in the source.

## Relationship to CCM

This issue does not apply to the primary CCM ground-determinant target

```text
normalized det_reg(D_lambda-z) -> Xi(z),                  (7)
```

because `Xi` is entire. The CCM lane remains governed by
`ccm-growing-aperture-mellin-determinant-transfer.md`: continuous large-aperture simple-evenness and
projective ground-vector comparison in the growing Mellin topology.

## Novelty verdict

The proof is Rolle's theorem plus the elementary fact that an ordinary locally uniform limit of
entire functions is entire. It is a necessary source correction but not new scientific knowledge.

## Lean formalization

Modules: `formal/GaloisForLFunctions/RHTower/SuzukiCharacteristicEntireLimitNoGo.lean` (already in
the tree) and `formal/GaloisForLFunctions/RHTower/SuzukiCharacteristicMeromorphicLimit.lean` (new).

| Card statement | Lean declaration |
|---|---|
| a critical point with `X ≠ 0` is a pole of `R` | `RHTower.not_analyticAt_suzukiXiCharacteristicTarget_of_deriv_eq_zero` |
| two distinct positive real `X`-zeros force such a point (Rolle) | `RHTower.exists_pole_suzukiXiCharacteristicTarget_of_two_positive_real_XiC_zeros` |
| the ordinary all-compact convergence is impossible | `RHTower.not_suzukiXiCharacteristicLimitWall`, `RHTower.not_suzukiHolomorphicGaugeCharacteristicLimitWall` |
| under RH the target is not entire | `RHTower.not_analyticOnNhd_suzukiXiCharacteristicTarget_of_riemannHypothesis` |
| the corrected topology `(6)` | `RHTower.SuzukiXiMeromorphicCharacteristicLimitWall` |
| the corrected limit still implies RH | `RHTower.suzukiXiMeromorphicCharacteristicLimitWall_implies_riemannHypothesis` |
| Hurwitz existence on a pole-free disc | `RHTower.eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn`, `RHTower.mem_closed_of_tendstoLocallyUniformlyOn` |

Two remarks on the pole gate.  First, the *conclusion* the card draws from the pole — impossibility
of the entire-compact limit — is Lean-certified unconditionally, by a route that does not use
Hardy's theorem at all: the wall implies RH, RH supplies two distinct positive real centered zeros,
Rolle supplies the critical point, and the pole contradicts the wall's own analyticity clause.
Second, the literal statement "the target has an unconditional real pole" is Lean-certified as the
implication from its classical supply: `Hardy's theorem → two distinct positive real zeros →`
`exists_pole_suzukiXiCharacteristicTarget_of_two_positive_real_XiC_zeros`.  Hardy's theorem itself
(infinitely many real zeros of `ξ(1/2+it)`) is neither in mathlib nor in this tree; it is the only
step of this card's paper proof that is not Lean-internal, and no conclusion of the card depends on
it.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every declaration above.

## Gates

- [x] unconditional pole of the proposed target proved
- [x] ordinary all-compact convergence refuted
- [x] corrected meromorphic topology stated
- [x] corrected implication to RH checked at multiple zeros
- [x] separation from the CCM entire-determinant lane recorded
- [x] 2 -> 3: formalized; see `## Lean formalization`
- [ ] Lean proof of Hardy's theorem (the classical supply for the literal pole statement)
- [ ] meromorphic convergence on pole-free compacta
- [ ] RH
