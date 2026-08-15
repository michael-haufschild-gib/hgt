# Coherent Euler-logarithm square exclusion — formalized closure

- **ID:** `ccm-coherent-euler-logarithm-square-exclusion-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-coherent-euler-logarithm-square-exclusion-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCMCoherentSquareExclusion`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(7)`–`(8)` | `fwdShift`, `bwdShift`, `bwdShift_eq_zero_of_support`, `fwdShift_mul_eq_zero`, `integral_fwdShift_mul_eq_zero`, `commutatorForm_eq_zero` | on a packet supported in `(0,δ)` with every shift at least `δ`, the backward shift annihilates the packet and the forward shift leaves its support, so the prime commutator form `(4)` is identically zero on the packet. The integrand is pointwise zero, so no measure theory beyond `integral_zero` is used |
| `(15)` | `star_combo_expand` | for self-adjoint `X` and skew-adjoint `Z`, `star(X-Z)(X-Z) = X² - [X,Z] + (star Z)Z`; with `star_smul_selfAdjoint`/`star_smul_skewAdjoint` this gives the balanced identity for `a•X`, `b•Z` |
| `(5)`–`(6)` | `BoundaryPacket`, `tentPacket`, `boundaryPacket_tentPacket` | the packet class is inhabited at every width, so nothing downstream is vacuous |
| `(2)` at exponent one | `primeChannel`, `eulerShellApply`, `eulerShellApply_eq_sum_primeChannel` | inside a large enough aperture the shell is exactly the sum of the translates, so the aperture cutoff is invisible to the packet |
| arithmetic input | `primeReciprocalSum`, `tendsto_primeReciprocalSum_atTop` | Euler's `∑ 1/p = ∞` — the only arithmetic input |
| channel mass | `integral_sq_primeChannel` | the mass of one channel is `1/p` times the packet mass, by translation invariance; no hypothesis on the packet |
| `(12)`–`(14)` | `primeReciprocalSum_mul_mass_le` | the coherent energy dominates its own diagonal, because the packet is nonnegative and every Euler coefficient is positive |
| divergence | `tendsto_energy_atTop`, `tendsto_energy_atTop_natAperture` | the coherent energy diverges along every aperture schedule keeping the visible shifts inside the aperture; `A = N + δ` is such a schedule |
| `(16)`, fixed factor | `positionApply_mass_pos` | the position energy is positive and aperture-independent |
| `(7)` as orthogonality | `positionApply_mul_primeChannel_eq_zero`, `integral_positionApply_mul_eulerShellApply` | exact orthogonality of the two outputs. This is the only place `δ ≤ log 2` of `(5)` is used |
| `(16)` | `integral_sq_sub_of_orthogonal`, `two_mul_sqrt_mul_sqrt_le` | the mixed square splits exactly on orthogonal outputs, and no balancing scalar brings the split below twice the geometric mean of the two energies |
| `(17)`–`(19)` | `not_exists_coherent_square_packet` | the exclusion in the concrete model: `2√X √Z_N → ∞` while `q_N` is constant |
| `(17)`–`(19)`, abstract | `not_exists_coherent_square`, `not_exists_coherent_square_of_divergence` | the same conclusion in an arbitrary real inner-product space, so it applies to any other realization of the two outputs |

## Strengthening relative to the card

The card derives `(14)` from the prime-counting bound `#P_A ≥ c_δ e^A/A`. The exclusion consumes only
divergence of the coherent energy, and that follows from Euler's `∑ 1/p = ∞` with no prime-counting
rate. The prime number theorem is therefore recorded as a sharpening, not as an input.

## Axioms

`#print axioms` on every theorem returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

Not needed for the exclusion, and open route content of the card: identification of `(2)` as the
unitary image of the weighted skew Euler logarithm, the commutator computation `(4)` for the actual
operators, transport of the completed archimedean form `q_arch` to the unweighted carrier `(18)`, the
PNT rate `(13)`–`(14)`, and the channel-resolution alternatives `(20)`–`(22)`.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
