# Leaf-reflection Bohr projection catastrophe

- **ID:** `leaf-reflection-bohr-projection-catastrophe`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/rhtower_status_constraint_1107.md` · §3
- **Statement:** For an irrational two-base one-sided flank carrier, every nonzero transverse Bohr mode forces the corresponding exact-period Cesàro projectors to be nonnormal on every connected domain joining the two reflected flanks.

## Goal

Replace the unsupported continued-fraction guess in the leaf-intrinsic reflection-rigidity cell by
an exact obstruction.  The theorem must identify what fails when a bivariate power-series germ
continues only along the dense exponential leaf, without assuming a transverse torus extension or
installing a growth bound.

The result is not itself an RH route.  It is a constraint-side diagnostic for the independent
two-base weld problem.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, narrow build green, lint green
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, literature verdict

## Exact setting

Let `α, β, w > 0` with `β/α ∉ ℚ`.  Let `G : ℂ → ℂ` be entire and even.  Suppose that on
`Im z ≤ -w`,

\[
G(z)=\sum_{m,n\ge 0} b_{m,n}e^{-iz(m\alpha+n\beta)},
\qquad
\sum_{m,n\ge0}|b_{m,n}|e^{-w(m\alpha+n\beta)}<\infty.
\]

Put `Tα = 2π/α` and `θ = 2πβ/α`.  For `r ≥ 0`, define the exact-period transverse projector

\[
P_{r,N}G(z)=\frac1N\sum_{k=0}^{N-1}e^{ikr\theta}G(z+kT_\alpha).
\]

This is a static spectral projection sequence.  Translation is used only to extract a boundary
character; no parameter propagates `G` or defines the carrier.

## Theorem candidate

`[PROVED HERE — paper, novelty unverified]` Fix `r ≥ 1`.  If the slice

\[
B_r(z)=\sum_{m\ge0}b_{m,r}e^{-iz(m\alpha+r\beta)}
\]

is nonzero, then `{P_{r,N}G}` is not locally bounded on any connected open set meeting both
`{Im z < -w}` and `{Im z > w}`.  Equivalently, the normality domains containing the two flanks
are distinct, and their complement is an intrinsic seam separator.

### Proof

On the lower flank, absolute convergence permits termwise Cesàro averaging.  The `(m,n)` term
acquires the factor

\[
\frac1N\sum_{k=0}^{N-1}e^{ik(r-n)\theta}.
\]

Because `θ/(2π)=β/α` is irrational, this tends to `1` for `n=r` and to `0` otherwise.  Dominated
convergence gives locally uniform convergence `P_{r,N}G → B_r` on `Im z < -w`.

On the upper flank, evenness gives

\[
G(z+kT_\alpha)=G(-z-kT_\alpha).
\]

The reflected point lies on the lower flank, and the `(m,n)` term now acquires

\[
\frac1N\sum_{k=0}^{N-1}e^{ik(r+n)\theta}.
\]

For `r ≥ 1` and `n ≥ 0`, irrationality makes every such mean tend to `0`.  Hence
`P_{r,N}G → 0` locally uniformly on `Im z > w`.

If the projector family were locally bounded on a connected open `U` meeting both flanks,
Montel plus the identity theorem would give a holomorphic subsequential limit on `U`.  Its lower
open piece would equal `B_r`, while its upper open piece would be zero.  The identity theorem would
force `B_r = 0`, contrary to the hypothesis.  Therefore the family is nonnormal across every such
`U`.  The slice is nonzero whenever some `b_{m,r}` is nonzero, by uniqueness of absolutely
convergent generalized Dirichlet coefficients.  ∎

## Consequences

1. `[PROVED HERE — paper]` Any hypothetical nonconstant two-base weld has a nonzero transverse
   slice.  If all `r ≥ 1` slices vanished, the spectrum would lie in `αℕ`, and the existing
   periodic-spectrum rigidity theorem would make `G` constant.
2. `[PROVED HERE — paper]` Analytic continuation along the leaf and transverse Bohr projection do
   not commute for a hypothetical counterexample.  The exact obstruction is nonnormality of the
   projection sequence, not failure of coefficient recovery on either flank.
3. `[PROVED HERE — paper]` The qualitative obstruction uses only irrationality.  Continued-fraction
   rates affect convergence speed but do not enter the existence of the seam separator.  The guess
   “rigid iff partial quotients are unbounded” has no support from return-time arguments alone.
4. `[CONJECTURE]` The nonnormality locus of a nonzero transverse projector contains a closed
   connected left-to-right seam wall.  This should follow from planar separation applied to the
   open normality set, but the exact unbounded-component statement still needs a careful topology
   proof.

## Attack and scientific verdict

- **Degenerate boundary:** if `β/α ∈ ℚ`, a common exact period exists and periodic-spectrum
  rigidity closes the carrier.  There is no projection mismatch.
- **Finite torus model:** transverse entire extension makes the projectors locally bounded, so the
  theorem kills every nonzero transverse slice, recovering the previously proved torus rigidity.
- **Loud leaf-only model:** arbitrary seam growth can support projector nonnormality, so the theorem
  does not by itself contradict a leaf-intrinsic weld.
- **Parent-theory reduction:** after erasing project language, the proof is geometric Cesàro
  orthogonality plus Montel and the identity theorem.  It is therefore a useful `[BRIDGE]`, not yet
  candidate new scientific knowledge under the scientific-novelty gate.
- **RH gate:** the obstruction neither distinguishes the zeta divisor nor supplies a source-pure RH
  localization mechanism.  It cannot be promoted as an RH route.

## Open core

`[OPEN CORE]` Prove or refute existence of an even entire two-base weld whose transverse projector
families possess the forced seam nonnormality.  Any rigidity proof must rule out this nonnormality
using the exact semigroup carrier; any counterexample must construct it.  Diophantine return times
without a carrier-derived transverse growth bound cannot close the core.

## Lean target

Formalize the algebraic/analytic core in a new isolated RHTower module:

1. finite geometric Cesàro character limits for irrational `β/α`;
2. lower-flank `r`-slice extraction and upper-flank annihilation;
3. a projection-compatibility no-go theorem under an explicit locally uniform analytic-limit
   hypothesis;
4. only then consider importing the in-tree Montel machinery for the full nonnormality statement.

## Literature audit

Primary-source audit is in progress across Bohr holomorphic almost-periodic functions,
Fourier–Borel/exponential-series theory, analytic continuation of absolutely convergent Dirichlet
series, and normal-family theory.  No scientific-novelty claim is made before that audit closes.


## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/RHTower/LeafReflectionBohrProjection.lean`
(namespace `GaloisForLFunctions.LeafReflectionProjection`, wired into the
`GaloisForLFunctions.RHTower` umbrella).

The card's own Lean target listed four items; all four are delivered, including item 4 (the full
nonnormality statement), which is obtained from the in-tree Vitali theorem rather than from a
bare ball-level Montel.

| Card's Lean target | Lean name |
|---|---|
| **1.** finite geometric Cesàro character limits for irrational `β/α` | `cesaro`, `norm_cesaro_le`, `tendsto_cesaro_one`, `tendsto_cesaro_of_ne_one`, `exp_int_rot_ne_one`, `chi_ne_one` |
| **2.** lower-flank `r`-slice extraction | `proj_eq_tsum_lower`, `tendsto_proj_lower` |
| **2.** upper-flank annihilation | `proj_eq_tsum_upper`, `tendsto_proj_upper` |
| **3.** projection-compatibility no-go under an explicit analytic-limit hypothesis | `flank_limits_incompatible` |
| **4.** the full nonnormality statement | `leaf_reflection_bohr_projection_catastrophe` |

| Paper step | Lean name |
|---|---|
| the exact-period projector `P_{r,N}G(z) = N⁻¹ Σ_{k<N} e^{ikrθ} G(z+kT_α)` | `proj`, `proj_eq_character_form` |
| the flank hypothesis `Σ |b_{m,n}| e^{-w(mα+nβ)} < ∞` and its domination | `flankBound`, `norm_modeTerm_le`, `summable_modeTerm`, `norm_modeTerm_mul_le` |
| a period shift multiplies the `(m,n)` mode by `e^{∓ i k n θ}` | `modeTerm_add_period`, `modeTerm_sub_period` |
| termwise Cesàro averaging on the lower flank | `proj_eq_tsum_lower` |
| `θ/2π = β/α` irrational ⟹ the mean tends to `[n=r]` | `tendsto_cesaro_of_ne_one`, `chi_ne_one` |
| dominated convergence ⟹ `P_{r,N}G → B_r` on `Im z < -w` | `tendsto_proj_lower` |
| evenness reflects `z+kT_α` into the lower flank | `proj_eq_tsum_upper` (uses `hev : ∀ y, G (-y) = G y`) |
| for `r ≥ 1, n ≥ 0` every mean tends to `0` ⟹ `P_{r,N}G → 0` on `Im z > w` | `tendsto_proj_upper` |
| the slice `B_r` is holomorphic on the open lower flank | `differentiableOn_slice` |
| normality (Montel) on a connected `U`: locally bounded + convergence on one ball ⟹ convergence on all of `U` with holomorphic limit | `convNbhd`, `isOpen_convNbhd`, `convNbhd_closed`, `exists_limit_of_locallyBounded` |
| identity theorem: a limit equal to `B_r` below and `0` above forces `B_r ≡ 0` | `flank_limits_incompatible` |
| **the theorem candidate** | `leaf_reflection_bohr_projection_catastrophe` |
| `B_r(z) = Σ_m b_{m,r} e^{-iz(mα+rβ)}` in displayed form | `slice_eq_tsum_row` |
| "the slice is nonzero whenever some `b_{m,r}` is nonzero" | `slice_ne_zero_of_coeff_ne_zero` |
| **the theorem in coefficient form** | `leaf_reflection_catastrophe_of_coeff` |

Two points where the Lean proof is sharper than the sketch.

* **Pointwise suffices.**  The sketch invokes locally uniform convergence on each flank.  The Lean
  proof only needs *pointwise* convergence there: the Montel/Vitali step already supplies a
  locally uniform limit on `U`, and pointwise identification of that limit on the two flank pieces
  is enough for the identity theorem.  This removes the locally-uniform-convergence layer entirely.
* **The last sentence of the proof is proved, not cited.**  "By uniqueness of absolutely
  convergent generalized Dirichlet coefficients" is discharged by
  `slice_ne_zero_of_coeff_ne_zero`, which runs the *same* Cesàro extraction in the second base
  (period `2π/β`, character `2πα/β`, irrational because `(β/α)⁻¹ = α/β`) on the row family
  `rowFamily`, and reads off `b_{m₀,r}` as the limit — so no external uniqueness theorem for
  generalized Dirichlet series is imported.  Supporting lemmas:
  `flankBound_rowFamily_le`, `summable_flankBound_rowFamily`, `slice_eq_carrier_rowFamily`,
  `slice_rowFamily_eq`.

Consequence 3 of the card ("the qualitative obstruction uses only irrationality; continued-fraction
rates do not enter") is now literally visible in the statement: the only Diophantine hypothesis in
`leaf_reflection_bohr_projection_catastrophe` is `Irrational (β / α)`.

**Not formalized (and not an obligation of this card).**  Consequence 1 quotes the in-tree
periodic-spectrum rigidity theorem for the `αℕ` spectrum case; consequence 4 is explicitly marked
`[CONJECTURE]` on the card (the closed connected seam wall needs a planar-separation argument that
the card itself flags as unproved); and the `[OPEN CORE]` — existence or nonexistence of an even
entire two-base weld — is the open problem the card is diagnosing, not a claim of it.

Verification: `lake build GaloisForLFunctions.RHTower.LeafReflectionBohrProjection` — PASS;
`#print axioms` on all 24 named results reports only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-07-11 — card created; exact projector mismatch and paper proof isolated; continued-fraction
  guess downgraded; full leaf-rigidity core remains open.
- 2026-08-17 — formalized in Lean: all four items of the card's Lean target delivered,
  including the full nonnormality statement and the coefficient criterion; card moved to stage 3.
