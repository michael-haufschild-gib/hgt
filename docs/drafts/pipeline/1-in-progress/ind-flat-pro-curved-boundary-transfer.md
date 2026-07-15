# Ind-flat source assembly and Pro-curved boundary transfer

- **ID:** `ind-flat-pro-curved-boundary-transfer`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT CONJECTURE / VARIANCE-DUAL BOUNDARY FIELD
- **Scientific status:** `[CONJECTURE] [BOUNDARY FACTORIZATION LEAN-FORMALIZED] [CURVATURE-ONLY RECONSTRUCTION KILLED] [BOUNDARY COLLIGATION LEAN-FORMALIZED] [GAMMA IND-FLATNESS LEAN-FORMALIZED] [NOVELTY OPEN]`
- **Parents:**
  - `constraint-curvature-integration-stack.md`
  - `self-dual-decorated-clock-boundary.md`
  - `calibrated-clock-curvature-class.md`
- **Statement:** A source operation can assemble exactly along the forward Ind clock while its
  finite observable shadows remain curved along the backward Pro clock. The curvature is precisely
  transfer from the newly exposed boundary layer into retained observables.

## Exact split-clock theorem

Let

```text
O_0 --i--> O_1 --p--> O_0,       p i=1.                  (1)
```

Suppose finite shadows satisfy forward compatibility

```text
T_1 i=i T_0.                                               (2)
```

Define backward-observation curvature

```text
kappa=p T_1-T_0 p.                                        (3)
```

Then the Lean-formalized factorization is

```text
kappa=p T_1 (1-i p).                                      (4)
```

Consequently

```text
kappa i=0.                                                 (5)
```

The idempotent `b=1-i p` projects onto the new boundary layer `ker(p)`. Therefore `(4)` says that
all observable curvature is a boundary-transfer map

```text
beta : ker(p) -> O_0,       beta=p T_1|ker(p),             (6)
kappa=beta b.                                               (7)
```

Independently of a chosen complement, curvature vanishes on `range(i)` and descends canonically to

```text
bar_beta : O_1/range(i) -> O_0.                            (7a)
```

Pullback of `bar_beta` along the quotient map is exactly `kappa`. This intrinsic quotient descent
is Lean-formalized.

No global time evolution is involved. The variance is the point: `i` assembles source directions;
`p` forgets observables.

## Rank-one no-go and positive residue

If each scalar clock step adds one dimension, then `ker(p)` is one-dimensional. Equation `(7)`
forces `rank(kappa)<=1` for every forward-compatible source operation. Hence rank-one curvature by
itself is not a special Gamma discovery; it is the generic maximum allowed by a one-slot clock
boundary.

**Positive replacement.** The invariant data are:

1. the actual transfer vector or morphism `beta_N`;
2. its covariance under the complete source-constraint algebra;
3. how the sequence `(beta_N)` integrates in the source topology;
4. its reflected incoming transfer and Hermitian orientation;
5. its holonomy under changes of local source chart.

Thinness is the finite rank of each boundary layer. Source content is the transfer field living on
those layers.

## Gamma model `[LEAN-FORMALIZED]`

For Gamma unit translation, let `i_N` append a zero highest derivative. The canonical Taylor
shadows satisfy

```text
E_(N+1) i_N=i_N E_N.                                      (8)
```

Thus they assemble to one operator on the algebraic direct-limit clock. Backward truncation still
has

```text
kappa_N(a)_i=a_N/(N-i)!.                                  (9)
```

The Gamma boundary transfer is therefore

```text
beta_N(1)=(1/N!,1/(N-1)!,...,1).                         (10)
```

The accumulated transpose vectors in `(10)` are the infinite Taylor conormal for
`h(1)-h(0)`. Gamma is simultaneously:

```text
Ind-flat source assembly + Pro-curved observation + analytic integrability.  (11)
```

This makes Gamma the positive integrable vacuum of the proposed field theory, not a nonzero
ordinary derived-limit obstruction.

## Transfer-only field no-go and positive colligation field

Curvature and transfer do not determine the higher clock action. With `b_N=1-i_N p_N`, every
boundary perturbation `b_N g_N b_N` preserves both forward compatibility and `beta_N`. This is
Lean-formalized.

**Positive reconstruction theorem `[LEAN-FORMALIZED]`.** The higher action is exactly

```text
T_(N+1)=i_N T_N p_N+i_N kappa_N+delta_N,                  (12)
delta_N=b_N T_(N+1)b_N.                                   (13)
```

Therefore `(T_N,beta_N,delta_N)` reconstructs `T_(N+1)` uniquely.

**[CONJECTURE — COLLIGATION FIELD]** Every regular finite-observably free constrained HT source has
a canonical sequence of boundary colligations

```text
(beta_x,N,delta_x,N),       beta_x,N:B_x,N->O_x,N,
                            delta_x,N:B_x,N->B_x,N,        (14)
```

equivariant for its source-constraint algebra and independent of faithful split clock charts. The
source-specific field further includes the descent anomaly; the universal clock colligation alone
is only observation kinematics.

**Falsifier.** Two source-equivalent calibrated split clocks yield inequivalent colligation and
anomaly sequences after their boundary layers are canonically identified.

## Conjecture II: source reconstruction from anomaly colligation

**[CONJECTURE — ANOMALY-COLLIGATION RECONSTRUCTION]** In the analytic source-minimal category, the full
nonlinear source deformation problem is reconstructible from:

```text
(Ind clock, boundary layers B_N, beta_N, delta_N,
 descent anomaly alpha_N, affine calibration,
 source algebra, topology, holonomy).                     (15)
```

For Gamma, the universal translation colligation has factorial `beta_N` and unit `delta_N`; the
source-specific period-one tangent and affine shift anomaly distinguish Gamma from arbitrary
analytic germs. In general, the integrability stack is the moduli of global source operations
having the prescribed anomaly colligation.

**Falsifier.** Two inequivalent source-minimal analytic constraints have isomorphic complete data
`(15)` but different deformation functors.

## Conjecture III: self-dual anomaly colligation

A polarized realization has an incoming transfer from old observables into the new boundary and
an outgoing transfer `beta_N`, together with the internal boundary symbol `delta_N` and source
anomaly `alpha_N`. Write schematically

```text
F_N = [ T_N       beta_N      alpha_N
        beta_N^*  delta_N     alpha_N^vee
        0          0          S_N       ].                (16)
```

**[CONJECTURE — SELF-DUAL BOUNDARY FIELD]** Source reflection identifies the complete augmented
colligation with its reflected dual up to calibrated gauge. The positive observable energy is not
merely `beta_N beta_N^*`; it is the orientation form of the minimal realization of `(16)`, while
spectral incompleteness is its tangent homology or failure of controllable/observable minimality.

This connects the curvature model to the already formalized cross-boundary/Kadison operator
without asserting that every positive block carries source arithmetic. Positivity is automatic for
`beta beta^*`; the new obligation is source orientation and comparison across realizations.

## Conjecture IV: five integration phases of one anomaly colligation

**[CONJECTURE — COLLIGATION REALIZATION LAW]** For a fixed source anomaly colligation:

1. continuation asks whether `(beta_N)` integrates on a larger source domain;
2. boundary conditions are inequivalent global integrations;
3. monodromy is holonomy of local integrations;
4. spectral incompleteness is tangent homology of the integration fiber;
5. positivity is orientation of the reflected transfer pair.

Different chains are the same only when they preserve the actual `beta_N`, not merely its rank,
operator ideal, energy, or determinant.

## RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A zeta source transfer field would have to be constructed from
prime and archimedean constraints before the divisor. The existing RH chains may be observing
different integration failures of such a field. Critical zeros would be fixed-locus degeneracies
of a self-dual assembled transfer complex.

No zeta function, completed xi function, zero set, or zero-indexed operator may define the
transfers. No common transfer sequence has yet been constructed.

## Collision boundary and gates

- Split exact sequences, off-diagonal blocks, low-rank transfer, finite sections, and operator
  colligations are parent theory.
- Rank-one curvature for a one-dimensional new layer is structural and not new.
- The candidate-new residue is a source-canonical HT transfer field, reconstruction, and a proved
  multi-realization integration law.

- [x] split-clock boundary-transfer factorization Lean-formalized
- [x] curvature vanishing on assembled lower clock Lean-formalized
- [x] intrinsic transfer through `O_(N+1)/range(i_N)` Lean-formalized
- [x] transfer-only reconstruction no-go Lean-formalized
- [x] exact boundary-colligation reconstruction and uniqueness Lean-formalized
- [x] Gamma forward Ind compatibility Lean-formalized
- [x] Gamma factorial transfer vector and rank-one range Lean-formalized
- [x] Gamma unit boundary self-symbol Lean-formalized
- [ ] transfer-field covariance under faithful split clock charts proved
- [ ] Gamma analytic integration reconstructed from the transfer sequence
- [ ] one non-Gamma transfer field constructed
- [ ] self-dual incoming/outgoing pair constructed
- [ ] transfer complex and tangent homology defined
- [ ] two analytic obstruction realizations proved to preserve one transfer field
- [ ] independent novelty and significance audit
