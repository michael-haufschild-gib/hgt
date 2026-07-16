# Ulrich separation of Clifford bivectors

- **ID:** `ulrich-separation-of-clifford-bivectors`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / GENERALIZED CLIFFORD ALGEBRA / ULRICH MODULI / QUANTUM HORIZON
- **Scientific status:** `[CONJECTURE] [PAPER-PROOF CANDIDATE VIA WARING QUANTUM TORUS] [LEAN PENDING] [NOVELTY PROVISIONAL]`
- **Depends on:** `generalized-clifford-ulrich-hypertranscendence-horizons`

## 1. Conjecture

Let `F` be a smooth homogeneous form on a finite-dimensional vector space `V` over an
algebraically closed characteristic-zero field, and let `C_F` be its Roby generalized Clifford
algebra.  Write `[u,v]` for the commutator of the canonical generators associated with `u,v in V`.

> **Ulrich bivector-separation conjecture.**  For every nonzero `q in exterior^2 V`, there is a
> finite-dimensional representation `rho_q` of `C_F` such that
>
> ```text
> rho_q(sum q_ij [x_i,x_j]) != 0.                                    (1)
> ```

Because `exterior^2 V` is finite-dimensional, pointwise separation implies that finitely many
representations suffice.  Their direct sum is one finite-dimensional representation `rho` whose
commutator symbol

```text
B_rho : exterior^2 V -> End(M),   u wedge v |-> [rho(u),rho(v)]       (2)
```

is injective.

Under the generalized-Clifford/Ulrich correspondence, `(1)` says that finite families of Ulrich
bundles on the cyclic cover `X_F : w^d=F` separate every Clifford bivector.

## 1.1. The invariant that survives failure

Let `beta_F : exterior^2 V -> C_F` send `u wedge v` to the commutator of the canonical
generators, and let

```text
J_fd(C_F) = intersection { ker rho : rho is a finite-dimensional representation of C_F }.
```

Define the **finite-world blind bivector space**

```text
I_2(F) = beta_F^(-1)(J_fd(C_F)).                                  (3)
```

This is defined whether or not the conjecture holds.  The Ulrich bivector-separation conjecture is
exactly `I_2(F)=0`.  A nonzero value would be a new invariant of a smooth hypersurface: a canonical
part of its antisymmetric generalized-Clifford sector invisible to every finite-dimensional
Clifford module and hence to every Ulrich bundle.

For `N>=1`, intersect only kernels of representations of dimension at most `N` and write the
result as `I_2^(N)(F)`.  These form a descending filtration of the finite-dimensional space
`exterior^2 V`, so they stabilize at `I_2(F)`.  Thus `I_2(F)=0` is equivalent to separation at one
finite representation-size cutoff, and finite direct sum then produces one representation with
injective commutator symbol.

## 2. Hypertranscendence consequence

The Lean-proven Clifford shift-suspension theorem turns `rho` into a finite-width exact
hypertranscendence-horizon realization with dependence locus `Z(F)`.  Injectivity of `(2)` then
means:

> Every pairwise incompatibility channel in law space survives above one and the same classical
> holographic horizon.

Thus the conjecture would prove that every smooth projective hypersurface has a finite-memory
realization that is simultaneously exact and maximally noncommutative.  The horizon equation fixes
the classical boundary; Ulrich matter supplies enough worlds to detect its entire bivector sector.

## 3. Evidence already proved

1. The exact shift-suspension horizon theorem is unconditional in Lean once a finite-dimensional
   Clifford representation is supplied.
2. Finite-dimensional Clifford representations exist for smooth forms by the classical
   Clifford/Ulrich correspondence together with the 2024 existence theorem for Ulrich bundles on
   every smooth cyclic covering of projective space.
3. Any decomposable bivector represented by a horizon chord containing an escaping point is
   detected in every exact realization, by the Lean-proven horizon-chord commutator theorem.
4. In three law dimensions every bivector is decomposable.  Hence for a plane horizon with no
   total-contact line, every Clifford representation already has injective commutator symbol.
5. The explicit conic Clifford/factorization model has maximal commutator rank.
6. The general principal-symbol factorization has a complete proof and a Lean module in
   verification: the differential-field exterior commutator kernel is exactly the internal
   Clifford-representation kernel.  Therefore `I_2(F)` is the precise obstruction, with no loss
   introduced by shift suspension or by passage to rational observables.

The genuinely open content begins with nondecomposable bivectors in law dimension at least four.

## 4. Parent and novelty gate

Known parent theory includes finite-dimensional representations of generalized Clifford algebras,
their moduli, the Van den Bergh/Ulrich correspondence, and residual finite-dimensionality questions
for associative algebras.  Targeted searches found no theorem that finite-dimensional
representations of `C_F` separate its canonical bivector sector for every smooth form, nor the
equivalent Ulrich-bundle statement.

This is an absence-of-hit result.  The conjecture must be checked against primitive-ideal and
residual-finiteness literature by theorem statement before any priority claim.

## 5. Anti-theatre and failure modes

The conjecture can fail in two different places:

1. a nonzero canonical bivector may already vanish inside `C_F` because the filtered Roby
   relations create an unexpected low-degree identity;
2. it may survive in `C_F` but lie in the intersection of all finite-dimensional representation
   kernels.

Neither possibility may be assumed away by a PBW slogan.  The first task is to construct and study
the canonical map `exterior^2 V -> C_F`; the second is a degree-two residual
finite-dimensionality theorem.  A counterexample would still be significant: it would define a
new invisible-bivector invariant of the hypersurface.

## 6. Spencer refinement

For a representation kernel `K_rho=ker B_rho`, the Lean-proven first Spencer law forces every
`q in K_rho` to annihilate the terminal principal-symbol coefficient matrix.  The proposed route
is to identify this matrix intrinsically from the Ulrich resolution.  If stability or linear
resolution exactness makes that coefficient map faithful on bivectors, `(1)` follows.

If not, the higher Spencer annihilator tower should refine the degree-two invariant:

```text
I_invisible(F) = intersection over Ulrich E of the full Spencer kernel of E.               (4)
```

The conjecture is `I_invisible(F)=0` in degree two.

## 7. RH impact

For RH research this would say that an arithmetic horizon cannot be modeled only by its scalar
equation: a source must also separate the required bivector incompatibility channels.  No Xi or
L-function Ulrich/Clifford module is presently known, so this remains a source criterion rather
than an RH implication.

## 8. Proof route

The direct route is now the Waring quantum-torus construction in
`waring-quantum-torus-universal-horizon.md`.  A spanning decomposition
`F=sum ell_i^d` and pairwise q-commuting generators make the commutator map a faithful copy of
`exterior^2(c |-> (ell_i(c)))`.  Smoothness forces that coefficient map to be injective.

1. Complete the parent-literature audit of general polynomial linearizations.
2. Prove the finite quantum-torus ordered-monomial basis and quantum multinomial identity.
3. Prove smoothness implies every Waring decomposition spans the full dual law space.
4. Prove the resulting single representation has injective canonical bivector map.
5. Translate that representation through the Ulrich correspondence.
6. Formalize every promoted theorem in Lean; keep `(1)` labeled conjectural until then.
