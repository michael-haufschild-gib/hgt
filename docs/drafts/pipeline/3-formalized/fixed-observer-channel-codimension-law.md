# Fixed observer-channel codimension law

- **ID:** fixed-observer-channel-codimension-law
- **Stage:** 3-formalized
- **Formalized companion:** `./fixed-observer-channel-codimension-law-formalized.md`
- **Type:** THEOREM / exclusion of fixed-block fast-forwarding competitors
- **Status:** `[PAPER-PROVED] [BRIDGE]`
- **Parent:** `../1-in-progress/observer-rank-autonomous-no-shortcut-law.md`

## Exact linear theorem

Let `V,W` be finite-dimensional real vector spaces, let
`T:V -> W` be linear with

[
 m=dim V,qquad v=operatorname{rank}T,
]

and let `U<=V`, `K<=W` be linear subspaces satisfying

[
 T(U)subseteq K.                                      	ag{1}
]

Then

[
 oxed{dim Ule m-v+dim K.}                         	ag{2}
]

The stronger exact preimage formula is

[
 dim T^{-1}(K)
 =m-v+dim(Kcapoperatorname{range}T),                	ag{3}
]

so (2) is optimal given only `dim K`.

## Proof

Restrict `T` to a map `T_U:U->K` using (1).  Its range embeds in `K),
while its kernel embeds in `ker T`.  Rank-nullity therefore gives

[
 dim U
 =dimoperatorname{range}T_U+dimker T_U
 ledim K+dimker T
 =dim K+m-v,
]

which proves (2).

For (3), restrict `T` to `T^{-1}(K)`.  Its kernel is exactly `ker T`
and its range is exactly `K intersect range T`: one inclusion is the
definition of the preimage; for the other, any `y=T(x)` lying in `K`
has `x in T^{-1}(K)`.  Rank-nullity gives (3).

## Quantum block consequence

Let `Phi` be normalized, let `T_Phi` be the real projective
Hamiltonian-action map, and put `v_Phi=rank_R T_Phi`.  Let
`B subset H` be a fixed complex `d`-dimensional subspace containing
`Phi`.  Its projective tangent channel

[
 K_B=BcapPhi^perp
]

has real dimension `2(d-1)`.

If a real coefficient subspace `U<=V` consists of Hamiltonians preserving
`B`, then `H(x)Phi in B` for every `x in U`, hence

[
 T_Phi(U)subseteq K_B.
]

Equation (2) gives

[
 oxed{dim_R Ule m-v_Phi+2(d-1).}                 	ag{4}
]

Thus a fixed efficiently diagonalizable or fast-forwardable block can beat
the stationary-kernel carrier by at most twice its nontrivial complex state
dimension.  For the full fixed-`q` Pauli family with product input,

[
 v_Phi=2sum_{k=1}^q{nchoose k}.
]

Any fixed easy block with `d=o(n^q)` therefore cannot change the conjectured
leading shortcut exponent.  To falsify the observer-rank law through
fixed-block diagonalization, one needs an easy accessible block of
`Theta(n^q)` complex dimension or a family of blocks carrying the missing
leading-dimensional entropy.

## Hostile audit

1. This excludes only a **fixed linear block**.  Quadratic/Gaussian state
   manifolds, moving invariant blocks, periodic component proliferation, and
   arbitrary Hamiltonian-dependent circuit selectors are not fixed linear
   channels and remain outside the theorem.
2. A block of polynomial Hilbert dimension need not be efficiently
   synthesizable; (4) is an upper dimension bound even when a compiler exists,
   not a fast-forwarding theorem.
3. A parameterized family of blocks can add its parameter dimension to the
   union.  No manifold-union dimension claim is made without a separate tame
   incidence theorem.
4. The underlying result is rank-nullity and is classified as a `[BRIDGE]`.
   The frontier delta is the exact exclusion it supplies: bounded-dimensional
   block diagonalization cannot be the leading counterexample to the
   observer-rank conjecture.

## Verdict

`[PAPER-PROVED] [BRIDGE]`.  This closes one competitor class but does not
prove the selector-aware upper law.

## Formalization status

The exact abstract inequality (2), its rank form, and the exact preimage
formula (3) are `[LEAN-PROVED]` as
`QuantumAlg.observerChannel_subspace_finrank_le`,
`QuantumAlg.observerChannel_subspace_finrank_add_rank_le`, and
`QuantumAlg.observerChannel_preimage_finrank_eq` in
`HTGeometry/ObserverVisibleLocalTimeDimension.lean`.

The quantum block-dimension specialization (4) is `[LEAN-PROVED]` as
`QuantumAlg.finrank_blockPreserving_add_observerRank_le` and, in quantum Fisher form,
`QuantumAlg.finrank_blockPreserving_add_qfim_rank_le` in
`HTGeometry/FixedObserverBlockChannelCodimension.lean`, together with the exact channel
dimension `QuantumAlg.finrank_real_blockTangentChannel_add_two`.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  See the formalized companion.
