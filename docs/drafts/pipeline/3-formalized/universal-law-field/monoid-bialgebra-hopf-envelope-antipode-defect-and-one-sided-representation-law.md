# Monoid bialgebra, Hopf envelope, antipode defect, and one-sided representation law

- **ID:** ULF-BIALG-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** bialgebraic law-genesis fork
- **Statement:** The polynomial monoid bialgebra has no antipode, its Hopf envelope is Laurent localization, and a unilateral-shift representation becomes reversible only after quotienting its Toeplitz defect.
- **Status:** [PAPER-PROVED] [SINGLE-PRODUCER CALIBRATION] [CLASSICAL HOPF/TOEPLITZ PARENTS] [LEAN CERTIFIED]

## 1. Algebraic setup

Let \(k\) be a field and put \(B=k[t]\). Define

\[
\Delta(t)=t\otimes t,
\qquad
\varepsilon(t)=1,
\tag{1}
\]

and extend \(\Delta\) and \(\varepsilon\) as algebra maps.

## 2. Theorem

1. \((B,\Delta,\varepsilon)\) is a commutative bialgebra.
2. It has no antipode.
3. The localization

   \[
   H=k[t,t^{-1}]
   \tag{2}
   \]

   is a Hopf algebra with \(S_H(t)=t^{-1}\).
4. The inclusion \(B\hookrightarrow H\) is universal among bialgebra maps from \(B\) to Hopf
   algebras: every such map factors uniquely through (2).
5. Algebraically, this is the passage from the positive monoid \(\mathbb N\) to its group
   completion \(\mathbb Z\).
6. Let \(V\) be the unilateral shift on \(\ell^2(\mathbb N_0)\). The representation

   \[
   \rho:B\to B(\ell^2(\mathbb N_0)),
   \qquad
   \rho(t)=V,
   \tag{3}
   \]

   does not extend to \(H\).
7. After passing to the Calkin/Toeplitz boundary, the image \(u=\pi(V)\) is unitary, so (3)
   extends uniquely to a representation of \(H\) with \(t^{-1}\mapsto u^*\).
8. The erased operator defect is

   \[
   1-VV^*=P_{e_0},
   \tag{4}
   \]

   and is invisible in the Hopf-envelope algebra (2).

### Proof

Coassociativity and counitality need only be checked on \(t\):

\[
(\Delta\otimes1)\Delta(t)=t\otimes t\otimes t=(1\otimes\Delta)\Delta(t),
\]

and both counit composites send \(t\) to \(t\). Since the maps are algebra maps, this proves the
bialgebra axioms.

If an antipode \(S_B\) existed, the antipode identity on \(t\) would give

\[
S_B(t)t=1=tS_B(t).
\]

Thus \(t\) would be invertible in \(k[t]\), contradiction. In the Laurent algebra it is invertible,
and \(t\mapsto t^{-1}\) satisfies the antipode identities.

Given a bialgebra map \(f:B\to K\) into a Hopf algebra, \(f(t)\) is group-like. Its inverse is
the antipode value \(S_K(f(t))\). The universal property of localization therefore extends \(f\)
uniquely through \(k[t,t^{-1}]\), proving the Hopf-envelope claim.

A representation of \(H\) must send \(t\) to an invertible operator. The unilateral shift is not
surjective and hence not invertible, proving nonextension of (3). In the Calkin quotient,

\[
\pi(V)^*\pi(V)=1,
\qquad
\pi(V)\pi(V)^*=\pi(1-P_{e_0})=1,
\]

so \(u=\pi(V)\) is unitary and defines the Laurent representation. Equation (4) is the standard
range defect and lies in the compact ideal killed by \(\pi\). QED.

## 3. Exact field lesson

One multiplication/comultiplication law produces:

- directed history through \(\mathbb N\);
- reversible observer history through \(\mathbb Z\);
- an algebraic antipode obstruction;
- one-sided positive operator realizations;
- a boundary quotient where the history becomes unitary.

But the Hopf envelope forgets the size and module structure of the operator defect. Therefore the
bialgebra alone is not a complete field primitive. A representation/fibre functor and its completion
are load-bearing, not optional decoration.

## 4. Hostile scope

- Hopf envelopes and universal quantum semigroups are established theory.
- The bialgebra does not select the unilateral-shift representation.
- Different representations of the same bialgebra have different positivity, defects, and topology.
- No hypertranscendence, proof cost, or arithmetic selector follows from the antipode obstruction.

## 5. External parent

Farinati, `Universal quantum (semi)groups and Hopf envelopes`, arXiv:2008.09937.

## Log

- 2026-08-09 — bialgebra single-producer test proved; representation dependence exposed.

## Lean certification status (2026-08-10) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveMonoidBialgebraHopfEnvelope`
(wired into `HTGeometry.UniversalLawField`).

`B = k[t]` is the monoid bialgebra `MonoidBialg k = AddMonoidAlgebra k ℕ`, whose comultiplication is
mathlib's group-like one; `polyEquivMonoidBialg` is the algebra isomorphism with `Polynomial k`
sending `X` to the generator, so this really is `k[t]`.  The Toeplitz side is **reused** from
`ConstitutiveToeplitzDefectIndex` (ULF-TOEPLITZ-1).

1. `isGroupLikeElem_tGen` with `comul_tGen` and `counit_tGen` is equation (1); the bialgebra
   structure itself is mathlib's `AddMonoidAlgebra.instBialgebra`.
2. `not_isUnit_tGen` (via `Polynomial.not_isUnit_X`) and `no_antipode`: the antipode identity at the
   group-like generator reads `S(t)·t = ε(t)·1 = 1`, which would make `t` invertible.
   `isUnit_of_isGroupLikeElem` records the abstract reason — in any Hopf algebra a group-like
   element is a unit.
3. `HopfEnv k = LaurentPolynomial k` carries mathlib's Hopf structure and `antipode_T_one` gives
   `S(t) = t⁻¹`; `isUnit_T_one` is the invertibility.
4. `algHom_ext_tGen` and `algHom_ext_T` are the two determinacy lemmas.  `hopfEnvelope_universal`
   proves the universal property: every algebra map from `B` to a Hopf algebra sending the generator
   to a group-like element factors **uniquely** through `H`, because in a Hopf algebra that image is
   automatically a unit (`GroupLike.toUnits`).  `hopfEnvelope_universal_comp` proves the factorization
   really is a factorization through the inclusion `B ↪ H`, and
   `hopfEnvelope_extension_isGroupLike` proves every basis image of the extension is again group-like
   — which is what makes the factorization a map of bialgebras.
5. `nat_int_group_completion` is the group completion `ℕ → ℤ` in its universal form.
6. `shiftMonoidHom`, `shiftRep` and `shiftRep_tGen` are equation (3); `shiftRep_not_extends` proves
   no algebra map from the Laurent algebra sends `t` to the shift, because that would make the shift
   invertible while it is not surjective (`shiftOp_not_surjective`).
7. `boundary_representation_extends`: for **any** unital algebra map that kills the Toeplitz defect —
   the Calkin quotient being one instance — the image of the shift is a two-sided unit, and the
   representation extends **uniquely** to the Hopf envelope with `t⁻¹` going to the image of `S*`.
8. `defect_eq_rankOne` is equation (4): `1 − V V* = D₁`, which is the projection onto the `e₀`
   coordinate and has rank one.

**Scope note.**  Clause 7 is certified in a form strictly stronger than the Calkin statement and
independent of it: mathlib has no Calkin algebra (the compact operators are available only as a
submodule, not as a two-sided ideal with quotient ring), so the theorem is stated for an arbitrary
defect-killing unital algebra map.  Clause 4 is certified at the algebra-map level together with the
group-likeness of every basis image; mathlib's `BialgHom` packaging is not constructed.

`#print axioms` on `isGroupLikeElem_tGen`, `not_isUnit_tGen`, `no_antipode`, `antipode_T_one`,
`nat_int_group_completion`, `hopfEnvelope_universal`, `hopfEnvelope_extension_isGroupLike`,
`hopfEnvelope_universal_comp`, `shiftRep_not_extends`, `defect_eq_rankOne`, and
`boundary_representation_extends` reports only `propext`, `Classical.choice`, and `Quot.sound`
(the group-completion statement needs only `propext` and `Quot.sound`).
