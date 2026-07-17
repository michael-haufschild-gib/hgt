# Hypertranscendental scattering is a relative modular-conjugation invariant

- **ID:** `relative-modular-hypertranscendental-scattering-carrier`
- **Stage:** 2-fully-proven / not_new_scientific_knowledge
- **Type:** BRIDGE THEOREM / ALGEBRAIC QFT / PHYSICAL ONTOLOGY
- **Scientific status:** `[PROVED FROM PARENT AQFT] [DIRECT CONSEQUENCE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Scope:** massive asymptotically complete QFT with Bisognano--Wichmann wedge modular data;
  explicit specialization to regular scalar factorizing models; no RH or distinguished
  special-function input
- **Parents:** `../../1-in-progress/geometric-cdd-hypertranscendental-local-qft.md` and
  `../needs-audit/sectoral-kolchin-signature-quantum-fields.md`
- **Statement:** In the incoming physical representation, the scattering operator is the product
  `S_phys=J_in J` of the incoming and interacting wedge modular conjugations. Their modular flows
  are the same boost flow. Hence the complete scattering law, including any HT Kolchin signature,
  is encoded in the relative orientation of two localization constraints with a common flow.
  For the geometric CDD model, the two-particle multiplier of this relative modular unitary is
  hypertranscendental.

## Goal

Identify where HT lives in the QFT itself. The scattering amplitude is operational, but it is
defined through asymptotic states. Modular localization supplies an intrinsic algebraic carrier:
the relative position of the interacting and incoming wedge algebras.

This bridge realizes the mission slogan exactly:

```text
the modular flow is unchanged;
the interaction is in the relative constraint.                            (1)
```

The equality behind `(1)` is established AQFT, not a new theorem.

## Relative modular identity `[PARENT THEOREM]`

Let `A(W)` be an interacting wedge algebra with vacuum `Omega`, and assume asymptotic
completeness so that incoming and outgoing Moller maps

```text
V_in,V_out : H_Fock -> H_phys                                  (2)
```

are unitary. Transport the free incoming wedge algebra to the physical Hilbert space:

```text
A_in(W)=V_in A_0(W) V_in^*.                                   (3)
```

If `J_0` is the free wedge modular conjugation, covariance of modular objects under unitary
transport gives

```text
J_in=V_in J_0 V_in^*.                                         (4)
```

In Lechner's convention the interacting TCP/modular conjugation obeys

```text
J=V_in J_0 V_out^*,                                           (5)
```

and the scattering operator on the physical Hilbert space is

```text
S_phys=V_in V_out^*.                                          (6)
```

Equations `(4)`--`(6)` give

```text
J=J_in S_phys,
S_phys=J_in J.                                                (7)
```

Both factors in `(7)` are antiunitary involutions, so their product is unitary. Other scattering
and TCP conventions can reverse the order or replace `S` by `S^*`; the generated differential
field and Kolchin signature are unchanged. Equation `(7)` fixes the convention used here.

The Bisognano--Wichmann property identifies both modular unitary groups with the same Lorentz
boost representation:

```text
Delta^(it)=Delta_in^(it)=U(Lambda(-2 pi t)).                  (8)
```

Thus no interacting information is added to the one-parameter modular flow. It appears in the
replacement of `J_in` by `J`, equivalently in the relative unitary `(7)`.

## Exact factorizing multiplier

In the incoming Fock representation,

```text
S_hat=V_in^* S_phys V_in=V_out^* V_in.                        (9)
```

For Lechner's scalar factorizing model, its `n`-particle component is multiplication by

```text
S_n(theta_1,...,theta_n)
  =product_(1<=k<l<=n) S_2(|theta_k-theta_l|).               (10)
```

On either ordered two-particle rapidity chamber, analytic continuation of the nontrivial
multiplier is exactly the input two-particle scattering function `S_2(theta_1-theta_2)`, up to
the unitarity inversion determined by the chamber. Therefore

```text
differential field of the two-particle relative modular multiplier
  = differential field of S_2.                               (11)
```

The scattering Kolchin signature is consequently also the two-particle relative-modular
Kolchin signature. This is an equality of the same operator in two descriptions, not a second
independent complexity theorem.

## Hypertranscendental local-QFT corollary

For the geometric CDD family,

```text
S_(q,C)(theta)=-P_q(-i sinh(theta)/C),
P_q(t)=product_(k>=0) ((1-q^k t)/(1+q^k t))^2.               (12)
```

The parent construction proves that this is a regular factorizing scattering function defining
a local asymptotically complete interacting QFT, and that `P_q` is HT over `C(t)` in the canonical
crossing coordinate. Equations `(7)` and `(10)` therefore give a physical model whose relative
wedge modular unitary has an HT two-particle multiplier:

```text
sigma_mod,2=sigma_scatt=1.                                   (13)
```

The real Wigner--Smith phase delay remains the operational reporter. The modular formulation does
not create a different experiment; it identifies the localization-theoretic object that the
experiment reads.

## Fixed-flow modular geometry

The bridge suggests the following exact organization of the physical theory.

For a fixed incoming standard pair `(A_in(W),Omega)`, consider interacting standard pairs with
the same modular group `Delta_in^(it)`. Their relative modular unitary is

```text
M_W=J_in J.                                                   (14)
```

It automatically commutes with the common modular flow, and the involution law for `J` gives the
reality condition

```text
J_in M_W J_in=M_W^*.                                         (15)
```

Factorizing QFT imposes much stronger constraints on `(14)`: Poincare invariance, unitarity,
crossing, Yang--Baxter coherence, strip regularity, modular nuclearity, and reconstruction of
compact-local intersections. Kolchin strata of its rapidity multipliers distinguish DA from HT
relative modular geometry.

This is a useful definition of **relative modular Kolchin geometry**, but `(14)`--`(15)` alone do
not characterize QFT. Products of conjugations are far more general than local scattering
operators.

## Anti-theatre and novelty gate

1. **The S-matrix as relative modular invariant called new.** Rejected. The relation is standard
   AQFT/TCP scattering theory and is explicit in the cited parent sources.
2. **Kolchin equality called a new conservation law.** Rejected. Equation `(11)` follows because
   the relative modular unitary is the scattering operator itself.
3. **An intrinsic local observable claimed.** Rejected. `M_W` is an intrinsic net-level operator,
   but its two-particle multiplier is accessed through the asymptotic representation; it is not a
   compact-local observable.
4. **The modular flow called HT.** Rejected. The boost flow `(8)` is common to interacting and
   incoming theories. HT lies in the relative conjugation constraint.
5. **A general reconstruction theorem claimed.** Rejected. The identities do not show that an
   arbitrary unitary satisfying `(15)` comes from a local QFT.

The bridge is retained because it fixes the ontology of the proposed field without pretending to
add a theorem. It also prevents a wrong research program: searching for HT in the modular
Hamiltonian or boost flow misses the interaction carrier in this class.

## Exact open core

1. The nontrivial analytic locality problem is the relative Hardy-twist problem in
   `unitary-pair-twist-hardy-exponential-bound.md`, not identity `(7)`. That companion card proves
   only a conditional pair-word norm estimate; the actual matrix twist remains open.
2. The intrinsic compact-local strengthening remains the on-shell-to-off-shell Kolchin transfer
   conjecture in `../needs-audit/sectoral-kolchin-signature-quantum-fields.md`.
3. A genuinely new theorem would have to derive a locality, entropy, nuclearity, or connected-
   correlation bound from the differential complexity of `(14)`, or conversely constrain its
   Kolchin strata from modular inclusions. No such theorem is proved here.

## Lean boundary

Formalizing `(7)` as multiplication of two involutions would be wrapper theatre. The
load-bearing inputs are external operator-algebraic scattering and modular theorems. No Lean edit
or build is justified by this bridge.

## Primary literature

- G. Lechner, *On the Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0611050>, especially equations (4.2.18), (4.2.20), Proposition
  4.4.2, and Theorem 6.1.2.
- B. Schroer, *Particle physics and quantum field theory at the turn of the century: Old
  principles with new concepts*, <https://arxiv.org/abs/hep-th/9810080>, for the S-matrix as a
  relative modular invariant.
- H.-J. Borchers, D. Buchholz, and B. Schroer, *Polarization-Free Generators and the S-Matrix*,
  <https://arxiv.org/abs/hep-th/0003243>.

## Gates

- [x] exact convention and antiunitary order fixed
- [x] modular-conjugation identity traced to primary sources
- [x] common modular flow identified
- [x] factorizing multiparticle multiplier identified
- [x] HT corollary derived from the existing local-QFT construction
- [x] novelty rejected for the bridge itself
- [ ] nontrivial modular/Kolchin locality inequality
- [ ] compact-local connected-sector transfer
