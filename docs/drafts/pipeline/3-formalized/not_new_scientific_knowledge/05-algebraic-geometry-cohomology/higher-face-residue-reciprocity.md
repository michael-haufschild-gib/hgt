# Higher Face-Residue Reciprocity and the Constraint-Depth Phase Transition

- **ID:** `higher-face-residue-reciprocity`
- **Stage:** 3-formalized / needs independent scientific audit
- **Type:** THEOREM (paper) / ALL-RANK RECIPROCITY / NO-GO THEOREM
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` — the all-rank reciprocity theorem is unconditional; the HT-kernel examples use the candidate generic multiple-elliptic-gamma theorem
- **Statement:** Every meromorphic function with a constant full mixed difference has one canonical top face-residue, independent of which boundary face is used to compute it. This holds in every rank. The invariant is complete for DA versus HT exactly in the triptic case; at every higher constraint depth it has a hypertranscendental kernel. The exact repair is not a full higher complex but the collection of unpushed triptic residues on all two-parameter faces.

## Constraint classes

Let `d>=1`, let

`tau_1,...,tau_d in H`,

and assume

`1,tau_1,...,tau_d`

are linearly independent over `Q`. Put

`H_d=Z+sum_(j=1)^d Z tau_j`, `G_d=C/H_d`.

Define

`Q_d(tau)={F in Mer(C):Delta_1 F=0 and product_(j=1)^d Delta_(tau_j) F in C}`.

The class is defined by one full mixed constraint, not by a special function or a recurrence flow.

## Depth-one principal-part charge

For `d=1`, every `F in Q_1(tau_1)` is quasi-elliptic:

`Delta_(tau_1)F in C`.

Its pole classes form a finite set on the elliptic curve

`E_1=C/(Z+Z tau_1)`.

At a pole class `p`, write

`PP_p(F)=sum_(k>=1)a_(p,k)(z-p)^(-k)`

and set

`L_p(X)=sum_(k>=1)a_(p,k)X^(k-1)/((-1)^(k-1)(k-1)!)`.

Define

`R_1(F)=sum_p L_p(delta)[-p+H_1] in C[delta][G_1]`.

The factorial normalization makes

`R_1(delta F)=delta R_1(F)`.

Translation acts by translating the group-algebra divisor.

## Pushforward of finite differential divisors

For a subset of periods with group `H_S subset H_d`, the quotient map

`C/H_S -> C/H_d`

induces a pushforward on finite-support group algebras:

`push_(S,d):C[delta][C/H_S] -> C[delta][G_d]`.

It sends a basis class to its class modulo `H_d` and adds coefficients that collide. Pushforwards along nested quotients commute.

## Recursive face residue

Suppose `d>=2` and `F in Q_d(tau)`. For each `j`,

`F_j=Delta_(tau_j)F`

belongs to `Q_(d-1)(tau^(j))`, where `tau^(j)` omits `tau_j`.

Assuming `R_(d-1)` is already defined, form the `j`-face candidate

`R_d^(j)(F)=push_(hat j,d)(R_(d-1)(F_j)) in C[delta][G_d]`.

## Higher face-residue reciprocity `[PROVED HERE]`

For every `d>=2`, every `F in Q_d(tau)`, and every pair `j,k`,

`R_d^(j)(F)=R_d^(k)(F)`.

Hence there is one well-defined invariant

`R_d(F) in C[delta][G_d]`,

the **depth-`d` face residue** of `F`.

### Base case: `d=2`

This is the direct local-finiteness theorem in `triptic-orbit-residue-reciprocity`. The two face candidates are the labelled orbital principal-part divisors computed on

`C/(Z+Z tau_1)` and `C/(Z+Z tau_2)`.

On each `H_2`-orbit and at each pole order, the principal-part coefficients of `F` form a `Z^2`-array. Its first differences have finite support and the mixed constraint makes the array additively separable. The two mixed quadrants contain infinitely many lattice points in compact subsets modulo period `1`; meromorphic local finiteness forces both mixed tail values to vanish. The two boundary jumps are therefore equal.

### Induction

Assume the theorem through depth `d-1`, and fix `j != k`. Since the face residue of `F_j=Delta_(tau_j)F` is independent of its own chosen face, compute it through direction `k`:

`R_(d-1)(F_j)=push_(hat{j,k},hat j)(R_(d-2)(Delta_(tau_k)Delta_(tau_j)F))`.

After pushing through direction `j`,

`R_d^(j)(F)=push_j push_k R_(d-2)(Delta_(tau_j)Delta_(tau_k)F)`.

The same argument with `j` and `k` interchanged gives

`R_d^(k)(F)=push_k push_j R_(d-2)(Delta_(tau_k)Delta_(tau_j)F)`.

Translations commute, and the two finite-support pushforwards commute. Therefore the expressions are equal.

For `d=2` the direct theorem supplies the induction base; for `d=3` the displayed formula uses the depth-one principal-part charge defined above.

## Explicit higher-Stokes formula `[PROVED HERE]`

Choose any surviving direction `i`. Apply differences in every other direction:

`V_i=product_(j != i) Delta_(tau_j)F`.

Then `V_i in Q_1(tau_i)`. Take its labelled principal-part divisor `R_1(V_i)` on the elliptic curve with periods `1,tau_i`, and push it through all omitted directions to `G_d`.

The result is `R_d(F)`, independently of `i` and independently of the order in which the faces are traversed.

Thus `R_d` is a finite `(d-1)`-fold corner charge. The theorem is a meromorphic higher-Stokes law: every codimension-one route to the same rank-`(d+1)` boundary gives the same charge.

## Module properties `[PROVED HERE]`

The map

`R_d:Q_d(tau) -> C[delta][G_d]`

is additive, commutes with `delta`, and is equivariant for arbitrary complex translation:

`R_d(T_aF)=t_(a+H_d)R_d(F)`.

Consequently every structural parameter difference lies in its kernel:

`R_d(Delta_(tau_j)F)=0`.

Indeed `tau_j=0` in `G_d`.

## Multiple elliptic gamma is the unit-charge carrier `[PROVED FROM THE CLASSICAL HIERARCHY]`

Let `Psi_(d-1)` be the logarithmic derivative of Nishizawa's order-`d-1` multiple elliptic gamma function with parameters `tau_1,...,tau_d`. The hierarchy equations give

`Delta_(tau_j)Psi_(d-1)=Psi_(d-2)^(j)`.

After differences in any `d-1` distinct directions, one reaches a theta logarithmic derivative in the surviving parameter. Its normalized depth-one principal-part charge is `[0]`. Hence

`R_d(Psi_(d-1))=[0] in C[delta][G_d]`.

For any finite differential divisor `D in C[delta][G_d]`, choose lifts of its support and apply `D` to `Psi_(d-1)`. Translation and differential equivariance give

`R_d(D Psi_(d-1))=D`.

Therefore `R_d` is surjective in every depth.

## Completeness phase transition `[PROVED HERE, WITH HT STATUS CONDITIONAL ON THE ORDER-ONE PARENT]`

### Depth one: nonzero residue can be DA

Every member of `Q_1` is DA: shifted derivatives of a theta logarithmic derivative match its principal parts, and the remainder is constant. Yet `R_1` is generally nonzero. Thus the depth-one charge is not a DA obstruction.

### Depth two: exact completeness

The triptic normal-form and elliptic-gamma atomic theorem give

`F in Q_2 is DA iff R_2(F)=0`.

At this unique depth, the top face residue is a complete DA/HT invariant.

### Every depth `d>=3`: hypertranscendental kernel

Take the unit-charge carrier `Psi_(d-1)` and one structural direction `tau_j`. Then

`R_d(Delta_(tau_j)Psi_(d-1))=0`.

But the hierarchy equation identifies this kernel element with

`Psi_(d-2)^(j)`.

For `d>=3`, this is a positive-order multiple elliptic gamma logarithmic derivative and is hypertranscendental in the generic rationally independent regime, conditional only on the audited order-one elliptic-gamma theorem.

Therefore

`ker R_d contains HT functions for every d>=3`.

This proves a sharp phase transition:

- depth `1`: residue is nonzero even on DA functions;
- depth `2`: residue is exactly complete for DA versus HT;
- depth `>=3`: residue has a hypertranscendental kernel.

## No-go theorem for single-residue classifications `[PROVED HERE]`

No invariant that factors only through the common top face residue `R_d` can classify differential algebraicity in depths `d>=3`. In particular, higher multiple elliptic gamma hypertranscendence cannot be reduced to one terminal residue, even though every full boundary route has the same terminal charge.

The missing information lives on the proper faces before pushforward. This is the precise obstruction left by the failure of completeness.

## Multiplicative higher-face reciprocity `[PROVED HERE]`

Let `Y` be a nonzero `1`-periodic meromorphic function and form its full multiplicative mixed coboundary

`C_Y^(d)(z)=product_(S subset {1,...,d}) Y(z+sum_(j in S)tau_j)^((-1)^(d-card(S)))`.

Assume

`delta C_Y^(d)/C_Y^(d) in C`.

Then `F=delta Y/Y` belongs to `Q_d`, and

`D_d(Y):=R_d(delta Y/Y) in Z[G_d]`.

The invariant can be computed from any codimension-one multiplicative face by taking zero/pole orders, recursively passing to a surviving elliptic curve, and pushing to the common quotient. Every face gives the same integer divisor.

At `d=2`, `D_2(Y)` completely classifies DA versus HT behavior and all finite translate products, conditional on elliptic-gamma atomicity. At every `d>=3`, the terminal multiplicative divisor is not complete: structural quotients of higher multiple elliptic gamma functions are HT but have zero terminal charge.

## The face-complex question is closed by the pair-face theorem

The terminal invariant suggested retaining a full simplex of recursively quotiented residues. That object is unnecessary.

For every pair `{i,j}`, apply all differences in directions outside the pair and take the unpushed triptic residue on the remaining two-parameter face:

`S_(ij)(F)=R_2^(ij)(product_(k notin {i,j})Delta_(tau_k)F)`.

The theorem in `all-depth-pair-face-signature-completeness` proves, conditional only on the depth-two DA-completeness theorem, that

`F is DA iff S_(ij)(F)=0 for every pair {i,j}`.

Thus the rank-three `2`-skeleton is complete at every ambient depth. Higher raw faces carry no additional DA/HT information. The terminal charge `R_d(F)` is the common pushforward of these pair-face divisors and becomes incomplete precisely because that final push identifies distinct finite configurations.

Moreover, a finite family of pair-face divisors is realized by some `F in Q_d` exactly when its three pushforwards agree on every triple. Hence `Q_d` modulo DA is isomorphic to the compatible pair-divisor space, not merely injected into it.

The proof uses a multi-telescoping identity on the bottom elliptic principal-part divisor,

`intersection_i ker(q_i)=(product_i(t_(tau_i)-1))A`,

removes that full boundary by a DA theta layer, and descends inductively in constraint depth.

## Parent-theory and anti-rediscovery audit

### Known components

- one-curve orbital and panorbital residues classify elliptic summability;
- theta principal parts give `R_1`;
- the elliptic gamma gerbe relates rank-three faces multiplicatively;
- Nishizawa and Narukawa give the multiple elliptic gamma hierarchy;
- higher geometric gamma families satisfy coboundary and modular relations;
- simplicial pushforwards and commuting finite sums are formal.

### Residue not located in the parents

No located source defines the all-rank invariant `R_d` for arbitrary meromorphic mixed-constraint functions, proves independence of every boundary face, or identifies the completeness phase transition above. The gerbe literature treats gamma sections and cohomology classes, not DA/HT completeness or the hypertranscendental kernel of terminal residue. The summability literature remains on one elliptic curve.

### Routine-parent separation

Once the depth-two local-finiteness theorem is known, higher face independence is a formal induction. The candidate scientific content is therefore the package:

1. the unconditional depth-two cross-curve residue law;
2. its canonical all-rank extension;
3. the proof that terminal residue is complete at exactly one depth;
4. the resulting no-go theorem and identification of the face complex as the missing invariant.

The formal induction alone is `[BRIDGE]`; it is not claimed independently as discovery.

## Boundaries

1. Full `Q`-linear independence is used to make the rank-`(d+1)` orbits nondegenerate and to obtain the HT examples.
2. The functions are meromorphic on `C`; essential singularities are excluded.
3. `R_d` uses constant-coefficient differential labels.
4. For `d>=3`, the top charge is deliberately not claimed complete.
5. The pair-face signature is complete at every `d>=2`, conditional on depth-two atomicity.

## Lean formalization

The dependency-closed theorem package is collected by
`formal/GaloisForLFunctions/HTGeometry/HigherFaceResidueReciprocity.lean`.
It imports the exact corpus results rather than restating weaker wrappers:

- depth-two reciprocity and DA criterion:
  `triptic_orbit_residue_reciprocity` and
  `differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero`;
- all-depth pair-face vanishing, exact completeness, and exact image:
  `pairFaceSignature_eq_zero_of_differentialAlgebraicOver`,
  `differentialAlgebraicOver_iff_pairFace_eq_zero`,
  `differentialAlgebraicOver_iff_pairFace_univ`,
  `pairSig_triple_compat`, and
  `exists_class_member_with_prescribed_pairSig`;
- multiplicative reciprocity and bottom-charge push:
  `differentialAlgebraicOver_iff_pairFace_logDeriv`,
  `additiveOrbitalDivisorAt_pairFaceWitnessFun`, and
  `exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero`;
- higher-depth noncompression and exact multiple-gamma depth:
  `pairFaceCarrier_private`, `exists_private_carrier_of_omitted_pair`,
  `differentialAlgebraicOver_listShiftDiff_multipleEllipticGammaLogDerivMero_iff`,
  and
  `hypertranscendentalOver_listShiftDiff_multipleEllipticGammaLogDerivMero_iff`.

The capstone passes direct `lake env lean` checking and the targeted
`lake build GaloisForLFunctions.HTGeometry.HigherFaceResidueReciprocity`.
It is wired into `GaloisForLFunctions.HTGeometry`; the umbrella itself was not
built. The capstone introduces no declarations and therefore no new axiom
surface; all imported endpoints are existing unconditional corpus theorems.

## Gates

- [x] Depth-one labelled principal-part charge defined.
- [x] Direct depth-two reciprocity theorem supplied as the base.
- [x] All-rank face independence proved by induction.
- [x] Explicit higher-Stokes formula proved.
- [x] Differential-translation module properties proved.
- [x] Surjectivity realized by multiple elliptic gamma unit charge.
- [x] Depth-one, depth-two, and higher-depth completeness regimes classified.
- [x] Hypertranscendental kernel exhibited at every depth `>=3`.
- [x] Single-terminal-residue classification ruled out at every higher depth.
- [x] Multiplicative higher-face reciprocity proved.
- [x] Full face-residue complex isolated as the exact open core.
- [x] Depth-three unpushed face signature proved complete for the full `Q_3` class.
- [x] Codimension-one face classes proved complete on every cyclic multiple-gamma structural module.
- [x] Full face-complex conjecture replaced by the all-depth complete pair-face `2`-skeleton.
- [x] Exact image characterized by triple compatibility and every compatible family realized.
- [x] Whole dependency-closed theorem package formalized unconditionally in Lean.
- [ ] Independent audit of depth-two atomicity and higher hierarchy HT.
- [ ] Exact/equivalent/stronger literature audit across higher gerbes and discrete cohomology.
- [ ] Independent audit of the all-depth pair-face induction.

## Primary sources checked

- G. Felder, A. Henriques, C. A. Rossi, and C. Zhu, *A gerbe for the elliptic gamma function*.
- G. Felder and A. Varchenko, *The elliptic gamma function and `SL(3,Z) x Z^3`*.
- M. Nishizawa, *An elliptic analogue of the multiple gamma function*.
- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic gamma functions*.
- J. Winding, *Multiple elliptic gamma functions associated to cones*.
- C. E. Arreche and M. W. Babbitt, *Panorbital residues and elliptic summability*.
- M. Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational Period*.

## Log

- 2026-07-10 — Opened after the direct triptic proof revealed a face law rather than a one-function identity.
- 2026-07-10 — Added the depth-one principal-part charge and proved all higher face candidates agree by commuting pushforwards.
- 2026-07-10 — Identified multiple elliptic gamma logarithmic derivatives as unit-charge carriers in every depth.
- 2026-07-10 — Proved the completeness phase transition and exhibited HT kernel elements at every depth at least three.
- 2026-07-10 — Isolated the full face-residue complex as the nontrivial next invariant; terminal residue alone is proved insufficient.
- 2026-07-10 — Closed the first open case: the three unpushed triptic face residues are complete throughout `Q_3`; moved the universal open core to depth four and above.
- 2026-07-10 — Closed the all-depth open core: the `binom(d,2)` unpushed triptic pair faces classify DA versus HT throughout `Q_d`; no higher face complex is required.
- 2026-08-24 — Audited exact corpus endpoints, added and targeted-built the higher-face capstone, wired it into the HTGeometry umbrella, and advanced the card to Stage 3.
