# Suzuki ground-edge Cayley universality and the defect-leakage window

- **ID:** `suzuki-ground-edge-cayley-universality`
- **Stage:** 3-formalized / needs external novelty audit
- **Type:** THEOREM (paper and Lean), NECESSITY THEOREM, `[NEW PROJECT KNOWLEDGE]`
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [EXTERNAL NOVELTY UNVERIFIED]`
  `[NOT AN RH PROOF]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096 (2026), especially Theorems 1.4--1.5 and Sections 5--6
- **Statement:** A Suzuki shift that approaches a simple even restricted-Weil ground state faster
  than odd spectral mass can leak through the first gap has a universal Cayley carrier.  The
  dimensionless leakage ratio below is therefore a necessary scale selector for any non-universal,
  Xi-bearing cofinal limit.

## Exact setup

Fix an aperture `a>0`.  Let `A_a` be Suzuki's lower-semibounded self-adjoint restricted-Weil
operator, let `lambda_a` be its lowest eigenvalue, and let `Jf(x)=f(-x)` be parity.  Suzuki proves
that `A_a` has discrete spectrum and commutes with `J`.  Put

```text
B_a=A_a-lambda_a I >=0,
R_tau=(B_a+tau I)^(-1),             tau>0.                 (1)
```

The corresponding admissible shift is `lambda=lambda_a-tau`.  Write

```text
f_+(x)=e^x,       f_-(x)=e^(-x),
f_e=(f_++f_-)/2=cosh x,
f_o=(f_+-f_-)/2=sinh x.                                  (2)
```

Since `R_tau` commutes with parity, define the two nonnegative defect energies

```text
E_e(tau)=<f_e,R_tau f_e>,
E_o(tau)=<f_o,R_tau f_o>.                                 (3)
```

The norm and cross-Gram entries of Suzuki's reflected deficiency pair are

```text
N_tau=<f_+,R_tau f_+>=E_e(tau)+E_o(tau),
C_tau=<f_-,R_tau f_+>=E_e(tau)-E_o(tau).                  (4)
```

Thus its projective defect angle is

```text
kappa_tau=C_tau/N_tau
          =(E_e(tau)-E_o(tau))/(E_e(tau)+E_o(tau)).       (5)
```

## Ground-pole leakage theorem

Assume that the ground eigenvalue is simple and even.  Let `phi_0` be its normalized real
eigenvector and suppose

```text
alpha=|<phi_0,f_e>|^2>0.                                  (6)
```

Let `Delta>0` be a lower spectral bound for `B_a` on the odd subspace and put

```text
beta=||f_o||^2,
rho_a(tau)=tau beta/(Delta alpha).                         (7)
```

Then

```text
0 <= 1-kappa_tau <= 2 rho_a(tau).                         (8)
```

In particular `kappa_tau -> 1` as `tau -> 0+`.

### Proof

The spectral projection of `B_a` at zero is `P_0=|phi_0><phi_0|`.  Functional calculus and
positivity give

```text
E_e(tau)
 =alpha/tau+<P_0^perp f_e,(B_a+tau I)^(-1)P_0^perp f_e>
 >=alpha/tau.                                             (9)
```

The odd subspace is orthogonal to `phi_0`, and `B_a>=Delta I` there, so

```text
0<=E_o(tau)<=beta/(Delta+tau)<=beta/Delta.                (10)
```

Equations `(5)`, `(9)`, and `(10)` yield

```text
1-kappa_tau
 =2E_o(tau)/(E_e(tau)+E_o(tau))
 <=2E_o(tau)/E_e(tau)
 <=2 tau beta/(Delta alpha).                              (11)
```

This proves `(8)`.

For every sufficiently small aperture, Suzuki proves that the ground state is simple, positive
almost everywhere, and even.  Since `cosh x>0`, condition `(6)` then holds automatically.  The
discrete spectrum supplies `Delta>0`.  Hence the theorem applies unconditionally on Suzuki's
small-aperture regime.

## Exact carrier derivative

Let

```text
v_tau=R_tau f_+,
F_tau(z)=integral_(-a)^a v_tau(x)e^(izx) dx,
Theta_tau(z)=((z-i)F_tau(z))/((z+i)F_tau(-z)).             (12)
```

This is the canonically anchored Livsic quotient extracted from Suzuki's characteristic pencil.
At `z=i`,

```text
F_tau(i)=<f_-,R_tau f_+>=C_tau,
F_tau(-i)=<f_+,R_tau f_+>=N_tau.                          (13)
```

Therefore

```text
2i Theta_tau'(i)=C_tau/N_tau=kappa_tau.                   (14)
```

Conjugate the upper half-plane to the disk by

```text
z(w)=i(1+w)/(1-w),
h_tau(w)=Theta_tau(z(w)).                                 (15)
```

Since `z(0)=i` and `z'(0)=2i`, equations `(14)--(15)` give

```text
h_tau(0)=0,             h_tau'(0)=kappa_tau.              (16)
```

Suzuki's all-angle real-zero theorem implies `|Theta_tau(z)|<1` for `Im z>0`; this implication is
already proved in Lean in `SuzukiFiniteApertureHermiteBiehler.lean`.  Thus every `h_tau` is a disk
Schur function fixing zero.

## Cayley universality theorem

Let `tau_j->0+`, allowing the aperture to vary with `j`.  Assume the corresponding Suzuki
carriers have a locally uniform subsequential limit `Theta` on the upper half-plane and that

```text
rho_(a_j)(tau_j)->0.                                      (17)
```

Then

```text
Theta(z)=(z-i)/(z+i).                                     (18)
```

### Proof

The strict Schur bound passes to the closed-disk bound for `Theta`, and the common anchor passes to
`Theta(i)=0`.  Locally uniform convergence of holomorphic functions implies locally uniform
convergence of their derivatives.  Equations `(8)`, `(16)`, and `(17)` therefore give, for

```text
h(w)=Theta(i(1+w)/(1-w)),
```

the identities

```text
h(0)=0,        |h(w)|<=1 on |w|<1,        h'(0)=1.        (19)
```

The equality case of the Schwarz lemma forces `h(w)=w`.  Conjugating back proves `(18)`.

The same proof gives the odd-ground classification: if the simple ground state is odd and has
nonzero overlap with `sinh`, then `kappa_tau->-1` and every locally uniform ground-edge limit is
`-(z-i)/(z+i)`.  Thus a simple parity ground pole always produces a degree-one universal carrier;
it cannot retain an infinite arithmetic spectrum.

## No-go closure and strongest positive survivor

- **Exact killing theorem/mechanism:** The tempting prescription “choose the admissible shift as
  close as possible to the restricted-Weil floor so the defect cannot disappear” is false as an
  RH strategy.  A simple parity ground pole dominates both deficiency channels projectively.  The
  carrier survives, but Schwarz equality rigidifies it to the universal Cayley map and erases all
  excited spectral data.
- **Strongest positive survivor:** The leakage number

  ```text
  rho_a(tau)=tau ||sinh||^2/(Delta_a |<phi_(0,a),cosh>|^2) (20)
  ```

  is an effective, dimensionless scale selector.  For any cofinal Suzuki schedule whose target is
  not the degree-one Cayley model, it is necessary that `rho_a(tau)` not tend to zero along a
  locally uniform subsequence.
- **New insight:** Together with the already proved far-negative free-boundary law, there are now
  two universal ends of the projective shift parameter:

  ```text
  far below the floor  -> free carrier -> zero cofinally,
  too close to a simple parity floor -> plus/minus Cayley,
  arithmetic limit -> excited-state leakage must survive between them. (21)
  ```

  The Suzuki route is therefore not a one-parameter “take the shift to the floor” limit.  It is a
  two-scale problem coupling the ground distance `tau` to the parity gap and source overlap.  The
  remaining positive target is a cofinal lower bound on this leakage together with exclusion of
  the free boundary.
- **Status:** The paper proof and its exact analytic core are formalized unconditionally in
  `SuzukiGroundEdgeCayleyUniversality.lean`.  The module proves the Fourier endpoint derivative,
  defect-angle identity, leakage bound and limit, locally uniform derivative transfer,
  Schwarz-equality rigidity, and the Cayley-universality capstone.  Instantiation with the analytic
  restricted-Weil operator remains blocked only by the absence of that operator and its spectral
  projections from the Lean tree, not by an open mathematical premise in this theorem.

## Lean realization

The unconditional module is

```text
formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
```

Its principal declarations are

```text
upperHalfPlane_cayley_rigidity
suzukiDefectAngle
suzukiGroundLeakage
deriv_suzukiFourierLivsic_disk_zero
deriv_suzukiFourierLivsic_disk_zero_eq_defectAngle
suzukiDefectAngle_ground_leakage_bound
suzukiDefectAngle_tendsto_one
suzukiGroundEdge_cayley_limit
suzukiGroundEdge_cayley_universality
suzukiGroundEdge_nonCayley_forces_leakage_not_tendsto_zero.
```

The capstone allows the aperture, ground mass, parity gap, odd budget, and both defect energies to
vary along an arbitrary nontrivial filter.  It therefore records the exact cofinal scaling wall,
not only a fixed-aperture corollary.

## Hostile attacks

1. **Vanishing ground overlap.** Without `(6)`, the ground pole is invisible to the source and the
   conclusion can fail.  Positivity of Suzuki's small-aperture ground state closes this there; a
   cofinal theorem must prove a quantitative overlap rather than assume it silently.
2. **Closing parity gap.** A fixed-aperture gap is not enough for varying apertures.  Equation
   `(20)` retains the exact `Delta_a` dependence, so the cofinal statement does not hide gap
   collapse.
3. **Multiple ground eigenspace.** Simplicity is essential for the `plus/minus` classification.  A
   mixed-parity ground projection can have an interior limiting derivative and is not forced to be
   Cayley.  Such multiplicity is a distinct live route, not covered by the no-go.
4. **Pointwise versus locally uniform convergence.** Derivative passage needs locally uniform
   holomorphic convergence.  Suzuki's Schur bound supplies normality; the theorem is stated for a
   locally uniform subsequence and does not infer derivative convergence from pointwise data.
5. **RH circularity.** The shift `lambda_a-tau` is admissible for every `tau>0`, irrespective of the
   sign of `lambda_a`.  No positivity of the unshifted Weil operator and no RH assumption enters.

## Literature and novelty boundary, checked 2026-07-21

- Suzuki constructs `A_a`, proves discrete lower-bounded spectrum, parity, the small-aperture
  simple positive even ground state, and the all-angle real-zero characteristic pencil.  He leaves
  control of the shift and identification of the cofinal characteristic limit open; no
  `tau->0`, defect-angle, or Cayley-universality theorem appears in arXiv:2606.09096.
- General Livsic/Weyl-function literature contains characteristic-function identities and the
  equality case of Schwarz's lemma, but the search found no source coupling Suzuki's two parity
  resolvent energies to the leakage invariant `(20)` or the two universal shift boundaries.
- No arXiv follow-up or citing mathematical paper stating `(8)`, `(18)`, or `(21)` was found as of
  the audit date.  This is evidence for new project knowledge, not a certified priority claim;
  external novelty remains explicitly unverified.

References:

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- A. Aleman, R. T. W. Martin, W. T. Ross, *On a theorem of Livsic*, arXiv:1209.4497.
- M. S. Livsic characteristic-function survey, arXiv:2104.12694.

## Gates

- [x] exact no-go isolated and attacked
- [x] strongest positive survivor stated as an effective invariant
- [x] complete paper proof of the energy bound and Cayley endpoint
- [x] RH-circularity and multiplicity attacks recorded
- [x] current literature searched through 2026-07-21
- [ ] external specialist novelty review
- [x] Lean theorem and exact module audit
- [ ] instantiate the restricted-Weil spectral data in Lean
- [ ] prove a cofinal nonzero-leakage lower bound
- [ ] exclude the far-negative free boundary on the same schedule
- [ ] identify a non-universal cofinal carrier with the Xi/de Branges target

## Log

- 2026-07-21 — Ground-edge survival conjecture falsified by Schwarz equality; positive leakage
  invariant and the plus/minus Cayley classification proved on paper.  The even-ground leakage
  law, exact Fourier derivative connector, and locally uniform Cayley capstone were formalized in
  Lean without an RH premise.
