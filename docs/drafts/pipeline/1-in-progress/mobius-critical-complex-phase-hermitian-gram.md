# P-G159 — Complex Möbius phase Hermitian Gram and singular graph preservation

- **Route:** P / C47--C49 source orientation and non-diagonal row
- **Status:** formalized positive survivor; RH not proved
- **Lean:** `RHTower/MobiusCriticalComplexPhaseHermitianGram.lean`
- **Statement:** complex inward Möbius source columns have an exact arithmetic Hermitian Gram
  kernel, finite packets are PSD, and the forced Gamma/Xi graph normalizer preserves every kernel
  entry exactly.

## Goal

Replace P-G158's failed aperture-sign doubling by a genuine Hilbert adjoint orientation on the
common squarefree Möbius source. Determine whether non-diagonal source positivity survives the
already-constructed singular Gamma/Xi graph landing.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: direct check and targeted module build green; axiom audit PASS
- [ ] 3 → 4 publication-ready: external novelty limited; RH bridge remains open

## Conjecture loop

### P-G159a — complex source overlap is a Hermitian Euler kernel

For `sigma>1` and inward complex nodes `Re u,Re v>=0`, let

```text
phi_sigma(u)_n = exp(-(sigma-1)u log n) psi_sigma(n).
```

Then

```text
<phi_sigma(u),phi_sigma(v)>
  = squarefreeBoundaryOverlap sigma (sigma-1) (v+conj u).       (P-G159.1)
```

**[PROVED HERE].** Coordinatewise, the second clock phase times the conjugate of the first is the
single clock phase at `v+conj u`; the real signed Möbius weight times its conjugate is the
squarefree probability. Summation is the existing absolutely convergent squarefree Euler overlap.
No continuation, zero-free hypothesis beyond the Euler half-plane, or RH premise enters.

### P-G159b — finite complex packets are positive semidefinite

Define

```text
K_sigma(u,v)=squarefreeBoundaryOverlap sigma (sigma-1) (v+conj u).
```

Equation `(P-G159.1)` gives

```text
conj(K_sigma(u,v))=K_sigma(v,u),
Re sum_i,j conj(c_i)c_j K_sigma(u_i,u_j)>=0.             (P-G159.2)
```

**[PROVED HERE].** The quadratic form is exactly the squared Hilbert norm of
`sum_i c_i phi_sigma(u_i)`. This is the genuine adjoint/conjugate pairing that P-G158 showed cannot
be replaced by `a↦-a`.

### P-G159c — singular graph normalization destroys the non-diagonal Gram

**FALSIFIED.** Let `N_sigma(v)` be the forced complete graph normalizer from the existing
Gamma/Xi source graph. For every pair of inward nodes,

```text
N_sigma(v) * (XiAffine_v(phi_sigma(u))-XiAffine_v(0))
  = K_sigma(u,v).                                       (P-G159.3)
```

Thus graph-normal landing preserves the entire Hermitian Gram entry, not merely diagonal norm.

## Hostile audit

- Weighted Dirichlet-series kernels `sum a_n n^(-s-conj t)` and their PSD/RKHS interpretation are
  classical; see Sahu, *Multipliers of the Hilbert spaces of Dirichlet series*,
  <https://arxiv.org/abs/2301.06413>, and McCarthy--Shalit, *Spaces of Dirichlet series with the
  complete Pick property*, <https://arxiv.org/abs/1507.04162>. Generic Hermitian/PSD kernel form is
  not claimed as external novelty.
- Corpus-new content is the exact normalized squarefree Möbius clock formula at physical
  displacement `sigma-1`, its Lean-closed finite-packet quadratic law, and exact preservation by
  the specific singular completed Gamma/Xi graph normalizer. No external source for this combined
  arithmetic graph statement was located; external novelty remains unverified.
- `(P-G159.3)` does not prove the unnormalized Xi/Ward row contractive. The normalizer contains
  `2(sigma-1) squarefreeBoundaryOverlap`; undoing it pays the already-known singular gain.
- Positivity exists before residue division and survives after multiplication by the full graph
  normal. Missing theorem is compatibility of this positive graph metric with the strict-right
  complementary Ward component at tangent scale, not existence of a source Gram.

## Higher principle

Earlier source failures were shadows of using wrong involution or wrong metric. Aperture reversal
is reciprocal algebra; complex clock reflection is Hilbert adjunction. Ambient source norm becomes
expansive after singular division, but graph-normal metric transports the full arithmetic Gram
isometrically. Route P must therefore compare strict-right Ward energy in the **graph-normal
Hermitian metric**, before taking the critical normal quotient.

## Exact next producer

Construct paired graph-normal Ward difference on conjugate complex nodes and isolate its
strict-right complementary component. Prove or falsify a Schur-complement inequality showing that
this component is dominated by the PSD kernel `(P-G159.2)` uniformly as `sigma→1+`. Any estimate
after division by `sigma-1` is too late and must be rejected.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/MobiusCriticalComplexPhaseHermitianGram.lean` — PASS.
- `lake build GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHermitianGram` — PASS,
  `9119/9119`.
- Four capstone `#print axioms` audits — each exactly
  `[propext, Classical.choice, Quot.sound]`.
- Umbrella import — present in `GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-14 — P-G159a and P-G159b proved in Lean scratch; P-G159c no-go conjecture falsified by
  exact graph-normal preservation.
- 2026-08-14 — direct check, targeted module build, umbrella wiring, axiom audit, and external
  novelty audit completed.
