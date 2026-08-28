# SC holomorphic matrix-equivalence divisor no-go

- **ID:** SC-HMEDN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** read-only `rh-current-frontier-map.md` · route SC `LAND COMP`; corpus theorems `reservoirBaseMatrix_det`, `preDivisorRiggedPrimeHolomorphicPacket_zeroCondensation`, and finite matrix determinant multiplicativity
- **Statement:** No finite-valued packet-dependent left/right matrix coupling of the canonical holomorphic SC reservoir matrix can converge in determinant locally uniformly to normalized centered Xi, even when the matrices mix every prime coordinate.

## Goal
Close the finite multiplicative cross-prime/operator-coupling branch left after the scalar
prime-log zero-condensation no-go.  Identify the exact structural operation a viable SC landing
must use.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicMatrixCoupling`, `lake build` green, scoped axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus baseline

The previous SC theorem constructs an entire packet determinant with noncentral zeros
`πi/log p_{m+1} → 0`.  The corpus also has the exact shared-reservoir matrix and its determinant,
but no searched declaration gives a coefficient-faithful complex matrix representative or audits
arbitrary cross-prime matrix equivalences against normalized Xi convergence.

## Conjecture loop

1. **C1 — canonical matrix complexification.**  Put the complex Bockstein coefficients on the
   columns of the universal reservoir base matrix.  Its determinant should be exactly the already
   formalized holomorphic SC packet.
2. **C2 — arbitrary left/right coupling.**  For any finite-valued matrices `A_m(z),B_m(z)`, the
   determinant of `A_m(z) M_m(z) B_m(z)` factors as
   `det A_m(z) · det B_m(z) · det M_m(z)`.  The previous moving-zero theorem should therefore
   forbid locally uniform normalized-Xi convergence without any diagonal, triangular, invertible,
   or holomorphic assumption on `A_m,B_m`.
3. **C3 — hostile escape.**  Additive matrix perturbations do not obey this divisor-preservation
   law and can move zeros.  Therefore the positive survivor is not “all matrix coupling fails”:
   viable coupling must be genuinely additive/non-equivalent before determinant formation, or
   meromorphically singular at the moving prime-log points.

## Attack

Define `M_m(z)=R_{m+2}·diag(B_{p_i}(z))`, where `R_n=I-11ᵀ` is the universal reservoir base matrix
and `B_p` is the exact holomorphic signed Bockstein.  Use `det R_n=1-n` and `det diag=∏` to prove
`det M_m(z)` equals the exact holomorphic SC packet.  Apply determinant multiplicativity twice and
instantiate the scalar-factor zero-condensation theorem with
`G_m(z)=det A_m(z)·det B_m(z)`.

## Paper proof `[PROVED HERE]`

For `n≥0`, let `c_n` be the `n×1` all-one column, `r_n` the `1×n` all-one row, and
`R_n=I_n-c_nr_n`.  Sylvester's determinant identity gives

`det R_n = det(I_1-r_nc_n)`.

The unique entry of `r_nc_n` is the sum of `n` ones, hence equals `n`; therefore
`det R_n=1-n`.

For packet size `m`, put `n=m+2`, let `b_i(z)` be the coefficient-faithful entire signed
Bockstein of prime `p_i`, and define

`M_m(z)=R_n diag(b_0(z),…,b_{n-1}(z))`.

By determinant multiplicativity and the diagonal determinant formula,

`det M_m(z)=(1-n)∏_{i<n}b_i(z)`,

which is definitionally the previously formalized holomorphic SC packet.  Thus this is a literal
coefficient-faithful complex reservoir matrix representative, not an arbitrary matrix sharing only
its determinant on the real line.

Now take arbitrary complex matrices `A_m(z),B_m(z)` of the same finite size and set

`F_m(z)=det(A_m(z)M_m(z)B_m(z))`.

Twice applying determinant multiplicativity yields

`F_m(z)=(det A_m(z) det B_m(z)) det M_m(z)`.

This is precisely the scalar-factor hypothesis of the prior zero-condensation theorem with scalar
profile `G_m(z)=det A_m(z)det B_m(z)`; no invertibility or analytic assumption is needed.  Hence
`F_m` cannot converge locally uniformly to `XiC(z)/XiC(0)`.  Equivalently, arbitrary finite
cross-prime mixing by left/right multiplication preserves the condensing SC divisor and cannot be
the missing Xi landing.

The conclusion does not cover additive perturbations `M_m+K_m`.  Such perturbations can change
the determinant divisor.  Therefore the exact survivor is additive/non-equivalence coupling (or
meromorphic singularity at the moving zeros), not generic “matrix coupling.”

## Literature audit (as of 2026-08-28)

- Finite determinant multiplicativity and divisor invariance under holomorphic matrix equivalence
  are classical; no novelty is claimed for that algebraic principle.
- [Kaad--Nest](https://arxiv.org/abs/1403.7937) treat holomorphic determinant-line sections and
  perturbation isomorphisms for Fredholm complexes.
- [Hartmann--Lesch](https://arxiv.org/abs/2106.02444) and
  [Britz et al.](https://arxiv.org/abs/2007.12834) confirm regularized determinant corrections are
  multiplicative up to exponential, hence zero-free, anomalies.
- No located source states this SC reservoir/Xi divisor obstruction or the additive-coupling
  classification.  **Novelty status:** `[NOVELTY UNVERIFIED]`.

## Door passport

- **Unconditional source:** exact SC Bocksteins, universal reservoir determinant, ordinary-prime
  enumeration.
- **No RH leakage:** target contradiction uses only normalized Xi value `1` at the origin.
- **Hard burden removed if proved:** all finite matrix basis changes, preconditioners, and
  left/right multiplicative cross-prime mixing, including singular matrices.
- **Survivor:** an SC Xi landing must change the pencil additively/non-equivalently before taking
  determinant, or supply packet-dependent meromorphic poles at the condensing noncentral lattice.

## Log
- 2026-08-28 — created in Stage 1 after mandatory corpus search and primary-literature audit;
  frontier map left read-only.
- 2026-08-28 — dependency-closed paper proof completed.  Hostile audit retained additive
  perturbations as the exact surviving coupling class; promoted to Stage 2.
- 2026-08-28 — formalized in
  `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicMatrixEquivalenceNoGo`; exact leaf build
  passed.  Scoped axiom audit for reservoir determinant, packet determinant, coupled determinant,
  and Xi non-convergence capstone returned only `propext`, `Classical.choice`, and `Quot.sound`.
  Umbrella import wired; formal lint recognizes module as reachable (repository-wide lint remains
  red only on unrelated concurrent unreachable modules).
