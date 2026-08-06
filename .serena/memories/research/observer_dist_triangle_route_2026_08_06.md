# observerDist triangle inequality — elementary route (no Riemannian calculus)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/projective-horizon/projective-ht-horizon-symmetric-space-boundary.md`.
Its ONE remaining analytic gap: the triangle inequality of `observerDist`
(`formal/GaloisForLFunctions/HTGeometry/ObserverPairDistance.lean`), i.e. the CAT(0) theorem for
`SL_N(C)/SU(N)`.

## Do NOT use the Riemannian route
Bhatia's proof (path length + exponential-metric-increasing + Daleckii–Krein derivative of exp)
needs the Fréchet derivative of `exp`/`log` of operators, which mathlib does not have.
Golden–Thompson / Araki log-majorization is the WRONG direction: it gives
`‖H+K‖ ≤ ‖log(e^{H/2}e^K e^{H/2})‖` (that is EMI), not the triangle inequality.
`‖log(e^{H/2}e^Ke^{H/2})‖ ≤ ‖H+K‖` is FALSE.

## The route that works (fully elementary; Ky Fan products + majorization)
`d(P,Q) = ‖log λ(P⁻¹Q)‖₂` where `λ(P,Q)` = eigenvalues of `P^{-1/2} Q P^{-1/2}` (all > 0).

1. **Scalar submultiplicativity, via quadratic forms only.** For positive-definite `X,Y` put
   `μ(X,Y) = λmax(X^{-1/2} Y X^{-1/2})`; then `Y ≤ μ(X,Y)·X` in the Loewner order and
   `R ≤ μ(Q,R)Q ≤ μ(Q,R)μ(P,Q)P`, so `μ(P,R) ≤ μ(P,Q)·μ(Q,R)`. No eigenvalue theory needed —
   it is one chain of quadratic-form inequalities.
2. **Run step 1 on the k-th compound (exterior power).** `C_k` is multiplicative (Cauchy–Binet),
   `C_k(Aᴴ) = C_k(A)ᴴ`, `C_k(1) = 1`, `C_k(diagonal d) = diagonal (∏_{i∈s} d i)`,
   `C_k(unitary)` unitary. Hence for every `k`:
   `∏_{i<k} λ↓(P,R) ≤ ∏_{i<k} λ↓(P,Q) · ∏_{i<k} λ↓(Q,R)`  (Ky Fan / Horn).
3. **Determinants** give equality at `k = N`: `∏ λ(P,R) = ∏λ(P,Q)·∏λ(Q,R)`.
4. So `a := log λ(P,R)` is **majorized** by `v := (log λ(P,Q))↓ + (log λ(Q,R))↓`.
5. **Karamata for `f = square`** is one Abel summation: `Σ(a²−v²) = Σ(a+v)(a−v)`, the weights
   `a_i+v_i` are non-increasing and the partial sums of `a−v` are ≤ 0 with total 0.
6. `‖a‖₂ ≤ ‖v‖₂ ≤ ‖log λ(P,Q)‖₂ + ‖log λ(Q,R)‖₂` (Minkowski). Done.

## Lean architecture (matrices, to dodge an inner product on ⋀^k)
mathlib has NO Cauchy–Binet, NO inner product on exterior powers, NO majorization.
It DOES have `exteriorPower.map` + `map_comp` + `Module.Basis.exteriorPower` +
`exteriorPower.ιMultiDual_apply_ιMulti` (the minor formula) — so define
`compound k A := LinearMap.toMatrix (b.exteriorPower k) (b.exteriorPower k)
   (exteriorPower.map k (Matrix.toLin b b A))` with `b = Pi.basisFun ℂ ι`;
**Cauchy–Binet is then free from functoriality**, and the minor formula gives `C_k(Aᴴ) = C_k(A)ᴴ`.
Index type is `Set.powersetCard ι k` (Fintype + DecidableEq instances exist);
`Set.powersetCard.ofFinEmbEquiv.symm s = Finset.orderEmbOfFin s.val s.prop`.

Master matrix lemma is stated with **explicit unitary diagonalisations as hypotheses**
(`A = Vᴴ * diagonal α * V`, `S` Hermitian with `S*P*S = 1`, `A = S*Q*S`, …), never via
`Matrix.IsHermitian.eigenvalues` — that dodges eigenvalue-multiset uniqueness and makes the
operator→matrix bridge mechanical (`LinearMap.toMatrix` of the corpus's `sqrtOp`/`invOp`/
`eigenvectorBasis`, plus `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`).

Modules: `MatrixCompound.lean` → `CompoundKyFan.lean` → `MajorizationSquare.lean` →
`ObserverTriangleInequality.lean`.
