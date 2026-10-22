# CLG/TTF rank six, arbitrary six-point clusters and exact successor source

- **Stage:** 3-formalized
- **Closed result:** The actual signed center-mixed Hankel matrix of size six is strictly positive at every critical aperture. Every sufficiently small distinct six-point cluster is strictly positive, with one aperture-dependent diameter bound covering all shapes.
- **Exact next obligation:** Nonnegativity of the complete native successor integral at order six, equivalently positivity of the seven-dimensional signed matrix.
- **Scope:** No sign for that next integral or the all-order hierarchy is claimed. RH remains unproved.

## Six-dimensional assembly

Write `s_k(a)=thetaCuspCenterMixedSignedJet a k`. The actual source is even, so `s_(2k+1)=0` and `s_(2k)=(-1)^k f_a⁽²ᵏ⁾(0)`. Put `m_k=s_(2k)`.

The signed six-dimensional matrix has entries `s_(i+j)` for `0≤i,j<6`. Separating even and odd coordinates gives exactly

`E=Hankel₃(m₀,m₁,m₂,m₃,m₄)` and `O=Hankel₃(m₁,m₂,m₃,m₄,m₅)`.

The corpus proves positive first entries and leading two-dimensional minors for both blocks. The even determinant is the already proved eighth-order mixed determinant. The odd determinant is the global compensated source theorem from [the complete compensation proof](clg-ttf-global-odd-compensation.md).

The existing division-free Schur square identity makes each block strictly positive on every nonzero vector. The six-dimensional quadratic form is their sum. Every nonzero six-vector has a nonzero parity component, so the sum is strictly positive. This proves `thetaCuspCenterMixedSignedHankel_six_posDef` for every `0<a<1/2`, with no extra source premise.

## Arbitrary six-point clusters

The factorial-normalized translation jet matrix has entries

`T_ij=(-1)^j f_a⁽ⁱ⁺ʲ⁾(0)/(i!j!)`.

It equals `Sᵀ H₆ S`, with diagonal entries `S_ii=(-1)^floor(i/2)/i!`. Every diagonal entry is nonzero, so the proved positive signed matrix makes this literal translation jet matrix strictly positive.

The corpus prefix divided-difference Gram theorem uses the complete source's proved ten-times differentiability and evenness. It supplies a radius valid for every strictly increasing six-tuple. Translating a tuple by its first node converts the radius into a diameter bound, without changing pairwise differences. Sorting any injective six-tuple and applying a permutation congruence removes the ordering restriction.

Thus for every `0<a<1/2`, there is `δ>0` such that every injective `t:Fin 6→ℝ` with `|t_i−t_j|<δ` for all pairs has strictly positive literal matrix `[f_a(t_i−t_j)]`. There is no minimum-spacing or shape-ratio premise. No uniform radius over all apertures or all cardinalities is asserted.

## Exact successor comparison at every order

For any real moment sequence `s`, set

`A_n=[s_(i+j)]_(0≤i,j<n)`, `b_i=s_(i+n)`,

`Σ_n=s_(2n)−Σ_(i,j<n) b_i (A_n⁻¹)_ij b_j`.

If the actual head `A_n` is strictly positive, its inverse exists. Reindexing the successor matrix as `Fin n ⊕ Fin 1` gives the exact blocks `[[A_n,b],[bᵀ,s_(2n)]]`. The matrix Schur-complement theorem therefore gives

`A_(n+1) positive semidefinite ↔ Σ_n≥0`.

The proof includes the one-dimensional scalar reduction and returns to the original index order. It does not assume a positive successor or replace a singular head by an inverse.

For the literal theta sequence, let `h_k(x)=thetaCuspNativeSignedJet x k` and define the complete native source

`Q_(a,n)(x)=h_(2n)(x)−Σ_(i,j<n) s_(i+n)(a) (H_n(a)⁻¹)_ij h_(j+n)(x)`.

Every term retains the complete source. The existing all-order weighted-native-jet integrability theorem makes `r sinh(ar) Q_(a,n)(r/2)` integrable for `0≤a<1/2`. Finite-sum linearity and the exact native-to-mixed identities prove

`Σ_n(a)=∫_(r>0) r sinh(ar) Q_(a,n)(r/2) dr`

at every order. No sign has been used in this identity.

At `n=6`, the head's strict positivity is now unconditional at every critical aperture. Hence the first unproved section satisfies the exact source equivalence

`H₇(a) positive semidefinite ↔ ∫_(r>0) r sinh(ar) Q_(a,6)(r/2) dr≥0`.

Its leading term is the literal twelfth derivative:

`Σ₆(a)=f_a⁽¹²⁾(0)−Σ_(i,j<6) s_(i+6)(a)(H₆(a)⁻¹)_ij s_(j+6)(a)`.

The odd three-dimensional block stays fixed at rank seven; the even block grows to dimension four. The remaining source inequality must be proved for every critical aperture. Finite rank-six positivity does not provide its sign or an induction over all ranks.

## Lean implementation and verification

Five new modules, 449 lines, 19 public declarations:

- `HTGeometry/SixPointSignedHankel.lean`: strict quadratic-form and parity assembly.
- `HTGeometry/HankelSuccessorSchur.lean`: exact scalar successor admission for every strict finite head.
- `RHTower/ThetaCusp/ThetaCuspCenterMixedSixthRank.lean`: literal parity incidence and unconditional rank-six positivity.
- `RHTower/ThetaCusp/ThetaCuspCenterMixedSixPointCluster.lean`: factorial congruence and arbitrary-cluster theorem.
- `RHTower/ThetaCusp/ThetaCuspCenterMixedSuccessorSource.lean`: all-order complete native source identity and exact rank-seven obligation.

Each module passed a foreground `lake env lean` check; only required new oleans were emitted. The checked source bytes are copied into the corpus, and every module is imported once by its umbrella. No full, umbrella or cascading build was run. Axiom audits of the five new capstones report only `propext`, `Classical.choice`, `Quot.sound`. Formal lint passes with existing large-file warnings. Owned scratch files are removed at the final checkpoint, and no earlier theorem was re-audited.
