# Infinite coprime traces and exact energy projection

For each d∈ℕ let m=d+2, n_j=m(j+1), and H=L²(ℝ,dt). Write
F_q(t)=∫₀ᵗq and f_q(x)=F_q(eˣ). Inputs are actual elements of H and ℓ²(ℕ).
No summability, regularity or graph-admission premise is added.

## Construction

Let c_k=1_(k,k+1] and h_j=c_(n_j−1)−c_(n_j). Distinct integer cells are
disjoint, have measure one, and therefore form an orthonormal family in H.
Since m≥2, the two cells of h_j never coincide with either cell of h_i for
i≠j. Thus ⟨h_i,h_j⟩=2δ_ij and e_j=h_j/√2 is orthonormal.

For v∈ℓ², finite sums of v_j h_j are Cauchy: the squared norm of any finite
tail is exactly 2 times its squared coefficient sum. Completeness of H gives
E_d(v)=Σ_jv_jh_j in H, with ‖E_d(v)‖²=2Σ_jv_j². Equivalently, let S_d be
the linear isometry v↦Σ_jv_je_j; then E_d(v)=S_d(√2v). Its range is closed:
a convergent image sequence pulls back to a Cauchy sequence in complete ℓ².
It equals the closed span of the tent velocities, since finite sequences are
dense in ℓ² and each h_j lies in the range.

For any integer n≥0, the functional q↦F_q(n) is the continuous inner product
with 1_(0,n]. Its value on c_k is 1 when k<n and 0 otherwise. Consequently
F_(h_j)(n)=δ_(n,n_j). Applying this continuous functional to the convergent
series gives F_(E_d(v))(n)=Σ_jv_jδ_(n,n_j). Injectivity of j↦n_j gives value
v_j at n=n_j and zero at every other nonnegative integer. In particular the
extension realizes every infinite coprime trace, including all forbidden nodes.
At n_j>0, f_(E_d(v))(log n_j)=v_j. Local logarithmic absolute continuity,
the actual derivative and weighted energy transport follow from the proved
Sobolev logarithmic transport theorem for every actual H velocity.

## Intrinsic coefficients and projection

Let A_d=S_d* be the Hilbert adjoint. For arbitrary q∈H,

    (A_d q)_j = ⟨e_j,q⟩ = a_j(q)/√2,
    a_j(q) = 2F_q(n_j)−F_q(n_j−1)−F_q(n_j+1).

The integral identity follows by splitting the two unit cells and subtracting
their primitive increments. Since A_d maps H into actual ℓ², a(q) is square
summable without an extra premise. Set b_d(q)=A_d(q)/√2, so b_j=a_j/2, and
P_d(q)=E_d(b_d(q))=S_dA_dq. Isometry gives A_dS_d=I. Hence P_d fixes every
extension, P_d²=P_d, and for all v∈ℓ²,

    ⟨E_d(v), q−P_dq⟩=0.

This identifies P_d as the orthogonal projection onto the closed extension
range. Pythagoras and the synthesis energy yield the unconditional identity

    ∫ℝ q² = ½ Σ_j a_j(q)² + ∫ℝ (q−P_dq)².

More strongly, for every v∈ℓ²,

    ∫ℝ (q−E_d(v))²
      = ∫ℝ (q−P_dq)² + 2 Σ_j (b_j(q)−v_j)².

Thus the projection is the unique nearest extension and its residual is the
entire loss. If neighboring traces vanish, then a_j=2F_q(n_j), giving the
sharp infinite coprime inequality 2Σ_jF_q(n_j)²≤∫q². Equality holds exactly
for the corresponding tent extension. This is a consequence, not an assumed
support restriction in the core theorems.

## Scope and parent theory

The contribution closes the finite-to-infinite trace realization gap and
identifies its exact continuum energy projection. It does not assert a
unitary affine action or identify a closed SourceGraph operator. The full
physical energy includes the negative half-line; logarithmic transport on
bounded intervals uses the existing theorem and does not discard that energy.

The Hilbert-series and projection tools are classical: [NPTEL, Spaces,
§§1.4.2–1.5.3](https://archive.nptel.ac.in/content/storage2/courses/111106047/chapter1.pdf).
Novelty is relative to this corpus: the searched finite interpolation and
finite defect results do not construct this infinite trace space or its
second-difference projection. Search freshness limitations are recorded on
the pipeline card.

## Formal certification

`CoprimeTentHilbertFrame.lean` (197 lines, 17 theorems, 8 definitions and one
abbreviation) and `InfiniteCoprimeTraceProjection.lean` (260 lines, 23 theorems,
3 definitions) pass final serial direct `lake --old env lean` checks without
warnings. All 52 public declarations were audited: only `propext`,
`Classical.choice`, `Quot.sound`; 12 main signatures have no extra analytic
premise. Both imports and both field maps are updated, and all 40 theorem names
are indexed. The exact equality classifiers and best-approximation inequality
are formalized too. Local logarithmic energy transport uses the existing
`log_energy_eq` from `SobolevLogarithmicTransport.lean` in the same namespace.

Global lint reports nine unrelated concurrent modules missing umbrella imports;
none concerns these leaves. Exact names and evidence are in the knowledge ledger.
This is certified contribution 9/100, counted once.
