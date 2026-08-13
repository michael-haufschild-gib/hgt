# M. Riesz / KernelMinimalExponentialType — literature grounding (2026-08-13)

Target: `KernelMinimalExponentialType s` (NevanlinnaEntryMinimalType.lean): ∀ A>0 ∃ C≥1 ∀ n z,
kernelRoot ≤ C·exp(A‖z‖) for both monicOrthoC and secondKindC kernels — i.e. **minimal
exponential type of P(z) = (Σ|P_n(z)|²)^{1/2} and Q(z)** (uniformity in n is free: partial sums
increase to the limit).

## From Berg–Szwarc arXiv:1310.0247 ("On the order of indeterminate moment problems")

- Thm 1.1: indeterminate ⟺ Σ(P_n²(0)+Q_n²(0)) < ∞ ⟺ P(z) < ∞ ∀z.  (= corpus BoundedKernel.)
- **Thm 1.2 (α ∈ (0,1]), quantitative**: (P_n²(0)),(Q_n²(0)) ∈ ℓ^α ⟹
  P(z) ≤ C exp(K|z|^α) with C = (Σ(P_n²(0)+Q_n²(0)))^{1/2},
  K = (1/α)Σ(|P_n(0)|^{2α}+|Q_n(0)|^{2α}).  At α=1 this is ELEMENTARY-looking (their Thm 4.7)
  and gives finite exponential type K from BoundedKernel alone — but NOT minimal type.
- Riesz's minimal-type theorem is called "deep", cf. Akhiezer p.56 (Thm 2.4.3 area).
- Coefficient machinery: b_{k,n} = coeffs of orthonormal P_n; c_k = (Σ_n b_{k,n}²)^{1/2};
  **(16): Σ_k r^{2k} c_k² = (1/2π)∫ P(re^{it})² dt** (Parseval; b_{k,n} Cauchy-integral (14)).
  A = (a_{j,k}), a_{j,k} = Σ_n b_{j,n}b_{k,n} is trace class with tr = ρ₀ = mean of P² on unit
  circle (their [7]).  Their Φ(z) = Σ c_k z^k has minimal exponential type (proved in [7]).
- Since |P_n|² is subharmonic, P² is subharmonic ⟹ P(r)² ≤ 3·(circle mean at 2r) ⟹ via (16):
  **minimal type of P ⟺ decay k·c_k^{1/k} → 0** (coefficient criterion for the even series
  Σ c_k² x^{2k}).  Self-improvement from the α=1 bound alone fixed-points at K — the strictly
  smaller-than-any-A input must come from moment structure (Akhiezer/Riesz argument: N-extremal
  atoms, zeros of B, genus-0 canonical products, masses ρ_k = 1/K(x_k,x_k), residue relation
  ρ_k = −A(x_k)/B'(x_k)); or from Berg–Szwarc [7]'s direct c_k-decay proof.
- Shift-invariance remark (their p.7, Pedersen): shifted (Jacobi tail) problem has same order and
  type; P-function of shifted problem = b₀·Q(z).  Could transfer P-bounds to Q for free once
  built (also corpus has NevBDWronskian etc.).

## Next actions
1. Fetch Akhiezer, The Classical Moment Problem, §2.4 (pp. 50–60), extract the exact proof of
   Thm 2.4.3 (minimal type of A,B,C,D) and of Σ1/|x_k| behaviour; and/or Berg–Szwarc's [7]
   (inverse Hankel; c_k decay) — pick the Lean-cheapest route.
2. First Lean brick regardless of route: the α=1 quantitative bound (Berg–Szwarc Thm 4.7 shape):
   BoundedKernel(0) ⟹ P(z) ≤ C e^{K|z|} — likely close to corpus assets
   (`norm_nevAinf_le` etc. used S_z·P_0 bounds; check `SecondKindGlobal`).
3. Then the minimal-type upgrade per chosen route; numerically pre-certify identities (mpmath)
   before Lean (project rule).

Corpus reduction already done: `hasMinimalExponentialType_nev{A,B,C,D}inf` from
`KernelMinimalExponentialType` (NevanlinnaEntryMinimalType.lean).  Do NOT re-attempt
Volterra/Gronwall (order 2; recorded no-go).
