# Multilinear process tomography, blind sector, and positive-robustness law

- **ID:** ULF-MPTB-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** intervention-completeness attack on constitutive kernel geometry
- **Statement:** A finite law process is reconstructed exactly by a spanning family of joint interventions; every nonspanning family has a canonical annihilator blind sector, and interior positivity cannot remove that nonidentifiability.
- **Status:** [LEAN CERTIFIED] [ROUTE-INDEPENDENT PROCESS THEOREM] [NOT RH]

## 1. Coordinate-free process

Let (E_1,\ldots,E_k) be nonzero finite-dimensional vector spaces over
\(\mathbb F\in\{\mathbb R,\mathbb C\}\). A (k)-slot constitutive process is a multilinear
functional

\[
W:E_1\times\cdots\times E_k\longrightarrow\mathbb F,
\]

equivalently

\[
W\in\left(E_1\otimes\cdots\otimes E_k\right)^*.
\tag{1}
\]

An experiment chooses a joint intervention tensor

\[
u=e_1\otimes\cdots\otimes e_k
\]

and reads (W(u)). Let \(\mathcal U\) be any family of allowed joint interventions and put

\[
U=\operatorname{span}\mathcal U
\subseteq E_1\otimes\cdots\otimes E_k.
\tag{2}
\]

## 2. Exact tomography theorem

### Theorem 2.1

1. The complete experiment record is the restriction

   \[
   \operatorname{res}_U(W)=W|_U.
   \]

2. Its exact blind sector is

   \[
   \boxed{
   \ker(\operatorname{res}_U)=U^\perp
   =\{\Delta:\Delta(u)=0\text{ for every }u\in U\}.}
   \tag{3}
   \]

3. The experiment family reconstructs every process exactly if and only if

   \[
   \boxed{U=E_1\otimes\cdots\otimes E_k.}
   \tag{4}
   \]

4. If (U\) is proper, then every process (W\) lies in a nontrivial affine family

   \[
   W+U^\perp
   \tag{5}
   \]

   of experimentally indistinguishable constitutive laws.

### Proof

Items 1 and 2 are the definition and kernel of linear restriction. In finite dimension, restriction
is injective exactly when its annihilator is zero, which is equivalent to (U) being the whole
tensor product. If (U) is proper, its annihilator contains a nonzero functional \(\Delta\), and
(W\) and (W+c\Delta\) agree on all allowed interventions for every scalar (c). QED.

### Product-instrument corollary

If allowed interventions contain all products from subsets (S_i\subseteq E_i), put
(V_i=\operatorname{span}S_i). Then

\[
U=V_1\otimes\cdots\otimes V_k,
\tag{6}
\]

so product tomography is complete exactly when every slot family spans (E_i). If
(d_i=\dim E_i) and (r_i=\dim V_i), then

\[
\boxed{
\dim U^\perp=\prod_i d_i-\prod_i r_i.}
\tag{7}
\]

This is the exact hidden constitutive dimension, not an analogy to missing coordinates.

## 3. Interior positivity does not repair incomplete experiments

Let \(\mathcal A\) be an affine subspace of Hermitian operators on a finite-dimensional Hilbert
space, representing normalization or causal constraints, and let

\[
\mathcal P=\{W\in\mathcal A:W\succeq0\}.
\]

Suppose (W_0\in\mathcal P) is positive definite and

\[
0\ne\Delta\in(\mathcal A-\mathcal A)\cap U^\perp
\]

is Hermitian. Then, for every

\[
0<\varepsilon<\frac{\lambda_{\min}(W_0)}{\|\Delta\|_{op}},
\]

both

\[
\boxed{W_\pm=W_0\pm\varepsilon\Delta}
\tag{8}
\]

belong to \(\mathcal P\), are distinct, and give identical values on all allowed interventions.

Indeed,

\[
W_\pm\succeq
\bigl(\lambda_{\min}(W_0)-\varepsilon\|\Delta\|_{op}\bigr)1\succ0,
\]

while affine constraints are preserved because \(\Delta\) is tangent to \(\mathcal A\), and
experimental equality follows from \(\Delta\in U^\perp\).

Thus positivity can shrink the law space but cannot generically fill a tomographic blind direction.

## 4. Passive kernels are not processes

`observationally-identical-law-systems-and-intervention-separation-law.md` supplies the sharp
two-bit example: opposite structural directions have the identical full passive joint probability
kernel, but one elementary intervention separates them. A static positive kernel is therefore only
a zero-slot or passive shadow of a constitutive process.

Theorem 2.1 gives the exact replacement. A process is a functional of interventions. Different proof
routes can be called local gauges only when they are proven to be different spanning instrument
families on the same (W). If their combined intervention span is proper, the no-go is the literal
annihilator (U^\perp); if it spans, process tomography reconstructs (W).

## 5. Quantum/process-tensor specialization

For finite quantum processes, each (E_i) may be the real vector space of Hermitian Choi operators
for an intervention slot, and (W\succeq0) the Choi operator of a process tensor/quantum comb subject
to causal trace constraints. The generalized Born rule is precisely the pairing (W(u)).
Tomographically complete instruments span the slot spaces; incomplete instruments leave the blind
sector (3), with positive robustness supplied by (8).

This specialization is established process-tensor theory. The theorem is stated abstractly so it
also applies to classical causal mechanisms, proof transformations, multilinear response systems,
and nonprobabilistic field-valued experiments.

## 6. Hostile scope

- Multilinear duality and tomography are classical.
- Quantum combs, process tensors, causal boxes, and generalized Born rules are occupied.
- A process tensor can be chosen to fit arbitrary finite experiment data.
- The theorem says when routes can be gauges of one process; it does not construct their common
  process.
- Positivity, composition, and causal constraints must be sourced, not declared after observation.
- Infinite process rank is not differential hypertranscendence.
- No physical cost, gravity law, or RH claim follows.

## 7. Lean certification boundary

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveProcessTomography`.

Closed in Lean:

1. exact restriction-kernel/dual-annihilator identity;
2. exact reconstruction iff the intervention subspace is top;
3. existence of a nonzero blind direction iff the intervention subspace is proper;
4. equality of every affine blind-family record;
5. general open-interior robustness: sufficiently small opposite perturbations along every nonzero
   blind direction remain admissible and distinct.

Targeted source check and final module build passed. `#print axioms` reports only standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies.

Also closed in Lean:

6. the tensor-product dimension formula (7) in its stated product-slot form, together with the
   identification of the product-instrument span with the tensor product of the slot subspaces and
   the completeness criterion "every slot family spans";
7. the quantitative positive-definite spectral bound (8) with its distinctness and affine/record
   clauses, and the existence of the least-eigenvalue constant in finite dimension.

Every clause of this card is therefore certified unconditionally in Lean.

Primary process-tomography parent: G. A. L. White et al.,
*Non-Markovian Quantum Process Tomography*, https://arxiv.org/abs/2106.11722.

## Log

- 2026-08-09 — abstract process-tomography and positive blind-sector theorem proved.
- 2026-08-09 — route-independent tomography core and qualitative open-interior robustness closed
  in Lean; quantitative product/PSD clauses remain at paper level.

## Lean certification status — COMPLETE

Modules:

```
GaloisForLFunctions.HTGeometry.ConstitutiveProcessTomography            -- Theorem 2.1
GaloisForLFunctions.HTGeometry.ConstitutiveProcessTomographyDimension   -- equation (7)
GaloisForLFunctions.HTGeometry.ConstitutiveProcessTomographyPositivity  -- equation (8)
```

### Equation (7) — the hidden constitutive dimension

| Declaration | Statement |
|---|---|
| `finrank_piTensorProduct` | `dim (E₁ ⊗ ⋯ ⊗ E_k) = ∏ᵢ dim Eᵢ`, read off the basis `Basis.piTensorProduct` |
| `finiteDimensional_piTensorProduct` | the tensor product of finite-dimensional slots is finite-dimensional |
| `piTensorProduct_map_injective` | a slotwise injective family induces an injective map of tensor products (each slot inclusion splits over a field) |
| `productInterventionSpace` | `U = V₁ ⊗ ⋯ ⊗ V_k` as the range of the slotwise inclusion |
| `productInterventionSpace_eq_span` | `U` is exactly the span of the product interventions `⨂ᵢ vᵢ`, `vᵢ ∈ Vᵢ` — equation (6) |
| `finrank_productInterventionSpace` | `dim U = ∏ᵢ dim Vᵢ` |
| **`finrank_dualAnnihilator_productInterventionSpace`** | **`dim U^⊥ = ∏ᵢ dim Eᵢ − ∏ᵢ dim Vᵢ`** — equation (7) |
| `productInterventionSpace_eq_top_iff` | product tomography is complete iff every slot family spans |

### Equation (8) — interior positivity does not repair the blind sector

| Declaration | Statement |
|---|---|
| `reApplyInnerSelf_add`, `reApplyInnerSelf_sub` | additivity of the quadratic form |
| `abs_reApplyInnerSelf_le` | `\|re ⟪Dx,x⟫\| ≤ ‖D‖·‖x‖²` |
| `reApplyInnerSelf_pos_of_perturb` | uniform positivity survives any perturbation of smaller operator norm |
| **`reApplyInnerSelf_pos_of_smul_perturb`** | **both `W₀ ± εΔ` are positive definite when `ε‖Δ‖` is below the positivity constant** |
| `perturb_ne` | the two perturbations are distinct |
| `record_eq_of_blind` | a blind direction leaves every linear record — hence every affine constraint — unchanged |
| `exists_uniform_positive` | in finite dimension a positive definite operator has a positive uniform constant (the least eigenvalue, as the minimum of the quadratic form on the unit sphere) |
| **`interiorPositivity_blindDirection_persists`** | **the capstone: a threshold below which both perturbations are positive definite, distinct, and experimentally identical** |

The estimate is stated with the positivity constant `c` rather than with `λ_min` symbolically:
`exists_uniform_positive` produces exactly the least eigenvalue as that constant, and carrying `c`
through keeps every later step free of spectral-decomposition machinery.

Umbrella `GaloisForLFunctions.HTGeometry.UniversalLawField` green at 11 577 jobs; `#print axioms`
on `finrank_dualAnnihilator_productInterventionSpace`, `productInterventionSpace_eq_top_iff`,
`productInterventionSpace_eq_span`, `interiorPositivity_blindDirection_persists` and
`exists_uniform_positive` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Log (continued)

- 2026-08-10 — equations (7) and (8) closed in Lean unconditionally; card promoted to stage 3.
