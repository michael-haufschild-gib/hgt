# Deninger compact-open graded Real-jet universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `deningerEntireFunctionalEquationSigma`, the algebraic conjugate-linear involution
  `F(z) ↦ conj(F(-conj z))` fixing `XiC`;
- the compact-open topology on the entire-source space and continuity of every point jet;
- `iteratedDeriv_conj_conj` and `iteratedDeriv_comp_neg`, which separately control Schwarz
  reflection and argument negation at every derivative order; and
- `xiZeroConjEquiv` with `xiSpectralPointSupport_zeroConj`, which identifies the transformed
  centered Xi divisor point.

The corpus contains these ingredients separately, but no theorem makes the algebraic Real
structure continuous on compact-open cohomology or identifies its simultaneous action on the full
Xi jet tower.

## Universal law

Let

`ΣF(z) = conj(F(-conj z))`

on the compact-open Fréchet space of entire functions. Then:

1. `Σ` is a continuous conjugate-linear involution;
2. `Σ(XiC·F)=XiC·ΣF`, so it descends continuously to
   `O(C)/(XiC·O(C))`;
3. for every entire source `F`, point `z`, and order `k`,

   `J_(z,k)(ΣF) = (-1)^k conj(J_(-conj z,k)(F))`;

4. at every Xi divisor point `rho`, this becomes

   `J_(alpha_rho,k)(ΣF)
      = (-1)^k conj(J_(alpha_conj(rho),k)(F))`.

Thus the compact-open Real involution is not merely algebraic: it acts on the entire continuous
Xi jet observation by conjugating the zero orbit and multiplying degree `k` by the exact parity
character `(-1)^k`.

## Dependency-closed paper proof

1. Precomposition of compact-open continuous maps by `z ↦ -conj z` is continuous, and
   postcomposition by complex conjugation is continuous. Their composite restricts to entire
   functions because Schwarz reflection preserves holomorphicity. Additivity and conjugate
   scalar-linearity are pointwise.
2. Applying the same formula twice cancels both conjugations and both negations, so `Σ²=1`.
3. Since `ΣXiC=XiC` and `Σ` is multiplicative,
   `Σ(XiC·F)=XiC·ΣF`. Hence the Xi range is stable. Quotient-map universality descends `Σ` to a
   continuous conjugate-linear involution on compact-open middle cohomology.
4. Write `G(w)=F(-w)`. Schwarz differentiation gives
   `D^k(conj∘G∘conj)(z)=conj(D^kG(conj z))`.
   Negated-argument differentiation gives
   `D^kG(conj z)=(-1)^k D^kF(-conj z)`. Since `(-1)^k` is real, conjugation fixes that scalar,
   yielding the displayed all-order jet formula.
5. For centered Xi support,
   `alpha_(conj rho)=-conj(alpha_rho)` by `xiSpectralPointSupport_zeroConj`. Substitution into
   step 4 gives the divisor-indexed graded Real law.

No zero-distribution premise, RH premise, convergence upgrade, numerical computation, or
unproved topological division statement enters.

## Formal targets

- `deningerCompactOpenFunctionalEquationSigma`
- `deningerCompactOpenFunctionalEquationSigma_sq`
- `deningerCompactOpenFunctionalEquationSigma_XiMul`
- `deningerArithmeticCompactOpenH1EvenSigma`
- `deningerArithmeticCompactOpenH1EvenSigma_sq`
- `deningerCompactOpenJet_functionalEquationSigma`
- `deningerCompactOpenXiJet_functionalEquationSigma`
- `deninger_compactOpen_gradedRealJetUniversality`

## Novelty audit

Post-proof searches found Deninger's conjectural cohomological/dynamical program, obstructions to
real-coefficient Weil cohomology for arithmetic curves, and entire-function operator models of
zeta divisors. They did not reveal the exact compact-open quotient construction or its
simultaneous conjugate-zero/parity action on every Xi jet order.

The exact topological graded Real-jet law remains **[NOVELTY UNVERIFIED]**:

- https://arxiv.org/abs/math/0605724
- https://arxiv.org/abs/2204.02714
- https://arxiv.org/abs/1705.06222

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerCompactOpenGradedRealJetUniversalityLaw.lean`

with declarations:

- `deningerCompactOpenFunctionalEquationSigma`
- `deningerCompactOpenFunctionalEquationSigma_sq`
- `deningerCompactOpenFunctionalEquationSigma_XiMul`
- `deningerArithmeticCompactOpenH1EvenSigma`
- `deningerArithmeticCompactOpenH1EvenSigma_sq`
- `deningerCompactOpenJet_functionalEquationSigma`
- `deningerCompactOpenXiJet_functionalEquationSigma`
- `deninger_compactOpen_gradedRealJetUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerCompactOpenGradedRealJetUniversalityLaw.lean`

Wired into `GaloisForLFunctions/RHTower.lean` beside the compact-open topological jet dual.
