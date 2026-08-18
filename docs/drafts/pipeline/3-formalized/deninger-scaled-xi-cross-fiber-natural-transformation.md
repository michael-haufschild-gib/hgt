# Scaled completed-Xi cross-fiber natural transformation

- **ID:** deninger-scaled-xi-cross-fiber
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Connes--Consani Scaling Site family; standard quotient functoriality; internal Big-Witt centered-mark comparison
- **Statement:** Half-scaling pullback induces an algebra equivalence from completed-Xi cohomology to the quotient by the half-scaled Xi source, transports every centered theta fiber at `alpha` isomorphically to the target fiber at `2 alpha`, and intertwines Big-Witt Frobenius with the transported reporter.

## Goal

Construct the missing cross-fiber map without assuming stability of the zero divisor under
`alpha |-> 2 alpha`.  The target must therefore vary with the scaling cover.  This matches the
Scaling Site's family-valued action and separates canonical cross-fiber transport from the
unsupported identification of every scaled target with the original completed-Xi quotient.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Literature prerequisite

Connes--Consani's Scaling Site carries the positive-integer action across a family of geometric
fibres.  The relevant algebraic prerequisite is standard quotient functoriality: an algebra
equivalence `e : A ≃ B` induces `A/I ≃ B/e(I)`.  Here `A=B=Entire(C)`,
`e(F)(z)=F(z/2)`, and `I=(XiC(z))`.  The target is therefore

`H_scaled(2) = Entire(C) / (XiC(z/2))`.

This prerequisite constructs no Xi zero and assumes no divisor stability.

## Conjecture / failure loop

1. **[CONJECTURE A] Fixed-quotient half-scaling.**  Descend `F(z) |-> F(z/2)` to an
   endomorphism of `Entire(C)/(XiC(z))`.
   **Verdict: FALSE as the canonical source route.**  Descent would require
   `XiC(z/2) ∈ (XiC(z))`; hence every Xi zero would halve repeatedly.  The resulting zeros tend
   to zero, contradicting the proved zero-free unit disc.  This is an ideal-stability demand, not
   quotient functoriality.

2. **[CONJECTURE B] Arbitrary fixed-quotient fibre maps.**  Choose nonzero maps from the fibre at
   `alpha` to the fibre at `2 alpha` inside one completed-Xi quotient.
   **Verdict: CIRCULAR.**  A total choice forces `XiC alpha = 0 -> XiC (2 alpha) = 0`.  No
   source-native map in the corpus or audited literature supplies that divisor law.

3. **[CONJECTURE C] Family-valued pullback.**  Replace the fixed target ideal by the image ideal
   under half-scaling.
   **Verdict: SURVIVES; [BRIDGE].**  Quotient functoriality gives an algebra equivalence, and the
   centered coordinate has exact weight two.  This is the canonical cross-fibre transformation.

## Exact objects

Let `C₂ F(z)=F(z/2)` and `D₂ F(z)=F(2z)`.  They are inverse complex-algebra automorphisms of
`Entire(C)`.  Put

`I = (XiC(z))`, `I₂ = C₂(I) = (XiC(z/2))`,

`H = Entire(C)/I`, and `H₂ = Entire(C)/I₂`.

Let `E₂ : H ≃ H₂` be induced by `C₂`.  On both quotients let `Z` be coordinate class and
`Theta = 1/2 + I Z`, acting by multiplication.  A spectral fibre consists of nonzero vectors
`x` satisfying `Theta x = (1/2 + I alpha)x`.

## Dependency-closed proof

1. Entire functions are closed under precomposition with complex-linear maps, so `C₂` and `D₂`
   are complex-algebra homomorphisms.  Pointwise identities `(z/2)*2=z` and `(2z)/2=z` make them
   inverse algebra equivalences.
2. Standard quotient functoriality applied to `C₂` and `I` gives
   `E₂ : Entire/I ≃ Entire/C₂(I)`.  Mapping a principal ideal maps its generator, hence
   `C₂(I)=(XiC(z/2))`.
3. Since `C₂(z)=z/2`, the quotient coordinate obeys
   `Z₂ E₂(x)=2 E₂(Zx)`.  Expanding `Theta` gives the affine intertwining law
   `Theta₂ E₂(x)=2 E₂(Theta x)-1/2 E₂(x)`.
4. If `Theta x=(1/2+I alpha)x`, the affine law simplifies to
   `Theta₂ E₂(x)=(1/2+I(2 alpha))E₂(x)`.  Injectivity of `E₂` preserves `x≠0`.  Applying the
   inverse equivalence gives a bijection of the two spectral fibres.
5. The Big-Witt reporter ignores the vector and records the centered mark.  Existing
   `F₂([u_p(s(alpha))])=[u_p(s(alpha))²]` and
   `u_p(s(2 alpha))=u_p(s(alpha))²` prove the naturality square with transported target label
   `2 alpha`.

Every step is unconditional.  No theorem asserts `XiC alpha = 0 -> XiC (2 alpha) = 0`; the
target quotient changes exactly so the transported eigenvector exists.

## No-go closure

- **Exact killing theorem/mechanism:** fixed-quotient descent demands preservation of the Xi
  principal ideal under half-scaling, which would make the Xi divisor closed under repeated
  halving and accumulate it at a known nonzero point of Xi.
- **Strongest positive survivor:** exact algebra equivalence between original and scaled-Xi
  quotients, exact weight-two coordinate law, fibre equivalence, and Big-Witt naturality square.
- **New insight:** arithmetic Frobenius becomes horizontal only after the analytic receiver is
  treated as a scaling family.  Identifying the scaled receiver back with the fixed completed-Xi
  quotient is precisely the forbidden divisor-stability step.
- **Status:** internal Lean corpus and primary literature audited; `[PROVED HERE]`; formalized by
  `deningerEntire_scalingCover_quotientFunctoriality`,
  `completedXiScaledTwoCrossFiberEquiv`, and
  `deningerBigWitt_completedXi_scaledTwo_crossFiberNaturalTransformation`.  Direct-file Lean and
  targeted module builds pass.  Axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.  No umbrella build was run.

## Log

- 2026-08-18 — created in 1-in-progress after corpus and Scaling Site audits.
- 2026-08-18 — three conjecture/failure loops completed; hostile dependency audit closed the
  family-valued theorem; moved to 2-fully-proven before Lean formalization.
- 2026-08-18 — literature prerequisite formalized first, then cross-fibre equivalence and
  Big-Witt naturality square; scratch, direct-file Lean, targeted builds, proof-debt scan, and axiom
  audit passed; moved to 3-formalized and wired into the RHTower umbrella without building it.
