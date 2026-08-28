# SC holomorphic parity-symmetrized unitization polarity no-go

- **ID:** SC-HPSUPN
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** read-only `rh-current-frontier-map.md` · route SC `LAND COMP`; survivor of `SC-HUCPN`; corpus theorems `preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal`, `XiC_ne_zero_of_norm_le_one`, `XiC_ofReal_im`, and `continuousOn_nonzero_endpoint_product_pos`
- **Statement:** The even, entire, center-normalized parity product `U_m(z)U_m(-z)` of coefficient-faithful holomorphic SC identity-unitizations has eventually negative polarity at `z=1`, whereas normalized centered Xi has positive polarity there; compact-open convergence is impossible.

## Goal

Attack the exact strongest survivor of the odd-compound no-go.  Multiplying the unitized SC
determinant by its reflected copy cancels every odd compound automatically and produces an entire,
even function normalized to one at the center.  Decide whether this symmetry-complete finite
determinant can be the missing SC landing.

## Gates

- [x] 0 → 1  in-progress: source-pure conjecture, mandatory corpus search, hostile escape audit, current literature search
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: exact Lean leaf source-check/build green; scoped axiom and forbidden-declaration audits pass
- [ ] 3 → 4  publication-ready: standalone paper and independent novelty review

## Corpus baseline

The previous formalized cycle proved that

`U_m(z)=det(I+(I-11ᵀ)diag(B_0(z),…,B_{m+2}(z)))`

is entire and satisfies `U_m(0)=1`, but its full odd exterior-compound part prevents convergence to
even normalized Xi.  Its strongest surviving escape is

`S_m(z)=U_m(z)U_m(-z)`.

This candidate is genuinely outside the prior theorem: `S_m` is entire, exactly even, centrally
normalized, and cancels every odd compound rather than only the cubic term.

## Conjecture loop and result

1. **C1 — odd-part cancellation may suffice.** Confirmed only structurally: `S_m` is entire, even,
   and `S_m(0)=1`.  The prior odd-compound witness vanishes identically, so the old proof cannot be
   reused.
2. **C2 — exact determinant polarity law.** For any finite diagonal with `1+b_i>0`, the reservoir
   determinant has the exact factorization
   `det(I+(I-11ᵀ)diag(b)) = ∏_i(1+b_i)(1-Σ_i b_i/(1+b_i))`.
   Hence its sign is classified exactly by whether the rank-one polarity index
   `Σ_i b_i/(1+b_i)` is below, on, or above one. **[PROVED HERE]**
3. **C3 — reflected prime packets cross the polarity wall.** Corpus definitions reduce the
   transverse-one Gamma-Bockstein coefficient symbolically to `-(p-1)/(p+1)`.  The forward packet
   lies in `(-1,0)` coordinatewise, so `U_m(1)>0`.  Reflection gives positive weights
   `(p-1)/(p+1)`; every cofinal packet eventually has polarity index above one, so `U_m(-1)<0` and
   `S_m(1)<0`. **[PROVED HERE]**
4. **C4 — Xi has matching negative polarity.** Fails.  Corpus reality on the real axis and the
   certified zero-free closed unit disc imply that `XiC(0).re·XiC(1).re>0`; division by the nonzero
   center gives `Re(XiC(1)/XiC(0))>0`.  Pointwise convergence at one contradicts the eventually
   negative source polarity. **[PROVED HERE]**

## Hard-frontier significance

This is not a tightened analytic constant.  It closes the symmetry-complete multiplicative escape
left by the preceding SC theorem: evenness, entireness, center normalization, and cancellation of
the complete odd exterior algebra still do not produce Xi.  The new invariant is the exact
rank-one polarity index and its three-way determinant sign classification.

## No-go closure

- **Exact killing theorem/mechanism:** reflection turns the negative Möbius prime weights into a
  positive cofinal diagonal whose rank-one polarity index crosses one; the two reflected unitized
  determinants therefore have opposite signs at the real anchor.
- **Strongest positive survivor:** `unitizedRealReservoirDeterminant_sign_classification` gives the
  exact polarity wall for every finite reservoir diagonal, not merely this counterexample.
- **New insight:** a viable SC landing must alter the reflected rank-one polarity index itself.  A
  direct multiplicative parity product cannot work.  Surviving constructions require an
  orientation-sensitive additive/coupled counterterm that preserves evenness and the center unit
  while moving the reflected determinant back across the polarity wall.
- **Status:** survivor dependency-closed and formalized in the same Lean module.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicParitySymmetrizedPolarityNoGo`
- Exact algebra and classification:
  - `unitizedRealReservoirDeterminant_eq_product_mul`
  - `unitizedRealReservoirDeterminant_sign_classification`
  - `primeGammaCofinalBocksteinCoefficient_one`
  - `primeGammaBocksteinUnitWeight_ratio_eq`
- Source polarity:
  - `unitized_primeBockstein_positive`
  - `primeBockstein_reflected_ratio_sum_gt_one`
  - `unitized_reflected_primeBockstein_negative`
  - `preDivisorRiggedPrimeHolomorphicParitySymmetrizedDeterminant_one_re_neg`
- Target polarity and capstone:
  - `normalizedXiC_one_re_pos`
  - `not_tendstoLocallyUniformly_normalizedXiC_of_paritySymmetrizedUnitization`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicParitySymmetrizedPolarityNoGo.lean` — PASS
  - `lake build GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicParitySymmetrizedPolarityNoGo` — PASS (`Built ...`, 41s)
  - scoped `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
  - forbidden declaration scan and scoped diff check — PASS
  - leaf wired into `GaloisForLFunctions.RHTower`

## Literature audit (as of 2026-08-28)

- Gesztesy--Zinchenko, *Symmetrized Perturbation Determinants and Applications to Boundary Data Maps
  and Krein-Type Resolvent Formulas* (arXiv:1007.4605), studies abstract symmetrized Fredholm
  determinants and reductions to boundary-data determinants, not this prime-reservoir parity product
  or its polarity index.
- Connes--Consani, *The Scaling Hamiltonian* (arXiv:1910.14368), studies semi-local trace formulas,
  Weil positivity, and the limits of a semi-local operator approach, not the SC determinant above.
- Sun, *Modulus representation of the Riemann ξ function and polynomial inequalities equivalent to
  the Riemann hypothesis* (arXiv:2404.06642), studies a theta/modulus representation and equivalent
  polynomial inequalities, not finite prime-reservoir determinant polarity.
- Targeted current searches found no source stating the exact reservoir sign classification, the
  reflected Gamma-Bockstein polarity crossing, or the compact-open no-go. **Novelty status:**
  `[NOVELTY UNVERIFIED]` pending independent expert review.

## Door passport

- **Unconditional source:** ordinary-prime enumeration, exact activation-Fisher density, exact
  holomorphic Gamma-Bocksteins, universal shared reservoir, certified Xi central zero-free disc.
- **No RH leakage:** target positivity uses only real-axis reality, continuity, and unconditional
  zero-freeness on `[0,1]`.
- **Hard burden removed:** the exact even entire center-normalized multiplicative symmetrization, not
  a numerical estimate or scalar rescaling.
- **Positive survivor:** orientation-sensitive additive/coupled correction must reverse the
  reflected polarity index while retaining parity and central normalization.

## Log

- 2026-08-28 — created from mandatory Lean-corpus research and current primary-literature search;
  frontier map remained read-only.
- 2026-08-28 — determinant-lemma conjecture strengthened to exact three-way polarity
  classification; reflected prime crossing and normalized-Xi polarity formalized; source check,
  exact leaf build, scoped axiom audit, forbidden scan, and umbrella wiring passed.
