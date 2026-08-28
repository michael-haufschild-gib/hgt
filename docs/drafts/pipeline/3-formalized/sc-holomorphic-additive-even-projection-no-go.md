# SC holomorphic additive even-projection exterior-square no-go

- **ID:** SC-HAEPN
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** read-only `rh-current-frontier-map.md` · route SC `LAND COMP`; additive survivor of `SC-HPSUPN`; corpus Boolean-cube determinant expansion, exact Gamma-Bockstein weights, holomorphic real restriction, and normalized-Xi real polarity
- **Statement:** The canonical additive even projection
  `A_m(z)=(U_m(z)+U_m(-z))/2` of coefficient-faithful holomorphic SC identity-unitizations is entire, even, and center-normalized, but its even-compound expansion has cofinally negative exterior-square polarity at `z=1`; compact-open convergence to normalized centered Xi is impossible.

## Goal

Test the additive parity repair surviving the multiplicative polarity no-go.  It cancels every odd
compound without multiplying forward and reflected determinants, so it genuinely avoids both the
fixed cubic witness and the reflected rank-one polarity-product mechanism.

## Gates

- [x] 0 → 1 in-progress: mandatory corpus search, source-derived conjecture, hostile escape audit, current literature search
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean source check/build, scoped axiom audit, forbidden-declaration scan, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone paper and independent novelty review

## Conjecture loop and result

1. **C1 — additive parity projection may escape both prior SC obstructions.** Confirmed
   structurally: `A_m` is entire, exactly even, and satisfies `A_m(0)=1`; neither the odd-compound
   gap nor the multiplicative reflected-polarity proof applies.
2. **C2 — additive projection is exactly the even exterior algebra.** The corpus powerset formula
   yields
   `A(b)=Σ_{S even}(1-|S|)∏_{i∈S}b_i`.
   This is an exact identity for every finite real packet. **[PROVED HERE]**
3. **C3 — higher even compounds might repair the quadratic sign.** Fails for every strictly
   negative packet.  Each even product is positive and every nonempty even coefficient `1-|S|`
   is negative.  Therefore deleting degrees four and above only increases `A(b)`, giving the exact
   exterior-square upper bound
   `A(b) ≤ 1-Σ_{|S|=2}∏_{i∈S}b_i`. **[PROVED HERE]**
4. **C4 — prime weights may make exterior-square mass negligible.** Fails.  At transverse input
   one each Bockstein coordinate is `-(p-1)/(p+1)`, with positive magnitude at least `1/3`.
   Consequently the pair mass grows cofinally and already exceeds the center term for every packet
   `m ≥ 2`; hence `A_m(1)<0`. **[PROVED HERE]**
5. **C5 — normalized Xi may have matching polarity.** Fails unconditionally.  Corpus real-axis
   reality plus the certified zero-free closed unit disc gives
   `Re(XiC(1)/XiC(0))>0`.  Local-uniform convergence would imply pointwise convergence at one and
   contradict the eventual source sign. **[PROVED HERE]**

## Hard-frontier significance and limit

This theorem is structural rather than a numerical-bound improvement: additive parity projection
retains the complete even exterior algebra, whose degree-two component already has the wrong
cofinal orientation and whose higher even components reinforce it.  It closes one canonical
additive SC landing.

It does **not** retire SC or solve SC's hardest open core.  A general additive non-equivalent
operator pencil, a landing singular at moving prime-log clock zeros, or a nondeterminantal invariant
still survives.  Further iteration over ad hoc parity repairs is not justified; research returns to
the shared source-normal completion/orientation producer for L/WBF/JAS/XST/CDC.

## No-go closure

- **Exact killing mechanism:** the center term is opposed by every nonempty even exterior compound;
  cofinal exterior-square mass alone forces negative polarity.
- **Positive survivor:** the exact even-compound formula and its universal quadratic upper bound
  classify the obstruction for arbitrary finite negative packets.
- **Surviving architecture:** a viable SC landing must change the even compound coefficients or use
  a singular/nondeterminantal landing.  Direct additive averaging of reflected unitized
  determinants cannot work.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicAdditiveEvenProjectionNoGo`
- Exact algebra:
  - `evenProjectedUnitizedRealReservoirDeterminant_eq_even_powerset`
  - `even_product_pos_of_neg`
  - `evenProjectedUnitizedRealReservoirDeterminant_le_one_sub_pairMass`
- Prime exterior-square obstruction:
  - `primeGammaBocksteinUnitWeight_ge_one_third`
  - `primeBockstein_pairMass_gt_one`
  - `evenProjected_primeBockstein_neg`
- Holomorphic lift and capstone:
  - `preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection_zero`
  - `preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection_even`
  - `differentiable_preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection`
  - `preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection_one_re_neg`
  - `not_tendstoLocallyUniformly_normalizedXiC_of_additiveEvenProjection`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicAdditiveEvenProjectionNoGo.lean` — PASS
  - `lake build GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicAdditiveEvenProjectionNoGo` — PASS (`Built ...`, 74s)
  - scoped `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
  - forbidden declaration scan and scoped diff check — PASS
  - leaf wired into `GaloisForLFunctions.RHTower`

## Literature audit (as of 2026-08-28)

- Costas-Santos, *On the elementary symmetric functions of a sum of matrices*
  (arXiv:math/0612464), studies determinant and elementary-symmetric identities for matrix sums,
  not the prime-reservoir additive parity projection or Xi polarity obstruction.
- Bornemann, *On the Numerical Evaluation of Fredholm Determinants* (arXiv:0804.2543), studies
  numerical Fredholm determinant evaluation, not this coefficient-faithful SC landing.
- Din, *Analysis of Riemann Zeta-Function Zeros using Pochhammer Polynomial Expansions*
  (arXiv:1009.2989), studies symmetrized Pochhammer approximants to Xi, not additive determinant
  parity projection.
- Griffin--Ono--Rolen--Thorner--Tripp--Wagner, *Jensen Polynomials for the Riemann Xi Function*
  (arXiv:1910.01227), studies eventual Jensen-polynomial hyperbolicity, not prime-reservoir
  exterior-compound polarity.
- Targeted searches found no source stating this exact even-compound upper bound, its Gamma-
  Bockstein cofinal exterior-square obstruction, or the compact-open Xi no-go. **Novelty status:**
  `[NOVELTY UNVERIFIED]` pending independent expert review.

## Door passport

- **Unconditional source:** ordinary-prime enumeration, exact Gamma-Bockstein coefficient,
  Boolean-cube determinant identity, certified central Xi zero-free disc.
- **No RH leakage:** target polarity uses only real-axis reality, continuity, and unconditional
  zero-freeness on `[0,1]`.
- **Burden removed:** canonical additive even projection of identity-unitized coefficient-faithful
  SC determinants.
- **Burden not removed:** general SC additive pencils and shared infinite-completion orientation.

## Log

- 2026-08-28 — created from mandatory Lean-corpus research and current primary-literature search;
  frontier map remained read-only.
- 2026-08-28 — exact even-compound expansion, universal exterior-square upper bound, cofinal prime
  pair-mass obstruction, holomorphic lift, and compact-open Xi no-go formalized and audited.
- 2026-08-28 — explicitly capped this line: no further repair-by-repair SC pruning; next work targets
  shared L/WBF/JAS/XST/CDC source-normal completion/orientation core.
