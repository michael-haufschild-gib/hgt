# Global arithmetic Green-energy radical

- **ID:** `deninger-global-green-energy-radical`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_GLOBAL_GREEN_ENERGY_RADICAL`
- **Parent:** `deninger-arithmetic-calderon-green-intermediate-extension`
- **Statement:** on arithmetic middle cocycles, radical of the
  source Green energy is exactly the closed boundary subspace.

## Source form

Let
\[
 Z^1_{\mathrm{arith}}=\ker Q\subset
 \mathcal E^1_{\mathrm{arith}},\qquad
 B^1_{\mathrm{arith}}=
 \overline{Q\mathcal E^0_{\mathrm{arith}}}
\]
in the strict nuclear source topology.  For each generic Kummer,
finite-prime extended-cusp, real-apex, and relative Milnor packet
\(\alpha\), let
\[
  \mathcal E_\alpha(x)\ge0
\]
be its local Dirichlet/Green energy after applying the corresponding
full Cauchy restriction and passing to the local relative harmonic
quotient.  Equivalently, apply the local Dirichlet-minimizing
projection before taking energy.  This boundary-invariant
harmonic energy, not raw cochain Dirichlet energy, is used below.
Include the restricted product-formula \(L^1\) channel and every
residue/corestriction channel in the packet index.  The global source
energy is
\[
  \mathcal E_{\mathrm{arith}}(x)
  =
  \sum_\alpha \mathcal E_\alpha(x).                           \tag{1}
\]

## Conjecture

`[CONJECTURE] [DAC_GLOBAL_GREEN_ENERGY_RADICAL]`

For every \(x\in Z^1_{\mathrm{arith}}\):

1. the series `(1)` converges in every defining bounded-set energy
   seminorm;
2. boundaries have zero relative harmonic energy;
3. simultaneous local zero energy classifies boundaries:
   \[
    \bigl(\forall\alpha,\ \mathcal E_\alpha(x)=0\bigr)
      \quad\Longleftrightarrow\quad
    x\in B^1_{\mathrm{arith}}.                                \tag{2}
   \]

Consequently
\[
  \mathcal E_{\mathrm{arith}}(x)=0
    \quad\Longleftrightarrow\quad
  x\in B^1_{\mathrm{arith}},                                  \tag{3}
\]
so `(1)` descends to a positive-definite form on
\[
  H^1_{\mathrm{arith}}
  =
  Z^1_{\mathrm{arith}}/B^1_{\mathrm{arith}}
  \cong M_\zeta.
\]

## Proved abstract passage

`[PROVED] [DAC_GLOBAL_GREEN_ENERGY_RADICAL_PASSAGE]`

For any summable family of nonnegative local energies, if boundaries
are locally zero and simultaneous local zero is equivalent to being a
boundary, then the summed energy has radical exactly the boundary
submodule.  No uniform local coercivity constant is required.

This is formalized as
`RHTower.deningerTsumEnergy_eq_zero_iff_mem_boundaries` in
`GaloisForLFunctions.RHTower.DeningerArithmeticPositiveCalderonKoszul`;
required direct-file Lean check passes.

Closed-boundary passage is also abstractly complete:
`RHTower.deningerContinuousEnergy_zero_on_boundaryClosure` proves
that a continuous energy vanishing on algebraic boundaries vanishes
on their topological closure.  Thus closure creates no separate
radical problem once continuity in the source graph topology is
proved.

Form-level summability now supplies that continuity.  On a defining
Banach disk \(B\), write \(G_{\alpha,B}\) for the continuous local
Green bilinear form.  The sufficient source estimate is
\[
 [\text{CONJECTURE}]
 [\text{DAC\_ALL\_PLACE\_GREEN\_FORM\_NUCLEAR\_SUMMABILITY}]
 \qquad
 \sum_\alpha G_{\alpha,B}
 \text{ converges in }
 \mathcal L(B,\mathcal L(B,\mathbb R))
 \tag{4}
\]
compatibly over the defining disks.  Under `(4)`, evaluation commutes
with the sum and \(x\mapsto\sum_\alpha G_\alpha(x,x)\) is continuous.
This abstract theorem and a scalar summable-majorant criterion are
formalized in
`RHTower.deningerSummedGreenForm_hasSum_apply_apply`,
`RHTower.deningerSummedGreenEnergy_continuous`, and
`RHTower.deningerLocalEnergy_summable_of_summable_majorant`.

Cauchy restriction descent is also abstractly complete.  If each
full Cauchy restriction carries global boundaries to local
boundaries, it descends to quotient cohomology.  The single remaining
conservativity statement is
\[
 [\text{CONJECTURE}]
 [\text{DAC\_FULL\_CAUCHY\_BOUNDARY\_CLASSIFICATION}]
 \qquad
 \bigl(\forall\alpha,\ r_\alpha(x)
       \text{ is a local boundary}\bigr)
 \Longrightarrow x\in B^1_{\mathrm{arith}}.                  \tag{5}
\]
Under `(5)` and the proved local zero-energy classifications, local
energies jointly detect the global quotient.  This quotient argument
is formalized in
`RHTower.deningerCauchyQuotientRestrictions_eq_zero_iff` and
`RHTower.deningerLocalCauchyEnergy_zero_iff_globalClass_zero`.

## Attack on `(2)`

Let \(x\) be a middle cocycle with every local energy zero.

1. Kummer Dirichlet positivity makes every nonconstant unitary-face
   full Cauchy packet zero.
2. Extended-cusp positivity makes every nonzero prime Fourier packet
   zero while retaining, rather than deleting, the logarithmic
   residue line.
3. Real orientation positivity kills both invariant and
   orientation-anti-invariant nonconstant packets.
4. `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` contracts every finite
   positive-total-degree Tate--Milnor relative cell.
5. `DAC_LOCAL_FULL_CAUCHY_UNIQUENESS` kills local harmonic interiors
   after their full Cauchy packets vanish.
6. Only constant, prime-residue, real-apex, and product-formula
   augmentation packets remain.
7. The strict completed Arakelov endpoint sequence identifies those
   remnants with \(Q\mathcal E^0_{\mathrm{arith}}\) plus the actual
   \(H^0/H^2\) endpoint lines.  Endpoint reduction in middle degree
   removes the latter, proving \(x\in B^1_{\mathrm{arith}}\).
   This endpoint input is already proved by
   `DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`; no new endpoint conjecture
   is needed.

The reverse implication in `(2)` is Green--Stokes plus local harmonic
projection: exact middle cochains have zero relative harmonic Cauchy
energy.

## Exact remaining inputs

1. Prove `(4)` on every defining Banach disk of the mixed restricted
   \(L^1/L^2\) nuclear topology.  This single form-level estimate now
   implies both placewise energy summability for `(1)` and continuity
   needed for closed-boundary passage.
2. Prove the full Cauchy restriction maps commute with every
   Rost--Schmid differential, Milnor attaching map,
   residue/corestriction, and real orientation descent.  This gives
   boundary preservation needed for quotient descent.  Assembly of
   the six componentwise identities into a three-term chain map is
   already formalized by
   `deningerTwoColumnSignatureCauchyChainMap`.
3. Prove the conservative boundary law `(5)`: simultaneous local
   boundary classes leave only the endpoint sector, then apply
   `DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`.
4. Prove Green--Stokes vanishing on algebraic finite-support
   boundaries and continuity of `(1)`; the formal closed-boundary
   passage then applies.

## Consequences

- The global Green form is closable and faithful on
  \(H^1_{\mathrm{arith}}\).
- Its completion is the source-defined positive Hodge Hilbert space.
- The associated Dirichlet-to-Neumann operator is strictly positive,
  even if local spectral gaps tend to zero.
- Together with the constrained Euler--Lagrange identity and local
  Cauchy uniqueness, this proves
  `DAC_ARITHMETIC_CALDERON_GLOBAL_CHIRALITY_KERNEL`.

## Falsifiers

- Defining the Hilbert space by quotienting an unknown null space does
  not prove `(3)` or faithfulness on \(M_\zeta\).
- Dropping logarithmic residue or product-formula channels can enlarge
  the radical.
- Finite-packet positivity alone does not classify the radical after
  closure.
- Orthogonal projective-ray completion before incidence can collapse
  nonzero augmentation classes to zero energy.
- No zeta zero, zero-sector projector, RH premise, CCM object, or
  numerical computation enters `(1)`--`(3)`.

## Gates

- [x] 0 → 1 in-progress: exact radical statement and proof reduction
- [ ] 1 → 2 fully-proven: strict summability and endpoint
  classification
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## References

- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.
- `DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY`.
- `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX`.
- `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION`.
- `DAC_LOCAL_FULL_CAUCHY_UNIQUENESS`.
- `DAC_GLOBAL_CALDERON_CHIRALITY_KERNEL_REDUCTION`.

## Log

- 2026-07-27 — Isolated energy faithfulness as exact radical
  classification `(2)` and formalized nonuniform summable
  local-to-global passage.
- 2026-07-27 — Replaced separate scalar-summability and continuity
  obligations by the sharper all-place Green-form summability
  conjecture `(4)`.  Proved and formalized that summability in the
  continuous-bilinear-map space commutes with evaluation, gives
  continuous global diagonal energy, and follows pointwise from a
  summable packet majorant.
- 2026-07-27 — Formalized Cauchy restriction on quotient cohomology
  and reduced joint global energy detection to the exact conservative
  boundary statement `(5)`.  This separates formal quotient descent
  from the remaining Rost--Schmid/Milnor/Arakelov source theorem.
- 2026-07-27 — Formalized componentwise Cauchy maps on the actual
  two-column Rost--Schmid/signature totalization.  Six local
  commutation identities now assemble automatically into a
  three-term chain map and induced maps on \(H^0,H^1,H^2\).
