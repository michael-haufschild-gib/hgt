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

There is now also a sharp necessary topology condition.  Operator-norm summability in one Banach
disk forces the norms of the local forms to tend to zero.  Therefore no fixed disk may contain
unit-norm packets whose own-place Green diagonal is identically one.  This is proved and formalized
by `DAC_ALL_PLACE_GREEN_FORM_UNIFORM_PACKET_NO_GO`.  Applied to graph-normalized prime packets,
`(4)` requires an explicit high-prime disk-gauge escape theorem or arithmetic damping of the local
diagonal; graph coercivity alone cannot prove `(4)`.

Absolute scalar majorants are not the only admissible mechanism.  The same formalized result gives
an orthogonal maximum-tail criterion: if every finite disjoint packet sum has norm bounded by the
largest packet norm, then local form-norm decay is equivalent to unordered operator-space
summability.  This is the correct candidate for the prime graph direct sum.  Its natural local
bound is `(log p)^(-2)`, which tends to zero but is not scalar-summable over primes (the latter
divergence is already formalized by `tendsto_primeReciprocalLogSqSum_atTop`).  Therefore the prime
sector must use graph orthogonality/max-tail control, not the scalar summable-majorant criterion.

That candidate is now instantiated exactly on the orthogonal prime coordinate model
\(\ell^2(\mathbb P)\). Each local continuous Green form has norm \((\log p)^{-2}\); arbitrary finite
prime sums satisfy the maximum-tail bound; and the unordered form series converges in operator
norm. Separately, every unit-Green packet has graph cost at least \((\log p)^2\), hence escapes
every fixed graph disk cofinally. These theorems close the prime-diagonal functional-analysis
problem; the summed coordinate energy is nonnegative and has zero radical. They do not prove that
the actual mixed restricted arithmetic source decomposes as this
orthogonal model or that cross-prime Milnor/cup incidence preserves its maximum-tail estimate.

`DeningerGreenFormPullbackTransport` sharpens that remaining comparison. Any bounded linear map
\(U:E\to\ell^2(\mathbb P)\) pulls the already-summable local family back to an operator-norm
summable family on \(E\); pullback commutes with the unordered sum. The transported energy is
nonnegative and its radical is exactly \(\ker U\). Therefore cross-prime incidence need not satisfy
a second termwise maximum-tail proof. A sufficient arithmetic target is a bounded comparison map
whose kernel is the closed middle-boundary subspace. Constructing such a map is one concrete
full-packet Cauchy/Bessel proof of the radical theorem, not a necessary definition of the Green
form and not Route L's first source theorem.

There is also a formal obstruction to using only this scalar comparison. Packet averaging is a
bounded functional, and its pulled-back positive Green energy is exactly `Av_p(f)^2`; its radical
is the entire mean-zero packet subspace. A clopen packet piece of intermediate mass gives an
explicit nonzero zero-energy vector. Since the one-prime coefficient calculation retains these
mean-zero modes in middle degree, one scalar coordinate per prime is not a faithful Route L source
map. The comparison must include packet Fourier/transverse coordinates, or the arithmetic boundary
classification must prove those modes exact.

The full-fibre repair is now formalized. Give each prime an arbitrary complete real Hilbert packet
fibre \(K_p\). Identity-on-fibre block Green forms weighted by \((\log p)^{-2}\) retain every
mean-zero/Fourier mode, satisfy the same finite maximum-tail estimate, and sum in operator norm on
\(\ell^2(\mathbb P;K_p)\); the summed energy has zero radical. A source family
\(r_p:E\to K_p\) assembles to a bounded comparison exactly under a global Bessel estimate. The
pulled-back energy then obeys
\[
 G_E(x,x)=\sum_p(\log p)^{-2}\|r_p x\|^2,
 \qquad
 \operatorname{rad}G_E=\bigcap_p\ker r_p.
\]
Thus prime-sector `(4)` is reduced to two source statements with no hidden functional analysis:
the Bessel estimate and \(\bigcap_p\ker r_p=B^1_{\mathrm{arith}}\). Generic and real packets must
either be added as further Hilbert blocks with their own Bessel estimates or handled by a separate
summable finite-sector form.

For the already constructed quotient packet, the fibre is now fixed canonically as normalized
Haar \(L^2(U_p/\overline{\langle p\rangle},\mathbb R)\). The full-block summability and
zero-radical theorems specialize unconditionally to these fibres. This removes freedom to choose a
divisor-adapted target metric. It still does not construct arithmetic full-Cauchy restriction maps
into Haar \(L^2\), prove their Bessel estimate, or classify their simultaneous kernel.

Cauchy restriction descent is also abstractly complete. If this proof method is used and each
full Cauchy restriction carries global boundaries to local
boundaries, it descends to quotient cohomology. Its remaining
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

1. Prove `(4)` on every defining Banach disk of the actual mixed restricted
   \(L^1/L^2\) nuclear topology. Quantitative graph-disk escape and the full
   maximum-tail estimate with exact \((\log p)^{-2}\) local norms are proved on the orthogonal
   full-packet block model. Bessel assembly proves it is enough to construct the local full-packet
   restrictions and establish their square-sum bound on each relevant source disk. The comparison
   kernel is automatically their simultaneous kernel. Remaining work is the arithmetic Bessel
   estimate and compatibility with residue, corestriction, Milnor, cup, generic, and real sectors.
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
- 2026-08-01 — Proved and formalized the all-place uniform-packet no-go: form-level operator-norm
  summability forces local form norms to vanish, so unit-normalized prime packets must escape every
  fixed defining disk or acquire explicit arithmetic damping.
- 2026-08-01 — Formalized the orthogonal maximum-tail survivor: local form-norm decay is sufficient
  for unordered operator-space summability under disjoint maximum-tail control, even when scalar
  norm majorants diverge.  This isolates the exact prime graph estimate still needing arithmetic
  instantiation.
- 2026-08-01 — Instantiated that survivor on \(\ell^2(\mathbb P)\): exact local norm
  \((\log p)^{-2}\), finite maximum-tail control, unordered operator-norm convergence, and a
  continuous faithful summed form with zero radical. Also proved the complementary unit-Green graph cost lower bound
  \((\log p)^2\to\infty\). Actual source-disk and cross-sector comparison remain open.
- 2026-08-01 — Formalized bounded pullback transport. Any source-to-prime comparison inherits
  unordered form summability, and transported global Green radical is exactly comparison kernel.
  This reduces prime-sector radical classification to constructing the arithmetic comparison with
  kernel equal to closed middle boundaries.
- 2026-08-01 — Formalized scalar-residue insufficiency: bounded packet-average Green energy has
  radical exactly the mean-zero packet subspace, with an explicit nonzero witness. Therefore a
  faithful source comparison must retain nonconstant packet modes or prove them boundaries.
- 2026-08-01 — Formalized the full-Hilbert-packet repair and Bessel restriction assembly. Prime
  Green summability and radical classification now reduce exactly to a source Bessel inequality
  and simultaneous-local-kernel boundary theorem.
