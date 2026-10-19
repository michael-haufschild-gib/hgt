# APT complete-form estimates and detection

- **ID:** APT-REVIEW1910-A1-A3
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME / OPEN
- **Source:** ../../../reports/review-1910/astra.md, §3
- **Statement:** Resolve A1–A3 for an explicit arithmetic family, retaining the complete signed form and the parameter costs needed to enlarge the family.

## Requirements

- [x] **A1:** An explicit unit singleton is negative for the complete limiting critical prime form, with margin `4log2/(390π⁴)`. This concerns the prime channel; the prime–Gamma–polar Weil sign remains separate.
- [ ] **A2:** Prove a quantitative approximation theorem for the chosen family controlling prime, Gamma, and polar errors jointly. State support, aperture, coefficient, and scale dependence; fixed-pattern convergence alone is insufficient.
- [ ] **A3:** Prove detection or a scoped failure of detection on explicit off-line configurations. Retain the diagonal budget and reflection defect. A model theorem is not a statement about all arithmetic axioms of zeta.
- [ ] Audit implications, strongest positive survivors, existing-corpus priority, and scientific significance.
- [ ] Formalize dependency-closed conclusions without additional mathematical premises or axioms; wire leaves and run direct-file Lean/axiom/lint audits.

## Established input and first open dependency

The complete translated prime limit, harmonic charge classification, common-density
formula, continuous reflected cell kernel, and exact positive weight mass already
exist. Reuse the modules named in
`apt-critical-prime-kernel-signature-2026-10-19.md`; do not repeat their construction.
That prior card is a historical paused task; the present request resumes its sign
question under the broader A1–A3 scope.

For the singleton pattern, the old analytic candidate isolates the negative charge
at harmonic two and bounds every positive harmonic plus the infinite tail. Its
finite rational bookkeeping was checked, but its harmonic estimates were not.
The combined Lean proof now establishes a negative singleton with an explicit
margin, without a sign premise. **[A1 COMPLETE]** The installed
`FactorialCriticalPrimeSingletonNegative.lean` retains every harmonic and passes
its actual-file check with an empty log. All twenty-six public A1 results have
only `propext`, `Classical.choice`, and `Quot.sound` in their axiom reports.
Global lint has unrelated umbrella-reachability errors, detailed below.

**[OPEN CORE A2]** Control the complete receiving form in a joint growing regime;
the existing critical physical affine error does not control the prime form by itself.
**[OPEN CORE A3]** Match the selected family and its normalization to an explicit
off-line model and prove a negative complete-form readout or a sharp detection boundary.

## Proof and audit discipline

No numerical experiments, full/umbrella builds, heartbeat increases, commits, or
changes to concurrent work. One owned foreground Lean process at a time. Use
`lake --old env lean <actual-file>` for final audits and `/tmp` for API/axiom probes.
Persist crisp reusable facts and failures in `logs/apt-review1910-knowledge.md`.
Keep research changes in this card, owned Lean leaves, and their umbrella imports.
Persisted corpus-only instructions preclude an external novelty certification here.

## Plan

1. Audit native harmonic bounds and complete-form/detection machinery in the corpus.
2. Close a dependency-closed analytic sign argument, then formalize it.
3. Derive full-form approximation costs and test detection without discarding signed terms.
4. Audit every requirement against actual theorem statements and verification output.

## Dependency-closed small-harmonic argument

Write `a=π/6` and `γ(u)=u⁻²(1−cos(au))`. The existing singleton/common-tail
and exact-mass theorems give, for every natural `m`,
`J_m=m(π²/12−∫₀ᵐγ(u)du)`, including `m=0` directly.
The corpus's global alternating cosine inequalities give, for `u>0`,

`a²/2−a⁴u²/24+a⁶u⁴/720−a⁸u⁶/40320 ≤ γ(u)`

`γ(u) ≤ a²/2−a⁴u²/24+a⁶u⁴/720`.

The value at zero is immaterial to integration. Integrate these polynomials and
use the exact head identity. With `θ=πm/6`, the resulting bounds are

`πθ/2−θ²/2+θ⁴/72−θ⁶/3600 ≤ J_m`

`J_m ≤ πθ/2−θ²/2+θ⁴/72−θ⁶/3600+θ⁸/282240`.

Specialization to `m=2,3,5,6`, with `157/50<π<22/7`, gives respectively
`J₂≥10/9`, `J₃≤4/3`, `J₅≤4/3`, and `J₆≤7/6` by rational inequalities.
This proof uses the complete native harmonic mass; it has no Laplace-transform
premise. These four bounds are support for the pending sign argument, not a
complete sign theorem or a novelty claim.

**Lean support result:** `FactorialCriticalHarmonicTaylorBounds.lean` proves the
exact head identity, both global Taylor inequalities, and all four displayed
small-harmonic bounds. The actual file passed `lake --old env lean -j 1 -o ...
-i ... <actual-file>` and is umbrella-imported. Two redundant-tactic warnings
were removed; the final actual-file recheck passed with an empty log
(`/tmp/apt_review1910_taylor_actual.log`). The axiom audit passed; global lint is
non-green only for the foreign modules listed below.

## Oscillatory tail replacement

For `p>1`, define `C_p(θ)=∫₁∞v⁻ᵖ cos(θv)dv` and
`S_p(θ)=∫₁∞v⁻ᵖ sin(θv)dv`. Absolute integrability gives
`|C_p|,|S_p|≤1/(p−1)`. Integration by parts, with vanishing boundary at infinity,
gives `θ C₂=−sin θ+2S₃` and `θ S₃=cos θ−3C₄`.
Consequently the native defect, at `θ=πm/6>0`, satisfies

`|J_m−1|≤2/θ`,

`J_m≤1+sin θ/θ+2(1−cos θ)/θ²`.

These bounds replace the unproved Laplace representation. The first gives
`J_m≤6/5` for `m≥20`, a slightly larger infinite-tail budget than the prior
candidate's `11/10`. The second retains the phase needed for harmonics
`7,9,10,11,13,14,15,17,18,19`. The final arithmetic budget must be recomputed
symbolically with `6/5`; the old margin cannot be reused unchanged.

The old tail coefficient `671/86640` is replaced by `61/7220`, using
`log19≤(13/3)log2` and `log2≥2/3`. The increase is `61/86640`.
Since `1/300−61/86640>1/390`, the proposed complete singleton budget still
has room for `Σ A(m)J_m/m⁴≤−log2/390`. This is exact rational bookkeeping,
conditional only at the planning level on the analytic estimates still being
formalized; it is not a Lean endpoint or an imported theorem premise.

The oscillatory recurrences, inverse-frequency error, and phase-sensitive bound
pass Lean in scratch. `FactorialCriticalHarmonicOscillationBounds.lean` installs
these proofs together with the `6/5` cutoff at twenty and `7/6` cutoff at nineteen;
its actual-file Lean check passed. For the latter cutoff, `θ≥19/2` and
`θ sin θ+2(1−cos θ)≤θ+4≤θ²/6`. These are native defect bounds, not a sign decision.

For the remaining finite phases, the same inequality gives `J₉,J₁₀,J₁₁≤1`
and `J₇,J₁₃,J₁₄,J₁₅,J₁₇,J₁₈≤7/6`. Reduce their angles modulo `2π`, use
`1≤√3≤7/4`, and bound the resulting quadratic with `π>3` (`π>157/50` for
harmonic fifteen). No phase averaging or independent selection of masses occurs.
`FactorialCriticalHarmonicFiniteBounds.lean` passes its actual-file Lean check
and is umbrella-imported. The logarithmic remainder follows from the antitone integral test and
`∫₁₉∞log(x)/x³ dx=(log19+1/2)/722`. Exact integer-power comparisons give
`log3/log2≤8/5`, `log5/log2≤7/3`, `log7/log2≤17/6`,
`log11/log2≤7/2`, `log13/log2≤15/4`, `log17/log2≤25/6`, and
`log19/log2≤13/3`. Together with `log2≥2/3`, these yield the unweighted remainder
`Σ_(m≥20)log(m)/m³≤(61/8664)log2`.

The complete proposed certificate keeps composite charges exactly:
`A₆=3log3−2log2`, `A₉=12log3`, `A₁₀=5log5−2log2`,
`A₁₄=7log7−2log2`, `A₁₅=3log3+5log5`, `A₁₈=12log3−2log2`.
The terms at `0,1,4,8,12,16` vanish. Summing every term below twenty with
the proved harmonic bounds gives at most `(-61/7220−1/390)log2`;
the entire remaining tail is at most `(61/7220)log2`. Thus the paper argument
gives the unconditional negative singleton witness
`P∞≤−(4/(390π⁴))log2<0`. Scratch and installed-leaf Lean checks passed.
Evidence: `/tmp/apt_review1910_singleton_actual.log` (empty, exit zero).
All twenty-six A1 axiom reports are standard. The full Weil form subtracts the prime channel,
so this does not assert negativity of the prime–Gamma–polar form or prove RH.

## A2 endpoint and next paper obligations

The native critical source is `u(x)=1_(x≤0) exp(x/2) F(exp(-x))`. Its phase has
`|F|≤B`, slope bound `D`, and a bounded primitive `G`, `|G|≤C`, where the
existing source estimates give `B=2Σ|b_n|`, `D=14Σ(n+1)|b_n|`, and
`C=12Σ|b_n|/(n+1)`. The critical weight corresponds to weighted-tail abscissa
`-1/2`, outside the existing Gamma theorem's strip `[-1/4,5/4]`.

For integer cutoff `K≥3`, truncate to `[-log K,0]`. Integration by parts predicts
the following complete prime error, with `L=log K`:

`|P(u)−P(u_K)|≤(C/K)[2B(1+2L)+D(1+L)²]`.

Indeed, for `r≤K` the omitted correlation begins at `v=K/r`, and its bound is
`(C/r)[2B(r/K)²+D(r/K)]`; include the full `Λ(r)/r` weight before summing.
For `r>K`, keep the entire correlation and the existing inverse-square prime
majorant. These estimates remain paper obligations, not imported premises.

The difficult polar endpoint is the improper integral `∫₁∞F(v)/v dv`.
Its proposed definition is `−G(1)+∫₁∞G(v)/v² dv`; integration by parts should
give cutoff error `≤2C/K`. Do not use the ordinary Lebesgue integral of `F(v)/v`
without proving absolute integrability. The other polar feature has absolute
tail bound `B/K`.

For Gamma, set `M≥1` with `D≤MB`; the actual family can take
`M=7(1+max S)`. The pending critical translation proof uses
`Cτ=12+2exp(2)` and aims at
`||u(·+h)−u||₂²≤Cτ B² min(1,Mh)` for `h≥0`.
For `0<Mh≤1`, split at `x=log(Mh)`: the bounded phase contributes
`8B²Mh`, the squared Lipschitz estimate contributes `2B²Mh`, the boundary
interval contributes `B²h`, and amplitude variation contributes at most
`2exp(2)B²h²`. For `Mh≥1`, use the mass bound `4B²`.
The existing one-power phase estimate loses integrability at this weight.

The known Gamma kernel satisfies `w(h)≤1/h` on `(0,1]` and has finite tail
mass `W=∫₁∞w`. Thus the positive physical Gamma graph energy should be at most
`CΓ B²(1+log M)`, where `CΓ=1+Cτ+4W`. The omitted physical tail is a translate
of a source with amplitude `B/√K` and clock scale `MK`; its Gamma graph cost is
at most `CΓ B²(1+log K+log M)/K`.

Keep quadratic cross terms via the pointwise inequality
`|a²−b²|≤η b²+(1+η⁻¹)(a−b)²`. Choosing `η=K⁻¹/²` gives a cutoff error of
order `B²(1+log K+log M)/√K`, rather than mistaking the tail's squared energy
for the quadratic error. These Gamma statements remain to formalize and connect
to the exact complete Weil normalization.

For smoothing radius `ε≤1/M`, contraction of translation increments suggests
Gamma error energy `O(B²Mε(1+log(1/ε)))`. A uniform autocorrelation error
`O(B²√(Mε))` then controls **all** prime terms in aperture `log K+2ε`, with cost
`O(B²K(1+log K)√(Mε))`; the compact polar term is controlled at the same scale.
The explicit regime `K≈M²`, `ε≈1/(MK⁴)` would allow growing support and slow
coefficient growth. Constants, source admission, the full signed assembly, and
off-line detection remain obligations. No A2 or A3 conclusion follows yet.

The full twenty-candidate/twenty-source screen of the cached query
`critical factorial Gamma polar full Weil translated tail approximation` found
the existing weighted-tail strip estimates and compact smoothing limits, not
the missing critical joint estimate. Coverage: inventory complete, compiler
snapshots largely pending/stale; no absence or novelty claim. Evidence:
`/tmp/apt_review1910_full_critical_search.json`.

## Audit checkpoint

The four A1 leaves are umbrella-imported and pass direct actual-file Lean checks.
The twenty-six-public-declaration axiom audit passed; evidence:
`/tmp/apt_review1910_axioms.log`. `scripts/formal_tools.py lint`
returned one because eight concurrent modules are unreachable from their own
umbrellas: five BiScaleUncertainty, two BezoutValuationIncidence, one
SquareRootThreshold. No A1 module is named among the errors. These foreign files
are preserved; there is no global-green claim. Evidence:
`/tmp/apt_review1910_lint.log`. Scoped `git diff --check` passed.

## A3 reuse and remaining diagonal obligation

The direct critical-tail route still needs its full Gamma cutoff bound and a
uniform lattice diagonal. An alternative within the existing arithmetic source
construction is the finite translated span of `factorialSourceRight n` (the
exponential tent), followed by the corpus mollifier. This is an explicit family
extension; it does not assert a full-form comparison for the critical tails.

For compact real sources `f,g`, put `D=∫|f−g|`. The exact translated cross-term
identity gives
`|R_f(t)−R_g(t)|≤(M_f+M_g)D` and
`|(R_f(0)−R_f(t))−(R_g(0)−R_g(t))|≤(K_f+K_g)D|t|`,
where `M` and `K` bound values and Lipschitz constants. Thus the Gamma error is
at most `D[|gammaBracket 0|(M_f+M_g)+J(K_f+K_g)]`, with the corpus's finite
universal moment `J=∫₀∞t exp(t/2)/sinh(t) dt`. If both sources vanish outside
`[-A,A]`, choose `N=ceil(exp(2A+1))`; the complete prime–polar error is at most
`mass(N)(M_f+M_g)D`. The actual Weil energy includes twice that pairing.
No prime or polar term is discarded.

For `f=Σ b_i factorialSourceRight(n_i)(·−t_i)`, native bounds give
`M=30Σ(n_i+1)|b_i|`, `K=2000Σ(n_i+1)²|b_i|`, and finite aperture
`R=1+Σ|t_i|`. Mollification has radius `r_k=1/[4(k+1)]`, preserves `M,K`,
and has `D≤2(R+1)Kr_k`. The resulting full-form error is
`4(R+1)Kr_k[M(|gammaBracket 0|+2mass(N))+JK]`,
with `A=R+1` and the preceding explicit `N`. This proves a joint growing
regime once the displayed bound tends to zero; formalization remains open.

For detection, use `f(x)=β(x+L/2)−β(x−L/2)`, with `β` a smoothed native
tent. Every on-line lattice readout at `2πk/L` vanishes exactly. At the
specified pair `1/2±δ+2πi/L`, the finite-difference multipliers have opposite
real signs. If the tent collar plus smoothing radius is at most `L/(8π)`,
its two tilted readouts lie in a common sector of half-angle at most `1/4`;
their mixed real product is strictly positive. The remaining pair therefore
has negative Weil value. Its square diagonal and reflection defect must be
recorded explicitly: the on-line budget is zero, and the finite pair's defect
exceeds its diagonal. This is a paper strategy, not yet an audited theorem.

The direct critical-source/detection query returned no useful mechanism beyond
the source definition. A rephrased, fully screened twenty-candidate/twenty-source
query recovered `factorialMuntzCorrectedTail_readout_eq_primitive` and
`factorialMuntzCorrectedTail_readout_decay` in
`BiScaleUncertainty/FactorialMuntzTailReadoutDecay.lean`. Their actual statements
and proofs were read. The hypothesis `-1<Re(s)` accommodates the shift `s↦s−1`
when the critical readout has `Re(s)>0`; reuse these theorems before rebuilding
complex integration by parts. Evidence:
`/tmp/apt_review1910_critical_readout_search.json` (inventory complete; compiler
coverage mostly pending/stale; no novelty inference).

Bounded primitive estimates can make every readout on a fixed finite off-line
configuration tend to zero under high arithmetic translation. Such decay alone
does **not** prove failure of detection: the full diagonal background and
reflection defect must be compared in the same normalization. That comparison
remains open.
