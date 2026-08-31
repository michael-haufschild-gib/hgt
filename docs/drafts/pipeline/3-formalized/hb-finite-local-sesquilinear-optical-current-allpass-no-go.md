# Finite local sesquilinear optical currents cannot detect the theta-Hawking all-pass sector

- **ID:** HB-LOCAL-SESQ-ALLPASS-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only), HB differential-boundary survivor; `ThetaCuspHawkingSchwarzianOpticalTheoremEndpoint`
- **Statement:** Every same-frequency sesquilinear current formed from finitely many translation-invariant linear differential channels factors through the input intensity, so every causal theta-Hawking all-pass factor is invisible to the whole class even though its Wigner--Smith clock is strictly positive.

## Goal

Kill, rather than postpone, the remaining HB proposal that increasing differential order or using a
more general local Hermitian/positive optical current could derive the minimum-phase clock rigidity
equivalent to RH.  The proof chain under attack is

`local differential boundary law -> phase-sensitive optical current -> no positive all-pass clock -> minimum-phase rigidity -> RH`.

The theorem severs the first arrow for the maximal finite same-frequency sesquilinear class.  It is
source-pure: the specialization uses the corpus's literal theta-Hawking Born form factor and its
canonical causal all-pass factor.  No divisor is chosen by the reporter.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `d4ThetaCuspHawkingFiniteSameFrequencySesquilinearOpticalCurrentRouteKilled`, targeted `lake build` green, axioms audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Conjecturing loop

### C1 — ellipticity/locality alone forbids chiral leakage — falsified

The corpus already proves that a one-sector symmetric operator forces leakage, while
`ThetaCuspHawkingHBReducedTeukolskyHermitianDilationFidelityNoGo` constructs an unconditional
doubled conservative completion.  Abstract ellipticity, locality, and Hermiticity do not select the
critical wall.

### C2 — sufficiently high local quadratic differential order recovers all-pass phase — falsified

Let `a_j(x)` be the frequency symbol of any finite family of translation-invariant linear
differential channels and let `H_{jk}(x)` be arbitrary complex coefficients.  At a fixed real
frequency `x`, all channels have the form `a_j(x) F(x)`.  The most general same-frequency
sesquilinear current is

`Q_x(F) = sum_{j,k} conj(a_j F) H_{jk} (a_k F)`.

For every complex scalar `F`, commutativity gives the exact classification

`Q_x(F) = normSq(F) * sum_{j,k} conj(a_j) H_{jk} a_k = normSq(F) Q_x(1)`.

Consequently `Q_x(u F) = Q_x(F)` for every `u` of unit norm.  Order, positivity, Hermiticity,
coercivity, and the number of channels are irrelevant; the statement is proved for arbitrary `H`.

### C3 — exact survivor

A phase-sensitive producer must leave this class.  It must use at least one of:

1. a source-fixed external/reference channel that is not dressed by the same phase;
2. cross-frequency or time-bilocal coupling, so the dressing contributes `conj(u(x)) u(y)`;
3. frequency differentiation (the Wigner--Smith clock), which is time-nonlocal;
4. a complex-bilinear, rather than sesquilinear, Green current together with a separately derived
   phase gauge.

Complex-bilinear Teukolsky currents are not claimed blind: under common phase `u` they scale by
`u^2`.  Without a source-fixed gauge that value is not a physical common-phase invariant.  This is
the precise remaining escape, not a loophole in the no-go.

## Paper theorem

For `n : Nat`, symbols `a : Fin n -> Complex`, coefficients
`H : Matrix (Fin n) (Fin n) Complex`, and amplitude `F : Complex`, define

`Q(a,H,F) = sum_j sum_k conj(a_j F) H_jk (a_k F)`.

Then:

1. `Q(a,H,F) = normSq(F) Q(a,H,1)`.
2. If `norm(u)=1`, then `Q(a,H,uF)=Q(a,H,F)`.
3. For every upper theta-Hawking resonant mode `r`, every real frequency `x`, and the literal
   theta form factor `F(x)=XiC(x)`, dressing every channel by the canonical boundary factor
   `B_r(x)` leaves `Q` unchanged, while the canonical clock satisfies `0 < tau_r(x)`.

### Proof

For each summand,

`conj(a_j F) H_jk (a_k F)`
`= conj(F) F * conj(a_j) H_jk a_k`
`= normSq(F) * conj(a_j) H_jk a_k`.

Finite summation proves (1).  Applying (1) to `uF` and using
`normSq(uF)=normSq(u)normSq(F)=norm(u)^2 normSq(F)=normSq(F)` proves (2).

For (3), the already formalized theta-Hawking minimum-phase endpoint proves
`norm(B_r(x))=1` and `0 < tau_r(x)` whenever `0 < Im(r)`.  Substitute
`u=B_r(x)` and `F=XiC(x)` into (2), then use clock positivity.  All quantifiers are internal to the
closed theorem; no existence of an off-line zero is assumed.

`[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** common all-pass phase factors out of every finite
  same-frequency sesquilinear differential current as `conj(u)u=1`.
- **Strongest positive survivor:** exact intensity-factorization theorem plus necessity of a
  reference, cross-frequency/time-bilocal coupling, frequency derivative, or gauge-fixed
  complex-bilinear current.
- **New insight:** the HB differential-boundary survivor is not a question of differential order.
  It is a categorical choice between diagonal/sesquilinear observables and off-diagonal or
  phase-referenced observables.  Higher local Teukolsky current towers cannot help while they are
  evaluated as physical same-frequency Hermitian energies.
- **Status:** paper proof dependency-closed; formalized by
  `d4ThetaCuspHawkingFiniteSameFrequencySesquilinearOpticalCurrentRouteKilled` in
  `ThetaCuspHawkingFiniteSameFrequencySesquilinearNoGo.lean`.

## Novelty and literature audit (through 2026-08-31)

- **Classical input, not claimed new:** Fourier-magnitude phase ambiguity and zero flipping are due
  to Akutowicz (1956/1957), Walther (1963), and Hofstetter (1964).  All-pass/minimum-phase
  factorization is standard signal theory.
- **Current physical context:** Green--Hollands--Sberna--Toomani--Zimmerman
  (`arXiv:2210.15935`, v3 2024) construct an increasing differential-order tower of conserved local
  Kerr/Teukolsky complex-bilinear currents.  Assaad--Macedo (`arXiv:2506.04326`) and
  Ferrer-Sánchez et al. (`arXiv:2608.19774`) treat the Teukolsky QNM problem as a two-dimensional
  elliptic eigenproblem.  Butera (`arXiv:2306.03813`) derives nonlocal moving-mirror dissipation and
  noise kernels.
- **Corpus audit:** exact searches for pointwise phase-invariant quadratic kernels, local
  translation-invariant all-pass blindness, bilocal frequency sensitivity, and finite jet
  reporters found isolated gauge-invariance lemmas and the existing scalar intensity endpoint, but
  no class theorem covering arbitrary finite channel symbols and arbitrary sesquilinear coefficient
  matrices, nor its theta-Hawking clock separation.
- **Novel claim:** the route-level maximal no-go and its exact survivor classification.  No claim is
  made that the underlying one-line sesquilinear algebra is new.

## Falsification attempts

1. **Raise derivative order:** fails because every derivative only changes `a_j(x)`.
2. **Allow arbitrary cross terms or indefinite coefficients:** already included in arbitrary `H`.
3. **Use a Hermitian/positive matrix:** strict subclass of arbitrary `H`.
4. **Use complex-bilinear current:** escapes theorem, but scales by `u^2`; requires a source-fixed
   phase gauge and is recorded as survivor.
5. **Compare different frequencies:** escapes theorem via `conj(u(x))u(y)` and is recorded as
   survivor.

## Log

- 2026-08-31 — created in 1-in-progress after corpus and external SOTA audits; C1 and unrestricted
  C2 rejected, maximal sesquilinear C2 paper-proved.
- 2026-08-31 — formalized exact intensity quotient, arbitrary-symbol/matrix phase invariance, and
  theta-Hawking positive-clock separation; moved to 3-formalized after targeted audit.
