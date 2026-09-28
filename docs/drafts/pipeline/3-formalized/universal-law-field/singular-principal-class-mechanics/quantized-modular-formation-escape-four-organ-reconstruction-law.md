# Quantized modular-formation escape and four-organ principal-class reconstruction

- **ID:** ULF-SPCM-01
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** dependency-closed paper proof; Lean formalisation complete
- **Statement:** Gamma-six boundary residue, Möbius prime-normal double-log energy, resolved Green codiagonal survival, and reflected Kakutani escape reconstruct one reflection-even principal class.

## 1. Common invariant

For an actual multiplicity-labelled Xi divisor copy `q`, write

\[
 a(q)=2\operatorname{Re}(q)-1
\]

for its centered modular rate and `B(q)` for its signed theta rank-two boundary flux. Corpus gives

\[
 B(q)=-M(q)a(q), \qquad M(q)>0.                    \tag{SPC.1}
\]

Define the principal escape class

\[
 I(q)=\begin{cases}0,&B(q)=0,\\1,&B(q)\ne0.\end{cases}             \tag{SPC.2}
\]

By `(SPC.1)`,

\[
 I(q)=\mathbf 1_{a(q)\ne0}.                         \tag{SPC.3}
\]

Thus `I` is not another scalar approximation to horizontal displacement. It is the support class
obtained after positive cofinal formation forgets the size and sign of every nonzero modular
charge but retains whether that charge survives.

## 2. Four-organ reconstruction law

### Theorem 2.1 -- Gamma-six principal residue

For every depth `m>=1`, the literal filtered Gamma-six second boundary jet `J_{m,p}(q)` satisfies

\[
 \lim_{p\to\infty} pJ_{m,p}(q)
   ={\log 2\over m^2}I(q).                           \tag{SPC.4}
\]

### Theorem 2.2 -- Möbius prime-normal principal residue

Let `E_N(q)` be ordered physical Möbius prime-normal half-density energy through the `N`th prime.
Then

\[
 \lim_{N\to\infty}{E_N(q)\over\log\log N}=I(q).     \tag{SPC.5}
\]

### Theorem 2.3 -- resolved Green zero stratum

For every retained prime `p`, let `G_p(q)` be actual adaptive resolved Green codiagonal. Then

\[
 G_p(q)=0 \quad\Longleftrightarrow\quad I(q)=0.       \tag{SPC.6}
\]

### Theorem 2.4 -- reflection-pair unsigned escape

Let `K_S(q)` be finite-prime Kakutani/Hellinger polarization normalized by reciprocal-prime mass.
For the functional-equation reflected copy `q*`,

\[
 \lim_{S\uparrow\mathbb P}\bigl(K_S(q)+K_S(q^*)\bigr)=2I(q).       \tag{SPC.7}
\]

Reflection reverses signed modular charge but preserves `I`; positive completion therefore adds
two escape units instead of cancelling them.

## 3. Proof

Equation `(SPC.1)` is the exact theta-flux factorization already proved in the corpus; positivity
of theta mass and root energy gives `(SPC.3)`.

For `(SPC.4)`, the Gamma-six coefficient theorem gives

\[
 pJ_{m,p}(q)\longrightarrow R_m(a(q)),\qquad
 R_m(t)=\begin{cases}0,&t=0,\\ \log 2/m^2,&t\ne0.\end{cases}
\]

Substitute `(SPC.3)`.

For `(SPC.5)`, if `I(q)=0`, every physical half-density amplitude is zero. If `I(q)=1`, corpus
gives the exact coefficient decomposition

\[
 A_p(q)^2={1\over p}-D_p(q),\qquad D_p(q)\ge0,qquad\sum_pD_p(q)<\infty.
\]

Mertens' prime harmonic law gives `sum_{p<=p_N}1/p ~ log log N`; the summable correction divided
by `log log N` tends to zero. Hence the limit is one.

For `(SPC.6)`, resolved Green comparison gives `G_p(q)=0` exactly when
`Re(q)=1/2`. This is `a(q)=0`, hence `I(q)=0` by `(SPC.3)`.

For `(SPC.7)`, the one-copy quantized Kakutani theorem gives limit `I(q)`. Functional-equation
reflection sends `B(q)` to `-B(q)`, so `I(q*)=I(q)`. Add the two limits. QED.

## 4. Higher-law interpretation

The mechanism is a formation tropicalization:

\[
 \text{signed modular charge }a
 \longmapsto \text{positive cofinal energy}
 \longmapsto \text{principal class }\mathbf1_{a\ne0}.              \tag{SPC.8}
\]

This explains four corpus-wide facts without route vocabulary:

1. positivity is a phase quotient: it erases sign but retains survival;
2. reflection cancels oriented current but doubles unsigned principal escape;
3. hypertranscendental/cofinal noncompactness appears as a universal harmonic principal part;
4. ordinary Hilbert, trace-class, or signed-Fredholm comparisons miss the surviving class.

The relevant comparison category is therefore sequences or relations modulo summable error, not
ordinary bounded maps between completed Hilbert marginals.

## 5. Exact RH interface and limitation

From `(SPC.3)`,

\[
 \forall q,\ I(q)=0 \quad\Longleftrightarrow\quad RH.              \tag{SPC.9}
\]

The theorem does not prove the left side. It proves that four previously separate organs carry
one principal class and fixes the only viable source interface: construct a pre-divisor arithmetic
formation morphism that

1. lands in the singular principal-class quotient;
2. preserves the coefficient of the reciprocal-prime harmonic class;
3. makes the completed Xi-zero output principal-exact.

Such a morphism would send the source class to zero at every Xi-zero fibre while `(SPC.4)`--`(SPC.7)`
force the same class to equal `I(q)`, proving `(SPC.9)`. Ordinary `L2` convergence, bounded
same-completion annihilation, scalar codiagonal cancellation, or a reflection-odd index cannot
substitute for this law; corpus no-gos already exclude them.

## Gates

- [x] exact common zero/nonzero class
- [x] Gamma-six prime-end reconstruction
- [x] Möbius double-log reconstruction
- [x] resolved Green reconstruction
- [x] Kakutani reflected-pair reconstruction
- [x] Lean formalisation
- [ ] source-native singular principal-class descent
- [ ] RH consequence

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.XiFormationEscapePrincipalClassLaw`, `GaloisForLFunctions.RHTower.XiFormationStratificationLaw`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.RHTower.XiFormationEscapePrincipalClassLaw` (8 constants) and `GaloisForLFunctions.RHTower.XiFormationStratificationLaw` (18 constants); axiom audit clean (transitively). `a(q)` is `primeDepthBVWoldXiCenteredRate q.1` (`= 2 Re q - 1`), `B(q)` is `thetaXiRankTwoBoundaryFlux q`, `I(q)` is `thetaKakutaniHarmonicEscapeIndex q`.

| Claim | Lean declaration |
|-|-|
| (SPC.1) `B(q) = -M(q) a(q)`, `M(q) > 0` | `thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate`, `thetaXiFluxMassEnergy_pos` |
| (SPC.2) principal escape class | `thetaKakutaniHarmonicEscapeIndex` |
| (SPC.3) `I(q) = 1_{a(q) ≠ 0}` | `thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero`, `thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_centeredRate_eq_zero`, `thetaKakutaniHarmonicEscapeIndex_eq_indicator` |
| Thm 2.1 (SPC.4) Gamma-six residue `p J_{m,p}(q) → (log 2/m²) I(q)` | `gammaSixFilteredBoundaryAsymptoticResidue_eq_escapeIndex`, `tendsto_gammaSixFilteredBoundarySecondJet_harmonic_residue_escapeIndex` |
| Thm 2.2 (SPC.5) `E_N(q)/log log N → I(q)` | `tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_escapeIndex` |
| Thm 2.3 (SPC.6) `G_p(q) = 0 ⟺ I(q) = 0` | `adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_escapeIndex_zero` |
| Thm 2.4 (SPC.7) reflected pair `→ 2 I(q)`; `I(q*) = I(q)` | `tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass_escapeIndex`, `thetaKakutaniHarmonicEscapeIndex_reflect` |
| Four-organ law | `xiFormationEscapePrincipalClass_fourOrganLaw` |
| (SPC.9) `∀ q, I(q) = 0 ⟺ RH` | `forall_thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_riemannHypothesis` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
