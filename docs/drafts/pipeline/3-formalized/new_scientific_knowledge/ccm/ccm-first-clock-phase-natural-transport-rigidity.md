# CCM first-clock phase-natural transport rigidity

- **ID:** `ccm-first-clock-phase-natural-transport-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / ROUTE-A TRANSPORT CLASSIFICATION
- **Source:** Route A terminal audit of the remaining coefficientwise source/response
  intertwiner seam
- **Statement:** A finite prime-power transport preserving the literal critical-Mellin source and
  intertwining every physical first-clock phase is the identity. Every nontrivial source-faithful
  mixer therefore creates a nonzero phase-connection defect at some explicit aperture.
- **RH used:** no
- **Computation used:** no

## Goal

Close the last aperture-independent cross-prime transport proposed for Route A without assuming
source sign, zero location, or a positive factorization. The literal prime-power labels carry the
injective logarithmic clock

```text
h_i = log k_i > 0,
```

and the physical first-clock phase at aperture `L>0` is

```text
s_L(h_i) = sin(2*pi*h_i/L).
```

An aperture-independent transport natural for this physical clock must commute with every
diagonal phase matrix `diag(s_L(h_i))`. Exact source faithfulness requires it to fix the nonzero
critical-Mellin weight vector. The theorem classifies their intersection.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement, hard seam, falsifiers, and complete paper
  proof
- [x] 1 → 2 fully-proven: hostile proof and novelty audits complete
- [x] 2 → 3 formalized: Lean module, umbrellas, direct check, axioms, final SOTA module build
- [ ] 3 → 4 publication-ready: not proposed; generic commutant parent is classical

## Exact theorem

Let `I` be finite, let `h : I -> R` be positive and injective, let `w : I -> R` be nowhere zero,
and let `M` be a real `I x I` matrix. Put

```text
S_L = diag(i |-> sin(2*pi*h_i/L)).
```

Then

```text
M w = w  and  (for every L>0, S_L M = M S_L)
  <->
M = 1.                                                       (1)
```

Consequently, under `M w=w`,

```text
M != 1
  -> exists L>0, S_L M != M S_L.                            (2)
```

The witness is explicit. If `M_ij != 0` for `i!=j`, take

```text
L_ij = 4(h_i+h_j).                                          (3)
```

Both phase arguments lie strictly between `0` and `pi/2`, and strict monotonicity of sine gives

```text
s_(L_ij)(h_i) != s_(L_ij)(h_j).                             (4)
```

Hence the `(i,j)` entry of the commutator is nonzero.

For a duplicate-free finite packet of actual prime powers `k_i`, take

```text
h_i = log k_i,
w_i = Lambda(k_i)/sqrt(k_i).
```

Prime-power support makes every `w_i` strictly positive, and injectivity of `k` plus strict
monotonicity of logarithm makes `h` injective. Therefore `(1)--(2)` apply to the literal
critical-Mellin packet.

## Dependency-closed paper proof `[PROVED HERE]`

### Lemma 1 — physical phases separate every positive clock pair

Fix `a,b>0` with `a!=b` and put `L=4(a+b)>0`. Then

```text
x = 2*pi*a/L = pi*a/(2(a+b)),
y = 2*pi*b/L = pi*b/(2(a+b)).
```

Both `x,y` belong to `(0,pi/2)`. Since their common positive scalar denominator makes
`x=y <-> a=b`, they are distinct. Sine is strictly increasing on `[-pi/2,pi/2]`; hence
`sin x != sin y`. This proves `(4)` without arithmetic approximation.

### Lemma 2 — all-phase naturality kills every off-diagonal entry

Assume `S_L M=M S_L` for every `L>0`. For `i!=j`, injectivity gives `h_i!=h_j`; Lemma 1 supplies
`L_ij>0` with `s_(L_ij)(h_i)!=s_(L_ij)(h_j)`. The `(i,j)` entry of the commutation identity is

```text
(s_(L_ij)(h_i)-s_(L_ij)(h_j)) M_ij = 0.
```

Therefore `M_ij=0`. Thus `M` is diagonal.

### Lemma 3 — source faithfulness fixes the diagonal

For diagonal `M`, the coordinate identity `M w=w` reads

```text
M_ii w_i = w_i.
```

Since `w_i!=0`, `M_ii=1` for every `i`; hence `M=1`. Conversely the identity matrix fixes `w` and
commutes with every `S_L`. This proves `(1)`.

### Corollary — unavoidable connection current

Assume `M w=w` and `M!=1`. If every physical commutator vanished, `(1)` would give `M=1`, a
contradiction. Therefore `(2)` holds. More sharply, source faithfulness implies a nonidentity
matrix cannot be diagonal, so it has an off-diagonal `M_ij!=0`; `(3)` supplies an explicit
aperture detecting the defect.

## Heavy-conjecture tournament and hostile audit

### C0 — positive or nonlinear Dirichlet-convolution transport

Already dead. Infinite operator-valued prime-face rigidity shows that convolution functionals act
through one prime-local differential and cannot mix irreducible prime labels.

### C1 — fixed cross-prime transport commuting with logarithmic clock

Dead by the generic diagonal-commutant theorem already in the corpus. It is too strong because a
candidate might preserve only physical first-clock phases, not the raw logarithmic generator.

### C2 — fixed cross-prime transport commuting with every physical first clock

Killed by `(1)`. This is strictly sharper than C1 at the hypothesis level: raw clock commutation is
not assumed. The entire moving sine family reconstructs enough of the simple clock to force the
same diagonal commutant.

### C3 — aperture-dependent source-faithful transport

Survives only with a nonzero phase-naturality defect. Such a family is not an intertwiner of one
fixed source/response carrier. Its derivative or finite transition must retain the commutator as a
connection current. Positivity of that current is not proved here.

### C4 — remove the defect by post hoc diagonal energy subtraction

Already dead. Route J's one-node unit packet proves that subtracting the diagonal destroys the
normalized anchor-capacity inequality. The counterterm must be inserted before good/bad positive
projection and must be sourced, not normalized away.

## No-go closure

- **Exact killing theorem/mechanism:** physical phase family separates every pair of positive
  logarithmic labels; its common commutant is diagonal, and fixing the nonzero source vector makes
  that diagonal the identity.
- **Strongest positive survivor:** every nontrivial source-faithful cross-prime transport carries
  an unavoidable, explicitly detectable phase-connection defect. This is the exact algebraic
  coordinate a successor construction must orient.
- **New insight:** Route A cannot be preceded by an aperture-independent source/response
  intertwiner, even one allowed signed entries and requiring naturality only for physical sine
  clocks. A viable successor is necessarily connection-valued/aperture-dependent and is therefore
  a different mechanism from the advertised coefficientwise intertwiner.
- **Status:** paper and Lean proofs dependency-closed. Generic diagonal-commutant and sine
  monotonicity parents are classical; novelty claim is limited to the physical-family
  classification, literal CCM source specialization, and unavoidable connection-defect
  consequence. Formal certificate:
  `RHTower/CCMFirstClockPhaseNaturalTransportRigidity.lean`.

## Anti-theatre boundary

This theorem does not prove a lower floor, source nonnegativity, or RH. It does not exclude an
aperture-dependent nonlinear construction carrying a new oriented connection current. Calling
the identity transport a positive factorization would be circular: its scalar compression is the
original RH-equivalent first-clock source.

## Falsifiers

- positive injective labels and a nonidentity matrix fixing a nowhere-zero source vector while
  commuting with every `S_L`;
- distinct positive labels whose phases agree at `L=4(a+b)`;
- an actual prime-power packet with a zero critical-Mellin weight.

## Lean certificate

The module proves explicit phase-pair separation at `L=4(a+b)`, combines it with the diagonal
commutant classification, proves source-faithful identity and nontrivial-transport defect, and
specializes to duplicate-free prime-power packets. It is wired into `RHTower.lean` and
`RiemannHypothesisSOTA2026.lean`.

Audited endpoints:

```text
ccmFirstClockPhaseNatural_sourceFaithful_iff_eq_one
ccmFirstClockPrimePowerPacket_phaseNatural_sourceFaithful_iff_eq_one
ccmFirstClockPrimePowerPacket_nontrivial_has_explicit_phaseConnectionDefect
```

`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passed 9,960 jobs. Scratch
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-01 — frozen after internal no-go audit and primary-source review of Suzuki, CCM, and
  finite Guinand--Weil constructions; no checked source supplies the missing global source floor.
- 2026-08-01 — paper proof formalized, both umbrellas wired, direct check and SOTA build passed;
  promoted to Stage 3.
