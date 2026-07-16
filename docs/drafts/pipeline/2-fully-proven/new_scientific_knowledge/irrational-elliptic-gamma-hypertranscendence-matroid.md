# Irrational elliptic-gamma hypertranscendence and the exact translation-defect matroid

- **ID:** `irrational-elliptic-gamma-hypertranscendence-matroid`
- **Stage:** 2-fully-proven
- **Type:** SPECIAL-FUNCTION HYPERTRANSCENDENCE / EXACT DIFFERENTIAL MATROID
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — PAPER PROOF]`
  `[SIGNIFICANCE PASS] [EXTERNAL NOVELTY PRELIMINARY] [NOT AN RH RESULT]`
- **Parent proof:**
  `../not_new_scientific_knowledge/paired-quasi-elliptic-constraint-rigidity.md`
- **Formal bridge:**
  `../../3-formalized/not_new_scientific_knowledge/relative-boundary-effectivity-conservativity.md`

## Theorem

Let `tau,sigma` lie in the complex upper half-plane and suppose that

```text
1,tau,sigma are linearly independent over Q.
```

Let `Gamma(z;tau,sigma)` be the standard additive elliptic gamma function and put

```text
F=partial_z log Gamma(z;tau,sigma),
H=Z+Z tau+Z sigma.
```

Then:

1. `F` and `Gamma` are hypertranscendental over `C(z)`.
2. The exact differential-algebraic shift spectrum is

   ```text
   {h in C : Delta_h F is DA over C(z)}=H.                 (1)
   ```

3. If `h_1,...,h_n` represent `m` distinct nonzero cosets of `H`, then

   ```text
   dtrdeg_(C(z)) C(z)<Delta_(h_1)F,...,Delta_(h_n)F>_delta=m.  (2)
   ```

   Repeated cosets contribute no new differential-transcendence degree and the zero coset is
   differential-algebraic.  Thus the complete finite shift-defect matroid is the partition
   matroid of `C/H`, with the zero class deleted from the free part.
4. For `h notin H`, the elliptic-gamma quotient

   ```text
   Gamma(z+h;tau,sigma)/Gamma(z;tau,sigma)
   ```

   is hypertranscendental.

This is a theorem about the actual elliptic gamma function.  The fact that a broader one-pole
constraint class collapses to elliptic gamma does not demote the theorem; it only prevents the
class itself from being advertised as a new family.

## Proof

Write

```text
lambda_tau=partial_z log theta_tau,
lambda_sigma=partial_z log theta_sigma.
```

The elliptic-gamma equations give the compatible paired boundary system

```text
Delta_sigma F=lambda_tau,
Delta_tau F=lambda_sigma.                                  (3)
```

The two right-hand sides are differential-algebraic: their derivatives are elliptic functions.
Let `E_tau,E_sigma` be the elliptic function fields for the lattices `Z+Z tau` and
`Z+Z sigma`, and put `K=E_tau E_sigma`.  Rational independence implies:

- `E_tau` and `E_sigma` are algebraically independent over `C`;
- the common fixed field of the two translations on every field generated below is `C`, because
  a meromorphic function with periods `1,tau,sigma` has a nondiscrete period group and is
  constant.

For any finite family of shifts, each `d_h=Delta_h F` satisfies a compatible unipotent system over
`K`.  The several-automorphism parameterized Picard--Vessiot theory of Hardouin--Singer applies to
this integrable two-translation system.  If the `d_h` were differentially dependent, the proper
differential algebraic subgroup of the additive Galois group would, by Cassidy's classification,
give operators `L_h in C[delta]`, not all zero, and one simultaneous primitive `g in K` such that

```text
Delta_sigma g=sum_h L_h(Delta_h lambda_tau),
Delta_tau   g=sum_h L_h(Delta_h lambda_sigma).              (4)
```

The usual temporary extension of the common constants to a differential closure does not enlarge
the final coefficient field.  Every invariant fraction and every telescoper uses finitely many
coefficients; specialization over the algebraically closed field `C`, followed by normalization
of one nonzero operator coefficient, descends `(4)` to `C`.

View `K` as the function field of the product of the two elliptic curves; what is used here is the
proved algebraic independence of their function fields in the common argument, not abstract
nonisogeny of the curves.  In the first equation of `(4)`, translation by `sigma` acts on the
`E_tau` factor and fixes the `E_sigma` factor.  Specializing the second factor away from the finite
denominator locus produces the same equation with `g_tau in E_tau`.

The function `lambda_tau(z+h)-lambda_tau(z)` has two simple pole classes on the first elliptic
curve.  Their translation-by-`sigma` orbits coincide exactly when `h in H`.  For `h notin H`, the
highest principal-part coefficient of every nonzero `L_h` has nonzero sum on one isolated orbit.
Every coboundary `Delta_sigma g_tau` has zero principal-part sum on each orbit by finite-support
telescoping.  This contradicts `(4)` and proves `(1)`.

For representatives of distinct nonzero cosets, their isolated pole orbits are disjoint.  Choosing
an operator of maximal differential order in `(4)` gives the same contradiction on one private
orbit, proving differential independence and `(2)`.  Hypertranscendence of `F` follows from any
`h notin H`: if `F` were DA, so would be `Delta_h F`.  If `Gamma` were DA, its logarithmic
derivative would be DA.  The quotient statement follows by logarithmically differentiating the
quotient.

## Differential-algebraic anomaly corollary

Let `B` be the multiplicative group of nonzero meromorphic functions DA over `C(z)` and let
`M` be all nonzero meromorphic functions.  For `u in H`, put

```text
a_u(z)=Gamma(z+u)/Gamma(z).
```

Then `a` is a cocycle in `Z^1(H,B)`, its class is nonzero in `H^1(H,B)`, and its image in
`H^1(H,M)` is zero.  Indeed, `Gamma` trivializes it in `M`; any trivialization in `B` would differ
from `Gamma` by a meromorphic function fixed by `1,tau,sigma`, hence by a constant, contradicting
the theorem.  Equivalently, the fixed coset of `Gamma` in `M/B` has nonzero connecting class.

This is the first natural analytic realization of the source-effectivity object: locally DA
boundary multipliers possess a meromorphic primitive but no DA primitive.

## Pointed DA--holomorphic bi-anomaly corollary

The gamma-gerbe construction supplies a second, independent anomaly face from the same source
cochain.  On the fixed irrational triptic fibre, the Felder--Henriques--Rossi--Zhu group--Cech
cochain `s_Gamma` has coboundary components that are exponentials of rational functions.  Hence
its coboundary lies in the intersection of the holomorphic-unit and DA-meromorphic coefficient
complexes.

It follows that `s_Gamma` defines a nonzero relative class modulo this intersection.  Its
connecting class maps to the nontrivial gamma-gerbe class and hence to the Dixmier--Douady
generator.  The source pointing selects the standard wedge component `Gamma(z;tau,sigma)`, whose
independently nonzero edge is the DA translation anomaly above.  Both edge anomalies become
effective in the ambient meromorphic coefficient theory.

This is proved in
`irrational-elliptic-gamma-pointed-bi-anomaly-fracture.md`.  It is the first natural analytic
two-axis model of the source-fracture architecture.  The DA and DD classes are not identified;
their exact relation is common pointed origin and simultaneous ambient effectivity.

## Significance and novelty gate

Masaki Kato proved differential algebraicity of the multiple elliptic gamma function for rational
period vectors and stated explicitly that the non-rational-period case was unknown:
https://doi.org/10.1619/fesi.64.225.  The present theorem settles the generic rank-three
non-rational regime for `G_1` in the opposite direction and strengthens it to the exact spectrum
and complete finite defect matroid.

The principal parent theories are:

- Hardouin--Singer's parameterized difference Galois theory, including the general
  `Sigma-Delta-Pi` theory for several commuting automorphisms,
  https://arxiv.org/abs/0801.1493;
- Cassidy's classification of differential algebraic subgroups of the additive group;
- elliptic orbital-residue and telescoping theory;
- Felder--Varchenko's elliptic-gamma automorphy class,
  https://arxiv.org/abs/math/9907061;
- the gamma gerbe of Felder--Henriques--Rossi--Zhu,
  https://arxiv.org/abs/math/0601337.

Morain's 2025--2026 geometric multiple-elliptic-gamma papers extend the Bernoulli-rational
coboundary and higher-cocycle theory to higher-rank lattices.  They do not address differential
algebraicity, the irrational shift spectrum, or the DA-filtered anomaly.

Targeted searches through 2026 found results on differential transcendence of elliptic
hypergeometric solutions and `q`-difference equations over elliptic fields, but no theorem for the
irrational elliptic gamma function, no spectrum `(1)`, no matroid `(2)`, and no DA-filtered
cohomology class above.  This is a preliminary novelty conclusion, not a substitute for specialist
review.

- **Paper verdict:** yes.  The hypertranscendence theorem, exact spectrum, matroid, and DA anomaly
  form a coherent standalone paper.  The pointed DA--holomorphic bi-anomaly materially strengthens
  it by connecting the new DA theorem to the established gamma-gerbe geometry through a new
  intersection-coefficient relative class.
- **Fields verdict:** no.  This is significant new special-function knowledge, not the general HT
  reconstruction/effectivity equivalence.
- **RH boundary:** the theorem supplies a natural analytic HT effectivity model but no zeta source
  object, critical-zero statement, positivity theorem, or RH implication.

## Formalization status

Lean now proves the exact algebraic boundary skeleton in
`GaloisForLFunctions.HTGeometry.DifferenceDifferential`:

- equality of complete boundary fingerprints is equivalent to a joint-fixed difference;
- boundary plus calibration is injective exactly when calibration separates the joint-fixed gauge;
- a locally internal boundary has no internal primitive exactly when its ambient primitive escapes
  the internal sector.

The analytic theorem is not yet Lean-formalized.  Its remaining formal layers are elliptic
function fields, nondiscrete-period meromorphic rigidity, the several-automorphism
parameterized-Picard--Vessiot theorem, differential algebraic subgroup classification, and orbital
principal-part residues.  The present Lean result is labelled a bridge and is not substituted for
those layers.

## Gates

- [x] actual elliptic-gamma theorem isolated from the collapsed abstract class
- [x] complete paper proof written
- [x] Hardouin--Singer several-automorphism parent checked
- [x] exact shift spectrum and finite differential matroid proved
- [x] nonzero DA-filtered cohomology class deduced
- [x] pointed DA--holomorphic bi-anomaly class deduced
- [x] DD and DA anomaly faces recovered from one pointed gamma cochain
- [x] external search found Kato's explicit open non-rational regime
- [x] preliminary exact/equivalent/stronger novelty search
- [x] significance: resolves an open special-function regime and gives strictly stronger structure
- [x] algebraic conservativity/effectivity core Lean-formalized
- [ ] full analytic proof Lean-formalized
- [ ] independent expert audit of simultaneous telescoping descent and novelty
