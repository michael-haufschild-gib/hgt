# Mass-shifted fixed-corona polarized landing boundary

- **ID:** MSST-FCPL-1
- **Stage:** 3-formalized
- **Type:** FALSIFIED / THEOREM (paper and Lean 4)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, following conjectures
  34--36 and imported finite/global observer-boundary results
- **Statement:** Product-continuous Hausdorff linear reporters on the fixed Gamma corona vanish;
  nevertheless lifetime plus critical-wall corona orientation reconstructs centered grade, and
  canonical odd-by-odd polarization turns every nonneutral finite grade packet into one nonzero
  harmonic ray while still admitting no product-continuous detector.

## Goal

Determine whether the fixed infinite Gamma corona can carry the missing shifted-Hankel normal,
without treating finite Hankel faces as faithful carriers. Separate algebraic loss, reflection
cancellation, topology, and admission, then extract the strongest source invariant that survives
all but the still-missing adaptive landing.

## Gates

- [x] 0 → 1  in-progress: fixed corona, canonical lift, critical response, and reflection fixed
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: targeted module build and axiom audit pass
- [ ] 3 → 4  publication-ready: standalone paper not claimed

## Approach

1. Pull a prime trace reporter back along a fixed enumeration of primes and apply the corpus
   product-density theorem for finitely supported clocks.
2. Compute the critical response class of the Gamma Bockstein modulo the summable ideal.
3. Pair lifetime magnitude with the surviving harmonic orientation and test injectivity.
4. Audit functional-equation reflection before and after odd-by-odd centered-grade polarization.
5. Reapply the topology no-go to the polarized survivor and locate the exact remaining landing
   burden.

## Paper proof `[PROVED HERE]`

### 1. Product-continuous fixed-corona reporters vanish

Let `S = Nat.Primes → C`, let `I` be the subspace of summable sequences, and let `Q = S/I`.
For a linear reporter `R : Q → V`, its canonical lift `L = R ∘ mkQ` vanishes on `I`, hence on
every finitely supported prime sequence. Reindexing primes by `N` transports this statement to the
finitely supported clock submodule. That submodule is dense in the raw product topology. If `V`
is Hausdorff and `L` is continuous, equality with zero on the dense submodule forces `L = 0`.
Surjectivity of `mkQ` then forces `R = 0`.

Thus every nonzero linear landing from the fixed corona has a product-discontinuous canonical
lift. This locates the imported finite/global escape at nonclosed topology or admission, not at an
unknown finite-dimensional approximation.

### 2. Critical response has only three oriented corona values

Let `B(t)` be the fixed-corona Gamma Bockstein and let

`C(t) = Gamma_(|t|/2)(B(t))`.

At the critical response time its representative is the critically damped coefficient sequence.
The corpus harmonic-quantization estimates show that modulo summable sequences

`C(t) = -H` for `t > 0`, `C(0) = 0`, and `C(t) = H` for `t < 0`,

where `H` is the prime-harmonic corona class. Critical survival at `t = 1` proves `H != 0`.
Meanwhile the exact lifetime is `|t|/2`. Therefore

`t ↦ (|t|/2, C(t))`

is injective: lifetime distinguishes magnitudes and the nonzero harmonic class distinguishes
signs. Fixed infinite source retains the complete centered divisor coordinate even though every
finite/product-continuous observer loses it.

### 3. Reflection kills linear orientation and polarization repairs it

The critical representative is odd, hence `C(-t) = -C(t)` and
`C(t) + C(-t) = 0`. Linear functional-equation aggregation therefore erases the orientation
before a finite Hankel observer is reached.

Define the canonical polarized class `P(t) = t C(t)`. Then

`P(-t) = P(t)`, `P(t) != 0 ↔ t != 0`, and `P(t) = -|t| H`.

Consequently a reflected pair doubles rather than cancels, and every finite packet satisfies

`sum_i P(t_i) = -(sum_i |t_i|) H`.

If one grade is nonneutral, the packet is nonzero. This is a fixed-corona positive-ray
no-shorting law, derived without a finite-dimensional carrier or numerical computation.

### 4. Polarization does not solve topology or adaptive landing

The product-topology theorem applies to every Hausdorff linear reporter on the same corona. Hence
no reporter with product-continuous canonical lift can detect `P(t)`, even when `t != 0`.
Polarization repairs reflection cancellation but not topology/admission.

The exact surviving route is therefore bilinear and source-sensitive: land the cooriented
odd-by-odd class before functional-equation summation into the even marked Lorentz shear of the
adaptive null polynomial. Existing Gamma positive-cone and `(2,3)` Gamma/Cartier theorems provide
the positive centered-grade source factor; existing shifted-Hankel Lorentz theorems provide the
even phase shear. Corpus search finds no theorem identifying these two factors on the actual
`P^sharp` null flag. That missing bilinear landing, plus its admissible topology, is the producer;
fixed linear reporting is now excluded.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Summable quotient contains the product-dense finitely
  supported subspace, so every Hausdorff product-continuous linear lift is zero. Unpolarized
  critical-wall classes additionally cancel on reflected grade pairs.
- **Strongest positive survivor:** Oriented lifetime is injective in centered grade. Canonical
  polarization is reflection-even, nonzero exactly off center, and places every finite
  nonneutral packet on the same nonzero harmonic ray.
- **New insight:** Fixed corona is neither useless nor a finite carrier. It is an algebraically
  complete but topologically nonobservable source signature. RH-facing information survives only
  after odd-by-odd polarization and must cross a nonproduct/admission-sensitive bilinear landing
  before finite Hankel observation.
- **Status:** Paper proof dependency-closed and formalized unconditionally in
  `RHTower/XiShiftedHankelBoundaryCoronaLandingNoGo.lean`. Direct `lake env lean` and targeted
  `lake build GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryCoronaLandingNoGo` pass. Capstone
  axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Repository lint reaches
  this module through the `RHTower` umbrella; its only errors are four unrelated concurrent
  unwired modules (`BurnolReflectedBoundary`, `FiniteUnitaryHaarReindex`,
  `RungeInterfaceDischarge`, and `SeparableBuresPositiveReporterLaw`).

## Log

- 2026-08-09 — conjectures 37--40 attacked. Product-continuous landing falsified; oriented
  lifetime injectivity, reflection cancellation, canonical harmonic-ray polarization, finite
  no-shorting, and topology separation proved on paper and in Lean source.
- 2026-08-09 — targeted build passed (11,355 jobs). Five capstone declarations audited with only
  `propext`, `Classical.choice`, and `Quot.sound`; promoted to Stage 3. Global lint failure is
  isolated to four unrelated umbrella omissions and does not involve this module.
