# Extinction of the co-moving Xi prime source

- **ID:** mass-xi-comoving-prime-extinction
- **Stage:** 3-formalized
- **Type:** POSITIVE SURVIVOR
- **Source:** ../../../reports/mass-shifted-spectral-trace-route.md · §9.3 Exact open core
- **Statement:** Every widening admissible co-moving mass trace vanishes, and the concrete Xi
  co-moving von-Mangoldt bottom source tends to zero; hence the canonical semigroup high-pass is
  asymptotic to the fixed prime source modulo a `C₀` correction.

## Conjecture C17

The uniform co-moving cone estimate may conceal extinction.  If aperture `a(u)` tends to infinity
while `|u|≤a(u)`, the real mass damping should defeat each fixed spectral atom, and the existing
cone estimate should provide a summable dominator for the full trace.  For Xi, the centered Gamma
channel and crossed residue should vanish with mass as well.

## Hostile audit

The pointwise claim alone is insufficient: the spectral family is infinite, and no exchange of
limit and trace is legal without a summable bound independent of `u`.  The prior cone theorem gives
exactly that missing bound, `F.weight (σ-1/2)`, when `σ>1/2`.  Tannery's theorem therefore applies
without shell truncation or a uniform cardinality estimate.

On the Gamma side, monotonicity alone does not prove limit zero.  The proof first applies dominated
convergence along integer masses to the centered `L¹` norm, separately proves crossed-pole decay,
then transfers the limit to all real masses using the already-formalized antitonicity and the
natural floor.

The conjecture survives both audits.

## Exact theorem

Let `F` be an admissible abstract spectral family with `1/2≤F.base`.  Suppose

- `1/2≤a(u)`;
- `|u|≤a(u)`;
- `a(u)→∞` as `u→∞`.

For every `σ>1/2`, Lean proves

`(F.mass a(u)).traceC (σ+iu) → 0`.

The pointwise aperture estimate is

`‖term_(a(u))(σ+iu,i)‖ ≤ exp(-σ a(u) + Re(F.pt i)/2)`.

For the Xi schedule `A(u)=|u|+2`, Lean further proves

`xiMassBottomArchIntegral A(u) 1 (σ+iu) → 0`,

`xiMassBottomPrimeIntegral A(u) 1 (σ+iu) → 0`.

Consequently

`xiMassPrimeSemigroupHighPass σ u`

`  - xiMassBottomPrimeIntegral 1 (3/4) (σ+iu) → 0`.

Thus the adaptive mass subtraction removes no asymptotic arithmetic information.  It replaces the
fixed source by an asymptotically identical source and isolates a universal `C₀` correction.

## Significance

Loops 12–16 could only say the co-moving source was bounded and that the high-pass carried the same
growth type.  Extinction sharpens this from `L∞` control to a canonical quotient by `C₀`.  The
fixed source and high-pass have identical asymptotic cluster behavior, limsup norms, and
boundedness obstruction.  Any hoped-for recovery from special structure of the subtracted arm is
therefore impossible at infinity: arithmetic cancellation must already occur in the fixed arm.

## Lean certificate

Universal module `HTGeometry.AbstractSpectralComovingExtinction`:

- `norm_mass_term_le_comoving_aperture_decay`;
- `tendsto_mass_traceC_comoving_zero`.

Xi module `RHTower.XiMassComovingPrimeExtinction`:

- `tendsto_integral_norm_xiMassCenteredArchIntegrand_natMass_zero`;
- `tendsto_xiMassBottomArchUniformBound_atTop_zero`;
- `tendsto_xiMassTraceC_comoving_zero`;
- `tendsto_xiMassBottomArchIntegral_comoving_zero`;
- `tendsto_xiMassBottomPrimeIntegral_comoving_zero`;
- `tendsto_xiMassPrimeSemigroupHighPass_sub_fixedSource_zero`.

Verification:

- direct Lean checks — PASS;
- `lake build GaloisForLFunctions.HTGeometry.AbstractSpectralComovingExtinction` — PASS
  (`[2749/2749]`);
- `lake build GaloisForLFunctions.RHTower.XiMassComovingPrimeExtinction` — PASS
  (`[9392/9392]`);
- axiom audit of the universal decay estimate, abstract trace extinction, Xi
  archimedean extinction, literal prime-source extinction, and high-pass
  asymptotic identity — PASS; only `propext`, `Classical.choice`, and
  `Quot.sound` occur.
