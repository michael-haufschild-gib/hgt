# Signed critical limit of the upward-prime residual

- **ID:** critical-upward-residual-signed-limit
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [critical-ratio continuation](critical-ratio-continuation.md)

## Exact statement

Fix positive conductors m,l and R>0. Put c_N=max(1,(R log N)^(1/8)),
φ=tiltedUnitSpline, aφ=(∫φ)²/∫φ², and let v_m(N) denote the normalized
Ramanujan horizon vector. The target is

    (log N/c_N) ⟨upwardPrimeVector φ c_N N v_m
                   - shellCorrection φ c_N m · v_m, v_l⟩
      → -aφ(γ+1)[m=1][l=1],

where γ is Euler's constant. The existing estimate is only O_m,l(c/log N).
This target retains its sign and removes its leading term on every other
fixed conductor pair. It does not assert uniformity over growing conductors,
or the sign of the complete form.

The same derivation applies to any overlap schedule c_N≥1 with c_N→∞
and c_N⁴(log N)²/N→0. The critical clock is a particular case.

## Source inputs

- `exists_nearGram_mode_bilinear_approx`: near-Gram mean
  `[m=l] shellCorrection(c,m)/log N`, error O_m,l(c⁵/N).
- `ramanujanLogDivisorJet_eq_conductor_sum`: exact decomposition of the jet
  into Ramanujan modes of divisors.
- `completedConductorEnergy_eq_sub_shellCorrection` and the reference
  energy formula: shellCorrection(c,m)=aφ c[m=1]−log c+C_m−E_m(c).
  Completed conductor energies are nonnegative, antitone and tend to zero.
- Harmonic Gram finite parts: log N(⟨v₁,v₁⟩−1)→γ and
  log N⟨v₁,v_l⟩→−Λ(l)/sqrt(φ(l)) for l>1.
- The adjoint downward expansion and exterior bound inside
  `exists_upward_bilinear_log_free` in `LogarithmFreeCriticalConductorResiduals`.
  The two shell-row definitions there are private; their exact finite sums
  must be exposed or reconstructed before formalization.

## Paper derivation to formalize

Write L=log N, w=c/N, e_m(n)=c_m(n)/sqrt(φ(m)), and

    A_ij = e_m(i)e_l(j) K_w(i,j)/sqrt(ij),
    K_w(i,j) = [i≠j] shellAutocorr φ (|log j−log i|/w)/∫φ²,
    B_T = Σ_(i,j≤T) A_ij.

Here the width w is held fixed when T changes. Thus
B_T=log T · nearGramModeBilin φ (cT/N) T m l for T≥2.
The near-row cardinality bound gives |B_T|≤C_m,l cT/N on every horizon.
This also controls the early horizons, where the asymptotic Gram theorem
does not yet apply.

**Logarithmic row.** If Slog denotes its bilinear pairing from the source,
then L·Slog=Σ A_ij log(N/j). Replace j by max(i,j). The change has absolute
value at most wΣ|A_ij|=O_m,l(c²/N): the kernel sees only logarithmic gaps
≤w, each row has O(wi) sites, and each entry is O_m,l(1/i).
The replacement has the exact finite identity

    Σ A_ij log(N/max(i,j))
      = Σ_(T=1)^(N−1) B_T log((T+1)/T).

Split at T≈N/sqrt(c). Above that cutoff the existing near-Gram theorem
applies uniformly once N is large: T tends to infinity, the conductors
stay fixed, and its radius condition follows from c²=o(N). It gives

    B_T = [m=l] shellCorrection(cT/N,m)
          + O_m,l((cT/N)⁵ log T/T).

After division by u=cT/N, this error is at most O_m,l(c⁴ log N/N),
uniformly for T≤N.
For u≥1,

    shellCorrection(u,m) = aφ u[m=1] + O_m(1+log u).

On the retained horizons u≥sqrt(c), so the shell remainder divided by u
is O_m((1+log c)/sqrt(c)). The omitted horizons cost O_m,l(1/sqrt(c)+1/N)
by the linear raw bound and T log((T+1)/T)≤1. Finally

    (1/N) Σ_(T=1)^(N−1) T log((T+1)/T) → 1,

by T/(T+1)≤T log(1+1/T)≤1. Consequently

    (L/c) Slog → aφ[m=1][l=1].

**Jet row.** The exact divisor-jet decomposition expresses L·Sjet as

    log l · B_N(m,l)
      + Σ_(d|l) Λ(d) sqrt(φ(l/d))/sqrt(φ(l)) · B_N(m,l/d).

The near-Gram theorem and shell-correction asymptotic therefore give

    (L/c) Sjet → aφ[m=1] Λ(l)/sqrt(φ(l)).

**Assembly.** The exact downward adjoint identity writes the upward
residual pairing as

    L·nearGramModeBilin(m,l) − shellCorrection(c,m)⟨v_m,v_l⟩
      − Slog − Sjet + exterior.

The first expression, after multiplication by L/c, tends to
−aφ[m=1] times the harmonic Gram finite part. Its near-Gram error is
O_m,l(c⁴L²/N). The exterior contribution tends to zero by its existing
O_m,l(c²/N) bound. For m=1,l>1 the harmonic finite part cancels the jet
term exactly; for m=l=1 the two remaining constants are −aφγ and −aφ.
For m>1 all leading terms vanish. This yields the stated limit.

## Attack and status

The argument uses actual finite-horizon kernels and their proved
conductor means; it assumes no Weil positivity or zero-location claim.
The low-zero genus theorem does not imply this individual channel law.
The complete residual still contains center, separated cross and combined
near-Gamma terms whose leading signs must be retained together.

Verdict: `SURVIVES PRELIMINARY ATTACK` relative to the local corpus.
The generic finite layer identity and its unit-mass limit are verified in
`HTGeometry/FiniteHorizonLayerCake.lean`; their audited axioms are exactly
`[propext, Classical.choice, Quot.sound]`. The application to the arithmetic
kernel and its uniform error remain Lean obligations. The stated signed
limit is not yet a kernel-verified theorem. No claim of novelty beyond
the local corpus audit is made.
