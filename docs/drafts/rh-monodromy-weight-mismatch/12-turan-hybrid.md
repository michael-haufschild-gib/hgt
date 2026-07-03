# 12 — The Turán hybrid: spike recurrence at σ = 1+η, and the race that decides it

Register: SEARCH. §1 is a candidate mechanism with its own refutation trail (two bugs found
and incorporated); §2 is the decisive calculation, open. Companions: 08 §7.2 (single-test
closure), checks/c8-turan-taspect-note.md (the hybrid is literature-absent; both flanks are
proved by power sums), 11 (why the mechanism MUST consume the Euler product — it does).

## 1. The mechanism `[CONJECTURE — candidate, with named failure modes]`

Φ(t) := −ζ′/ζ(1+η+it) is UNIFORMLY (Bohr) almost periodic — unconditionally, from the
absolutely convergent Dirichlet series Σ Λ(n)n^{−1−η−it}. This is exact-class input: 11
Theorem B's counterexample has no such line (its f′/f is not a.p. on any line right of the
zeros) — so this mechanism is invisible to the soft-route closure. The chiasmus resolves:
the Euler product CAN act on the recurrence side, at σ > 1.

A zero ρ₀ = 1−δ+iγ₀ imprints on Re Φ a spike of height ≍ 1/(η+δ) and width η+δ at t = γ₀
(all zero-contributions Re(1/(s₀−ρ)) are POSITIVE at σ₀ = 1+η; on-line zeros give broad
bumps of width ≥ η+1/2). Bohr almost-periodicity forces the ENTIRE profile — spike included
— to recur within ε at every ε-translation number τ, a relatively dense set with gap L(ε).
A recurring narrow spike needs narrow constituents: by Fourier positivity, broad (on-line)
bumps of total local mass M can forge frequency-1/δ content only if M ≳ e^{c/δ}, while the
unconditional local mass bound is M ≤ C log t. So below the FORGING CEILING
t ≤ exp(e^{c/δ}), every recurrence site carries a genuine zero with β ≥ 1 − C′δ; the
quantified Reduction (06 §6 / Ingham, effective) then contradicts the forced linear count
once the height range exceeds T₁ ≈ (C·L(ε))^{1/(1−θ)}.

Refutation trail (both bugs found by attack-as-false, both survivable so far):
(i) the ambient field near γ₀ has size O(log γ₀), not O(1) — the spike is buried in VALUE
for log γ₀ > 1/δ; survived by matching PROFILES (Fourier content is additive and linear, so
the spike's high-frequency signature survives inside an ε-recurrence regardless of ambient
size); (ii) on-line clusters can forge the spike once local mass reaches e^{c/δ} — this
caps the usable height range at the forging ceiling and converts the would-be strip into a
height-dependent region. Output shape IF the mechanism survives §2: a zero-free region of
width ~ c/loglog γ — which would exceed Vinogradov–Korobov and is therefore ALSO the
strongest reason to expect §2 to kill or degrade it. The consistency question is sharp,
quantitative, and ours to settle.

## 2. The race `[OPEN — the decisive calculation]`

Everything reduces to two doubly-exponential scales:
- **Forging ceiling** T_forge(δ) ≈ exp(e^{c/δ}): above it, broad on-line mass can imitate
  the spike and the mechanism sees nothing.
- **Translation-number gap** L(ε, η): Bohr gives finiteness; the effective gap for
  Σ Λ(n)n^{−1−η−it} is governed by simultaneous Diophantine approximation of the phases
  {t log p : p ≤ P(η)} with P(η) the effective series cutoff (P ≈ e^{1/η} weighted terms).
  Kronecker-counting heuristic: matching N ≈ π(P)/… ≈ e^{1/η}/η-many phases to precision ε′
  costs L ≈ (1/ε′)^{N} = exp(c″·e^{1/η}·log(1/ε′)).

The mechanism yields a nontrivial region iff T₁ ≈ L^{1/(1−θ)} < T_forge, i.e. iff the
forging constant c beats the Kronecker constant c″ (with η ≍ δ). Both constants are
computable: c from the Fourier-positivity forging bound (Poisson kernel decay e^{−w|ξ|} vs
local zero-count C log t — C explicit from the Riemann–von Mangoldt formula), c″ from an
effective Kronecker/Weyl bound on the return times of (t log p)_{p ≤ P} — and the DIMENSION
COUNT is the crux: the spike lives at ONE height, so full-line sup-recurrence (all N
phases) may be far more than needed; a WINDOWED recurrence (Stepanov-type, matching the
profile only near γ₀ − τ) needs fewer effective phases and shrinks L. Note what 11 Thm A
gives here for free: Φ is holomorphic in s, so windowed S²-recurrence of Φ on two nearby
lines upgrades to sup-recurrence on the window — the S²-degree is available BECAUSE we are
at σ > 1. The race calculation with the windowed gap is the lane's next proof target; its
outcome is a theorem either way:
- c beats c″ (windowed): a new zero-free region — promote with extreme prejudice after the
  VK-consistency autopsy;
- c″ beats c: the mechanism is dead at σ = 1+η, and the death certificate (recurrence too
  slow vs forging too easy) quantifies EXACTLY how much a.p. rigidity the Euler product
  buys — the first measured constant on the exact-structure side of the wall.
