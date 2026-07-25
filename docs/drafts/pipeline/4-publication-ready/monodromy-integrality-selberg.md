# Monodromy Integrality and Selberg's normality conjecture

**Draft preprint.** Status: theorems complete and dependency-closed as stated; the central
conjecture (MI) is open.

---

## Abstract

Let `S` be the Selberg class. For `F,G ∈ S` write `R_{F,G}(w) = Σ_n a_F(n) conj(a_G(n)) n^{−w}`,
absolutely convergent for `Re w > 1` by the Ramanujan axiom. We isolate a single hypothesis —
that `R_{F,G}` is **meromorphic** (single-valued) near `w = 1` — and show that it already implies
Selberg's normality conjecture (Conjecture A), including the integrality of `n_F`, and that it
determines the full complex Selberg pairing, which Conjecture A alone cannot reach. We show that
Conjecture A is not a consequence of the Dirichlet-series, Euler-product and Ramanujan axioms alone.
Finally we prove a *Cusp–Spectrum Radius Law*: the shift-lattice expansion of the degree-`d` theta
function of `F` at any base point has radius of convergence exactly the distance from that point to
the rest of the Kaczorowski–Perelli standard-twist spectrum; at the cusp this reads `d q_F^{−1/d}`.

## 1. The hypothesis

**(MI)** For all `F,G ∈ S` there is an open `Ω ⊇ {Re w ≥ 1}` and a meromorphic function on `Ω`
agreeing with `R_{F,G}` on `{Re w > 1}`, holomorphic and non-vanishing on `{Re w = 1}\{1}`.

MI is strictly weaker than the received formulations of the missing ingredient — "`S` is closed
under Rankin–Selberg convolution", "`S` is automorphic" — both of which demand of `R_{F,G}` a
functional equation, an Euler product of the correct degree, entirety, and a spectral model. MI
demands **only single-valuedness**.

**Refinement (MI⁺⁺).** For `F,G` of equal degree `d` and conductor, `R_{F,G}` is meromorphic on
`{Re w > 1/2}`, with poles there contained in `{1 − j/d : j ∈ Z_{≥0}}`, all of integer order.
(The half-plane is sharp: for a newform `f`, `R_{F,F} = ζ(w)L(w,sym²f)/ζ(2w)` has poles at `ρ/2`
for every zeta zero `ρ`, all with `Re < 1/2`.)

## 2. Theorems

**Theorem 1.** *(MI ⟹ Conjecture A.)* Let `F ∈ S` satisfy MI for the pair `(F,F)`. Then there is an
integer `n_F ≥ 0` with `Σ_{p≤x}|a_F(p)|²/p = n_F log log x + C_F + o(1)`, and
`n_F = −ord_{w=1}R_{F,F}`, with `n_F ≥ 1` iff the abscissa of `R_{F,F}` equals 1.

*Proof.* `R_{F,F}` has non-negative coefficients, so by Landau its abscissa is a singularity; MI
turns it into a pole, whence `n_F ∈ Z_{≥0}`. Writing `log R_{F,F}(w) = Σ_p|a_F(p)|²p^{−w} + E(w)`
with `E` holomorphic on `Re w > 1/2` (Euler product + Ramanujan), MI gives
`P(w) := Σ_p |a_F(p)|² p^{−w} = n_F log(1/(w−1)) + G(w)` with `G` holomorphic near `{Re w ≥ 1}`.
Then `−P'(w) = Σ_p |a_F(p)|²(log p)p^{−w}` has **non-negative** coefficients and a simple pole of
residue `n_F` at `w=1`, holomorphic on the rest of the closed line; Wiener–Ikehara gives
`Σ_{p≤x}|a_F(p)|² log p = n_F x + o(x)`, and partial summation finishes. ∎

**Theorem 2.** *(MI ⟹ integrality of the full complex pairing.)* Under MI for `(F,G)`,
`Σ_p a_F(p)conj(a_G(p))p^{−w} = κ_{F,G} log(1/(w−1)) + O(1)` as `w → 1+`, with
`κ_{F,G} = −ord_{w=1}R_{F,G} ∈ Z`; and `|κ_{F,G}|² ≤ n_F n_G`.

*Remark.* Conjecture A by itself gives only `Re B(F,G) ∈ (1/2)Z`, via `a_{FG}(p)=a_F(p)+a_G(p)`,
and says nothing about `Im B(F,G)`. MI removes the imaginary part outright, making the Selberg
pairing an **integral** positive-semidefinite Hermitian form on the monoid `S`.

**Corollary 3.** Under MI for all pairs, Selberg's orthogonality conjecture follows from exactly two
further statements: **(P1)** `n_F = 1` for every primitive `F`; **(P2)** if
`Σ_p|a_F(p) − a_G(p)|²/p = O(1)` then `F = G`. ((P2) strengthens the Murty–Murty /
Soundararajan / Farmer strong-multiplicity-one line, which assumes `a_F(p)=a_G(p)` off a thin set.)

**Theorem 4.** *(Axiom necessity.)* `F(s) = exp(Σ_p (log p)^{10} p^{−s})` satisfies Selberg axioms
(1) (Dirichlet series, `a_F(1)=1`, absolute convergence for `σ>1`), (4) (Euler product with
`b_F(p) = (log p)^{10} ≪_θ p^θ` for every `θ>0`, `b_F(p^k)=0` for `k ≥ 2`) and (5) (Ramanujan), and
satisfies `Σ_{p≤x}|a_F(p)|²/p ≍ (log x)^{20}`. Hence Conjecture A is **not** a consequence of axioms
(1),(4),(5): every proof must use the analytic continuation or the functional equation.

**Theorem 5 (Cusp–Spectrum Radius Law).** For `F ∈ S^♯` of degree `d`, conductor `q`, with standard
twists `F_α` and `Δ(α₀) = dist(α₀, Spec(F)\{α₀})`:
```
limsup_{k→∞} | F_{α₀}(s − k/d)/k! |^{1/k} = 1/(2π Δ(α₀))      (s off {s*_ℓ + k/d}).
```
At the cusp, `Δ(0) = min Spec(F) = d q^{−1/d}`, so the left side equals `q^{1/d}/(2πd)`; the left
side is computed from the archimedean data alone (uniform Stirling on the functional equation), the
right side from `a_F(1)=1` and the first prime-side singularity — a local–global identity.
Verified exactly on `ζ`, `L(·,χ)`, level-1 holomorphic newforms and level-1 Maass forms.

## 3. Machine-checked components

Lean 4 / Mathlib, all unconditional, `#print axioms` = `[propext, Classical.choice, Quot.sound]`:
- `RHTower.selberg_pairing_prime_sq` : `a_F(p)conj(a_G(p)) = a_{F·conj G}(p²) − a_F(p²) − conj(a_G(p²))`
- `RHTower.selberg_energy_polarization`, `RHTower.selberg_pairing_cauchy_schwarz`,
  `RHTower.int_eq_zero_or_one_or_neg_one_of_sq_le_one` — the algebraic bridge of Corollary 3
- `HTGeometry.genPoly_meanValue` — exact mean value of a generalized Dirichlet polynomial with
  arbitrary real frequencies
- `HTGeometry.residue_jump_bound`, `HTGeometry.residue_jump_of_integral_eq_zero` — the residue-jump
  obstruction used in Theorem 5

## 4. Obstructions (why MI is the right weakening)

1. *Degree multiplicativity.* Any construction of `R_{F,G}` separately linear in `F` and in `G`
   transports archimedean invariants additively, while the target has degree `d_F d_G`; so no such
   construction yields a functional equation. Meromorphy is the most one can ask.
2. *Linear-moment closure.* The axioms deliver exactly `Σ_p a_H(p)p^{−w} = log H(w) + O(1)` — the
   linear prime moments. Conjecture A asks for a quadratic moment, which lies in the square of that
   space.
3. *Truncated spectral data.* The spectral-spike sum of the standard twist **is** a partial sum of
   `R_{F,G}`; its limit is exactly what the continuation encodes. Such constructions give identities,
   not continuations.
4. *Frequency non-isolation.* In `Φ_F(s,z)·\bar G(s',z)` the diagonal is the frequency class
   `2Λ_d`, but off-diagonal frequencies approach it at distance `≍ h²k^{1/d−2}`; the diagonal is
   never spectrally isolated, so no smooth Fourier cutoff extracts it.

## 5. Open

MI itself; (P1); (P2). Under MI, Conjecture A and (by Kaczorowski–Perelli) the generalized prime
number theorem for `S` follow.
