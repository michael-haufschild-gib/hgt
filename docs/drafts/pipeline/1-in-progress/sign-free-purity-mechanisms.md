# Sign-free purity mechanisms: the Frobenius shadow and the separation shadow over ℤ

- **ID:** sign-free-purity-mechanisms
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → Lean
- **Source:** `docs/reports/review-0911/fable.md` §6, questions (S1) and (S2)
- **Statement:** ℤ carries both mechanisms as structure and as receivers, with exact costs; neither is a producer.

## Questions

- **(S1)** Is there a ring with commuting endomorphisms `F_n`, `F_mF_n=F_{mn}`, whose fixed-point
  counts are `N(n)=Λ(n)+1+1/(n²−1)`, on which high-order vanishing at the fixed points of the
  degrees of a window costs less than `m` times the window's Chebyshev count?
- **(S2)** Is there a sign-free prime-side quantity that bounds the fibre multiplicity of the
  height map on the zeros?

## Theorems and proofs

Notation: `ψ_n F = F(X^n)` on `ℤ[X]`; `F̄` reduction modulo a prime `p`; `θ(S)=Σ_{p∈S} log p`.

**T1 (no literal count).** For `n≥2` not a prime power, `N(n)=1+1/(n²−1)` lies strictly between
`1` and `2`. No family of sets has cardinalities `N(n)`.

**T2 (logarithmic count).** For `n≥2`, `Λ(n)=log Φ_n(1)`. For a prime `p` and `k≥1`,
`Φ_{p^k} ≡ (X−1)^{p^k−p^{k−1}} (mod p)`.
*Proof.* `Φ_{p^k}(1)=p`, `Φ_n(1)=1` otherwise; in characteristic `p`,
`Φ_{p^k}=Φ_1^{p^k−p^{k−1}}`. ∎
The degree-`n` points of Spec ℤ are counted by the logarithm of the order of the intersection of
the primitive `n`-torsion with the fixed point `1`, and at `p` they collapse onto it.

**T3 (no archimedean zero derivative).** A ring endomorphism `φ` of `ℤ[X]` with `(φX)′=0` is
`F↦F(a)` for an integer `a`: its image is the constants.
*Proof.* In characteristic zero `(φX)′=0` gives `φX=a`; ring homomorphisms out of `ℤ[X]` are
determined by the image of `X`. ∎

**T4 (Stepanov's identity modulo `n`, all orders).** For `A,B∈ℤ[X]`, every `n` and `k`,
`(A·ψ_nB)^{(k)} ≡ A^{(k)}·ψ_nB (mod n)`.
*Proof.* `(ψ_nB)′=nX^{n−1}ψ_n(B′)`. Induct on `k`: `(Aψ_nB)′=A′ψ_nB+n·(…)`, and derivatives of
multiples of `n` are multiples of `n`. ∎

**T5 (Chebyshev floor).** Let `F∈ℤ[X]` be monic and `S` a finite set of primes with
`F′≡0 (mod p)` for every `p∈S`. Then `Π_{p∈S}p` divides `deg F`; if `deg F≥1`,
`θ(S)≤log deg F`.
*Proof.* The coefficient of `X^{d−1}` in `F′` is `d`. ∎

**T6 (exact cost of inseparability).** Let `F` be monic and suppose `F̄` is a `p^{k_p}`-th power
for every `p∈S`. Then `Π_{p∈S}p^{k_p}` divides `deg F`. Conversely for `n=p^k m`,
`ψ_nF ≡ (ψ_mF)^{p^k} (mod p)`, so with `n=Π_{p∈S}p^{k_p}` every `ψ_nF` attains the bound up to
the factor `deg F`.
*Proof.* Degrees of powers; `ψ_{p}G≡G^{p}` over `𝔽_p`, iterated. ∎

**T7 (cheap multiplicity modulo `p`).** For monic `F`, `n=p^km`, every root of the reduction of
`ψ_nF` modulo `p` has multiplicity at least `p^k`. For `m≥1` and `k_p=⌈log_p m⌉`,
`n=Π_{p∈S}p^{k_p}` gives multiplicity `≥m` at every `p∈S` at cost
`log n ≤ θ(S)+|S|·log m`.
*Proof.* T6 and `p^{k_p}≤mp`. ∎

**T8 (separation principle).** Let `L/K` be Galois, `v` a function on `L` invariant under
`Gal(L/K)`, `f∈K[X]`. If `v` is injective on the roots of `f` in `L`, every root lies in `K`.
For `K=ℝ`: a real polynomial whose complex roots have pairwise distinct absolute values has
only real roots.
*Proof.* `σx` is a root with `v(σx)=v(x)`, so `σx=x` for all `σ`. ∎

**T9 (the height separates iff the traces are bounded).** For `σ≥0`:
every two nontrivial zeros of ζ at the same height have real parts within `2σ` of each other
⇔ zero width `≤σ` ⇔ `∃K ∀p: |c(log p)|≤Kp^σ`, `c` the cubic-spline trace. At `σ=0`: the height
is injective on the nontrivial zeros ⇔ RH ⇔ the traces at the primes are bounded.
*Proof.* The reflection `ρ↦1−ρ̄` preserves the height and the zero set, and
`Re ρ−Re(1−ρ̄)=2(Re ρ−½)`; the two-sided prime criterion of
`CollectiveDiophantineGeometry.TwoSidedGapIteration`. ∎

## Answers

- **(S1).** A literal count does not exist (T1); the count is logarithmic (T2). The Frobenius
  shadow exists one prime at a time: `ψ_p` is a Frobenius lift and Stepanov's identity holds
  modulo `p` to all orders (T4). It cannot be archimedean (T3). Its cost is exact (T6):
  multiplicity `m` at every prime of `S` costs `≤θ(S)+|S|log m`, far below `m·θ(S)` (T7), and
  never less than `θ(S)` (T5). The degree of an auxiliary that is inseparable at every prime of
  a window is divisible by the primorial of the window: the mechanism pays the Chebyshev count
  it is meant to bound before it starts. The multiplicity it buys lives modulo `p`; the
  archimedean order is not lowered (ALST: exact order costs the degree).
- **(S2).** Yes as a receiver: the absolute cubic-spline trace at the primes. Its boundedness is
  equivalent to fibre multiplicity one, and its growth exponent to the horizontal spread of the
  fibres (T9). The mechanism itself is T8. No producer: in the ultrametric case the injectivity
  of the invariant is read from the Newton polygon; over ℤ it is the statement to be proved.

## Gates
- [x] 0 → 1
- [ ] 1 → 2
- [ ] 2 → 3

## Not done
The reproof of the Carlitz–Goss Riemann hypothesis in the corpus's language.
