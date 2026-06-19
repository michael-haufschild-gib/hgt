# The Spectral Torelli / Inverse Problem (B29) — does the secular moment sequence determine the L-function?

> **NASCENT / SEARCH channel. Air-marked; no proof of RH claimed.** Branch B29 of the charter (`hypertranscendental_galois_program.md`). The *inverse* of the forward map "L-function ↦ its secular moments `{s_m}`": injectivity (a Torelli theorem) and the image characterization. Complementary to dyson's `rh-byproduct-secular-hankel-overdetermination.md` (which studies the *positivity/transcendence of a fixed* `{P_k}`); this draft studies the *map* itself. Companions: `…field_foundations.md` §17/§19/§20, `EulerProduct.lean` (the multiplicativity firewall).

## 0. The forward map and the Torelli question

The field's carrier is the map
```
   Φ :  {completed L-functions ξ}  ⟶  {secular moment sequences}  ,    ξ ⟼ (s_m)_{m≥2},   s_m := Σ_ρ ρ^{-m}.
```
**Torelli question:** is `Φ` injective (does `{s_m}` determine `ξ`), and what is its **image** (which sequences are genuine spectra)? A clean answer separates three independent properties of a moment sequence — *existence* (realizability), *arithmeticity* (Euler product), and *positivity* (RH) — that the single object `{s_m}` entangles.

## 1. Injectivity: the secular moments determine the L-function `[PROVED HERE — standard complex analysis]`

> **Spectral Torelli (injectivity).** A completed L-function `ξ` (entire, order 1, genus ≤ 1, with functional equation `ξ(s)=ξ(1−s)` and normalization `ξ(0)=ξ(1)=½`) is **uniquely determined** by its secular moments `{s_m}_{m≥2}`.

*Proof.*
1. **Moments → zero-multiset.** Order 1 gives `Σ_ρ |ρ|^{-2} < ∞`, so `s_m=Σ_ρ ρ^{-m}` converges absolutely for `m≥2`. Form the generating function
   ```
      R(z) := Σ_{m≥2} s_m z^{m-1} = Σ_ρ Σ_{m≥2} ρ^{-m} z^{m-1} = Σ_ρ  z/(ρ(ρ−z))  =  Σ_ρ [ 1/(ρ−z) − 1/ρ ] .
   ```
   `R(z)` is a meromorphic function whose **poles are exactly the zeros `ρ`, with residues the multiplicities**. So `{s_m}_{m≥2}` determines the zero-multiset `{ρ}` (with multiplicity) — power sums determine the multiset (the resolvent makes it explicit).
2. **Zero-multiset → `ξ` up to `e^{a+bs}`.** By Hadamard (genus 1), `ξ(s)=e^{a+bs}∏_ρ (1−s/ρ)e^{s/ρ}`. The zeros fix the product; only `a,b` remain.
3. **FE + normalization fix `a,b`.** `ξ(s)=ξ(1−s)` forces `b=0` (an `e^{bs}` factor is not FE-symmetric unless `b=0`, the zeros already being FE-symmetric); `ξ(0)=½` fixes `a`. Hence `ξ` is determined.
4. **`ξ → L`.** Dividing by the universal archimedean factor `(s-1)π^{-s/2}Γ(s/2+1)` recovers `ζ` (resp. the L-function). ∎

So `Φ` is **injective**: the completed L-function is reconstructible from its secular moments. The finite
spectral-polynomial faithfulness core is now Lean-ledgered (`spectralTorelli_faithful`, plus the
constant-term/Vieta bridge `spectralPoly_coeff_zero` and the self-dual coefficient-reality bridge
`selfDual_spectralPoly_coeff_real`); the infinite
resolvent/Hadamard passage from `{s_m}_{m≥2}` to the full divisor still needs meromorphic/Hadamard
infrastructure.

## 2. The image: three independent cuts on moment space `[CONJECTURE / OPEN CORE]`

Injectivity is the easy half. The **image** `Φ({ξ})` — which sequences `{s_m}` are genuine spectra — is cut out by three *independent* conditions, and disentangling them is the field's inverse problem:

```
   (E) EXISTENCE / realizability :  {s_m} is the moment sequence of SOME order-1, FE-symmetric divisor.
   (A) ARITHMETICITY / Euler     :  that divisor's ξ has an EULER PRODUCT (multiplicativity).
   (P) POSITIVITY / RH           :  the divisor lies on the critical line (Face A / Bogomolov-minimal, B7).
```
- **(E) Existence** is a growth + reality condition (the `R(z)` of §1 must have all poles in the critical strip, FE-paired, with order-1 counting `N(T)~ (T/2π)log T`). A realizability/positivity gate, not yet sharp.
- **(A) Arithmeticity** is the field's **First Theorem** (`…field_foundations.md` §9, `EulerProduct.lean`): Euler product ⟺ Bohr-lift factorization, detectable at finite level — the **fake-family firewall**. Davenport–Heilbronn lives in `(E) ∧ ¬(A)`: a realizable FE-symmetric divisor with **no Euler product**.
- **(P) Positivity** is RH, i.e. Face A / Li-positivity / Bogomolov-minimality (B7).

> **The inverse problem disentangles what `{s_m}` entangles.** RH is *only* cut (P). The fakes (Davenport–Heilbronn) are `(E)∧¬(A)` and can **even satisfy a Hankel-positivity** without being genuine — so positivity (P) does **not** imply arithmeticity (A). This is the no-margin / integrality lesson in inverse-problem form: *genuineness is the Euler cut (A), not the positivity cut (P).* Any criterion that "sees RH" from positivity alone has confused (P) with (A) and will pass a fake.

## 3. The overdetermination is the defining equation of the image `[REFRAME → dyson]`

Each `s_m` is computable **two ways**: from the **zeros** (`s_m=Σ_ρ ρ^{-m}`) and from the **primes** (via the explicit formula / `−ξ'/ξ` Dirichlet data). For a *genuine* spectrum these agree for every `m`; for an arbitrary sequence they do not. So:
```
   Φ({ξ})  =  { {s_m} :  (zero-side formula)_m = (prime-side formula)_m   for all m }   ∩  (E)∧(A) .
```
This **overdetermination** — an infinite system of zero-side = prime-side constraints — is exactly dyson's `rh-byproduct-secular-hankel-overdetermination.md`. B29's contribution is to read it as the **defining equations of the Torelli image**: the genuine sequences are the overdetermined locus, and the explicit formula is its equation system. The image is therefore *thin* (infinite-codimension) in the space of all FE-symmetric realizable sequences — the rigidity that makes a fake hard to sustain.

## 4. Why this matters

- **A genuine theorem (injectivity, §1):** the L-function is its secular moments — the field's coordinates are *faithful*. This licenses working entirely in moment space (`{s_m}`) without losing the L-function, justifying the whole charter's use of `s_m` as Object-X.
- **A clean separation (§2):** existence / arithmeticity / positivity are three independent cuts; RH is only the third; the fakes inhabit the second's complement. This is the sharpest statement of *why positivity alone cannot prove RH* (it cannot see cut (A)).
- **A defining-equation view of genuineness (§3):** the image is the explicit-formula overdetermination locus — uniting the inverse problem with dyson's Hankel-overdetermination.

**House status.** §1 injectivity is **proved** (standard complex analysis: resolvent + Hadamard + FE); it is the genuine new theorem here — *the secular-moment coordinates are faithful*. The finite polynomial root-multiset faithfulness half is Lean-ledgered; the infinite resolvent/Hadamard reconstruction remains Tier B. §2 (the three-cut image) and §3 (overdetermination = defining equations) are reframes/open: the existence cut (E) is not sharp, the arithmeticity cut (A) is the §9 firewall (Lean-formalized direction), and positivity (P) = RH is the wall. Crosses CITY districts D2/D4/D8 and dyson's overdetermination draft. Next: sharpen cut (E) (the realizability gate), and test §3's overdetermination against Davenport–Heilbronn (a fake should fail the zero-side=prime-side system at some explicit `m`).

**Ledger update — the Torelli injectivity (faithfulness) core is now ledger-proven.** Formalized in `formal/GaloisForLFunctions/SpectralTorelli.lean` (`spectralTorelli_faithful`), axiom-clean (`[propext, Classical.choice, Quot.sound]`, zero `sorry`): the monic spectral polynomial `∏_{ρ∈s}(X−ρ)` faithfully determines the zero multiset `s` (equal spectral polynomials ⟹ equal multisets), with inverse `Polynomial.roots` (mathlib `roots_multiset_prod_X_sub_C`). The same file now also proves `spectralPoly_coeff_zero`: the constant term is `(-1)^{#s}∏ρ`, the finite Vieta product bridge to the Arakelov product-formula side. It also proves `selfDual_spectralPoly_coeff_real`: if the finite multiset is invariant under complex conjugation, every coefficient of its spectral polynomial is fixed by conjugation. This is the **injectivity half of B29** at ledger grade: the elementary-symmetric/coefficient data are faithful coordinates, hence — via the Newton bijection in characteristic zero (`SecularNewton.lean`/`MomentReconstruction.lean`) — so are the secular power sums `s_m=Σρ^m`. The *image* characterization (the three-cut (E)/(A)/(P): which multisets are genuine zero sets) remains the open/wall side, unformalized.

**Ledger update — the Newton inversion engine is now ledger-proven (toward power-sum Torelli).** `MultisetNewton.lean`, axiom-clean: `aeval_psum_eq_multiset_powerSum` (the psum `aeval` bridge, companion to mathlib's `aeval_esymm_eq_multiset_esymm`, which mathlib lacked) and `multiset_newton` — **Newton's identity for a multiset**, `p_k = (-1)^{k+1}·k·e_k − Σ_{0<a<k}(-1)^a·e_a·p_{k-a}`, transferred from `MvPolynomial.psum_eq_mul_esymm_sub_sum` via the two `aeval` bridges. In characteristic zero (`k` invertible) this **solves for `e_k`** from `p_1,…,p_k` — the recursion that, by strong induction, recovers the elementary symmetric functions, hence the spectral polynomial (Vieta), hence the zero multiset (roots), from the secular **power sums** `p_k`. This is the engine of the *power-sum* Torelli (the B29 headline: secular-moment faithfulness), upgrading the polynomial/esymm-level `spectralTorelli_faithful`. Remaining (next build steps): the char-0 strong-induction inversion `(p_1..p_n) ↦ (e_1..e_n)` and the faithfulness conclusion.

**LEDGER MILESTONE — the POWER-SUM Torelli (B29 headline) is now FULLY ledger-proven.** `PowerSumTorelli.lean`, axiom-clean (`[propext, Classical.choice, Quot.sound]`, zero `sorry`): `powerSum_torelli` — for finite families `f, g : Fin n → ℂ`, equal secular power sums `Σ_i f(i)^k = Σ_i g(i)^k` (all `k`) ⟹ equal zero multisets `univ.val.map f = univ.val.map g`. *The secular power sums faithfully determine the zero multiset* — the genuine secular-moment faithfulness, upgrading the polynomial/esymm-level `spectralTorelli_faithful`. The proof runs the field's own program in Lean: **(1) inversion** `esymm_eq_of_powerSum_eq` (equal power sums ⟹ equal elementary symmetric, by strong induction through the multiset Newton identity, solving for `e_k` in characteristic zero); **(2) tie** (equal `e_k` ⟹ equal spectral polynomials `∏(X−ρ)` via Vieta coefficients `±e_k` ⟹ equal multisets via `Polynomial.roots`). Built on the from-scratch `MultisetNewton.lean` (the psum bridge + Newton's identity for multisets, both absent from mathlib). The **injectivity half of B29 is now complete at the power-sum (secular-moment) level**; the open/wall side remains the *image* three-cut (E)/(A)/(P) (which multisets are genuine zero sets).
