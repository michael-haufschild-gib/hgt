# Crystalline producers: a Weil-positive system with atomic Weil measure on the zeta spectrum is Λ, and forces RH

- **ID:** weil-crystalline-producer-rigidity
- **Stage:** 3-formalized (Lean closed 2026-09-29)
- **Type:** THEOREM (paper + Lean, standard axioms)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L150. It settles L105/L106/L129 in the crystalline case **without RH**. L140 needed RH and two-sidedness.
- **Statement.** Let `lam: ℕ_{≥2} → ℝ` with `Σ|lam(n)|n^{−σ} < ∞` for `σ > 1`. Suppose that on `σ > 1`
  `Γ̃(s) + 1/(s−1) − Σ lam(n)n^{−s} = Φ̃(s) := (2(s−½)/π) Σ_j c_j/((s−½)² + t_j²)`,
  with real `c_j`, ordinates `t_j > 0` satisfying `ζ(½+it_j) = 0`, and `Σ|c_j|/t_j² < ∞`. Then `lam = Λ`, `c_j/π` is the multiplicity of `½+it_j`, and **RH holds**.
  - If `c_j ≥ 0`, `Φ̃` is exactly a Herglotz function whose boundary measure is purely atomic on `{±t_j}`: this is a Weil-positive system with crystalline Weil measure on the zeta spectrum.
  - Extension (paper): all but finitely many atoms at zeta ordinates gives the same conclusion.

## Meaning for the producer question
- **Crystalline producers are unique and RH-equivalent.** A positivity certificate whose Weil measure is a sum of point masses at zeta ordinates is necessarily Λ's own, and its existence is RH.
  - So a producer other than Λ must have a non-atomic Weil measure, or atoms away from the zeros ("fake zeros").
  - With L148/L149 (dense support, RH-quality PNT) this pins down the only remaining shapes of a second producer.
- **Why no RH is needed.**
  - The odd functional equation of `D_w = D_lam − D_Λ` comes from two sources: atomicity (`Φ̃(1−s) = −Φ̃(s)`) and ζ's functional equation (`ξ'/ξ(1−s) = −ξ'/ξ(s)`, unconditional).
  - Multiplying by ζ removes every pole of `D_w` at **every** zero of ζ, including hypothetical off-line zeros.

## Proof
1. **Oddness.**
   - `Φ̃` extends meromorphically to ℂ, with simple poles at `½ ± it_j` (residue `c_j/π`), and `Φ̃(1−s) = −Φ̃(s)`. The series converges locally uniformly off the poles, because `Σ|c_j|/t_j² < ∞`.
   - `D_lam := Γ̃ + 1/(s−1) − Φ̃` continues `Σ lam(n)n^{−s}` meromorphically. With `D_Λ = −ζ'/ζ = Γ̃ + 1/(s−1) − ξ'/ξ`, we get `D_w := D_lam − D_Λ = ξ'/ξ − Φ̃` and `D_w(1−s) = −D_w(s)`.
2. **Poles cancel against ζ.**
   - `D_w` has simple poles only at zeros of ξ (residue `m_ρ`, minus `c_j/π` where `ρ = ½+it_j` is an atom) and at the atoms. Every atom is a zero of ζ, and ζ is real on conjugates, so `½ − it_j` is one too.
   - Hence `F := ζ·D_w` (a Dirichlet series with coefficients `1⋆w`, absolutely convergent on `σ > 1`) has `(s−1)F` entire.
3. **Growth.**
   - `ζ·ξ'/ξ = ζΓ̃ + ζ/(s−1) + ζ'` has polynomial growth in vertical strips (convexity).
   - `ζΦ̃ = Σ_j (2(s−½)c_j/π)·ζ(s)/((s−½)²+t_j²)`. Near an atom `|ζ(s)/(s−½−it_j)| ≤ sup|ζ'|`; far from it `|(s−½)²+t_j²| ≳ t_j|t−t_j|`. Splitting at `t_j ≤ 2|t|` and using `Σ|c_j|/t_j² < ∞` gives polynomial growth.
   - So `Γ_ℝ F` decays exponentially in vertical strips.
4. **Odd Hamburger.** `Γ_ℝ(s)F(s) = −Γ_ℝ(1−s)F(1−s)`, with `(s−1)F` entire of finite order. So `F ≡ 0` (Hamburger, odd case; corpus `HTGeometry.coeff_eq_zero_of_odd_completed_functional_equation`, or the reflection-free `coeff_eq_zero_of_critical_line_odd`).
5. **Conclusion.**
   - `1⋆w = 0` gives `w = 0` and `lam = Λ`, so `ξ'/ξ = Φ̃`.
   - `Φ̃` is holomorphic off the critical line, so ξ has no zeros off it: RH.
   - Comparing residues gives `c_j/π = m_ρ`. ∎

## Extension: finitely many fake atoms (paper)
- If `Φ̃` also has finitely many atoms `t_f` with `ζ(½+it_f) ≠ 0`, then `F` has finitely many simple poles on the line.
- In Hamburger's Laplace–periodicity step their contributions `r_f Γ(1−ρ_f/2)(πτ²)^{ρ_f/2−1}` are analytic at every `τ = in₀`. So residue comparison still gives `a_{n+1} = a_n`, and the odd sign gives `F ≡ 0`. That contradicts the nonzero residues `−(c_f/π)ζ(½+it_f)`, so there are no fake atoms and the theorem applies.
- With **infinitely many** fake atoms the sum diverges on the imaginary axis (L142/L144). That case stays open.

## Gates
- [x] 0 → 1, 1 → 2: proof above.
- [x] 2 → 3: Lean closed. See the Lean section.
  - The finite-fake-atom extension is paper only.

## Log
- 2026-09-29 — created from L150.
- 2026-09-29 — Lean closed: `RHTower.crystalline_producer_rigidity`, standard axioms only.

## Lean
- `RHTower/ZetaSpectrumAtomicSeries.lean`: the atomic series and its ζ-cancelled form.
  - `atomicPairSeries c t` is `Φ̃`.
  - `atomQuot t = dslope (dslope Λ (½+it)) (½−it)`, which equals `Λ/((s−½)²+t²)` off the atoms.
  - `atomicZetaPart c t = Σ (2c_j/π)(s−½) atomQuot(t_j)`, which equals `ΛΦ̃`.
  - `ZetaAtoms c t` requires `t_j ≥ 1`, `ζ(½+it_j) = 0` and `Σ|c_j|/t_j² < ∞`.
  - `differentiableOn_atomicZetaPart`: holomorphic on `ℂ∖{0,1}`. Local bound: maximum principle on unit discs about the atoms.
  - `atomicZetaPart_one_sub`: odd.
  - `exists_decay_atomicZetaPart`: `‖Z‖ ≤ C/(1+t²)` on `½ ≤ σ ≤ 3/2`, `|t| ≥ 4`.
- `RHTower/CrystallineProducerRigidity.lean`: the odd Hamburger step and the RH deduction.
  - `completedZetaXiLogDeriv = Λ₀' + Λ₀(1/s + 1/(s−1))`, which equals `Λξ'/ξ`.
    - `completedZetaXiLogDeriv_one_sub`: odd.
    - `exists_decay_completedZetaXiLogDeriv`: decay via Cauchy's estimate on radius-½ discs.
  - `differentiableOn_atomicPairSeries`: `Φ̃` is holomorphic on `Re s > ½`, by a locally uniform lower bound `κt²` on the atom denominators.
  - `crystallineRemainder = Λξ'/ξ − ΛΦ̃ − βΓ_ℝ(s−1)` with `β = (Λ₀(1) − Φ̃(1))/2`, and the removable singularity at 1 filled.
    - `differentiableOn_crystallineRemainder` on `Re s > 0`.
    - `exists_decay_crystallineRemainder`: decay on the closed strip.
  - `Gammaℝ_mul_riemannZeta_mul_eq`: `Γ_ℝζ(Γ̃ + 1/(s−1) − φ + ζ'/ζ) = Λξ'/ξ − Λφ` on `Re s > 1`.
  - `crystallineCoeff_eq_zero`: `1 ⋆ (lam − Λ) = 0`, via `HTGeometry.coeff_eq_zero_of_critical_line_odd`.
  - `eventually_eq_zero_of_deriv_eq_mul`: if `f' = fg` with `g` continuous at a zero of analytic `f`, then `f ≡ 0` near it.
  - `riemannHypothesis_of_completedZetaXiLogDeriv_eq`: `Λξ'/ξ = ΛΦ̃` on `Re s > 1` implies RH, via the identity theorem on `ℂ∖{0,1}` and the ODE lemma.
  - `crystalline_producer_rigidity`: the card's statement. The hypotheses are `ZetaAtoms`, `Σ|lam n|n^{−σ} < ∞` for `σ > 1`, and `Γ̃ + 1/(s−1) − Σlam n^{−s} = Φ̃` on `Re s > 1`. The conclusion is `(∀ n ≠ 0, lam n = Λ n) ∧ RiemannHypothesis`.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
