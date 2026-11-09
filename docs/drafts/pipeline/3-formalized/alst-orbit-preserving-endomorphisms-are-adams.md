# Polynomial orbit preservers are translated Adams operations

- **ID:** alst-orbit-preserving-endomorphisms-are-adams
- **Stage:** 3-formalized
- **Status:** FORMALIZED. All six modules passed final plain Lean checks and transitive axiom audits.
- **Statement:** Let `P` be a finite set containing two distinct primes. Every complex polynomial self-map preserving `O(t)=(p^(−it))_{p∈P}` has the unique form `F_p(X)=p^(−ib)X_p^n`, with `n∈ℕ`, `b∈ℝ`. Its clock is `t↦nt+b`, without any regularity assumption. Over `ℤ`, `b=0`: the endomorphisms are exactly Adams operations.

## Research consequence
This classifies all exact polynomial Frobenius candidates preserving the
prime orbit. A nonidentity candidate cannot fix two orbit points. Changing
the polynomial map while preserving the whole orbit cannot supply a
Frobenius with many fixed orbit points. The positive result is the full classification,
including translations, constant maps, and the induced clocks.

## Proof
Write `λ_α=Σ_p α_p log p`. Unique factorization makes distinct monomial
frequencies distinct. Each coordinate of `F(O(t))` is a finite sum
`Σ_α c_α exp(−itλ_α)` of modulus one. If its nonzero support had distinct
extreme frequencies, the largest difference frequency in its squared
modulus would have the unique coefficient `c_max conjugate(c_min)≠0`.
The corresponding Bohr coefficient of the constant function `1` is zero,
a contradiction. Thus `F_p=c_p X^{A_p}`, with `|c_p|=1`.

Choose `b` with `F(O(0))=O(b)`. Then `c_p=p^(−ib)`. For every `t`, choose
`u(t)` with `F(O(t))=O(u(t))` and put `τ(t)=u(t)−b`. Consequently
`p^(−iτ(t))=exp(−itλ_{A_p})`. The prime orbit is injective: equality at two
times would give a common exact return for two distinct primes. The
character identities therefore imply `τ(s+t)=τ(s)+τ(t)` and `τ(0)=0`.
For each prime `p`, the additive function
`δ_p(t)=−log(p)τ(t)+λ_{A_p}t` takes values in `2πℤ`. Its image is divisible
and contained in a cyclic group, hence zero. Taking one prime coordinate
gives `τ(t)=at`, and all coordinates give `λ_{A_p}=a log p`.

Let `L=Σ_p ℤ log p ⊂ ℝ`. This is a nonzero finitely generated integer
module, and the preceding identities give `aL⊂L`. The determinant trick
makes `a` integral over `ℤ`. Baker independence of prime logarithms over
real algebraic coefficients, applied to
`Σ_q (A_p(q)−a·1_{q=p})log q=0`, gives `A_p(q)=a·1_{q=p}`. Hence `a=n∈ℕ`
and `A_p=n e_p`, proving the claimed form. Conversely, those polynomials
send `O(t)` to `O(nt+b)`. Injectivity of `O`, evaluated at times zero and
one, proves uniqueness of `b` and `n`.

For integer coefficients, each `c_p` is an integer of complex modulus one,
so `c_p²=1`. Absence of common nonzero torsion returns forces `b=0`.
A fixed orbit point is exactly a solution of `(n−1)t+b=0`. Two distinct
solutions force `n=1,b=0`, the identity. If `n=1,b≠0` there are no fixed
points; if `n≠1` there is exactly one, `t=−b/(n−1)`.

## Lean verification
All six modules passed final `lake --old env lean <module>.lean` checks.
Every audited declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. Uniqueness, identity, both fixed-point cases, and the
integral endomorphism classification were audited explicitly.

| Module | Main declaration |
|---|---|
| `FiniteUnitSpectrum` | `finiteExpWave_unit_support` |
| `PolynomialUnitOrbit` | `complexOrbitValue_unit_monomial` |
| `PrimeOrbitClockRigidity` | `prime_character_clock_linear` |
| `FinitePrimeClockMultipliers` | `prime_frequency_dilation_is_nat` |
| `PolynomialOrbitPreserversAreAdams` | `preservesPrimeOrbit_iff`, `translatedAdams_eq_iff`, `translatedAdams_fixed_iff`, `preservesPrimeOrbit_two_fixed_points` |
| `IntegralOrbitPreserversAreAdams` | `integerPreservesPrimeOrbit_iff`, `integer_endomorphism_is_adams` |

The determinant trick is `isIntegral_of_smul_mem_submodule`; algebraic
prime-logarithm independence is `RHTower.primeLog_algIndep` (standard
transitive axioms). Period-lattice rigidity uses
`addSubgroup_eq_bot_of_le_fg_of_nsmulDivisible`. Integral descent uses
`eq_zero_of_torsion_return`. The umbrella imports all six modules.
Corpus searches found no matching classification outside the new modules.
