# Polynomial orbit preservers are translated Adams operations

- **ID:** alst-orbit-preserving-endomorphisms-are-adams
- **Stage:** 2-fully-proven
- **Status:** Paper proof complete; Lean formalization pending. Uncounted.
- **Statement:** Let `P` be a finite set containing two distinct primes. Every complex polynomial self-map preserving `O(t)=(p^(−it))_{p∈P}` has the unique form `F_p(X)=p^(−ib)X_p^n`, with `n∈ℕ`, `b∈ℝ`. Its clock is `t↦nt+b`, without any regularity assumption. Over `ℤ`, `b=0`: the endomorphisms are exactly Adams operations.

## Research consequence
This classifies all exact polynomial Frobenius candidates preserving the
prime orbit. A nonidentity candidate cannot fix two orbit points. Changing
the polynomial map within this algebra cannot supply a Frobenius with many
fixed orbit points. The positive result is the full classification,
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

## Formal inputs and obligations
- `finiteExpWave_unit_support`, `complexOrbitValue_unit_monomial`, `prime_character_clock_linear`, `prime_frequency_dilation_is_nat`: Lean checked; standard axioms only.
- `preservesPrimeOrbit_iff`, `preservesPrimeOrbit_two_fixed_points`: Lean checked; standard axioms only.
- `RHTower.primeLog_algIndep`: transitive audit contains only `propext`, `Classical.choice`, `Quot.sound`.
- `isIntegral_of_smul_mem_submodule`: the determinant trick.
- `addSubgroup_eq_bot_of_le_fg_of_nsmulDivisible`: period-lattice rigidity.
- `eq_zero_of_torsion_return`: removes integral translation factors.

`integerPreservesPrimeOrbit_iff` and `integer_endomorphism_is_adams` passed
the final plain module check with standard axioms only. Final plain checks
of the five supporting modules remain required.
Corpus searches found no matching classification outside the new modules.
