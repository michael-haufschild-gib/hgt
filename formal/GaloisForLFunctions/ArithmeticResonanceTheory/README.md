# ArithmeticResonanceTheory (ART)

Namespace `GaloisForLFunctions.ArithmeticResonanceTheory`; umbrella `ArithmeticResonanceTheory.lean`; 16 modules.
All results unconditional; RH and zero-free strips appear only as conclusions of implications.

## 1. Motivation

Zeros of `ζ` are resonances (poles of a continuation), not spectra of any positive object the corpus owns.
Outside positivity, two mechanisms control resonances: **oscillation** (Dolgopyat: twisted transfer operators
contract, giving resonance-free strips) and **amplification** (Deligne: a family moment with loss fixed in the
tensor power gives the sharp bound for one member). Oscillation needs a **realization**: a dynamical system whose
dynamical zeta function is `ζ`. ART determines which realizations of the primes can exist, what each would give,
and what an amplifier over `ℤ` can and cannot do.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Prime zeta on ℝ | `primeZetaR` | `P(σ) = Σ_p p^{−σ}` |
| Commutative realization | `commEigen`, `commTrace` | disjoint loops `log p`; diagonal transfer operator, eigenvalues `p^{−s}` |
| Free realization | `freeTrace` | full shift on the prime alphabet; `n`-th trace `P(σ)^n` |
| Prime-length system | `IsPrimeLength`, `IsAdditivePrimeLength` | every primitive periodic orbit has exponentiated length a prime |
| Return words | `IsReturnWord`, `IsFirstReturn` | start at `a`, avoid `a`, close to `a` (finite-type / any alphabet) |
| Cycle family | `IsCycleFamily`, `cyclePoint`, `familyPoint`, `fixedPointFamily` | `(u^n v)^∞` shadowing `u^∞` |
| Finite graph zeta | `graphMatrix`, `graphZeta` | `M(s)_{ij} = Σ_{e:i→j} c_e e^{−s r_e}`, `exp Σ tr M^k/k` |
| Exponential polynomial | `IsExpPoly` | `Σ c_j e^{−λ_j s}`, `λ_j ∈ ℝ` |
| Oscillation | `phase`, `wordSum`, `twistedPrimeZeta`, `RelativeDolgopyat` | `e^{−itℓ}`; `‖Z_n(t)‖ ≤ Cρ^n z_n` for `t ≥ T` |
| Length spectrum | `massAt`, `OrbitIndex`, `orbitWeight`, `primeWeight`, `signedWeight`, `signedLength` | coefficient mass at a length; orbit side vs prime-power side |
| Defect chain | `IsDefectChain` | increasing primes with `p_{n+1} = a p_n + m_n` |
| Amplifier family | `IsBrauer`, `monomial` | degree-`k` monomials of unimodular phases orthogonal over the family |

External: `periodicZ`, `periodicSumR`, `birkhoff`, `IsAdmissible`, `IsMixing`, `IsHolderPotential`,
`exists_holomorphic_reciprocal` (HTGeometry symbolic dynamics); `exp_neg_traceSeries_eq_finiteDet2_neg`
(HTGeometry determinants); `RHTower.zetaResidueFactor`.

## 3. Language

- **Realization of `ζ`**: roof `φ ≥ r_min > 0` on a subshift with `ζ(s) = exp Σ_n Z_n(s)/n` on `Re s > 1`.
- **Spectral pole**: an eigenvalue of the transfer operator crosses 1. **Nuclearity pole**: trace norm diverges
  while spectral radius stays < 1.
- **Even / odd part**: denominator / numerator determinant of a virtual realization `det(1 − M⁻)/det(1 − M⁺)`;
  poles from even, zeros from odd.
- **Conformal defect**: integer `m_n = p_{n+1} − a p_n` along a cycle family; **conformal threshold**: distortion
  `a^{−n}`; **super-conformal**: below it.
- **Fixed loss**: moment loss `D` independent of tensor power `k`; **envelope loss**: `D_k = e^{2kλ}`.
- **Rank**: number of independent phases an amplifier must separate (`2g` over `F_q`, `π(y)` over `ℤ`).

## 4. Mechanisms

**A. Arithmetic obstructions**
1. Cunningham: modulo `ℓ = p_M > a`, `x ↦ ax + m` is a permutation; its orbit returns to 0, so `ℓ` divides a
   later member. Periodic defects reduce to slope `a^d` on residue classes of indices.
2. Pisot: a convergent integer sequence is eventually constant; super-conformal ratios make `p_{n+1} − a p_n → 0`.
3. Unique factorization: concatenating two first-return words of an additive roof gives a primitive orbit of
   length `log(pq)`; a periodic orbit carries mass ≥ 1 at its length, a prime power `p^{k+1}` only `1/(k+1)`.
4. Trivial zeros: they lie on a real progression; an exponential polynomial vanishing there is identically zero.
5. Congruence forcing: if a fixed modulus determines a bounded defect, residues follow a self-map of `ZMod L`
   and defects become periodic.

**B. Analytic tools**
6. Bounded distortion: Hölder roof ⇒ one-step law `|φ^{P(n+1)} − φ^L(y) − φ^{P(n)}| ≤ 2C θ^{nL}/(1 − θ)`.
7. Determinant identity `det(1 − A) = exp(−Σ tr A^k/k)` for small entries ⇒ graph zeta = `1/det` (entire).
8. Uniqueness of generalized Dirichlet series with locally finite frequencies (least bad frequency, gap, tail).
9. Ruelle–Pollicott continuation + identity theorem through the residue factor `(s − 1)ζ(s)`.
10. Dirichlet simultaneous approximation: finitely many phases return to 1 at arbitrarily large `t`; absolutely
    convergent sums return to their untwisted value.

**C. Amplifier calculus**
11. Rate = depth: a difference operator peels frequencies; almost periodic sums → 0 have zero coefficients.
12. Moments lose a root `D^{1/2k}`; positivity transfers family moments to members.
13. Orthogonality: monomial vectors are orthogonal in `ℂ^X`; multinomial expansion + Cauchy–Schwarz.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Commutative realization realizes `ζ`; its pole is a nuclearity pole | `exp_tsum_commTrace_eq_riemannZeta`, `commutative_pole_is_nuclear` | proved |
| Free realization: zeta `(1 − P)^{−1}`, spectral pole at unique `σ* ∈ (1,2)` | `exp_tsum_freeTrace_eq`, `free_pole_is_spectral` | proved |
| Additive prime-length shifts have one first-return word per symbol (commutative); free not prime-length | `firstReturn_unique`, `not_isAdditivePrimeLength_full` | proved |
| Even realizations are pole-only; `ζ` is no finite graph zeta | `graphZeta_mul_det_eq_one`, `riemannZeta_ne_graphZeta` | proved |
| `ζ` is no finite virtual realization (archimedean place) | `riemannZeta_ne_virtualRealization`, `eq_zero_of_vanish_on_progression` | proved |
| `F_q` calibration: zeros = spectrum of `F`, vertical periodicity, RH = unitarity | `det_one_sub_cpow_smul_eq_zero_iff`, `cpow_add_period`, `re_eq_half_of_norm_eigenvalue` | proved |
| Every realization of `ζ` on an SFT is prime-length | `isPrimeLength_of_realization`, `massAt_eq_zero_of_tsum_eq_zero` | proved |
| No affine recurrence, periodic defect, super-conformal ratio or conformal expansion for primes | `not_eventually_affine_recurrence`, `not_eventually_periodic_defect`, `not_eventually_prime_of_ratio`, `not_eventually_prime_of_conformal_expansion` | proved |
| Cycle law `a θ^L ≥ 1`; `θ^{|u|}e^{φ^{|u|}(u^∞)} ≥ 1` on every re-enterable cycle | `one_le_mul_pow_of_cycleFamily`, `one_le_exp_mul_pow_of_returnWords`, `one_le_exp_mul_of_isPrimeLength` | proved |
| Hölder realization ⇒ zero-free strip `Re s > 1 − ε`, at price `θ ≥ p_u^{−1/|u|}` | `riemannZeta_ne_zero_of_holderRealization`, `one_le_exp_mul_pow_of_holderRealization` | proved |
| No relative Dolgopyat bound on finite additive or free realizations | `not_relativeDolgopyat_of_finite_edges`, `not_relativeDolgopyat_free`, `norm_commEigen_twist` | proved |
| Amplifier law: fixed loss ⇒ sharp bound and pole-killing; envelope loss attained | `norm_le_of_fixed_loss`, `pole_coefficient_eq_zero`, `envelope_moment_bound_attained` | proved |
| Rank law: Brauer families never beat the trivial bound; cost → 1 at fixed rank, ≥ `r/k` | `pow_sum_le_moment_of_isBrauer`, `tendsto_choose_rpow_inv_of_fixed_rank`, `rank_div_le_choose_rpow_inv` | proved |
| Mills boundary: no prime `⌊Ca^n⌋` for `a = 2..6`; none within ½ of `Ca^n` for `a = 2,4,5`; small-defect chains excluded | `not_eventually_prime_floor`, `not_eventually_prime_near`, `not_isDefectChain_of_even`, `not_isDefectChain_of_odd` | proved |
| A realization of `ζ` (or exclusion) at/below the conformal threshold; an identity amplifier over `ℤ` | — | open |

## 6. Tools

**Developed**
- Realization calculus: cycle families, return words, primitive-period lemmas, prime-length systems.
- Length-spectrum reader: uniqueness of generalized Dirichlet series with repeated frequencies.
- Arithmetic obstructions: Cunningham, Pisot, unique factorization, trivial-zero progression, congruence forcing.
- Realization → strip bridge (Ruelle–Pollicott + residue factor).
- Oscillation diagnostics: phases, simultaneous returns, relative Dolgopyat bounds.
- Amplifier calculus: rate = depth, moment roots, fixed/envelope losses, pole-killing, rank law.
- Exponential-polynomial algebra and the graph determinant identity.

**To build**
- Growing-moduli congruence arguments for bounded defects not forced by a fixed modulus.
- Non-additive realizations on countable alphabets (Gurevich pressure, non-quasi-compact transfer operators).
- Infinite-rank odd parts carrying the Gamma factor's trivial zeros.
- Identity amplifiers: family moments evaluated by an explicit formula with loss fixed in `k`.

## 7. Open questions

1. Does a prime sequence `p_n = Ca^n + O(1)` exist? Open where congruences do not force the defect: `±1` with
   `6 | a`, `±2` with `a = 3`, integer parts for `a ≥ 7`, nearest integers for `a = 3` and `a ≥ 6`.
2. Construct or exclude Hölder realizations of `ζ` satisfying the cycle law `θ^{|u|}p_u ≥ 1` everywhere; relate
   admissible `θ` to strip width.
3. Non-additive realizations over the infinite prime alphabet: continuation and where oscillation is needed.
4. Virtual realizations with infinite-dimensional odd part: what carries the nontrivial zeros?
5. Is there a family moment over `ℤ` evaluated by an identity with loss fixed in `k`?
6. Classify existing amplifier attempts (fixed, envelope, or rank-limited loss).

## 8. Traps

| Trap | Fact |
|---|---|
| `ζ` is the zeta of prime dynamics | Only of the commutative realization, which has no mixing |
| Mixing the prime loops keeps `ζ` | Free mixing gives `(1 − P)^{−1}` with entropy `σ* > 1` |
| The pole at 1 is a Perron–Frobenius eigenvalue | Commutative spectral radius ≤ ½ on `σ ≥ 1`; the pole is a nuclearity breakdown |
| Oscillation produces the strip | In a finite-type Hölder realization the strip comes from continuation alone |
| A smoother roof is a better realization | Integrality forbids super-conformal roofs: `θ ≥ p_u^{−1/|u|}` |
| A finite odd part can carry the zeros | Trivial zeros on a real progression kill every finite odd determinant |
| Independent lengths help oscillation | Simultaneous approximation returns all phases; additive data never contract uniformly |
| A small moment constant amplifies | Only the growth of the loss in `k` matters; envelope losses are attained |
| Orthogonality amplifies | It pays for itself exactly (`C(r+k−1,k)` members) |
| These obstructions are analytic | They use integrality and unique factorization; Beurling systems escape them |
| "Realization" is a picture | The zeta identity forces prime-length by Dirichlet-series uniqueness |

## 9. Context

**Uses** (import counts): HTGeometry 4 (SymbolicShiftSpace, SymbolicRuellePollicott, FiniteDeterminantLogSeries,
DirichletSimultaneousApproximation), RHTower 2 (ZetaResidueFactorDerivative). Seven modules use Mathlib only.

**Used by**: none (umbrella only).

| Neighbour | Relation |
|---|---|
| HTGeometry symbolic dynamics | Shift spaces, Birkhoff sums, Hölder potentials, Ruelle–Pollicott continuation reused here |
| RHTower (`RuelleZetaNuclearZeroFree`, `DensityEnvelopeNoGo`, `ZetaMultipleLandauZeroFree`) | Nuclear Markov zetas are zero-free; existing envelope/amplifier attempts that the amplifier law classifies |
| HilbertianExplicitFormulas, ConjugateDiagonalGeometry | Why explicit formulas see reflection pairings, not spectra: the resonance side ART works on |
| ArithmeticCastelnuovoSeveri | Finite-field calibration; the rank law is the counting form of infinite genus |
| ArithmeticPositiveDuality | Bost–Connes partition function = commutative realization's zeta |
| DilutionCrystallizationPincer | Kronecker/Baker independence on the prime torus, the same that defeats additive oscillation |
| TransThresholdPairCorrelation | Tensor powers of scale traces as prime correlations: candidate identity amplifier at level 2 |
| ArithmeticOrientationGeometry, SquareRootThreshold | Rate-equals-depth laws used as the amplifier's engine |

## 10. Big picture

ART asks whether the two non-positive mechanisms that prove resonance bounds elsewhere, oscillation and
amplification, can be brought to `ζ`. The answer is a sharp map of obstructions. Every realization of `ζ` by a
dynamical system is forced to be prime-length, additive ones collapse to the trivial commutative one, finite ones
are excluded by the archimedean place, and the regularity of any Hölder realization is bounded by integrality
along every cycle. Such a realization would immediately give a zero-free strip, which is why the obstructions are
so strong: the difficulty is not the oscillation but the existence of the system.

For amplification, the finite-field proof works because rank is finite; over `ℤ` orthogonality costs exactly what
it gains, so any amplifier must evaluate its moments by an arithmetic identity rather than by orthogonality. For
the RH effort this says that neither a transfer-operator picture of the primes nor a Deligne-style family moment
is available off the shelf; both require a genuinely new arithmetic input (a non-additive realization or an
identity with fixed loss), and integrality, unique factorization and the Gamma factor are the precise constraints
it must respect.
