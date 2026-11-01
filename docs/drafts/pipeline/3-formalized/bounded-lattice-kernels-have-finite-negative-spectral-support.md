# Bounded lattice kernels and finite negative spectral support

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4; transitive axioms audited)
- **Obstacle:** route-obstacles B9, converse Krein–Langer without a zero configuration.
- **Statement:** A bounded Hermitian kernel on a countable free abelian group has
  finite negative index iff it is positive definite minus a finite positive
  combination of distinct unitary characters. The least number of negative
  characters equals its negative index. This includes the Hecke lattice of
  positive rationals. Among finite-index kernels, boundedness is exactly the
  existence of such an index-sized unitary decomposition.
- **Boundary:** The general unbounded converse remains open. No RH consequence
  or complete resolution of B9 is claimed.

## Proof

Write the group additively as `G = ⊕_I ℤ`, its compact dual as `T = (ℝ/ℤ)^I`,
and its characters as `χ_t(θ)`. Suppose `κ(k) = m < ∞` and `k` is bounded.

### Bounded corrections and signed spectral representation

The corpus Pontryagin decomposition gives
`φ_i(g) = Σ_b w_ib k(g−x_b)`, for `1 ≤ i ≤ m`, such that every finite packet
satisfies

`Σ_ab conjugate(c_a)c_b k(x_b−x_a) + Σ_i |Σ_a c_a φ_i(x_a)|² ≥ 0`.

The first term is real. Boundedness of `k` gives one constant `C` with
`|φ_i(g)| ≤ C` for all `i,g` (`exists_bounded_pontryagin_corrections`).

For a nonempty finite box `W`, use the packet `c_x = χ_{−x}(θ)` and divide by
`|W|`. Its Toeplitz term is a continuous real density `d_W`; its correction
term is the continuous nonnegative density

`q_W(θ) = |W|⁻¹ Σ_i |Σ_{x∈W} φ_i(x)χ_{−x}(θ)|²`.

Thus `d_W + q_W ≥ 0`. Haar orthogonality gives
`∫q_W = |W|⁻¹Σ_iΣ_{x∈W}|φ_i(x)|² ≤ mC²` and `∫d_W = k(0)`.
The positive measures `(d_W+q_W)dθ` and `q_W dθ` therefore have uniformly
bounded masses, for example by `|k(0)| + mC² + 1`.

Take `W = [0,N]^F`, extended by zero outside the finite coordinate set `F`.
The Fourier coefficient of their difference at `t` is

`k(t) · #{(x,y)∈W² : y−x=t}/|W|`.

When `support(t) ⊆ F`, this normalized count is the Fejér product over
`support(t)`: every extra zero coordinate contributes one. Each factor tends
to one as `N → ∞`. Hence the coefficient tends to `k(t)` along the product
filter of expanding `F` and expanding `N`.

Finite positive measures of uniformly bounded mass on compact `T` form a
compact space. A cluster point of the measure pairs retains every Fourier
coefficient, since integration of each continuous character is continuous.
Jordan reduction gives mutually singular finite positive measures `P,N` with

`k(t) = ∫χ_t dP − ∫χ_t dN`.

### Finite negative support

The translate correction has continuous density
`q_i(θ) = Σ_b w_ib χ_{−x_b}(θ)`:
`φ_i(t) = ∫q_iχ_t dP − ∫q_iχ_t dN`.
Writing `ρ = P+N`, the corrected packet inequality is therefore

`∫|f|²dP − ∫|f|²dN + Σ_i |∫q_if dP − ∫q_if dN|² ≥ 0`

for every finite character packet `f`. The character span is uniformly dense
in `C(T)`, and continuous functions are dense in `L²(ρ)`. The signed energy
and the finitely many integral functionals are continuous on `L²(ρ)`:
use the bounded Jordan sign multiplier for the energy, and Cauchy–Schwarz
for the functionals. The inequality holds for all `L²(ρ)` tests.

Let `H` be a negative Hahn set, so `P(H)=0`, `N(Hᶜ)=0`. The densities `q_i`
are bounded; choose `D` bounding all their norms. For measurable `A`, test
with `1_{A∩H}`. The inequality gives

`N(A) ≤ mD² N(A)²`.

Consequently every positive-mass measurable set has mass at least
`1/(mD²+1)`. If the support of `N` were infinite, the corpus theorem
`InfiniteSupportPositiveAperture` would provide arbitrarily many disjoint
positive-mass measurable sets, contradicting finiteness of `N(T)`.
Thus `N = Σ_{j=1}^r a_j δ_{θ_j}`, with distinct `θ_j` and `a_j>0`.

### Exact index and decomposition

Mutual singularity gives `P({θ_j})=0`. For arbitrary `z∈ℂ^r`, test the extended
inequality with the function supported on these atoms and taking value `z_j`
at `θ_j`. It gives

`Σ_j a_j|z_j|² ≤ Σ_i |Σ_j a_j q_i(θ_j) z_j|²`.

The displayed linear map from `ℂ^r` to `ℂ^m` is injective; hence `r≤m`.
Fourier transformation of the atomic representation gives

`k(t) = p(t) − Σ_j a_j χ_t(θ_j)`, where `p(t)=∫χ_t dP` is positive definite.

The characters are unitary and distinct. The corpus index bound for a
positive-definite kernel plus `r` character pairs gives `m≤r`, so `r=m`.
The same bound applied to any competing decomposition proves minimality.

Conversely every finite such decomposition has finite negative index by that
bound. It is bounded because `|p(t)|≤p(0)` and each character has modulus one.
This also proves the claimed boundedness/unitary-decomposition equivalence.

The existing prime-valuation equivalence identifies `⊕_p ℤ` multiplicatively
with positive rationals. Its multiplicativity is
`RHTower.BAGTrace.rationalOfValuations_add`; AKG
`negIndex_comp_of_surjective` preserves the index under this equivalence.
Pullback and descent transfer the theorem to the full Hecke lattice.

## Novelty and Lean status

The earlier Pontryagin theorem supplies corrections depending separately on
packet points. It does not supply a positive-definite group kernel or unitary
characters. The new steps are uniform Fejér correction masses, a signed
spectral representation, and finite negative support with exact atom count.
No existing bounded classification surfaced in the final corpus audit.

Lean capstones in `GaloisForLFunctions.HeckeKreinToeplitz`:

| Declaration | Content |
|---|---|
| `bounded_free_lattice_krein_langer` | Exact-index decomposition on every countable free abelian group |
| `bounded_free_lattice_finite_index_iff` | Finite index iff a finite positive unitary-character subtraction |
| `negative_index_le_unitary_decomposition_size` | Minimality of the character count |
| `finite_index_bounded_iff_unitary_decomposition` | Exact boundedness boundary on the finite stratum |
| `bounded_hecke_krein_langer` | The full positive-rational Hecke lattice |

Modules: `HeckeKreinToeplitz/Index/BoundedKreinLanger.lean` and
`HeckeKreinToeplitz/Index/HeckeBoundedKreinLanger.lean`. Both direct checks pass;
all capstone axiom audits contain exactly `propext`, `Classical.choice`,
`Quot.sound`. Supporting modules compile and both programme umbrellas are wired.
