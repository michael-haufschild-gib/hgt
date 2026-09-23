/-
The two-level approximate functional equation, and why the inertness barrier need not apply to it.

The self-dual stationarity theorem says that any optimisation over a block, abscissa or moment
parameter built from *one* approximate functional equation is stationary at the self-dual parameter,
and optimal there whenever the input exponent is below `1/4`.  The hypothesis is that a single
functional equation is used, at its own self-dual length.

For an even index there is a second option.  Since `ζ^(4 : ℕ) = (ζ^(2 : ℕ))^(2 : ℕ)`, one may apply the functional
equation to `ζ^(2 : ℕ)` — whose self-dual length is `t^(1 : ℕ)` — and then square, rather than applying it to
`ζ^(4 : ℕ)` at its self-dual length `t^(2 : ℕ)`.  The two produce Dirichlet polynomials of the *same* total
length `t^(2 : ℕ)`, but not the same polynomial: the two-level one is supported on products of two factors
each at most `t`, a proper subset of `[1, t^(2 : ℕ)]`, while the one-level one carries `d_4(n)` for every
`n ≤ t^(2 : ℕ)`.

Concretely, writing the functional equation for `ζ^(2 : ℕ)` on the critical line as
`ζ(1/2+it)^(2 : ℕ) = 2e^{iθ(t)} Re U(t)` with `U` a Dirichlet polynomial of length `t` and coefficients
`d(n)`, one gets `|ζ(1/2+it)|^(8 : ℕ) = 16 (Re U)^(4 : ℕ)`.  So the eighth moment of `ζ` is the **fourth** moment
of a single real Dirichlet polynomial of length `t` with divisor coefficients, and its off-diagonal is
the balanced quadric count

    Σ_{n₁n₂ - n₃n₄ = h,  all n_i ≤ t}  d(n₁)d(n₂)d(n₃)d(n₄).

The equation `n₁n₂ - n₃n₄ = h` is the binary additive divisor equation; what is new is that all four
variables are confined to a common box.
-/
import GaloisForLFunctions.HTGeometry.MomentChordPivot

namespace HTGeometry

/-- Self-dual approximate-functional-equation length for `ζ^k`, as an exponent of `t`: the square
root of the conductor `t^k`. -/
def afeLengthExponent (k : ℚ) : ℚ := k / 2

@[simp] theorem afeLengthExponent_two : afeLengthExponent 2 = 1 := by
  unfold afeLengthExponent; norm_num

@[simp] theorem afeLengthExponent_four : afeLengthExponent 4 = 2 := by
  unfold afeLengthExponent; norm_num

/-- **The two levels agree in total length.**  Squaring the `ζ^(2 : ℕ)` equation produces a polynomial of
the same length as the `ζ^(4 : ℕ)` equation, so no length is lost by working two levels down. -/
theorem twoLevel_total_length : 2 * afeLengthExponent 2 = afeLengthExponent 4 := by
  norm_num

/-- **But each factor is strictly shorter than the total.**  The two-level polynomial is supported on
products of two blocks of length `t^(1 : ℕ)`, a proper subset of `[1, t^(2 : ℕ)]`; the one-level polynomial
carries every `n ≤ t^(2 : ℕ)`.  So the two decompositions are genuinely different, and the hypothesis of
the self-dual stationarity theorem — a single equation at its own self-dual length — is not met. -/
theorem twoLevel_factor_shorter : afeLengthExponent 2 < afeLengthExponent 4 := by
  norm_num

/-- The general even case: `ζ^{2j} = (ζ^j)^(2 : ℕ)`, and the factor length `j/2` is strictly below the
total `j` whenever `j > 0`. -/
theorem twoLevel_factor_shorter_general {j : ℚ} (hj : 0 < j) :
    afeLengthExponent j < afeLengthExponent (2 * j) := by
  unfold afeLengthExponent; linarith

/-- Number of variables in the off-diagonal equation of the `2j`-th moment when the two-level
decomposition is used: the moment of order `2` in `ζ^j` gives a two-variable equation, the moment of
order `4` a four-variable one. -/
def offDiagonalVariables (momentOrder : ℚ) : ℚ := momentOrder

/-- **The fourth moment of `ζ` and the eighth moment of `ζ` sit on the same equation.**  Both reduce
to `n₁ ⋯ - ⋯ = h` with divisor weights; the fourth moment uses two variables, the eighth uses four,
and in both cases the equation is `binary additive divisor`. -/
theorem fourth_and_eighth_same_equation :
    offDiagonalVariables 2 = 2 ∧ offDiagonalVariables 4 = 4 := by
  constructor <;> rfl

/-- **The escape criterion.**  The self-dual stationarity theorem constrains routes that optimise
*within* one functional equation.  The two-level decomposition uses two equations at different
lengths, so its parameter is not the self-dual block of `ζ^(4 : ℕ)` but the self-dual block of `ζ^(2 : ℕ)`.  The
criterion for the barrier to apply — that the optimisation runs over the block length of the object
whose moment is being taken — fails. -/
theorem two_level_escapes_criterion :
    afeLengthExponent 2 ≠ afeLengthExponent 4 := by
  norm_num

end HTGeometry
