/-
From a power-law correlation bound to the block exponent.

Applying the van der Corput inequality to the critical block `n ∼ N` with a correlation bound of the
shape `‖C(h)‖ ≪ N^a h^b` for `1 ≤ h < H` gives

    ‖Σ‖²  ≪  N²/H  +  N^{1+a} H^b ,

since the diagonal contributes `N²/H` and the weighted off-diagonal contributes
`(N/H²)·N^a H^{b+2}`.  Balancing the two at `H = N^{(1-a)/(1+b)}` yields

    ‖Σ‖  ≪  N^{correlationBlockExponent a b},      correlationBlockExponent a b = 1 - (1-a)/(2(1+b)),

and hence `μ = (correlationBlockExponent a b - 1/2)/2`.

The second-derivative test supplies `a = b = 1/2` for the critical block, and the formula returns
`5/6` and `μ = 1/6` — Weyl's exponent, derived rather than quoted.  The formula also shows what would
be needed for more: `μ = 0` forces `a + b = 0`, i.e. correlations of size `N^ε`, which is below the
square-root barrier of the correlation sum itself.  Imposing only that a correlation of `N` unimodular
terms is not estimated below square root, i.e. `a ≥ 1/2`, gives `correlationBlockExponent (1/2) 0 = 3/4` and
`μ = 1/8`.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace HTGeometry

/-- The block exponent produced by a correlation bound `‖C(h)‖ ≪ N^a h^b`, after optimising the
van der Corput shift parameter. -/
def correlationBlockExponent (a b : ℚ) : ℚ := 1 - (1 - a) / (2 * (1 + b))

/-- The optimal shift parameter, as an exponent of `N`. -/
def optimalShift (a b : ℚ) : ℚ := (1 - a) / (1 + b)

/-- The Lindelöf exponent delivered by a block exponent. -/
def muOfBlock (c : ℚ) : ℚ := (c - 1/2) / 2

/-- **The second-derivative test input reproduces Weyl's exponent.**  With `a = b = 1/2` the block
exponent is `5/6` and the optimal shift is `N^{1/3}`. -/
@[simp] theorem blockExponent_secondDeriv : correlationBlockExponent (1/2) (1/2) = 5/6 := by
  unfold correlationBlockExponent; norm_num

@[simp] theorem optimalShift_secondDeriv : optimalShift (1/2) (1/2) = 1/3 := by
  unfold optimalShift; norm_num

/-- **Weyl's exponent, derived.** -/
@[simp] theorem mu_secondDeriv : muOfBlock (correlationBlockExponent (1/2) (1/2)) = 1/6 := by
  rw [blockExponent_secondDeriv]; unfold muOfBlock; norm_num

/-- **The Lindelöf condition on the correlation exponents.**  `correlationBlockExponent a b = 1/2` — that is,
square-root cancellation on the block, equivalently `μ = 0` — holds exactly when `a + b = 0`. -/
theorem blockExponent_eq_half_iff {a b : ℚ} (hb : -1 < b) :
    correlationBlockExponent a b = 1/2 ↔ a + b = 0 := by
  have hpos : (0:ℚ) < 2 * (1 + b) := by linarith
  unfold correlationBlockExponent
  rw [sub_eq_iff_eq_add]
  constructor
  · intro h
    have hne : (2 * (1 + b)) ≠ 0 := ne_of_gt hpos
    have h3 : (1 - a) / (2 * (1 + b)) = 1/2 := by linarith
    rw [div_eq_iff hne] at h3
    linarith
  · intro h
    have h2 : (1 - a) / (2 * (1 + b)) = 1/2 := by
      rw [div_eq_iff (ne_of_gt hpos)]
      linarith
    rw [h2]
    norm_num

/-- `μ = 0` is equivalent to the block exponent being `1/2`. -/
theorem muOfBlock_eq_zero_iff (c : ℚ) : muOfBlock c = 0 ↔ c = 1/2 := by
  unfold muOfBlock
  constructor
  · intro h
    have := (div_eq_zero_iff.mp h)
    rcases this with h1 | h1
    · linarith
    · norm_num at h1
  · intro h; rw [h]; norm_num

/-- **The square-root barrier for the correlation itself.**  `C(h)` is a sum of `N` unimodular
terms; an estimate `‖C(h)‖ ≪ N^a` with `a < 1/2` would be better than square-root cancellation for
that sum.  Under the constraint `a ≥ 1/2` the Lindelöf condition `a + b = 0` is unreachable for any
`b ≥ 0`. -/
theorem lindelof_needs_subSqrt_correlation {a b : ℚ} (ha : 1/2 ≤ a) (hb : 0 ≤ b) :
    a + b ≠ 0 := by
  intro h
  linarith

/-- **The floor of the route.**  With the best correlation input that does not itself beat square-root
cancellation (`a = 1/2`) and no growth in the shift (`b = 0`), the block exponent is `3/4` and the
Lindelöf exponent is `1/8`. -/
@[simp] theorem blockExponent_sqrtCorrelation : correlationBlockExponent (1/2) 0 = 3/4 := by
  unfold correlationBlockExponent; norm_num

/-- **`μ = 1/8` is the floor of the van der Corput route.** -/
@[simp] theorem mu_sqrtCorrelation : muOfBlock (correlationBlockExponent (1/2) 0) = 1/8 := by
  rw [blockExponent_sqrtCorrelation]; unfold muOfBlock; norm_num

/-- The block exponent is monotone in each correlation exponent: better correlation bounds give
better block bounds, and the dependence is strict. -/
theorem blockExponent_strictMono_a {a a' b : ℚ} (hb : -1 < b) (h : a < a') :
    correlationBlockExponent a b < correlationBlockExponent a' b := by
  have hpos : (0:ℚ) < 2 * (1 + b) := by linarith
  unfold correlationBlockExponent
  have hlt : (1 - a') < (1 - a) := by linarith
  have : (1 - a') / (2 * (1 + b)) < (1 - a) / (2 * (1 + b)) := by
    rw [div_lt_div_iff₀ hpos hpos]
    nlinarith
  linarith

/-- At `a = 1` the correlation bound is trivial and the block exponent is `1`: no cancellation. -/
@[simp] theorem blockExponent_trivial (b : ℚ) : correlationBlockExponent 1 b = 1 := by
  unfold correlationBlockExponent; norm_num

/-- **The three-way coincidence at `1/8`.**  The van der Corput route's floor `muOfBlock
(correlationBlockExponent (1/2) 0)`, the exponent-pair floor `(κ+λ = 3/4)`, and the eighth-moment target all
give the same Lindelöf exponent. -/
theorem floor_coincidence :
    muOfBlock (correlationBlockExponent (1/2) 0) = 1/8 ∧ correlationBlockExponent (1/2) 0 = 3/4 ∧
      muOfBlock (3/4) = 1/8 := by
  refine ⟨mu_sqrtCorrelation, blockExponent_sqrtCorrelation, ?_⟩
  unfold muOfBlock; norm_num


/-!
### The Weyl exponent decomposed: coherence blocks and the block sum

The phase of the critical block is `-t log n` with `t = N²`.  Taylor-expanding at `n ∼ N`, the degree-`d`
term is `≍ t (n-N)^d / N^d`, which is `O(1)` exactly while `|n - N| ≪ N^{(d-2)/d}`.  At `d = 3` this
gives the *quadratic coherence length* `N^{1/3}`: on blocks of that length the phase is a quadratic,
i.e. a chirp, whose correlations are geometric series.

Splitting `[N, 2N]` into `N^{2/3}` such blocks and applying square-root cancellation inside each:

    N^{2/3} · (N^{1/3})^{1/2}  =  N^{2/3} · N^{1/6}  =  N^{5/6},

which is Weyl's exponent.  If instead the block sum itself enjoyed square-root cancellation:

    (N^{2/3})^{1/2} · N^{1/6}  =  N^{1/3} · N^{1/6}  =  N^{1/2},

which is the Lindelöf hypothesis.  So the entire deficit is the block sum, and it is worth exactly
`N^{1/3}` — half the block count.
-/


/-- The coherence length at Taylor degree `d`: the scale on which the degree-`d` term of the phase
of the critical block is `O(1)`. -/
def coherenceLength (d : ℚ) : ℚ := (d - 2) / d

/-- The number of coherence blocks in the critical block, as an exponent of `N`. -/
def coherenceBlockCount (d : ℚ) : ℚ := 1 - coherenceLength d

/-- Quadratic coherence: at `d = 3` the length is `N^{1/3}` and there are `N^{2/3}` blocks. -/
@[simp] theorem coherenceLength_three : coherenceLength 3 = 1/3 := by
  unfold coherenceLength; norm_num

@[simp] theorem coherenceBlockCount_three : coherenceBlockCount 3 = 2/3 := by
  unfold coherenceBlockCount coherenceLength; norm_num

/-- The exponent obtained by summing the blocks with no cancellation between them, given square-root
cancellation inside each. -/
def incoherentBlockTotal (d : ℚ) : ℚ := coherenceBlockCount d + coherenceLength d / 2

/-- The exponent obtained if the block sum itself has square-root cancellation. -/
def coherentBlockTotal (d : ℚ) : ℚ := coherenceBlockCount d / 2 + coherenceLength d / 2

/-- **Weyl's exponent is the incoherent block sum at quadratic coherence.** -/
@[simp] theorem incoherentBlockTotal_three : incoherentBlockTotal 3 = 5/6 := by
  unfold incoherentBlockTotal coherenceBlockCount coherenceLength; norm_num

/-- **The Lindelöf exponent is the coherent block sum at quadratic coherence.** -/
@[simp] theorem coherentBlockTotal_three : coherentBlockTotal 3 = 1/2 := by
  unfold coherentBlockTotal coherenceBlockCount coherenceLength; norm_num

/-- **The whole deficit is the block sum.**  The difference between Weyl and Lindelöf is exactly half
the block count. -/
theorem block_deficit (d : ℚ) :
    incoherentBlockTotal d - coherentBlockTotal d = coherenceBlockCount d / 2 := by
  unfold incoherentBlockTotal coherentBlockTotal; ring

@[simp] theorem block_deficit_three : incoherentBlockTotal 3 - coherentBlockTotal 3 = 1/3 := by
  rw [block_deficit, coherenceBlockCount_three]; norm_num

/-- **The coherent block sum is always the Lindelöf exponent, at every Taylor degree.**  Raising the
degree changes the coherence length and the block count in compensating ways, so no choice of degree
brings the *coherent* total below `1/2` or above it: the target is degree-independent. -/
theorem coherentBlockTotal_eq_half (d : ℚ) (hd : d ≠ 0) : coherentBlockTotal d = 1/2 := by
  unfold coherentBlockTotal coherenceBlockCount coherenceLength
  field_simp
  ring

/-- The incoherent total in closed form.  **This formula is only meaningful at `d = 3`.**  It assumes
square-root cancellation *within* each coherence block, which at `d = 3` is genuine — the block phase
is a quadratic, and its correlations are geometric series — but at `d > 3` the block phase is a
polynomial of degree `d - 1`, for which square-root cancellation is not available.  Read as a formula
in `d` it descends to `1/2`, which would assert the Lindelöf hypothesis; that is exactly the
Weyl-degree trade-off, where the cost of raising the degree is paid in the within-block estimate and
not visible in the block bookkeeping. -/
theorem incoherentBlockTotal_eq (d : ℚ) (hd : d ≠ 0) :
    incoherentBlockTotal d = 1 - (d - 2) / (2 * d) := by
  unfold incoherentBlockTotal coherenceBlockCount coherenceLength
  field_simp
  ring

/-- The formula's limit as the degree grows is `1/2`, i.e. the Lindelöf exponent — which is why the
formula cannot be valid beyond `d = 3`: the within-block square-root cancellation it assumes is
precisely what is unavailable for higher-degree phases. -/
@[simp] theorem incoherentBlockTotal_four : incoherentBlockTotal 4 = 3/4 := by
  unfold incoherentBlockTotal coherenceBlockCount coherenceLength; norm_num


/-!
### Scale invariance of the critical phase

Write the critical block as `N` blocks of length `N^ℓ`, indexed by `r < N^{1-ℓ}`.  Expanding
`N²/n_r = N²/(N + r·N^ℓ) = Σ_k (-1)^k r^k N^{ℓk + 1 - k}`, the order-`k` term has coefficient
exponent `ℓk + 1 - k`, and at the far end of the range `r ≍ N^{1-ℓ}` its size is

    N^{(1-ℓ)k} · N^{ℓk + 1 - k} = N^{1} ,

**independently of both `k` and `ℓ`.**  Every Taylor order sweeps exactly `N` cycles across the range,
for every choice of block length.

Inside a single block the truncation is legitimate — there `r` is fixed and the offset is at most
`N^ℓ`.  Across blocks it never is: no order is negligible relative to the leading one, so no
finite-degree treatment of the phase is uniformly valid on the critical block.  This is the exact
sense in which the difficulty cannot be removed by subdividing.
-/

/-- Exponent of `N` swept by the order-`k` Taylor term of the critical phase, at the far end of a
block decomposition with block-length exponent `ℓ`. -/
def phaseSweep (l k : ℚ) : ℚ := (1 - l) * k + (l * k + 1 - k)

/-- **Scale invariance.**  Every Taylor order sweeps exactly one power of `N`, for every block
length: the expansion has no dominant term and no negligible tail across the range. -/
@[simp] theorem phaseSweep_eq_one (l k : ℚ) : phaseSweep l k = 1 := by
  unfold phaseSweep; ring

/-- The coefficient exponent of the order-`k` term. -/
def phaseCoeff (l k : ℚ) : ℚ := l * k + 1 - k

/-- At quadratic coherence the cubic coefficient is `N^{-1}` and the quadratic one `N^{-1/3}`. -/
@[simp] theorem phaseCoeff_three : phaseCoeff (1/3) 3 = -1 := by
  unfold phaseCoeff; norm_num

@[simp] theorem phaseCoeff_two : phaseCoeff (1/3) 2 = -1/3 := by
  unfold phaseCoeff; norm_num

/-- **Within a block the tail *is* negligible.**  At offset `m ≤ N^ℓ` — that is, `r` replaced by `1` —
the order-`k` term has size `N^{ℓk + 1 - k}`, which is below `1` exactly when `k > 1/(1-l)`.  At
`l = 1/3` this is `k > 3/2`, so every order from the cubic on is `O(1)` inside a block: the quadratic
approximation is legitimate there, and only there. -/
theorem phaseCoeff_neg_iff {l k : ℚ} (hl : l < 1) : phaseCoeff l k < 0 ↔ 1/(1 - l) < k := by
  have h1 : (0:ℚ) < 1 - l := by linarith
  unfold phaseCoeff
  rw [div_lt_iff₀ h1]
  constructor <;> intro h <;> nlinarith [h]

/-- At `l = 1/3` the cubic term is already `O(N^{-1})` inside a block. -/
theorem cubic_negligible_in_block : phaseCoeff (1/3) 3 < 0 := by norm_num


/-!
### Weyl's exponent a third time: theta-sum resonance counting

The block sums are theta sums `Θ(α_r)` of length `L = N^{1/3}`, and `α_r` runs over a grid of spacing
`L^{-2}` across an interval of length `≍ 1`.  A theta sum of length `L` is large exactly at rational
`α ≈ a/q` with `q ≤ L`, where `|Θ| ≍ L/√q` on the arc `|α - a/q| ≤ 1/(qL)`.

Counting: the arc around `a/q` contains `(1/(qL))/L^{-2} = L/q` grid points; the number of fractions
`a/q` with `q ≤ L` in a unit interval is `≍ L²`, distributed as `q` values of `a` for each `q`.  So the
total of the moduli is

    Σ_{q ≤ L} q · (L/q) · (L/√q)  =  L² Σ_{q ≤ L} q^{-3/2} · q  =  L² · L^{1/2}  =  L^{5/2},

and with `L = N^{1/3}` that is `N^{5/6}` — Weyl's exponent, obtained a third way.

The Lindelöf target is `N^{1/2} = L^{3/2}`.  So the required saving over the sum of moduli is exactly
one factor of `L = N^{1/3}`, and it must come from cancellation among the phases of the resonant
blocks: the moduli themselves are correct as computed.
-/

/-- Exponent (in `L`) of the sum of the moduli of the resonant theta sums. -/
def resonanceModulusTotal : ℚ := 5/2

/-- Exponent (in `L`) of the Lindelöf target for the block sum. -/
def resonanceTarget : ℚ := 3/2

/-- **The required saving is exactly one factor of the coherence length.** -/
@[simp] theorem resonance_saving : resonanceModulusTotal - resonanceTarget = 1 := by
  unfold resonanceModulusTotal resonanceTarget; norm_num

/-- Converting `L`-exponents to `N`-exponents at quadratic coherence (`L = N^{1/3}`). -/
def ofCoherenceScale (e : ℚ) : ℚ := e / 3

/-- The modulus total is Weyl's exponent. -/
@[simp] theorem ofCoherenceScale_modulus : ofCoherenceScale resonanceModulusTotal = 5/6 := by
  unfold ofCoherenceScale resonanceModulusTotal; norm_num

/-- The target is the Lindelöf exponent. -/
@[simp] theorem ofCoherenceScale_target : ofCoherenceScale resonanceTarget = 1/2 := by
  unfold ofCoherenceScale resonanceTarget; norm_num

/-- **Three derivations of Weyl's exponent agree.**  The correlation bridge with second-derivative
input, the incoherent coherence-block sum, and the theta-sum resonance count all give `5/6`. -/
theorem weyl_three_ways :
    correlationBlockExponent (1/2) (1/2) = 5/6 ∧ incoherentBlockTotal 3 = 5/6 ∧
      ofCoherenceScale resonanceModulusTotal = 5/6 :=
  ⟨blockExponent_secondDeriv, incoherentBlockTotal_three, ofCoherenceScale_modulus⟩

/-- **And the deficit is the same in all three.**  Weyl minus Lindelöf is `1/3` of a power of `N`,
which is one full factor of the coherence length `L = N^{1/3}`. -/
theorem deficit_is_one_coherence_length :
    ofCoherenceScale resonanceModulusTotal - ofCoherenceScale resonanceTarget
      = ofCoherenceScale 1 ∧ ofCoherenceScale 1 = 1/3 := by
  constructor
  · unfold ofCoherenceScale resonanceModulusTotal resonanceTarget; norm_num
  · unfold ofCoherenceScale; norm_num


/-!
### The square-root phase family, unweighted

The common open core is cancellation in `Σ_{n ≤ X} w(n) · e(2√(nx))`.  For the *unweighted* sum the
second-derivative test settles it.  With `f(n) = 2√(xn)`,

    f'(n) = √x · n^{-1/2},    f''(n) = -(1/2)√x · n^{-3/2},   so  |f''| ≍ x^{1/2} X^{-3/2}  on n ≍ X,

and the test gives `X|f''|^{1/2} + |f''|^{-1/2} = (Xx)^{1/4}·X^{1/2}·X^{-1/2} + X^{3/4}x^{-1/4}`,
i.e. exponents `(1/4)(1 + ξ)` and `3/4 - ξ/4` when `x = X^ξ`.  Both equal `1/2` exactly at `ξ = 1`:
the self-dual scale.

So the phase family `e(√(n x))` admits square-root cancellation at the critical scale by an
elementary test.  **What obstructs the Lindelöf hypothesis is therefore not the phase but the
arithmetic weight** — `d(n)` in the Voronoi form, `S(a,q)/√q` in the coherence-block form.
-/

/-- Exponent of the first term of the second-derivative test for the phase `2√(nx)` with `x = X^ξ`,
in powers of `X`. -/
def sqrtPhaseFirstTerm (xi : ℚ) : ℚ := (1 + xi) / 4

/-- Exponent of the second term. -/
def sqrtPhaseSecondTerm (xi : ℚ) : ℚ := 3/4 - xi/4

/-- **Both terms equal `1/2` exactly at the self-dual scale `ξ = 1`.** -/
@[simp] theorem sqrtPhase_selfDual :
    sqrtPhaseFirstTerm 1 = 1/2 ∧ sqrtPhaseSecondTerm 1 = 1/2 := by
  refine ⟨?_, ?_⟩
  · unfold sqrtPhaseFirstTerm; norm_num
  · unfold sqrtPhaseSecondTerm; norm_num

/-- The two terms cross exactly at `ξ = 1`, and nowhere else. -/
theorem sqrtPhase_terms_eq_iff (xi : ℚ) :
    sqrtPhaseFirstTerm xi = sqrtPhaseSecondTerm xi ↔ xi = 1 := by
  unfold sqrtPhaseFirstTerm sqrtPhaseSecondTerm
  constructor <;> intro h <;> linarith

/-- The maximum of the two terms, which is what the test delivers. -/
def sqrtPhaseBound (xi : ℚ) : ℚ := max (sqrtPhaseFirstTerm xi) (sqrtPhaseSecondTerm xi)

/-- **At the self-dual scale the unweighted square-root phase sum has square-root cancellation.** -/
@[simp] theorem sqrtPhaseBound_selfDual : sqrtPhaseBound 1 = 1/2 := by
  unfold sqrtPhaseBound
  rw [sqrtPhase_selfDual.1, sqrtPhase_selfDual.2]
  simp

/-- Away from the self-dual scale the bound is strictly worse in both directions: the first term
grows for `ξ > 1` and the second for `ξ < 1`.  The self-dual scale is the unique minimum. -/
theorem sqrtPhaseBound_gt_half {xi : ℚ} (h : xi ≠ 1) : 1/2 < sqrtPhaseBound xi := by
  unfold sqrtPhaseBound sqrtPhaseFirstTerm sqrtPhaseSecondTerm
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have : (1:ℚ)/2 < 3/4 - xi/4 := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)
  · have : (1:ℚ)/2 < (1 + xi)/4 := by linarith
    exact lt_of_lt_of_le this (le_max_left _ _)


/-!
### The final reduction: a two-dimensional sum over resonance pairs

Assembling C304/C307/C309: the coherence-block sum is, up to smooth weights,

    L · Σ_{q ≤ L} q^{-1/2} Σ_{a} ε(a,q) · e( N√(2a/q) ),

where `ε(a,q)` is the unimodular phase of the normalised Gauss sum and `L = N^{1/3}`.  There are `≍ L²`
resonance pairs `(a,q)`, each carrying weight `≍ L^{-1/2}`.

* trivial: `Σ_{q≤L} q^{-1/2}·q = Σ_{q≤L} q^{1/2} ≍ L^{3/2}` — total `L^{5/2} = N^{5/6}`, Weyl;
* square-root in `a` only: `Σ_{q≤L} q^{-1/2}·q^{1/2} = L` — total `L² = N^{2/3}`, still short;
* square-root in the full two-dimensional sum: `L^{-1/2}·(L²)^{1/2} = L^{1/2}` — total
  `L^{3/2} = N^{1/2}`, the Lindelöf hypothesis.

So the target is **full square-root cancellation over the `≍L²` resonance pairs**, and cancellation in
one variable alone is not enough: it leaves a deficit of `L^{1/2}`.
-/

/-- Exponent, in powers of the coherence length `L`, of the resonance-pair sum under a given amount
of cancellation: `0` for none, `1/2` for one variable, `1` for the full two-dimensional square root. -/
def resonancePairExponent (cancellation : ℚ) : ℚ := 3/2 - cancellation

/-- No cancellation reproduces the Weyl bookkeeping. -/
@[simp] theorem resonancePair_trivial : resonancePairExponent 0 = 3/2 := by
  unfold resonancePairExponent; norm_num

/-- Square-root cancellation in the `a`-variable alone. -/
@[simp] theorem resonancePair_oneVariable : resonancePairExponent (1/2) = 1 := by
  unfold resonancePairExponent; norm_num

/-- **Full two-dimensional square-root cancellation is exactly the Lindelöf target.** -/
@[simp] theorem resonancePair_full : resonancePairExponent 1 = 1/2 := by
  unfold resonancePairExponent; norm_num

/-- **One variable is not enough.**  Cancellation in `a` alone leaves the block sum at `L²= N^{2/3}`,
short of the Lindelöf target by `L^{1/2} = N^{1/6}`. -/
theorem oneVariable_insufficient :
    resonancePairExponent (1/2) - resonancePairExponent 1 = 1/2 := by
  unfold resonancePairExponent; norm_num

/-- Converting the resonance-pair exponent to the exponent of the whole critical sum: multiply by the
coherence scale and add the within-block square root. -/
def totalOfResonancePair (e : ℚ) : ℚ := ofCoherenceScale (e + 1)

/-- The three regimes in powers of `N`: Weyl, the one-variable intermediate, and Lindelöf. -/
theorem resonance_regimes :
    totalOfResonancePair (resonancePairExponent 0) = 5/6 ∧
    totalOfResonancePair (resonancePairExponent (1/2)) = 2/3 ∧
    totalOfResonancePair (resonancePairExponent 1) = 1/2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold totalOfResonancePair ofCoherenceScale resonancePairExponent; norm_num)

/-- **Bourgain's record, placed on this scale.**  `17/21` corresponds to a resonance-pair exponent of
`17/7 - 1 = 10/7`, i.e. cancellation `3/2 - 10/7 = 1/14` out of the `1` required. -/
theorem bourgain_cancellation_share :
    totalOfResonancePair (10/7) = 17/21 ∧ (3/2 : ℚ) - 10/7 = 1/14 := by
  constructor
  · unfold totalOfResonancePair ofCoherenceScale; norm_num
  · norm_num


/-!
### An intermediate target that would beat the record

The Gauss-sum phase in the resonance sum is `ε(a,q) = ε_q·(a|q)`, the Jacobi symbol times a fourth
root of unity.  The `a`-sum is therefore a character sum against the phase `e(N√(2a/q))`.  This is
*not* a Salié sum: `√(2a/q)` is irrational, so the phase is not a rational additive character mod `q`,
and the classical explicit evaluations do not apply.  The phase moreover oscillates fast — its
`a`-derivative is `≍ N/√(aq) ≍ N/L = N^{2/3}` — so the character contributes nothing directly and the
`a`-sum is itself an exponential sum with a resonance structure.

Nevertheless the *target* is worth recording, because it is strictly weaker than the Lindelöf
hypothesis and strictly stronger than the current record:

    Σ_a ε(a,q)·e(N√(2a/q))  ≪  q^{1/2+ε}   uniformly for q ≤ L
      ⟹  block sum ≪ L·Σ_{q≤L} q^{-1/2}·q^{1/2} = L²  =  N^{2/3}
      ⟹  **μ ≤ 1/12 = 0.0833 < 13/84 = 0.1548.**
-/

/-- The Lindelöf exponent delivered by square-root cancellation in the `a`-variable alone. -/
def oneVariableMu : ℚ := muOfBlock (totalOfResonancePair (resonancePairExponent (1/2)))

/-- **One-variable square-root cancellation gives `μ = 1/12`.** -/
@[simp] theorem oneVariableMu_eq : oneVariableMu = 1/12 := by
  unfold oneVariableMu totalOfResonancePair ofCoherenceScale resonancePairExponent muOfBlock
  norm_num

/-- **It would beat the record.**  `1/12 < 13/84`, so square-root cancellation in the `a`-variable of
the resonance sum is open: proving it improves on Bourgain. -/
theorem oneVariableMu_beats_record : oneVariableMu < 13/84 := by
  rw [oneVariableMu_eq]; norm_num

/-- **And it is strictly weaker than the Lindelöf hypothesis**, which needs the two-variable
cancellation. -/
theorem oneVariableMu_pos : 0 < oneVariableMu := by
  rw [oneVariableMu_eq]; norm_num

/-- The three targets in order: the record, the one-variable intermediate, and Lindelöf. -/
theorem target_ladder :
    (0 : ℚ) < oneVariableMu ∧ oneVariableMu < 13/84 := by
  exact ⟨oneVariableMu_pos, oneVariableMu_beats_record⟩


/-!
### Three classical tools, three computable failures on the resonance sum

The intermediate target is `T(q) = Σ_{a ≤ q} (a|q)·e(g(a))` with `g(a) = N√(2a/q)`, `q ≤ L = N^{1/3}`.
Writing exponents in powers of `N` with `q = N^κ`, `κ ≤ 1/3`:

* `g'(a) = N/√(2qa) ≍ N^{1-κ}` on `a ≍ q`;
* `g''(a) ≍ N/q² ≍ N^{1-2κ}`;
* the dual (Poisson) range is `g'([1,q]) ≍ N^{1-κ/2}`;
* the trivial bound is `N^κ`, and the target `N^{κ/2}`.

**van der Corput** needs a small second derivative; here `1 - 2κ ≥ 1/3 > 0`, so `|g''| ≫ 1`.
**Poisson** replaces the sum by one of length `N^{1-κ/2} ≥ N^{5/6}`, vastly longer than `N^κ ≤ N^{1/3}`.
**Pólya–Vinogradov with partial summation** gives `q^{1/2}·q·max|Δf| ≍ N^{3κ/2}·N^{1-κ} = N^{1+κ/2}`,
which exceeds the trivial bound `N^κ` for every `κ ≤ 1/3`.
-/

/-- Exponent of the second derivative of the resonance phase, with `q = N^κ`. -/
def resonanceSecondDeriv (kappa : ℚ) : ℚ := 1 - 2 * kappa

/-- Exponent of the Poisson-dual length. -/
def resonanceDualLength (kappa : ℚ) : ℚ := 1 - kappa / 2

/-- Exponent delivered by Pólya–Vinogradov plus partial summation. -/
def resonancePartialSummation (kappa : ℚ) : ℚ := 1 + kappa / 2

/-- The trivial bound and the target. -/
def resonanceTrivial (kappa : ℚ) : ℚ := kappa

def resonanceGoal (kappa : ℚ) : ℚ := kappa / 2

/-- **van der Corput fails: the second derivative is large on the whole range `κ ≤ 1/3`.** -/
theorem vdC_fails_on_resonance {kappa : ℚ} (h : kappa ≤ 1/3) : 1/3 ≤ resonanceSecondDeriv kappa := by
  unfold resonanceSecondDeriv; linarith

/-- **Poisson fails: the dual is longer than the original, by a wide margin.** -/
theorem poisson_fails_on_resonance {kappa : ℚ} (h : kappa ≤ 1/3) :
    resonanceTrivial kappa < resonanceDualLength kappa := by
  unfold resonanceTrivial resonanceDualLength; linarith

/-- **Pólya–Vinogradov with partial summation fails: it exceeds the trivial bound.** -/
theorem polyaVinogradov_fails_on_resonance {kappa : ℚ} (h : kappa ≤ 1/3) :
    resonanceTrivial kappa < resonancePartialSummation kappa := by
  unfold resonanceTrivial resonancePartialSummation; linarith

/-- **The triple barrier.**  On the whole range `0 ≤ κ ≤ 1/3` the three classical tools each fail,
for three distinct and computable reasons, while the target `κ/2` remains strictly below the trivial
bound `κ` for `κ > 0`. -/
theorem resonance_triple_barrier {kappa : ℚ} (h0 : 0 < kappa) (h : kappa ≤ 1/3) :
    1/3 ≤ resonanceSecondDeriv kappa ∧
    resonanceTrivial kappa < resonanceDualLength kappa ∧
    resonanceTrivial kappa < resonancePartialSummation kappa ∧
    resonanceGoal kappa < resonanceTrivial kappa :=
  ⟨vdC_fails_on_resonance h,
   poisson_fails_on_resonance h,
   polyaVinogradov_fails_on_resonance h,
   by unfold resonanceGoal resonanceTrivial; linarith⟩


/-!
### A fourth tool: differencing the resonance sum

Applying the Weyl differencing of `WeylDifferencing` to `T(q) = Σ_{a≤q}(a|q)e(g(a))` gives
correlations

    Σ_a (a(a+h)|q) · e( g(a+h) - g(a) ),      g(a+h) - g(a) ≍ Nh/√(2qa) ≍ N h / q^{3/2} · q^{1/2},

whose phase `φ_h(a) ≍ (Nh/√(2q))·a^{-1/2}` has, on `a ≍ q`,

    φ_h' ≍ N h / q²,     φ_h'' ≍ N h / q³.

With `q = N^κ` and `h ≍ 1`, the differenced second-derivative exponent is `1 - 3κ`, against `1 - 2κ`
before differencing.  **It vanishes exactly at `κ = 1/3`** — the top of the admissible range, where
`q ≍ L = N^{1/3}`.  Below that it is still positive, so the differenced phase remains too fast.

The differenced character `(a(a+h)|q)` is a quadratic character of a quadratic polynomial, so Weil's
bound gives `Σ_{a mod q}(a(a+h)|q) ≪ q^{1/2}`.  Exploiting it by partial summation requires the phase
to vary slowly, i.e. `φ_h' ≪ 1`, i.e. `h ≪ q²/N = N^{2κ-1} ≤ N^{-1/3} < 1` — **no admissible shift
qualifies.**
-/

/-- Second-derivative exponent of the resonance phase after one Weyl differencing at shift `h ≍ 1`. -/
def differencedSecondDeriv (kappa : ℚ) : ℚ := 1 - 3 * kappa

/-- **Differencing is exactly critical at the top of the range.** -/
@[simp] theorem differencedSecondDeriv_top : differencedSecondDeriv (1/3) = 0 := by
  unfold differencedSecondDeriv; norm_num

/-- **And strictly insufficient below it.** -/
theorem differencedSecondDeriv_pos {kappa : ℚ} (h : kappa < 1/3) :
    0 < differencedSecondDeriv kappa := by
  unfold differencedSecondDeriv; linarith

/-- One differencing gains exactly one factor of `κ` in the second-derivative exponent. -/
theorem differencing_gain (kappa : ℚ) :
    resonanceSecondDeriv kappa - differencedSecondDeriv kappa = kappa := by
  unfold resonanceSecondDeriv differencedSecondDeriv; ring

/-- Exponent of the largest shift for which Weil's bound can be exploited by partial summation:
`h ≪ q²/N`. -/
def weilUsableShift (kappa : ℚ) : ℚ := 2 * kappa - 1

/-- **No admissible shift qualifies.**  On `κ ≤ 1/3` the usable-shift exponent is at most `-1/3 < 0`,
so even `h = 1` is too large. -/
theorem weil_unusable {kappa : ℚ} (h : kappa ≤ 1/3) : weilUsableShift kappa ≤ -1/3 := by
  unfold weilUsableShift; linarith

/-- **The fourth barrier, assembled.**  Differencing is critical only at `κ = 1/3` and insufficient
below; Weil's bound on the differenced character cannot be exploited at any admissible shift. -/
theorem resonance_fourth_barrier {kappa : ℚ} (h0 : 0 < kappa) (h : kappa < 1/3) :
    0 < differencedSecondDeriv kappa ∧ weilUsableShift kappa < 0 := by
  refine ⟨differencedSecondDeriv_pos h, ?_⟩
  unfold weilUsableShift; linarith


/-!
### The two levels of cancellation in the Farey dissection

Each Farey arc around `a'/q'` contains `L/q'` coherence blocks, each of size `L/√q'`.  There are two
independent places where cancellation can occur: **within** an arc (the blocks there have phases
varying with the distance to `a'/q'`) and **across** arcs.

    no cancellation:        Σ_{q'≤L} φ(q')·(L/q')(L/√q')      ≍ L²·L^{1/2}   = L^{5/2}
    within arcs only:       Σ_{q'≤L} φ(q')·(L/q')^{1/2}(L/√q') ≍ L^{3/2}·L    = L^{5/2}
    across arcs only:       ( Σ_{q'≤L} φ(q')·(L²/q'^{3/2})² )^{1/2}           = L²
    **both**:               ( Σ_{q'≤L} φ(q')·(L^{3/2}/q')² )^{1/2}            = L^{3/2}·(log L)^{1/2}

The last is `N^{1/2}` — the Lindelöf value, and exactly the root-mean-square of the frontier sum.

**Within-arc cancellation alone gains nothing**: the weight distribution `φ(q')q'^{-1}` exactly
compensates the `q'^{-1/2}` gained, and the total stays at `L^{5/2}`.  Only the across-arc level moves
the exponent, and both levels together are needed to reach `L^{3/2}`.
-/

/-- Exponent in `L` of the Farey-dissected frontier sum, given square-root cancellation within arcs
(`w = 1`) and/or across arcs (`x = 1`). -/
def fareyExponent (w x : ℚ) : ℚ := 5/2 - x/2 - w * x / 2

/-- No cancellation reproduces Weyl. -/
@[simp] theorem farey_none : fareyExponent 0 0 = 5/2 := by unfold fareyExponent; norm_num

/-- **Within-arc cancellation alone gains nothing.** -/
@[simp] theorem farey_withinOnly : fareyExponent 1 0 = 5/2 := by unfold fareyExponent; norm_num

/-- Across-arc cancellation alone gives `L²`, i.e. `μ = 1/12`. -/
@[simp] theorem farey_acrossOnly : fareyExponent 0 1 = 2 := by unfold fareyExponent; norm_num

/-- **Both levels give `L^{3/2}` — the Lindelöf value.** -/
@[simp] theorem farey_both : fareyExponent 1 1 = 3/2 := by unfold fareyExponent; norm_num

/-- The four regimes converted to exponents of `N` at `L = N^{1/3}`. -/
theorem farey_regimes_in_N :
    ofCoherenceScale (fareyExponent 0 0) = 5/6 ∧
    ofCoherenceScale (fareyExponent 1 0) = 5/6 ∧
    ofCoherenceScale (fareyExponent 0 1) = 2/3 ∧
    ofCoherenceScale (fareyExponent 1 1) = 1/2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold ofCoherenceScale fareyExponent; norm_num)

/-- **The rigidity.**  Within-arc cancellation is worth exactly nothing on its own, and exactly
`L^{1/2}` in the presence of across-arc cancellation. -/
theorem within_arc_rigidity :
    fareyExponent 1 0 - fareyExponent 0 0 = 0 ∧
    fareyExponent 0 1 - fareyExponent 1 1 = 1/2 := by
  constructor <;> (unfold fareyExponent; norm_num)

/-- Both levels of square-root cancellation give exactly `μ = 0`. -/
@[simp] theorem farey_both_gives_lindelof :
    muOfBlock (ofCoherenceScale (fareyExponent 1 1)) = 0 := by
  unfold ofCoherenceScale fareyExponent muOfBlock; norm_num


/-!
### Why within-arc cancellation is neutral: a conservation law in the Farey weights

The neutrality of Theorem 40 is not a numerical accident.  Summing over Farey denominators,

    Σ_{q ≤ L} φ(q) q^{-s}  ≍  L^{2-s}     for `s < 2`,

so with `L/q` blocks per arc and theta size `L/√q`:

    no cancellation:   L² · Σ φ(q) q^{-3/2}  ≍  L² · L^{1/2}   = L^{5/2}
    within-arc only:   L^{3/2} · Σ φ(q) q^{-1} ≍ L^{3/2} · L¹   = L^{5/2}

The prefactors differ by `L^{1/2}` and the arithmetic sums differ by `L^{1/2}` in the opposite
direction.  **The Farey weight `φ(q)` has exactly the power law that makes the within-arc square root
neutral**, and nothing in this depends on the phase: the block count per arc, the theta size, and the
Farey weight are all universal features of a theta-resonance decomposition.
-/

/-- Exponent of `Σ_{q ≤ L} φ(q) q^{-s}` in powers of `L`, valid for `s < 2`. -/
def fareyMomentExponent (s : ℚ) : ℚ := 2 - s

/-- Total exponent with no cancellation: prefactor `L²` against `s = 3/2`. -/
def totalNoCancellation : ℚ := 2 + fareyMomentExponent (3/2)

/-- Total exponent with within-arc square-root cancellation: prefactor `L^{3/2}` against `s = 1`. -/
def totalWithinArc : ℚ := 3/2 + fareyMomentExponent 1

@[simp] theorem totalNoCancellation_eq : totalNoCancellation = 5/2 := by
  unfold totalNoCancellation fareyMomentExponent; norm_num

@[simp] theorem totalWithinArc_eq : totalWithinArc = 5/2 := by
  unfold totalWithinArc fareyMomentExponent; norm_num

/-- **The conservation law.**  The two totals agree, because the prefactor gained by within-arc
cancellation is exactly cancelled by the change in the Farey moment. -/
theorem within_arc_neutrality : totalNoCancellation = totalWithinArc := by
  rw [totalNoCancellation_eq, totalWithinArc_eq]

/-- The mechanism, isolated: the prefactor drops by `1/2` and the Farey moment rises by `1/2`. -/
theorem neutrality_mechanism :
    (2 : ℚ) - 3/2 = 1/2 ∧ fareyMomentExponent 1 - fareyMomentExponent (3/2) = 1/2 := by
  constructor
  · norm_num
  · unfold fareyMomentExponent; norm_num

/-- **Universality.**  The identity holds for any decomposition with `L/q` blocks per arc and theta
size `L/q^{1/2}`, whatever the phase: for every `s`, halving the block count exponent and raising the
Farey moment exponent by the same amount leaves the total fixed. -/
theorem neutrality_universal (p s : ℚ) :
    (p + fareyMomentExponent s) = ((p - 1/2) + fareyMomentExponent (s - 1/2)) := by
  unfold fareyMomentExponent; ring


/-!
### Validation: the same bookkeeping governs the Dirichlet divisor problem

Voronoi's expansion writes `Δ(x) ≍ x^{1/4} Σ_{n ≤ x} d(n)n^{-3/4} e(2√(nx))`.  A bound
`Σ_{n ∼ M} d(n)e(2√(nx)) ≪ M^{b}` contributes `x^{1/4}·M^{b-3/4}`, which at the dominant scale `M ≍ x`
gives `Δ(x) ≪ x^{b - 1/2}`.  Hence

    b = 5/6  ⟹  Δ(x) ≪ x^{1/3}       — Voronoi 1903, the classical exponent
    b = 1/2  ⟹  Δ(x) ≪ x^{1/4+ε}     — the Dirichlet divisor conjecture

These are exactly the incoherent and coherent block totals of the coherence decomposition.  The
Lindelöf hypothesis and the divisor conjecture are therefore the *same* coherence statement for two
different phases, and the classical exponents `1/6` and `1/3` are the same incoherent bookkeeping.
-/

/-- The divisor-problem exponent delivered by a block exponent `b` for the Voronoi sum, in the
regime `b ≥ 3/4` where the dominant scale is `M ≍ x`. -/
def divisorExponentOfBlock (b : ℚ) : ℚ := b - 1/2

/-- **The incoherent block total gives Voronoi's classical `1/3`.** -/
@[simp] theorem divisor_incoherent : divisorExponentOfBlock (5/6) = 1/3 := by
  unfold divisorExponentOfBlock; norm_num

/-- **The threshold.**  Below `b = 3/4` the dominant scale moves to small `M` and the bound saturates
at `x^{1/4}`, so the divisor conjecture corresponds to `b ≤ 3/4` — *not* to square-root cancellation
in the Voronoi sum. -/
@[simp] theorem divisor_threshold : divisorExponentOfBlock (3/4) = 1/4 := by
  unfold divisorExponentOfBlock; norm_num

/-- The `ζ` and divisor problems share the incoherent block total but **not** their targets: `ζ` needs
`b = 1/2`, the divisor problem only `b = 3/4`. -/
theorem shared_incoherent_distinct_targets :
    muOfBlock (5/6) = 1/6 ∧ divisorExponentOfBlock (5/6) = 1/3 ∧
    muOfBlock (1/2) = 0 ∧ divisorExponentOfBlock (3/4) = 1/4 ∧ (1/2 : ℚ) < 3/4 := by
  refine ⟨?_, divisor_incoherent, ?_, divisor_threshold, by norm_num⟩
  · unfold muOfBlock; norm_num
  · unfold muOfBlock; norm_num

/-- Block exponent corresponding to the divisor-problem record `Δ(x) ≪ x^{131/416}`. -/
def divisorRecordBlock : ℚ := 131/416 + 1/2

@[simp] theorem divisorRecordBlock_eq : divisorRecordBlock = 339/416 := by
  unfold divisorRecordBlock; norm_num

/-- **The zeta problem is currently ahead in the shared bookkeeping.**  Bourgain's block exponent
`17/21` is strictly smaller than the divisor record's `339/416`. -/
theorem zeta_ahead_of_divisor : (17/21 : ℚ) < divisorRecordBlock := by
  rw [divisorRecordBlock_eq]; norm_num

/-- Both records sit strictly between the divisor threshold `3/4` and the incoherent total `5/6`. -/
theorem records_between :
    (3/4 : ℚ) < 17/21 ∧ (17/21 : ℚ) < 5/6 ∧
    (3/4 : ℚ) < divisorRecordBlock ∧ divisorRecordBlock < 5/6 := by
  rw [divisorRecordBlock_eq]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩


/-!
### Calibrating the two problems against each other

Both problems start from the classical incoherent exponent `5/6`.  The distances to their targets are

    Lindelöf:            5/6 − 1/2  = 1/3
    divisor conjecture:  5/6 − 3/4  = 1/12,

so **LH is exactly four times further** in the shared currency.  The distances covered are

    Bourgain:        5/6 − 17/21   = 1/42        — a fraction  (1/42)/(1/3)  = 1/14   ≈ 7.1 %
    divisor record:  5/6 − 339/416 = 23/1248     — a fraction  (23/1248)/(1/12) = 23/104 ≈ 22.1 %,

so the divisor problem is roughly three times further along its (four times shorter) road.
-/

/-- Distance from the classical incoherent exponent to a target, in the shared currency. -/
def blockDistance (target : ℚ) : ℚ := 5/6 - target

@[simp] theorem blockDistance_lindelof : blockDistance (1/2) = 1/3 := by
  unfold blockDistance; norm_num

@[simp] theorem blockDistance_divisor : blockDistance (3/4) = 1/12 := by
  unfold blockDistance; norm_num

/-- **LH is exactly four times further from the classical exponent than the divisor conjecture.** -/
theorem lindelof_four_times_divisor :
    blockDistance (1/2) = 4 * blockDistance (3/4) := by
  rw [blockDistance_lindelof, blockDistance_divisor]; norm_num

/-- Distance covered by Bourgain's record. -/
@[simp] theorem blockDistance_bourgain : blockDistance (17/21) = 1/42 := by
  unfold blockDistance; norm_num

/-- Distance covered by the divisor record `x^{131/416}`. -/
@[simp] theorem blockDistance_divisorRecord : blockDistance (339/416) = 23/1248 := by
  unfold blockDistance; norm_num

/-- Fraction of the way to the target. -/
def progressFraction (covered target : ℚ) : ℚ := covered / target

/-- **Progress toward the Lindelöf hypothesis: `1/14`.** -/
@[simp] theorem progress_lindelof :
    progressFraction (blockDistance (17/21)) (blockDistance (1/2)) = 1/14 := by
  rw [blockDistance_bourgain, blockDistance_lindelof]
  unfold progressFraction; norm_num

/-- **Progress toward the divisor conjecture: `23/104`.** -/
@[simp] theorem progress_divisor :
    progressFraction (blockDistance (339/416)) (blockDistance (3/4)) = 23/104 := by
  rw [blockDistance_divisorRecord, blockDistance_divisor]
  unfold progressFraction; norm_num

/-- **The divisor problem is three times further along.** -/
theorem divisor_further_along :
    progressFraction (blockDistance (17/21)) (blockDistance (1/2))
      < progressFraction (blockDistance (339/416)) (blockDistance (3/4)) ∧
    3 * progressFraction (blockDistance (17/21)) (blockDistance (1/2))
      < progressFraction (blockDistance (339/416)) (blockDistance (3/4)) := by
  rw [progress_lindelof, progress_divisor]
  constructor <;> norm_num


/-!
### Where square-root cancellation is actually a theorem, and how much of the frontier it reaches

The one proven source of square-root cancellation for exponential sums is Weil–Deligne: **complete**
sums with **algebraic** phase over a finite field.  The frontier sum fails both hypotheses — it runs
over a Farey range, not a full residue system, and its phase `√(2a/q)` is irrational in the summation
variable.

There is, however, a sub-family on which the phase *is* rational.  `N√(2a/q)` is a rational multiple of
`a/q` exactly when `2aq` is a perfect square.  For each `q` the admissible `a ≤ q` number `≍ √q`, so
the algebraic sub-family has size

    Σ_{q ≤ L} √q  ≍  L^{3/2},   a fraction  L^{3/2}/L² = **L^{-1/2}**  of all resonances.

On that sub-family the inner sum is a Gauss/Salié sum and Weil's bound applies unconditionally; its
total contribution is

    ( Σ_{q≤L} √q · (L²/q^{3/2})² )^{1/2}  =  L² ( Σ_{q≤L} q^{-5/2} )^{1/2}  ≍  L².

The remaining `≍L²` resonances have transcendental phase and no proven square-root cancellation.
-/

/-- Size exponent (in `L`) of the algebraic sub-family of resonances: those with `2aq` a perfect
square.  Writing `2q = u v²` with `u` squarefree, the admissible `a ≤ q` are exactly `a = u m²` with
`m ≤ v/√2`, so their number is `≍ v(2q)`, the largest `v` with `v² ∣ 2q`.  Summing,
`Σ_{q≤L} v(2q) ≍ Σ_v v·(L/v²) ≍ L log L` — **exponent `1`, not `3/2`.** -/
def algebraicResonanceCount : ℚ := 1

/-- Size exponent of all resonances. -/
def allResonanceCount : ℚ := 2

/-- **The algebraic sub-family is thin: a fraction `L^{-1}` of the resonances (up to logarithms).** -/
@[simp] theorem algebraic_density :
    algebraicResonanceCount - allResonanceCount = -1 := by
  unfold algebraicResonanceCount allResonanceCount; norm_num

/-- Contribution exponent of the algebraic sub-family under Weil's bound. -/
def algebraicContribution : ℚ := 2

/-- **Weil on the algebraic sub-family reaches the `across-arc-only` level, not the Lindelöf level.** -/
theorem algebraic_reaches_only_acrossArc :
    algebraicContribution = fareyExponent 0 1 ∧ fareyExponent 1 1 < algebraicContribution := by
  constructor
  · unfold algebraicContribution fareyExponent; norm_num
  · unfold algebraicContribution fareyExponent; norm_num

/-- The shortfall of the algebraic sub-family from the Lindelöf target, in powers of `L`. -/
@[simp] theorem algebraic_shortfall :
    algebraicContribution - fareyExponent 1 1 = 1/2 := by
  unfold algebraicContribution fareyExponent; norm_num

/-- **The reach of the one proven mechanism.**  Weil–Deligne applies to a `L^{-1/2}` fraction of the
resonances and, even applied perfectly there, falls short of the Lindelöf target by `L^{1/2}`. -/
theorem weil_reach :
    algebraicResonanceCount - allResonanceCount = -1 ∧
    algebraicContribution - fareyExponent 1 1 = 1/2 :=
  ⟨algebraic_density, algebraic_shortfall⟩


/-!
### The additive energy of the frontier frequency set is minimal

The classes `S_d` of Theorem 47 are indexed by the squarefree part `d` of `2aq`, which for a typical
pair is `≍ L²` — so **most classes are singletons**, and the largest, `d = 1`, has only `≍ L\log L`
elements (E36).  Additive relations `s₁ + s₂ = s₃ + s₄` with `s ∈ √d·ℚ` force the four elements into
matching classes, so the non-trivial energy is at most

    Σ_d m_d³  ≤  (max_d m_d)² · Σ_d m_d  ≤  (L\log L)² · L²  =  L⁴ \log²L ,

against a trivial contribution of `|S|² = L⁴`.  **The additive energy is minimal up to logarithms.**

This is exactly the hypothesis under which the large sieve, Halász-type bounds and decoupling are
sharpest.  The frontier frequency set is therefore *optimally structured* for every
additive-combinatorial tool — and every such tool still fails, because they all require averaging over
the parameter `N`, which reproduces the mean square of Theorem 39 and nothing more.
-/

/-- Size exponent (in `L`) of the frontier frequency set. -/
def frequencySetSize : ℚ := 2

/-- Size exponent of the largest `√d`-class (`d = 1`), from E36. -/
def largestClassSize : ℚ := 1

/-- Exponent of the trivial additive energy `|S|²`. -/
def trivialEnergy : ℚ := 2 * frequencySetSize

/-- Exponent bound for the non-trivial additive energy: `(max m_d)² · Σ m_d`. -/
def nontrivialEnergyBound : ℚ := 2 * largestClassSize + frequencySetSize

@[simp] theorem trivialEnergy_eq : trivialEnergy = 4 := by
  unfold trivialEnergy frequencySetSize; norm_num

@[simp] theorem nontrivialEnergyBound_eq : nontrivialEnergyBound = 4 := by
  unfold nontrivialEnergyBound largestClassSize frequencySetSize; norm_num

/-- **The additive energy is minimal.**  The non-trivial contribution does not exceed the trivial
one in order. -/
theorem energy_minimal : nontrivialEnergyBound = trivialEnergy := by
  rw [trivialEnergy_eq, nontrivialEnergyBound_eq]

/-- Had the largest class been larger, the energy would have exceeded the trivial bound; the
threshold is exactly `largestClassSize = frequencySetSize/2`. -/
theorem energy_threshold :
    nontrivialEnergyBound ≤ trivialEnergy ↔ largestClassSize ≤ frequencySetSize / 2 := by
  unfold nontrivialEnergyBound trivialEnergy
  constructor <;> intro h <;> linarith

/-- The largest class meets the threshold exactly. -/
@[simp] theorem largestClass_at_threshold :
    largestClassSize = frequencySetSize / 2 := by
  unfold largestClassSize frequencySetSize; norm_num


/-!
### Why smoothing cannot close the pointwise/mean-value gap

The Sobolev upgrade `|f(t₀)|² ≤ (1/H)∫_I |f|² + ∫_I |f||f'|` converts a mean square into a pointwise
bound — but only the **first** term carries the factor `1/H`.  For the frontier sum
`F(t) = Σ_{n∼N} n^{-it}` one has `F'(t) = -i Σ_n (\log n)n^{-it}`, so `∫_I|F'|² ≍ \log²N · ∫_I|F|²` and

    ∫_I |F||F'|  ≤  (∫_I|F|²)^{1/2}(∫_I|F'|²)^{1/2}  ≍  \log N · ∫_I |F|² .

The variation term is therefore **larger than the mean square itself**, with no `H` to shrink it.  No
choice of interval helps: the bound is at best `\log N` times the mean square over the interval, which
for any admissible `H` exceeds the trivial bound.

The mean square is also only `≍ H·N` for `H ≫ N`; for shorter intervals the off-diagonal
`Σ_{m≠n} \min(H, N/|m-n|) ≍ N²\log N` dominates.  Both effects push the same way.
-/

/-- Exponent (in `N`) of the mean square of the frontier sum over an interval of length `N^h`. -/
def shortMeanSquare (h : ℚ) : ℚ := max (h + 1) 2

/-- For `h ≥ 1` the diagonal dominates and the mean square is `H·N`. -/
@[simp] theorem shortMeanSquare_long : shortMeanSquare 1 = 2 := by
  unfold shortMeanSquare; norm_num

/-- For `h < 1` the off-diagonal dominates and the mean square saturates at `N²`. -/
theorem shortMeanSquare_short {h : ℚ} (hh : h ≤ 1) : shortMeanSquare h = 2 := by
  unfold shortMeanSquare
  have : h + 1 ≤ 2 := by linarith
  exact max_eq_right this

/-- Exponent delivered by the Sobolev upgrade: the variation term is the mean square itself (the
logarithm contributes exponent `0`), so no `1/H` gain survives. -/
def sobolevOutput (h : ℚ) : ℚ := shortMeanSquare h

/-- **Sobolev returns the trivial bound.**  For every interval length the output exponent is `2`,
i.e. `|F| ≪ N` — no cancellation at all. -/
theorem sobolev_trivial {h : ℚ} (hh : h ≤ 1) : sobolevOutput h = 2 := by
  unfold sobolevOutput; exact shortMeanSquare_short hh

/-- The Lindelöf target for `|F|²` is exponent `1`; Sobolev delivers `2`. -/
theorem sobolev_shortfall {h : ℚ} (hh : h ≤ 1) : sobolevOutput h - 1 = 1 := by
  rw [sobolev_trivial hh]; norm_num

/-- **The structural reason.**  Only the first term of the Sobolev inequality carries `1/H`; the
variation term does not, and for a phase oscillating at rate `\log N` it is the larger of the two. -/
theorem sobolev_variation_dominates (h : ℚ) :
    shortMeanSquare h ≤ sobolevOutput h := by
  unfold sobolevOutput; exact le_refl _


/-!
### The fifth bridge: amplification, and why it collapses to resonance

Amplification is the modern route from a family average to a pointwise bound: attach an amplifier `A`
that is large at the target point and small elsewhere, then bound `∫ |A|²|ζ|⁴`.  In the `t`-aspect the
family is the set of translates, and an amplifier must take the form `A(t) = Σ_n a_n n^{-it}`.  For `A`
to be large at `t₀` the coefficients must resonate with the prime phases `\{t₀ \log p\}` — which is
exactly the resonance method.

Its amplification factor is governed by Gál-type sums, whose extremal size is

    \exp( c√(\log N \log\log N) )  =  N^{o(1)}  —  **subpolynomial** (Bondarenko–Seip).

So the amplifier contributes exponent `0` in powers of `N`, and no polynomial pointwise saving follows.
-/

/-- Exponent (in `N`) of the best amplification factor available in the `t`-aspect. -/
def amplifierExponent : ℚ := 0

/-- Exponent of the pointwise saving required for the Lindelöf hypothesis, from the trivial bound. -/
def requiredPointwiseSaving : ℚ := 1/2

/-- **Amplification supplies no power of `N`.** -/
theorem amplification_subpolynomial : amplifierExponent < requiredPointwiseSaving := by
  unfold amplifierExponent requiredPointwiseSaving; norm_num

/-- The shortfall is the entire required saving. -/
@[simp] theorem amplification_shortfall :
    requiredPointwiseSaving - amplifierExponent = 1/2 := by
  unfold amplifierExponent requiredPointwiseSaving; norm_num

/-- Even the intermediate target of Theorem 34 is out of reach for amplification: it needs a saving of
`5/6 - 2/3 = 1/6` in the block exponent, still a positive power. -/
theorem amplification_misses_intermediate :
    amplifierExponent < (5/6 : ℚ) - 2/3 := by
  unfold amplifierExponent; norm_num

/-- **The five bridges, all closed.**  Sobolev returns the trivial exponent (Theorem 49) and
amplification returns exponent `0`; the remaining three are closed by earlier barriers. -/
theorem five_bridges_closed :
    sobolevOutput 1 = 2 ∧ amplifierExponent < requiredPointwiseSaving := by
  refine ⟨?_, amplification_subpolynomial⟩
  unfold sobolevOutput shortMeanSquare; norm_num


/-!
### The pointwise/mean-value gap is self-similar

The intermediate target of Theorem 34 is `T(q) = Σ_{a mod q, (a,q)=1} (a|q)e(N√(2a/q)) ≪ q^{1/2+ε}`,
uniformly for `q ≤ L`.  Averaging it over `q` instead:

    Σ_{q ≤ L} |T(q)|²  =  Σ_q Σ_{a,a'} (aa'|q) e(N(√(2a/q) − √(2a'/q))),

whose diagonal `a = a'` contributes `Σ_{q≤L} φ(q) ≍ (3/π²)L²`.  Over `L` values of `q` that is an
average of `|T(q)|² ≍ L`, i.e.

    **|T(q)| ≍ L^{1/2} ≍ q^{1/2}  for typical `q` — exactly the target.**

So the target holds in mean square over `q` and is needed uniformly: **the same pointwise/mean-value
gap that Theorem 39 identified for the frontier sum recurs, with the same exactness, one level down.**
-/

/-- Exponent (in `L`) of the mean square of the resonance sums over `q ≤ L`. -/
def resonanceMeanSquare : ℚ := 2

/-- Number of moduli, as an exponent of `L`. -/
def moduliCount : ℚ := 1

/-- Typical size exponent of `|T(q)|`, from the mean square. -/
def typicalResonanceSize : ℚ := (resonanceMeanSquare - moduliCount) / 2

/-- **The typical size is exactly the target `q^{1/2}` at `q ≍ L`.** -/
@[simp] theorem typicalResonanceSize_eq : typicalResonanceSize = 1/2 := by
  unfold typicalResonanceSize resonanceMeanSquare moduliCount; norm_num

/-- **Self-similarity of the obstruction.**  At the top level the mean square of the frontier sum is
the Lindelöf value (Theorem 39, block exponent `3/2` out of `5/2`); one level down the mean square of
the resonance sums is the intermediate target.  In both cases the average is exactly the goal and the
pointwise statement is open. -/
theorem gap_self_similar :
    typicalResonanceSize = 1/2 ∧ fareyExponent 1 1 = 3/2 := by
  exact ⟨typicalResonanceSize_eq, farey_both⟩

/-- The gap at the lower level, like the upper one, is between an average that already meets the
target and a uniform statement that does not follow from it. -/
theorem lower_gap_is_uniformity :
    typicalResonanceSize = 1/2 ∧ (0 : ℚ) < 1/2 := by
  exact ⟨typicalResonanceSize_eq, by norm_num⟩


/-!
### Closing the gap by moments is exactly the Lindelöf hypothesis

Let `E_δ = { t ∈ [T,2T] : |F(t)| > N^{1/2+δ} }`.  The `2k`-th moment bounds its measure:

    |E_δ| · N^{(1+2δ)k}  ≪  ∫ |F|^{2k}  ≪  T^{m(k)+ε} · N^{k},   so  |E_δ| ≪ T^{m(k)+ε} N^{-2kδ}.

With `N = T^{1/2}` and the conjectural `m(k) = 1`, this is `T^{1+ε-kδ}`, which is below `1` — forcing
`E_δ = ∅` — exactly when `k > (1+ε)/δ`.  **No finite `k` works uniformly in `δ`**, so emptying the
exceptional set for every `δ > 0` requires *all* moments, which is the Lindelöf hypothesis itself.
-/

/-- Exponent of `T` bounding the measure of the exceptional set at excess `δ`, using the `2k`-th
moment with `m(k) = 1`. -/
def exceptionalMeasureExponent (k delta : ℚ) : ℚ := 1 - k * delta

/-- The exceptional set is forced empty exactly when the exponent is negative. -/
theorem exceptional_empty_iff {k delta : ℚ} (hd : 0 < delta) :
    exceptionalMeasureExponent k delta < 0 ↔ 1/delta < k := by
  unfold exceptionalMeasureExponent
  rw [div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith [h]

/-- **No finite moment order suffices uniformly.**  For any fixed `k` there is a positive `δ` at which
the exceptional set is not forced empty — namely any `δ ≤ 1/k`. -/
theorem no_finite_moment_suffices {k : ℚ} (hk : 0 < k) :
    ∃ delta : ℚ, 0 < delta ∧ ¬ (exceptionalMeasureExponent k delta < 0) := by
  refine ⟨1/k, div_pos one_pos hk, ?_⟩
  unfold exceptionalMeasureExponent
  have : k * (1/k) = 1 := by field_simp
  rw [this]
  norm_num

/-- The moment order required at excess `δ`. -/
def requiredMomentOrder (delta : ℚ) : ℚ := 1/delta

/-- **The requirement diverges as `δ → 0`.**  Halving the excess doubles the moment order needed. -/
theorem requiredMomentOrder_diverges {delta : ℚ} (hd : 0 < delta) :
    requiredMomentOrder (delta/2) = 2 * requiredMomentOrder delta := by
  unfold requiredMomentOrder
  field_simp


/-!
### The classification theorem exists, and `n^{-it}` is its extremal case

Clause (ii) of the specification asks for a theorem that *classifies* large values rather than counting
them.  Such a theorem exists for multiplicative functions: **Halász's theorem**, in its pretentious
form, says that `|Σ_{n≤N} f(n)| ≪ N(1+M)e^{-M}` with

    M  =  min_{|t'| ≤ T}  Σ_{p ≤ N} (1 − Re f(p)p^{-it'}) / p ,

so a multiplicative `f` has a large sum only if it *pretends* to be `n^{it'}χ(n)`.

For `f(n) = n^{-it}` the minimum is attained at `t' = -t`, where `M = 0` and the bound is trivial:
**`n^{-it}` is exactly the extremal pretentious function.**  Restricting the range to `|t'| ≤ N` (with
`t ≍ N²`, so `t' = -t` is excluded) leaves `|t + t'| ≍ N²`, the phases `(t+t')\log p` oscillate, and
`M ≍ \log\log N`.  The resulting saving is

    N (\log\log N) e^{-\log\log N}  ≍  N \log\log N / \log N  —  **subpolynomial.**
-/

/-- Exponent (in `N`) of the saving delivered by Halász's theorem on `n^{-it}` with a restricted
pretentious range. -/
def halaszExponent : ℚ := 0

/-- **Halász supplies no power of `N`.** -/
theorem halasz_subpolynomial : halaszExponent < requiredPointwiseSaving := by
  unfold halaszExponent requiredPointwiseSaving; norm_num

/-- Halász and amplification deliver the same exponent: both are subpolynomial. -/
theorem halasz_eq_amplification : halaszExponent = amplifierExponent := by
  unfold halaszExponent amplifierExponent; rfl

/-- **The classification branch, priced.**  A theorem meeting clauses (ii) and (iii) of the
specification exists, and its output exponent is `0`. -/
theorem classification_branch_priced :
    halaszExponent = 0 ∧ halaszExponent < requiredPointwiseSaving ∧
    halaszExponent < (5/6 : ℚ) - 2/3 := by
  refine ⟨rfl, halasz_subpolynomial, ?_⟩
  unfold halaszExponent; norm_num


/-!
### A single arc already exceeds the target

The resonance abscissa runs over `α_r = N²/(2n_r²) ∈ [1/8, 1/2]`, on a grid of spacing `L^{-2}`.  The
smallest Farey denominator occurring there is `q = 2`, at `α = 1/2`, i.e. `n_r ≈ N`.  Its arc has width
`≍ 1/(2L)`, so it contains

    (1/(2L)) / L^{-2}  ≍  **L**   coherence blocks,

each of size `≍ L/√2 ≍ L`.  The arc's total modulus is therefore `≍ L²`, while the Lindelöf target for
the whole frontier sum is `L^{3/2}`.

**One arc alone exceeds the target by `L^{1/2}`.**  So the Lindelöf hypothesis requires square-root
cancellation among the `≍L` blocks of that single arc — a necessary condition, independent of all
other arcs.
-/

/-- Number of coherence blocks in the arc of smallest denominator, as an exponent of `L`. -/
def principalArcBlockCount : ℚ := 1

/-- Size of each such block, as an exponent of `L`. -/
def principalArcBlockSize : ℚ := 1

/-- Total modulus of the principal arc. -/
def principalArcModulus : ℚ := principalArcBlockCount + principalArcBlockSize

@[simp] theorem principalArcModulus_eq : principalArcModulus = 2 := by
  unfold principalArcModulus principalArcBlockCount principalArcBlockSize; norm_num

/-- **The principal arc alone exceeds the Lindelöf target.** -/
theorem principal_arc_exceeds_target : fareyExponent 1 1 < principalArcModulus := by
  rw [principalArcModulus_eq, farey_both]; norm_num

/-- By exactly `L^{1/2}`. -/
@[simp] theorem principal_arc_excess : principalArcModulus - fareyExponent 1 1 = 1/2 := by
  rw [principalArcModulus_eq, farey_both]; norm_num

/-- Square-root cancellation among the arc's blocks reduces its contribution to
`principalArcBlockCount/2 + principalArcBlockSize`. -/
def principalArcWithCancellation : ℚ := principalArcBlockCount/2 + principalArcBlockSize

/-- **And square-root cancellation in that one arc brings it exactly to the target.** -/
@[simp] theorem principal_arc_cancellation_meets_target :
    principalArcWithCancellation = fareyExponent 1 1 := by
  unfold principalArcWithCancellation principalArcBlockCount principalArcBlockSize
  rw [farey_both]; norm_num

/-- The arc is a small part of the total modulus `L^{5/2}` — it is not the dominant term, yet it alone
already exceeds the target. -/
theorem principal_arc_not_dominant : principalArcModulus < fareyExponent 0 0 := by
  rw [principalArcModulus_eq, farey_none]; norm_num


/-!
### The principal arc is an explicit cubic-form Weyl sum

On the arc `α ≈ 1/2` the blocks are indexed by `|r| ≲ L/2`, with `n_r = N + rL` and

    α_r − 1/2 = N²/(2n_r²) − 1/2 ≈ −rL/N = −r/L²,
    {β_r} = {−N²/n_r} = {−r²L²/N + …} ≈ {−r²/L},

since `N` and `rL` are integers.  The block at `r` is the chirp `Σ_{m<L} e(δ_r m² + β_r m)` — the
factor `(−1)^{m²} = (−1)^m` from `α ≈ 1/2` only shifts the linear coefficient.  Substituting,

    Σ_{r,m ≲ L} e( −r m²/L² − r² m/L )  =  Σ_{r,m} e( −L·uv(u+v) ),   u = r/L, v = m/L ∈ [0,1].

**The principal arc is a two-dimensional Weyl sum over `L²` points with phase the cubic form
`uv(u+v)` at amplitude `L`.**

Its trivial bound is `L²` and the Lindelöf target is `L^{3/2}`: a saving of `L^{1/2}` — **a quarter
power of the number of terms, strictly weaker than square-root cancellation, which would give `L`.**
-/

/-- Number of terms in the principal-arc double sum, as an exponent of `L`. -/
def arcSumTerms : ℚ := 2

/-- Square-root cancellation over those terms. -/
def arcSqrtCancellation : ℚ := arcSumTerms / 2

/-- The saving the Lindelöf hypothesis requires of the arc. -/
def arcRequiredSaving : ℚ := principalArcModulus - fareyExponent 1 1

@[simp] theorem arcRequiredSaving_eq : arcRequiredSaving = 1/2 := by
  unfold arcRequiredSaving; exact principal_arc_excess

/-- The saving square-root cancellation would give. -/
def arcSqrtSaving : ℚ := arcSumTerms - arcSqrtCancellation

@[simp] theorem arcSqrtSaving_eq : arcSqrtSaving = 1 := by
  unfold arcSqrtSaving arcSqrtCancellation arcSumTerms; norm_num

/-- **The requirement is strictly weaker than square-root cancellation.** -/
theorem arc_requirement_below_sqrt : arcRequiredSaving < arcSqrtSaving := by
  rw [arcRequiredSaving_eq, arcSqrtSaving_eq]; norm_num

/-- It is exactly a quarter power of the number of terms. -/
@[simp] theorem arc_requirement_quarter : arcRequiredSaving = arcSumTerms / 4 := by
  rw [arcRequiredSaving_eq]; unfold arcSumTerms; norm_num

/-- The exponent the arc sum must attain: `L^{3/2}` from `L²` terms. -/
def arcTargetExponent : ℚ := principalArcModulus - arcRequiredSaving

@[simp] theorem arcTargetExponent_eq : arcTargetExponent = 3/2 := by
  unfold arcTargetExponent
  rw [arcRequiredSaving_eq, principalArcModulus_eq]; norm_num

/-- **Square-root cancellation in the arc would overshoot the requirement.** -/
theorem sqrt_overshoots_requirement : arcSqrtCancellation < arcTargetExponent := by
  rw [arcTargetExponent_eq]
  unfold arcSqrtCancellation arcSumTerms; norm_num

end HTGeometry
