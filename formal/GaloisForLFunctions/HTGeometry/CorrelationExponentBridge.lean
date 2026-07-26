/-
From a power-law correlation bound to the block exponent.

Applying the van der Corput inequality to the critical block `n ∼ N` with a correlation bound of the
shape `‖C(h)‖ ≪ N^a h^b` for `1 ≤ h < H` gives

    ‖Σ‖²  ≪  N²/H  +  N^{1+a} H^b ,

since the diagonal contributes `N²/H` and the weighted off-diagonal contributes
`(N/H²)·N^a H^{b+2}`.  Balancing the two at `H = N^{(1-a)/(1+b)}` yields

    ‖Σ‖  ≪  N^{blockExponent a b},      blockExponent a b = 1 - (1-a)/(2(1+b)),

and hence `μ = (blockExponent a b - 1/2)/2`.

The second-derivative test supplies `a = b = 1/2` for the critical block, and the formula returns
`5/6` and `μ = 1/6` — Weyl's exponent, derived rather than quoted.  The formula also shows what would
be needed for more: `μ = 0` forces `a + b = 0`, i.e. correlations of size `N^ε`, which is below the
square-root barrier of the correlation sum itself.  Imposing only that a correlation of `N` unimodular
terms is not estimated below square root, i.e. `a ≥ 1/2`, gives `blockExponent (1/2) 0 = 3/4` and
`μ = 1/8`.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace HTGeometry

/-- The block exponent produced by a correlation bound `‖C(h)‖ ≪ N^a h^b`, after optimising the
van der Corput shift parameter. -/
def blockExponent (a b : ℚ) : ℚ := 1 - (1 - a) / (2 * (1 + b))

/-- The optimal shift parameter, as an exponent of `N`. -/
def optimalShift (a b : ℚ) : ℚ := (1 - a) / (1 + b)

/-- The Lindelöf exponent delivered by a block exponent. -/
def muOfBlock (c : ℚ) : ℚ := (c - 1/2) / 2

/-- **The second-derivative test input reproduces Weyl's exponent.**  With `a = b = 1/2` the block
exponent is `5/6` and the optimal shift is `N^{1/3}`. -/
@[simp] theorem blockExponent_secondDeriv : blockExponent (1/2) (1/2) = 5/6 := by
  unfold blockExponent; norm_num

@[simp] theorem optimalShift_secondDeriv : optimalShift (1/2) (1/2) = 1/3 := by
  unfold optimalShift; norm_num

/-- **Weyl's exponent, derived.** -/
@[simp] theorem mu_secondDeriv : muOfBlock (blockExponent (1/2) (1/2)) = 1/6 := by
  rw [blockExponent_secondDeriv]; unfold muOfBlock; norm_num

/-- **The Lindelöf condition on the correlation exponents.**  `blockExponent a b = 1/2` — that is,
square-root cancellation on the block, equivalently `μ = 0` — holds exactly when `a + b = 0`. -/
theorem blockExponent_eq_half_iff {a b : ℚ} (hb : -1 < b) :
    blockExponent a b = 1/2 ↔ a + b = 0 := by
  have hpos : (0:ℚ) < 2 * (1 + b) := by linarith
  unfold blockExponent
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
@[simp] theorem blockExponent_sqrtCorrelation : blockExponent (1/2) 0 = 3/4 := by
  unfold blockExponent; norm_num

/-- **`μ = 1/8` is the floor of the van der Corput route.** -/
@[simp] theorem mu_sqrtCorrelation : muOfBlock (blockExponent (1/2) 0) = 1/8 := by
  rw [blockExponent_sqrtCorrelation]; unfold muOfBlock; norm_num

/-- The block exponent is monotone in each correlation exponent: better correlation bounds give
better block bounds, and the dependence is strict. -/
theorem blockExponent_strictMono_a {a a' b : ℚ} (hb : -1 < b) (h : a < a') :
    blockExponent a b < blockExponent a' b := by
  have hpos : (0:ℚ) < 2 * (1 + b) := by linarith
  unfold blockExponent
  have hlt : (1 - a') < (1 - a) := by linarith
  have : (1 - a') / (2 * (1 + b)) < (1 - a) / (2 * (1 + b)) := by
    rw [div_lt_div_iff₀ hpos hpos]
    nlinarith
  linarith

/-- At `a = 1` the correlation bound is trivial and the block exponent is `1`: no cancellation. -/
@[simp] theorem blockExponent_trivial (b : ℚ) : blockExponent 1 b = 1 := by
  unfold blockExponent; norm_num

/-- **The three-way coincidence at `1/8`.**  The van der Corput route's floor `muOfBlock
(blockExponent (1/2) 0)`, the exponent-pair floor `(κ+λ = 3/4)`, and the eighth-moment target all
give the same Lindelöf exponent. -/
theorem floor_coincidence :
    muOfBlock (blockExponent (1/2) 0) = 1/8 ∧ blockExponent (1/2) 0 = 3/4 ∧
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
    blockExponent (1/2) (1/2) = 5/6 ∧ incoherentBlockTotal 3 = 5/6 ∧
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

end HTGeometry
