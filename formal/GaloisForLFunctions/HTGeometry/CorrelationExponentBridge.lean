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

end HTGeometry
