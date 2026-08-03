import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# A coherent position/Euler square is excluded by one boundary packet

The exclusion theorem, end to end.

* `star_combo_expand` — the completion-of-squares identity for a self-adjoint `X` and a skew-adjoint
  `Z`: `star (X - Z) * (X - Z) = X² - [X, Z] + (star Z) Z`.  Pure `⋆`-ring algebra; with
  `star_smul_selfAdjoint` and `star_smul_skewAdjoint` it applies to `a • X` and `b • Z`, which is the
  balanced form of the identity.
* `norm_sub_smul_sq_of_inner_eq_zero` and `two_mul_norm_mul_norm_le` — on a packet where the two
  outputs are orthogonal the square splits, and the split is bounded below by `2‖Xf‖‖Zf‖` for every
  balancing scalar.  So no choice of `α` can be cheap.
* `fwdShift`, `bwdShift`, `bwdShift_eq_zero_of_support`, `integral_fwdShift_mul_eq_zero`,
  `commutatorForm_eq_zero` — the fixed boundary packet: for a vector supported in `(0, δ)` and shifts
  of length exceeding `δ`, the backward shift annihilates the packet and the forward shift leaves its
  support, so the whole prime commutator form vanishes on it.  No measure theory beyond
  `integral_zero`, because the integrand is identically zero.
* `primeReciprocalSum`, `tendsto_primeReciprocalSum_atTop`, `BoundaryPacket`, `primeChannel`,
  `eulerShellApply`, `primeReciprocalSum_mul_mass_le`, `tendsto_energy_atTop` — the coherent
  amplification.  On a nonnegative packet every cross term of the coherently summed Euler logarithm
  is nonnegative, so the energy is at least the diagonal, which is the prime reciprocal sum times the
  packet mass.  Euler's divergence of that sum is the only arithmetic input; no prime-counting rate
  is needed.  `tentPacket` and `boundaryPacket_tentPacket` exhibit a packet at every width, so the
  statement is not vacuous.
* `integral_sq_sub_of_orthogonal`, `two_mul_sqrt_mul_sqrt_le`, `positionApply`,
  `positionApply_mass_pos`, `positionApply_mul_primeChannel_eq_zero`,
  `not_exists_coherent_square_packet` — the exclusion in the concrete model: the position energy is
  positive and aperture-independent, it is exactly orthogonal to the Euler output once the packet is
  narrower than `log 2`, the mixed square therefore splits, and no balancing scalar brings the split
  below twice the geometric mean of the two energies, which diverges.
* `not_exists_coherent_square`, `not_exists_coherent_square_of_divergence` — the same conclusion at
  the level of an abstract real inner product space: a form with a fixed finite value on the packet
  cannot equal a coherent square plus a nonnegative remainder once the square's lower bound diverges,
  no matter how the balancing scalar depends on the aperture.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology MeasureTheory Set

/-! ## The completion-of-squares identity -/

/-- **Equation (15).**  With `X` self-adjoint and `Z` skew-adjoint the mixed square expands with the
commutator as the only cross term. -/
theorem star_combo_expand {R : Type*} [Ring R] [StarRing R] (X Z : R)
    (hX : star X = X) (hZ : star Z = -Z) :
    star (X - Z) * (X - Z) = X * X - (X * Z - Z * X) + star Z * Z := by
  have hstar : star (X - Z) = X + Z := by
    rw [star_sub, hX, hZ, sub_neg_eq_add]
  rw [hstar, hZ]
  noncomm_ring

/-- Scaling by a real preserves self-adjointness. -/
theorem star_smul_selfAdjoint {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]
    (a : ℝ) {X : R} (hX : star X = X) : star (a • X) = a • X := by
  rw [star_smul, hX, star_trivial]

/-- Scaling by a real preserves skew-adjointness.  Together with `star_combo_expand` applied to
`a • X` and `b • Z` this is `(15)` for an arbitrary balancing scalar. -/
theorem star_smul_skewAdjoint {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]
    (b : ℝ) {Z : R} (hZ : star Z = -Z) : star (b • Z) = -(b • Z) := by
  rw [star_smul, hZ, star_trivial, smul_neg]

/-! ## The orthogonal split and its lower bound -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a packet where the two outputs are orthogonal the mixed square splits exactly. -/
theorem norm_sub_smul_sq_of_inner_eq_zero {u v : E} (h : inner ℝ u v = (0 : ℝ)) (a b : ℝ) :
    ‖a • u - b • v‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 := by
  have hsq : ‖a • u - b • v‖ ^ 2
      = ‖a • u‖ ^ 2 - 2 * inner ℝ (a • u) (b • v) + ‖b • v‖ ^ 2 := norm_sub_sq_real _ _
  rw [hsq, real_inner_smul_left, real_inner_smul_right, h, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs]
  rw [mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- **Equation (16).**  Every balancing scalar pays at least `2‖u‖‖v‖`. -/
theorem two_mul_norm_mul_norm_le {u v : E} (h : inner ℝ u v = (0 : ℝ)) {a b : ℝ}
    (hab : a * b = 1) : 2 * (‖u‖ * ‖v‖) ≤ ‖a • u - b • v‖ ^ 2 := by
  rw [norm_sub_smul_sq_of_inner_eq_zero h]
  have hsq : 0 ≤ (a * ‖u‖ - b * ‖v‖) ^ 2 := sq_nonneg _
  have habs : a * b * (‖u‖ * ‖v‖) = ‖u‖ * ‖v‖ := by rw [hab, one_mul]
  nlinarith [hsq, habs]

/-! ## The fixed boundary packet -/

/-- The aperture-restricted forward shift. -/
def fwdShift (A h : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if h ≤ x ∧ x ≤ A then f (x - h) else 0

/-- The aperture-restricted backward shift, the adjoint of `fwdShift`. -/
def bwdShift (A h : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if 0 ≤ x ∧ x + h ≤ A then f (x + h) else 0

/-- **Equation (7), backward half.**  A shift longer than the packet width annihilates the packet. -/
theorem bwdShift_eq_zero_of_support {A h delta : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta) (hh : delta ≤ h) :
    bwdShift A h f = fun _ => 0 := by
  funext x
  simp only [bwdShift]
  by_cases hx : 0 ≤ x ∧ x + h ≤ A
  · rw [if_pos hx]
    by_contra hne
    obtain ⟨_, hlt⟩ := hf (x + h) hne
    linarith [hx.1]
  · rw [if_neg hx]

/-- **Equation (7), forward half.**  The forward shift leaves the packet's support, so its pairing
with the packet vanishes identically. -/
theorem fwdShift_mul_eq_zero {A h delta : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta) (hh : delta ≤ h) (x : ℝ) :
    fwdShift A h f x * f x = 0 := by
  by_cases hx : f x = 0
  · rw [hx, mul_zero]
  · obtain ⟨_, hlt⟩ := hf x hx
    have hnot : ¬ (h ≤ x ∧ x ≤ A) := by
      intro hc
      linarith [hc.1]
    simp only [fwdShift, if_neg hnot, zero_mul]

theorem integral_fwdShift_mul_eq_zero {A h delta : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta) (hh : delta ≤ h) :
    (∫ x : ℝ, fwdShift A h f x * f x) = 0 := by
  have hzero : (fun x : ℝ => fwdShift A h f x * f x) = fun _ : ℝ => (0 : ℝ) :=
    funext fun x => fwdShift_mul_eq_zero hf hh x
  rw [hzero, integral_zero]

/-- **Equation (8).**  The whole prime commutator form vanishes on the packet: every shift is longer
than the packet width, so both the forward and the backward channel contribute nothing. -/
theorem commutatorForm_eq_zero {A delta : ℝ} {f : ℝ → ℝ} {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (hh : ι → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta)
    (hlong : ∀ n ∈ s, delta ≤ hh n) :
    (∫ x : ℝ, (∑ n ∈ s, c n * (fwdShift A (hh n) f x + bwdShift A (hh n) f x)) * f x) = 0 := by
  have hzero : (fun x : ℝ =>
      (∑ n ∈ s, c n * (fwdShift A (hh n) f x + bwdShift A (hh n) f x)) * f x)
      = fun _ : ℝ => (0 : ℝ) := by
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hb : bwdShift A (hh n) f x = 0 := by
      rw [bwdShift_eq_zero_of_support hf (hlong n hn)]
    have hfwd : fwdShift A (hh n) f x * f x = 0 :=
      fwdShift_mul_eq_zero hf (hlong n hn) x
    calc c n * (fwdShift A (hh n) f x + bwdShift A (hh n) f x) * f x
        = c n * (fwdShift A (hh n) f x * f x) + c n * (bwdShift A (hh n) f x * f x) := by ring
      _ = 0 := by rw [hfwd, hb]; ring
  rw [hzero, integral_zero]

/-! ## The exclusion -/

/-- **Equations (17)–(19).**  A form whose value on the packet is a fixed finite constant cannot be a
coherent square plus a nonnegative remainder once the square's lower bound diverges — for any
aperture-dependent balancing scalar. -/
theorem not_exists_coherent_square {q sq rem lower : ℕ → ℝ}
    (hq : ∀ j, q j = sq j + rem j) (hrem : ∀ j, 0 ≤ rem j)
    (hsq : ∀ j, lower j ≤ sq j) (hconst : ∃ c : ℝ, ∀ j, q j = c)
    (hdiv : Tendsto lower atTop atTop) : False := by
  obtain ⟨c, hc⟩ := hconst
  obtain ⟨j, hj⟩ := (hdiv.eventually_gt_atTop c).exists
  have h1 : lower j ≤ sq j := hsq j
  have h2 : sq j ≤ q j := by
    have := hrem j
    have := hq j
    linarith
  have h3 : q j = c := hc j
  linarith


/-! ## Compact-support combinators -/

theorem hasCompactSupport_sq {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport fun x : ℝ => (g x) ^ 2 := by
  have hgg : (fun x : ℝ => (g x) ^ 2) = g * g := by funext x; rw [sq]; rfl
  rw [hgg]
  exact hg.mul_right

theorem hasCompactSupport_mul {g h : ℝ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport fun x : ℝ => g x * h x := hg.mul_right

/-! ## The coherent boundary energy diverges -/

/-- The reciprocal sum over the primes below `N`. -/
def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range N).filter Nat.Prime, (p : ℝ)⁻¹

/-- Euler's divergence.  This is the only arithmetic input to the coherent lower bound: no rate for
the prime count is used, only that the reciprocal sums are unbounded. -/
theorem tendsto_primeReciprocalSum_atTop :
    Tendsto primeReciprocalSum atTop atTop := by
  classical
  have hnn : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | Nat.Prime p} (fun m : ℕ => (1 : ℝ) / m) n := by
    intro n
    rw [Set.indicator_apply]
    split_ifs with h
    · positivity
    · exact le_rfl
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp not_summable_one_div_on_primes
  refine Tendsto.congr (fun n => ?_) h
  rw [primeReciprocalSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq, one_div]

/-- A left-boundary packet: continuous, nonnegative, supported in `(0, delta)`, of positive mass.
The same zero-extended packet is used at every aperture. -/
structure BoundaryPacket (delta : ℝ) (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  nonneg : ∀ x, 0 ≤ f x
  support : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta
  mass_pos : 0 < ∫ x, (f x) ^ 2

theorem BoundaryPacket.hasCompactSupport {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := delta)) ?_
  intro x hx
  by_contra hne
  exact hx (Ioo_subset_Icc_self (hp.support x hne))

theorem BoundaryPacket.exists_ne_zero {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) :
    ∃ x, f x ≠ 0 := by
  by_contra hall
  have hall' : ∀ x, f x = 0 := fun x => not_not.mp fun h => hall ⟨x, h⟩
  have hz : (∫ x, (f x) ^ 2) = 0 := by simp [hall']
  exact absurd hz (ne_of_gt hp.mass_pos)

/-- The packet is a translate of `fwdShift` once the shift plus the packet width fits inside the
aperture: the aperture cutoff is then invisible to the packet. -/
theorem fwdShift_eq_translate {A h delta : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta) (hA : h + delta ≤ A) :
    fwdShift A h f = fun x => f (x - h) := by
  funext x
  simp only [fwdShift]
  by_cases hx : h ≤ x ∧ x ≤ A
  · rw [if_pos hx]
  · rw [if_neg hx]
    refine (?_ : f (x - h) = 0).symm
    by_contra hne
    obtain ⟨h1, h2⟩ := hf (x - h) hne
    exact hx ⟨by linarith, by linarith⟩

/-- The `p`-th channel of the Euler logarithm acting on a packet: the translate by `log p` carrying
the coefficient `p^{-1/2}` of `(3)` at exponent one. -/
def primeChannel (f : ℝ → ℝ) (p : ℕ) : ℝ → ℝ :=
  fun x => (Real.sqrt p)⁻¹ * f (x - Real.log p)

/-- **Equation (2), exponent-one shell.**  The coherently summed Euler logarithm applied to a
packet.  On a left-boundary packet the backward shifts contribute nothing, by
`bwdShift_eq_zero_of_support`, so this is the whole output. -/
def eulerShellApply (A : ℝ) (N : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∑ p ∈ (Finset.range N).filter Nat.Prime, (Real.sqrt p)⁻¹ * fwdShift A (Real.log p) f x

theorem primeChannel_nonneg {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) (p : ℕ) (x : ℝ) :
    0 ≤ primeChannel f p x :=
  mul_nonneg (by positivity) (hp.nonneg _)

theorem primeChannel_eq_zero_of_notMem {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f)
    (p : ℕ) {x : ℝ} (hx : x ∉ Icc (Real.log p) (Real.log p + delta)) :
    primeChannel f p x = 0 := by
  have hz : f (x - Real.log p) = 0 := by
    by_contra hne
    obtain ⟨h1, h2⟩ := hp.support _ hne
    exact hx ⟨by linarith, by linarith⟩
  rw [primeChannel, hz, mul_zero]

theorem continuous_primeChannel {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) (p : ℕ) :
    Continuous (primeChannel f p) := by
  have h1 : Continuous fun x : ℝ => x - Real.log p := by fun_prop
  exact continuous_const.mul (hp.continuous.comp h1)

theorem hasCompactSupport_primeChannel {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f)
    (p : ℕ) : HasCompactSupport (primeChannel f p) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := Real.log p) (b := Real.log p + delta)) ?_
  exact fun x hx => primeChannel_eq_zero_of_notMem hp p hx

theorem integrable_sq_primeChannel {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) (p : ℕ) :
    Integrable (fun x => (primeChannel f p x) ^ 2) :=
  ((continuous_primeChannel hp p).pow 2).integrable_of_hasCompactSupport
    (hasCompactSupport_sq (hasCompactSupport_primeChannel hp p))

/-- The mass of one channel is the packet mass scaled by `1/p`, by translation invariance. -/
theorem integral_sq_primeChannel (f : ℝ → ℝ) (p : ℕ) :
    (∫ x, (primeChannel f p x) ^ 2) = (p : ℝ)⁻¹ * ∫ x, (f x) ^ 2 := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hsq : ∀ x : ℝ, (primeChannel f p x) ^ 2 = (p : ℝ)⁻¹ * (f (x - Real.log p)) ^ 2 := by
    intro x
    rw [primeChannel, mul_pow, inv_pow, Real.sq_sqrt hp0]
  calc (∫ x, (primeChannel f p x) ^ 2)
      = ∫ x, (p : ℝ)⁻¹ * (f (x - Real.log p)) ^ 2 := by simp_rw [hsq]
    _ = (p : ℝ)⁻¹ * ∫ x, (f (x - Real.log p)) ^ 2 := integral_const_mul _ _
    _ = (p : ℝ)⁻¹ * ∫ x, (f x) ^ 2 := by
        congr 1
        exact integral_sub_right_eq_self (fun y => (f y) ^ 2) (Real.log p)

theorem log_bounds_of_mem_primeFilter {N p : ℕ} (hpP : p ∈ (Finset.range N).filter Nat.Prime) :
    0 ≤ Real.log p ∧ Real.log p ≤ Real.log N := by
  rw [Finset.mem_filter, Finset.mem_range] at hpP
  have h2 : 2 ≤ p := hpP.2.two_le
  have hpn : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpP.1.le
  refine ⟨Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)), ?_⟩
  exact Real.log_le_log (by positivity) hpn

/-- Inside a large enough aperture the shell is exactly the sum of the prime channels. -/
theorem eulerShellApply_eq_sum_primeChannel {A delta : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hp : BoundaryPacket delta f)
    (hA : ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A) :
    eulerShellApply A N f
      = fun x => ∑ p ∈ (Finset.range N).filter Nat.Prime, primeChannel f p x := by
  funext x
  rw [eulerShellApply]
  refine Finset.sum_congr rfl fun p hpP => ?_
  rw [fwdShift_eq_translate hp.support (hA p hpP), primeChannel]

theorem continuous_eulerShellApply {A delta : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hp : BoundaryPacket delta f)
    (hA : ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A) :
    Continuous (eulerShellApply A N f) := by
  rw [eulerShellApply_eq_sum_primeChannel hp hA]
  exact continuous_finsetSum _ fun p _ => continuous_primeChannel hp p

theorem hasCompactSupport_eulerShellApply {A delta : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hp : BoundaryPacket delta f)
    (hA : ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A) :
    HasCompactSupport (eulerShellApply A N f) := by
  rw [eulerShellApply_eq_sum_primeChannel hp hA]
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := Real.log N + delta)) ?_
  intro x hx
  refine Finset.sum_eq_zero fun p hpP => ?_
  refine primeChannel_eq_zero_of_notMem hp p ?_
  intro hmem
  obtain ⟨hl0, hlN⟩ := log_bounds_of_mem_primeFilter hpP
  exact hx ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem integrable_sq_eulerShellApply {A delta : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hp : BoundaryPacket delta f)
    (hA : ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A) :
    Integrable fun x => (eulerShellApply A N f x) ^ 2 :=
  ((continuous_eulerShellApply hp hA).pow 2).integrable_of_hasCompactSupport
    (hasCompactSupport_sq (hasCompactSupport_eulerShellApply hp hA))

/-- **Equations (12)--(14), sharpened.**  The coherent boundary energy of the Euler logarithm on a
fixed packet is at least the prime reciprocal sum times the packet mass.  Every cross term is
nonnegative, because the packet is nonnegative and every Euler coefficient is positive, so the energy
dominates its diagonal, whose `p`-th entry is exactly `1/p` times the mass.  The card's rate
`e^{A/2}/A` is replaced by this identity together with Euler's divergence, which is all the exclusion
consumes. -/
theorem primeReciprocalSum_mul_mass_le {A delta : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hp : BoundaryPacket delta f)
    (hA : ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A) :
    primeReciprocalSum N * (∫ x, (f x) ^ 2) ≤ ∫ x, (eulerShellApply A N f x) ^ 2 := by
  classical
  have hshell := eulerShellApply_eq_sum_primeChannel hp hA
  have hptw : ∀ x : ℝ,
      (∑ p ∈ (Finset.range N).filter Nat.Prime, (primeChannel f p x) ^ 2)
        ≤ (∑ p ∈ (Finset.range N).filter Nat.Prime, primeChannel f p x) ^ 2 := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun p hpP => ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun q => primeChannel f p x * primeChannel f q x)
      (fun q _ => mul_nonneg (primeChannel_nonneg hp p x) (primeChannel_nonneg hp q x)) hpP
  have hsumint : Integrable
      (fun x => ∑ p ∈ (Finset.range N).filter Nat.Prime, (primeChannel f p x) ^ 2) :=
    integrable_finsetSum _ fun p _ => integrable_sq_primeChannel hp p
  have hdiag : (∫ x, ∑ p ∈ (Finset.range N).filter Nat.Prime, (primeChannel f p x) ^ 2)
      = primeReciprocalSum N * (∫ x, (f x) ^ 2) := by
    rw [integral_finsetSum _ fun p _ => integrable_sq_primeChannel hp p, primeReciprocalSum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => integral_sq_primeChannel f p
  rw [← hdiag]
  refine integral_mono hsumint (integrable_sq_eulerShellApply hp hA) fun x => ?_
  simp only [hshell]
  exact hptw x

/-- The coherent boundary energy diverges along every aperture schedule that keeps each visible prime
shift inside the aperture. -/
theorem tendsto_energy_atTop {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) (A : ℕ → ℝ)
    (hA : ∀ N, ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A N) :
    Tendsto (fun N => ∫ x, (eulerShellApply (A N) N f x) ^ 2) atTop atTop :=
  tendsto_atTop_mono (fun N => primeReciprocalSum_mul_mass_le hp (hA N))
    (tendsto_primeReciprocalSum_atTop.atTop_mul_const hp.mass_pos)

/-- An explicit admissible schedule: aperture `N + delta` already contains every prime shift below
`N`, since `log p ≤ p - 1`. -/
theorem tendsto_energy_atTop_natAperture {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) :
    Tendsto (fun N : ℕ => ∫ x, (eulerShellApply ((N : ℝ) + delta) N f x) ^ 2) atTop atTop := by
  refine tendsto_energy_atTop hp _ fun N p hpP => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hpP
  have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpP.2.pos
  have hlp : Real.log p ≤ (p : ℝ) - 1 := Real.log_le_sub_one_of_pos hpos
  have hpn : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpP.1.le
  linarith

/-! ## The packet class is inhabited -/

/-- An explicit left-boundary packet: the tent supported on `(0, delta)`. -/
def tentPacket (delta : ℝ) : ℝ → ℝ := fun x => max 0 (min x (delta - x))

theorem continuous_tentPacket (delta : ℝ) : Continuous (tentPacket delta) := by
  unfold tentPacket
  fun_prop

theorem tentPacket_nonneg (delta : ℝ) (x : ℝ) : 0 ≤ tentPacket delta x := le_max_left _ _

theorem tentPacket_support {delta x : ℝ} (hx : tentPacket delta x ≠ 0) : x ∈ Ioo 0 delta := by
  have h : 0 < min x (delta - x) := by
    rcases lt_or_ge 0 (min x (delta - x)) with h | h
    · exact h
    · exact absurd (max_eq_left h : max 0 (min x (delta - x)) = 0) hx
  refine ⟨lt_of_lt_of_le h (min_le_left _ _), ?_⟩
  have h2 := lt_of_lt_of_le h (min_le_right _ _)
  linarith

theorem tentPacket_mid (delta : ℝ) : tentPacket delta (delta / 2) = max 0 (delta / 2) := by
  rw [tentPacket]
  congr 1
  rw [show delta - delta / 2 = delta / 2 by ring, min_self]

theorem hasCompactSupport_sq_tentPacket (delta : ℝ) :
    HasCompactSupport fun x : ℝ => (tentPacket delta x) ^ 2 := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := delta)) ?_
  intro x hx
  have hz : tentPacket delta x = 0 := by
    by_contra hne
    exact hx (Ioo_subset_Icc_self (tentPacket_support hne))
  rw [hz]
  ring

/-- The packet class of the exclusion theorem is inhabited at every width. -/
theorem boundaryPacket_tentPacket {delta : ℝ} (hd : 0 < delta) :
    BoundaryPacket delta (tentPacket delta) := by
  have hc : Continuous fun x : ℝ => (tentPacket delta x) ^ 2 :=
    (continuous_tentPacket delta).pow 2
  refine ⟨continuous_tentPacket delta, tentPacket_nonneg delta,
    fun x hx => tentPacket_support hx, ?_⟩
  refine integral_pos_of_integrable_nonneg_nonzero (x := delta / 2) hc
    (hc.integrable_of_hasCompactSupport (hasCompactSupport_sq_tentPacket delta))
    (fun x => by positivity) ?_
  rw [tentPacket_mid, max_eq_right (by positivity : (0 : ℝ) ≤ delta / 2)]
  positivity

/-! ## The concrete exclusion on the packet -/

/-- **Equation (16).**  On a pair of orthogonal outputs the mixed square splits exactly. -/
theorem integral_sq_sub_of_orthogonal {g h : ℝ → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (hhc : Continuous h) (hhs : HasCompactSupport h)
    (horth : (∫ x, g x * h x) = 0) (a b : ℝ) :
    (∫ x, (a * g x - b * h x) ^ 2)
      = a ^ 2 * (∫ x, (g x) ^ 2) + b ^ 2 * ∫ x, (h x) ^ 2 := by
  have hgsq : Integrable fun x : ℝ => (g x) ^ 2 :=
    (hgc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hgs)
  have hhsq : Integrable fun x : ℝ => (h x) ^ 2 :=
    (hhc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hhs)
  have hgh : Integrable fun x : ℝ => g x * h x :=
    (hgc.mul hhc).integrable_of_hasCompactSupport (hasCompactSupport_mul hgs)
  have i1 : Integrable fun x : ℝ => a ^ 2 * (g x) ^ 2 := hgsq.const_mul _
  have i2 : Integrable fun x : ℝ => b ^ 2 * (h x) ^ 2 := hhsq.const_mul _
  have i3 : Integrable fun x : ℝ => 2 * a * b * (g x * h x) := hgh.const_mul _
  have i12 : Integrable fun x : ℝ => a ^ 2 * (g x) ^ 2 + b ^ 2 * (h x) ^ 2 := i1.add i2
  have e1 : ∀ x : ℝ, (a * g x - b * h x) ^ 2
      = a ^ 2 * (g x) ^ 2 + b ^ 2 * (h x) ^ 2 - 2 * a * b * (g x * h x) := fun x => by ring
  simp_rw [e1]
  rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, horth, mul_zero, sub_zero]

/-- Balancing is powerless: whatever the scalar, the split is at least twice the geometric mean of
the two energies. -/
theorem two_mul_sqrt_mul_sqrt_le {X Z a : ℝ} (hX : 0 ≤ X) (hZ : 0 ≤ Z) (ha : a ≠ 0) :
    2 * Real.sqrt X * Real.sqrt Z ≤ a ^ 2 * X + (a⁻¹) ^ 2 * Z := by
  have hsX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have hsZ : Real.sqrt Z ^ 2 = Z := Real.sq_sqrt hZ
  have h0 : 0 ≤ (a * Real.sqrt X - a⁻¹ * Real.sqrt Z) ^ 2 := sq_nonneg _
  have hai : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hexp : (a * Real.sqrt X - a⁻¹ * Real.sqrt Z) ^ 2
      = a ^ 2 * X + (a⁻¹) ^ 2 * Z - 2 * Real.sqrt X * Real.sqrt Z := by
    have hring : (a * Real.sqrt X - a⁻¹ * Real.sqrt Z) ^ 2
        = a ^ 2 * (Real.sqrt X ^ 2) + (a⁻¹) ^ 2 * (Real.sqrt Z ^ 2)
          - 2 * (a * a⁻¹) * (Real.sqrt X * Real.sqrt Z) := by ring
    rw [hring, hsX, hsZ, hai]
    ring
  linarith [h0, hexp]

/-- **Equation (1).**  The position output on the packet. -/
def positionApply (f : ℝ → ℝ) : ℝ → ℝ := fun x => x * f x

theorem continuous_positionApply {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) :
    Continuous (positionApply f) := continuous_id.mul hp.continuous

theorem hasCompactSupport_positionApply {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) :
    HasCompactSupport (positionApply f) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := delta)) ?_
  intro x hx
  have hz : f x = 0 := by
    by_contra hne
    exact hx (Ioo_subset_Icc_self (hp.support x hne))
  rw [positionApply, hz, mul_zero]

/-- The position energy is positive and aperture-independent. -/
theorem positionApply_mass_pos {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f) :
    0 < ∫ x, (positionApply f x) ^ 2 := by
  obtain ⟨x0, hx0⟩ := hp.exists_ne_zero
  have hc : Continuous fun x : ℝ => (positionApply f x) ^ 2 :=
    (continuous_positionApply hp).pow 2
  refine integral_pos_of_integrable_nonneg_nonzero (x := x0) hc
    (hc.integrable_of_hasCompactSupport
      (hasCompactSupport_sq (hasCompactSupport_positionApply hp)))
    (fun x => by positivity) ?_
  have hx0' := hp.support x0 hx0
  exact pow_ne_zero 2 (mul_ne_zero (ne_of_gt hx0'.1) hx0)

/-- **Equation (7), the exact orthogonality.**  Every prime shift is at least `log 2`, so once the
packet is narrower than `log 2` the position output and the Euler output have disjoint supports. -/
theorem positionApply_mul_primeChannel_eq_zero {delta : ℝ} {f : ℝ → ℝ}
    (hp : BoundaryPacket delta f) (hdl : delta ≤ Real.log 2) {p : ℕ} (hpp : Nat.Prime p) (x : ℝ) :
    positionApply f x * primeChannel f p x = 0 := by
  by_cases hx : f x = 0
  · rw [positionApply, hx, mul_zero, zero_mul]
  · have hxd := hp.support x hx
    have hlog2 : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hpp.two_le)
    have hz : f (x - Real.log p) = 0 := by
      by_contra hne
      obtain ⟨h1, _⟩ := hp.support _ hne
      linarith [hxd.2]
    rw [primeChannel, hz, mul_zero, mul_zero]

theorem integral_positionApply_mul_eulerShellApply {A delta : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hp : BoundaryPacket delta f) (hdl : delta ≤ Real.log 2)
    (hA : ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A) :
    (∫ x, positionApply f x * eulerShellApply A N f x) = 0 := by
  have hz : (fun x => positionApply f x * eulerShellApply A N f x) = fun _ : ℝ => (0 : ℝ) := by
    funext x
    rw [eulerShellApply_eq_sum_primeChannel hp hA, Finset.mul_sum]
    refine Finset.sum_eq_zero fun p hpP => ?_
    rw [Finset.mem_filter] at hpP
    exact positionApply_mul_primeChannel_eq_zero hp hdl hpP.2 x
  rw [hz, integral_zero]

/-- **Equations (16)--(19), the exclusion.**  A form whose value on the fixed packet does not depend
on the aperture cannot be presented as the coherent position/Euler square plus a nonnegative
remainder, for any aperture-dependent balancing scalar: the square already diverges, while the
position energy stays fixed and the prime commutator form on the packet stays zero. -/
theorem not_exists_coherent_square_packet {delta : ℝ} {f : ℝ → ℝ} (hp : BoundaryPacket delta f)
    (hdl : delta ≤ Real.log 2) (A : ℕ → ℝ)
    (hA : ∀ N, ∀ p ∈ (Finset.range N).filter Nat.Prime, Real.log p + delta ≤ A N)
    {alpha q r : ℕ → ℝ} (halpha : ∀ N, alpha N ≠ 0)
    (hfact : ∀ N, q N = (∫ x, (alpha N * positionApply f x
        - (alpha N)⁻¹ * eulerShellApply (A N) N f x) ^ 2) + r N)
    (hr : ∀ N, 0 ≤ r N) (hconst : ∃ c : ℝ, ∀ N, q N = c) : False := by
  have hXpos : 0 < ∫ x, (positionApply f x) ^ 2 := positionApply_mass_pos hp
  have hZnn : ∀ N, 0 ≤ ∫ x, (eulerShellApply (A N) N f x) ^ 2 :=
    fun N => integral_nonneg fun x => by positivity
  have hsplit : ∀ N, 2 * Real.sqrt (∫ x, (positionApply f x) ^ 2)
      * Real.sqrt (∫ x, (eulerShellApply (A N) N f x) ^ 2)
      ≤ ∫ x, (alpha N * positionApply f x - (alpha N)⁻¹ * eulerShellApply (A N) N f x) ^ 2 := by
    intro N
    rw [integral_sq_sub_of_orthogonal (continuous_positionApply hp)
      (hasCompactSupport_positionApply hp) (continuous_eulerShellApply hp (hA N))
      (hasCompactSupport_eulerShellApply hp (hA N))
      (integral_positionApply_mul_eulerShellApply hp hdl (hA N))]
    exact two_mul_sqrt_mul_sqrt_le hXpos.le (hZnn N) (halpha N)
  refine not_exists_coherent_square (q := q)
    (sq := fun N => ∫ x, (alpha N * positionApply f x
      - (alpha N)⁻¹ * eulerShellApply (A N) N f x) ^ 2) (rem := r)
    (lower := fun N => 2 * Real.sqrt (∫ x, (positionApply f x) ^ 2)
      * Real.sqrt (∫ x, (eulerShellApply (A N) N f x) ^ 2))
    hfact hr hsplit hconst ?_
  have hsq : Tendsto
      (fun N => Real.sqrt (∫ x, (eulerShellApply (A N) N f x) ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_energy_atTop hp A hA)
  have hc : (0 : ℝ) < 2 * Real.sqrt (∫ x, (positionApply f x) ^ 2) := by
    have := Real.sqrt_pos.mpr hXpos
    positivity
  exact Filter.Tendsto.const_mul_atTop hc hsq

/-- **Equations (16)--(19), the abstract exclusion.**  If the position output `u` is a fixed nonzero vector
orthogonal to the Euler outputs `v j`, and those outputs grow without bound, then no aperture
dependent balancing scalar can present a form of fixed value as a coherent square plus a nonnegative
remainder. -/
theorem not_exists_coherent_square_of_divergence {u : E} {v : ℕ → E} {alpha q r : ℕ → ℝ}
    (horth : ∀ j, inner ℝ u (v j) = (0 : ℝ)) (hu : 0 < ‖u‖) (halpha : ∀ j, alpha j ≠ 0)
    (hdiv : Tendsto (fun j => ‖v j‖) atTop atTop)
    (hfact : ∀ j, q j = ‖alpha j • u - (alpha j)⁻¹ • v j‖ ^ 2 + r j)
    (hr : ∀ j, 0 ≤ r j) (hconst : ∃ c : ℝ, ∀ j, q j = c) : False := by
  refine not_exists_coherent_square (q := q)
    (sq := fun j => ‖alpha j • u - (alpha j)⁻¹ • v j‖ ^ 2) (rem := r)
    (lower := fun j => 2 * (‖u‖ * ‖v j‖)) hfact hr
    (fun j => two_mul_norm_mul_norm_le (horth j) (mul_inv_cancel₀ (halpha j))) hconst ?_
  have h := Filter.Tendsto.const_mul_atTop (show (0 : ℝ) < 2 * ‖u‖ by positivity) hdiv
  refine Tendsto.congr (fun j => ?_) h
  ring

end GaloisForLFunctions.RHTower

end
