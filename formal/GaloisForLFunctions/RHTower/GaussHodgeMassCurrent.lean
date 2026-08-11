import GaloisForLFunctions.RHTower.GaussMultiPlaceAssembly

/-!
# The Hodge mass current of the assembled pairing on the reflection-odd carrier

The source-zero horizontal carrier retains two reflection-odd components for every Xi divisor
copy: the cofinal tail log and the prime-labelled Gamma Bockstein.  Pairing them — the natural
quadratic pairing of the odd part with itself — and weighting by the strictly positive assembled
residue current produces the Hodge mass current

`H(q,p) = tailLog(q) · current(p) · Bockstein(q,p)`.

Because the two factors reverse sign together under the line-conjugate reflection, `H` is an
odd-square: unconditionally nonnegative, reflection-even, label-faithful, and vanishing at a
label exactly when the copy lies on the critical line.  **The Hodge sign of the constructed
pairing therefore holds unconditionally**; in closed form `H` is the hyperbolic mass shell

`H(q,p) = (log 2 / 2) · current(p) · density(p) · t · (p^t - p^{-t})`,  `t = 2 Re(q) - 1`.

The Hodge-index application — zero total mass — is exactly RH, and is stated as such, not
assumed.  The interface firewall at the end shows that the sign, evenness, and radical laws hold
for arbitrary label sizes and rate configurations, and that an explicit reflection-closed
off-line configuration has strictly positive mass: no argument from the pairing's own interface,
even with divisor-reflection closure, can force the mass to vanish.  The missing law is a global
trace identity, not more local structure.
-/

namespace RHTower

open GaloisForLFunctions Filter Topology

open GaloisForLFunctions.RHTower

noncomputable section

/-! ## The Hodge mass current -/

/-- The Hodge mass current: the pairing of the two retained reflection-odd carrier components,
weighted by the assembled residue current, at one divisor copy and one prime label. -/
def gaussHodgeMassCurrent (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  sourceZeroHorizontalTailLog q *
    (gaussChannelResidueCurrent m p * sourceZeroHorizontalPrimeCarrier q p)

/-- The tail log in closed form. -/
theorem sourceZeroHorizontalTailLog_closedForm (q : XiZeroCopy) :
    sourceZeroHorizontalTailLog q = (1 / 2 - (q.1 : ℂ).re) * Real.log 2 :=
  (completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog 0 q).2

/-- **Hodge positivity.**  The constructed pairing is nonnegative at every copy and label. -/
theorem gaussHodgeMassCurrent_nonneg {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gaussHodgeMassCurrent m q p := by
  rcases lt_trichotomy ((q.1 : ℂ).re) (1 / 2) with hlt | heq | hgt
  · have h1 : 0 < sourceZeroHorizontalTailLog q := by
      rw [sourceZeroHorizontalTailLog_closedForm]
      exact mul_pos (by linarith) (Real.log_pos (by norm_num))
    have h2 := gaussChannelResidueCurrent_mul_carrier_pos_of_leftHalf hm q hlt p
    exact (mul_pos h1 h2).le
  · have h1 : sourceZeroHorizontalTailLog q = 0 := by
      rw [sourceZeroHorizontalTailLog_closedForm, heq]
      norm_num
    rw [gaussHodgeMassCurrent, h1, zero_mul]
  · have h1 : sourceZeroHorizontalTailLog q < 0 := by
      rw [sourceZeroHorizontalTailLog_closedForm]
      exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num))
    have h2 := gaussChannelResidueCurrent_mul_carrier_neg_of_rightHalf hm q hgt p
    exact (mul_pos_of_neg_of_neg h1 h2).le

/-- Off the critical line the pairing is strictly positive at every label. -/
theorem gaussHodgeMassCurrent_pos_of_offLine {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) (p : Nat.Primes) :
    0 < gaussHodgeMassCurrent m q p := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · have h1 : 0 < sourceZeroHorizontalTailLog q := by
      rw [sourceZeroHorizontalTailLog_closedForm]
      exact mul_pos (by linarith) (Real.log_pos (by norm_num))
    exact mul_pos h1 (gaussChannelResidueCurrent_mul_carrier_pos_of_leftHalf hm q hlt p)
  · have h1 : sourceZeroHorizontalTailLog q < 0 := by
      rw [sourceZeroHorizontalTailLog_closedForm]
      exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num))
    exact mul_pos_of_neg_of_neg h1
      (gaussChannelResidueCurrent_mul_carrier_neg_of_rightHalf hm q hgt p)

/-- **Exact critical radical.**  The pairing vanishes at a label exactly on the critical line. -/
theorem gaussHodgeMassCurrent_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    by_contra hoff
    exact absurd h (gaussHodgeMassCurrent_pos_of_offLine hm q hoff p).ne'
  · intro h
    have h1 : sourceZeroHorizontalTailLog q = 0 := by
      rw [sourceZeroHorizontalTailLog_closedForm, h]
      norm_num
    rw [gaussHodgeMassCurrent, h1, zero_mul]

/-- **Reflection evenness.**  The pairing of the two odd components is even: both reflection
orientations enter, and the pairing is blind to neither yet flipped by neither. -/
theorem gaussHodgeMassCurrent_reflection (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m (xiZeroCopyLineConjEquiv q) p = gaussHodgeMassCurrent m q p := by
  rw [gaussHodgeMassCurrent, gaussHodgeMassCurrent,
    sourceZeroHorizontalTailLog_reflection 0 q,
    sourceZeroHorizontalPrimeCarrier_reflection]
  ring

/-! ## The hyperbolic closed form -/

/-- The generic hyperbolic mass shape at label size `s` and rate `t`. -/
def hodgeMassShape (s t : ℝ) : ℝ :=
  t * (s ^ t - s ^ (-t))

/-- **Boost-square law.**  In closed form the Hodge mass current is the hyperbolic mass shell of
the centered rate, weighted by the assembled residue current and the occupancy Fisher density. -/
theorem gaussHodgeMassCurrent_eq_boost_square (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p
      = Real.log 2 / 2 * gaussChannelResidueCurrent m p *
          primeActivationOccupancyFisherDensity p *
          hodgeMassShape (p.1 : ℝ) (primeDepthBVWoldXiCenteredRate q.1) := by
  have htail : sourceZeroHorizontalTailLog q
      = -(primeDepthBVWoldXiCenteredRate q.1 / 2) * Real.log 2 := by
    rw [sourceZeroHorizontalTailLog_closedForm, primeDepthBVWoldXiCenteredRate]
    ring
  rw [gaussHodgeMassCurrent, htail, sourceZeroHorizontalPrimeCarrier,
    primeGammaCofinalBocksteinCoefficient, primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist, hodgeMassShape]
  ring

/-- **The Hodge-index application is exactly RH.**  Zero total mass of the unconditionally
nonnegative current — every copy at the bottom of the mass shell — is the Riemann hypothesis. -/
theorem gaussHodgeMass_vanishing_iff_riemannHypothesis {m : ℕ} (hm : 1 ≤ m) :
    (∀ (q : XiZeroCopy) (p : Nat.Primes), gaussHodgeMassCurrent m q p = 0) ↔
      RiemannHypothesis := by
  rw [← sourceZeroHorizontalCarrierVanishes_iff_riemannHypothesis 0]
  constructor
  · intro h
    funext q
    apply (sourceZeroHorizontalCarrierAt_eq_zero_iff 0 q).2
    exact (gaussHodgeMassCurrent_eq_zero_iff hm q ⟨2, Nat.prime_two⟩).1
      (h q ⟨2, Nat.prime_two⟩)
  · intro h q p
    apply (gaussHodgeMassCurrent_eq_zero_iff hm q p).2
    exact (sourceZeroHorizontalCarrierAt_eq_zero_iff 0 q).1 (congrFun h q)

/-! ## The interface firewall

The three structural laws of the pairing — nonnegativity, evenness, exact radical — are pure
interface algebra: they hold at every label size `s > 1` and every rate `t`, with no arithmetic
input.  Consequently they can never force the mass to vanish: an explicit reflection-closed
off-line configuration has strictly positive mass.  The mass-zero law for the actual Xi system
must therefore consume data beyond the pairing's interface — a global identity distinguishing
the actual divisor, not more local structure. -/

theorem hodgeMassShape_nonneg {s : ℝ} (hs : 1 < s) (t : ℝ) :
    0 ≤ hodgeMassShape s t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hlt : s ^ t < s ^ (-t) :=
      Real.rpow_lt_rpow_left_iff hs |>.mpr (by linarith)
    have : s ^ t - s ^ (-t) < 0 := by linarith
    exact (mul_pos_of_neg_of_neg ht this).le
  · rw [hodgeMassShape, ht]
    norm_num
  · have hlt : s ^ (-t) < s ^ t :=
      Real.rpow_lt_rpow_left_iff hs |>.mpr (by linarith)
    have : 0 < s ^ t - s ^ (-t) := by linarith
    exact (mul_pos ht this).le

theorem hodgeMassShape_pos {s : ℝ} (hs : 1 < s) {t : ℝ} (ht : t ≠ 0) :
    0 < hodgeMassShape s t := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hlt : s ^ t < s ^ (-t) :=
      Real.rpow_lt_rpow_left_iff hs |>.mpr (by linarith)
    have : s ^ t - s ^ (-t) < 0 := by linarith
    exact mul_pos_of_neg_of_neg h this
  · have hlt : s ^ (-t) < s ^ t :=
      Real.rpow_lt_rpow_left_iff hs |>.mpr (by linarith)
    have : 0 < s ^ t - s ^ (-t) := by linarith
    exact mul_pos h this

theorem hodgeMassShape_eq_zero_iff {s : ℝ} (hs : 1 < s) (t : ℝ) :
    hodgeMassShape s t = 0 ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact absurd h (hodgeMassShape_pos hs ht).ne'
  · intro h
    rw [hodgeMassShape, h]
    ring_nf

/-- The generic shape is reflection-even. -/
theorem hodgeMassShape_even (s t : ℝ) :
    hodgeMassShape s (-t) = hodgeMassShape s t := by
  rw [hodgeMassShape, hodgeMassShape, neg_neg]
  ring

/-- Zero total mass over any finite configuration is equivalent to every rate vanishing: the
interface can only ever *diagnose* an on-line configuration, never force one. -/
theorem sum_hodgeMassShape_eq_zero_iff {s : ℝ} (hs : 1 < s) (T : Finset ℝ) :
    (∑ t ∈ T, hodgeMassShape s t) = 0 ↔ ∀ t ∈ T, t = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hodgeMassShape_nonneg hs t)]
  constructor
  · intro h t ht
    exact (hodgeMassShape_eq_zero_iff hs t).1 (h t ht)
  · intro h t ht
    exact (hodgeMassShape_eq_zero_iff hs t).2 (h t ht)

/-- **The firewall.**  There is a reflection-closed configuration with strictly positive mass:
the pairing's interface laws — even together with closure under the divisor reflection — cannot
force the mass to vanish.  The mass-zero law must come from outside the interface. -/
theorem hodgeMass_interface_cannot_force_vanishing :
    ¬ ∀ T : Finset ℝ, (∀ t ∈ T, -t ∈ T) → (∑ t ∈ T, hodgeMassShape 2 t) = 0 := by
  classical
  intro h
  have hT : ∀ t ∈ ({(1 : ℝ) / 2, -(1 / 2)} : Finset ℝ), -t ∈
      ({(1 : ℝ) / 2, -(1 / 2)} : Finset ℝ) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
    rcases ht with h1 | h1
    · subst h1
      right
      norm_num
    · subst h1
      left
      norm_num
  have hzero := h ({(1 : ℝ) / 2, -(1 / 2)} : Finset ℝ) hT
  have hmem : ((1 : ℝ) / 2) ∈ ({(1 : ℝ) / 2, -(1 / 2)} : Finset ℝ) :=
    Finset.mem_insert_self _ _
  have := (sum_hodgeMassShape_eq_zero_iff (by norm_num : (1 : ℝ) < 2) _).1 hzero
    ((1 : ℝ) / 2) hmem
  norm_num at this

end

end RHTower
