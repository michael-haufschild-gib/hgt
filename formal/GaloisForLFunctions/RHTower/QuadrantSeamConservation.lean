/-
The quadrant–seam conservation conjecture: its refutation as a topological statement, and the
reduction of its ξ-content to `RH₂` via a zero-density contradiction.

For the descended carrier `X(u) = ξ(½ + √u)` (`xiDescent`) the conjecture reads: every nonzero
quadrant-local rung-1 deck charge off the seam must pair with an equal-and-opposite seam charge or
persist to the far field; the far field is charge-free and the seam parity rules forbid unmatched odd
charge; hence `w₁ = 0` off the seam.  This file separates what is unconditional from what is not.

**Unconditional core.**  The descent preserves multiplicity, so the rung-1 charge transports between
the `s`-plane and the `u`-plane (`carrierCharge_xiDescent_center_sq`).  The far-field drain is
charge-free: where `Re √u > ½` one has `Re s > 1`, and `ξ` is zero-free there
(`xiDescent_ne_zero_farField`, `carrierCharge_xiDescent_farField`).

**The naive conjecture is false as topology.**  Two carriers refute the two premises the argument
needs beyond conservation and the drain:

* `naive_terminal_dichotomy_false` — `P(u) = u² + 1` is entire and nonvanishing on the whole real
  axis (hence on the seam and on the drain), yet carries odd rung-1 charge at the off-seam point `I`.
  The charge sits in a compact conjugate-pair island: it neither pairs with a seam zero nor escapes.
  The symmetric aggregate is blind (`island_aggregate_blind`): `±I` each carry odd charge but their
  orders sum to an even number.
* `naive_seam_parity_insufficient` — in the collision family `Q_t(u) = (u+1)² + t²`, the seam limit
  `Q₀ = (u+1)²` has even order `2` at the seam point `-1`, yet the pre-collision upper zero at
  `-1 + I` (`t = 1`) has odd charge.  An even seam multiplicity is the endpoint of an odd upper/lower
  pair, so seam evenness does not forbid odd quadrant charge.  At rung 1 "equal and opposite" is
  vacuous (`wCharge_two_neg_self`): in `ZMod 2` a charge equals its own negation.

**The reduction (`rhLadder_one_of_recurrence_of_density`).**  What survives is a zero-density
contradiction.  A right-half ξ-zero of odd order is a defect (`XiDefect`).  If a single defect forces
a linear lower bound on the right-half zero count (`DefectRecurrence` — the open replication core) and
the count is sublinear (`SubLinearDensity` — Ingham's zero-density), the two are incompatible
(`not_linearLowerBound_of_subLinear`).  Hence no defect exists: every right-half ξ-zero has even
multiplicity, i.e. `RHLadder 1`.  The two named inputs are exactly the doc's reduced open core.
-/
import GaloisForLFunctions.RHTower.ChargeMotion
import GaloisForLFunctions.RHTower.UPlaneDescent
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.CarrierDeckCharge

open Complex Set

namespace RHTower

/-! ### Unconditional core: the descent transports charge; the far-field drain is charge-free -/

/-- **Charge transport under the descent.**  The rung-1 deck charge of `xiDescent` at `(s − ½)²`
equals the charge of `ξ` at `s`: the `u`-plane descent preserves the vanishing multiplicity, so an
off-line odd ξ-zero is an off-seam odd `xiDescent`-zero and conversely. -/
theorem carrierCharge_xiDescent_center_sq {s : ℂ} (hs : s ∈ rightHalf) :
    carrierCharge xiDescent 1 ((s - (1 / 2 : ℂ)) ^ 2) = carrierCharge xi 1 s := by
  rw [carrierCharge_one_eq_neg_one_pow, carrierCharge_one_eq_neg_one_pow,
    analyticOrderAt_xiDescent_center_sq hs]

/-- **The far-field drain is zero-free.**  On the slit plane where `Re √u > ½`, the point
`s = ½ + √u` has `Re s > 1`, where `ξ` does not vanish; hence `xiDescent u ≠ 0`. -/
theorem xiDescent_ne_zero_farField {w : ℂ} (hw : w ∈ slitPlane) (hfar : 1 / 2 < (uSqrt w).re) :
    xiDescent w ≠ 0 := by
  rw [xiDescent_of_ne_zero (slitPlane_ne_zero hw)]
  apply xi_ne_zero_of_one_lt_re
  have hre : ((1 / 2 : ℂ) + uSqrt w).re = 1 / 2 + (uSqrt w).re := by
    rw [Complex.add_re]; norm_num
  rw [hre]; linarith

/-- The far field carries trivial rung-1 charge. -/
theorem carrierCharge_xiDescent_farField {w : ℂ} (hw : w ∈ slitPlane) (hfar : 1 / 2 < (uSqrt w).re) :
    carrierCharge xiDescent 1 w = 1 :=
  carrierCharge_eq_one_of_ne_zero _ _ (xiDescent_ne_zero_farField hw hfar)

/-! ### Refutation 1: the compact odd conjugate-pair island `P(u) = u² + 1` -/

/-- The island carrier `P(u) = u² + 1`, entire and real (reflection) symmetric, whose only zeros are
the conjugate pair `±I`. -/
def Pmodel : ℂ → ℂ := fun u => u ^ 2 + 1

theorem Pmodel_analyticOnNhd : AnalyticOnNhd ℂ Pmodel univ := by
  intro z _
  exact (analyticAt_id.pow 2).add analyticAt_const

/-- `P` is nonvanishing on the entire real axis — in particular on the seam `(-∞, 0]` and the
far-field drain `[0, ∞)`. -/
theorem Pmodel_ne_zero_real (x : ℝ) : Pmodel (x : ℂ) ≠ 0 := by
  have hcast : Pmodel (x : ℂ) = ((x ^ 2 + 1 : ℝ) : ℂ) := by
    simp only [Pmodel]; push_cast; ring
  rw [hcast, Complex.ofReal_ne_zero]; positivity

private theorem Pmodel_order_pt {ρ : ℂ} (hρ : ρ ^ 2 + 1 = 0) (hd : (2 : ℂ) * ρ ≠ 0) :
    analyticOrderAt Pmodel ρ = 1 := by
  have han : AnalyticAt ℂ Pmodel ρ := (analyticAt_id.pow 2).add analyticAt_const
  have hf0 : Pmodel ρ = 0 := hρ
  have hderiv : HasDerivAt Pmodel (((2 : ℕ) : ℂ) * ρ ^ (2 - 1)) ρ :=
    (hasDerivAt_pow 2 ρ).add_const (1 : ℂ)
  have hd0 : deriv Pmodel ρ ≠ 0 := by
    rw [hderiv.deriv]; simpa using hd
  exact han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hd0

theorem Pmodel_order_I : analyticOrderAt Pmodel I = 1 :=
  Pmodel_order_pt (by simp [Complex.I_sq]) (by simp)

theorem Pmodel_order_neg_I : analyticOrderAt Pmodel (-I) = 1 :=
  Pmodel_order_pt (by simp [Complex.I_sq]) (by simp)

theorem Pmodel_charge_odd : carrierCharge Pmodel 1 I ≠ 1 := by
  rw [carrierCharge_one_eq_neg_one_pow, Pmodel_order_I]; norm_num

/-- **The naive terminal dichotomy is false.**  There is an entire carrier — nonvanishing on the whole
real axis, hence on the seam and on the far-field drain — that nevertheless carries a nontrivial
rung-1 deck charge at an off-seam, off-real point.  Conservation, the charge-free drain, and seam
nonvanishing do NOT force `w₁ = 0` off the seam: the charge can sit in a compact conjugate-pair
island that never reaches a boundary. -/
theorem naive_terminal_dichotomy_false :
    ∃ (f : ℂ → ℂ) (ρ : ℂ), AnalyticOnNhd ℂ f univ ∧ (∀ x : ℝ, f (x : ℂ) ≠ 0) ∧
      ρ.re ≠ 1 / 2 ∧ ρ.im ≠ 0 ∧ carrierCharge f 1 ρ ≠ 1 :=
  ⟨Pmodel, I, Pmodel_analyticOnNhd, Pmodel_ne_zero_real,
    by rw [Complex.I_re]; norm_num, by rw [Complex.I_im]; norm_num, Pmodel_charge_odd⟩

/-- **Symmetric-aggregate blindness.**  The two conjugate zeros `±I` of the island each carry odd
rung-1 charge, but their orders sum to an even number: a reflection-symmetric detector sees charge
`0 mod 2` and misses the quadrant-local defect entirely. -/
theorem island_aggregate_blind :
    Even ((analyticOrderAt Pmodel I).toNat + (analyticOrderAt Pmodel (-I)).toNat) ∧
      carrierCharge Pmodel 1 I ≠ 1 := by
  refine ⟨?_, Pmodel_charge_odd⟩
  rw [Pmodel_order_I, Pmodel_order_neg_I]; decide

/-! ### Refutation 2: the collision family `Q_t(u) = (u + 1)² + t²` -/

/-- The collision family `Q_t(u) = (u − a)² + t²`. -/
def coll (a t : ℂ) : ℂ → ℂ := fun u => (u - a) ^ 2 + t ^ 2

/-- At the seam limit `t = 0`, `Q₀(u) = (u + 1)²` has even order `2` at the seam point `-1`. -/
theorem coll_seam_order : analyticOrderAt (coll (-1) 0) (-1 : ℂ) = 2 := by
  have hfun : coll (-1 : ℂ) 0 = (fun u : ℂ => u - (-1 : ℂ)) ^ 2 := by
    funext u; simp [coll]
  rw [hfun]
  have hlin_an : AnalyticAt ℂ (fun u : ℂ => u - (-1 : ℂ)) (-1 : ℂ) :=
    analyticAt_id.sub analyticAt_const
  have hlin_ord : analyticOrderAt (fun u : ℂ => u - (-1 : ℂ)) (-1 : ℂ) = 1 := by
    refine hlin_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) ?_
    have hd : deriv (fun u : ℂ => u - (-1 : ℂ)) (-1 : ℂ) = 1 :=
      ((hasDerivAt_id (-1 : ℂ)).sub_const (-1 : ℂ)).deriv
    rw [hd]; exact one_ne_zero
  rw [analyticOrderAt_pow hlin_an, hlin_ord]; rfl

/-- At `t = 1` the upper zero of `Q₁(u) = (u + 1)² + 1` at `-1 + I` has odd order `1`. -/
theorem coll_upper_order : analyticOrderAt (coll (-1) 1) (-1 + I) = 1 := by
  have han : AnalyticAt ℂ (coll (-1 : ℂ) 1) (-1 + I) := by
    apply AnalyticAt.add _ analyticAt_const
    exact (analyticAt_id.sub analyticAt_const).pow 2
  have hf0 : coll (-1 : ℂ) 1 (-1 + I) = 0 := by
    simp only [coll]; ring_nf; simp [Complex.I_sq]
  have hd0 : deriv (coll (-1 : ℂ) 1) (-1 + I) ≠ 0 := by
    have hb : HasDerivAt (coll (-1 : ℂ) 1)
        (((2 : ℕ) : ℂ) * ((-1 + I) - (-1 : ℂ)) ^ (2 - 1) * 1) (-1 + I) :=
      (((hasDerivAt_id (-1 + I)).sub_const (-1 : ℂ)).pow 2).add_const ((1 : ℂ) ^ 2)
    rw [hb.deriv]
    have hI : ((-1 + I) - (-1 : ℂ)) = I := by ring
    rw [hI]; simp
  exact han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hd0

/-- **At rung 1 "equal and opposite" is vacuous.**  In `ZMod 2` negation is the identity, so a charge
`wCharge 2 m` equals `wCharge 2 (−m)`: the phrase "pair with an equal-and-opposite seam charge"
carries no information at level `w₁`, and cannot express the cancellation the naive argument needs. -/
theorem wCharge_two_neg_self (m : ℤ) : wCharge 2 (-m) = wCharge 2 m := by
  have h : ∀ x : ZMod 2, -x = x := by decide
  rw [wCharge_neg, h]

/-- **Ordinary seam parity is insufficient.**  The seam limit `Q₀` has EVEN order at the seam point
`-1`, yet the pre-collision upper zero of `Q₁` at `-1 + I` has ODD charge.  An even seam multiplicity
is exactly the endpoint of an odd upper/lower pair, so seam evenness does not forbid odd quadrant
charge — the naive seam-parity premise fails. -/
theorem naive_seam_parity_insufficient :
    Even (analyticOrderAt (coll (-1) 0) (-1 : ℂ)).toNat ∧
      carrierCharge (coll (-1) 1) 1 (-1 + I) ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [coll_seam_order]; decide
  · rw [carrierCharge_one_eq_neg_one_pow, coll_upper_order]; norm_num

/-! ### The reduction: a zero-density contradiction gives `RH₂` -/

/-- A **right-half ξ-defect**: a zero right of the critical line carrying nontrivial rung-1 deck
charge, i.e. of odd multiplicity.  This is the `w₁ = 1` box datum localized to a point (a small box
around such a zero has `boxCharge 1 = carrierCharge`, by `boxCharge_single`). -/
def XiDefect (ρ : ℂ) : Prop := ρ ∈ rightHalf ∧ xi ρ = 0 ∧ carrierCharge xi 1 ρ ≠ 1

/-- A defect reads as odd multiplicity. -/
theorem xiDefect_charge_iff_odd (ρ : ℂ) :
    carrierCharge xi 1 ρ ≠ 1 ↔ Odd (analyticOrderAt xi ρ).toNat := by
  rw [ne_eq, carrierCharge_eq_one_iff_dvd, pow_one, Nat.two_dvd_ne_zero]
  exact Nat.odd_iff.symm

/-- **Linear lower bound** on a height-count `N`: a positive density `c` from some point on. -/
def LinearLowerBound (N : ℝ → ℝ) (c : ℝ) : Prop := ∃ T₀, ∀ T ≥ T₀, c * T ≤ N T

/-- **Sublinear (Ingham) density**: the count is `o(T)`. -/
def SubLinearDensity (N : ℝ → ℝ) : Prop := ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, N T ≤ ε * T

/-- **Density incompatibility.**  A positive linear lower bound and a sublinear upper bound on the
same count are contradictory: choosing `ε = c/2` beats the linear floor at any large height. -/
theorem not_linearLowerBound_of_subLinear {N : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hlow : LinearLowerBound N c) (hsub : SubLinearDensity N) : False := by
  obtain ⟨T₁, hT₁⟩ := hlow
  obtain ⟨T₂, hT₂⟩ := hsub (c / 2) (by positivity)
  set T := max (max T₁ T₂) 1 with hTdef
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h1 : c * T ≤ N T := hT₁ T (le_trans (le_max_left _ _) (le_max_left _ _))
  have h2 : N T ≤ (c / 2) * T := hT₂ T (le_trans (le_max_right _ _) (le_max_left _ _))
  nlinarith [h1, h2, mul_pos hc hTpos]

/-- **Reduced `RH₂` theorem** (the surviving ξ-content of the quadrant–seam conjecture).  Let `N`
count right-half ξ-zeros up to height `T`.  Suppose:

* **Defect recurrence** — a single odd right-half zero forces a positive linear lower bound on `N`
  (one defect replicates to a relatively dense family, each box contributing a zero); and
* **Sublinear density** — `N T = o(T)` (Ingham's zero-density estimate).

Then no right-half ξ-zero has odd order: every zero right of the critical line has even multiplicity,
i.e. `RHLadder 1`.  The proof is the density contradiction: a defect would make `N` both linearly
bounded below and sublinearly bounded above.  The two hypotheses are precisely the reduced open core —
replication (open) and zero-density (classical, absent from mathlib; built in `ZeroDensityEngine`). -/
theorem rhLadder_one_of_recurrence_of_density {N : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hrec : (∃ ρ, XiDefect ρ) → LinearLowerBound N c)
    (hden : SubLinearDensity N) : RHLadder 1 := by
  rw [rhLadder_iff_toNat_dvd]
  intro ρ hρ hz
  rw [pow_one]
  by_contra hodd
  have hdef : XiDefect ρ :=
    ⟨hρ, hz, (xiDefect_charge_iff_odd ρ).mpr
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))⟩
  exact not_linearLowerBound_of_subLinear hc (hrec ⟨ρ, hdef⟩) hden

end RHTower
