import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# The divisor-lattice ladder and the sharp collapse level

The dyadic ladder `RHLadder k` is the restriction, along the cofinal chain `2^k`, of a family
indexed by the full divisibility lattice `(ℕ, ∣)`: `OrderLadder n` demands that every right-half
ξ-zero have vanishing order divisible by `n`.  The family is antitone in divisibility,
`OrderLadder 1` is trivial, and the lattice's top element `0` recovers RH itself: `0 ∣ ord`
forces `ord = 0`, i.e. no zero.  Moduli of unbounded size — no divisibility relations among them
required — already suffice for RH, since a fixed nonzero order admits only finitely many
divisors.

The second half proves the sharp dichotomy for the dyadic chain.  The truth set
`{k | RHLadder k}` is either all of `ℕ` (exactly RH) or the initial segment of levels up to
`sharpLevel`, the least 2-adic valuation of a right-half ξ-zero order; in the latter case the
ladder breaks for the first time at `sharpLevel + 1`.  Consequently RH is equivalent to
unboundedness — equivalently infinitude — of the set of true rungs.
-/

open Complex Set

namespace RHTower

/-! ## The divisor-lattice ladder -/

/-- The divisor-lattice ladder: every right-half ξ-zero has vanishing order divisible by `n`.
The dyadic ladder is the chain `RHLadder k = OrderLadder (2 ^ k)`; the lattice top `0` is RH. -/
def OrderLadder (n : ℕ) : Prop :=
  ∀ ρ ∈ rightHalf, xi ρ = 0 → ((n : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ

/-- The dyadic ladder is the divisor-lattice ladder along the chain `2 ^ k`. -/
theorem orderLadder_pow_two (k : ℕ) : OrderLadder (2 ^ k) ↔ RHLadder k := Iff.rfl

/-- The lattice bottom is trivial: every order is divisible by `1`. -/
theorem orderLadder_one : OrderLadder 1 := by
  intro ρ _ _
  simp

/-- **Divisibility antitonicity.** The ladder is antitone over the divisor lattice `(ℕ, ∣)`. -/
theorem orderLadder_of_dvd {m n : ℕ} (hmn : m ∣ n) (h : OrderLadder n) : OrderLadder m :=
  fun ρ hρ hzero => dvd_trans (Nat.cast_dvd_cast hmn) (h ρ hρ hzero)

/-- **The top of the divisor lattice is RH.**  Divisibility of every right-half order by `0`
says every such order vanishes — that is, ξ has no zero on `Re s > ½`. -/
theorem orderLadder_zero_iff_rh : OrderLadder 0 ↔ RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro h ρ hρ hzero
    have h0 := h ρ hρ hzero
    rw [Nat.cast_zero, zero_dvd_iff] at h0
    exact analyticOrderAt_ne_zero.mpr ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hzero⟩ h0
  · intro h ρ hρ hzero
    exact absurd hzero (h ρ hρ)

/-- RH holds iff the divisor-lattice ladder holds at every modulus. -/
theorem rh_iff_forall_orderLadder : RiemannHypothesis ↔ ∀ n, OrderLadder n := by
  constructor
  · intro hRH n
    exact orderLadder_of_dvd (dvd_zero n) (orderLadder_zero_iff_rh.mpr hRH)
  · intro h
    exact orderLadder_zero_iff_rh.mp (h 0)

/-- Divisibility of the order transferred to its finite `toNat` form, for a nonzero modulus. -/
theorem orderLadder_iff_toNat_dvd {n : ℕ} (hn : n ≠ 0) :
    OrderLadder n ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → n ∣ (analyticOrderAt xi ρ).toNat := by
  unfold OrderLadder
  refine forall₃_congr fun ρ _ _ => ?_
  have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  constructor
  · intro h
    rw [hcoe] at h
    exact natCast_dvd_natCast_of_enat hn h
  · intro h
    rw [hcoe]
    exact Nat.cast_dvd_cast h

/-- **Unbounded moduli suffice.**  If the divisor-lattice ladder holds at moduli of unbounded
size — with no divisibility relations among them — then RH holds: a fixed nonzero vanishing
order cannot be divisible by a number exceeding it. -/
theorem rh_of_orderLadder_unbounded (h : ∀ N, ∃ n, N ≤ n ∧ OrderLadder n) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  set m := (analyticOrderAt xi ρ).toNat with hm
  obtain ⟨n, hn, hlad⟩ := h (m + 1)
  have hne : n ≠ 0 := by omega
  have hdvd : n ∣ m := (orderLadder_iff_toNat_dvd hne).mp hlad ρ hρ hzero
  have hm0 : m ≠ 0 := xi_order_toNat_ne_zero hzero
  have hle : n ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  omega

/-! ## The sharp collapse level of the dyadic ladder -/

/-- The set of ladder heights (2-adic valuations of vanishing orders) attained by right-half
ξ-zeros.  Empty exactly when RH holds. -/
def ladderHeightSet : Set ℕ := ladderHeight '' {ρ | ρ ∈ rightHalf ∧ xi ρ = 0}

theorem ladderHeightSet_nonempty_iff_not_rh :
    ladderHeightSet.Nonempty ↔ ¬ RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · rintro ⟨h, ρ, ⟨hρ, hzero⟩, rfl⟩ hall
    exact hall ρ hρ hzero
  · intro h
    push Not at h
    obtain ⟨ρ, hρ, hzero⟩ := h
    exact ⟨ladderHeight ρ, ρ, ⟨hρ, hzero⟩, rfl⟩

/-- The sharp collapse level: the least 2-adic valuation of a right-half ξ-zero order (with the
`sInf` junk value `0` when RH holds and the height set is empty). -/
noncomputable def sharpLevel : ℕ := sInf ladderHeightSet

/-- **The rung criterion at the sharp level.**  If RH fails, rung `k` holds iff `k` is at most
the sharp level: the truth set of the dyadic ladder is exactly the initial segment
`{k | k ≤ sharpLevel}`. -/
theorem rhLadder_iff_le_sharpLevel (h : ¬ RiemannHypothesis) (k : ℕ) :
    RHLadder k ↔ k ≤ sharpLevel := by
  have hne : ladderHeightSet.Nonempty := ladderHeightSet_nonempty_iff_not_rh.mpr h
  constructor
  · intro hlad
    obtain ⟨ρ, ⟨hρ, hzero⟩, hval⟩ := Nat.sInf_mem hne
    rw [rhLadder_iff_ladderHeight_ge] at hlad
    calc k ≤ ladderHeight ρ := hlad ρ hρ hzero
      _ = sharpLevel := hval
  · intro hk
    rw [rhLadder_iff_ladderHeight_ge]
    intro ρ hρ hzero
    have hmem : ladderHeight ρ ∈ ladderHeightSet := ⟨ρ, ⟨hρ, hzero⟩, rfl⟩
    calc k ≤ sharpLevel := hk
      _ ≤ ladderHeight ρ := Nat.sInf_le hmem

/-- If RH fails, the ladder breaks for the first time exactly at `sharpLevel + 1`. -/
theorem not_rhLadder_succ_sharpLevel (h : ¬ RiemannHypothesis) :
    ¬ RHLadder (sharpLevel + 1) := by
  rw [rhLadder_iff_le_sharpLevel h]
  omega

/-- **The sharp dichotomy.**  Either RH — every rung holds — or the truth set of the dyadic
ladder is the finite initial segment of levels up to `sharpLevel`. -/
theorem forall_rhLadder_or_sharp :
    (∀ k, RHLadder k) ∨ ∀ k, (RHLadder k ↔ k ≤ sharpLevel) := by
  by_cases h : RiemannHypothesis
  · exact Or.inl (rh_iff_forall_ladder.mp h)
  · exact Or.inr (rhLadder_iff_le_sharpLevel h)

/-- Failure of RH is exactly the existence of a finite breaking level for the ladder. -/
theorem not_rh_iff_exists_sharp :
    ¬ RiemannHypothesis ↔ ∃ H, ∀ k, (RHLadder k ↔ k ≤ H) := by
  constructor
  · intro h
    exact ⟨sharpLevel, rhLadder_iff_le_sharpLevel h⟩
  · rintro ⟨H, hH⟩ hRH
    have := (hH (H + 1)).mp ((rh_iff_forall_ladder.mp hRH) (H + 1))
    omega

/-- **RH ⟺ the true rungs are unbounded** — the cofinal criterion upgraded to an equivalence. -/
theorem rh_iff_rhLadder_unbounded :
    RiemannHypothesis ↔ ∀ N, ∃ k, N ≤ k ∧ RHLadder k := by
  constructor
  · intro hRH N
    exact ⟨N, le_refl N, (rh_iff_forall_ladder.mp hRH) N⟩
  · exact rh_of_rhLadder_cofinal

/-- **RH ⟺ infinitely many rungs hold.**  With the sharp dichotomy the cofinal criterion
becomes pure cardinality: the truth set of the ladder is `ℕ` or a finite initial segment, so RH
is exactly its infinitude. -/
theorem rh_iff_setOf_rhLadder_infinite :
    RiemannHypothesis ↔ {k | RHLadder k}.Infinite := by
  constructor
  · intro hRH
    have huniv : {k | RHLadder k} = Set.univ := by
      ext k
      simp [(rh_iff_forall_ladder.mp hRH) k]
    rw [huniv]
    exact Set.infinite_univ
  · intro hinf
    by_contra h
    have hsub : {k | RHLadder k} ⊆ Set.Iic sharpLevel := fun k hk =>
      (rhLadder_iff_le_sharpLevel h k).mp hk
    exact hinf ((Set.finite_Iic sharpLevel).subset hsub)

end RHTower
