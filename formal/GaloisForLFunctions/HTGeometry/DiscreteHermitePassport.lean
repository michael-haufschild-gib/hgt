import GaloisForLFunctions.RHTower.ConnesLatticeFiniteSupport
import GaloisForLFunctions.HTGeometry.WeierstrassProductMultiplicity
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization

/-!
# Entire functions carrying arbitrary closed discrete Hermite passports

Every closed discrete subset of `ℂ` is countable and locally finite.  We encode each nonzero site
at its canonical natural-number code, reserve exactly the prescribed finite block of pair indices,
and fill all other indices by the escaping positive-integer sequence.  The resulting zero sequence
is nonzero and tends to infinity even when the passport is finite or has unbounded multiplicities.
A power of `z` separately carries the passport at zero.  Exact Weierstrass multiplicity then yields
an entire function whose analytic order dominates every prescribed order.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set

noncomputable section

def nonzeroPart (S : Set ℂ) : Set ℂ := S \ {0}

def discretePassportSeq (S : Set ℂ) (m : S → ℕ) [Encodable (nonzeroPart S)]
    (n : ℕ) : ℂ :=
  match Encodable.decode (α := nonzeroPart S) (Nat.unpair n).1 with
  | some a =>
      if Encodable.encode a = (Nat.unpair n).1 ∧
          (Nat.unpair n).2 < m ⟨a, a.2.1⟩ + 1 then a else ((n + 1 : ℕ) : ℂ)
  | none => ((n + 1 : ℕ) : ℂ)

theorem discretePassportSeq_pair (S : Set ℂ) (m : S → ℕ)
    [Encodable (nonzeroPart S)] (a : nonzeroPart S) (j : ℕ)
    (hj : j < m ⟨a, a.2.1⟩ + 1) :
    discretePassportSeq S m (Nat.pair (Encodable.encode a) j) = a := by
  simp [discretePassportSeq, Nat.unpair_pair, hj]

theorem discretePassportSeq_ne_zero (S : Set ℂ) (m : S → ℕ)
    [Encodable (nonzeroPart S)] (n : ℕ) : discretePassportSeq S m n ≠ 0 := by
  unfold discretePassportSeq
  generalize hopt : Encodable.decode (α := nonzeroPart S) (Nat.unpair n).1 = oa
  cases oa with
  | none =>
      change ((n + 1 : ℕ) : ℂ) ≠ 0
      exact_mod_cast Nat.succ_ne_zero n
  | some a =>
      change (if Encodable.encode a = (Nat.unpair n).1 ∧
          (Nat.unpair n).2 < m ⟨a, a.2.1⟩ + 1 then (a : ℂ)
        else ((n + 1 : ℕ) : ℂ)) ≠ 0
      split
      next => exact a.2.2
      next => exact_mod_cast Nat.succ_ne_zero n

theorem countable_of_isDiscrete_complex {S : Set ℂ} (hSd : IsDiscrete S) : S.Countable := by
  haveI : DiscreteTopology S := isDiscrete_iff_discreteTopology.mp hSd
  exact Set.countable_coe_iff.mp
    (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

theorem finite_bounded_nonzeroPart {S : Set ℂ} (hSd : IsDiscrete S) (hSc : IsClosed S)
    (R : ℝ) : {a : nonzeroPart S | ‖(a : ℂ)‖ < R}.Finite := by
  let B : Set (nonzeroPart S) := {a | ‖(a : ℂ)‖ < R}
  have hambient : (S ∩ Metric.closedBall 0 (max R 0)).Finite :=
    RHTower.connes_discrete_inter_compact_finite hSd hSc
      (ProperSpace.isCompact_closedBall 0 (max R 0))
  have himage : ((fun a : nonzeroPart S => (a : ℂ)) '' B).Finite := by
    refine hambient.subset ?_
    rintro z ⟨a, ha, rfl⟩
    refine ⟨a.2.1, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (le_of_lt ha) (le_max_left _ _)
  exact Set.Finite.of_finite_image himage (Set.injOn_of_injective Subtype.val_injective)

def prescribedPairIndices (S : Set ℂ) (m : S → ℕ) [Encodable (nonzeroPart S)]
    (B : Set (nonzeroPart S)) : Set ℕ :=
  ⋃ a ∈ B, (fun j : ℕ => Nat.pair (Encodable.encode a) j) '' {j | j < m ⟨a, a.2.1⟩ + 1}

theorem finite_prescribedPairIndices (S : Set ℂ) (m : S → ℕ)
    [Encodable (nonzeroPart S)] {B : Set (nonzeroPart S)} (hB : B.Finite) :
    (prescribedPairIndices S m B).Finite := by
  rw [prescribedPairIndices]
  exact hB.biUnion fun a _ =>
    (Set.finite_lt_nat (m ⟨a, a.2.1⟩ + 1)).image _

theorem tendsto_norm_discretePassportSeq {S : Set ℂ} (hSd : IsDiscrete S)
    (hSc : IsClosed S) (m : S → ℕ) [Encodable (nonzeroPart S)] :
    Tendsto (fun n => ‖discretePassportSeq S m n‖) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro R
  let B : Set (nonzeroPart S) := {a | ‖(a : ℂ)‖ < R}
  have hB : B.Finite := finite_bounded_nonzeroPart hSd hSc R
  let F : Set ℕ := prescribedPairIndices S m B
  have hF : F.Finite := finite_prescribedPairIndices S m hB
  obtain ⟨N₀, hN₀⟩ := hF.exists_le
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, R ≤ (N₁ : ℝ) := exists_nat_ge R
  refine ⟨max (N₀ + 1) N₁, fun n hn => ?_⟩
  have hnF : n ∉ F := by
    intro hnmem
    have := hN₀ n hnmem
    omega
  rw [discretePassportSeq]
  split
  next a hdecode =>
    split
    next hj =>
      by_contra hlt
      have haB : a ∈ B := by
        exact lt_of_not_ge hlt
      apply hnF
      change n ∈ prescribedPairIndices S m B
      rw [prescribedPairIndices]
      refine Set.mem_iUnion₂.2 ⟨a, haB, ?_⟩
      refine ⟨(Nat.unpair n).2, ?_, ?_⟩
      · exact hj.2
      · simp [hj.1]
    next =>
      rw [Complex.norm_natCast]
      exact le_trans hN₁ (Nat.cast_le.2
        (le_trans (le_trans (le_max_right _ _) hn) (Nat.le_succ n)))
  next =>
    rw [Complex.norm_natCast]
    exact le_trans hN₁ (Nat.cast_le.2
      (le_trans (le_trans (le_max_right _ _) hn) (Nat.le_succ n)))

theorem zeroMultiplicity_discretePassportSeq_ge {S : Set ℂ} (m : S → ℕ)
    [Encodable (nonzeroPart S)] (a : S) (ha : (a : ℂ) ≠ 0)
    (htend : Tendsto (fun n => ‖discretePassportSeq S m n‖) atTop atTop) :
    m a + 1 ≤ zeroMultiplicity (discretePassportSeq S m) a := by
  let a₀ : nonzeroPart S := ⟨a, a.2, ha⟩
  let f : Fin (m a + 1) → ℕ := fun j => Nat.pair (Encodable.encode a₀) j
  have hf : Function.Injective f := by
    intro j k hjk
    have hu := congrArg Nat.unpair hjk
    exact Fin.ext (by simpa [f] using congrArg Prod.snd hu)
  have hrange : Set.range f ⊆ {n : ℕ | discretePassportSeq S m n = a} := by
    rintro n ⟨j, rfl⟩
    change discretePassportSeq S m (Nat.pair (Encodable.encode a₀) j) = (a : ℂ)
    simpa [a₀] using discretePassportSeq_pair S m a₀ j j.2
  have hzeroFin : {n : ℕ | discretePassportSeq S m n = (a : ℂ)}.Finite :=
    finite_zeroIndices htend a
  calc
    m a + 1 = Nat.card (Fin (m a + 1)) := (Nat.card_fin _).symm
    _ = (Set.range f).ncard := (Set.ncard_range_of_injective hf).symm
    _ ≤ {n : ℕ | discretePassportSeq S m n = (a : ℂ)}.ncard :=
      Set.ncard_le_ncard hrange hzeroFin
    _ = zeroMultiplicity (discretePassportSeq S m) a := rfl

theorem exists_entire_prescribed_discrete_vanishing_nontrivial {S : Set ℂ}
    (hSd : IsDiscrete S) (hSc : IsClosed S) (m : S → ℕ) :
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
      (∃ z, W z ≠ 0) ∧
      ∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt W a := by
  classical
  have hcount : (nonzeroPart S).Countable :=
    (countable_of_isDiscrete_complex hSd).mono sdiff_subset
  letI : Encodable (nonzeroPart S) := hcount.toEncodable
  let seq : ℕ → ℂ := discretePassportSeq S m
  have htend : Tendsto (fun n => ‖seq n‖) atTop atTop :=
    tendsto_norm_discretePassportSeq hSd hSc m
  have hsne : ∀ n, seq n ≠ 0 := discretePassportSeq_ne_zero S m
  let P : ℂ → ℂ := weierstrassGenusProduct seq
  have hPdiff : Differentiable ℂ P := differentiable_weierstrassGenusProduct htend hsne
  let M : ℕ := if h0 : 0 ∈ S then m ⟨0, h0⟩ + 1 else 0
  let W : ℂ → ℂ := fun z => (z - 0) ^ M * P z
  have hWdiff : Differentiable ℂ W := by
    dsimp [W]
    fun_prop
  let augmentedSeq : ℕ → ℂ := fun n => if n = 0 then 0 else seq (n - 1)
  obtain ⟨z₀, hz₀⟩ := exists_notMem_range augmentedSeq
  have hz₀ne : z₀ ≠ 0 := by
    intro hz
    apply hz₀
    refine ⟨0, ?_⟩
    simp [augmentedSeq, hz]
  have hz₀seq : ∀ n, z₀ ≠ seq n := by
    intro n heq
    apply hz₀
    refine ⟨n + 1, ?_⟩
    simp [augmentedSeq, heq]
  have hPz₀ : P z₀ ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff htend hsne z₀).mp h
    exact hz₀seq n hn
  have hWz₀ : W z₀ ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero M (sub_ne_zero.mpr hz₀ne)) hPz₀
  refine ⟨W, hWdiff, ⟨z₀, hWz₀⟩, fun a => ?_⟩
  by_cases ha0 : (a : ℂ) = 0
  · have h0 : (0 : ℂ) ∈ S := ha0 ▸ a.2
    have hae : a = ⟨0, h0⟩ := Subtype.ext ha0
    subst a
    have hP0 : P 0 ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff htend hsne 0).mp h
      exact hsne n hn.symm
    dsimp only [W]
    change (m ⟨0, h0⟩ + 1 : ℕ∞) ≤
      analyticOrderAt ((fun z : ℂ => (z - 0) ^ M) * P) 0
    rw [analyticOrderAt_mul (HTGeometry.analyticAt_sub_pow 0 M 0) (hPdiff.analyticAt 0),
      HTGeometry.analyticOrderAt_sub_pow_self,
      (hPdiff.analyticAt 0).analyticOrderAt_eq_zero.mpr hP0, add_zero]
    simp [M, h0]
  · dsimp only [W]
    change (m a + 1 : ℕ∞) ≤
      analyticOrderAt ((fun z : ℂ => (z - 0) ^ M) * P) a
    rw [analyticOrderAt_mul (HTGeometry.analyticAt_sub_pow 0 M a) (hPdiff.analyticAt a),
      HTGeometry.analyticOrderAt_sub_pow_of_ne 0 M ha0,
      analyticOrderAt_weierstrassGenusProduct htend hsne, zero_add]
    exact_mod_cast zeroMultiplicity_discretePassportSeq_ge m a ha0 htend

/-- Every closed discrete multiplicity passport is carried by a nonzero entire function. -/
theorem exists_entire_prescribed_discrete_vanishing {S : Set ℂ}
    (hSd : IsDiscrete S) (hSc : IsClosed S) (m : S → ℕ) :
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
      ∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt W a := by
  obtain ⟨W, hW, _, horder⟩ :=
    exists_entire_prescribed_discrete_vanishing_nontrivial hSd hSc m
  exact ⟨W, hW, horder⟩

end

end GaloisForLFunctions
