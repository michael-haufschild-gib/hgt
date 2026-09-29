import GaloisForLFunctions.HTGeometry.TwoLocalPauliSpectralJetLaw
import GaloisForLFunctions.HTGeometry.SpectralCharacterReplicaHeightLaw
import GaloisForLFunctions.HTGeometry.OrderedReplicaPushforward

/-!
# Replica-sensitive depth of full two-local Pauli spectral jets

A nonzero integer character realized by `r` forward and `r` backward
spectral labels is detected by a genuine derivative of the full weight-two
Pauli family of order at most `min (n + 1) (Nat.log 2 r + 2)`.
The zero character, including the order-zero case, is retained explicitly.

The arithmetic mechanism is the minimum-volume Boolean-trade bound:
the first surviving Walsh coefficient of degree `d` is divisible by `2^d`,
whereas replica mass bounds its magnitude by `2*r`. The minimum-volume
mechanism is classical; see Ghorbani, Kamali, Khosrovshahi and Krotov,
*On the volumes and affine types of trades*, arXiv:1810.02296.

For each fixed system size and replica order, the detectors persist on one
full-dimensional neighborhood of actual real characteristic roots. Each
detector is selected before the source point. The radius is existential:
no growing-order radius bound, quenched incidence-action estimate, circuit
exclusion, or first-return law follows from these statements alone.
-/

open scoped BigOperators Topology Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry
noncomputable section

noncomputable local instance replicaDepthBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

private theorem sum_subsets_bool_sign {I : Type*} [DecidableEq I]
    (B : Finset I) (x : I → Bool) :
    (∑ A ∈ B.powerset, ∏ j ∈ A, if x j then (-1 : ℤ) else 1) =
      if (∀ j ∈ B, x j = false) then (2 : ℤ) ^ B.card else 0 := by
  classical
  rw [← Finset.prod_one_add]
  by_cases hx : ∀ j ∈ B, x j = false
  · rw [if_pos hx]
    calc
      _ = ∏ _j ∈ B, (2 : ℤ) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hx j hj]
        norm_num
      _ = _ := Finset.prod_const _
  · rw [if_neg hx]
    push Not at hx
    obtain ⟨j, hj, hxj⟩ := hx
    apply Finset.prod_eq_zero hj
    cases h : x j with
    | false => exact (hxj h).elim
    | true => norm_num

/-- A Walsh subcube sum is an integer marginal times its exact power of two. -/
theorem integerStarWalshPacket_subcube_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (k : (I → Bool) → ℤ) (B : Finset I) :
    (∑ A ∈ B.powerset, integerStarWalshPacket k A) =
      (2 : ℤ) ^ B.card * ∑ x, if (∀ j ∈ B, x j = false) then k x else 0 := by
  classical
  unfold integerStarWalshPacket
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_subsets_bool_sign]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ j ∈ B, x j = false
  · simp only [if_pos hx]
    exact mul_comm _ _
  · simp only [if_neg hx, mul_zero]

/-- Vanishing proper submodes forces divisibility of the first surviving mode. -/
theorem integerStarWalshPacket_dvd_of_proper_subsets_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (k : (I → Bool) → ℤ) (B : Finset I)
    (hzero : ∀ A : Finset I, A ⊂ B → integerStarWalshPacket k A = 0) :
    (2 : ℤ) ^ B.card ∣ integerStarWalshPacket k B := by
  classical
  have hsum : (∑ A ∈ B.powerset, integerStarWalshPacket k A) =
      integerStarWalshPacket k B := by
    apply Finset.sum_eq_single B
    · intro A hA hne
      exact hzero A (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hA, hne⟩)
    · intro hnot
      exact (hnot (Finset.mem_powerset.mpr (fun _ hx => hx))).elim
  have h := integerStarWalshPacket_subcube_sum k B
  rw [hsum] at h
  exact ⟨_, h⟩

/-- Every nonzero integer packet has a first mode whose magnitude is at least
the power of two of its degree. This is the Boolean-trade minimum-mass mechanism. -/
theorem exists_integerStarWalshPacket_degree_mass
    {I : Type*} [Fintype I] [DecidableEq I]
    (k : (I → Bool) → ℤ) (hk : k ≠ 0) :
    ∃ B : Finset I, integerStarWalshPacket k B ≠ 0 ∧
      (∀ A : Finset I, A.card < B.card → integerStarWalshPacket k A = 0) ∧
      2 ^ B.card ≤ (integerStarWalshPacket k B).natAbs := by
  classical
  let modes : Finset (Finset I) := Finset.univ.filter fun B => integerStarWalshPacket k B ≠ 0
  obtain ⟨A, hA⟩ := exists_integerStarWalshPacket_ne_zero k hk
  have hmodes : modes.Nonempty := ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩⟩
  obtain ⟨B, hB, hmin⟩ := modes.exists_min_image Finset.card hmodes
  have hBne := (Finset.mem_filter.mp hB).2
  have hzero (A : Finset I) (hcard : A.card < B.card) : integerStarWalshPacket k A = 0 := by
    by_contra hne
    exact (not_le_of_gt hcard) (hmin A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩))
  have hdiv := integerStarWalshPacket_dvd_of_proper_subsets_zero k B
    (fun A hA => hzero A (Finset.card_lt_card hA))
  refine ⟨B, hBne, hzero, ?_⟩
  simpa only [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl] using
    Int.natAbs_le_of_dvd_ne_zero hdiv hBne

/-- A realizable order-r character has no Walsh coefficient larger than 2r. -/
theorem integerStarWalshPacket_le_replica_mass
    {I : Type*} [Fintype I] [DecidableEq I]
    {r : ℕ} {k : (I → Bool) → ℤ}
    (hk : SpectralCharacterReplicaRealizes r k) (B : Finset I) :
    (integerStarWalshPacket k B).natAbs ≤ 2 * r := by
  obtain ⟨p, q, hp, hq, hk⟩ := hk
  have hsign (x : I → Bool) : |∏ j ∈ B, if x j then (-1 : ℤ) else 1| = 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_eq_one
    intro j _
    cases x j <;> norm_num
  have hbound : |integerStarWalshPacket k B| ≤ (2 * r : ℕ) := by
    calc
      _ ≤ ∑ x, |k x * ∏ j ∈ B, if x j then (-1 : ℤ) else 1| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, |k x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [abs_mul, hsign, mul_one]
      _ ≤ ∑ x, ((p x : ℤ) + (q x : ℤ)) := by
        apply Finset.sum_le_sum
        intro x _
        rw [hk]
        simpa only [sub_zero, zero_sub, abs_neg,
          abs_of_nonneg (show (0 : ℤ) ≤ (p x : ℤ) from Int.natCast_nonneg _),
          abs_of_nonneg (show (0 : ℤ) ≤ (q x : ℤ) from Int.natCast_nonneg _)] using
          abs_sub_le (p x : ℤ) 0 (q x : ℤ)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hp, hq]
        push_cast
        ring
  rw [← Int.natCast_natAbs] at hbound
  exact_mod_cast hbound

/-- Replica-character nonvanishing is detected at logarithmic order in the actual
full two-local Pauli family. Zero characters are retained as an explicit alternative;
there is no assumed rank or suppression estimate. -/
theorem pauliReplica_logarithmic_jet_detection (n r : ℕ)
    (k : {k : (Fin n → Bool) → ℤ // SpectralCharacterReplicaRealizes r k}) :
    k.val = 0 ∨ ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
      2 ^ S.card ≤ r ∧
      (starSpectralJetWord S).length ≤ min (n + 1) (Nat.log 2 r + 2) ∧
      (2 : ℝ) ^ (S.card + 1) ≤
        |iteratedFDeriv ℝ (starSpectralJetWord S).length
          (commonReferencePauliAction (fun x => (k.val x : ℝ))) 0
          (fun j => starPauliDirectionMap i (Pi.single ((starSpectralJetWord S).get j) 1))| := by
  classical
  by_cases hk : k.val = 0
  · exact Or.inl hk
  right
  have hbalance : ∑ x, k.val x = 0 := by
    obtain ⟨p, q, hp, hq, hfreq⟩ := k.property
    simp_rw [hfreq, Finset.sum_sub_distrib, ← Nat.cast_sum, hp, hq, sub_self]
  obtain ⟨B, hBne, _, hmass⟩ := exists_integerStarWalshPacket_degree_mass k.val hk
  have hB : B.Nonempty := by
    by_contra h
    have h0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hBne
    simpa only [h0, integerStarWalshPacket, Finset.prod_empty, mul_one] using hbalance
  obtain ⟨i, hi⟩ := hB
  let S := B.subtype (fun j => j ≠ i)
  have hcard : S.card + 1 = B.card := by
    simpa only [S, Finset.card_subtype, Finset.filter_ne'] using
      Finset.card_erase_add_one hi
  have hupper := integerStarWalshPacket_le_replica_mass k.property B
  have hpow : 2 ^ S.card ≤ r := by
    have h := hmass.trans hupper
    rw [← hcard, pow_succ] at h
    omega
  have hlen : (starSpectralJetWord S).length = S.card + 2 := by
    simp only [starSpectralJetWord, List.length_append, List.length_map,
      Finset.length_toList, List.length_cons, List.length_nil, Nat.reduceAdd]
  refine ⟨i, S, hpow, ?_, ?_⟩
  · rw [hlen]
    apply le_min
    · have hBn : B.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ B
      omega
    · exact Nat.add_le_add_right (Nat.le_log_of_pow_le (by omega : 1 < 2) hpow) 2
  · have hcast : (integerStarWalshPacket k.val B : ℝ) =
        realStarWalshPacket (fun x => (k.val x : ℝ)) B :=
      integerStarWalshPacket_cast_real k.val B
    have hmag : (2 : ℝ) ^ B.card ≤ |realStarWalshPacket (fun x => (k.val x : ℝ)) B| := by
      rw [← hcast]
      have hmagI : (2 : ℤ) ^ B.card ≤ |integerStarWalshPacket k.val B| := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hmass
      exact_mod_cast hmagI
    have hmagS : (2 : ℝ) ^ (S.card + 1) ≤
        |realStarWalshPacket (fun x => (k.val x : ℝ)) B| := by
      simpa only [hcard] using hmag
    rw [commonReferencePauliAction_star_jet, orderedStarCouplingDeriv_realAction,
      ← realStarWalshPacket_edge (fun x => (k.val x : ℝ)) B i hi]
    change (2 : ℝ) ^ (S.card + 1) ≤
      |commonReferenceStarJetAmplifier i S * realStarWalshPacket (fun x => (k.val x : ℝ)) B|
    rw [abs_mul]
    exact hmagS.trans (le_mul_of_one_le_left (abs_nonneg _)
      (one_le_abs_commonReferenceStarJetAmplifier i S))

/-- Ordered replica histories either have identical multiplicities or admit a
logarithmic-order detector in the full two-local source. No resonance premise is needed. -/
theorem pauliOrderedReplica_logarithmic_jet_detection (n r : ℕ)
    (α β : Fin r → (Fin n → Bool)) :
    orderedReplicaMultiplicity α = orderedReplicaMultiplicity β ∨
      ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
        2 ^ S.card ≤ r ∧
        (starSpectralJetWord S).length ≤ min (n + 1) (Nat.log 2 r + 2) ∧
        (2 : ℝ) ^ (S.card + 1) ≤
          |iteratedFDeriv ℝ (starSpectralJetWord S).length
            (commonReferencePauliAction (fun x =>
              (orderedReplicaMultiplicity α x : ℝ) - orderedReplicaMultiplicity β x)) 0
            (fun j => starPauliDirectionMap i (Pi.single ((starSpectralJetWord S).get j) 1))| := by
  classical
  let k : (Fin n → Bool) → ℤ := fun x =>
    (orderedReplicaMultiplicity α x : ℤ) - orderedReplicaMultiplicity β x
  have hk : SpectralCharacterReplicaRealizes r k :=
    ⟨orderedReplicaMultiplicity α, orderedReplicaMultiplicity β,
      (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag α)).1,
      (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag β)).1,
      fun _ => rfl⟩
  rcases pauliReplica_logarithmic_jet_detection n r ⟨k, hk⟩ with hzero | hjet
  · left
    funext x
    have hx := congrFun hzero x
    change (orderedReplicaMultiplicity α x : ℤ) - orderedReplicaMultiplicity β x = 0 at hx
    exact_mod_cast sub_eq_zero.mp hx
  · right
    simpa only [k, Int.cast_sub, Int.cast_natCast] using hjet

/-- For each fixed replica order, one full-dimensional source neighborhood
preserves all logarithmic detectors, with each detector chosen before the source
point. The radius is positive but not quantitatively controlled in `n` or `r`. -/
theorem pauliOrderedReplica_uniform_logarithmic_jet_detection (n r : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ p ∈ Metric.ball (0 : PauliBoundedLabel n 2 → ℝ) ρ,
        ∀ x : Fin n → Bool,
          matrixCharpolyRelation (commonReferencePauliMatrix n p,
            commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)) = 0 ∧
          (commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)).im = 0) ∧
      ∀ α β : Fin r → (Fin n → Bool),
      orderedReplicaMultiplicity α = orderedReplicaMultiplicity β ∨
        ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
          2 ^ S.card ≤ r ∧
          (starSpectralJetWord S).length ≤ min (n + 1) (Nat.log 2 r + 2) ∧
          ∀ p ∈ Metric.ball (0 : PauliBoundedLabel n 2 → ℝ) ρ,
            1 ≤ |iteratedFDeriv ℝ (starSpectralJetWord S).length
              (commonReferencePauliAction (fun x =>
                (orderedReplicaMultiplicity α x : ℝ) - orderedReplicaMultiplicity β x)) p
              (fun j => starPauliDirectionMap i
                (Pi.single ((starSpectralJetWord S).get j) 1))| := by
  classical
  let J := (Fin r → (Fin n → Bool)) × (Fin r → (Fin n → Bool))
  have hlocal (q : J) : ∃ ρ : ℝ, 0 < ρ ∧
      (orderedReplicaMultiplicity q.1 = orderedReplicaMultiplicity q.2 ∨
        ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
          2 ^ S.card ≤ r ∧
          (starSpectralJetWord S).length ≤ min (n + 1) (Nat.log 2 r + 2) ∧
          ∀ p ∈ Metric.ball (0 : PauliBoundedLabel n 2 → ℝ) ρ,
            1 ≤ |iteratedFDeriv ℝ (starSpectralJetWord S).length
              (commonReferencePauliAction (fun x =>
                (orderedReplicaMultiplicity q.1 x : ℝ) - orderedReplicaMultiplicity q.2 x)) p
              (fun j => starPauliDirectionMap i
                (Pi.single ((starSpectralJetWord S).get j) 1))|) := by
    rcases pauliOrderedReplica_logarithmic_jet_detection n r q.1 q.2 with heq | hjet
    · exact ⟨1, zero_lt_one, Or.inl heq⟩
    obtain ⟨i, S, hmass, horder, hdetect⟩ := hjet
    let k : (Fin n → Bool) → ℝ := fun x =>
      (orderedReplicaMultiplicity q.1 x : ℝ) - orderedReplicaMultiplicity q.2 x
    let dirs := fun j => starPauliDirectionMap i
      (Pi.single ((starSpectralJetWord S).get j) (1 : ℝ))
    have hc : ContinuousAt
        (fun p => |iteratedFDeriv ℝ (starSpectralJetWord S).length
          (commonReferencePauliAction k) p dirs|) 0 :=
      ((continuous_eval_const dirs).continuousAt.comp
        ((contDiffAt_commonReferencePauliAction k).continuousAt_iteratedFDeriv
          (show ((starSpectralJetWord S).length : WithTop ℕ∞) ≤ ⊤ from le_top))).abs
    have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (S.card + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_left zero_le_two (one_le_pow₀ one_le_two)
    have hlarge : (1 : ℝ) < |iteratedFDeriv ℝ (starSpectralJetWord S).length
        (commonReferencePauliAction k) 0 dirs| := lt_of_lt_of_le (by norm_num) (htwo.trans hdetect)
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
      (hc.eventually (Ioi_mem_nhds hlarge))
    exact ⟨ρ, hρ, Or.inr ⟨i, S, hmass, horder, fun p hp => (hball hp).le⟩⟩
  choose ρ hρ hgood using hlocal
  let δ := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset J).Nonempty) ρ
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun q _ => hρ q)
  have ht : Filter.Tendsto (commonReferencePauliMatrix n) (𝓝 0)
      (𝓝 (commonReferenceSpectralMatrix n)) := by
    simpa only [commonReferencePauliMatrix_zero] using!
      ((contDiff_commonReferencePauliMatrix n).continuous.continuousAt
        (x := (0 : PauliBoundedLabel n 2 → ℝ))).tendsto
  have hbranches : ∀ᶠ p in 𝓝 (0 : PauliBoundedLabel n 2 → ℝ),
      ∀ x : Fin n → Bool,
        matrixCharpolyRelation (commonReferencePauliMatrix n p,
          commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)) = 0 ∧
        (commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)).im = 0 := by
    apply Filter.eventually_all.mpr
    intro x
    exact (ht.eventually (commonReferenceSpectralBranch_spec n x).2.2).and
      (commonReferencePauli_branch_real n x)
  obtain ⟨R, hR, hchart⟩ := Metric.mem_nhds_iff.mp hbranches
  refine ⟨min R δ, lt_min hR hδ, ?_, ?_⟩
  · intro p hp
    exact hchart (Metric.ball_subset_ball (min_le_left R δ) hp)
  intro α β
  rcases hgood (α, β) with heq | hjet
  · exact Or.inl heq
  obtain ⟨i, S, hmass, horder, hball⟩ := hjet
  refine Or.inr ⟨i, S, hmass, horder, ?_⟩
  intro p hp
  exact hball p (Metric.ball_subset_ball
    ((min_le_right R δ).trans (Finset.inf'_le ρ (Finset.mem_univ (α, β)))) hp)

end
end GaloisForLFunctions.HTGeometry
