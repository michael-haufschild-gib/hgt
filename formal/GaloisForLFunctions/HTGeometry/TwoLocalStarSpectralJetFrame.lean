import GaloisForLFunctions.HTGeometry.TwoLocalStarSpectralJetDetection
import GaloisForLFunctions.HTGeometry.FiniteWalshObservationCapacityLaw

/-!
# An exact real spectral-jet frame at one two-local reference Hamiltonian

The integer-character certificate in `TwoLocalStarSpectralJetDetection` is
upgraded to a quantitative statement for every real covector. For each
nonempty Boolean parity mode, select one distinguished spin and differentiate
the literal spectral action twice transversely and once in each remaining
star coupling. Divide by its explicit signed factorial/gap amplification.

The resulting compensated responses satisfy the unconditional identity

`sum_B response(k,B)^(2 : ℕ) + (sum_x k(x))^(2 : ℕ) = 2^n * sum_x k(x)^(2 : ℕ)`.

Consequently every centered nonzero real covector has a literal derivative
of order at most `n+1` with magnitude at least its Euclidean norm. The common
reference Hamiltonian and the order bound are independent of replica count.
The square roots in the action are the characteristic roots already realized
by the ordinary two-local star matrices in the imported certificate.

This addresses the normalization gap in local source nondegeneracy. It does
not give a quantitative common neighbourhood, a transfer to one full-family
analytic eigenbranch chart or its iterated Frechet derivatives, typical-draw
estimates, global fibre multiplicity, a circuit-budget cutoff, or the
return-excised complete-circuit incidence-action bound. The available star
couplings are two-local, not restricted to a prescribed nearest-neighbour path.
Walsh response is not being identified with quantum circuit complexity.
-/

open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance starFrameBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

/-- Unnormalized real Walsh coefficient, used only as a spectral-response coordinate. -/
def realStarWalshPacket {I : Type*} [Fintype I]
    (k : (I → Bool) → ℝ) (B : Finset I) : ℝ :=
  ∑ x, k x * ∏ j ∈ B, (if x j then (-1 : ℝ) else 1)

private theorem realStarWalshPacket_cast_complex
    {I : Type*} [Fintype I] (k : (I → Bool) → ℝ) (B : Finset I) :
    (realStarWalshPacket k B : ℂ) =
      ∑ x, (k x : ℂ) * orientationWalshCharacter B x := by
  classical
  simp only [realStarWalshPacket, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_prod, orientationWalshCharacter]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> norm_num [primeDirichletSign]

private theorem inverseWalshCoefficient_realStarWalshPacket
    {I : Type*} [Fintype I] (k : (I → Bool) → ℝ) (B : Finset I) :
    inverseWalshCoefficient (fun x => (k x : ℂ)) B =
      (((2 : ℝ) ^ Fintype.card I)⁻¹ * realStarWalshPacket k B : ℝ) := by
  rw [Complex.ofReal_mul, realStarWalshPacket_cast_complex]
  simp [inverseWalshCoefficient]

/-- Real Parseval with no centering or nonzero premise. -/
theorem sum_sq_realStarWalshPacket
    {I : Type*} [Fintype I] (k : (I → Bool) → ℝ) :
    (∑ B : Finset I, realStarWalshPacket k B ^ (2 : ℕ)) =
      (2 : ℝ) ^ Fintype.card I * ∑ x, k x ^ (2 : ℕ) := by
  classical
  have h := sum_norm_sq_inverseWalshCoefficient (fun x => (k x : ℂ))
  simp_rw [inverseWalshCoefficient_realStarWalshPacket, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, mul_pow] at h
  rw [← Finset.mul_sum] at h
  have hD : (2 : ℝ) ^ Fintype.card I ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscale := congrArg (fun v : ℝ => ((2 : ℝ) ^ Fintype.card I) ^ 2 * v) h
  simpa only [pow_two, mul_assoc, mul_inv_cancel_left₀ hD] using hscale

/-- Real spectral action on a star slice through the common diagonal reference. -/
def commonReferenceRealStarAction {n : ℕ}
    (k : (Fin n → Bool) → ℝ) (i : Fin n)
    (c : {j : Fin n // j ≠ i} → ℝ) (u : ℝ) : ℝ :=
  ∑ p : Fin 2 × qubitEnvironment n i, k (edgeEquiv i p) *
    blockSplitRoot
      (fun z => ∑ j : {j : Fin n // j ≠ i},
        starJetReferenceField n j * (if z j then -1 else 1))
      (twoLocalStarGap (starJetReferenceField n i) c) p u

theorem orderedStarCouplingDeriv_realAction {n : ℕ}
    (k : (Fin n → Bool) → ℝ) (i : Fin n)
    (S : Finset {j : Fin n // j ≠ i}) :
    orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (commonReferenceRealStarAction k i c)) 0) 0 =
      (-1 : ℝ) ^ S.card * (S.card.factorial : ℝ) *
        (starJetReferenceField n i)⁻¹ ^ (S.card + 1) *
          realStarWalshPacket
            (fun z => k (edgeState i z false) - k (edgeState i z true)) S := by
  let m : qubitEnvironment n i → ℝ := fun z =>
    ∑ j : {j : Fin n // j ≠ i},
      starJetReferenceField n j * (if z j then -1 else 1)
  have haction (c : {j : Fin n // j ≠ i} → ℝ) :
      commonReferenceRealStarAction k i c =
        blockSplitRelation
          (∑ z, (k (edgeEquiv i (0,z)) + k (edgeEquiv i (1,z))) * m z)
          (fun z => k (edgeEquiv i (0,z)) - k (edgeEquiv i (1,z)))
          (twoLocalStarGap (starJetReferenceField n i) c) := by
    funext u
    unfold commonReferenceRealStarAction
    rw [sum_blockSplitRoot_eq]
  simp_rw [haction, edgeEquiv_zero, edgeEquiv_one]
  exact orderedStarCouplingDeriv_actualSpectralCurvature (starJetReferenceField n i)
    (starJetReferenceField_pos_le_one n i).1
    (fun z => k (edgeState i z false) - k (edgeState i z true)) _ S

private theorem realWalshSign_edgeState {n : ℕ} (B : Finset (Fin n))
    (i : Fin n) (hi : i ∈ B) (z : qubitEnvironment n i) (b : Bool) :
    (∏ j ∈ B, (if edgeState i z b j then (-1 : ℝ) else 1)) =
      (if b then (-1 : ℝ) else 1) *
        ∏ j ∈ B.subtype (fun j => j ≠ i), (if z j then (-1 : ℝ) else 1) := by
  let f : Fin n → ℝ := fun j => if edgeState i z b j then -1 else 1
  have hprod :
      (∏ j ∈ B.subtype (fun j => j ≠ i), (if z j then (-1 : ℝ) else 1)) =
        ∏ j ∈ B.erase i, f j := by
    calc
      _ = ∏ j ∈ B.subtype (fun j => j ≠ i), f j := by
        apply Finset.prod_congr rfl
        intro j _
        simp [f, edgeState_of_ne i z b j.property]
      _ = ∏ j ∈ B with j ≠ i, f j := Finset.prod_subtype_eq_prod_filter f
      _ = _ := by congr 1; ext j; simp [and_comm]
  rw [hprod]
  simpa [f, edgeState_self] using (Finset.mul_prod_erase B f hi).symm

/-- Every nonconstant Walsh mode is an actual distinguished-spin spectral response. -/
theorem realStarWalshPacket_edge {n : ℕ} (k : (Fin n → Bool) → ℝ)
    (B : Finset (Fin n)) (i : Fin n) (hi : i ∈ B) :
    realStarWalshPacket k B =
      realStarWalshPacket
        (fun z => k (edgeState i z false) - k (edgeState i z true))
        (B.subtype (fun j => j ≠ i)) := by
  unfold realStarWalshPacket
  rw [← (edgeEquiv i).sum_comp
    (fun x => k x * ∏ j ∈ B, (if x j then (-1 : ℝ) else 1))]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  change (∑ z, k (edgeState i z false) *
      ∏ j ∈ B, (if edgeState i z false j then (-1 : ℝ) else 1)) +
      (∑ z, k (edgeState i z true) *
        ∏ j ∈ B, (if edgeState i z true j then (-1 : ℝ) else 1)) = _
  simp_rw [realWalshSign_edgeState B i hi]
  simp only [Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Known scalar amplification of one literal mixed derivative. -/
def commonReferenceStarJetAmplifier {n : ℕ} (i : Fin n)
    (S : Finset {j : Fin n // j ≠ i}) : ℝ :=
  (-1 : ℝ) ^ S.card * (S.card.factorial : ℝ) *
    (starJetReferenceField n i)⁻¹ ^ (S.card + 1)

theorem one_le_abs_commonReferenceStarJetAmplifier {n : ℕ} (i : Fin n)
    (S : Finset {j : Fin n // j ≠ i}) :
    1 ≤ |commonReferenceStarJetAmplifier i S| := by
  have ha := starJetReferenceField_pos_le_one n i
  have hinv : 1 ≤ (starJetReferenceField n i)⁻¹ := (one_le_inv₀ ha.1).mpr ha.2
  have hfac : (1 : ℝ) ≤ (S.card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos S.card
  have hp : (1 : ℝ) ≤ (starJetReferenceField n i)⁻¹ ^ (S.card + 1) :=
    one_le_pow₀ hinv
  simp only [commonReferenceStarJetAmplifier, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (S.card.factorial : ℝ) by positivity),
    abs_of_nonneg (inv_nonneg.mpr ha.1.le)]
  exact one_le_mul_of_one_le_of_one_le hfac hp

/-- One compensated actual star derivative for each nonempty parity mode.
The empty mode is set to zero: it represents the global spectral shift. -/
def commonReferenceSpectralJet {n : ℕ} (k : (Fin n → Bool) → ℝ)
    (B : Finset (Fin n)) : ℝ :=
  if h : B.Nonempty then
    let i := B.min' h
    let S := B.subtype (fun j => j ≠ i)
    orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (commonReferenceRealStarAction k i c)) 0) 0 /
        commonReferenceStarJetAmplifier i S
  else 0

theorem commonReferenceSpectralJet_eq_packet {n : ℕ}
    (k : (Fin n → Bool) → ℝ) (B : Finset (Fin n)) (hB : B.Nonempty) :
    commonReferenceSpectralJet k B = realStarWalshPacket k B := by
  unfold commonReferenceSpectralJet
  rw [dif_pos hB]
  dsimp only
  rw [orderedStarCouplingDeriv_realAction,
    ← realStarWalshPacket_edge k B (B.min' hB) (B.min'_mem hB)]
  change commonReferenceStarJetAmplifier _ _ * _ /
    commonReferenceStarJetAmplifier _ _ = _
  have hne : commonReferenceStarJetAmplifier (B.min' hB)
      (B.subtype fun j => j ≠ B.min' hB) ≠ 0 := by
    have := one_le_abs_commonReferenceStarJetAmplifier (B.min' hB)
      (B.subtype fun j => j ≠ B.min' hB)
    intro hz
    rw [hz, abs_zero] at this
    norm_num at this
  exact mul_div_cancel_left₀ _ hne

@[simp] theorem commonReferenceSpectralJet_empty {n : ℕ}
    (k : (Fin n → Bool) → ℝ) : commonReferenceSpectralJet k ∅ = 0 := by
  simp [commonReferenceSpectralJet]

/-- Exact energy identity for actual common-base spectral derivatives.
No nondegeneracy, centering, integrality or source-tail premise is required.
The only omitted energy is the constant (global-shift) mode. -/
theorem commonReferenceSpectralJet_parseval (n : ℕ)
    (k : (Fin n → Bool) → ℝ) :
    (∑ B : Finset (Fin n), commonReferenceSpectralJet k B ^ (2 : ℕ)) +
        (∑ x, k x) ^ (2 : ℕ) = (2 : ℝ) ^ n * ∑ x, k x ^ (2 : ℕ) := by
  classical
  have hterm (B : Finset (Fin n)) :
      realStarWalshPacket k B ^ (2 : ℕ) = commonReferenceSpectralJet k B ^ (2 : ℕ) +
        if B = ∅ then (∑ x, k x) ^ (2 : ℕ) else 0 := by
    rcases B.eq_empty_or_nonempty with rfl | hB
    · simp [realStarWalshPacket]
    · rw [commonReferenceSpectralJet_eq_packet k B hB, if_neg hB.ne_empty, add_zero]
  have h := sum_sq_realStarWalshPacket k
  simp_rw [hterm] at h
  simpa only [Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.card_fin] using h

private theorem exists_large_realStarWalshPacket {n : ℕ}
    (k : (Fin n → Bool) → ℝ) (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ B : Finset (Fin n), B.Nonempty ∧
      (∑ x, k x ^ (2 : ℕ)) ≤ realStarWalshPacket k B ^ (2 : ℕ) := by
  classical
  let E : ℝ := ∑ x, k x ^ (2 : ℕ)
  have hE : 0 < E := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hk
    exact Finset.sum_pos' (fun x _ => sq_nonneg (k x))
      ⟨x, Finset.mem_univ x, sq_pos_of_ne_zero hx⟩
  by_contra hn
  push Not at hn
  have hle (B : Finset (Fin n)) : realStarWalshPacket k B ^ (2 : ℕ) ≤ E := by
    rcases B.eq_empty_or_nonempty with rfl | hB
    · simpa [realStarWalshPacket, hbalance] using hE.le
    · exact (hn B hB).le
  have hlt : (∑ B : Finset (Fin n), realStarWalshPacket k B ^ (2 : ℕ)) <
      ∑ _B : Finset (Fin n), E := by
    apply Finset.sum_lt_sum (fun B _ => hle B)
    refine ⟨∅, Finset.mem_univ _, ?_⟩
    simpa [realStarWalshPacket, hbalance] using hE
  rw [sum_sq_realStarWalshPacket] at hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hlt
  exact (lt_irrefl _) hlt

/-- Quantitative real-covector detection without an integrality assumption.
One literal parameter derivative of order at most `n+1` has magnitude at
least the Euclidean coefficient norm. The base is independent of the covector.
This is a local source certificate, not a quenched circuit-exclusion estimate. -/
theorem balanced_real_character_commonBase_starJet_detection
    (n : ℕ) (k : (Fin n → Bool) → ℝ)
    (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
      S.card + 2 ≤ n + 1 ∧
        Real.sqrt (∑ x, k x ^ (2 : ℕ)) ≤
          |orderedStarCouplingDeriv S.toList
            (fun c => deriv (deriv (commonReferenceRealStarAction k i c)) 0) 0| := by
  obtain ⟨B, hB, hlarge⟩ := exists_large_realStarWalshPacket k hbalance hk
  let i := B.min' hB
  let S := B.subtype (fun j => j ≠ i)
  have hi : i ∈ B := B.min'_mem hB
  have henv : Fintype.card {j : Fin n // j ≠ i} < n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_lt (x := i) (p := fun j : Fin n => j ≠ i) (not_not.mpr rfl)
  have hcard := Finset.card_le_univ S
  refine ⟨i, S, by omega, ?_⟩
  rw [orderedStarCouplingDeriv_realAction,
    ← realStarWalshPacket_edge k B i hi]
  change Real.sqrt _ ≤ |commonReferenceStarJetAmplifier i S * realStarWalshPacket k B|
  have hp : Real.sqrt (∑ x, k x ^ (2 : ℕ)) ≤ |realStarWalshPacket k B| := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨abs_nonneg _, by simpa only [sq_abs] using hlarge⟩
  rw [abs_mul]
  apply hp.trans
  exact le_mul_of_one_le_left (abs_nonneg _) (one_le_abs_commonReferenceStarJetAmplifier i S)

end
end GaloisForLFunctions.HTGeometry
