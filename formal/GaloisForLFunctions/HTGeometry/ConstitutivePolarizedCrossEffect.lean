import GaloisForLFunctions.HTGeometry.SteinerMobiusDuality
import GaloisForLFunctions.HTGeometry.BiasedWalshInteractionMechanics

/-!
# Constitutive polarized cross-effect mechanics

This module proves the finite formation mechanism of ULF-PCIM-1. Boolean Möbius packets recover
laws exactly. Complement becomes a triangular involution on raw packets and degree parity after
Bernoulli/Walsh polarization. No bounded-arity raw reporter carries that complement action
universally. Together these results certify exact formation, recovery, positive polarization, and
the obstruction created by incomplete interaction arity.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators
open HTGeometry.ConstraintFrameRelativity

noncomputable section

def booleanPacketRecovery {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (c : Finset I → R) : Finset I → R :=
  fun X => ∑ S : Finset I, c S * booleanZetaFeature S X

def booleanCrossEffectPacket {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (f : Finset I → R) : Finset I → R :=
  fun S => booleanMobiusProbe S f

theorem booleanPacketRecovery_crossEffectPacket
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (f : Finset I → R) :
    booleanPacketRecovery (booleanCrossEffectPacket f) = f := by
  classical
  have h := (booleanZetaBasis (V := I) (R := R)).sum_repr f
  funext X
  have hX := congrFun h X
  simpa [booleanPacketRecovery, booleanCrossEffectPacket,
    booleanZetaBasis_repr, booleanZetaBasis_apply, smul_eq_mul] using hX

theorem booleanCrossEffectPacket_packetRecovery
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (c : Finset I → R) :
    booleanCrossEffectPacket (booleanPacketRecovery c) = c := by
  classical
  funext S
  have hfun : booleanPacketRecovery c =
      ∑ T : Finset I, c T • booleanZetaFeature T := by
    funext X
    simp [booleanPacketRecovery, smul_eq_mul]
  change booleanMobiusProbeLinear S (booleanPacketRecovery c) = c S
  rw [hfun]
  rw [map_sum]
  simp [booleanMobiusProbe_booleanZetaFeature]

def booleanComplementLaw {I R : Type*} [Fintype I] [DecidableEq I]
    (f : Finset I → R) : Finset I → R :=
  fun X => f Xᶜ

def rawComplementPacket {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (c : Finset I → R) : Finset I → R :=
  booleanCrossEffectPacket (booleanComplementLaw (booleanPacketRecovery c))

def rawComplementTriangular
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (c : Finset I → R) (S : Finset I) : R :=
  (-1 : R) ^ S.card * ∑ U : Finset I, if S ⊆ U then c U else 0

private theorem booleanZetaFeature_eq_prod_indicator
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (S X : Finset I) :
    booleanZetaFeature (R := R) S X =
      ∏ i ∈ S, if i ∈ X then 1 else 0 := by
  classical
  unfold booleanZetaFeature
  simp only [IncidenceAlgebra.zeta_apply]
  by_cases hSX : S ⊆ X
  · rw [if_pos hSX]
    symm
    apply Finset.prod_eq_one
    intro i hi
    simp [hSX hi]
  · rw [if_neg hSX]
    obtain ⟨i, hiS, hiX⟩ := Finset.not_subset.mp hSX
    symm
    exact Finset.prod_eq_zero hiS (by simp [hiX])

private theorem booleanComplementLaw_zeta_expansion
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (U : Finset I) :
    booleanComplementLaw (booleanZetaFeature (R := R) U) =
      fun X => ∑ S ∈ U.powerset,
        (-1 : R) ^ S.card * booleanZetaFeature S X := by
  classical
  funext X
  rw [booleanComplementLaw, booleanZetaFeature_eq_prod_indicator]
  have hpoint : ∀ i : I,
      (if i ∈ Xᶜ then (1 : R) else 0) =
        1 - (if i ∈ X then 1 else 0) := by
    intro i
    by_cases hi : i ∈ X <;> simp [hi]
  simp_rw [hpoint]
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one,
    booleanZetaFeature_eq_prod_indicator]

private theorem booleanMobiusProbe_complement_zeta
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (S U : Finset I) :
    booleanMobiusProbe S
        (booleanComplementLaw (booleanZetaFeature (R := R) U)) =
      if S ⊆ U then (-1 : R) ^ S.card else 0 := by
  classical
  rw [booleanComplementLaw_zeta_expansion]
  have hfun : (fun X => ∑ T ∈ U.powerset,
      (-1 : R) ^ T.card * booleanZetaFeature T X) =
      ∑ T ∈ U.powerset,
        (-1 : R) ^ T.card • booleanZetaFeature (R := R) T := by
    funext X
    simp [smul_eq_mul]
  rw [hfun]
  change booleanMobiusProbeLinear S
      (∑ T ∈ U.powerset,
        (-1 : R) ^ T.card • booleanZetaFeature (R := R) T) = _
  rw [map_sum]
  simp only [map_smul, booleanMobiusProbeLinear_apply,
    booleanMobiusProbe_booleanZetaFeature]
  by_cases hSU : S ⊆ U
  · rw [if_pos hSU]
    rw [Finset.sum_eq_single S]
    · simp
    · intro T hTU hTS
      simp [hTS]
    · intro hSnot
      exact (hSnot (Finset.mem_powerset.mpr hSU)).elim
  · rw [if_neg hSU]
    apply Finset.sum_eq_zero
    intro T hTU
    have hTS : T ≠ S := by
      intro h
      subst T
      exact hSU (Finset.mem_powerset.mp hTU)
    simp [hTS]

theorem rawComplementPacket_eq_triangular
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (c : Finset I → R) :
    rawComplementPacket c = rawComplementTriangular c := by
  classical
  funext S
  have hrecover : booleanPacketRecovery c =
      ∑ U : Finset I, c U • booleanZetaFeature U := by
    funext X
    simp [booleanPacketRecovery, smul_eq_mul]
  have hcomp : booleanComplementLaw (booleanPacketRecovery c) =
      ∑ U : Finset I,
        c U • booleanComplementLaw (booleanZetaFeature U) := by
    rw [hrecover]
    funext X
    simp [booleanComplementLaw, smul_eq_mul]
  change booleanMobiusProbeLinear S
      (booleanComplementLaw (booleanPacketRecovery c)) = _
  rw [hcomp, map_sum]
  simp only [map_smul, booleanMobiusProbeLinear_apply,
    booleanMobiusProbe_complement_zeta, rawComplementTriangular]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hSU : S ⊆ U <;> simp [hSU, mul_comm]

theorem rawComplementPacket_involutive
    {I R : Type*} [Fintype I] [DecidableEq I] [Field R]
    (c : Finset I → R) :
    rawComplementPacket (rawComplementPacket c) = c := by
  classical
  change booleanCrossEffectPacket
      (booleanComplementLaw
        (booleanPacketRecovery
          (booleanCrossEffectPacket
            (booleanComplementLaw (booleanPacketRecovery c))))) = c
  rw [booleanPacketRecovery_crossEffectPacket]
  have hc : booleanComplementLaw
      (booleanComplementLaw (booleanPacketRecovery c)) = booleanPacketRecovery c := by
    funext X
    simp [booleanComplementLaw]
  rw [hc, booleanCrossEffectPacket_packetRecovery]

def finsetComplementEquiv (I : Type*) [Fintype I] [DecidableEq I] :
    Finset I ≃ Finset I :=
  Equiv.ofBijective (fun X : Finset I => Xᶜ) ⟨
    (fun X Y h => by
      have := congrArg (fun Z : Finset I => Zᶜ) h
      simpa using this),
    (fun Y => ⟨Yᶜ, by simp⟩)⟩

@[simp]
theorem finsetComplementEquiv_apply
    (I : Type*) [Fintype I] [DecidableEq I] (X : Finset I) :
    finsetComplementEquiv I X = Xᶜ := rfl

theorem bernoulliWeight_complement
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (X : Finset I) :
    bernoulliWeight (fun i => 1 - q i) Xᶜ = bernoulliWeight q X := by
  classical
  simp [bernoulliWeight]
  ring

theorem biasedWalshCoordinate_complement
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (i : I) (X : Finset I) :
    biasedWalshCoordinate (fun j => 1 - q j) i Xᶜ =
      -biasedWalshCoordinate q i X := by
  classical
  have hv : biasedBernoulliVariance (fun j => 1 - q j) i =
      biasedBernoulliVariance q i := by
    simp [biasedBernoulliVariance]
    ring
  by_cases hi : i ∈ X
  · simp [biasedWalshCoordinate, hi, hv]
    ring
  · simp [biasedWalshCoordinate, hi, hv]
    ring

theorem biasedWalshCharacter_complement
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (S X : Finset I) :
    biasedWalshCharacter (fun i => 1 - q i) S Xᶜ =
      (-1 : ℝ) ^ S.card * biasedWalshCharacter q S X := by
  classical
  rw [biasedWalshCharacter_eq_prod_coordinate,
    biasedWalshCharacter_eq_prod_coordinate]
  simp_rw [biasedWalshCoordinate_complement]
  exact Finset.prod_neg _

theorem biasedWalshCoefficient_complement
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (f : Finset I → ℝ) (S : Finset I) :
    biasedWalshCoefficient (fun i => 1 - q i)
        (booleanComplementLaw f) S =
      (-1 : ℝ) ^ S.card * biasedWalshCoefficient q f S := by
  classical
  unfold biasedWalshCoefficient bernoulliExp
  let e := finsetComplementEquiv I
  rw [← e.sum_comp]
  simp only [e, finsetComplementEquiv_apply, booleanComplementLaw]
  simp only [compl_compl]
  simp_rw [bernoulliWeight_complement,
    biasedWalshCharacter_complement]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X hX
  ring

def polarizedPacketTransform
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (c : Finset I → ℝ) (S : Finset I) : ℝ :=
  (∏ i ∈ S, Real.sqrt (biasedBernoulliVariance q i)) *
    ∑ T : Finset I,
      if S ⊆ T then (∏ j ∈ T \ S, q j) * c T else 0

private theorem biasedWalshCoefficient_booleanZetaFeature
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (S T : Finset I) :
    biasedWalshCoefficient q (booleanZetaFeature T) S =
      if S ⊆ T then
        (∏ i ∈ S, Real.sqrt (biasedBernoulliVariance q i)) *
          ∏ j ∈ T \ S, q j
      else 0 := by
  classical
  let sf : I → ℝ := fun i =>
    if i ∈ S then (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1
  let sg : I → ℝ := fun i =>
    if i ∈ T then 0
    else if i ∈ S then -q i / Real.sqrt (biasedBernoulliVariance q i) else 1
  have hobs : ∀ X : Finset I,
      booleanZetaFeature T X * biasedWalshCharacter q S X =
        (∏ i ∈ X, sf i) * ∏ i ∈ Xᶜ, sg i := by
    intro X
    unfold booleanZetaFeature biasedWalshCharacter
    simp only [IncidenceAlgebra.zeta_apply]
    by_cases hTX : T ⊆ X
    · rw [if_pos hTX]
      simp only [one_mul, sf]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      have hiT : i ∉ T := fun hiT =>
        (Finset.mem_compl.mp hi) (hTX hiT)
      simp [sg, hiT]
    · rw [if_neg hTX, zero_mul]
      obtain ⟨i, hiT, hiX⟩ := Finset.not_subset.mp hTX
      have hz : ∏ i ∈ Xᶜ, sg i = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_compl.mpr hiX)
        simp [sg, hiT]
      rw [hz, mul_zero]
  unfold biasedWalshCoefficient
  rw [congrArg (bernoulliExp q) (funext hobs), bernoulliExp_prod]
  have hlocal : ∀ i : I,
      q i * sf i + (1 - q i) * sg i =
        if i ∈ S then
          if i ∈ T then Real.sqrt (biasedBernoulliVariance q i) else 0
        else if i ∈ T then q i else 1 := by
    intro i
    have hv : 0 < biasedBernoulliVariance q i := by
      exact mul_pos (hq0 i) (sub_pos.mpr (hq1 i))
    have hsqrt : Real.sqrt (biasedBernoulliVariance q i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hv)
    have hsq : Real.sqrt (biasedBernoulliVariance q i) ^ (2 : ℕ) =
        biasedBernoulliVariance q i := Real.sq_sqrt hv.le
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
    · simp [sf, sg, hiS, hiT]
      field_simp [hsqrt]
      rw [hsq, biasedBernoulliVariance]
    · simp [sf, sg, hiS, hiT]
      field_simp [hsqrt]
      ring
    · simp [sf, sg, hiS, hiT]
    · simp [sf, sg, hiS, hiT]
  simp_rw [hlocal]
  by_cases hST : S ⊆ T
  · rw [if_pos hST]
    have hfactor : ∀ i : I,
        (if i ∈ S then
            if i ∈ T then Real.sqrt (biasedBernoulliVariance q i) else 0
          else if i ∈ T then q i else 1) =
          (if i ∈ S then Real.sqrt (biasedBernoulliVariance q i) else 1) *
            (if i ∈ T \ S then q i else 1) := by
      intro i
      by_cases hiS : i ∈ S
      · have hiT : i ∈ T := hST hiS
        simp [hiS, hiT]
      · by_cases hiT : i ∈ T <;> simp [hiS, hiT]
    simp_rw [hfactor, Finset.prod_mul_distrib,
      Finset.prod_ite_mem]
    simp
  · rw [if_neg hST]
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hiS, hiT]

theorem biasedWalshCoefficient_packetRecovery
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (c : Finset I → ℝ) (S : Finset I) :
    biasedWalshCoefficient q (booleanPacketRecovery c) S =
      polarizedPacketTransform q c S := by
  classical
  have hsum : (fun X =>
      booleanPacketRecovery c X * biasedWalshCharacter q S X) =
      (fun X => ∑ T : Finset I,
        c T * (booleanZetaFeature T X * biasedWalshCharacter q S X)) := by
    funext X
    simp only [booleanPacketRecovery, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T hT
    ring
  calc
    biasedWalshCoefficient q (booleanPacketRecovery c) S =
        ∑ T : Finset I,
          c T * biasedWalshCoefficient q (booleanZetaFeature T) S := by
      unfold biasedWalshCoefficient bernoulliExp
      rw [hsum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      apply Finset.sum_congr rfl
      intro X hX
      ring
    _ = polarizedPacketTransform q c S := by
      unfold polarizedPacketTransform
      simp_rw [biasedWalshCoefficient_booleanZetaFeature hq0 hq1]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hST : S ⊆ T
      · simp [hST]
        ring
      · simp [hST]

theorem biasedWalshCoefficient_crossEffectFusion
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) (S : Finset I) :
    biasedWalshCoefficient q f S =
      polarizedPacketTransform q (booleanCrossEffectPacket f) S := by
  calc
    biasedWalshCoefficient q f S =
        biasedWalshCoefficient q
          (booleanPacketRecovery (booleanCrossEffectPacket f)) S := by
      rw [booleanPacketRecovery_crossEffectPacket]
    _ = polarizedPacketTransform q (booleanCrossEffectPacket f) S :=
      biasedWalshCoefficient_packetRecovery hq0 hq1 _ _

theorem polarizedPacketTransform_complement_intertwining
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (c : Finset I → ℝ) (S : Finset I) :
    polarizedPacketTransform (fun i => 1 - q i) (rawComplementPacket c) S =
      (-1 : ℝ) ^ S.card * polarizedPacketTransform q c S := by
  have hqbar0 : ∀ i, 0 < 1 - q i := fun i => sub_pos.mpr (hq1 i)
  have hqbar1 : ∀ i, 1 - q i < 1 := fun i => by linarith [hq0 i]
  rw [← biasedWalshCoefficient_packetRecovery hqbar0 hqbar1,
    rawComplementPacket, booleanPacketRecovery_crossEffectPacket,
    biasedWalshCoefficient_complement,
    biasedWalshCoefficient_packetRecovery hq0 hq1]

def packetAgreesThrough
    {I R : Type*} [Fintype I] [DecidableEq I]
    (d : ℕ) (c c' : Finset I → R) : Prop :=
  ∀ S, S.card ≤ d → c S = c' S

theorem deltaPacket_agrees_zero_through
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : ℕ} {U : Finset I} (hU : U.card = d + 1) :
    packetAgreesThrough d (fun S => if S = U then (1 : ℝ) else 0) 0 := by
  intro S hS
  have hne : S ≠ U := by
    intro h
    subst S
    omega
  simp [hne]

def truncatePacket
    {I R : Type*} [Fintype I] [DecidableEq I]
    (d : ℕ) (c : Finset I → R) :
    {S : Finset I // S.card ≤ d} → R :=
  fun S => c S

theorem rawComplementPacket_delta_empty
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Finset I) :
    rawComplementPacket (fun S => if S = U then (1 : ℝ) else 0) ∅ = 1 := by
  classical
  rw [rawComplementPacket_eq_triangular]
  simp [rawComplementTriangular]

theorem no_bounded_arity_raw_complement_factor
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : ℕ} {U : Finset I} (hU : U.card = d + 1) :
    ¬ ∃ Φ : ({S : Finset I // S.card ≤ d} → ℝ) →
        ({S : Finset I // S.card ≤ d} → ℝ),
        ∀ c, truncatePacket d (rawComplementPacket c) =
          Φ (truncatePacket d c) := by
  rintro ⟨Φ, hΦ⟩
  let delta : Finset I → ℝ := fun S => if S = U then 1 else 0
  have htrunc : truncatePacket d delta = truncatePacket d 0 := by
    funext S
    exact deltaPacket_agrees_zero_through hU S S.property
  have houtfun : truncatePacket d (rawComplementPacket delta) =
      truncatePacket d (rawComplementPacket 0) := by
    calc
      truncatePacket d (rawComplementPacket delta) = Φ (truncatePacket d delta) := hΦ delta
      _ = Φ (truncatePacket d 0) := congrArg Φ htrunc
      _ = truncatePacket d (rawComplementPacket 0) := (hΦ 0).symm
  have hout := congrFun houtfun ⟨∅, Nat.zero_le d⟩
  change rawComplementPacket delta ∅ = rawComplementPacket 0 ∅ at hout
  rw [show delta = (fun S => if S = U then (1 : ℝ) else 0) by rfl,
    rawComplementPacket_delta_empty] at hout
  have hzero : rawComplementPacket (0 : Finset I → ℝ) = 0 := by
    funext S
    simp [rawComplementPacket, booleanCrossEffectPacket,
      booleanComplementLaw, booleanPacketRecovery, booleanMobiusProbe]
  rw [hzero] at hout
  norm_num at hout

theorem no_bounded_arity_raw_complement_factor_fin (d : ℕ) :
    ¬ ∃ Φ : ({S : Finset (Fin (d + 1)) // S.card ≤ d} → ℝ) →
        ({S : Finset (Fin (d + 1)) // S.card ≤ d} → ℝ),
        ∀ c, truncatePacket d (rawComplementPacket c) =
          Φ (truncatePacket d c) := by
  apply no_bounded_arity_raw_complement_factor
      (U := Finset.univ)
  simp

end

end GaloisForLFunctions.HTGeometry
