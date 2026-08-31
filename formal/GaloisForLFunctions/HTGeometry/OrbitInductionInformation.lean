import GaloisForLFunctions.HTGeometry.OrbitInductionEssentialization
import GaloisForLFunctions.HTGeometry.CommonMarkovRecoveryNeutrality
import GaloisForLFunctions.HTGeometry.PoissonIntensityMarkingIsometry
import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# Orbit induction: functional equation, information amplification, and global selection

Three further organs of the orbit-induction mechanism.

* `lpTwist` `(OI.21)` and `lpTwist_orbitInduction` — **Theorem 6.1**: a reciprocal local law
  `J_K D_{σ i} = D_i J_H` lifts to an exact functional equation `W_K Ind(D) = Ind(D) W_H` for the
  induced operator, where `W` permutes the orbit coordinates and applies the local involution.
* `klDiv_orbitPacket` `(OI.16)`, `klDiv_orbitPacket_recovery` `(OI.17)`,
  `formationJeffreys_orbitPacket` `(OI.18)` — **Theorem 5.1**: relative entropy is exactly
  amplified by the orbit size and is untouched by a common Markov recovery kernel.
* `bounded_cofinal_work_iff` `(OI.19)` — **Corollary 5.2**: bounded cofinal common-recovery work
  is equivalent to exact local neutrality.
* `orbit_selection_certificate` — **Theorem 7.1**: global compactness of the induced defect,
  global bijectivity of the induced formation block, and bounded cofinal information work each
  force the local law to be neutral.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology

noncomputable section

/-! ## The functional-equation twist -/

section Twist

variable {I : Type} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem memℓp_twist (σ : Equiv.Perm I) (J : W ≃ₗᵢ[ℂ] W) (x : lp (fun _ : I => W) 2) :
    Memℓp (fun i => J ((x : ∀ _ : I, W) (σ i))) 2 := by
  refine memℓp_gen ?_
  have hre : Summable fun i => ‖(x : ∀ _ : I, W) (σ i)‖ ^ 2 :=
    (σ.summable_iff (f := fun i => ‖(x : ∀ _ : I, W) i‖ ^ 2)).mpr (lp_summable_norm_sq x)
  have hcast : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [hcast, Real.rpow_natCast]
  exact hre.congr fun i => by rw [J.norm_map]

/-- `(OI.21)`  The functional-equation twist: permute the orbit coordinates and apply the local
involution. -/
def lpTwist (σ : Equiv.Perm I) (J : W ≃ₗᵢ[ℂ] W) :
    lp (fun _ : I => W) 2 ≃ₗᵢ[ℂ] lp (fun _ : I => W) 2 where
  toFun x := ⟨fun i => J ((x : ∀ _ : I, W) (σ i)), memℓp_twist σ J x⟩
  invFun y := ⟨fun i => J.symm ((y : ∀ _ : I, W) (σ.symm i)),
    memℓp_twist σ.symm J.symm y⟩
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp
  left_inv x := by ext i; simp
  right_inv y := by ext i; simp
  norm_map' := fun x => by
    have hsq : ‖(⟨fun i => J ((x : ∀ _ : I, W) (σ i)), memℓp_twist σ J x⟩ :
        lp (fun _ : I => W) 2)‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [lp_norm_sq_eq_tsum, lp_norm_sq_eq_tsum]
      calc (∑' i, ‖J ((x : ∀ _ : I, W) (σ i))‖ ^ 2)
          = ∑' i, ‖(x : ∀ _ : I, W) (σ i)‖ ^ 2 := tsum_congr fun i => by rw [J.norm_map]
        _ = ∑' i, ‖(x : ∀ _ : I, W) i‖ ^ 2 :=
            Equiv.tsum_eq σ fun i => ‖(x : ∀ _ : I, W) i‖ ^ 2
    show ‖(⟨fun i => J ((x : ∀ _ : I, W) (σ i)), memℓp_twist σ J x⟩ :
      lp (fun _ : I => W) 2)‖ = ‖x‖
    nlinarith [hsq, norm_nonneg (⟨fun i => J ((x : ∀ _ : I, W) (σ i)), memℓp_twist σ J x⟩ :
      lp (fun _ : I => W) 2), norm_nonneg x]

@[simp] theorem lpTwist_apply (σ : Equiv.Perm I) (J : W ≃ₗᵢ[ℂ] W)
    (x : lp (fun _ : I => W) 2) (i : I) :
    ((lpTwist σ J x : lp (fun _ : I => W) 2) : ∀ _ : I, W) i
      = J ((x : ∀ _ : I, W) (σ i)) := rfl

/-- The twist of an involutive permutation by an involutive isometry is an involution. -/
theorem lpTwist_involutive (σ : Equiv.Perm I) (J : W ≃ₗᵢ[ℂ] W)
    (hσ : ∀ i, σ (σ i) = i) (hJ : ∀ w, J (J w) = w) (x : lp (fun _ : I => W) 2) :
    lpTwist σ J (lpTwist σ J x) = x := by
  ext i
  rw [lpTwist_apply, lpTwist_apply, hJ, hσ]

end Twist

/-! ## Theorem 6.1: the induced functional equation -/

section FunctionalEquation

variable {I : Type} {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Theorem 6.1, `(OI.22)`.**  A reciprocal local law lifts to an exact functional equation for
the orbit induction. -/
theorem lpTwist_orbitInduction (σ : Equiv.Perm I) (JH : H ≃ₗᵢ[ℂ] H) (JK : K ≃ₗᵢ[ℂ] K)
    (hrec : ∀ i x, JK (orbitBlock D U V (σ i) x) = orbitBlock D U V i (JH x))
    (ξ : lp (fun _ : I => H) 2) :
    lpTwist σ JK (orbitInduction D U V ξ) = orbitInduction D U V (lpTwist σ JH ξ) := by
  ext i
  rw [lpTwist_apply, orbitInduction_apply, orbitInduction_apply, lpTwist_apply]
  exact hrec i ((ξ : ∀ _ : I, H) (σ i))

end FunctionalEquation

/-! ## Section 5: exact information amplification -/

section Information

variable {Z Wz : Type*} [MeasurableSpace Z] [MeasurableSpace Wz]

/-- `(OI.14)`  The independent orbit packet of a source law over `n` orbit points. -/
def orbitPacket (n : ℕ) (P : Measure Z) : Measure (Fin n → Z) := Measure.pi fun _ => P

instance isProbabilityMeasure_orbitPacket (n : ℕ) (P : Measure Z) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (orbitPacket n P) := by
  rw [orbitPacket]; infer_instance

/-- **Theorem 5.1, `(OI.16)`.**  Relative entropy is exactly amplified by the orbit size. -/
theorem klDiv_orbitPacket (n : ℕ) (P Q : Measure Z) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    klDiv (orbitPacket n P) (orbitPacket n Q) = n * klDiv P Q := by
  rw [orbitPacket, orbitPacket, klDiv_pi]
  simp [Finset.sum_const, nsmul_eq_mul]

instance isProbabilityMeasure_splitPacketLaw (P : Measure Z) [IsProbabilityMeasure P]
    (κ : Kernel Z Wz) [IsMarkovKernel κ] : IsProbabilityMeasure (splitPacketLaw P κ) := by
  rw [splitPacketLaw]; infer_instance

/-- **Theorem 5.1, `(OI.17)`.**  Common recovery is exactly neutral on the orbit packet. -/
theorem klDiv_orbitPacket_recovery (n : ℕ) (P Q : Measure Z) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (κ : Kernel Z Wz) [IsMarkovKernel κ] :
    klDiv (orbitPacket n (splitPacketLaw P κ)) (orbitPacket n (splitPacketLaw Q κ))
      = klDiv (orbitPacket n P) (orbitPacket n Q) := by
  rw [klDiv_orbitPacket, klDiv_orbitPacket, klDiv_splitPacketLaw]

/-- **Theorem 5.1, `(OI.18)`.**  The cofinal symmetric information work is exactly linear in the
orbit size, and untouched by common recovery. -/
theorem formationJeffreys_orbitPacket (n : ℕ) (P Q : Measure Z) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (κ : Kernel Z Wz) [IsMarkovKernel κ] :
    formationJeffreys (orbitPacket n (splitPacketLaw P κ)) (orbitPacket n (splitPacketLaw Q κ))
      = n * formationJeffreys P Q := by
  rw [formationJeffreys, formationJeffreys, klDiv_orbitPacket_recovery,
    klDiv_orbitPacket_recovery, klDiv_orbitPacket, klDiv_orbitPacket, mul_add]

theorem eq_zero_of_forall_nat_mul_le {J M : ℝ≥0∞} (hM : M ≠ ∞) (h : ∀ n : ℕ, n * J ≤ M) :
    J = 0 := by
  by_contra hJ
  rcases eq_or_ne J ∞ with rfl | hJtop
  · have := h 1
    rw [Nat.cast_one, one_mul] at this
    exact hM (top_le_iff.mp this)
  · have hdiv : M / J ≠ ∞ := by
      intro htop
      rw [ENNReal.div_eq_top] at htop
      rcases htop with ⟨_, h0⟩ | ⟨hMtop, _⟩
      · exact hJ h0
      · exact hM hMtop
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hdiv
    rw [ENNReal.div_lt_iff (Or.inl hJ) (Or.inl hJtop)] at hn
    exact absurd (h n) (not_le.mpr hn)

/-- **Corollary 5.2, `(OI.19)`.**  Bounded cofinal common-recovery work forces exact local
neutrality. -/
theorem bounded_cofinal_work_iff (P Q : Measure Z) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (κ : Kernel Z Wz) [IsMarkovKernel κ] :
    (∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n : ℕ,
        formationJeffreys (orbitPacket n (splitPacketLaw P κ))
          (orbitPacket n (splitPacketLaw Q κ)) ≤ M)
      ↔ P = Q := by
  constructor
  · rintro ⟨M, hM, h⟩
    have hJ : formationJeffreys P Q = 0 :=
      eq_zero_of_forall_nat_mul_le hM fun n => by
        rw [← formationJeffreys_orbitPacket n P Q κ]; exact h n
    rw [formationJeffreys, add_eq_zero] at hJ
    exact klDiv_eq_zero_iff.mp hJ.1
  · rintro rfl
    refine ⟨0, by simp, fun n => ?_⟩
    rw [formationJeffreys_orbitPacket, formationJeffreys, klDiv_self]
    simp

end Information

/-! ## Section 7: the global formation-selection theorem -/

section Selection

variable {I : Type} {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {Z Wz : Type*} [MeasurableSpace Z] [MeasurableSpace Wz]

/-- **Theorem 7.1.**  Three independent global admission laws each force the local law to be
neutral: global compactness of the induced defect, global bijectivity of the induced formation
block, and boundedness of the cofinal common-recovery information work. -/
theorem orbit_selection_certificate [DecidableEq I] [Infinite I]
    (Dθ : H →L[ℂ] K) (Tθ : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (Pθ Qθ : Measure Z) [IsProbabilityMeasure Pθ] [IsProbabilityMeasure Qθ]
    (κ : Kernel Z Wz) [IsMarkovKernel κ]
    (hneutral₁ : Dθ = 0 ↔ Pθ = Qθ) (hneutral₂ : Pθ = Qθ ↔ Function.Bijective Tθ) :
    (IsCompactOperator (orbitInduction Dθ U V) →
        Dθ = 0 ∧ Pθ = Qθ ∧ Function.Bijective Tθ)
      ∧ (Function.Bijective (orbitInduction Tθ U V) →
        Dθ = 0 ∧ Pθ = Qθ ∧ Function.Bijective Tθ)
      ∧ ((∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n : ℕ,
            formationJeffreys (orbitPacket n (splitPacketLaw Pθ κ))
              (orbitPacket n (splitPacketLaw Qθ κ)) ≤ M) →
        Dθ = 0 ∧ Pθ = Qθ ∧ Function.Bijective Tθ) := by
  have hbundle : ∀ _ : Pθ = Qθ, Dθ = 0 ∧ Pθ = Qθ ∧ Function.Bijective Tθ := by
    intro hPQ
    exact ⟨hneutral₁.mpr hPQ, hPQ, hneutral₂.mp hPQ⟩
  refine ⟨fun hc => ?_, fun hb => ?_, fun hw => ?_⟩
  · exact hbundle (hneutral₁.mp ((isCompactOperator_orbitInduction_iff Dθ U V).mp hc))
  · exact hbundle (hneutral₂.mpr ((orbitInduction_bijective_iff Tθ U V).mp hb))
  · exact hbundle ((bounded_cofinal_work_iff Pθ Qθ κ).mp hw)

end Selection

end

end GaloisForLFunctions.HTGeometry
