import GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityFiniteXiVerticalDefect
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

open Complex Filter Set Topology
open scoped Classical

namespace RHTower

noncomputable section

/-- Centered dilation on a finite multiplicity-sensitive Xi jet packet. -/
def deningerMeyerFiniteXiJetPacketCenteredFlow
    (S : Finset XiDivisorSupport) (c : ℝ) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ]
      DeningerMeyerFiniteXiJetPacket S :=
  Complex.exp (-(c : ℂ) / 2) • deningerMeyerFiniteXiJetPacketFlow S c

@[simp]
theorem deningerMeyerFiniteXiJetPacketCenteredFlow_apply
    (S : Finset XiDivisorSupport) (c : ℝ)
    (x : DeningerMeyerFiniteXiJetPacket S)
    (q : DeningerMeyerFiniteXiJetSlot S) :
    deningerMeyerFiniteXiJetPacketCenteredFlow S c x q =
      Complex.exp (-(c : ℂ) / 2) *
        ∑ i ∈ Finset.range (q.2.val + 1),
          (q.2.val.choose i : ℂ) * (c : ℂ) ^ i *
            Complex.exp ((c : ℂ) * (q.1.1 : ℂ)) *
            x
              ⟨q.1,
                ⟨q.2.val - i,
                  lt_of_le_of_lt (Nat.sub_le q.2.val i) q.2.isLt⟩⟩ :=
  rfl

/-- Full finite Xi jet evaluation intertwines centered source and packet flows. -/
theorem deningerMeyerFiniteXiJetPacketLM_centeredFlow
    (S : Finset XiDivisorSupport) (c : ℝ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiJetPacketLM S
        (deningerMeyerStrongLogCenteredCohomologyFlow c u) =
      deningerMeyerFiniteXiJetPacketCenteredFlow S c
        (deningerMeyerFiniteXiJetPacketLM S u) := by
  rw [deningerMeyerStrongLogCenteredCohomologyFlow,
    deningerMeyerFiniteXiJetPacketCenteredFlow,
    LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
    deningerMeyerFiniteXiJetPacketLM_flow]

/-- Centered finite Xi Jordan packets form an exact one-parameter group. -/
theorem deningerMeyerFiniteXiJetPacketCenteredFlow_add
    (S : Finset XiDivisorSupport) (a b : ℝ)
    (x : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiJetPacketCenteredFlow S a
        (deningerMeyerFiniteXiJetPacketCenteredFlow S b x) =
      deningerMeyerFiniteXiJetPacketCenteredFlow S (a + b) x := by
  obtain ⟨u, rfl⟩ := deningerMeyerFiniteXiJetPacketLM_surjective S x
  rw [← deningerMeyerFiniteXiJetPacketLM_centeredFlow,
    ← deningerMeyerFiniteXiJetPacketLM_centeredFlow,
    deningerMeyerStrongLogCenteredCohomologyFlow_add,
    deningerMeyerFiniteXiJetPacketLM_centeredFlow]

@[simp]
theorem deningerMeyerFiniteXiJetPacketCenteredFlow_zero
    (S : Finset XiDivisorSupport)
    (x : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiJetPacketCenteredFlow S 0 x = x := by
  obtain ⟨u, rfl⟩ := deningerMeyerFiniteXiJetPacketLM_surjective S x
  rw [← deningerMeyerFiniteXiJetPacketLM_centeredFlow,
    deningerMeyerStrongLogCenteredCohomologyFlow_zero]

/-- Literal Meyer class isolating one coordinate of a finite full Xi jet packet. -/
def deningerMeyerFiniteXiJetBasisClass
    (S : Finset XiDivisorSupport)
    (q : DeningerMeyerFiniteXiJetSlot S) :
    DeningerMeyerStrongLogCohomology :=
  Classical.choose
    (deningerMeyerFiniteXiJetPacketLM_surjective S
      (Pi.single q (1 : ℂ)))

@[simp]
theorem deningerMeyerFiniteXiJetBasisClass_evaluation
    (S : Finset XiDivisorSupport)
    (q r : DeningerMeyerFiniteXiJetSlot S) :
    deningerMeyerFiniteXiJetPacketLM S
        (deningerMeyerFiniteXiJetBasisClass S q) r =
      (Pi.single q (1 : ℂ) : DeningerMeyerFiniteXiJetPacket S) r := by
  exact congrFun
    (Classical.choose_spec
      (deningerMeyerFiniteXiJetPacketLM_surjective S
        (Pi.single q (1 : ℂ)))) r

/-- Fixed algebraic section of the finite full Xi jet observation. -/
def deningerMeyerFiniteXiJetPacketSection
    (S : Finset XiDivisorSupport)
    (x : DeningerMeyerFiniteXiJetPacket S) :
    DeningerMeyerStrongLogCohomology :=
  ∑ q : DeningerMeyerFiniteXiJetSlot S,
    x q • deningerMeyerFiniteXiJetBasisClass S q

@[simp]
theorem deningerMeyerFiniteXiJetPacketLM_section
    (S : Finset XiDivisorSupport)
    (x : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiJetPacketLM S
        (deningerMeyerFiniteXiJetPacketSection S x) = x := by
  funext r
  simp only [deningerMeyerFiniteXiJetPacketSection, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply,
    deningerMeyerFiniteXiJetBasisClass_evaluation, smul_eq_mul]
  rw [Finset.sum_eq_single r]
  · rw [Pi.single_eq_same, mul_one]
  · intro q _ hq
    rw [Pi.single_eq_of_ne (Ne.symm hq)]
    simp
  · simp

/-- Packet supported on the full jet block belonging to one selected Xi point. -/
def deningerMeyerFiniteXiJetSupportBlock
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (y : DeningerMeyerFiniteXiJetPacket S) :
    DeningerMeyerFiniteXiJetPacket S := fun q =>
  if q.1 = rho then y q else 0

theorem sum_deningerMeyerFiniteXiJetSupportBlock
    (S : Finset XiDivisorSupport)
    (y : DeningerMeyerFiniteXiJetPacket S) :
    (∑ rho : ↥S, deningerMeyerFiniteXiJetSupportBlock S rho y) = y := by
  funext q
  simp only [Finset.sum_apply, deningerMeyerFiniteXiJetSupportBlock]
  rw [Finset.sum_eq_single q.1]
  · simp
  · intro rho _ hrho
    simp [Ne.symm hrho]
  · simp

/-- Inverse centered Jordan counterpacket for one Xi support block. -/
def deningerMeyerFiniteXiJetCounterpacket
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (y : DeningerMeyerFiniteXiJetPacket S) (n : ℕ) :
    DeningerMeyerFiniteXiJetPacket S :=
  deningerMeyerFiniteXiJetPacketCenteredFlow S
    (-deningerMeyerHalfDensityXiGraphTime rho.1 n)
    (deningerMeyerFiniteXiJetSupportBlock S rho y)

/-- Polynomial Jordan shear times the off-line countercharacter tends to zero. -/
private theorem tendsto_graphTime_pow_mul_countercharacter
    (rho : XiDivisorSupport) (i : ℕ)
    (hrho : (rho : ℂ).re ≠ 1 / 2) :
    Tendsto
      (fun n : ℕ =>
        ((deningerMeyerHalfDensityXiGraphTime rho n : ℝ) : ℂ) ^ i *
          Complex.exp
            (-((deningerMeyerHalfDensityXiGraphTime rho n : ℝ) : ℂ) *
              ((rho : ℂ) - 1 / 2)))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let a : ℝ := deningerMeyerHalfDensityXiHorizontalRate rho
  have ha : a ≠ 0 := by
    dsimp [a, deningerMeyerHalfDensityXiHorizontalRate]
    exact sub_ne_zero.mpr hrho
  have ha2 : 0 < a ^ (2 : ℕ) := sq_pos_of_ne_zero ha
  have hbase :=
    (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_scaled i ha2).comp
      tendsto_natCast_atTop_atTop
  have hscaled := hbase.const_mul (|a| ^ i)
  rw [mul_zero] at hscaled
  convert hscaled using 1
  funext n
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp]
  dsimp [a]
  rw [deningerMeyerHalfDensityXiGraphTime]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.div_ofNat_re, Complex.one_re]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [deningerMeyerHalfDensityXiHorizontalRate]
  ring_nf

theorem deningerMeyerFiniteXiJetCounterpacket_coord_tendsto_zero
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (hrho : (rho.1 : ℂ).re ≠ 1 / 2)
    (y : DeningerMeyerFiniteXiJetPacket S)
    (q : DeningerMeyerFiniteXiJetSlot S) :
    Tendsto (fun n => deningerMeyerFiniteXiJetCounterpacket S rho y n q)
      atTop (𝓝 0) := by
  by_cases hq : q.1 = rho
  · have hsum := tendsto_finsetSum (Finset.range (q.2.val + 1))
      (fun i _ =>
        (((tendsto_graphTime_pow_mul_countercharacter rho.1 i hrho).const_mul
          (((q.2.val.choose i : ℂ) * (-1 : ℂ) ^ i) *
            y
              ⟨q.1,
                ⟨q.2.val - i,
                  lt_of_le_of_lt (Nat.sub_le q.2.val i) q.2.isLt⟩⟩))))
    have hsum' : Tendsto
        (fun n : ℕ =>
          ∑ i ∈ Finset.range (q.2.val + 1),
            (((q.2.val.choose i : ℂ) * (-1 : ℂ) ^ i) *
              y
                ⟨q.1,
                  ⟨q.2.val - i,
                    lt_of_le_of_lt (Nat.sub_le q.2.val i) q.2.isLt⟩⟩) *
              (((deningerMeyerHalfDensityXiGraphTime rho.1 n : ℝ) : ℂ) ^ i *
                Complex.exp
                  (-((deningerMeyerHalfDensityXiGraphTime rho.1 n : ℝ) : ℂ) *
                    ((rho.1 : ℂ) - 1 / 2))))
        atTop (𝓝 0) := by
      simpa using hsum
    apply hsum'.congr'
    filter_upwards with n
    symm
    rw [deningerMeyerFiniteXiJetCounterpacket,
      deningerMeyerFiniteXiJetPacketCenteredFlow_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [deningerMeyerFiniteXiJetSupportBlock, hq, if_true]
    let t : ℂ :=
      ((deningerMeyerHalfDensityXiGraphTime rho.1 n : ℝ) : ℂ)
    have hexp :
        Complex.exp (-(-t) / 2) * Complex.exp ((-t) * (rho.1 : ℂ)) =
          Complex.exp (-t * ((rho.1 : ℂ) - 1 / 2)) := by
      rw [← Complex.exp_add]
      congr 1
      ring_nf
    have hpow : (-t) ^ i = (-1 : ℂ) ^ i * t ^ i := by
      rw [neg_pow]
    push_cast
    change
      Complex.exp (-(-t) / 2) *
          ((q.2.val.choose i : ℂ) * (-t) ^ i *
            Complex.exp ((-t) * (rho.1 : ℂ)) *
            y
              ⟨q.1,
                ⟨q.2.val - i,
                  lt_of_le_of_lt (Nat.sub_le q.2.val i) q.2.isLt⟩⟩) = _
    rw [show
      Complex.exp (-(-t) / 2) *
          ((q.2.val.choose i : ℂ) * (-t) ^ i *
            Complex.exp ((-t) * (rho.1 : ℂ)) *
            y
              ⟨q.1,
                ⟨q.2.val - i,
                  lt_of_le_of_lt (Nat.sub_le q.2.val i) q.2.isLt⟩⟩) =
        (q.2.val.choose i : ℂ) * (-t) ^ i *
          y
            ⟨q.1,
              ⟨q.2.val - i,
                lt_of_le_of_lt (Nat.sub_le q.2.val i) q.2.isLt⟩⟩ *
          (Complex.exp (-(-t) / 2) *
            Complex.exp ((-t) * (rho.1 : ℂ))) by ring_nf,
      hexp, hpow]
    dsimp [t]
    ring_nf
  · have hzero :
        (fun n => deningerMeyerFiniteXiJetCounterpacket S rho y n q) =
          fun _ => 0 := by
      funext n
      rw [deningerMeyerFiniteXiJetCounterpacket,
        deningerMeyerFiniteXiJetPacketCenteredFlow_apply]
      simp [deningerMeyerFiniteXiJetSupportBlock, hq]
    rw [hzero]
    exact tendsto_const_nhds

/-- Countertransported section, followed by forward source flow, fixes one full jet block. -/
def deningerMeyerFiniteXiJetGraphNullAtom
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (y : DeningerMeyerFiniteXiJetPacket S) (n : ℕ) :
    DeningerMeyerStrongLogCohomology :=
  deningerMeyerStrongLogCenteredCohomologyFlow
    (deningerMeyerHalfDensityXiGraphTime rho.1 n)
    (deningerMeyerFiniteXiJetPacketSection S
      (deningerMeyerFiniteXiJetCounterpacket S rho y n))

theorem deningerMeyerFiniteXiJetGraphNullAtom_evaluation
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (y : DeningerMeyerFiniteXiJetPacket S) (n : ℕ) :
    deningerMeyerFiniteXiJetPacketLM S
        (deningerMeyerFiniteXiJetGraphNullAtom S rho y n) =
      deningerMeyerFiniteXiJetSupportBlock S rho y := by
  rw [deningerMeyerFiniteXiJetGraphNullAtom,
    deningerMeyerFiniteXiJetPacketLM_centeredFlow,
    deningerMeyerFiniteXiJetPacketLM_section,
    deningerMeyerFiniteXiJetCounterpacket,
    deningerMeyerFiniteXiJetPacketCenteredFlow_add]
  simp

theorem deningerMeyerFiniteXiJetGraphNullAtom_tendsto_zero
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (hrho : (rho.1 : ℂ).re ≠ 1 / 2)
    (y : DeningerMeyerFiniteXiJetPacket S) :
    Tendsto
      (fun n => deningerMeyerHalfDensityCompletionMk
        (deningerMeyerFiniteXiJetGraphNullAtom S rho y n))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsection := tendsto_finsetSum
    (Finset.univ : Finset (DeningerMeyerFiniteXiJetSlot S))
    (fun q _ =>
      ((deningerMeyerFiniteXiJetCounterpacket_coord_tendsto_zero
        S rho hrho y q).smul_const
          (deningerMeyerHalfDensityCompletionMk
            (deningerMeyerFiniteXiJetBasisClass S q))))
  have hsource :
      Tendsto
        (fun n => deningerMeyerHalfDensityCompletionMk
          (deningerMeyerFiniteXiJetPacketSection S
            (deningerMeyerFiniteXiJetCounterpacket S rho y n)))
        atTop (𝓝 0) := by
    simpa [deningerMeyerFiniteXiJetPacketSection, map_sum, map_smul] using hsection
  have hnorm :
      (fun n => ‖deningerMeyerHalfDensityCompletionMk
        (deningerMeyerFiniteXiJetGraphNullAtom S rho y n)‖) =
      (fun n => ‖deningerMeyerHalfDensityCompletionMk
        (deningerMeyerFiniteXiJetPacketSection S
          (deningerMeyerFiniteXiJetCounterpacket S rho y n))‖) := by
    funext n
    rw [deningerMeyerFiniteXiJetGraphNullAtom,
      deningerMeyerHalfDensityCompletionMk_norm,
      deningerMeyerHalfDensityCohomologySeminorm_centeredFlow,
      ← deningerMeyerHalfDensityCompletionMk_norm]
  rw [hnorm]
  exact tendsto_zero_iff_norm_tendsto_zero.mp hsource

/-- Joint full-jet graph in the canonical half-density completion. -/
def deningerMeyerFiniteXiJetGraph
    (S : Finset XiDivisorSupport) :
    Submodule ℂ
      (DeningerMeyerHalfDensityCompletion × DeningerMeyerFiniteXiJetPacket S) :=
  LinearMap.range
    (LinearMap.prod deningerMeyerHalfDensityCompletionMk
      (deningerMeyerFiniteXiJetPacketLM S))

/-- Every finite packet of off-line Xi generalized eigenspaces is vertical. -/
theorem deningerMeyerFiniteXiJetGraph_fullVertical_of_offline
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2)
    (y : DeningerMeyerFiniteXiJetPacket S) :
    ((0 : DeningerMeyerHalfDensityCompletion), y) ∈
      (deningerMeyerFiniteXiJetGraph S).topologicalClosure := by
  let seq : ℕ → DeningerMeyerStrongLogCohomology := fun n =>
    ∑ rho : ↥S, deningerMeyerFiniteXiJetGraphNullAtom S rho y n
  have hzero :
      Tendsto (fun n => deningerMeyerHalfDensityCompletionMk (seq n))
        atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset ↥S)
      (fun rho _ =>
        deningerMeyerFiniteXiJetGraphNullAtom_tendsto_zero
          S rho (hoffline rho) y)
    simpa [seq, map_sum] using hsum
  have heval : ∀ n, deningerMeyerFiniteXiJetPacketLM S (seq n) = y := by
    intro n
    simp only [seq, map_sum,
      deningerMeyerFiniteXiJetGraphNullAtom_evaluation,
      sum_deningerMeyerFiniteXiJetSupportBlock]
  change ((0 : DeningerMeyerHalfDensityCompletion), y) ∈
    closure (deningerMeyerFiniteXiJetGraph S : Set
      (DeningerMeyerHalfDensityCompletion × DeningerMeyerFiniteXiJetPacket S))
  apply mem_closure_of_tendsto
    (hzero.prodMk_nhds
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)))
  filter_upwards with n
  refine ⟨seq n, ?_⟩
  exact Prod.ext rfl (heval n)

/-- Multivalued part of the closed full finite Xi jet observation relation. -/
def deningerMeyerFiniteXiJetGraphVertical
    (S : Finset XiDivisorSupport) :
    Submodule ℂ (DeningerMeyerFiniteXiJetPacket S) :=
  (deningerMeyerFiniteXiJetGraph S).topologicalClosure.comap
    (LinearMap.inr ℂ DeningerMeyerHalfDensityCompletion
      (DeningerMeyerFiniteXiJetPacket S))

/-- Off line, the closed relation loses the complete generalized eigenspace. -/
theorem deningerMeyerFiniteXiJetGraphVertical_eq_top_of_offline
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2) :
    deningerMeyerFiniteXiJetGraphVertical S = ⊤ := by
  apply top_unique
  intro y _
  exact deningerMeyerFiniteXiJetGraph_fullVertical_of_offline S hoffline y

/-- Total analytic multiplicity carried by a finite Xi support packet. -/
def deningerMeyerFiniteXiTotalMultiplicity
    (S : Finset XiDivisorSupport) : ℕ :=
  ∑ rho : ↥S, xiSupportMultiplicity rho.1

theorem card_deningerMeyerFiniteXiJetSlot
    (S : Finset XiDivisorSupport) :
    Fintype.card (DeningerMeyerFiniteXiJetSlot S) =
      deningerMeyerFiniteXiTotalMultiplicity S := by
  simp [deningerMeyerFiniteXiTotalMultiplicity,
    DeningerMeyerFiniteXiJetSlot, DeningerArithmeticJetIndex,
    Fintype.card_sigma]

/-- Exact defect index: full algebraic Xi multiplicity, not only support cardinality. -/
theorem finrank_deningerMeyerFiniteXiJetGraphVertical_of_offline
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2) :
    Module.finrank ℂ (deningerMeyerFiniteXiJetGraphVertical S) =
      deningerMeyerFiniteXiTotalMultiplicity S := by
  calc
    Module.finrank ℂ (deningerMeyerFiniteXiJetGraphVertical S) =
        Fintype.card (DeningerMeyerFiniteXiJetSlot S) := by
      rw [deningerMeyerFiniteXiJetGraphVertical_eq_top_of_offline S hoffline]
      simp
    _ = deningerMeyerFiniteXiTotalMultiplicity S :=
      card_deningerMeyerFiniteXiJetSlot S

end
end RHTower
