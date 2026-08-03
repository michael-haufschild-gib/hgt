import GaloisForLFunctions.HTGeometry.CayleyJetChartSubmersion

/-!
# The Cayley outer jet chart is a submersion

On packets the chart and its branch inverse are mutually inverse near every packet whose zeroth
entry avoids `-i`, and both are smooth.  So the chart's derivative is surjective there.

This is the submersion input a parametric transversality argument needs; it is strictly stronger
than the openness the corpus already had, because an open map may still have degenerate derivative.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The base point of the exponential stage -/

/-- The value of the Möbius stage of the Cayley chart: the base point at which the logarithmic
branch of the inverse is taken. -/
def chiJetBase (y : ℕ → ℂ) : ℂ :=
  affJetScalar (-(2 * Complex.I)) 1
    (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I y m) l) 0

theorem chiJetScalar_zero_eq (y : ℕ → ℂ) : chiJetScalar y 0 = Complex.exp (chiJetBase y) :=
  expJetScalar_zero _

theorem inner_affJet_ne_zero {y : ℕ → ℂ} (hy : y 0 + Complex.I ≠ 0) :
    (fun m => affJetScalar 1 Complex.I y m) 0 ≠ 0 := by
  simpa [affJetScalar_apply_zero] using hy

/-- The Möbius stage never takes the value `1`: that is the pole of the inverse Möbius map. -/
theorem chiJetBase_ne_one {y : ℕ → ℂ} (hy : y 0 + Complex.I ≠ 0) : chiJetBase y ≠ 1 := by
  have hz0 := inner_affJet_ne_zero hy
  have hinv : invJetScalar (fun m => affJetScalar 1 Complex.I y m) 0
      = ((fun m => affJetScalar 1 Complex.I y m) 0)⁻¹ := invJetScalar_zero hz0
  rw [chiJetBase, affJetScalar_apply_zero, hinv]
  intro hcontra
  have hzero : (-(2 * Complex.I)) * ((fun m => affJetScalar 1 Complex.I y m) 0)⁻¹ = 0 := by
    linear_combination hcontra
  rcases mul_eq_zero.mp hzero with h | h
  · exact neg_two_I_ne_zero h
  · exact inv_ne_zero hz0 h

/-! ## The chart inverse is a left inverse -/

theorem chiJetInv_chiJetScalar {y : ℕ → ℂ} (hy : y 0 + Complex.I ≠ 0) (k : ℕ) :
    chiJetInv (chiJetBase y) (fun j => chiJetScalar y j) k = y k := by
  have hz0 := inner_affJet_ne_zero hy
  have h1 : expJetInv (chiJetBase y) (fun j => chiJetScalar y j)
      = fun j => affJetScalar (-(2 * Complex.I)) 1
        (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I y m) l) j :=
    funext fun j => expJetInv_expJetScalar _ j
  have h3 : (fun m => affJetScalar (-(2 * Complex.I))⁻¹ (-(1 / (-(2 * Complex.I))))
      (fun j => affJetScalar (-(2 * Complex.I)) 1
        (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I y m) l) j) m)
      = fun m => invJetScalar (fun m' => affJetScalar 1 Complex.I y m') m :=
    funext fun m => affJetScalar_affJetScalar' neg_two_I_ne_zero _ m
  have h4 : (fun l => invJetScalar
      (fun m => invJetScalar (fun m' => affJetScalar 1 Complex.I y m') m) l)
      = fun l => affJetScalar 1 Complex.I y l :=
    funext fun l => invJetScalar_invJetScalar hz0 l
  have hstart : chiJetInv (chiJetBase y) (fun j => chiJetScalar y j) k
      = affJetScalar (1 : ℂ)⁻¹ (-(Complex.I / 1))
        (fun l => invJetScalar (fun m => affJetScalar (-(2 * Complex.I))⁻¹
          (-(1 / (-(2 * Complex.I))))
          (expJetInv (chiJetBase y) (fun j => chiJetScalar y j)) m) l) k := rfl
  rw [hstart, h1, h3, h4]
  exact affJetScalar_affJetScalar' one_ne_zero y k

/-! ## Packet level -/

/-- The branch inverse of the Cayley chart on packets. -/
def chiJetInvPacket (n : ℕ) (a : ℂ) (w : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  fun k => chiJetInv a (jetExtend n w) (k : ℕ)

theorem jetExtend_zero {n : ℕ} (w : Fin (n + 1) → ℂ) : jetExtend n w 0 = w 0 := by
  simp [jetExtend]

theorem chiJetPacket_chiJetInvPacket {n : ℕ} {a : ℂ} {w : Fin (n + 1) → ℂ} (hw : w 0 ≠ 0)
    (hbranch : logBranch a (w 0) ≠ 1) : chiJetPacket n (chiJetInvPacket n a w) = w := by
  funext k
  have hloc : chiJetScalar (jetExtend n (chiJetInvPacket n a w)) (k : ℕ)
      = chiJetScalar (chiJetInv a (jetExtend n w)) (k : ℕ) := by
    refine chiJetScalar_congr (K := n) (fun j hj => ?_) (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)
    simp [jetExtend, chiJetInvPacket, Nat.lt_succ_of_le hj]
  have h0 : jetExtend n w 0 = w 0 := jetExtend_zero w
  have hstart : chiJetPacket n (chiJetInvPacket n a w) k
      = chiJetScalar (jetExtend n (chiJetInvPacket n a w)) (k : ℕ) := rfl
  rw [hstart, hloc,
    chiJetScalar_chiJetInv (by rw [h0]; exact hw) (by rw [h0]; exact hbranch) (k : ℕ)]
  simp [jetExtend, k.isLt]

theorem chiJetInvPacket_chiJetPacket {n : ℕ} {y : Fin (n + 1) → ℂ} (hy : y 0 + Complex.I ≠ 0) :
    chiJetInvPacket n (chiJetBase (jetExtend n y)) (chiJetPacket n y) = y := by
  funext k
  have hy' : jetExtend n y 0 + Complex.I ≠ 0 := by
    rw [jetExtend_zero]
    exact hy
  have hloc : chiJetInv (chiJetBase (jetExtend n y))
        (jetExtend n (chiJetPacket n y)) (k : ℕ)
      = chiJetInv (chiJetBase (jetExtend n y))
        (fun j => chiJetScalar (jetExtend n y) j) (k : ℕ) := by
    refine chiJetInv_congr _ (k := (k : ℕ)) fun j hj => ?_
    have hjlt : j < n + 1 := lt_of_le_of_lt hj k.isLt
    show jetExtend n (chiJetPacket n y) j = chiJetScalar (jetExtend n y) j
    simp only [jetExtend, dif_pos hjlt]
    rfl
  have hstart : chiJetInvPacket n (chiJetBase (jetExtend n y)) (chiJetPacket n y) k
      = chiJetInv (chiJetBase (jetExtend n y)) (jetExtend n (chiJetPacket n y)) (k : ℕ) := rfl
  rw [hstart, hloc, chiJetInv_chiJetScalar hy' (k : ℕ)]
  simp [jetExtend, k.isLt]

/-! ## Surjectivity of the derivative -/

/-- The packets on which the branch inverse at `a` is defined and inverts the chart. -/
def chiChartTarget (n : ℕ) (a : ℂ) : Set (Fin (n + 1) → ℂ) :=
  {v : Fin (n + 1) → ℂ | v 0 / Complex.exp a ∈ Complex.slitPlane} ∩
    {v : Fin (n + 1) → ℂ | logBranch a (v 0) ≠ 1}

theorem isOpen_chiChartTarget (n : ℕ) (a : ℂ) : IsOpen (chiChartTarget n a) := by
  have hslitOpen : IsOpen {v : Fin (n + 1) → ℂ | v 0 / Complex.exp a ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage ((continuous_apply (0 : Fin (n + 1))).div_const _)
  have hlogOn : ContinuousOn Complex.log Complex.slitPlane := fun z hz =>
    ((Complex.contDiffAt_log (n := 0) hz).continuousAt).continuousWithinAt
  have hcont : ContinuousOn (fun v : Fin (n + 1) → ℂ => logBranch a (v 0))
      {v : Fin (n + 1) → ℂ | v 0 / Complex.exp a ∈ Complex.slitPlane} := by
    simp only [logBranch]
    refine continuousOn_const.add ?_
    exact hlogOn.comp (((continuous_apply (0 : Fin (n + 1))).div_const _).continuousOn)
      fun v hv => hv
  have hpre : chiChartTarget n a
      = {v : Fin (n + 1) → ℂ | v 0 / Complex.exp a ∈ Complex.slitPlane} ∩
        (fun v : Fin (n + 1) → ℂ => logBranch a (v 0)) ⁻¹' {z : ℂ | z ≠ 1} := rfl
  rw [hpre]
  exact hcont.isOpen_inter_preimage hslitOpen isOpen_ne

theorem chiJetPacket_mem_chiChartTarget {n : ℕ} {y : Fin (n + 1) → ℂ}
    (hy : y 0 + Complex.I ≠ 0) :
    chiJetPacket n y ∈ chiChartTarget n (chiJetBase (jetExtend n y)) := by
  have hy' : jetExtend n y 0 + Complex.I ≠ 0 := by
    rw [jetExtend_zero]
    exact hy
  have hval : chiJetPacket n y 0 = Complex.exp (chiJetBase (jetExtend n y)) := by
    have h0 : chiJetPacket n y 0 = chiJetScalar (jetExtend n y) 0 := rfl
    rw [h0, chiJetScalar_zero_eq]
  constructor
  · show chiJetPacket n y 0 / Complex.exp (chiJetBase (jetExtend n y)) ∈ Complex.slitPlane
    rw [hval, div_self (Complex.exp_ne_zero _)]
    simp [Complex.mem_slitPlane_iff]
  · show logBranch (chiJetBase (jetExtend n y)) (chiJetPacket n y 0) ≠ 1
    rw [hval, logBranch_exp]
    exact chiJetBase_ne_one hy'

theorem contDiffOn_chiJetInvPacket (n : ℕ) (a : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chiJetInvPacket n a) (chiChartTarget n a) := by
  rw [contDiffOn_pi]
  intro k
  refine contDiffOn_chiJetInv_comp (W := fun v : Fin (n + 1) → ℂ => jetExtend n v) a
    (fun j => contDiffOn_jetExtend j) (fun v hv => ?_) (fun v hv => ?_) (k : ℕ)
  · rw [jetExtend_zero]
    exact hv.1
  · rw [jetExtend_zero]
    exact hv.2

/-- **The Cayley outer jet chart is a submersion.**  Its derivative is surjective at every packet
whose zeroth entry avoids `-i`, because the branch inverse is a smooth right inverse there. -/
theorem surjective_fderiv_chiJetPacket {n : ℕ} {y : Fin (n + 1) → ℂ}
    (hy : y 0 + Complex.I ≠ 0) :
    Function.Surjective (fderiv ℝ (chiJetPacket n) y) := by
  set a : ℂ := chiJetBase (jetExtend n y) with ha
  set w : Fin (n + 1) → ℂ := chiJetPacket n y with hw
  have hwmem : w ∈ chiChartTarget n a := chiJetPacket_mem_chiChartTarget hy
  have hUopen : IsOpen {v : Fin (n + 1) → ℂ | v 0 + Complex.I ≠ 0} := by
    have hcont : Continuous fun v : Fin (n + 1) → ℂ => v 0 + Complex.I :=
      (continuous_apply (0 : Fin (n + 1))).add continuous_const
    exact isOpen_ne.preimage hcont
  have hPsiDiff : DifferentiableAt ℝ (chiJetInvPacket n a) w :=
    ((contDiffOn_chiJetInvPacket n a).differentiableOn (by simp)).differentiableAt
      ((isOpen_chiChartTarget n a).mem_nhds hwmem)
  have hPsiw : chiJetInvPacket n a w = y := chiJetInvPacket_chiJetPacket hy
  have hPhiDiff : DifferentiableAt ℝ (chiJetPacket n) y := by
    refine ((contDiffOn_chiJetPacket n).differentiableOn (by simp)).differentiableAt ?_
    exact hUopen.mem_nhds hy
  have hcomp : HasFDerivAt (chiJetPacket n ∘ chiJetInvPacket n a)
      ((fderiv ℝ (chiJetPacket n) y).comp (fderiv ℝ (chiJetInvPacket n a) w)) w := by
    have h1 : HasFDerivAt (chiJetPacket n) (fderiv ℝ (chiJetPacket n) y) y :=
      hPhiDiff.hasFDerivAt
    have h2 : HasFDerivAt (chiJetInvPacket n a) (fderiv ℝ (chiJetInvPacket n a) w) w :=
      hPsiDiff.hasFDerivAt
    have h1' : HasFDerivAt (chiJetPacket n) (fderiv ℝ (chiJetPacket n) y)
        (chiJetInvPacket n a w) := by
      rw [hPsiw]
      exact h1
    exact HasFDerivAt.comp w h1' h2
  have hid : HasFDerivAt (chiJetPacket n ∘ chiJetInvPacket n a)
      (ContinuousLinearMap.id ℝ (Fin (n + 1) → ℂ)) w := by
    refine (hasFDerivAt_id w).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_chiChartTarget n a).mem_nhds hwmem) ?_
    intro v hv
    have hv0 : v 0 ≠ 0 := by
      intro h
      have hmem : v 0 / Complex.exp a ∈ Complex.slitPlane := hv.1
      rw [h, zero_div] at hmem
      simp [Complex.mem_slitPlane_iff] at hmem
    exact chiJetPacket_chiJetInvPacket hv0 hv.2
  have hker : (fderiv ℝ (chiJetPacket n) y).comp (fderiv ℝ (chiJetInvPacket n a) w)
      = ContinuousLinearMap.id ℝ (Fin (n + 1) → ℂ) := hcomp.unique hid
  have hsurj : Function.Surjective
      ((fderiv ℝ (chiJetPacket n) y) ∘ (fderiv ℝ (chiJetInvPacket n a) w)) := by
    intro v
    refine ⟨v, ?_⟩
    have hv := congrArg (fun L : (Fin (n + 1) → ℂ) →L[ℝ] (Fin (n + 1) → ℂ) => L v) hker
    simpa using hv
  exact hsurj.of_comp

end

end GaloisForLFunctions.HTGeometry
