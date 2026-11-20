import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitExcursion
import GaloisForLFunctions.HTGeometry.ContinuousCircuitCompletedOccupationLaw

/-!
# Recurrence of the actual maximum physical circuit cost

Compactness gives a finite net of actual orbit times. Compiling this net at
half the target error bounds the minimum gate count at every time. The
largest integer cost is attained on an open region. Translating the same
finite-net argument in time brings that region back with bounded gaps.
-/

open Set MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Every orbit point is close to a propagator from a bounded time interval. -/
private theorem bounded_time_net (H : selfAdjoint (Reg n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ∃ u : ℝ, |u| ≤ B ∧
      ‖unitaryEvolution (H : Reg n) t - unitaryEvolution H u‖ < δ := by
  classical
  let U := unitaryEvolution (H : Reg n)
  have hrange : range U ⊆ Metric.closedBall 0 1 := by
    rintro x ⟨t,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 t)).le
  have hc : IsCompact (closure (range U)) :=
    (isCompact_closedBall (0 : Reg n) 1).of_isClosed_subset isClosed_closure
      (closure_minimal hrange Metric.isClosed_closedBall)
  obtain ⟨s,hs,hsfin,hcover⟩ := exists_finite_cover_balls_of_isCompact_closure hc hδ
  letI := hsfin.fintype
  have hrep (x : s) : ∃ v, U v = x.val := hs x.property
  choose τ hτ using hrep
  refine ⟨∑ x : s, |τ x|, Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  intro t
  obtain ⟨x,hx,hball⟩ := Set.mem_iUnion₂.mp (hcover (mem_range_self t))
  let j : s := ⟨x,hx⟩
  refine ⟨τ j,Finset.single_le_sum (fun i _ => abs_nonneg (τ i)) (Finset.mem_univ j),?_⟩
  change ‖U t - U (τ j)‖ < δ
  rw [hτ]
  simpa only [j,dist_eq_norm] using Metric.mem_ball.mp hball

private theorem evolve_mul (H : selfAdjoint (Reg n)) (s t : ℝ) :
    unitaryEvolution (H : Reg n) s * unitaryEvolution H t = unitaryEvolution H (s+t) := by
  simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul H (s+t) t

/-- A norm neighbourhood of any chosen orbital point contains recurrent
physical intervals of positive width, for every time-independent generator. -/
private theorem recurrent_orbit_ball (H : selfAdjoint (Reg n)) (v : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G w : ℝ, 0 ≤ G ∧ 0 < w ∧ ∀ a : ℝ, ∃ u ∈ Icc a (a+G),
      ∀ t ∈ Icc u (u+w), ‖unitaryEvolution (H : Reg n) t - unitaryEvolution H v‖ < δ := by
  let U := unitaryEvolution (H : Reg n)
  obtain ⟨B,hB,hnet⟩ := bounded_time_net H (half_pos hδ)
  let w := (δ/2)/(‖(H : Reg n)‖+1)
  have hw : 0 < w := by dsimp [w]; positivity
  have hspeed : ‖(H : Reg n)‖ * w ≤ δ/2 := by
    calc
      _ ≤ (‖(H : Reg n)‖+1) * w := mul_le_mul_of_nonneg_right (by linarith) hw.le
      _ = _ := by dsimp [w]; field_simp
  refine ⟨2*B,w,by linarith,hw,?_⟩
  intro a
  let x := a+B-v
  obtain ⟨k,hk,hclose⟩ := hnet x
  let u := a+B-k
  have huk : u ∈ Icc a (a+2*B) := by
    have h := abs_le.mp hk
    constructor <;> dsimp [u] <;> linarith only [h.1,h.2]
  have htrans : (U x - U k)*U (v-k) = U u - U v := by
    rw [sub_mul,show U x * U (v-k) = U (x+(v-k)) from evolve_mul H _ _,
      show U k * U (v-k) = U (k+(v-k)) from evolve_mul H _ _]
    rw [show x+(v-k) = u by dsimp [x,u]; ring, show k+(v-k) = v by ring]
  have hnear : ‖U u - U v‖ < δ/2 := by
    calc
      _ = ‖(U x - U k) * U (v-k)‖ := congrArg norm htrans.symm
      _ ≤ ‖U x-U k‖ * ‖U (v-k)‖ := norm_mul_le _ _
      _ = ‖U x-U k‖ := by rw [CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 _),mul_one]
      _ < _ := hclose
  refine ⟨u,huk,?_⟩
  intro t ht
  have hstep := norm_unitaryEvolution_time_sub_le H.2 t u
  have hd : |t-u| ≤ w := by rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]; linarith only [ht.2]
  have htu : ‖U t-U u‖ ≤ δ/2 :=
    hstep.trans ((mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans hspeed)
  change ‖U t-U v‖ < δ
  linarith only [norm_sub_le_norm_sub_add_norm_sub (U t) (U u) (U v),htu,hnear]

/-- Compile a bounded time net at error 1/20, reserving the remaining 1/20
for the displacement from a representative to an arbitrary orbital point. -/
private theorem exists_uniform_orbit_gate_budget {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Reg n)) (hlocal : HasPauliWeightAtMost (Fin n) 2 H) :
    ∃ P : ℕ, ∀ t : ℝ, HasProjectiveCircuitApproximation n (1/10:ℝ) P
      (unitaryEvolution (H : Reg n) t) := by
  obtain ⟨B,hB,hnet⟩ := bounded_time_net H (by norm_num : 0 < (1/20:ℝ))
  let m : ℕ := Fintype.card (PauliTracelessLabel n 2)
  let h := ‖(H : Reg n)‖
  let Z := 3*(m:ℝ)^3*h^2*B^2
  obtain ⟨r,hr⟩ := exists_nat_gt (max (B*m*h) (20*Z)+1)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hr1 : B*m*h ≤ (r:ℝ) := by linarith only [hr,le_max_left (B*m*h) (20*Z)]
  have hr2 : 20*Z ≤ (r:ℝ) := by linarith only [hr,le_max_right (B*m*h) (20*Z)]
  have hrpos : 0 < (r:ℝ) := by linarith only [hr,le_max_right (B*m*h) (20*Z),hZ]
  refine ⟨r*m,?_⟩
  intro t
  obtain ⟨u,hu,hnear⟩ := hnet t
  have hsmall : |u/(r:ℝ)| *m*h ≤ 1 := by
    rw [abs_div,abs_of_pos hrpos]
    calc
      _ = (|u| *m*h)/r := by ring
      _ ≤ 1 := (div_le_one hrpos).mpr ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg _)) (norm_nonneg _)).trans hr1)
  obtain ⟨c,hc,C,hcount,he⟩ := exists_twoLocal_projectiveTrotterCircuit_normBound
    hn H hlocal u r (by exact_mod_cast hrpos) hsmall
  have hcoef : 0 ≤ 3*(m:ℝ)^3*h^2 := by positivity
  have hsim : ‖unitaryEvolution H u - c • (C.eval : Reg n)‖ ≤ 1/20 := by
    apply he.trans
    apply (div_le_iff₀ hrpos).mpr
    have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) hu 2) hcoef
    change 3*(m:ℝ)^3*h^2*|u| ^2 ≤ 1/20*(r:ℝ)
    change 3*(m:ℝ)^3*h^2*|u| ^2 ≤ Z at hpow
    linarith only [hpow,hr2]
  refine ⟨c,hc,C,hcount.le,?_⟩
  linarith only [norm_sub_le_norm_sub_add_norm_sub
    (unitaryEvolution (H : Reg n) t) (unitaryEvolution H u) (c • (C.eval : Reg n)),hnear,hsim]

/-- A circuit exists on the whole orbit with the indicated uniform budget.
On recurrent positive-length windows every attaining circuit uses the full
budget. Thus this integer is the actual maximum of the minimum gate count. -/
def IsRecurrentOrbitCircuitMaximum (H : selfAdjoint (Reg n)) (m : ℕ) : Prop :=
  (∀ t : ℝ, HasProjectiveCircuitApproximation n (1/10:ℝ) m (unitaryEvolution (H : Reg n) t)) ∧
  ∃ G w : ℝ, 0 ≤ G ∧ 0 < w ∧ ∀ a : ℝ, ∃ u ∈ Icc a (a+G), ∀ t ∈ Icc u (u+w),
    ∀ (c : ℂ), ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
      ‖unitaryEvolution (H : Reg n) t - c • (C.eval : Reg n)‖ ≤ 1/10 → m ≤ C.gateCount

private theorem orbit_maximum_of_budget (H : selfAdjoint (Reg n))
    (hcap : ∃ P : ℕ, ∀ t : ℝ, HasProjectiveCircuitApproximation n (1/10:ℝ) P
      (unitaryEvolution (H : Reg n) t)) : ∃ m, IsRecurrentOrbitCircuitMaximum H m := by
  classical
  let m := Nat.find hcap
  refine ⟨m,Nat.find_spec hcap,?_⟩
  by_cases hm : m = 0
  · exact ⟨0,1,le_rfl,zero_lt_one,fun a =>
      ⟨a,⟨le_rfl,by simp⟩,fun _ _ _ _ _ _ => hm ▸ Nat.zero_le _⟩⟩
  let k := m-1
  have hk : k < m := by dsimp [k]; omega
  have hbad := Nat.find_min hcap hk
  push Not at hbad
  obtain ⟨v,hv⟩ := hbad
  let K := phaseCircuitMatrixImageAtMost n k
  let U := unitaryEvolution (H : Reg n)
  obtain ⟨Y,hY,hmin⟩ := exists_compactTarget_minDist (isCompact_phaseCircuitMatrixImageAtMost n k)
    (phaseCircuitMatrixImageAtMost_nonempty n k) (U v)
  have hfar : 1/10 < Metric.infDist (U v) K := by
    by_contra! h
    apply hv
    obtain ⟨c,hc,C,hC,rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hY
    refine ⟨c,hc,C,hC,?_⟩
    rw [← dist_eq_norm]
    change dist (U v) (c • (C.eval : Reg n)) ≤ 1/10
    exact hmin.le.trans h
  obtain ⟨G,w,hG,hw,hrec⟩ := recurrent_orbit_ball H v (sub_pos.mpr hfar)
  refine ⟨G,w,hG,hw,?_⟩
  intro a
  obtain ⟨u,hu,hclose⟩ := hrec a
  refine ⟨u,hu,?_⟩
  intro t ht c hc C he
  by_contra! hshort
  let X := c • (C.eval : Reg n)
  have hx : X ∈ K := mem_phaseCircuitMatrixImageAtMost_iff.mpr
    ⟨c,hc,C,by dsimp [k]; omega,rfl⟩
  have hd := Metric.infDist_le_dist_of_mem (x := U v) hx
  rw [dist_eq_norm] at hd
  have hnear := hclose t ht
  change ‖U t-U v‖ < Metric.infDist (U v) K - 1/10 at hnear
  rw [norm_sub_rev] at hnear
  change ‖U t-X‖ ≤ 1/10 at he
  linarith only [hd,norm_sub_le_norm_sub_add_norm_sub (U v) (U t) X,hnear,he]

private theorem circuit_approx_phase (n s : ℕ) (ε : ℝ) {X : Reg n} (z : ℂ) (hz : ‖z‖ = 1) :
    HasProjectiveCircuitApproximation n ε s (z • X) ↔ HasProjectiveCircuitApproximation n ε s X := by
  have move (Y : Reg n) (a : ℂ) (ha : ‖a‖ = 1)
      (h : HasProjectiveCircuitApproximation n ε s Y) :
      HasProjectiveCircuitApproximation n ε s (a • Y) := by
    obtain ⟨c,hc,C,hC,he⟩ := h
    refine ⟨a*c,by rw [norm_mul,ha,hc,one_mul],C,hC,?_⟩
    rwa [← smul_smul,← smul_sub,norm_smul,ha,one_mul]
  refine ⟨fun h => ?_,move X z hz⟩
  have h0 : z ≠ 0 := by intro hz0; simp [hz0] at hz
  simpa only [smul_smul,inv_mul_cancel₀ h0,one_smul] using
    move (z • X) z⁻¹ (by rw [norm_inv,hz,inv_one]) h

/-- At every error, the budgets covering a full-rank physical orbit are
exactly the budgets covering every independently assigned energy phase.
Thus the orbit maximum depends on the eigenbasis and the gate model. -/
theorem uniform_circuit_budget_iff_all_spectral_phases {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)))
    (s : ℕ) (ε : ℝ) :
    (∀ t : ℝ, HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t)) ↔
      ∀ θ : Fin d → UnitAddCircle, HasProjectiveCircuitApproximation n ε s
        (projectiveSpectralMatrix e (hermitianEigenbasisUnitary H.2.isHermitian) θ) := by
  let E := fun i => H.2.isHermitian.eigenvalues (e.symm i)
  let Φ := RHTower.projectivePhysicalPhaseFlowHom E
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let A := projectiveContinuousCircuitCaptureTarget e V s ε
  have ht (t : ℝ) : HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t) ↔ Φ t ∈ A := by
    rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e H.2.isHermitian]
    exact (circuit_approx_phase n s ε _ (by simp [Complex.norm_exp])).trans
      (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε _).symm
  constructor
  · intro h θ
    have hs : range Φ ⊆ A := by rintro y ⟨t,rfl⟩; exact (ht t).mp (h t)
    have hc := isClosed_projectiveContinuousCircuitCaptureTarget e V s ε
    exact (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε θ).mp
      (closure_minimal hs hc (RHTower.denseRange_projectivePhysicalPhaseFlowHom E hmax θ))
  · intro h t
    exact (ht t).mpr ((mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε _).mpr (h _))

#print axioms uniform_circuit_budget_iff_all_spectral_phases

/-- A full Gaussian nearest-neighbour draw attains its own maximum minimum
gate count on recurrent intervals. This maximum exceeds the exponential
budget, and the same draw remains distinguishable from Haar at all times. -/
theorem gaussianPath_attained_circuit_maximum_and_permanent_locality :
    ∀ᶠ L : ℕ in Filter.atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin
      (StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalParameterCount L)) 1),
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      (∃ m > excursionGateBudget (L*2), IsRecurrentOrbitCircuitMaximum H m) ∧
        RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  filter_upwards [Filter.eventually_ge_atTop 1,gaussianPath_translatedCircuitExcursions_and_permanentLocality]
    with L hL hgauss
  filter_upwards [hgauss] with p hp
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  obtain ⟨m,hm⟩ := orbit_maximum_of_budget H (exists_uniform_orbit_gate_budget (by omega) H
    (RHTower.pairQubitProjectivePauliSeed_hasPauliWeightAtMost_two L p))
  refine ⟨⟨m,?_,hm⟩,hp.2⟩
  obtain ⟨G,_,hb⟩ := hp.1
  obtain ⟨u,_,hu⟩ := hb 0
  have hw : 0 ≤ translatedExcursionWidth (L*2) ‖(H : Reg (L*2))‖ := by
    unfold translatedExcursionWidth; positivity
  obtain ⟨c,hc,C,hC,he⟩ := hm.1 u
  by_contra! h
  exact (not_lt_of_ge he) (hu u ⟨le_rfl,le_add_of_nonneg_right hw⟩ c hc C (hC.trans h))

#print axioms gaussianPath_attained_circuit_maximum_and_permanent_locality

end
end GaloisForLFunctions.HTGeometry
