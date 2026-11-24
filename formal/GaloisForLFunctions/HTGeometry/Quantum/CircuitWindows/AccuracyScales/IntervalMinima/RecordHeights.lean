import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.FrozenClearance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Accuracy margins for visits to a finite family of closed time intervals -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
open MaximumIntervals
open DiagonalSynthesis (Register)
noncomputable section

/-- The least gate-distance in the interval starting at a with duration
T. The chosen date is kept so the improved fit belongs to the very
same interval, even when several minima coincide. -/
private theorem attained {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (a T : ℝ) :
    ∃ t ∈ Icc a (a+max T 0), ∀ v ∈ Icc a (a+max T 0),
      orbitCircuitDistance H s t ≤ orbitCircuitDistance H s v := by
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (le_add_of_nonneg_right (le_max_right T 0)))
    (orbitCircuitDistance_lipschitz H s).continuous.continuousOn
  exact ⟨t,ht,isMinOn_iff.mp hmin⟩

def bestDate {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (a T : ℝ) : ℝ :=
  (attained H s a T).choose

theorem bestDate_spec {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (a T : ℝ) :
    let w := bestDate H s a T
    w ∈ Icc a (a+max T 0) ∧ ∀ v ∈ Icc a (a+max T 0),
      orbitCircuitDistance H s w ≤ orbitCircuitDistance H s v :=
  (attained H s a T).choose_spec

/-- Encode the minimum for an interval and a gate budget in one index. -/
def records (ω : PathPauliDisorder) (a T : ℕ → ℕ → ℝ) (k j : ℕ) : ℝ :=
  let N := k+3
  let B := 2^(6*N)
  let H := chainGenerator ω k
  let s := (j-1)%B
  let i := (j-1)/B
  if j=0 then 0 else orbitCircuitDistance H s (bestDate H s (a k i) (T k i))

/-- Put the row for physical prefix k at index b(k). The number of
admissible records can therefore scale with the observation horizon. -/
def embedRows (b : ℕ → ℕ) (g : ℕ → ℕ → ℝ) (n : ℕ) : ℕ → ℝ := by
  classical
  exact if h : ∃ k, b k=n then g h.choose else fun _ => 0

private theorem read_row {b : ℕ → ℕ} (hb : StrictMono b) (g : ℕ → ℕ → ℝ) (k : ℕ) :
    embedRows b g (b k)=g k := by
  classical
  have h : ∃ l, b l=b k := ⟨k,rfl⟩
  rw [embedRows,dif_pos h,hb.injective h.choose_spec]

/-- Rows of exponentially many heights at unevenly spaced integer indices
have simultaneous exponential clearance outside a zero-dimensional set. -/
theorem row_clearance (b : ℕ → ℕ) (hb : StrictMono b) (g : ℕ → ℕ → ℝ) :
    ∀ e ∉ exceptionalTolerances (embedRows b g), ∃ q : ℕ, ∀ᶠ k : ℕ in atTop,
      ¬ ∃ j < 2^(8*(b k+3)), |e-g k j| ≤ 1/(2:ℝ)^(q*b k) := by
  intro e he
  obtain ⟨q,hq⟩ := not_forall.mp he
  refine ⟨q,?_⟩
  filter_upwards [hb.tendsto_atTop.eventually (not_frequently.mp hq)] with k hfar
  simpa only [read_row hb] using hfar

/-- Exceptional errors for the minima on the chosen family of intervals. -/
def intervalExceptional (ω : PathPauliDisorder) (a T : ℕ → ℕ → ℝ) (b : ℕ → ℕ) : Set ℝ :=
  exceptionalTolerances (embedRows b (records ω a T))

/-- For every prefix, every indexed interval and every budget, an
affordable visit persists at a slightly tighter tolerance somewhere in
that interval. The exceptional tolerances have dimension zero. Both
interval endpoints may be chosen from the frozen chain. -/
theorem interval_clearance (ω : PathPauliDisorder) (a T : ℕ → ℕ → ℝ)
    (b : ℕ → ℕ) (hb : StrictMono b) (hbN : ∀ k, k+3 ≤ b k) :
    dimH (intervalExceptional ω a T b)=0 ∧
      ∀ e > (0:ℝ), e ∉ intervalExceptional ω a T b → ∃ c : ℕ, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H := chainGenerator ω k
      let δ := 1/(2:ℝ)^(c*b k)
      ∀ i < 2^(b k), let I := Icc (a k i) (a k i+max (T k i) 0)
        ∀ s : ℕ, ∀ v ∈ I, HasProjectiveCircuitApproximation N (e+δ) s (unitaryEvolution H.val v) →
          ∃ w ∈ I, HasProjectiveCircuitApproximation N (e-δ) s (unitaryEvolution H.val w) := by
  let g := records ω a T
  refine ⟨dimH_exceptionalTolerances _,?_⟩
  intro e he hreg
  obtain ⟨c,hc⟩ := row_clearance b hb g e hreg
  refine ⟨c,?_⟩
  filter_upwards [hc] with k hfar
  intro N H δ i hi I s v hv hfit
  have hδ : δ < e := by
    by_contra! hlt
    apply hfar ⟨0,by positivity,?_⟩
    change |e-0| ≤ δ
    rw [sub_zero, abs_of_pos he]
    exact hlt
  let B := 2^(6*N)
  by_cases hs : s < B
  · let idx := B*i+s+1
    have hB : 0 < B := by dsimp only [B]; positivity
    have hn := hbN k
    change N ≤ b k at hn
    have hidx : idx < 2^(8*(b k+3)) := by
      have ht : B*i+s < B*(i+1) := by rw [Nat.mul_succ]; omega
      have h₁ := ht.trans_le (Nat.mul_le_mul_left B (Nat.succ_le_of_lt hi))
      have h₂ : B*2^(b k) < 2^(8*(b k+3)) := by
        dsimp only [B]
        rw [←pow_add]
        exact Nat.pow_lt_pow_right (by decide) (by omega)
      dsimp only [idx]; omega
    let w := bestDate H s (a k i) (T k i)
    obtain ⟨hw,hmin⟩ := bestDate_spec H s (a k i) (T k i)
    have hm : g k idx = orbitCircuitDistance H s w := by
      simp only [g,records,idx,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,
        Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hs,B,N,H,w]
      rw [Nat.mul_add_div (by positivity),Nat.div_eq_of_lt hs,add_zero]
    refine ⟨w,hw,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr ?_⟩
    have hu := (hmin v hv).trans ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit)
    change orbitCircuitDistance H s w ≤ e+δ at hu
    by_contra! hlt
    change e-δ < orbitCircuitDistance H s w at hlt
    apply hfar ⟨idx,hidx,?_⟩
    change |e-g k idx| ≤ δ
    rw [hm]
    exact abs_le.mpr ⟨by linarith only [hu],by linarith only [hlt]⟩
  · have hN : 2 ≤ N := by dsimp only [N]; omega
    obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at hN H
      (hasPauliWeightAtMost_pathHamiltonian _ (isSelfAdjoint_pathHamiltonian _)) (e-δ) (sub_pos.mpr hδ)
    obtain ⟨z,hz,C,hC,herr⟩ := hm.1 v
    have hcap : m ≤ B := max_cap hN H (sub_nonneg.mpr hδ.le) hm
    exact ⟨v,hv,z,hz,C,hC.trans (hcap.trans (le_of_not_gt hs)),herr⟩

#print axioms interval_clearance
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
