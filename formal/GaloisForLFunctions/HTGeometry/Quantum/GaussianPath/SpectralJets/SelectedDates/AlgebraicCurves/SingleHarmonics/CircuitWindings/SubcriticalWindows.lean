import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.GateWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.NetScales

/-! # Doubly exponential windows excluding every subcritical circuit budget -/

open Set Real MeasureTheory Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open AntipodalHorizons SharpOccupation
noncomputable section

/-- Leave strictly positive margins for both the circuit net and the time
mesh while keeping the final enlarged arc below the chosen base. -/
theorem circuit_mesh_margins {ε b : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2)) (hb : physicalArc ε<b) :
    ∃ η>0, ∃ δ>0, ε+η < sqrt 2 ∧ physicalArc (ε+η)+δ < min b (1/2) := by
  have hx := (physicalArc_spec hε.1 hε.2).1
  obtain ⟨y,hxy,hy⟩ := exists_between (lt_min hb hx.2)
  have hc : Continuous physicalArc := by unfold physicalArc; fun_prop
  obtain ⟨a,ha,hball⟩ := Metric.mem_nhds_iff.mp (hc.continuousAt.eventually_lt_const hxy)
  obtain ⟨e',he,he'⟩ := exists_between (lt_min (lt_add_of_pos_right ε ha) hε.2)
  have hy' : physicalArc e'<y := hball (show e'∈Metric.ball ε a by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr he)]
    linarith only [he'.trans_le (min_le_left ..)])
  refine ⟨e'-ε,sub_pos.mpr he,y-physicalArc e',sub_pos.mpr hy',?_,?_⟩
  · rw [show ε+(e'-ε)=e' by ring]
    exact he'.trans_le (min_le_right ..)
  · rw [show ε+(e'-ε)=e' by ring,show physicalArc e'+(y-physicalArc e')=y by ring]
    exact hy

/-- A circuit net with single-observation cost bounded by w^D excludes
continuous visits over b^(-D) periods whenever w<b. -/
theorem gate_window_of_net_rate {s : ℕ→ℕ} {ε η δ w b : ℝ} (hε : 0<ε) (hη : 0<η)
    (he : ε+η<sqrt 2) (hδ : 0<δ) (hhalf : physicalArc (ε+η)+δ≤1/2)
    (hw : 0<w) (hwb : w<b) (hb : b<1)
    (hcost : ∀ᶠ k : ℕ in atTop, let N := k+3
      let d : ℕ := 2^N-3
      ((s N:ℝ)+1)*((((N:ℝ)+1)^2)*(1+4*(s N:ℝ)/η)^32)^(s N)*
        (((d:ℝ)+2)*(physicalArc (ε+η)+δ)^d) < w^(2^N:ℕ)) :
    ∃ c∈Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop, ∀ q : ℝ, ∀ᶠ n : ℕ in atTop,
      let D : ℕ := 2^(k+3)
      pathPauliDisorderLaw.real (gateWindow k n (s (k+3)) q ((1/b)^D) ε)<c^(D-3) := by
  let y := physicalArc (ε+η)+δ
  have hy : 0<y := add_pos (physicalArc_spec (add_pos hε hη) he).1.1 hδ
  obtain ⟨c,hc,hgrid⟩ := grid_count_decay hw hwb hb hδ
  let d (k : ℕ) := 2^(k+3)-3
  have hD (k : ℕ) : d k+3=2^(k+3) := by
    have := Nat.lt_two_pow_self (n:=k+3)
    dsimp only [d]
    omega
  have htop : Tendsto d atTop atTop := tendsto_atTop_mono (fun k => by
    have := Nat.lt_two_pow_self (n:=k+3)
    change k ≤ 2^(k+3)-3
    omega) tendsto_id
  refine ⟨c,hc,?_⟩
  filter_upwards [hcost,htop.eventually hgrid] with k hnetCost htime q
  let N := k+3
  let D : ℕ := 2^N
  let p := ((d k:ℝ)+2)*y^(d k)
  have hp : 0<p := mul_pos (by positivity) (pow_pos hy _)
  obtain ⟨F,hF,hcard⟩ := exists_budget_net N (s N) η hη
  let M := ⌈(1/b)^D/δ⌉₊
  have hcover : (1/b)^D ≤ (M:ℝ)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  have hcount : Fintype.card (Outside (topLevel k) 0)=d k+1 := by
    rw [outside_card _ _ (top_pos k).ne.symm,Fintype.card_fin,←hD k]
    omega
  have hmass : (Fintype.card (Outside (topLevel k) 0):ℝ≥0∞)*
      ENNReal.ofReal y^(Fintype.card (Outside (topLevel k) 0)-1)<ENNReal.ofReal p := by
    rw [hcount,Nat.add_sub_cancel,←ENNReal.ofReal_pow hy.le,←ENNReal.ofReal_natCast,
      ←ENNReal.ofReal_mul (Nat.cast_nonneg (α:=ℝ) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff hp).mpr
    apply mul_lt_mul_of_pos_right _ (pow_pos hy _)
    push_cast
    linarith
  have hu := gate_window_bound k (s N) M q hε hη he hδ hhalf F hF hmass
  have hnet : (F.card:ℝ)*p<w^D := (mul_le_mul_of_nonneg_right hcard hp.le).trans_lt hnetCost
  have hwD : w^D ≤ ((d k:ℝ)+2)*w^(d k) := by
    have hdim : d k≤D := by change d k≤2^(k+3); rw [←hD k]; omega
    exact (pow_le_pow_of_le_one hw.le (hwb.trans hb).le hdim).trans
      (le_mul_of_one_le_left (pow_nonneg hw.le _) (by linarith only [Nat.cast_nonneg (α:=ℝ) (d k)]))
  filter_upwards [hu] with n hn
  intro D'
  have hsub : gateWindow k n (s N) q ((1/b)^D) ε⊆gateWindow k n (s N) q ((M:ℝ)*δ) ε := by
    rintro ω ⟨v,hv,hfit⟩
    exact ⟨v,⟨hv.1,hv.2.trans (add_le_add le_rfl hcover)⟩,hfit⟩
  have hle := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
    ((measure_mono hsub).trans hn)
  change pathPauliDisorderLaw.real _ ≤ _ at hle
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_add,Nat.cast_one,ENNReal.toReal_ofReal hp.le] at hle
  apply hle.trans_lt
  calc (F.card:ℝ)*(((M:ℝ)+1)*p) = ((M:ℝ)+1)*((F.card:ℝ)*p) := by ring
       _ ≤ ((M:ℝ)+1)*(((d k:ℝ)+2)*w^(d k)) := mul_le_mul_of_nonneg_left (hnet.le.trans hwD) (by positivity)
       _ < c^(d k) := by rw [←mul_assoc]; simpa only [hD k,M,D,N] using htime

/-- At any fixed displacement from a prescribed extremal antipode, the
chance of any s-gate fit throughout the next b^(-D) periods decays
exponentially in D for all sufficiently late windings. -/
theorem gaussian_subcritical_gate_window {s : ℕ→ℕ} (hs : subcriticalBudget s) {ε b : ℝ}
    (hε : ε∈Ioo (0:ℝ) (sqrt 2)) (hb : b∈Ioo (physicalArc ε) 1) :
    ∃ c∈Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop, ∀ q : ℝ, ∀ᶠ n : ℕ in atTop,
      let D : ℕ := 2^(k+3)
      pathPauliDisorderLaw.real (gateWindow k n (s (k+3)) q ((1/b)^D) ε)<c^(D-3) := by
  obtain ⟨η,hη,δ,hδ,he,hsmall⟩ := circuit_mesh_margins hε hb.1
  let y := physicalArc (ε+η)+δ
  have hy : 0<y := add_pos (physicalArc_spec (add_pos hε.1 hη) he).1.1 hδ
  have hyb := hsmall.trans_le (min_le_left ..)
  obtain ⟨w,hyw,hwb⟩ := exists_between hyb
  have hw := hy.trans hyw
  exact gate_window_of_net_rate hε.1 hη he hδ (hsmall.le.trans (min_le_right ..)) hw hwb hb.2
    (spectator_net_scale hs hη hy hyw)

#print axioms gaussian_subcritical_gate_window
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
