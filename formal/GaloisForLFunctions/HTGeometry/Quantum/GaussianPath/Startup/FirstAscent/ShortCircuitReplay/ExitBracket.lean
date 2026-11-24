import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.BoundedHorizon

/-! # First departure after a physical short-circuit visit -/

open Filter MeasureTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
open ThermodynamicEdges EnergyMesh
noncomputable section

/-- Forward lag until the specified budget first fails its operator tolerance. -/
def firstDeparture {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (v e : ℝ) :=
  sInf {t : ℝ | 0 ≤ t ∧ e < orbitCircuitDistance H s (v+t)}

private theorem angle_below_turn {e : ℝ} (he : e ∈ Ioo (0:ℝ) 2) :
    0 < 4*arcsin (e/2) ∧ 4*arcsin (e/2) < 2*π := by
  have hh := arcsin_lt_arcsin (show -1 ≤ e/2 by linarith only [he.1]) (show e/2<1 by linarith only [he.2]) le_rfl
  rw [arcsin_one] at hh
  exact ⟨mul_pos (by norm_num) (arcsin_pos.mpr (half_pos he.1)),by linarith only [hh]⟩

private theorem crossed {e x : ℝ} (he : e ∈ Ioo (0:ℝ) 2) (hx : 0 ≤ x) :
    (clippedChord x < e ↔ x < 4*arcsin (e/2)) ∧
    (e < clippedChord x ↔ 4*arcsin (e/2) < x) := by
  let p := min x (2*π)/4
  have h₀ := le_min hx two_pi_pos.le
  have h₁ := min_le_right x (2*π)
  have hp : p ∈ Icc (-(π/2)) (π/2) := by
    dsimp only [p]; exact ⟨by linarith only [h₀,pi_pos],by linarith only [h₁]⟩
  have hu : e/2 ∈ Icc (-1:ℝ) 1 := ⟨by linarith only [he.1],by linarith only [he.2]⟩
  have hturn := (angle_below_turn he).2
  have hl : p < arcsin (e/2) ↔ x < 4*arcsin (e/2) := by
    dsimp only [p]
    rw [div_lt_iff₀ (by norm_num : (0:ℝ)<4),mul_comm (arcsin _),min_lt_iff]
    exact or_iff_left hturn.not_gt
  have hh : arcsin (e/2) < p ↔ 4*arcsin (e/2) < x := by
    dsimp only [p]
    rw [lt_div_iff₀ (by norm_num : (0:ℝ)<4),mul_comm (arcsin _),lt_min_iff]
    exact and_iff_left hturn
  change (2*sin p < e ↔ _) ∧ (e < 2*sin p ↔ _)
  constructor
  · rw [←hl,lt_arcsin_iff_sin_lt hp hu]
    constructor <;> intro h <;> linarith only [h]
  · rw [←hh,arcsin_lt_iff_lt_sin hu hp]
    constructor <;> intro h <;> linarith only [h]

private theorem chord_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    clippedChord a ≤ clippedChord b := by
  have bound {x : ℝ} (h : 0 ≤ x) : min x (2*π)/4 ∈ Icc (-(π/2)) (π/2) :=
    ⟨by linarith only [le_min h two_pi_pos.le,pi_pos],by linarith only [min_le_right x (2*π)]⟩
  exact mul_le_mul_of_nonneg_left (monotoneOn_sin (bound ha) (bound (ha.trans hab))
    (div_le_div_of_nonneg_right (min_le_min_right _ hab) (by norm_num))) zero_le_two

private theorem trap {N s : ℕ} (H : selfAdjoint (Register N)) (v e : ℝ) {a b : ℝ}
    (hb : 0 ≤ b) (hl : ∀ t ∈ Icc (0:ℝ) a, orbitCircuitDistance H s (v+t) ≤ e)
    (hu : e < orbitCircuitDistance H s (v+b)) : firstDeparture H s v e ∈ Icc a b := by
  let S := {t : ℝ | 0 ≤ t ∧ e < orbitCircuitDistance H s (v+t)}
  have hmem : b∈S := ⟨hb,hu⟩
  have hh : BddBelow S := ⟨0,fun _ h => h.1⟩
  refine ⟨le_csInf ⟨_,hmem⟩ ?_,csInf_le hh hmem⟩
  intro t ht
  exact le_of_not_gt fun h => ht.2.not_ge (hl t ⟨ht.1,h.le⟩)

/-- After every sublinear-budget visit at error δ, the first exit through
error e lies between the two thermodynamic dates at e−δ and e+δ, up to
any fixed scaled margin. This applies also to visits selected at a first
return. -/
theorem gaussian_visit_departure :
    ∃ w : ℝ, 0 < w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := fun n : ℕ => ((n+2 : ℕ):ℝ)
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => physicalWidth ω n/N n) atTop (𝓝 w) ∧
      ∀ (k s : ℕ→ℕ), (∀ᶠ n in atTop, k n ≤ s n) →
        Tendsto (fun n => (s n:ℝ)/N n) atTop (𝓝 0) →
        ∀ δ e η : ℝ, 0 ≤ δ → δ < e → e+δ < 2 → 0 < η →
        ∀ᶠ n in atTop, ∀ v : ℝ, orbitCircuitDistance (H n) (k n) v ≤ δ →
          N n*firstDeparture (H n) (s n) v e ∈
            Icc (4*arcsin ((e-δ)/2)/w-η) (4*arcsin ((e+δ)/2)/w+η) := by
  obtain ⟨w,hw,hω⟩ := gaussian_bounded_gate_replay
  refine ⟨w,hw,?_⟩
  filter_upwards [hω] with ω hω
  intro N H
  refine ⟨hω.1,?_⟩
  intro k s hk hs δ e η hδ he he' hη
  let α := 4*arcsin ((e-δ)/2)
  let β := 4*arcsin ((e+δ)/2)
  let a := max 0 (α/w-η)
  let b := β/w+η
  have he₁ : e-δ∈Ioo (0:ℝ) 2 := ⟨sub_pos.mpr he,by linarith only [hδ,he']⟩
  have he₂ : e+δ∈Ioo (0:ℝ) 2 := ⟨by linarith only [he,hδ],he'⟩
  have ha : 0 ≤ a := le_max_left ..
  have hb : 0 < b := add_pos (div_pos (angle_below_turn he₂).1 hw) hη
  have ha' : a*w < α := (lt_div_iff₀ hw).mp (max_lt (div_pos (angle_below_turn he₁).1 hw) (sub_lt_self _ hη))
  have hb' : β < b*w := (div_lt_iff₀ hw).mp (lt_add_of_pos_right _ hη)
  have h₁ := (crossed he₁ (mul_nonneg ha hw.le)).1.mpr ha'
  have h₂ := (crossed he₂ (mul_nonneg hb.le hw.le)).2.mpr hb'
  let m := min (e-δ-clippedChord (a*w)) (clippedChord (b*w)-(e+δ))/2
  have hpos : 0 < m := half_pos (lt_min (sub_pos.mpr h₁) (sub_pos.mpr h₂))
  have hm₁ : m ≤ e-δ-clippedChord (a*w) :=
    (half_le_self (le_min (sub_nonneg.mpr h₁.le) (sub_nonneg.mpr h₂.le))).trans (min_le_left ..)
  have hm₂ : m < clippedChord (b*w)-(e+δ) :=
    (half_lt_self (lt_min (sub_pos.mpr h₁) (sub_pos.mpr h₂))).trans_le (min_le_right ..)
  filter_upwards [hω.2 k s hk hs (max a b) m hpos] with n hn
  intro v hv
  have hN : 0 < N n := by dsimp only [N]; positivity
  have hN₁ : 1 ≤ N n := by dsimp only [N]; exact_mod_cast (by omega : 1 ≤ n+2)
  have hsup := trap (s:=s n) (H n) v e (b:=b/N n) (div_nonneg hb.le hN.le) (a:=a/N n) (by
    intro t ht
    have ht' := hn v t ⟨ht.1,ht.2.trans ((div_le_self ha hN₁).trans (le_max_left ..))⟩
    have htx : N n*t ≤ a := by simpa only [mul_comm (N n) t] using (le_div_iff₀ hN).mp ht.2
    have hl := chord_mono (mul_nonneg (mul_nonneg hN.le ht.1) hw.le) (mul_le_mul_of_nonneg_right htx hw.le)
    linarith only [(abs_le.mp ht').2,hl,hm₁,hv]) (by
    have hu := hn v (b/N n) ⟨div_nonneg hb.le hN.le,(div_le_self hb.le hN₁).trans (le_max_right ..)⟩
    rw [show N n*(b/N n)=b by field_simp] at hu
    linarith only [(abs_le.mp hu).1,hm₂,hv])
  refine ⟨(le_max_right 0 (α/w-η)).trans ?_,?_⟩
  · have h := (div_le_iff₀ hN).mp hsup.1
    simpa only [mul_comm (N n)] using h
  · have h := (le_div_iff₀ hN).mp hsup.2
    simpa only [mul_comm (N n)] using h

#print axioms gaussian_visit_departure
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
