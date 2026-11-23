import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.BondProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.WeakGuards
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.PacketScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.Capacity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.ExponentialFloor

/-! # Dense-cut exclusion up to a logarithmic physical date -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private theorem window_count {n w : ℕ} (hw : 0 < w) (hn : w^2 ≤ n) :
    Real.sqrt n ≤ ((n/w+1:ℕ):ℝ) := by
  have hw' : (w:ℝ) ≤ Real.sqrt n := (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
    (by exact_mod_cast hn)
  have hlen : n ≤ w*(n/w+1) := by
    have h := Nat.mod_add_div n w
    have hr := Nat.mod_lt n hw
    rw [Nat.mul_succ]
    omega
  have hmul : (n:ℝ) ≤ w*((n/w+1:ℕ):ℝ) := by exact_mod_cast hlen
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr ((Nat.pow_pos hw).trans_le hn))
  apply le_of_mul_le_mul_left _ hroot
  calc Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
       _ ≤ (w:ℝ)*((n/w+1:ℕ):ℝ) := hmul
       _ ≤ _ := mul_le_mul_of_nonneg_right hw' (Nat.cast_nonneg _)

/-- The date may grow with the prefix. Exponentially many sites in
the horizon suffice for the bad-event probability to decay as exp(-c√n). -/
theorem geometric_cut_overlap_tail {a η κ : ℝ} (ha : 0 < a) (hη : 0 < η) (hκ : 0 < κ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∃ c > 0, ∀ L : ℕ, 0 < L → ∀ n : ℕ, B^(2*L) ≤ n →
      ∀ t∈Icc a (L:ℝ), pathPauliDisorderLaw.real (cutOverlapEvent n t η κ) ≤
        (n:ℝ)*Real.exp (-c*Real.sqrt n) := by
  let p := η/4
  have hp : 0 < p := div_pos hη (by norm_num)
  have hq : 0 < p/8 := div_pos hp (by norm_num)
  obtain ⟨b,hb,hbond⟩ := geometric_bond_probability ha hq
  obtain ⟨r,d,g,hr,hd,hg,hg₁,k,hk,hpacket⟩ := geometric_packet_scale hb hκ
  obtain ⟨R,hR,hguard⟩ := geometric_weak_guards hg hg₁ hq
  obtain ⟨B,hB,hspace⟩ := geometric_packet_capacity R k hR hk hp
  refine ⟨B,hB,2*(p/8)^2,by positivity,?_⟩
  intro L hL n hn t ht
  obtain ⟨hbr,hgd,hdr,himp⟩ := hpacket L hL
  obtain ⟨hwidth,hroom,hboundary⟩ := hspace L hL n hn
  have hweak : 72*|t| *g^L ≤ d^L := by
    rw [abs_of_pos (ha.trans_le ht.1)]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 (by norm_num))
      (pow_pos hg _).le).trans hgd
  have hw₁ : 36*|t| *g^L ≤ d^L := by
    linarith only [hweak,mul_nonneg (abs_nonneg t) (pow_pos hg L).le]
  have hsub := cut_overlap_subset_bad (Nat.mul_pos (Nat.pow_pos hk) (Nat.pow_pos hk)) hdr hw₁ himp hroom
  have hbad := bad_center_bound hp (hweak.trans hdr.le) (hguard L hL) (n:=n) (t:=t)
  have hfull (e : Fin (n+1)) : pathPauliDisorderLaw.real
      {ω | |bondSignal e (pathPauliDisorderShell ω n) t| ≤ 3*r^L} ≤ p/8 := by
    apply (measureReal_mono (μ:=pathPauliDisorderLaw) (s₂:={ω | |bondSignal e (pathPauliDisorderShell ω n) t| ≤ b^L})
      (fun _ h => le_trans h hbr) (measure_ne_top _ _)).trans
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbond L hL n e t ht)).trans_eq
      (ENNReal.toReal_ofReal hq.le)
  apply ((measureReal_mono (μ:=pathPauliDisorderLaw) hsub (measure_ne_top _ _)).trans
    (hbad hfull hboundary)).trans
  let w := 2*R^L+2
  have hw : 0 < w := by dsimp only [w]; omega
  have hwn : w ≤ n := (le_self_pow₀ hw (by norm_num : 2 ≠ 0)).trans hwidth
  apply mul_le_mul (Nat.cast_le.mpr hwn) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (Nat.cast_nonneg _)
  simpa only [neg_mul] using neg_le_neg
    (mul_le_mul_of_nonneg_left (window_count hw hwidth) (by positivity : 0 ≤ 2*(p/8)^2))

#print axioms geometric_cut_overlap_tail
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
