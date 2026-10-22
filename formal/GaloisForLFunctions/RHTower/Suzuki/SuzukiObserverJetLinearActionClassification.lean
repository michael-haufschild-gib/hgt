import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetFormation
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# G-CE observer-jet linear-action classification

The literal completed harmonic source's absolute second-formation action is bounded linearly
exactly under the Riemann hypothesis. The new reverse estimate is a discrete Hardy–Green
transfer from the square-root Abel moment to every observer-jet history coordinate.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem observerJetSecondHistory_eq_weightedPrefix
    (r : ℕ → ℝ) (j : ℕ) :
    observerJetSecondHistory r j =
      ∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * r k := by
  induction j with
  | zero => simp [observerJetSecondHistory, observerJetPrefix]
  | succ j ih =>
      rw [observerJetSecondHistory_succ, ih]
      rw [observerJetPrefix]
      have hsumR : (∑ k ∈ Finset.range (j + 2), r k) =
          (∑ k ∈ Finset.range (j + 1), r k) + r (j + 1) := by
        simpa [show j + 2 = (j + 1) + 1 by omega] using
          (Finset.sum_range_succ r (j + 1))
      have hsumW : (∑ k ∈ Finset.range (j + 2),
          ((j + 2 - k : ℕ) : ℝ) * r k) =
          (∑ k ∈ Finset.range (j + 1),
            ((j + 2 - k : ℕ) : ℝ) * r k) + r (j + 1) := by
        rw [show j + 2 = (j + 1) + 1 by omega, Finset.sum_range_succ]
        norm_num
      calc
        (∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * r k) +
              ∑ k ∈ Finset.range (j + 2), r k =
            (∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * r k) +
              ((∑ k ∈ Finset.range (j + 1), r k) + r (j + 1)) := by
                rw [hsumR]
        _ = (∑ k ∈ Finset.range (j + 1),
              ((j + 2 - k : ℕ) : ℝ) * r k) + r (j + 1) := by
              rw [← add_assoc, ← Finset.sum_add_distrib]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.mem_range] at hk
              have hkj : k ≤ j := by omega
              have hsub : j + 2 - k = (j + 1 - k) + 1 := by omega
              rw [hsub]
              push_cast
              ring
        _ = ∑ k ∈ Finset.range (j + 2),
              ((j + 2 - k : ℕ) : ℝ) * r k := by
              rw [hsumW]

theorem observerJetResidual_history_eq_prefix_sub_mass_add_drift
    (q : ℕ → ℝ) (N j : ℕ) (_hN : 1 ≤ N) (hjN : j + 1 ≤ N) :
    observerJetSecondHistory (observerJetResidual q N) j =
      (∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * q k) -
        (j + 1 : ℕ) * observerJetMass q N + observerJetDrift q N := by
  rw [observerJetSecondHistory_eq_weightedPrefix]
  rcases j with _ | j
  · simp [observerJetResidual, observerJetAffinePart]
    ring
  · simp only [observerJetResidual, mul_sub, Finset.sum_sub_distrib]
    rw [show (∑ k ∈ Finset.range (j + 1 + 1),
        ((j + 1 + 1 - k : ℕ) : ℝ) * observerJetAffinePart q N k) =
        ((j + 2 : ℕ) : ℝ) * (observerJetMass q N - observerJetDrift q N) +
          ((j + 1 : ℕ) : ℝ) * observerJetDrift q N by
      let A := observerJetMass q N - observerJetDrift q N
      let D := observerJetDrift q N
      have hzero : (∑ k ∈ Finset.range (j + 2),
          ((j + 2 - k : ℕ) : ℝ) * (if k = 0 then A else 0)) =
          ((j + 2 : ℕ) : ℝ) * A := by
        simp_rw [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq']
        simp
      have hone : (∑ k ∈ Finset.range (j + 2),
          ((j + 2 - k : ℕ) : ℝ) * (if k = 1 then D else 0)) =
          ((j + 1 : ℕ) : ℝ) * D := by
        simp_rw [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq']
        simp
      change (∑ k ∈ Finset.range (j + 2),
          ((j + 2 - k : ℕ) : ℝ) * ((if k = 0 then A else 0) +
            (if k = 1 then D else 0))) = _
      rw [Finset.sum_congr rfl (fun k _ => mul_add _ _ _),
        Finset.sum_add_distrib, hzero, hone]
      ]
    push_cast
    ring_nf

theorem observerJetResidual_history_eq_tail
    (q : ℕ → ℝ) (N j : ℕ) (hN : 1 ≤ N) (hjN : j + 1 ≤ N) :
    observerJetSecondHistory (observerJetResidual q N) j =
      ∑ k ∈ Finset.Ico (j + 1) (N + 1),
        ((k - (j + 1) : ℕ) : ℝ) * q k := by
  rw [observerJetResidual_history_eq_prefix_sub_mass_add_drift q N j hN hjN]
  rw [observerJetMass, observerJetDrift]
  have hsplitQ := Finset.sum_range_add_sum_Ico q (show j + 1 ≤ N + 1 by omega)
  have hsplitK := Finset.sum_range_add_sum_Ico (fun k => (k : ℝ) * q k)
    (show j + 1 ≤ N + 1 by omega)
  rw [← hsplitQ, ← hsplitK]
  have hhead :
      (∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * q k) +
          (-(j + 1 : ℕ) * ∑ k ∈ Finset.range (j + 1), q k +
            ∑ k ∈ Finset.range (j + 1), (k : ℝ) * q k) = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hkj : k ≤ j := by omega
    rw [Nat.cast_sub (by omega : k ≤ j + 1)]
    push_cast
    ring
  have htail :
      (-((j + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.Ico (j + 1) (N + 1), q k +
        ∑ k ∈ Finset.Ico (j + 1) (N + 1), (k : ℝ) * q k) =
      ∑ k ∈ Finset.Ico (j + 1) (N + 1),
        ((k - (j + 1) : ℕ) : ℝ) * q k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Nat.cast_sub hk.1]
    push_cast
    ring
  calc
    (∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * q k) -
          ((j + 1 : ℕ) : ℝ) *
            ((∑ k ∈ Finset.range (j + 1), q k) +
              ∑ k ∈ Finset.Ico (j + 1) (N + 1), q k) +
        ((∑ k ∈ Finset.range (j + 1), (k : ℝ) * q k) +
          ∑ k ∈ Finset.Ico (j + 1) (N + 1), (k : ℝ) * q k) =
      ((∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * q k) +
          (-((j + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (j + 1), q k +
            ∑ k ∈ Finset.range (j + 1), (k : ℝ) * q k)) +
        (-((j + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.Ico (j + 1) (N + 1), q k +
          ∑ k ∈ Finset.Ico (j + 1) (N + 1), (k : ℝ) * q k) := by ring
    _ = _ := by rw [hhead, zero_add, htail]

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

def completedRieszInverseClockEdge (k : ℕ) : ℝ :=
  (Real.sqrt (k + 2 : ℕ) + Real.sqrt (k + 1 : ℕ)) /
    (((k + 1 : ℕ) : ℝ) * (k + 2 : ℕ))

def completedRieszSourceEdge (k : ℕ) : ℝ :=
  (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
    (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))

theorem harmonicCharge_eq_sourceEdge_mul_inverseClock (k : ℕ) :
    completedPrimePolarGammaHarmonicCharge k =
      completedRieszSourceEdge k * completedRieszInverseClockEdge k := by
  have h1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have h2 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
  have hs1 : Real.sqrt (k + 1 : ℕ) ^ (2 : ℕ) = (k + 1 : ℕ) :=
    Real.sq_sqrt h1.le
  have hs2 : Real.sqrt (k + 2 : ℕ) ^ (2 : ℕ) = (k + 2 : ℕ) :=
    Real.sq_sqrt h2.le
  rw [completedPrimePolarGammaHarmonicCharge]
  unfold completedRieszSourceEdge completedRieszInverseClockEdge
  have hgap : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
      1 / (((k + 1 : ℕ) : ℝ) * (k + 2 : ℕ)) := by
    push_cast
    field_simp [h1.ne', h2.ne']
    ring
  rw [hgap]
  have hprod :
      (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) *
          (Real.sqrt (k + 2 : ℕ) + Real.sqrt (k + 1 : ℕ)) = 1 := by
    calc
      _ = Real.sqrt (k + 2 : ℕ) ^ (2 : ℕ) - Real.sqrt (k + 1 : ℕ) ^ (2 : ℕ) := by ring
      _ = ((k + 2 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) := by rw [hs2, hs1]
      _ = 1 := by push_cast; ring
  symm
  calc
    (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
          (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) *
        ((Real.sqrt (k + 2 : ℕ) + Real.sqrt (k + 1 : ℕ)) /
          (((k + 1 : ℕ) : ℝ) * (k + 2 : ℕ))) =
      (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
        (((Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) *
          (Real.sqrt (k + 2 : ℕ) + Real.sqrt (k + 1 : ℕ))) /
            (((k + 1 : ℕ) : ℝ) * (k + 2 : ℕ))) := by ring
    _ = (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
        (1 / (((k + 1 : ℕ) : ℝ) * (k + 2 : ℕ))) := by rw [hprod]

theorem inverseClockEdge_nonneg (k : ℕ) :
    0 ≤ completedRieszInverseClockEdge k := by
  unfold completedRieszInverseClockEdge
  positivity

theorem inverseClockEdge_le (k : ℕ) :
    completedRieszInverseClockEdge k ≤
      2 / (((k + 1 : ℕ) : ℝ) * Real.sqrt (k + 1 : ℕ)) := by
  let a := Real.sqrt (k + 1 : ℕ)
  let b := Real.sqrt (k + 2 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have haa : a ^ (2 : ℕ) = ((k + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hbb : b ^ (2 : ℕ) = ((k + 2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  unfold completedRieszInverseClockEdge
  change (b + a) / (((k + 1 : ℕ) : ℝ) * (k + 2 : ℕ)) ≤
    2 / (((k + 1 : ℕ) : ℝ) * a)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [← haa, ← hbb]
  have hcore : (b + a) * a ≤ 2 * b ^ (2 : ℕ) := by
    calc
      (b + a) * a = a * (a + b) := by ring
      _ ≤ b * (a + b) := mul_le_mul_of_nonneg_right hab (by positivity)
      _ ≤ b * (b + b) := mul_le_mul_of_nonneg_left
        (add_le_add hab (le_refl b)) hb.le
      _ = 2 * b ^ (2 : ℕ) := by ring
  calc
    (b + a) * (a ^ (2 : ℕ) * a) = a ^ (2 : ℕ) * ((b + a) * a) := by ring
    _ ≤ a ^ (2 : ℕ) * (2 * b ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcore (sq_nonneg a)
    _ = 2 * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) := by ring

theorem abs_inverseClockEdge_succ_sub_le (k : ℕ) :
    |completedRieszInverseClockEdge (k + 1) -
        completedRieszInverseClockEdge k| ≤
      3 / (Real.sqrt (k + 1 : ℕ)) ^ (5 : ℕ) := by
  let a := Real.sqrt (k + 1 : ℕ)
  let b := Real.sqrt (k + 2 : ℕ)
  let c := Real.sqrt (k + 3 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have hbc : b ≤ c := Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))
  have hac : a ≤ c := hab.trans hbc
  have haa : a ^ (2 : ℕ) = ((k + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hbb : b ^ (2 : ℕ) = ((k + 2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hcc : c ^ (2 : ℕ) = ((k + 3 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hca : c - a = 2 / (c + a) := by
    apply (eq_div_iff (by positivity : c + a ≠ 0)).2
    calc
      (c - a) * (c + a) = c ^ (2 : ℕ) - a ^ (2 : ℕ) := by ring
      _ = ((k + 3 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) := by rw [hcc, haa]
      _ = 2 := by push_cast; ring
  have hca0 : 0 ≤ c - a := sub_nonneg.mpr hac
  have hca_le : c - a ≤ 1 / a := by
    rw [hca]
    apply (div_le_div_iff₀ (by positivity : 0 < c + a) ha).2
    nlinarith
  have hbracket0 : 0 ≤ a * c + b * (c + a) := by positivity
  have hbracket : a * c + b * (c + a) ≤ 3 * c ^ (2 : ℕ) := by
    have hacmul : a * c ≤ c * c := mul_le_mul_of_nonneg_right hac hc.le
    have hbc1 : b * c ≤ c * c := mul_le_mul_of_nonneg_right hbc hc.le
    have hba : b * a ≤ c * c := by nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hab)]
    nlinarith
  have hfactor :
      (completedRieszInverseClockEdge k -
          completedRieszInverseClockEdge (k + 1)) =
        (c - a) * (a * c + b * (c + a)) / (a ^ (2 : ℕ) * b ^ (2 : ℕ) * c ^ (2 : ℕ)) := by
    have hr0 : completedRieszInverseClockEdge k =
        (a + b) / (a ^ (2 : ℕ) * b ^ (2 : ℕ)) := by
      unfold completedRieszInverseClockEdge
      rw [haa, hbb]
      ring
    have hr1 : completedRieszInverseClockEdge (k + 1) =
        (b + c) / (b ^ (2 : ℕ) * c ^ (2 : ℕ)) := by
      unfold completedRieszInverseClockEdge
      rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega,
        hbb, hcc]
      ring
    rw [hr0, hr1]
    field_simp [ha.ne', hb.ne', hc.ne']
    ring
  have hfactor0 : 0 ≤ completedRieszInverseClockEdge k -
      completedRieszInverseClockEdge (k + 1) := by
    rw [hfactor]
    positivity
  rw [abs_sub_comm, abs_of_nonneg hfactor0, hfactor]
  have hnum : (c - a) * (a * c + b * (c + a)) ≤ 3 * c ^ (2 : ℕ) / a := by
    calc
      _ ≤ (1 / a) * (3 * c ^ (2 : ℕ)) :=
        mul_le_mul hca_le hbracket hbracket0 (by positivity)
      _ = 3 * c ^ (2 : ℕ) / a := by ring
  have hden0 : 0 < a ^ (2 : ℕ) * b ^ (2 : ℕ) * c ^ (2 : ℕ) := by positivity
  calc
    (c - a) * (a * c + b * (c + a)) / (a ^ (2 : ℕ) * b ^ (2 : ℕ) * c ^ (2 : ℕ)) ≤
        (3 * c ^ (2 : ℕ) / a) / (a ^ (2 : ℕ) * b ^ (2 : ℕ) * c ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_right hnum hden0.le
    _ = 3 / (a ^ (3 : ℕ) * b ^ (2 : ℕ)) := by field_simp [ha.ne', hb.ne', hc.ne']
    _ ≤ 3 / a ^ (5 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity : 0 < a ^ (3 : ℕ) * b ^ (2 : ℕ)) (by positivity : 0 < a ^ (5 : ℕ))]
      have hab2 : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ) := by nlinarith
      calc
        3 * a ^ (5 : ℕ) = 3 * (a ^ (3 : ℕ) * a ^ (2 : ℕ)) := by ring
        _ ≤ 3 * (a ^ (3 : ℕ) * b ^ (2 : ℕ)) := by gcongr

def completedRieszTailKernel (j k : ℕ) : ℝ :=
  ((k - (j + 1) : ℕ) : ℝ) * completedRieszInverseClockEdge k

def completedRieszDriftKernel (k : ℕ) : ℝ :=
  (k : ℝ) * completedRieszInverseClockEdge k

theorem abs_tailKernel_le (j k : ℕ) :
    |completedRieszTailKernel j k| ≤
      2 / Real.sqrt (k + 1 : ℕ) := by
  have hs : 0 < Real.sqrt (k + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have hr0 := inverseClockEdge_nonneg k
  have hr := inverseClockEdge_le k
  have hsub : ((k - (j + 1) : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k (j + 1)
  have hsub0 : 0 ≤ ((k - (j + 1) : ℕ) : ℝ) := by positivity
  rw [completedRieszTailKernel, abs_of_nonneg (mul_nonneg hsub0 hr0)]
  calc
    ((k - (j + 1) : ℕ) : ℝ) * completedRieszInverseClockEdge k ≤
        (k : ℝ) * completedRieszInverseClockEdge k :=
      mul_le_mul_of_nonneg_right hsub hr0
    _ ≤ (k : ℝ) *
        (2 / (((k + 1 : ℕ) : ℝ) * Real.sqrt (k + 1 : ℕ))) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ 2 / Real.sqrt (k + 1 : ℕ) := by
      apply (le_div_iff₀ hs).2
      have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      field_simp [hk1.ne', hs.ne']
      have hle : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
      nlinarith

theorem abs_driftKernel_le (k : ℕ) :
    |completedRieszDriftKernel k| ≤
      2 / Real.sqrt (k + 1 : ℕ) := by
  have hs : 0 < Real.sqrt (k + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have hr0 := inverseClockEdge_nonneg k
  have hr := inverseClockEdge_le k
  rw [completedRieszDriftKernel, abs_of_nonneg (mul_nonneg (by positivity) hr0)]
  calc
    (k : ℝ) * completedRieszInverseClockEdge k ≤
        (k : ℝ) *
          (2 / (((k + 1 : ℕ) : ℝ) * Real.sqrt (k + 1 : ℕ))) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ 2 / Real.sqrt (k + 1 : ℕ) := by
      apply (le_div_iff₀ hs).2
      have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      field_simp [hk1.ne', hs.ne']
      have hle : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
      nlinarith

private theorem inverseClockEdge_succ_le_cube (k : ℕ) :
    completedRieszInverseClockEdge (k + 1) ≤
      2 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) := by
  have h := inverseClockEdge_le (k + 1)
  let a := Real.sqrt (k + 1 : ℕ)
  let b := Real.sqrt (k + 2 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have haa : a ^ (2 : ℕ) = ((k + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hbb : b ^ (2 : ℕ) = ((k + 2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  rw [show k + 1 + 1 = k + 2 by omega] at h
  change completedRieszInverseClockEdge (k + 1) ≤ 2 / a ^ (3 : ℕ)
  refine h.trans ?_
  change 2 / (((k + 2 : ℕ) : ℝ) * b) ≤ 2 / a ^ (3 : ℕ)
  rw [← hbb]
  apply (div_le_div_iff₀ (by positivity : 0 < b ^ (2 : ℕ) * b)
    (by positivity : 0 < a ^ (3 : ℕ))).2
  have hcub : a ^ (3 : ℕ) ≤ b ^ (3 : ℕ) := by gcongr
  nlinarith

private theorem nat_mul_inverseClockEdge_diff_le_cube (k d : ℕ) (hdk : d ≤ k) :
    (d : ℝ) * |completedRieszInverseClockEdge (k + 1) -
        completedRieszInverseClockEdge k| ≤
      3 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) := by
  let a := Real.sqrt (k + 1 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have haa : a ^ (2 : ℕ) = ((k + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hd : (d : ℝ) ≤ a ^ (2 : ℕ) := by
    rw [haa]
    exact_mod_cast hdk.trans (Nat.le_succ k)
  have hdiff := abs_inverseClockEdge_succ_sub_le k
  change (d : ℝ) * _ ≤ 3 / a ^ (3 : ℕ)
  calc
    (d : ℝ) * |completedRieszInverseClockEdge (k + 1) -
        completedRieszInverseClockEdge k| ≤
      (d : ℝ) * (3 / a ^ (5 : ℕ)) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ ≤ a ^ (2 : ℕ) * (3 / a ^ (5 : ℕ)) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = 3 / a ^ (3 : ℕ) := by field_simp [ha.ne']

theorem abs_tailKernel_sub_succ_le (j k : ℕ) :
    |completedRieszTailKernel j k -
        completedRieszTailKernel j (k + 1)| ≤
      5 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) := by
  by_cases hk : k ≤ j
  · have hk0 : k - (j + 1) = 0 := by omega
    have hk1 : k + 1 - (j + 1) = 0 := by omega
    simp [completedRieszTailKernel, hk0, hk1]
    positivity
  · have hjk : j + 1 ≤ k := by omega
    let d := k - (j + 1)
    have hd : d ≤ k := Nat.sub_le k (j + 1)
    have hsucc : k + 1 - (j + 1) = d + 1 := by omega
    have hshape : completedRieszTailKernel j k -
          completedRieszTailKernel j (k + 1) =
        -(completedRieszInverseClockEdge (k + 1) +
          (d : ℝ) * (completedRieszInverseClockEdge (k + 1) -
            completedRieszInverseClockEdge k)) := by
      unfold completedRieszTailKernel
      rw [hsucc]
      change (d : ℝ) * completedRieszInverseClockEdge k -
        ((d + 1 : ℕ) : ℝ) * completedRieszInverseClockEdge (k + 1) = _
      push_cast
      ring
    rw [hshape, abs_neg]
    calc
      |completedRieszInverseClockEdge (k + 1) +
          (d : ℝ) * (completedRieszInverseClockEdge (k + 1) -
            completedRieszInverseClockEdge k)| ≤
        |completedRieszInverseClockEdge (k + 1)| +
          |(d : ℝ) * (completedRieszInverseClockEdge (k + 1) -
            completedRieszInverseClockEdge k)| := abs_add_le _ _
      _ = completedRieszInverseClockEdge (k + 1) +
          (d : ℝ) * |completedRieszInverseClockEdge (k + 1) -
            completedRieszInverseClockEdge k| := by
        rw [abs_of_nonneg (inverseClockEdge_nonneg _), abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ (d : ℝ))]
      _ ≤ 2 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) +
          3 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) :=
        add_le_add (inverseClockEdge_succ_le_cube k)
          (nat_mul_inverseClockEdge_diff_le_cube k d hd)
      _ = 5 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) := by ring

theorem abs_driftKernel_sub_succ_le (k : ℕ) :
    |completedRieszDriftKernel k -
        completedRieszDriftKernel (k + 1)| ≤
      5 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) := by
  have hshape : completedRieszDriftKernel k -
        completedRieszDriftKernel (k + 1) =
      -(completedRieszInverseClockEdge (k + 1) +
        (k : ℝ) * (completedRieszInverseClockEdge (k + 1) -
          completedRieszInverseClockEdge k)) := by
    unfold completedRieszDriftKernel
    push_cast
    ring
  rw [hshape, abs_neg]
  calc
    |completedRieszInverseClockEdge (k + 1) +
        (k : ℝ) * (completedRieszInverseClockEdge (k + 1) -
          completedRieszInverseClockEdge k)| ≤
      |completedRieszInverseClockEdge (k + 1)| +
        |(k : ℝ) * (completedRieszInverseClockEdge (k + 1) -
          completedRieszInverseClockEdge k)| := abs_add_le _ _
    _ = completedRieszInverseClockEdge (k + 1) +
        (k : ℝ) * |completedRieszInverseClockEdge (k + 1) -
          completedRieszInverseClockEdge k| := by
      rw [abs_of_nonneg (inverseClockEdge_nonneg _), abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (k : ℝ))]
    _ ≤ 2 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) +
        3 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) :=
      add_le_add (inverseClockEdge_succ_le_cube k)
        (nat_mul_inverseClockEdge_diff_le_cube k k (le_refl k))
    _ = 5 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) := by ring

theorem observerJetPrefix_sourceEdge_eq_mobiusMoment (N : ℕ) :
    observerJetPrefix completedRieszSourceEdge N =
      mobiusDivisorSquareRootAbelMoment (N + 2) := by
  rw [observerJetPrefix]
  symm
  simpa [completedRieszSourceEdge] using
    (mobiusDivisorSquareRootAbelMoment_eq_completedPrefixMesh
      (M := N + 2) (by omega : 1 ≤ N + 2))

theorem sourceEdge_prefix_linearBound
    {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ M : ℕ, 2 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M / M| ≤ B)
    (N : ℕ) :
    |observerJetPrefix completedRieszSourceEdge N| ≤ B * (N + 2 : ℕ) := by
  rw [observerJetPrefix_sourceEdge_eq_mobiusMoment]
  have h := hbound (N + 2) (by omega)
  have hpos : (0 : ℝ) < (N + 2 : ℕ) := by positivity
  have heq : |mobiusDivisorSquareRootAbelMoment (N + 2)| =
      |mobiusDivisorSquareRootAbelMoment (N + 2) / (N + 2 : ℕ)| *
        (N + 2 : ℕ) := by
    rw [abs_div, abs_of_pos hpos]
    field_simp [hpos.ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_right h hpos.le

private theorem succ_add_one_div_sqrt_cube_le (k : ℕ) :
    ((k + 2 : ℕ) : ℝ) /
        (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ) ≤
      2 / Real.sqrt (k + 1 : ℕ) := by
  let a := Real.sqrt (k + 1 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have haa : a ^ (2 : ℕ) = ((k + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  change ((k + 2 : ℕ) : ℝ) / a ^ (3 : ℕ) ≤ 2 / a
  apply (div_le_div_iff₀ (by positivity : 0 < a ^ (3 : ℕ)) ha).2
  rw [show ((k + 2 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    ← haa]
  have ha1 : 1 ≤ a ^ (2 : ℕ) := by rw [haa]; exact_mod_cast (show 1 ≤ k + 1 by omega)
  nlinarith [sq_nonneg a]

private theorem prefix_mul_kernelDiff_le
    {B : ℝ} (_hB : 0 ≤ B)
    (hprefix : ∀ k, |observerJetPrefix completedRieszSourceEdge k| ≤
      B * (k + 2 : ℕ))
    (w : ℕ → ℝ)
    (hdiff : ∀ k, |w k - w (k + 1)| ≤
      5 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ))
    (k : ℕ) :
    |observerJetPrefix completedRieszSourceEdge k * (w k - w (k + 1))| ≤
      10 * B * (1 / Real.sqrt (k + 1 : ℕ)) := by
  rw [abs_mul]
  calc
    |observerJetPrefix completedRieszSourceEdge k| * |w k - w (k + 1)| ≤
      (B * (k + 2 : ℕ)) *
        (5 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ)) :=
      mul_le_mul (hprefix k) (hdiff k) (abs_nonneg _) (by positivity)
    _ = 5 * B * (((k + 2 : ℕ) : ℝ) /
        (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ)) := by ring
    _ ≤ 5 * B * (2 / Real.sqrt (k + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left (succ_add_one_div_sqrt_cube_le k) (by positivity)
    _ = 10 * B * (1 / Real.sqrt (k + 1 : ℕ)) := by ring

private theorem prefix_mul_kernel_boundary_le
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ k, |observerJetPrefix completedRieszSourceEdge k| ≤
      B * (k + 2 : ℕ))
    (w : ℕ → ℝ)
    (hvalue : ∀ k, |w k| ≤ 2 / Real.sqrt (k + 1 : ℕ))
    (N : ℕ) :
    |observerJetPrefix completedRieszSourceEdge N * w N| ≤
      4 * B * Real.sqrt (N + 1 : ℕ) := by
  let a := Real.sqrt (N + 1 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have haa : a ^ (2 : ℕ) = ((N + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  rw [abs_mul]
  calc
    |observerJetPrefix completedRieszSourceEdge N| * |w N| ≤
      (B * (N + 2 : ℕ)) * (2 / Real.sqrt (N + 1 : ℕ)) :=
        mul_le_mul (hprefix N) (hvalue N) (abs_nonneg _) (by positivity)
    _ ≤ 4 * B * Real.sqrt (N + 1 : ℕ) := by
      change (B * ((N + 2 : ℕ) : ℝ)) * (2 / a) ≤ 4 * B * a
      have hNshape : ((N + 2 : ℕ) : ℝ) = a ^ (2 : ℕ) + 1 := by
        rw [haa]
        push_cast
        ring
      rw [hNshape]
      have ha1 : 1 ≤ a ^ (2 : ℕ) := by rw [haa]; exact_mod_cast (show 1 ≤ N + 1 by omega)
      rw [show B * (a ^ (2 : ℕ) + 1) * (2 / a) = B * ((a ^ (2 : ℕ) + 1) * (2 / a)) by ring,
        show 4 * B * a = B * (4 * a) by ring]
      apply mul_le_mul_of_nonneg_left _ hB
      field_simp [ha.ne']
      nlinarith

theorem abs_sourceEdge_sum_mul_le
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ k, |observerJetPrefix completedRieszSourceEdge k| ≤
      B * (k + 2 : ℕ))
    (w : ℕ → ℝ)
    (hvalue : ∀ k, |w k| ≤ 2 / Real.sqrt (k + 1 : ℕ))
    (hdiff : ∀ k, |w k - w (k + 1)| ≤
      5 / (Real.sqrt (k + 1 : ℕ)) ^ (3 : ℕ))
    (N : ℕ) :
    |∑ k ∈ Finset.range (N + 1), completedRieszSourceEdge k * w k| ≤
      24 * B * Real.sqrt (N + 1 : ℕ) := by
  have habel := observerJetAbelSummation completedRieszSourceEdge w N
  rw [habel]
  have hboundary := prefix_mul_kernel_boundary_le hB hprefix w hvalue N
  have hterm := prefix_mul_kernelDiff_le hB hprefix w hdiff
  have hsum : (∑ k ∈ Finset.range N,
      1 / Real.sqrt (k + 1 : ℕ)) ≤ 2 * Real.sqrt N := by
    have h := sum_one_div_sqrt_le N
    rw [sum_Icc_eq_sum_range_shift] at h
    simpa only using h
  have hinterior :
      (∑ k ∈ Finset.range N,
        |observerJetPrefix completedRieszSourceEdge k * (w k - w (k + 1))|) ≤
      20 * B * Real.sqrt N := by
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          10 * B * (1 / Real.sqrt (k + 1 : ℕ)) :=
        Finset.sum_le_sum fun k _ => hterm k
      _ = 10 * B * (∑ k ∈ Finset.range N,
          1 / Real.sqrt (k + 1 : ℕ)) := by rw [Finset.mul_sum]
      _ ≤ 10 * B * (2 * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 20 * B * Real.sqrt N := by ring
  have hsqrt : Real.sqrt N ≤ Real.sqrt (N + 1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show N ≤ N + 1 by omega))
  calc
    |observerJetPrefix completedRieszSourceEdge N * w N +
        ∑ n ∈ Finset.range N,
          observerJetPrefix completedRieszSourceEdge n * (w n - w (n + 1))| ≤
      |observerJetPrefix completedRieszSourceEdge N * w N| +
        |∑ n ∈ Finset.range N,
          observerJetPrefix completedRieszSourceEdge n * (w n - w (n + 1))| :=
      abs_add_le _ _
    _ ≤ |observerJetPrefix completedRieszSourceEdge N * w N| +
        ∑ n ∈ Finset.range N,
          |observerJetPrefix completedRieszSourceEdge n * (w n - w (n + 1))| :=
      add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 4 * B * Real.sqrt (N + 1 : ℕ) + 20 * B * Real.sqrt N :=
      add_le_add hboundary hinterior
    _ ≤ 4 * B * Real.sqrt (N + 1 : ℕ) +
        20 * B * Real.sqrt (N + 1 : ℕ) := by
      gcongr
    _ = 24 * B * Real.sqrt (N + 1 : ℕ) := by ring

theorem completedSourceObserverJetDrift_eq_sourceEdge_kernel
    {M : ℕ} (hM : 3 ≤ M) :
    completedSourceObserverJetDrift M =
      ∑ k ∈ Finset.range (M - 1),
        completedRieszSourceEdge k * completedRieszDriftKernel k := by
  unfold completedSourceObserverJetDrift observerJetDrift
  have hlen : M - 2 + 1 = M - 1 := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [harmonicCharge_eq_sourceEdge_mul_inverseClock]
  unfold completedRieszDriftKernel
  ring

theorem completedSourceObserverJetHistory_eq_sourceEdge_tailKernel
    {M j : ℕ} (hM : 3 ≤ M) (hj : j ∈ Finset.range (M - 3)) :
    completedSourceObserverJetHistory M j =
      ∑ k ∈ Finset.range (M - 1),
        completedRieszSourceEdge k * completedRieszTailKernel j k := by
  have hN : 1 ≤ M - 2 := by omega
  have hjN : j + 1 ≤ M - 2 := by
    rw [Finset.mem_range] at hj
    omega
  unfold completedSourceObserverJetHistory
  rw [GaloisForLFunctions.HTGeometry.observerJetResidual_history_eq_tail
    completedPrimePolarGammaHarmonicCharge (M - 2) j hN hjN]
  have htop : M - 2 + 1 = M - 1 := by omega
  rw [htop]
  have htail :
      (∑ k ∈ Finset.Ico (j + 1) (M - 1),
          ((k - (j + 1) : ℕ) : ℝ) * completedPrimePolarGammaHarmonicCharge k) =
      ∑ k ∈ Finset.Ico (j + 1) (M - 1),
          completedRieszSourceEdge k * completedRieszTailKernel j k := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [harmonicCharge_eq_sourceEdge_mul_inverseClock]
    unfold completedRieszTailKernel
    ring
  rw [htail]
  have hhead : (∑ k ∈ Finset.range (j + 1),
      completedRieszSourceEdge k * completedRieszTailKernel j k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hzero : k - (j + 1) = 0 := by omega
    simp [completedRieszTailKernel, hzero]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k => completedRieszSourceEdge k * completedRieszTailKernel j k)
    (show j + 1 ≤ M - 1 by omega)
  rw [hhead, zero_add] at hsplit
  exact hsplit

theorem abs_completedSourceObserverJetDrift_le
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ k, |observerJetPrefix completedRieszSourceEdge k| ≤
      B * (k + 2 : ℕ))
    {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetDrift M| ≤
      24 * B * Real.sqrt (M - 1 : ℕ) := by
  rw [completedSourceObserverJetDrift_eq_sourceEdge_kernel hM]
  have hN : M - 1 = (M - 2) + 1 := by omega
  rw [hN]
  exact abs_sourceEdge_sum_mul_le hB hprefix completedRieszDriftKernel
    abs_driftKernel_le abs_driftKernel_sub_succ_le (M - 2)

theorem abs_completedSourceObserverJetHistory_le
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ k, |observerJetPrefix completedRieszSourceEdge k| ≤
      B * (k + 2 : ℕ))
    {M j : ℕ} (hM : 3 ≤ M) (hj : j ∈ Finset.range (M - 3)) :
    |completedSourceObserverJetHistory M j| ≤
      24 * B * Real.sqrt (M - 1 : ℕ) := by
  rw [completedSourceObserverJetHistory_eq_sourceEdge_tailKernel hM hj]
  have hN : M - 1 = (M - 2) + 1 := by omega
  rw [hN]
  exact abs_sourceEdge_sum_mul_le hB hprefix (completedRieszTailKernel j)
    (abs_tailKernel_le j) (abs_tailKernel_sub_succ_le j) (M - 2)

private theorem sqrt_sub_mul_sqrt_sub_le
    {M : ℕ} (hM : 3 ≤ M) :
    Real.sqrt (M - 1 : ℕ) * Real.sqrt (M - 3 : ℕ) ≤ (M : ℝ) := by
  have h1 : Real.sqrt (M - 1 : ℕ) ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show M - 1 ≤ M by omega))
  have h3 : Real.sqrt (M - 3 : ℕ) ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show M - 3 ≤ M by omega))
  have hs0 : 0 ≤ Real.sqrt (M - 3 : ℕ) := Real.sqrt_nonneg _
  have hsM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hmul : Real.sqrt (M - 1 : ℕ) * Real.sqrt (M - 3 : ℕ) ≤
      Real.sqrt M * Real.sqrt M := mul_le_mul h1 h3 hs0 hsM0
  rw [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ M)] at hmul
  exact hmul

theorem completedSourceObserverJetWeightedAction_le
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ k, |observerJetPrefix completedRieszSourceEdge k| ≤
      B * (k + 2 : ℕ))
    {M : ℕ} (hM : 3 ≤ M) :
    completedSourceObserverJetWeightedAction M ≤ 72 * B * M := by
  have hdrift := abs_completedSourceObserverJetDrift_le hB hprefix hM
  have hsqrtM : Real.sqrt (M - 1 : ℕ) ≤ (M : ℝ) := by
    have hs : Real.sqrt (M - 1 : ℕ) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt (by exact_mod_cast (show M - 1 ≤ M by omega))
    have hsM : Real.sqrt M ≤ (M : ℝ) := by
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity), Real.sqrt_nonneg (M : ℝ)]
    exact hs.trans hsM
  have hdrift' : |completedSourceObserverJetDrift M| ≤ 24 * B * M := by
    exact hdrift.trans (mul_le_mul_of_nonneg_left hsqrtM (by positivity))
  have hsumInv : (∑ j ∈ Finset.range (M - 3),
      1 / Real.sqrt (j + 1 : ℕ)) ≤ 2 * Real.sqrt (M - 3 : ℕ) := by
    have h := sum_one_div_sqrt_le (M - 3)
    rw [sum_Icc_eq_sum_range_shift] at h
    simpa only using h
  have hhistory :
      (∑ j ∈ Finset.range (M - 3),
        |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ)) ≤
      48 * B * M := by
    calc
      _ ≤ ∑ j ∈ Finset.range (M - 3),
          (24 * B * Real.sqrt (M - 1 : ℕ)) *
            (1 / Real.sqrt (j + 1 : ℕ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hs : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
        have hh := abs_completedSourceObserverJetHistory_le hB hprefix hM hj
        calc
          |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ) ≤
              (24 * B * Real.sqrt (M - 1 : ℕ)) /
                Real.sqrt (j + 1 : ℕ) := div_le_div_of_nonneg_right hh hs.le
          _ = (24 * B * Real.sqrt (M - 1 : ℕ)) *
                (1 / Real.sqrt (j + 1 : ℕ)) := by ring
      _ = (24 * B * Real.sqrt (M - 1 : ℕ)) *
          (∑ j ∈ Finset.range (M - 3),
            1 / Real.sqrt (j + 1 : ℕ)) := by rw [Finset.mul_sum]
      _ ≤ (24 * B * Real.sqrt (M - 1 : ℕ)) *
          (2 * Real.sqrt (M - 3 : ℕ)) :=
        mul_le_mul_of_nonneg_left hsumInv (by positivity)
      _ = 48 * B *
          (Real.sqrt (M - 1 : ℕ) * Real.sqrt (M - 3 : ℕ)) := by ring
      _ ≤ 48 * B * M :=
        mul_le_mul_of_nonneg_left (sqrt_sub_mul_sqrt_sub_le hM) (by positivity)
  unfold completedSourceObserverJetWeightedAction
  calc
    |completedSourceObserverJetDrift M| +
        ∑ j ∈ Finset.range (M - 3),
          |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ) ≤
      24 * B * M + 48 * B * M := add_le_add hdrift' hhistory
    _ = 72 * B * M := by ring

theorem completedSourceObserverJetLinearActionBounded_of_mobius
    (hsource : MobiusDivisorSquareRootAbelBounded) :
    CompletedSourceObserverJetLinearActionBounded := by
  rcases hsource with ⟨B, hB, hbound⟩
  have hprefix := sourceEdge_prefix_linearBound hB hbound
  refine ⟨72 * B, by positivity, ?_⟩
  intro M hM
  exact completedSourceObserverJetWeightedAction_le hB hprefix hM

end


end RHTower

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

theorem completedSourceObserverJetLinearActionBounded_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    CompletedSourceObserverJetLinearActionBounded :=
  _root_.RHTower.completedSourceObserverJetLinearActionBounded_of_mobius
    (riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded.mp hRH)

/-- The strongest absolute observer-jet action producer is exactly RH. -/
theorem completedSourceObserverJetLinearActionBounded_iff_riemannHypothesis :
    CompletedSourceObserverJetLinearActionBounded ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_completedSourceObserverJetLinearActionBounded
  · exact completedSourceObserverJetLinearActionBounded_of_riemannHypothesis

end GaloisForLFunctions.RHTower
