import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetObservation
import GaloisForLFunctions.HTGeometry.JetObservationGenericity
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The exponential mass parameter observes jets locally surjectively

Bounded sequences of exponential mass parameters are a Banach space, and a perturbation supported on
finitely many coordinates is small there.  Rescaling those coordinates by factors close to one is
exactly a small move of the parameter, and it already realizes every jet packet near the current one.

So the jet packet is a locally surjective observation of the mass parameter, and countably many
polynomial constraints on it fail on a residual set of parameters.
-/

open Filter Topology MeasureTheory
open _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Bounded real sequences: the exponential mass parameter space. -/
abbrev MassParameter := lp (fun _ : ℕ => ℝ) ⊤

/-- The perturbation supported on finitely many coordinates. -/
def pertSeq {K : ℕ} (a : Fin K → ℕ) (s : Fin K → ℝ) (n : ℕ) : ℝ :=
  ∑ k, if a k = n then s k else 0

theorem pertSeq_of_notMem {K : ℕ} {a : Fin K → ℕ} (s : Fin K → ℝ) {n : ℕ}
    (hn : ∀ k, a k ≠ n) : pertSeq a s n = 0 :=
  Finset.sum_eq_zero fun k _ => if_neg (hn k)

theorem pertSeq_apply {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a) (s : Fin K → ℝ)
    (k : Fin K) : pertSeq a s (a k) = s k := by
  rw [pertSeq, Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro b _ hb
    exact if_neg fun h => hb (ha h)
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem abs_pertSeq_le {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a) {s : Fin K → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hs : ∀ k, |s k| ≤ c) (n : ℕ) : |pertSeq a s n| ≤ c := by
  classical
  by_cases hn : ∃ k, a k = n
  · obtain ⟨k, rfl⟩ := hn
    rw [pertSeq_apply ha s k]
    exact hs k
  · push Not at hn
    rw [pertSeq_of_notMem s hn, abs_zero]
    exact hc

theorem perturbedWeight_eq_expParameter {K : ℕ} (a : Fin K → ℕ) (s : Fin K → ℝ) (ε : ℕ → ℝ)
    (v : ℕ → ℝ) (n : ℕ) :
    perturbedWeight a s (fun m => ε m * Real.exp (v m)) n
      = ε n * Real.exp (v n + pertSeq a s n) := by
  rw [perturbedWeight, pertSeq, Real.exp_add]
  ring

/-- The finitely supported perturbation, as a bounded sequence. -/
def pertParameter {K : ℕ} (a : Fin K → ℕ) (s : Fin K → ℝ) (ha : Function.Injective a)
    {c : ℝ} (hc : 0 ≤ c) (hs : ∀ k, |s k| ≤ c) : MassParameter :=
  ⟨pertSeq a s, memℓp_infty ⟨c, by
    rintro y ⟨n, rfl⟩
    simpa [Real.norm_eq_abs] using abs_pertSeq_le ha hc hs n⟩⟩

theorem norm_pertParameter_le {K : ℕ} {a : Fin K → ℕ} {s : Fin K → ℝ}
    (ha : Function.Injective a) {c : ℝ} (hc : 0 ≤ c) (hs : ∀ k, |s k| ≤ c) :
    ‖pertParameter a s ha hc hs‖ ≤ c := by
  refine lp.norm_le_of_forall_le hc fun n => ?_
  simpa [pertParameter, Real.norm_eq_abs] using abs_pertSeq_le ha hc hs n

theorem summable_expParameter {ε : ℕ → ℝ} (hεnn : ∀ n, 0 ≤ ε n) (hε : Summable ε)
    (u : MassParameter) : Summable fun n => ε n * Real.exp (u n) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hεnn n) (Real.exp_nonneg _))
    (fun n => ?_) (hε.mul_right (Real.exp ‖u‖))
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hεnn n)
  have hle : ‖(u : ℕ → ℝ) n‖ ≤ ‖u‖ := lp.norm_apply_le_norm (by simp) u n
  rw [Real.norm_eq_abs] at hle
  exact le_trans (le_abs_self _) hle

/-- **The jet packet is a locally surjective observation of the exponential mass parameter.** -/
theorem locallySurjective_discreteJetObservation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodesinj : Function.Injective nodes) (hupper : ∀ i, 0 < (nodes i).im)
    (ord : ι → ℕ) (x : ℕ → ℝ) (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε) :
    LocallySurjectiveObservation
      (fun u : MassParameter =>
        discreteJetPacket nodes ord x fun n => ε n * Real.exp (u n)) := by
  classical
  intro u N hN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hN
  have hwpos : ∀ n, 0 < ε n * Real.exp (u n) := fun n => mul_pos (hεpos n) (Real.exp_pos _)
  have hwsum : Summable fun n => ε n * Real.exp (u n) :=
    summable_expParameter (fun n => (hεpos n).le) hε u
  obtain ⟨K, a, ha, hreach⟩ := exists_discreteJetPacket_reach nodes hnodesinj hupper ord x hx
    (w := fun n => ε n * Real.exp (u n)) hwpos hwsum (δ := δ / 2) (by linarith)
  refine Filter.mem_of_superset hreach fun y hy => ?_
  obtain ⟨s, hs, rfl⟩ := hy
  have hsle : ∀ k, |s k| ≤ δ / 2 := fun k => (hs k).le
  have hc : (0 : ℝ) ≤ δ / 2 := by linarith
  refine ⟨u + pertParameter a s ha hc hsle, ?_, ?_⟩
  · refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm := norm_pertParameter_le ha hc hsle
    simpa using lt_of_le_of_lt hnorm (by linarith)
  · have hcoe : ∀ n, ((u + pertParameter a s ha hc hsle : MassParameter) : ℕ → ℝ) n
        = (u : ℕ → ℝ) n + pertSeq a s n := by
      intro n
      rw [lp.coeFn_add]
      rfl
    have hweq : (fun n =>
          ε n * Real.exp (((u + pertParameter a s ha hc hsle : MassParameter) : ℕ → ℝ) n))
        = perturbedWeight a s fun n => ε n * Real.exp ((u : ℕ → ℝ) n) := by
      funext n
      rw [hcoe n, perturbedWeight_eq_expParameter]
    exact congrArg (discreteJetPacket nodes ord x) hweq

end

end GaloisForLFunctions.HTGeometry
