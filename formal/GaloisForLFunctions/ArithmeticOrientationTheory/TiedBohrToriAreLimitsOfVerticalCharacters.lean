import GaloisForLFunctions.ArithmeticOrientationTheory.AKernelBoundedBelowOnTheHalfPlaneIsAUnit
import GaloisForLFunctions.HTGeometry.LSeriesRightLimit

/-!
# Tied Bohr tori are limits of vertical characters

Finite prime phase approximation gives one vertical sequence converging
on all positive coordinates and on every Wiener series. Augmentation is
approached by moving the real part to infinity.
-/

noncomputable section
set_option autoImplicit false
open ArithmeticFunction LSeries Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticOrientationTheory

/-- One vertical sequence approaches a tied Bohr torus point on every positive coefficient
and every absolutely summable Wiener series. -/
theorem exists_vertical_sequence_tendsto_bohrEval (σ : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (ω : BohrPoint) (hω : ∀ p : ℕ, p.Prime → ‖ω.ω p‖ = (p : ℝ) ^ (-u)) :
    ∃ t : ℕ → ℝ,
      (∀ n : ℕ, n ≠ 0 → Tendsto (fun j =>
        (WienerAlgebraAt.halfPlanePoint σ ((σ + u : ℝ) - (t j : ℂ) * I)
          (by simp; linarith only [hu])).ω n) atTop (𝓝 (ω.ω n))) ∧
      ∀ a : WienerAlgebraAt σ, Tendsto
        (fun j => LSeries (⇑a.toFn) ((σ + u : ℝ) - (t j : ℂ) * I))
        atTop (𝓝 (bohrEval σ a.toFn ω)) := by
  have hK (j : ℕ) := exists_halfPlanePoint_approx_primes σ hu
    (show 0 < 1 / ((j : ℝ) + 1) by positivity) (j + 1) ω (fun p hp _ => hω p hp)
  choose t ht using hK
  have hs (j : ℕ) : σ ≤ ((σ + u : ℝ) - (t j : ℂ) * I : ℂ).re := by
    simp
    linarith only [hu]
  let ωj (j : ℕ) := WienerAlgebraAt.halfPlanePoint σ _ (hs j)
  have hprime (p : ℕ) (hp : p.Prime) :
      Tendsto (fun j => (ωj j).ω p) atTop (𝓝 (ω.ω p)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ?_ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [eventually_ge_atTop p] with j hj
    exact ht j p hp (by omega)
  have hlist (l : List ℕ) (hl : ∀ p ∈ l, p.Prime) :
      Tendsto (fun j => (l.map (ωj j).ω).prod) atTop (𝓝 ((l.map ω.ω).prod)) := by
    induction l with
    | nil => simpa only [List.map_nil, List.prod_nil] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
    | cons p l ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (hprime p (hl p (List.mem_cons_self ..))).mul
          (ih fun q hq => hl q (List.mem_cons_of_mem p hq))
  have hcoord (n : ℕ) (hn : n ≠ 0) :
      Tendsto (fun j => (ωj j).ω n) atTop (𝓝 (ω.ω n)) := by
    simp_rw [BohrPoint.apply_eq_prod _ hn]
    exact hlist n.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
  refine ⟨t, hcoord, fun a => ?_⟩
  have hlim : Tendsto (fun j => bohrEval σ a.toFn (ωj j)) atTop
      (𝓝 (bohrEval σ a.toFn ω)) := by
    unfold bohrEval LSeries
    refine tendsto_tsum_of_dominated_convergence a.summable.norm (fun n => ?_)
      (Eventually.of_forall fun j n => norm_term_le _ (by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) ((ωj j).norm_le_one n)))
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero]
      exact tendsto_const_nhds
    · simp only [term_of_ne_zero hn]
      exact ((hcoord n hn).const_mul _).div_const _
  simpa only [ωj, WienerAlgebraAt.bohrEval_halfPlanePoint] using hlim

end GaloisForLFunctions.ArithmeticOrientationTheory

namespace GaloisForLFunctions.ArithmeticOrientationTheory

/-- An augmentation Bohr point evaluates every Wiener series at its unit coefficient. -/
theorem bohrEval_eq_unit_coefficient_of_augmentation (σ : ℝ) (ω : BohrPoint)
    (hω : ∀ p : ℕ+, p ≠ 1 → ω.ω p = 0) (a : WienerAlgebraAt σ) :
    bohrEval σ a.toFn ω = a.toFn 1 := by
  unfold bohrEval LSeries
  rw [tsum_eq_single 1]
  · simp [ω.map_one]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp only [term_zero]
    · have hp : (⟨n, Nat.pos_of_ne_zero hn0⟩ : ℕ+) ≠ 1 := by
        intro h
        exact hn (congrArg PNat.val h)
      have hzero : ω.ω n = 0 := hω ⟨n, Nat.pos_of_ne_zero hn0⟩ hp
      rw [term_of_ne_zero hn0, hzero, mul_zero, zero_div]

/-- A tied radial Bohr character or augmentation is approached by one sequence of
half-plane evaluations on the entire Wiener algebra. -/
theorem exists_halfPlane_sequence_tendsto_bohrEval_of_radial_or_augmentation
    (σ : ℝ) (ω : BohrPoint)
    (hω : (∀ p : ℕ+, p ≠ 1 → ω.ω p = 0) ∨
      ∃ u : ℝ, 0 ≤ u ∧ ∀ p : ℕ+, ‖ω.ω p‖ = (p : ℝ) ^ (-u)) :
    ∃ s : ℕ → ℂ, (∀ j, σ ≤ (s j).re) ∧
      ∀ a : WienerAlgebraAt σ,
        Tendsto (fun j => LSeries (⇑a.toFn) (s j)) atTop (𝓝 (bohrEval σ a.toFn ω)) := by
  rcases hω with hzero | ⟨u, hu, hradial⟩
  · let s (j : ℕ) : ℂ := ((σ + (j : ℝ) : ℝ) : ℂ)
    have hs : Tendsto (fun j => (s j).re) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (b - σ)]
        with j hj
      change b ≤ σ + (j : ℝ)
      linarith only [hj]
    refine ⟨s, fun j => ?_, fun a => ?_⟩
    · change σ ≤ σ + (j : ℝ)
      exact le_add_of_nonneg_right (Nat.cast_nonneg j)
    · rw [bohrEval_eq_unit_coefficient_of_augmentation σ ω hzero a]
      exact HTGeometry.tendsto_LSeries_of_re_atTop a.summable.norm hs
  · have hprime (p : ℕ) (hp : p.Prime) : ‖ω.ω p‖ = (p : ℝ) ^ (-u) :=
      hradial ⟨p, hp.pos⟩
    obtain ⟨t, _, ht⟩ := exists_vertical_sequence_tendsto_bohrEval σ hu ω hprime
    refine ⟨fun j => (σ + u : ℝ) - (t j : ℂ) * I, fun j => ?_, ht⟩
    simp
    linarith only [hu]

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_vertical_sequence_tendsto_bohrEval
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.bohrEval_eq_unit_coefficient_of_augmentation
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_halfPlane_sequence_tendsto_bohrEval_of_radial_or_augmentation
end
