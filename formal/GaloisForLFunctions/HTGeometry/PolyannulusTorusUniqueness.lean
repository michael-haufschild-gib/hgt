import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The product torus is a uniqueness set for a polyannulus

A holomorphic function on a polyannulus which vanishes on the product of unit
circles vanishes identically.  The proof releases one coordinate at a time:
with the other coordinates frozen, the slice is holomorphic on a connected
annulus and vanishes on the unit circle, which accumulates inside the annulus,
so the one-variable identity theorem kills the slice.

This is the analytic step that lets a polynomial identity among the time jets
of a quasiperiodic function, valid on a dense real orbit, be promoted to an
identity of holomorphic functions on the whole polyannulus.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The annulus of a log-radius -/

/-- The open annulus `exp (-c) < ‖w‖ < exp c`. -/
def logAnnulus (c : ℝ) : Set ℂ :=
  {w : ℂ | Real.exp (-c) < ‖w‖ ∧ ‖w‖ < Real.exp c}

theorem mem_logAnnulus_iff (c : ℝ) (w : ℂ) :
    w ∈ logAnnulus c ↔ Real.exp (-c) < ‖w‖ ∧ ‖w‖ < Real.exp c := Iff.rfl

theorem isOpen_logAnnulus (c : ℝ) : IsOpen (logAnnulus c) := by
  have hset : logAnnulus c =
      (fun w : ℂ => ‖w‖) ⁻¹' Set.Ioo (Real.exp (-c)) (Real.exp c) := by
    ext w
    exact Iff.rfl
  rw [hset]
  exact isOpen_Ioo.preimage continuous_norm

/-- The annulus is the exponential image of a vertical strip. -/
theorem logAnnulus_eq_exp_image (c : ℝ) :
    logAnnulus c = Complex.exp '' {s : ℂ | -c < s.re ∧ s.re < c} := by
  ext w
  simp only [logAnnulus, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp only [norm_zero] at h1
      exact absurd h1 (not_lt.2 (Real.exp_nonneg _))
    have hwpos : 0 < ‖w‖ := by
      rcases lt_or_ge 0 ‖w‖ with h | h
      · exact h
      · exact absurd h1 (not_lt.2 (le_trans h (Real.exp_nonneg _)))
    refine ⟨Complex.log w, ⟨?_, ?_⟩, Complex.exp_log hw0⟩
    · rw [Complex.log_re]
      have := Real.log_lt_log (Real.exp_pos (-c)) h1
      rwa [Real.log_exp] at this
    · rw [Complex.log_re]
      have := Real.log_lt_log hwpos h2
      rwa [Real.log_exp] at this
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    rw [Complex.norm_exp]
    exact ⟨Real.exp_lt_exp.2 h1, Real.exp_lt_exp.2 h2⟩

theorem isConnected_logAnnulus {c : ℝ} (hc : 0 < c) : IsConnected (logAnnulus c) := by
  rw [logAnnulus_eq_exp_image]
  refine IsConnected.image ?_ _ Complex.continuous_exp.continuousOn
  refine Convex.isConnected ?_ ⟨0, ?_, ?_⟩
  · exact (convex_halfSpace_re_gt (-c)).inter (convex_halfSpace_re_lt c)
  · show -c < (0 : ℂ).re
    simpa using hc
  · show (0 : ℂ).re < c
    simpa using hc

theorem isPreconnected_logAnnulus {c : ℝ} (hc : 0 < c) :
    IsPreconnected (logAnnulus c) :=
  (isConnected_logAnnulus hc).isPreconnected

theorem mem_logAnnulus_of_norm_one {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : ‖w‖ = 1) :
    w ∈ logAnnulus c := by
  refine ⟨?_, ?_⟩ <;> rw [hw]
  · calc Real.exp (-c) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp c := Real.exp_lt_exp.2 hc

theorem one_mem_logAnnulus {c : ℝ} (hc : 0 < c) : (1 : ℂ) ∈ logAnnulus c :=
  mem_logAnnulus_of_norm_one hc (by simp)

/-! ### The unit circle accumulates at one -/

/-- Small rotations approach `1` inside the punctured plane. -/
theorem tendsto_smallRotation :
    Tendsto (fun n : ℕ => Complex.exp (((1 / (n + 1) : ℝ) : ℂ) * Complex.I))
      atTop (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h1 : Tendsto (fun n : ℕ => (1 / (n + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => ((1 / (n + 1) : ℝ) : ℂ)) atTop
        (𝓝 (((0 : ℝ) : ℂ))) := (Complex.continuous_ofReal.tendsto _).comp h1
    rw [Complex.ofReal_zero] at h2
    have h3 : Tendsto (fun n : ℕ => ((1 / (n + 1) : ℝ) : ℂ) * Complex.I) atTop
        (𝓝 (0 * Complex.I)) := h2.mul_const Complex.I
    rw [zero_mul] at h3
    have h4 : Tendsto
        (fun n : ℕ => Complex.exp (((1 / (n + 1) : ℝ) : ℂ) * Complex.I)) atTop
        (𝓝 (Complex.exp 0)) := (Complex.continuous_exp.tendsto _).comp h3
    rwa [Complex.exp_zero] at h4
  · refine Filter.Eventually.of_forall fun n => ?_
    intro hn
    simp only [Set.mem_singleton_iff] at hn
    rw [Complex.exp_eq_one_iff] at hn
    obtain ⟨k, hk⟩ := hn
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hk' : ((1 / (n + 1) : ℝ) : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
      have hmul : ((1 / (n + 1) : ℝ) : ℂ) * Complex.I
          = ((k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        rw [hk]; ring
      exact mul_right_cancel₀ hI hmul
    have hreal : (1 / (n + 1) : ℝ) = (k : ℝ) * (2 * Real.pi) := by
      exact_mod_cast hk'
    have hpos : 0 < (1 / (n + 1) : ℝ) := by positivity
    have hle : (1 / (n + 1) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hpi : (1 : ℝ) < 2 * Real.pi := by
      have := Real.two_le_pi
      linarith
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_of_lt_add_one (by omega)
      nlinarith [Real.pi_pos]
    · rw [hk0] at hreal
      simp at hreal
      linarith
    · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
      nlinarith [Real.pi_pos]

/-- A function vanishing on the unit circle vanishes frequently near `1`. -/
theorem frequently_eq_zero_of_eqOn_circle {g : ℂ → ℂ}
    (h : ∀ w : ℂ, ‖w‖ = 1 → g w = 0) :
    ∃ᶠ w in 𝓝[≠] (1 : ℂ), g w = 0 := by
  refine tendsto_smallRotation.frequently (Filter.Frequently.of_forall fun n => ?_)
  refine h _ ?_
  rw [Complex.norm_exp]
  simp

/-- **One-variable step.**  A function holomorphic on an annulus and vanishing
on the unit circle vanishes on the whole annulus. -/
theorem eqOn_zero_logAnnulus {c : ℝ} (hc : 0 < c) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (logAnnulus c))
    (h0 : ∀ w : ℂ, ‖w‖ = 1 → g w = 0) :
    Set.EqOn g 0 (logAnnulus c) :=
  hg.eqOn_zero_of_preconnected_of_frequently_eq_zero (isPreconnected_logAnnulus hc)
    (one_mem_logAnnulus hc) (frequently_eq_zero_of_eqOn_circle h0)

/-! ### The polyannulus and its torus -/

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The polyannulus of log-radii `ρ`. -/
def polyannulus (ρ : d → ℝ) : Set (d → ℂ) :=
  {z | ∀ j, z j ∈ logAnnulus (ρ j)}

/-- The product of unit circles. -/
def unitTorus (d : Type) : Set (d → ℂ) := {z : d → ℂ | ∀ j, ‖z j‖ = 1}

omit [Fintype d] [DecidableEq d] in
theorem unitTorus_subset_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j) :
    unitTorus d ⊆ polyannulus ρ :=
  fun _ hz j => mem_logAnnulus_of_norm_one (hρ j) (hz j)

/-- Points with a prescribed set of coordinates released from the torus into
the annulus. -/
def mixedAnnulus (ρ : d → ℝ) (T : Finset d) : Set (d → ℂ) :=
  {z | (∀ j ∈ T, z j ∈ logAnnulus (ρ j)) ∧ ∀ j, j ∉ T → ‖z j‖ = 1}

omit [Fintype d] [DecidableEq d] in
theorem mixedAnnulus_empty (ρ : d → ℝ) :
    mixedAnnulus ρ ∅ = unitTorus d := by
  ext z
  simp only [mixedAnnulus, unitTorus, Set.mem_setOf_eq, Finset.notMem_empty,
    not_false_eq_true, forall_const, IsEmpty.forall_iff, implies_true, true_and]

omit [DecidableEq d] in
theorem mixedAnnulus_univ (ρ : d → ℝ) :
    mixedAnnulus ρ Finset.univ = polyannulus ρ := by
  ext z
  simp only [mixedAnnulus, polyannulus, Set.mem_setOf_eq, Finset.mem_univ,
    forall_const, not_true_eq_false, IsEmpty.forall_iff, implies_true, and_true]

omit [Fintype d] in
theorem mixedAnnulus_subset_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (T : Finset d) : mixedAnnulus ρ T ⊆ polyannulus ρ := by
  intro z hz j
  by_cases hj : j ∈ T
  · exact hz.1 j hj
  · exact mem_logAnnulus_of_norm_one (hρ j) (hz.2 j hj)

/-- The coordinate slice through a point. -/
theorem analyticOnNhd_updateSlice (z : d → ℂ) (i : d) (U : Set ℂ) :
    AnalyticOnNhd ℂ (fun w : ℂ => Function.update z i w) U := by
  refine analyticOnNhd_pi_iff.mpr fun j => ?_
  by_cases hj : j = i
  · subst hj
    have hfun : (fun w : ℂ => Function.update z j w j) = fun w : ℂ => w := by
      funext w
      simp
    rw [hfun]
    exact analyticOnNhd_id
  · have hfun : (fun w : ℂ => Function.update z i w j) = fun _ : ℂ => z j := by
      funext w
      simp [hj]
    rw [hfun]
    exact analyticOnNhd_const

/-- **Coordinatewise release.**  A function holomorphic on the polyannulus and
vanishing on the torus vanishes on every mixed stratum. -/
theorem eqOn_zero_mixedAnnulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {G : (d → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G (polyannulus ρ))
    (h0 : ∀ z ∈ unitTorus d, G z = 0) (T : Finset d) :
    ∀ z ∈ mixedAnnulus ρ T, G z = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      intro z hz
      rw [mixedAnnulus_empty] at hz
      exact h0 z hz
  | insert i T hi ih =>
      intro z hz
      have hzi : z i ∈ logAnnulus (ρ i) := hz.1 i (Finset.mem_insert_self i T)
      have hmaps : Set.MapsTo (fun w : ℂ => Function.update z i w)
          (logAnnulus (ρ i)) (polyannulus ρ) := by
        intro w hw j
        by_cases hj : j = i
        · subst hj
          simpa using hw
        · simp only [Function.update_apply, if_neg hj]
          by_cases hjT : j ∈ T
          · exact hz.1 j (Finset.mem_insert_of_mem hjT)
          · exact mem_logAnnulus_of_norm_one (hρ j)
              (hz.2 j (by simp [hjT, hj]))
      have hg : AnalyticOnNhd ℂ (fun w : ℂ => G (Function.update z i w))
          (logAnnulus (ρ i)) :=
        hG.comp (analyticOnNhd_updateSlice z i _) hmaps
      have hcircle : ∀ w : ℂ, ‖w‖ = 1 → G (Function.update z i w) = 0 := by
        intro w hw
        refine ih _ ⟨?_, ?_⟩
        · intro j hjT
          have hj : j ≠ i := by rintro rfl; exact hi hjT
          simp only [Function.update_apply, if_neg hj]
          exact hz.1 j (Finset.mem_insert_of_mem hjT)
        · intro j hjT
          by_cases hj : j = i
          · subst hj
            simpa using hw
          · simp only [Function.update_apply, if_neg hj]
            exact hz.2 j (by simp [hjT, hj])
      have := eqOn_zero_logAnnulus (hρ i) hg hcircle hzi
      simpa using this

/-- **The product torus is a uniqueness set for the polyannulus.** -/
theorem eqOn_zero_polyannulus_of_eqOn_zero_unitTorus {ρ : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) {G : (d → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G (polyannulus ρ))
    (h0 : ∀ z ∈ unitTorus d, G z = 0) :
    ∀ z ∈ polyannulus ρ, G z = 0 := by
  intro z hz
  refine eqOn_zero_mixedAnnulus hρ hG h0 Finset.univ z ?_
  rwa [mixedAnnulus_univ]

/-- Two functions holomorphic on the polyannulus which agree on the torus
agree everywhere. -/
theorem eqOn_polyannulus_of_eqOn_unitTorus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {G H : (d → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G (polyannulus ρ))
    (hH : AnalyticOnNhd ℂ H (polyannulus ρ))
    (h0 : ∀ z ∈ unitTorus d, G z = H z) :
    ∀ z ∈ polyannulus ρ, G z = H z := by
  intro z hz
  have hzero := eqOn_zero_polyannulus_of_eqOn_zero_unitTorus hρ (hG.sub hH)
    (fun w hw => by simp [h0 w hw]) z hz
  have : G z - H z = 0 := hzero
  linear_combination this

end

end GaloisForLFunctions.HTGeometry
