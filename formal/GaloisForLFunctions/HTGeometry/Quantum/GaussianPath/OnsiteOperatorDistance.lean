import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualOnsiteDistance
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport
import GaloisForLFunctions.HTGeometry.ProductStabilizerPhysicalScore

/-!
# Product-state lower bounds on path Hamiltonian distance

Flipping all local stabilizer eigenvalues changes the sign of onsite
expectations and preserves the expectations of every bond.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem prod_stabilizer_onsite {n : ℕ}
    (p : Fin (n + 2) → Fin 3 × Bool) (s : Fin (n + 2)) (a : Fin 3) :
    (∏ t, stabilizerAxisExpectation (p t) (onsiteWord s a t)) =
      stabilizerAxisExpectation (p s) (some a) := by
  calc
    _ = ∏ t, if t = s then stabilizerAxisExpectation (p t) (some a) else 1 := by
      exact Finset.prod_congr rfl fun t _ => by by_cases h : t = s <;> simp [onsiteWord, h, stabilizerAxisExpectation]
    _ = _ := Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ _)

private theorem prod_stabilizer_bond {n : ℕ}
    (p : Fin (n + 2) → Fin 3 × Bool) (e : Fin (n + 1)) (a : Fin 3 × Fin 3) :
    (∏ t, stabilizerAxisExpectation (p t) (couplingWord e a t)) =
      stabilizerAxisExpectation (p e.castSucc) (some a.1) *
        stabilizerAxisExpectation (p e.succ) (some a.2) := by
  have he : e.castSucc ≠ e.succ := by
    intro h
    have hv := congrArg Fin.val h
    change e.val = e.val + 1 at hv
    omega
  calc
    _ = ∏ t, (if t = e.castSucc then stabilizerAxisExpectation (p t) (some a.1) else 1) *
        (if t = e.succ then stabilizerAxisExpectation (p t) (some a.2) else 1) := by
      apply Finset.prod_congr rfl
      intro t _
      by_cases h₁ : t = e.castSucc
      · subst t
        simp [couplingWord, he]
      · by_cases h₂ : t = e.succ
        · subst t
          simp [couplingWord, Ne.symm he]
        · simp [couplingWord, h₁, h₂, stabilizerAxisExpectation]
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ _),
        Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ _)]

private def flipSigns {σ : Type*} (p : σ → Fin 3 × Bool) (s : σ) : Fin 3 × Bool :=
  ((p s).1, !(p s).2)

private theorem stabilizerAxisExpectation_flip {σ : Type*} (p : σ → Fin 3 × Bool)
    (s : σ) (a : Fin 3) :
    stabilizerAxisExpectation (flipSigns p s) (some a) =
      -stabilizerAxisExpectation (p s) (some a) := by
  cases h : (p s).2 <;> by_cases ha : (p s).1 = a <;>
    simp [stabilizerAxisExpectation, flipSigns, h, ha]

private theorem norm_trace_productStabilizer_le {n : ℕ}
    (p : Fin (n + 2) → Fin 3 × Bool)
    (H : Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ) :
    ‖(productStabilizerDensity p * H).trace‖ ≤ ‖H‖ := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (productStabilizerDensity p)
  rw [productStabilizerDensity_isHermitian p, productStabilizerDensity_mul_self p] at h
  exact norm_trace_densityMatrix_mul_le h (trace_productStabilizerDensity p) H

/-- Two product stabilizer states with opposite eigenvalue signs isolate
the selected onsite coefficients and cancel all nearest-neighbour bonds. -/
theorem signed_onsite_sum_le_pathHamiltonian_dist {n : ℕ} (u v : PathShell n)
    (a : Fin (n + 2) → Fin 3) :
    (∑ s, |u (.inl (s, a s)) - v (.inl (s, a s))|) ≤
      ‖pathHamiltonian u - pathHamiltonian v‖ := by
  let H := pathHamiltonian u - pathHamiltonian v
  let p (s : Fin (n + 2)) : Fin 3 × Bool :=
    (a s, decide (0 ≤ u (.inl (s, a s)) - v (.inl (s, a s))))
  let E (q : Fin (n + 2) → Fin 3 × Bool) := (productStabilizerDensity q * H).trace
  let S := ∑ s, |u (.inl (s, a s)) - v (.inl (s, a s))|
  have he (q : Fin (n + 2) → Fin 3 × Bool) : E q =
      (∑ s : Fin (n + 2), ∑ b : Fin 3,
        ((u (.inl (s, b)) - v (.inl (s, b))) * stabilizerAxisExpectation (q s) (some b) : ℝ)) +
      (∑ e : Fin (n + 1), ∑ b : Fin 3 × Fin 3,
        ((u (.inr (e, b)) - v (.inr (e, b))) *
          (stabilizerAxisExpectation (q e.castSucc) (some b.1) *
           stabilizerAxisExpectation (q e.succ) (some b.2)) : ℝ)) := by
    simp only [E, H, pathHamiltonian, onsitePart, edgePart, Matrix.mul_sub, Matrix.mul_add,
      Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum,
      Matrix.trace_smul, trace_productStabilizerDensity_mul_finitePauliMatrix,
      prod_stabilizer_onsite, prod_stabilizer_bond, Fintype.sum_prod_type, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_sub, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib]
    abel
  have hp (s : Fin (n + 2)) :
      (∑ b : Fin 3, (u (.inl (s, b)) - v (.inl (s, b))) * stabilizerAxisExpectation (p s) (some b)) =
        |u (.inl (s, a s)) - v (.inl (s, a s))| := by
    rw [Finset.sum_eq_single (a s)]
    · by_cases hs : 0 ≤ u (.inl (s, a s)) - v (.inl (s, a s))
      · simp [p, stabilizerAxisExpectation, hs, abs_of_nonneg hs]
      · simp [p, stabilizerAxisExpectation, hs, abs_of_neg (lt_of_not_ge hs)]
    · intro b _ hb
      simp [p, stabilizerAxisExpectation, Ne.symm hb]
    · simp
  have hdiff : E p - E (flipSigns p) = (2 * S : ℝ) := by
    rw [he, he]
    simp only [stabilizerAxisExpectation_flip, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib,
      hp, S, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hle := (norm_sub_le (E p) (E (flipSigns p))).trans
    (add_le_add (norm_trace_productStabilizer_le p H) (norm_trace_productStabilizer_le (flipSigns p) H))
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg zero_le_two hS)] at hle
  change S ≤ ‖H‖
  linarith only [hle]

/-- Onsite rows whose three coefficients lie in the interval `[1, 2]`. -/
def onsiteUnitBox : Set (Fin 3 → ℝ) :=
  ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).pi fun _ => Icc 1 2

private theorem measurableSet_onsiteUnitBox : MeasurableSet onsiteUnitBox :=
  MeasurableSet.pi (Finset.univ : Finset (Fin 3)).countable_toSet (fun _ _ => measurableSet_Icc)

/-- Each onsite row in the unit box counts as one site. -/
def onsiteUnitBoxIndicator (x : Fin 3 → ℝ) : ℝ :=
  onsiteUnitBox.indicator (fun _ => 1) x

/-- Each site with all onsite coordinates in the unit box contributes one
unit to the operator distance, except for one possible multiaxis site. -/
theorem count_onsiteUnitBox_sub_one_le_noncontextual_distance {n : ℕ} (u v : PathShell n)
    (hv : PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1))) :
    (∑ s : Fin (n + 2), onsiteUnitBoxIndicator (fun a => u (.inl (s, a)))) - 1 ≤
      ‖pathHamiltonian u - pathHamiltonian v‖ := by
  classical
  let B := multiAxisSites {ia | v (.inl ia) ≠ 0}
  have hB : B.Subsingleton := path_noncontextual_forbids_two_multiaxis_sites v hv
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 2), ∀ s ≠ j, s ∉ B := by
    by_cases h : B.Nonempty
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, fun s hsj hs => hsj (hB hs hj)⟩
    · exact ⟨0, fun s _ hs => h ⟨s, hs⟩⟩
  let a (s : Fin (n + 2)) : Fin 3 := if v (.inl (s, 0)) = 0 then 0 else 1
  let F (s : Fin (n + 2)) := onsiteUnitBoxIndicator (fun b => u (.inl (s, b)))
  let d (s : Fin (n + 2)) := |u (.inl (s, a s)) - v (.inl (s, a s))|
  have hzero (s : Fin (n + 2)) (hs : s ≠ j) : v (.inl (s, a s)) = 0 := by
    by_cases h : v (.inl (s, 0)) = 0
    · simpa only [a, if_pos h] using h
    · simp only [a, if_neg h]
      by_contra h'
      exact hj s hs ⟨0, 1, h, h', Fin.zero_ne_one⟩
  have hle (s : Fin (n + 2)) (hs : s ≠ j) : F s ≤ d s := by
    by_cases h : (fun b => u (.inl (s, b))) ∈ onsiteUnitBox
    · have h1 : 1 ≤ u (.inl (s, a s)) := ((Set.mem_pi.mp h) (a s) (by simp)).1
      simpa only [F, onsiteUnitBoxIndicator, Set.indicator_of_mem h, d, hzero s hs, sub_zero]
        using h1.trans (le_abs_self _)
    · simpa only [F, onsiteUnitBoxIndicator, Set.indicator_of_notMem h] using abs_nonneg _
  have hjle : F j ≤ 1 := by
    by_cases h : (fun b => u (.inl (j, b))) ∈ onsiteUnitBox <;> simp [F, onsiteUnitBoxIndicator, h]
  have he := Finset.add_sum_erase Finset.univ F (Finset.mem_univ j)
  change (∑ s, F s) - 1 ≤ _
  calc
    _ ≤ ∑ s ∈ Finset.univ.erase j, F s := by linarith only [he, hjle]
    _ ≤ ∑ s ∈ Finset.univ.erase j, d s :=
      Finset.sum_le_sum fun s hs => hle s (Finset.ne_of_mem_erase hs)
    _ ≤ ∑ s, d s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun s _ _ => abs_nonneg _
    _ ≤ _ := signed_onsite_sum_le_pathHamiltonian_dist u v a

/-- Single-site probability used in the linear operator distance bound. -/
def gaussianOnsiteUnitBoxMass : ℝ := (gaussianOnsiteRowLaw onsiteUnitBox).toReal

theorem gaussianOnsiteUnitBoxMass_pos : 0 < gaussianOnsiteUnitBoxMass := by
  have he : gaussianOnsiteRowLaw onsiteUnitBox = (gaussianReal 0 1 (Icc (1 : ℝ) 2)) ^ 3 := by
    unfold gaussianOnsiteRowLaw onsiteUnitBox
    rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_Icc), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  letI : IsProbabilityMeasure gaussianOnsiteRowLaw := by unfold gaussianOnsiteRowLaw; infer_instance
  apply ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  rw [he]
  exact pow_ne_zero _ (gaussianReal_Icc_pos (by norm_num : (1 : ℝ) < 2)).ne'

private theorem gaussian_ae_unitBox_mean :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, onsiteUnitBoxIndicator (gaussianOnsiteRow ω j)) / (k : ℝ))
      atTop (𝓝 gaussianOnsiteUnitBoxMass) := by
  letI : IsProbabilityMeasure gaussianOnsiteRowLaw := by unfold gaussianOnsiteRowLaw; infer_instance
  have hmeas : Measurable onsiteUnitBoxIndicator :=
    measurable_const.indicator measurableSet_onsiteUnitBox
  have hint : Integrable onsiteUnitBoxIndicator gaussianOnsiteRowLaw :=
    (integrable_const (1 : ℝ)).indicator measurableSet_onsiteUnitBox
  have hmean : (∫ x, onsiteUnitBoxIndicator x ∂gaussianOnsiteRowLaw) = gaussianOnsiteUnitBoxMass := by
    simp [onsiteUnitBoxIndicator, gaussianOnsiteUnitBoxMass, Measure.real,
      integral_indicator measurableSet_onsiteUnitBox]
  rw [← hmean]
  exact gaussian_ae_onsiteRow_mean onsiteUnitBoxIndicator hmeas hint

/-- Along a single Gaussian path, the operator distance to every
noncontextual approximant eventually grows at least linearly. -/
theorem gaussian_ae_eventually_noncontextual_operator_linear_gap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ c : ℝ, c < gaussianOnsiteUnitBoxMass →
      ∀ᶠ n : ℕ in atTop, ∀ v : PathShell n,
        PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) →
          c * ((n + 2 : ℕ) : ℝ) ≤ ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖ := by
  filter_upwards [gaussian_ae_unitBox_mean] with ω hω
  intro c hc
  let x (j : ℕ) := onsiteUnitBoxIndicator (gaussianOnsiteRow ω j)
  have hmean : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range (n + 2), x j) / ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 gaussianOnsiteUnitBoxMass) := hω.comp (tendsto_add_atTop_nat 2)
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hlim : Tendsto (fun n : ℕ => ((∑ j ∈ Finset.range (n + 2), x j) - 1) / ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 gaussianOnsiteUnitBoxMass) := by
    simpa only [sub_div, sub_zero] using hmean.sub hi
  filter_upwards [hlim.eventually_const_lt hc] with n hn
  intro v hv
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  refine ((lt_div_iff₀ hN).mp hn).le.trans ?_
  have h := count_onsiteUnitBox_sub_one_le_noncontextual_distance (pathPauliDisorderShell ω n) v hv
  change (∑ s : Fin (n + 2), x s.val) - 1 ≤ _ at h
  rwa [Fin.sum_univ_eq_sum_range x] at h

/-- The operator distance to noncontextual support has linear order almost
surely, with the zero Hamiltonian giving the upper bound. -/
theorem gaussian_ae_noncontextual_operator_distance_linear_order :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      (∀ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) →
        c * ((n + 2 : ℕ) : ℝ) ≤ ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖) ∧
      (∃ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) ∧
        ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖ ≤ C * ((n + 2 : ℕ) : ℝ)) := by
  obtain ⟨_, b, _, hb, hmass⟩ := gaussian_path_eventual_coefficient_mass
  let c := gaussianOnsiteUnitBoxMass / 2
  have hc : 0 < c := half_pos gaussianOnsiteUnitBoxMass_pos
  have hlt : c < gaussianOnsiteUnitBoxMass := half_lt_self gaussianOnsiteUnitBoxMass_pos
  have h12b : 0 < 12 * b := mul_pos (by norm_num) hb
  refine ⟨c, Real.sqrt (12 * b), hc, Real.sqrt_pos_of_pos h12b, ?_⟩
  filter_upwards [gaussian_ae_eventually_noncontextual_operator_linear_gap, hmass] with ω hlow hup
  filter_upwards [hlow c hlt, hup] with n hn hcoeff
  refine ⟨hn, 0, ?_, ?_⟩
  · intro i
    exact (i.property rfl).elim
  · have hz : pathHamiltonian (0 : PathShell n) = 0 := (pathHamiltonianLM n).map_zero
    rw [hz, sub_zero]
    let N : ℝ := (n + 2 : ℕ)
    have hN : 0 ≤ N := Nat.cast_nonneg _
    have hcard : (Fintype.card (PathLabel n) : ℝ) ≤ 12 * N := by
      simp [N, PathLabel, Fintype.card_sum, Fintype.card_prod]
      linarith
    have hs : ‖pathHamiltonian (pathPauliDisorderShell ω n)‖ ≤ Real.sqrt (12 * b) * N := by
      refine (norm_pathHamiltonian_le _).trans ?_
      apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) hN)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt h12b.le]
      calc
        _ ≤ (12 * N) * (b * N) :=
          mul_le_mul hcard hcoeff.2 (sq_nonneg _) (mul_nonneg (by norm_num) hN)
        _ = _ := by ring
    exact hs

#print axioms signed_onsite_sum_le_pathHamiltonian_dist
#print axioms count_onsiteUnitBox_sub_one_le_noncontextual_distance
#print axioms gaussianOnsiteUnitBoxMass_pos
#print axioms gaussian_ae_eventually_noncontextual_operator_linear_gap
#print axioms gaussian_ae_noncontextual_operator_distance_linear_order

end

end GaloisForLFunctions.HTGeometry
