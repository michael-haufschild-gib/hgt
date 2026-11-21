import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AlternatingBondProbe
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliClawProbability

/-!
# Operator distance from path Hamiltonians with a twin line model

Each two-row claw certificate forces at least one of its six terms to
be erased. The minimum coefficient magnitude in the certificate is
therefore an unavoidable cost. Separate onsite and bond probes bound
the sum of these costs by a constant times the operator distance.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

private theorem pairedRow_lt (j : Fin ((n + 1) / 2)) (r : Fin 2) :
    2 * j.val + r.val < n + 1 := by
  have hj := j.isLt
  have hr := r.isLt
  omega

/-- Embed one direction in a pair of coefficient rows wholly inside the path. -/
def clawBlockPathLabel (j : Fin ((n + 1) / 2)) (i : PathPauliBlockLabel) : PathLabel n :=
  match i.2 with
  | .inl a => .inl (⟨2 * j.val + i.1.val, (pairedRow_lt j i.1).trans (Nat.lt_succ_self _)⟩, a)
  | .inr a => .inr (⟨2 * j.val + i.1.val, pairedRow_lt j i.1⟩, a)

/-- Every complete two-row certificate loses a term in a support
whose frustration graph admits a twin line model. -/
theorem exists_zero_of_twinLineModel_clawBlock {ρ : Type*} [DecidableEq ρ]
    (v : PathShell n) (j : Fin ((n + 1) / 2))
    (hv : Nonempty (TwinLineModel (pathFrustrationAdj {l | v l ≠ 0}) ρ)) :
    ∃ i ∈ clawBlockLabels, v (clawBlockPathLabel j i) = 0 := by
  classical
  by_contra! h
  let e : Fin (n + 1) := ⟨2 * j.val, by have := pairedRow_lt j 0; simpa using this⟩
  let f : Fin (n + 1) := ⟨2 * j.val + 1, by have := pairedRow_lt j 1; simpa using this⟩
  have hef : e.succ = f.castSucc := Fin.ext rfl
  let S : Set (PathLabel n) := {l | v l ≠ 0}
  have he : IsEmpty (TwinLineModel (pathFrustrationAdj S) ρ) :=
    path_no_twinLineModel_of_adjacent_rows S e f hef
      (h (0, .inr (2, 2)) (by simp [clawBlockLabels]))
      (h (1, .inr (0, 0)) (by simp [clawBlockLabels]))
      (h (0, .inl 0) (by simp [clawBlockLabels]))
      (h (1, .inl 0) (by simp [clawBlockLabels]))
      (h (0, .inl 2) (by simp [clawBlockLabels]))
      (h (1, .inr (0, 2)) (by simp [clawBlockLabels]))
  exact hv.elim he.false

private theorem clawBlockLabels_nonempty : clawBlockLabels.Nonempty :=
  ⟨(0, .inl 0), by simp [clawBlockLabels]⟩

/-- The smallest absolute coefficient among the six terms of a certificate. -/
def clawBlockErasureWeight (x : PathPauliBlockLabel → ℝ) : ℝ :=
  clawBlockLabels.inf' clawBlockLabels_nonempty fun i => |x i|

theorem clawBlockErasureWeight_nonneg (x : PathPauliBlockLabel → ℝ) :
    0 ≤ clawBlockErasureWeight x := by
  apply Finset.le_inf'
  exact fun i _ => abs_nonneg (x i)

private theorem sum_on_injective_le_sum_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    (∑ a, g (f a)) ≤ ∑ b, g b := by
  classical
  rw [← Finset.sum_image (f := g) (s := Finset.univ) (g := f) hf.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hg b

private theorem clawBlock_direction_sum_le (u v : PathShell n) (i : PathPauliBlockLabel) :
    (∑ j : Fin ((n + 1) / 2), |u (clawBlockPathLabel j i) - v (clawBlockPathLabel j i)|) ≤
      ‖pathHamiltonian u - pathHamiltonian v‖ := by
  rcases i with ⟨r, a | a⟩
  · let f (j : Fin ((n + 1) / 2)) : Fin (n + 2) :=
      ⟨2 * j.val + r.val, (pairedRow_lt j r).trans (Nat.lt_succ_self _)⟩
    have hf : Function.Injective f := by
      intro j k h
      apply Fin.ext
      have he := congrArg Fin.val h
      change 2 * j.val + r.val = 2 * k.val + r.val at he
      omega
    let g (s : Fin (n + 2)) := |u (.inl (s, a)) - v (.inl (s, a))|
    change (∑ j, g (f j)) ≤ _
    exact (sum_on_injective_le_sum_nonneg f hf g (fun _ => abs_nonneg _)).trans
      (signed_onsite_sum_le_pathHamiltonian_dist u v (fun _ => a))
  · let f (j : Fin ((n + 1) / 2)) : Fin (n + 1) := ⟨2 * j.val + r.val, pairedRow_lt j r⟩
    have hf : Function.Injective f := by
      intro j k h
      apply Fin.ext
      have he := congrArg Fin.val h
      change 2 * j.val + r.val = 2 * k.val + r.val at he
      omega
    let g (e : Fin (n + 1)) :=
      if (e.val + r.val) % 2 = 0 then |u (.inr (e, a)) - v (.inr (e, a))| else 0
    have hsum : (∑ j : Fin ((n + 1) / 2), |u (clawBlockPathLabel j (r, .inr a)) -
        v (clawBlockPathLabel j (r, .inr a))|) = ∑ j, g (f j) := by
      apply Finset.sum_congr rfl
      intro j _
      have he : ((f j).val + r.val) % 2 = 0 := by dsimp [f]; omega
      exact (if_pos he).symm
    rw [hsum]
    refine (sum_on_injective_le_sum_nonneg f hf g (fun e => ?_)).trans
      (alternating_bond_abs_sum_le_pathHamiltonian_dist u v r a)
    dsimp [g]
    split <;> simp only [abs_nonneg, le_refl]

/-- All disjoint certificate costs add. Six direction probes bound their
sum by six times the operator distance to a twin line approximation. -/
theorem sum_clawBlockErasureWeight_le_operator_dist {ρ : Type*} [DecidableEq ρ]
    (u v : PathShell n) (hv : Nonempty (TwinLineModel (pathFrustrationAdj {l | v l ≠ 0}) ρ)) :
    (∑ j : Fin ((n + 1) / 2), clawBlockErasureWeight (fun i => u (clawBlockPathLabel j i))) ≤
      6 * ‖pathHamiltonian u - pathHamiltonian v‖ := by
  let d (j : Fin ((n + 1) / 2)) (i : PathPauliBlockLabel) :=
    |u (clawBlockPathLabel j i) - v (clawBlockPathLabel j i)|
  have hs (j : Fin ((n + 1) / 2)) :
      clawBlockErasureWeight (fun i => u (clawBlockPathLabel j i)) ≤ ∑ i ∈ clawBlockLabels, d j i := by
    obtain ⟨i, hi, hz⟩ := exists_zero_of_twinLineModel_clawBlock v j hv
    calc
      _ ≤ |u (clawBlockPathLabel j i)| := Finset.inf'_le _ hi
      _ = d j i := by simp only [d, hz, sub_zero]
      _ ≤ _ := Finset.single_le_sum (fun _ _ => abs_nonneg _) hi
  calc
    _ ≤ ∑ j : Fin ((n + 1) / 2), ∑ i ∈ clawBlockLabels, d j i := Finset.sum_le_sum fun j _ => hs j
    _ = ∑ i ∈ clawBlockLabels, ∑ j, d j i := Finset.sum_comm
    _ ≤ ∑ _i ∈ clawBlockLabels, ‖pathHamiltonian u - pathHamiltonian v‖ :=
      Finset.sum_le_sum fun i _ => clawBlock_direction_sum_le u v i
    _ = _ := by simp [card_clawBlockLabels, nsmul_eq_mul]

private theorem measurable_clawBlockErasureWeight : Measurable clawBlockErasureWeight := by
  let f (i : PathPauliBlockLabel) (x : PathPauliBlockLabel → ℝ) := |x i|
  have he : clawBlockErasureWeight = clawBlockLabels.inf' clawBlockLabels_nonempty f := by
    funext x
    unfold clawBlockErasureWeight
    exact (Finset.inf'_apply (C := fun _ : PathPauliBlockLabel → ℝ => ℝ) clawBlockLabels_nonempty f x).symm
  rw [he]
  exact Finset.inf'_induction clawBlockLabels_nonempty f
    (fun _ h₁ _ h₂ => h₁.inf h₂) (fun i _ => (measurable_pi_apply i).abs)

/-- Law of two independent Gaussian coefficient rows. -/
def gaussianClawBlockLaw : Measure (PathPauliBlockLabel → ℝ) :=
  Measure.infinitePi fun _ => gaussianReal 0 1

private theorem integrable_clawBlockErasureWeight : Integrable clawBlockErasureWeight gaussianClawBlockLaw := by
  let i : PathPauliBlockLabel := (0, .inl 0)
  have hi : i ∈ clawBlockLabels := by simp [i, clawBlockLabels]
  have hstd : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
    have h : MemLp id 1 (gaussianReal 0 1) := memLp_id_gaussianReal' _ (by simp)
    simpa [Real.norm_eq_abs] using (memLp_one_iff_integrable.mp h).norm
  have hx : Integrable (fun x : PathPauliBlockLabel → ℝ => |x i|) gaussianClawBlockLaw :=
    (measurePreserving_eval_infinitePi (fun _ : PathPauliBlockLabel => gaussianReal 0 1) i).integrable_comp_of_integrable hstd
  refine hx.mono' measurable_clawBlockErasureWeight.aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (clawBlockErasureWeight_nonneg x)]
  exact Finset.inf'_le _ hi

/-- Mean unavoidable coefficient magnitude in a Gaussian claw certificate. -/
def gaussianClawErasureMean : ℝ := ∫ x, clawBlockErasureWeight x ∂gaussianClawBlockLaw

theorem gaussianClawErasureMean_pos : 0 < gaussianClawErasureMean := by
  apply (integral_pos_iff_support_of_nonneg clawBlockErasureWeight_nonneg integrable_clawBlockErasureWeight).mpr
  have hsub : clawBlockEvent 1 ⊆ Function.support clawBlockErasureWeight := by
    intro x hx
    have h : 1 ≤ clawBlockErasureWeight x := by
      apply Finset.le_inf'
      exact fun i hi => (show 1 < |x i| from hx i hi).le
    exact ne_of_gt (zero_lt_one.trans_le h)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [gaussianClawBlockLaw, gaussian_measure_clawBlockEvent]
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ (gaussianAbsoluteTailMass_pos _).ne')

/-- The strong law for every integrable observable of the paired Gaussian rows. -/
theorem gaussian_ae_pairedRows_mean (f : (PathPauliBlockLabel → ℝ) → ℝ)
    (hf : Measurable f) (hi : Integrable f gaussianClawBlockLaw) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
      (fun m : ℕ => (∑ j ∈ Finset.range m, f (pathPauliBlock ω j)) / (m : ℝ))
      atTop (𝓝 (∫ x, f x ∂gaussianClawBlockLaw)) := by
  letI : IsProbabilityMeasure gaussianClawBlockLaw := by unfold gaussianClawBlockLaw; infer_instance
  let ν := Measure.infinitePi fun _ : ℕ => gaussianClawBlockLaw
  let X (j : ℕ) (y : ℕ → PathPauliBlockLabel → ℝ) := f (y j)
  have hd (j : ℕ) : IdentDistrib (X j) f ν gaussianClawBlockLaw := by
    have hp := measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianClawBlockLaw) j
    have he : IdentDistrib (Function.eval j) id ν gaussianClawBlockLaw :=
      ⟨hp.measurable.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]; exact hp.map_eq⟩
    exact he.comp hf
  have hI : iIndepFun X ν :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianClawBlockLaw)
      (X := fun _ => f) (fun _ => hf)
  have h := strong_law_ae_real X ((hd 0).integrable_iff.mpr hi)
    (fun _ _ hjk => hI.indepFun hjk) (fun j => (hd j).trans (hd 0).symm)
  rw [(hd 0).integral_eq] at h
  have hp : MeasurePreserving pathPauliBlock pathPauliDisorderLaw ν := measurePreserving_paired_rows _
  exact hp.quasiMeasurePreserving.ae h

private theorem tendsto_pairedRows_atTop : Tendsto (fun n : ℕ => (n + 1) / 2) atTop atTop := by
  refine tendsto_atTop.mpr fun m => ?_
  filter_upwards [eventually_ge_atTop (2 * m)] with n hn
  omega

private theorem tendsto_pairedRows_fraction : Tendsto
    (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (1 / 2)) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) := tendsto_const_nhds
  have hlo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (1 / 2)) :=
    by simpa only [sub_zero] using hconst.sub hinv
  have bounds (n : ℕ) : (1 / 2 : ℝ) - 1 / ((n + 2 : ℕ) : ℝ) ≤
      (((n + 1) / 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) ∧
      (((n + 1) / 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) ≤ 1 / 2 := by
    have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hl : ((n + 2 : ℕ) : ℝ) ≤ (2 : ℝ) * (((n + 1) / 2 : ℕ) : ℝ) + 2 := by
      exact_mod_cast (show n + 2 ≤ 2 * ((n + 1) / 2) + 2 by omega)
    have hu : (2 : ℝ) * (((n + 1) / 2 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * ((n + 1) / 2) ≤ n + 2 by omega)
    constructor
    · apply (le_div_iff₀ hN).mpr
      rw [sub_mul, div_mul_cancel₀ _ hN.ne']
      linarith only [hl]
    · exact (div_le_iff₀ hN).mpr (by linarith only [hu])
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hlo.eventually_const_lt ha] with n hn
    exact hn.trans_le (bounds n).1
  · intro a ha
    exact .of_forall fun n => (bounds n).2.trans_lt ha

/-- The total certificate cost per site converges to half its mean per
paired row, since one certificate uses two coefficient rows. -/
theorem gaussian_ae_clawErasure_per_site :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun n : ℕ =>
      (∑ j ∈ Finset.range ((n + 1) / 2), clawBlockErasureWeight (pathPauliBlock ω j)) /
        ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (gaussianClawErasureMean / 2)) := by
  filter_upwards [gaussian_ae_pairedRows_mean clawBlockErasureWeight measurable_clawBlockErasureWeight
    integrable_clawBlockErasureWeight] with ω hω
  let S (m : ℕ) := ∑ j ∈ Finset.range m, clawBlockErasureWeight (pathPauliBlock ω j)
  have hm : Tendsto (fun n : ℕ => S ((n + 1) / 2) / (((n + 1) / 2 : ℕ) : ℝ))
      atTop (𝓝 gaussianClawErasureMean) := hω.comp tendsto_pairedRows_atTop
  have hlim : Tendsto (fun n : ℕ => (S ((n + 1) / 2) / (((n + 1) / 2 : ℕ) : ℝ)) *
      ((((n + 1) / 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)))
      atTop (𝓝 (gaussianClawErasureMean / 2)) := by
    simpa only [div_eq_mul_inv, one_mul] using hm.mul tendsto_pairedRows_fraction
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hm0 : 0 < (((n + 1) / 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  change (S ((n + 1) / 2) / (((n + 1) / 2 : ℕ) : ℝ)) *
    ((((n + 1) / 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) = S ((n + 1) / 2) / ((n + 2 : ℕ) : ℝ)
  rw [← mul_div_assoc, div_mul_cancel₀ _ hm0.ne']

/-- On one Gaussian draw the operator distance from every nearest-neighbour
Hamiltonian admitting a twin line model is eventually at least linear.
The bound is independent of the root graph's vertex type. -/
theorem gaussian_ae_eventually_twinLine_operator_linear_gap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ c : ℝ, c < gaussianClawErasureMean / 12 →
      ∀ᶠ n : ℕ in atTop, ∀ (ρ : Type*) [DecidableEq ρ], ∀ v : PathShell n,
        Nonempty (TwinLineModel (pathFrustrationAdj {l | v l ≠ 0}) ρ) →
          c * ((n + 2 : ℕ) : ℝ) ≤ ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖ := by
  filter_upwards [gaussian_ae_clawErasure_per_site] with ω hω
  intro c hc
  have hc' : 6 * c < gaussianClawErasureMean / 2 := by linarith only [hc]
  filter_upwards [hω.eventually_const_lt hc'] with n hn
  intro ρ _ v hv
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hl := (lt_div_iff₀ hN).mp hn
  have hu := sum_clawBlockErasureWeight_le_operator_dist (pathPauliDisorderShell ω n) v hv
  have he (j : Fin ((n + 1) / 2)) : (fun i => pathPauliDisorderShell ω n (clawBlockPathLabel j i)) =
      pathPauliBlock ω j.val := by
    funext i
    rcases i with ⟨r, a | a⟩ <;> rfl
  simp only [he] at hu
  rw [Fin.sum_univ_eq_sum_range (fun j => clawBlockErasureWeight (pathPauliBlock ω j))] at hu
  apply le_of_mul_le_mul_left _ (by norm_num : 0 < (6 : ℝ))
  calc
    _ = (6 * c) * ((n + 2 : ℕ) : ℝ) := by ring
    _ ≤ _ := hl.le.trans hu

private theorem zero_admits_twinLineModel (n : ℕ) (ρ : Type*) [DecidableEq ρ] :
    Nonempty (TwinLineModel (pathFrustrationAdj {l | (0 : PathShell n) l ≠ 0}) ρ) := by
  let S : Set (PathLabel n) := {l | (0 : PathShell n) l ≠ 0}
  have h (l : S) : False := l.property rfl
  exact ⟨⟨fun _ => ∅, fun i => (h i).elim, fun i => (h i).elim, fun i => (h i).elim⟩⟩

/-- The best operator-norm approximation by a path with a twin line
model has linear order. The zero path supplies the upper bound. -/
theorem gaussian_ae_twinLine_operator_distance_linear_order :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ (ρ : Type*) [DecidableEq ρ],
        (∀ v : PathShell n, Nonempty (TwinLineModel (pathFrustrationAdj {l | v l ≠ 0}) ρ) →
          c * ((n + 2 : ℕ) : ℝ) ≤ ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖) ∧
        (∃ v : PathShell n, Nonempty (TwinLineModel (pathFrustrationAdj {l | v l ≠ 0}) ρ) ∧
          ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖ ≤ C * ((n + 2 : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hUpper⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let c := gaussianClawErasureMean / 24
  have hc : 0 < c := div_pos gaussianClawErasureMean_pos (by norm_num)
  have hlt : c < gaussianClawErasureMean / 12 := by dsimp [c]; linarith [gaussianClawErasureMean_pos]
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hUpper, gaussian_ae_eventually_twinLine_operator_linear_gap] with ω hω hgap
  filter_upwards [hω, hgap c hlt] with n hnorm hsep
  intro ρ _
  refine ⟨hsep ρ, 0, zero_admits_twinLineModel n ρ, ?_⟩
  have hz : pathHamiltonian (0 : PathShell n) = 0 := (pathHamiltonianLM n).map_zero
  rw [hz, sub_zero]
  exact hnorm

/-- Even after choosing a phase, one twin line generator cannot track
the Gaussian evolution throughout a fixed inverse-size observation window. -/
theorem gaussian_ae_twinLine_projective_separation :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ (ρ : Type*) [DecidableEq ρ], ∀ v : PathShell n,
        Nonempty (TwinLineModel (pathFrustrationAdj {l | v l ≠ 0}) ρ) →
          ∃ t : ℝ, 0 < t ∧ t ≤ A / ((n + 2 : ℕ) : ℝ) ∧ ∀ z : ℂ, ‖z‖ = 1 →
            ε ≤ ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t -
              z • unitaryEvolution (pathHamiltonian v) t‖ := by
  obtain ⟨C, hC, hUpper⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let c := gaussianClawErasureMean / 24
  have hc : 0 < c := div_pos gaussianClawErasureMean_pos (by norm_num)
  have hlt : c < gaussianClawErasureMean / 12 := by dsimp [c]; linarith [gaussianClawErasureMean_pos]
  refine ⟨1 / c, (c / (c + C)) ^ 2 / 96, one_div_pos.mpr hc, by positivity, ?_⟩
  filter_upwards [hUpper, gaussian_ae_eventually_twinLine_operator_linear_gap] with ω hω hgap
  filter_upwards [hω, hgap c hlt] with n hnorm hsep
  intro ρ _ v hv
  let u := pathPauliDisorderShell ω n
  refine exists_time_projective_unitaryEvolution_separation (pathHamiltonian u) (pathHamiltonian v)
    (isSelfAdjoint_pathHamiltonian _) (isSelfAdjoint_pathHamiltonian _) ?_
    hc hC (by positivity) hnorm (hsep ρ v hv)
  rw [Matrix.trace_sub, trace_pathHamiltonian_zero, trace_pathHamiltonian_zero, sub_self]

#print axioms exists_zero_of_twinLineModel_clawBlock
#print axioms sum_clawBlockErasureWeight_le_operator_dist
#print axioms gaussianClawErasureMean_pos
#print axioms gaussian_ae_pairedRows_mean
#print axioms gaussian_ae_clawErasure_per_site
#print axioms gaussian_ae_eventually_twinLine_operator_linear_gap
#print axioms gaussian_ae_twinLine_operator_distance_linear_order
#print axioms gaussian_ae_twinLine_projective_separation

end

end GaloisForLFunctions.HTGeometry
