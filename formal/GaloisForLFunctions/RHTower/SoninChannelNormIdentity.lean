import GaloisForLFunctions.RHTower.SoninShellLayerProjections
import GaloisForLFunctions.RHTower.SoninBurnolLogShellChannel

/-!
# The exact energy of a step multiplier along the tower

Pairwise orthogonal vectors add in squares, so a step multiplier along the cutoff tower has an
exact energy: one term per layer, the squared coefficient times the squared layer mass.  The
triangle inequality only bounds this from above; the identity also bounds it from below, which is
what a divergence statement needs.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Finite Pythagoras.**  Pairwise orthogonal vectors add in squares. -/
theorem norm_sum_sq_of_pairwise_inner_eq_zero {ι : Type*} (s : Finset ι) (v : ι → E)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_𝕜 = 0) :
    ‖∑ i ∈ s, v i‖ ^ (2 : ℕ) = ∑ i ∈ s, ‖v i‖ ^ (2 : ℕ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hcross : ⟪v a, ∑ i ∈ s, v i⟫_𝕜 = 0 := by
        rw [inner_sum]
        refine Finset.sum_eq_zero fun i hi => ?_
        refine h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) ?_
        rintro rfl
        exact ha hi
      have hrest : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_𝕜 = 0 := fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      rw [Finset.sum_insert ha, Finset.sum_insert ha, @norm_add_sq 𝕜, hcross, map_zero, ih hrest]
      ring

/-- The layers of the tower are pairwise orthogonal on any vector. -/
theorem inner_layer_apply_eq_zero_of_ne (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (u : evenSubspace)
    {j k : ℕ} (hjk : j ≠ k) :
    ⟪evenIndicatorLayer (logShellRadius a r j) (logShellRadius a r (j + 1)) u,
      evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u⟫_ℂ = 0 := by
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · exact inner_evenIndicatorLayer_apply_eq_zero (logShellRadius_lt_succ ha hr j).le
      (logShellRadius_mono ha hr (Nat.succ_le_of_lt hlt))
      (logShellRadius_lt_succ ha hr k).le u u
  · have h := inner_evenIndicatorLayer_apply_eq_zero (logShellRadius_lt_succ ha hr k).le
      (logShellRadius_mono ha hr (Nat.succ_le_of_lt hgt))
      (logShellRadius_lt_succ ha hr j).le u u
    rw [← inner_conj_symm, h, map_zero]

/-- **Exact channel energy.**  The channel's squared norm on a vector is the sum over layers of the
squared layer logarithm times the squared layer mass. -/
theorem norm_sq_evenLogShellChannel_apply (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ)
    (u : evenSubspace) :
    ‖evenLogShellChannel a r n u‖ ^ (2 : ℕ) =
      ∑ k ∈ Finset.range n, |Real.log (logShellRadius a r k)| ^ (2 : ℕ) *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) := by
  classical
  set v : ℕ → evenSubspace := fun k =>
    ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u with hv
  have happly : evenLogShellChannel a r n u = ∑ k ∈ Finset.range n, v k := by
    rw [evenLogShellChannel, sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      ((evenIndicatorCutoff (logShellRadius a r (k + 1)) -
        evenIndicatorCutoff (logShellRadius a r k)) u) = v k
    rfl
  have hortho : ∀ j ∈ Finset.range n, ∀ k ∈ Finset.range n, j ≠ k →
      ⟪v j, v k⟫_ℂ = 0 := by
    intro j _ k _ hjk
    show ⟪((Real.log (logShellRadius a r j) : ℝ) : ℂ) •
        evenIndicatorLayer (logShellRadius a r j) (logShellRadius a r (j + 1)) u,
      ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
        evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u⟫_ℂ = 0
    rw [inner_smul_left (𝕜 := ℂ)
        (evenIndicatorLayer (logShellRadius a r j) (logShellRadius a r (j + 1)) u)
        (((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
          evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u),
      inner_smul_right (𝕜 := ℂ)
        (evenIndicatorLayer (logShellRadius a r j) (logShellRadius a r (j + 1)) u)
        (evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u),
      inner_layer_apply_eq_zero_of_ne a r ha hr u hjk, mul_zero, mul_zero]
  have hterm : ∀ k : ℕ, ‖v k‖ ^ (2 : ℕ) = |Real.log (logShellRadius a r k)| ^ (2 : ℕ) *
      ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) := by
    intro k
    show ‖((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) = _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  rw [happly, norm_sum_sq_of_pairwise_inner_eq_zero (𝕜 := ℂ) _ v hortho]
  exact Finset.sum_congr rfl fun k _ => hterm k

/-- **Two-radius lower bound, with no support hypothesis.**  The channel's energy is at least the
smallest layer logarithm in a range, times the mass the vector has between the two radii of that
range. -/
theorem sq_le_norm_sq_evenLogShellChannel_apply
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n m : ℕ) (hmn : m ≤ n) (u : evenSubspace)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ k, m ≤ k → k < n → L ≤ |Real.log (logShellRadius a r k)|) :
    L ^ (2 : ℕ) * (‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r n) u‖ ^ (2 : ℕ) -
        ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r m) u‖ ^ (2 : ℕ)) ≤
      ‖evenLogShellChannel a r n u‖ ^ (2 : ℕ) := by
  classical
  set P : ℕ → evenSubspace := fun k =>
    evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u with hP
  have hmass : ∀ j : ℕ, ∑ k ∈ Finset.range j, ‖P k‖ ^ (2 : ℕ) =
      ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r j) u‖ ^ (2 : ℕ) := by
    intro j
    have hsum := DFunLike.congr_fun (sum_evenIndicatorLayer (fun k => logShellRadius a r k) j) u
    rw [sum_apply] at hsum
    have hpy := norm_sum_sq_of_pairwise_inner_eq_zero (𝕜 := ℂ) (Finset.range j) P
      (fun i _ k _ hik => inner_layer_apply_eq_zero_of_ne a r ha hr u hik)
    rw [← hpy, hsum]
    rfl
  have hsplit : ∑ k ∈ Finset.range m, ‖P k‖ ^ (2 : ℕ) + ∑ k ∈ Finset.Ico m n, ‖P k‖ ^ (2 : ℕ) =
      ∑ k ∈ Finset.range n, ‖P k‖ ^ (2 : ℕ) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le m) hmn
  have hIco : L ^ (2 : ℕ) * (∑ k ∈ Finset.Ico m n, ‖P k‖ ^ (2 : ℕ)) ≤
      ∑ k ∈ Finset.Ico m n, |Real.log (logShellRadius a r k)| ^ (2 : ℕ) * ‖P k‖ ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨hmk, hkn⟩ := Finset.mem_Ico.mp hk
    have hsq : L ^ (2 : ℕ) ≤ |Real.log (logShellRadius a r k)| ^ (2 : ℕ) := by
      have := hL k hmk hkn
      nlinarith
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hdrop : ∑ k ∈ Finset.Ico m n, |Real.log (logShellRadius a r k)| ^ (2 : ℕ) * ‖P k‖ ^ (2 : ℕ) ≤
      ∑ k ∈ Finset.range n, |Real.log (logShellRadius a r k)| ^ (2 : ℕ) * ‖P k‖ ^ (2 : ℕ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hid := norm_sq_evenLogShellChannel_apply a r ha hr n u
  have hmn' := hmass n
  have hmm := hmass m
  have hgap : ∑ k ∈ Finset.Ico m n, ‖P k‖ ^ (2 : ℕ) =
      ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r n) u‖ ^ (2 : ℕ) -
        ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r m) u‖ ^ (2 : ℕ) := by
    rw [← hmn', ← hmm, ← hsplit]
    ring
  rw [hid, ← hgap]
  exact le_trans hIco hdrop

/-- **Lower bound.**  On a vector living between two tower radii the channel is at least the
smallest layer logarithm in that range. -/
theorem le_norm_evenLogShellChannel_apply
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n m : ℕ) (u : evenSubspace)
    (hlow : evenIndicatorCutoff (logShellRadius a r m) u = 0)
    (hhigh : evenIndicatorCutoff (logShellRadius a r n) u = u)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ k, m ≤ k → k < n → L ≤ |Real.log (logShellRadius a r k)|) :
    L * ‖u‖ ≤ ‖evenLogShellChannel a r n u‖ := by
  classical
  have hkill : ∀ s : ℝ, s ≤ logShellRadius a r m → evenIndicatorCutoff s u = 0 := by
    intro s hs
    have hnest := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le s _ hs) u
    simp only [mul_apply_eq_comp, hlow, map_zero] at hnest
    exact hnest.symm
  have hlayer_zero : ∀ k : ℕ, k < m →
      evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u = 0 := by
    intro k hk
    have h₁ : evenIndicatorCutoff (logShellRadius a r (k + 1)) u = 0 :=
      hkill _ (logShellRadius_mono ha hr (Nat.succ_le_of_lt hk))
    have h₂ : evenIndicatorCutoff (logShellRadius a r k) u = 0 :=
      hkill _ (logShellRadius_mono ha hr hk.le)
    rw [evenIndicatorLayer, sub_apply, h₁, h₂, sub_zero]
  have hsum : ∑ k ∈ Finset.range n,
      evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u = u := by
    have h := DFunLike.congr_fun (sum_evenIndicatorLayer (fun k => logShellRadius a r k) n) u
    rw [sum_apply, sub_apply, hhigh, hkill _ (logShellRadius_mono ha hr (Nat.zero_le m))] at h
    simpa using h
  have hnormu : ‖u‖ ^ (2 : ℕ) = ∑ k ∈ Finset.range n,
      ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) := by
    conv_lhs => rw [← hsum]
    exact norm_sum_sq_of_pairwise_inner_eq_zero (𝕜 := ℂ) (Finset.range n)
      (fun k => evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u)
      (fun j _ k _ hjk => inner_layer_apply_eq_zero_of_ne a r ha hr u hjk)
  have hterm : ∀ k ∈ Finset.range n,
      L ^ (2 : ℕ) * ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) ≤
        |Real.log (logShellRadius a r k)| ^ (2 : ℕ) *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) := by
    intro k hk
    rcases lt_or_ge k m with hkm | hkm
    · rw [hlayer_zero k hkm]
      simp
    · have hLk := hL k hkm (Finset.mem_range.mp hk)
      have hsq : L ^ (2 : ℕ) ≤ |Real.log (logShellRadius a r k)| ^ (2 : ℕ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hchain : L ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) ≤ ‖evenLogShellChannel a r n u‖ ^ (2 : ℕ) := by
    rw [norm_sq_evenLogShellChannel_apply a r ha hr n u, hnormu, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  nlinarith [norm_nonneg (evenLogShellChannel a r n u), norm_nonneg u,
    mul_nonneg hL0 (norm_nonneg u)]

end RHTower
