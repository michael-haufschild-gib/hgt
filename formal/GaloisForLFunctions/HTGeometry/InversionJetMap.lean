import GaloisForLFunctions.HTGeometry.TriangularSolveContinuity

/-!
# The jet map of a reciprocal is a continuous involution

The jets of `1 / f` are determined by the jets of `f` through the Leibniz relation for `f · (1/f) =
1`.  Read as a system in the unknown jets that relation is triangular with diagonal `f(z)`, so it has
a unique solution, continuous in the data.

The relation is symmetric in the two jet sequences, so the solution map is its own inverse: the
reciprocal jet map is a continuous involution of the packets with nonvanishing zeroth entry, hence a
homeomorphism, hence open.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Leibniz pairing of two jet sequences in order `k`. -/
def leibnizJetSum (y g : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℂ) * y i * g (k - i)

/-- The Leibniz pairing is symmetric. -/
theorem leibnizJetSum_comm (y g : ℕ → ℂ) (k : ℕ) :
    leibnizJetSum y g k = leibnizJetSum g y k := by
  rw [leibnizJetSum, leibnizJetSum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hik : i ≤ k := by omega
  have h1 : k + 1 - 1 - i = k - i := by omega
  have h2 : k - (k - i) = i := by omega
  rw [h1, h2, Nat.choose_symm hik]
  ring

/-- The part of the Leibniz pairing below the diagonal. -/
def invJetLower (y : ℕ → ℂ) (k : ℕ) (g : ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range k, ((k.choose (i + 1) : ℕ) : ℂ) * y (i + 1) * g (k - (i + 1))

theorem leibnizJetSum_eq (y g : ℕ → ℂ) (k : ℕ) :
    leibnizJetSum y g k = y 0 * g k + invJetLower y k g := by
  rw [leibnizJetSum, Finset.sum_range_succ', invJetLower]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  ring

theorem invJetLower_congr (y : ℕ → ℂ) (k : ℕ) (g g' : ℕ → ℂ) (h : ∀ j, j < k → g j = g' j) :
    invJetLower y k g = invJetLower y k g' := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [h (k - (i + 1)) (by omega)]

/-- The jets of a reciprocal, as the solution of the Leibniz system. -/
def invJetScalar (y : ℕ → ℂ) : ℕ → ℂ :=
  triangularSolve (y 0) (invJetLower y) fun k => if k = 0 then 1 else 0

/-- **The reciprocal jets pair to the unit.** -/
theorem leibnizJetSum_invJetScalar {y : ℕ → ℂ} (hy : y 0 ≠ 0) (k : ℕ) :
    leibnizJetSum y (invJetScalar y) k = if k = 0 then 1 else 0 := by
  rw [leibnizJetSum_eq]
  exact triangularSolve_spec hy (invJetLower y) (invJetLower_congr y) _ k

/-- **The pairing determines the reciprocal jets.** -/
theorem eq_invJetScalar_of_leibnizJetSum {y g : ℕ → ℂ} (hy : y 0 ≠ 0)
    (hg : ∀ k, leibnizJetSum y g k = if k = 0 then 1 else 0) (k : ℕ) :
    g k = invJetScalar y k := by
  refine triangularSolve_unique hy (invJetLower y) (invJetLower_congr y) _ g ?_ k
  intro m
  rw [← leibnizJetSum_eq]
  exact hg m

theorem invJetScalar_zero {y : ℕ → ℂ} (hy : y 0 ≠ 0) : invJetScalar y 0 = (y 0)⁻¹ := by
  have h := leibnizJetSum_invJetScalar hy 0
  rw [leibnizJetSum_eq] at h
  simp only [invJetLower, Finset.range_zero, Finset.sum_empty, add_zero] at h
  norm_num at h
  field_simp
  linear_combination h

theorem invJetScalar_zero_ne_zero {y : ℕ → ℂ} (hy : y 0 ≠ 0) : invJetScalar y 0 ≠ 0 := by
  rw [invJetScalar_zero hy]
  exact inv_ne_zero hy

/-- **The reciprocal jet map is an involution.** -/
theorem invJetScalar_invJetScalar {y : ℕ → ℂ} (hy : y 0 ≠ 0) (k : ℕ) :
    invJetScalar (invJetScalar y) k = y k := by
  refine (eq_invJetScalar_of_leibnizJetSum (invJetScalar_zero_ne_zero hy) ?_ k).symm
  intro m
  rw [leibnizJetSum_comm]
  exact leibnizJetSum_invJetScalar hy m

/-! ## The jet map computes the derivatives of a reciprocal -/

/-- **The recursion computes the derivatives of a reciprocal.** -/
theorem invJetScalar_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) f U) (hfne : ∀ w ∈ U, f w ≠ 0) {z : ℂ} (hz : z ∈ U) (k : ℕ) :
    iteratedDeriv k (fun w => (f w)⁻¹) z = invJetScalar (fun j => iteratedDeriv j f z) k := by
  have hy0 : (fun j => iteratedDeriv j f z) 0 ≠ 0 := by
    simpa using hfne z hz
  refine eq_invJetScalar_of_leibnizJetSum (y := fun j => iteratedDeriv j f z)
    (g := fun j => iteratedDeriv j (fun w => (f w)⁻¹) z) hy0 (fun m => ?_) k
  have hinv : ContDiffOn ℂ (⊤ : ℕ∞) (fun w => (f w)⁻¹) U := hf.inv hfne
  have hfm : ContDiffAt ℂ ((m : ℕ) : ℕ∞) f z :=
    (hf.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast (le_top : ((m : ℕ) : ℕ∞) ≤ ⊤))
  have hinvm : ContDiffAt ℂ ((m : ℕ) : ℕ∞) (fun w => (f w)⁻¹) z :=
    (hinv.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast (le_top : ((m : ℕ) : ℕ∞) ≤ ⊤))
  have hprod : (fun w => f w * (f w)⁻¹) =ᶠ[nhds z] fun _ => (1 : ℂ) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact mul_inv_cancel₀ (hfne w hw)
  have hone : iteratedDeriv m (fun w => f w * (f w)⁻¹) z = if m = 0 then 1 else 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq m hprod]
    cases m with
    | zero => simp
    | succ m => simp [iteratedDeriv_succ']
  rw [← hone, iteratedDeriv_fun_mul hfm hinvm, leibnizJetSum]

/-! ## Continuity and openness -/

theorem continuousOn_invJetScalar (k : ℕ) :
    ContinuousOn (fun y : ℕ → ℂ => invJetScalar y k) {y : ℕ → ℂ | y 0 ≠ 0} := by
  have heq : (fun y : ℕ → ℂ => invJetScalar y k)
      = fun y : ℕ → ℂ =>
        triangularSolve (y 0) (invJetLower y) (fun j => if j = 0 then 1 else 0) k := rfl
  rw [heq]
  refine continuousOn_triangularSolve (V := {y : ℕ → ℂ | y 0 ≠ 0}) (d := fun y : ℕ → ℂ => y 0)
    (L := fun y : ℕ → ℂ => invJetLower y)
    (w := fun _ : ℕ → ℂ => fun j : ℕ => if j = 0 then (1 : ℂ) else 0)
    ((continuous_apply (0 : ℕ)).continuousOn) (fun y hy => hy) ?_
    (fun j => continuousOn_const) k
  intro j u hu
  refine continuousOn_finsetSum _ fun i hi => ?_
  exact (continuousOn_const.mul ((continuous_apply (i + 1)).continuousOn)).mul
    (hu (j - (i + 1)))

/-- **The reciprocal jet map carries neighbourhoods to neighbourhoods.** -/
theorem invJetScalar_image_mem_nhds {y : ℕ → ℂ} (hy : y 0 ≠ 0) {N : Set (ℕ → ℂ)}
    (hN : N ∈ nhds y) :
    (fun v : ℕ → ℂ => fun k => invJetScalar v k) '' N
      ∈ nhds (fun k => invJetScalar y k) := by
  classical
  set V : Set (ℕ → ℂ) := {w : ℕ → ℂ | w 0 ≠ 0} with hV
  have hVopen : IsOpen V := by
    have hpre : V = (fun p : ℕ → ℂ => p 0) ⁻¹' ({(0 : ℂ)}ᶜ) := by
      ext w
      simp [hV]
    rw [hpre]
    exact isOpen_compl_singleton.preimage (continuous_apply (0 : ℕ))
  have hΨ : ContinuousOn (fun w : ℕ → ℂ => (fun k => invJetScalar w k)) V := by
    rw [continuousOn_pi]
    exact fun k => continuousOn_invJetScalar k
  have hmemV : (fun k => invJetScalar y k) ∈ V := invJetScalar_zero_ne_zero hy
  have hback : (fun k => invJetScalar (fun k => invJetScalar y k) k) = y := by
    funext k
    exact invJetScalar_invJetScalar hy k
  have hpre : (fun w : ℕ → ℂ => (fun k => invJetScalar w k)) ⁻¹' N
      ∈ nhdsWithin (fun k => invJetScalar y k) V := by
    refine hΨ _ hmemV ?_
    have hred : ((fun w : ℕ → ℂ => fun k => invJetScalar w k) fun k => invJetScalar y k) = y :=
      hback
    rw [hred]
    exact hN
  obtain ⟨W₀, hW₀open, hW₀mem, hW₀sub⟩ := mem_nhdsWithin.mp hpre
  refine Filter.mem_of_superset ((hW₀open.inter hVopen).mem_nhds ⟨hW₀mem, hmemV⟩) ?_
  rintro w ⟨hwW, hwV⟩
  refine ⟨fun k => invJetScalar w k, hW₀sub ⟨hwW, hwV⟩, ?_⟩
  funext k
  exact invJetScalar_invJetScalar hwV k

end

end GaloisForLFunctions.HTGeometry
