import GaloisForLFunctions.HTGeometry.TwoLocalRealSliceGenericity

open scoped BigOperators Matrix.Norms.Elementwise
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- Every nonconstant real spectral action of an embedded universal
two-local analytic branch packet escapes every prescribed constant inside
the same branch chart. -/
theorem exists_embeddedTwoLocalBranchAction_ne_const
    {m : ℕ}
    (M : Matrix (Fin n → Bool) (Fin n → Bool)
      (MvPolynomial (Fin m) ℂ))
    (embed : (HypercubeTwoLocalParameter n → ℂ) → (Fin m → ℂ))
    (shiftReal : (HypercubeTwoLocalParameter n → ℝ) → ℝ)
    (hembedCont : Continuous embed)
    (hembedSlice : ∀ (p : HypercubeTwoLocalParameter n → ℝ)
      (i : Fin n) (q : ℝ × ℝ),
      M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (embed (twoLocalEdgeSlice p i q))) =
        hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q) -
          ((shiftReal p : ℝ) : ℂ) •
            (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (p : HypercubeTwoLocalParameter n → ℝ)
    (V : Set (Fin m → ℂ))
    (branch : (Fin n → Bool) → (Fin m → ℂ) → ℂ)
    (htr : ∀ i : Fin n, p (.transverse i) = 0)
    (hinj : Function.Injective (hypercubeTwoLocalEnergy p))
    (hgappos : ∀ (i : Fin n) (z : qubitEnvironment n i),
      0 < edgeGap i (hypercubeTwoLocalEnergy p) z)
    (hgapinj : ∀ i : Fin n,
      Function.Injective (edgeGap i (hypercubeTwoLocalEnergy p)))
    (hVopen : IsOpen V)
    (hz₀V : embed (fun theta => (p theta : ℂ)) ∈ V)
    (hbranchA : ∀ x, AnalyticOnNhd ℂ (branch x) V)
    (hbranch0 : ∀ x,
      branch x (embed fun theta => (p theta : ℂ)) =
        ((hypercubeTwoLocalEnergy p x - shiftReal p : ℝ) : ℂ))
    (hbranchRoot : ∀ x, ∀ z ∈ V, matrixCharpolyRelation
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z), branch x z) = 0)
    (W : Set (ℝ × ℝ)) (hW : W ∈ 𝓝 ((0, 0) : ℝ × ℝ))
    (c : (Fin n → Bool) → ℝ)
    (hc : ¬ ∀ x y, c x = c y)
    (target : ℝ) :
    ∃ i : Fin n, ∃ q ∈ W,
      embed (twoLocalEdgeSlice p i q) ∈ V ∧
        (∑ x, (c x : ℂ) *
          branch x (embed (twoLocalEdgeSlice p i q))) ≠ (target : ℂ) := by
  classical
  obtain ⟨x₁, y₁, hxy⟩ : ∃ x y : Fin n → Bool, c x ≠ c y := by
    by_contra hcon
    push Not at hcon
    exact hc hcon
  obtain ⟨w, i, hwi⟩ := exists_boolToggle_ne_of_ne c hxy
  set env : qubitEnvironment n i := fun j => w j.1 with henvdef
  have hstate : edgeState i env (w i) = w := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [edgeState_self]
    · rw [edgeState_of_ne i env (w i) hj]
  have htoggle : edgeState i env (!(w i)) = boolToggle w i := by
    rw [← boolToggle_edgeState, hstate]
  have hstateNe : c (edgeState i env false) ≠ c (edgeState i env true) := by
    cases hw : w i with
    | false =>
        have h₀ : edgeState i env false = w := by
          rw [← hw]
          exact hstate
        have h₁ : edgeState i env true = boolToggle w i := by
          have h := htoggle
          rw [hw] at h
          exact h
        rw [h₀, h₁]
        exact fun hcon => hwi hcon.symm
    | true =>
        have h₁ : edgeState i env true = w := by
          rw [← hw]
          exact hstate
        have h₀ : edgeState i env false = boolToggle w i := by
          have h := htoggle
          rw [hw] at h
          exact h
        rw [h₀, h₁]
        exact hwi
  set kappa : Fin 2 × qubitEnvironment n i → ℝ :=
    fun q => c (edgeEquiv i q) with hkappadef
  have hkappane : kappa (0, env) - kappa (1, env) ≠ 0 := by
    rw [sub_ne_zero]
    simpa [hkappadef, edgeEquiv_zero, edgeEquiv_one] using hstateNe
  set slice : ℝ × ℝ → (Fin m → ℂ) :=
    fun q => embed (twoLocalEdgeSlice p i q) with hslicedef
  set E : (Fin n → Bool) → ℝ := hypercubeTwoLocalEnergy p with hEdef
  set s : ℝ := shiftReal p with hsdef
  set mBlk : qubitEnvironment n i → ℝ :=
    fun z => edgeMean i E z - s with hmBlk
  have hsliceParam0 :
      twoLocalEdgeSlice p i (0, 0) = fun theta => (p theta : ℂ) := by
    funext theta
    simp [twoLocalEdgeSlice]
  have hslice0 : slice (0, 0) = embed fun theta => (p theta : ℂ) := by
    show embed (twoLocalEdgeSlice p i (0, 0)) = _
    rw [hsliceParam0]
  have hsliceCont : Continuous slice := by
    refine hembedCont.comp ?_
    refine continuous_pi fun theta => ?_
    simp only [twoLocalEdgeSlice, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hHslice : ∀ q : ℝ × ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (slice q))).submatrix
          (edgeEquiv i) (edgeEquiv i) =
        shiftedBlockSplitMatrix mBlk (edgeGap i E) q := by
    intro q
    have hsub :
        ((hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q) -
          ((shiftReal p : ℝ) : ℂ) •
            (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).submatrix
              (edgeEquiv i) (edgeEquiv i)) =
          (hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q)).submatrix
              (edgeEquiv i) (edgeEquiv i) -
            ((shiftReal p : ℝ) : ℂ) •
              (1 : Matrix (Fin 2 × qubitEnvironment n i)
                (Fin 2 × qubitEnvironment n i) ℂ) := by
      ext a b
      simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, (edgeEquiv i).injective.eq_iff]
    rw [hslicedef, hembedSlice p i q, hsub,
      submatrix_hypercubeTwoLocalMatrix_twoLocalEdgeSlice p i htr q,
      hmBlk, hsdef, shiftedBlockSplitMatrix_sub_smul_one]
  have hblockEnergy : ∀ q' : Fin 2 × qubitEnvironment n i,
      blockEnergy mBlk (edgeGap i E) q' = E (edgeEquiv i q') - s := by
    intro q'
    rw [hmBlk, blockEnergy_sub_const, blockEnergy_edge]
  have hblockinj : Function.Injective fun q' : Fin 2 × qubitEnvironment n i =>
      ((blockEnergy mBlk (edgeGap i E) q' : ℝ) : ℂ) := by
    intro a b hab
    have hab' : ((blockEnergy mBlk (edgeGap i E) a : ℝ) : ℂ) =
        ((blockEnergy mBlk (edgeGap i E) b : ℝ) : ℂ) := hab
    rw [hblockEnergy, hblockEnergy] at hab'
    have hreal : E (edgeEquiv i a) - s = E (edgeEquiv i b) - s :=
      Complex.ofReal_injective hab'
    exact (edgeEquiv i).injective (hinj (by linarith [hreal]))
  have hWmem : slice ⁻¹' V ∈ 𝓝 ((0, 0) : ℝ × ℝ) := by
    refine hsliceCont.continuousAt.preimage_mem_nhds ?_
    rw [hslice0]
    exact hVopen.mem_nhds hz₀V
  obtain ⟨q, hqW, hqne⟩ :=
    exists_shifted_split_branch_relation_ne_const
      mBlk (edgeGap i E) (hgappos i) (hgapinj i) hblockinj
      (fun q' qq => branch (edgeEquiv i q') (slice qq))
      (fun q' => by
        have h₁ : ContinuousAt (branch (edgeEquiv i q')) (slice (0, 0)) := by
          rw [hslice0]
          exact (hbranchA (edgeEquiv i q') _ hz₀V).continuousAt
        exact h₁.comp hsliceCont.continuousAt)
      (fun q' => by
        rw [hslice0, hbranch0 (edgeEquiv i q'), hblockEnergy])
      (fun q' => by
        filter_upwards [hWmem] with qq hqq
        rw [← hHslice qq, matrixCharpolyRelation_submatrix_equiv]
        exact hbranchRoot (edgeEquiv i q') (slice qq) hqq)
      kappa hkappane target (Filter.inter_mem hWmem hW)
  refine ⟨i, q, hqW.2, hqW.1, ?_⟩
  change (∑ x, (c x : ℂ) * branch x (slice q)) ≠ (target : ℂ)
  have hreindex :
      (∑ x, (c x : ℂ) * branch x (slice q)) =
        ∑ q' : Fin 2 × qubitEnvironment n i,
          (kappa q' : ℂ) * branch (edgeEquiv i q') (slice q) :=
    (Fintype.sum_equiv (edgeEquiv i) _ _ fun q' => by
      simp [hkappadef]).symm
  rw [hreindex]
  exact hqne

end GaloisForLFunctions.HTGeometry
