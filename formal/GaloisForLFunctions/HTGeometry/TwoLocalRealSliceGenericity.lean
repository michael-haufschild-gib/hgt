import GaloisForLFunctions.HTGeometry.TwoLocalEdgeSliceFamily
import GaloisForLFunctions.HTGeometry.AnalyticEscapeGenericityTransfer
import GaloisForLFunctions.HTGeometry.SimpleSpectrumAnalyticBranch
import GaloisForLFunctions.HTGeometry.HypercubeCharacterNonconstancy
import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity

/-!
# Almost every real two-local Hamiltonian has no rational spectral relation

The all-qubit two-local family, with its coefficients numbered by a finite index, is a polynomial
matrix family.  Through a diagonal base with simple spectrum and simple positive edge gaps runs the
two-parameter edge slice of every qubit, and on that slice the family is the shifted block splitting
of the base energies.  A nonzero balanced integer character is nonconstant, hence differs across
some hypercube edge, so the block splitting of that edge escapes it arbitrarily close to the base.

Every labelling of every nonzero balanced relation is therefore escaped inside one chart around the
base, and the analytic escape transfer turns that into the real-parameter statement: outside a
meagre Lebesgue-null set of coefficients, the `2^n` energies are simple and satisfy no balanced
integer relation.
-/

open scoped BigOperators Matrix.Norms.Elementwise
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- Numbering of the two-local coefficients. -/
noncomputable def twoLocalParameterEquivFin (n : ℕ) :
    HypercubeTwoLocalParameter n ≃ Fin (Fintype.card (HypercubeTwoLocalParameter n)) :=
  Fintype.equivFin _

/-- The all-qubit two-local polynomial matrix family in numbered coefficients. -/
noncomputable def hypercubeTwoLocalFinPolynomialMatrix (n : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool)
      (MvPolynomial (Fin (Fintype.card (HypercubeTwoLocalParameter n))) ℂ) :=
  (universalHypercubeTwoLocalPolynomialMatrix n).map
    (MvPolynomial.rename (twoLocalParameterEquivFin n))

theorem map_eval_hypercubeTwoLocalFinPolynomialMatrix
    (z : Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℂ) :
    (hypercubeTwoLocalFinPolynomialMatrix n).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) z)
      = hypercubeTwoLocalMatrix (fun θ => z (twoLocalParameterEquivFin n θ)) := by
  rw [hypercubeTwoLocalFinPolynomialMatrix, Matrix.map_map]
  have hcomp : (fun P => MvPolynomial.eval₂Hom (RingHom.id ℂ) z
      ((MvPolynomial.rename (twoLocalParameterEquivFin n)) P))
      = fun P => MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun θ => z (twoLocalParameterEquivFin n θ)) P := by
    funext P
    show MvPolynomial.eval₂ (RingHom.id ℂ) z
        ((MvPolynomial.rename (twoLocalParameterEquivFin n)) P) = _
    rw [MvPolynomial.eval₂_rename]
    rfl
  show (universalHypercubeTwoLocalPolynomialMatrix n).map
      (fun P => MvPolynomial.eval₂Hom (RingHom.id ℂ) z
        ((MvPolynomial.rename (twoLocalParameterEquivFin n)) P)) = _
  rw [hcomp]
  exact eval_universalHypercubeTwoLocalPolynomialMatrix n
    (fun θ => z (twoLocalParameterEquivFin n θ))

/-- Toggling one qubit twice restores the configuration. -/
theorem boolToggle_boolToggle (x : Fin n → Bool) (i : Fin n) :
    boolToggle (boolToggle x i) i = x := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [boolToggle]
  · simp [boolToggle, Function.update_of_ne hj]

/-- The edge relation of a qubit is symmetric. -/
theorem boolToggle_eq_comm {x y : Fin n → Bool} {i : Fin n} :
    y = boolToggle x i ↔ x = boolToggle y i := by
  constructor <;> intro h <;> subst h <;> rw [boolToggle_boolToggle]

/-- At real coefficients the two-local Hamiltonian is Hermitian. -/
theorem isHermitian_hypercubeTwoLocalMatrix (p : HypercubeTwoLocalParameter n → ℝ) :
    (hypercubeTwoLocalMatrix (fun θ => (p θ : ℂ))).IsHermitian := by
  classical
  refine Matrix.IsHermitian.ext fun x y => ?_
  by_cases hxy : y = x
  · subst hxy
    rw [hypercubeTwoLocalMatrix_diagonal_entry]
    exact Complex.conj_ofReal _
  · rw [hypercubeTwoLocalMatrix_offdiagonal_entry _ (fun h => hxy h.symm),
      hypercubeTwoLocalMatrix_offdiagonal_entry _ hxy, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hy : y = boolToggle x i
    · rw [if_pos hy, if_pos (boolToggle_eq_comm.mp hy)]
      exact Complex.conj_ofReal _
    · rw [if_neg hy, if_neg (fun hcon => hy (boolToggle_eq_comm.mpr hcon))]
      exact star_zero ℂ


/-- The numbered two-local family is entire in its coefficients. -/
theorem analyticAt_hypercubeTwoLocalFinFamily
    (z₀ : Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℂ) :
    AnalyticAt ℂ (fun z => (hypercubeTwoLocalFinPolynomialMatrix n).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) z)) z₀ := by
  have hfun : (fun z => (hypercubeTwoLocalFinPolynomialMatrix n).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) z))
      = fun z => hypercubeTwoLocalMatrix (fun θ => z (twoLocalParameterEquivFin n θ)) :=
    funext fun z => map_eval_hypercubeTwoLocalFinPolynomialMatrix z
  rw [hfun]
  have hL : AnalyticAt ℂ (fun z : Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℂ =>
      fun θ => z (twoLocalParameterEquivFin n θ)) z₀ :=
    AnalyticAt.pi fun θ => (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin (Fintype.card (HypercubeTwoLocalParameter n)) => ℂ)
      (twoLocalParameterEquivFin n θ)).analyticAt z₀
  exact (analyticAt_hypercubeTwoLocalMatrix _).comp hL

/-- The numbered coefficient vector of a real parameter vector. -/
noncomputable def twoLocalFinCoefficients (p : HypercubeTwoLocalParameter n → ℝ) :
    Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℂ :=
  fun t => ((p ((twoLocalParameterEquivFin n).symm t) : ℝ) : ℂ)

theorem eval_twoLocalFinCoefficients (p : HypercubeTwoLocalParameter n → ℝ) :
    (hypercubeTwoLocalFinPolynomialMatrix n).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (twoLocalFinCoefficients p))
      = hypercubeTwoLocalMatrix (fun θ => (p θ : ℂ)) := by
  rw [map_eval_hypercubeTwoLocalFinPolynomialMatrix]
  congr 1
  funext θ
  simp [twoLocalFinCoefficients]


/-- **One analytic chart around a two-local diagonal base.**  For any polynomial matrix family which
realizes the two-local coefficients up to a constant energy offset, there is a connected open set of
complex parameters around the image of a diagonal base carrying analytic eigenvalue branches through
every base energy, simple and root-valued throughout. -/
theorem exists_embeddedTwoLocalAnalyticChart {m : ℕ}
    (M : Matrix (Fin n → Bool) (Fin n → Bool) (MvPolynomial (Fin m) ℂ))
    (embed : (HypercubeTwoLocalParameter n → ℂ) → (Fin m → ℂ))
    (shiftReal : (HypercubeTwoLocalParameter n → ℝ) → ℝ)
    (hembedBase : ∀ p : HypercubeTwoLocalParameter n → ℝ,
      M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (embed fun θ => (p θ : ℂ)))
        = hypercubeTwoLocalMatrix (fun θ => (p θ : ℂ))
          - ((shiftReal p : ℝ) : ℂ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    ∃ (p : HypercubeTwoLocalParameter n → ℝ) (V : Set (Fin m → ℂ))
      (branch : (Fin n → Bool) → (Fin m → ℂ) → ℂ),
      (∀ i : Fin n, p (.transverse i) = 0) ∧
      Function.Injective (hypercubeTwoLocalEnergy p) ∧
      (∀ (i : Fin n) (z : qubitEnvironment n i), 0 < edgeGap i (hypercubeTwoLocalEnergy p) z) ∧
      (∀ i : Fin n, Function.Injective (edgeGap i (hypercubeTwoLocalEnergy p))) ∧
      IsOpen V ∧ IsPreconnected V ∧ V.Nonempty ∧ (embed fun θ => (p θ : ℂ)) ∈ V ∧
      (∀ x, AnalyticOnNhd ℂ (branch x) V) ∧
      (∀ x, branch x (embed fun θ => (p θ : ℂ))
        = ((hypercubeTwoLocalEnergy p x - shiftReal p : ℝ) : ℂ)) ∧
      (∀ z ∈ V, Function.Injective fun x => branch x z) ∧
      (∀ x, ∀ z ∈ V, matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z), branch x z) = 0) := by
  classical
  obtain ⟨p, htr, hinj, hgappos, hgapinj⟩ := exists_twoLocalDiagonalBase_zeroTransverse n
  set z₀ : Fin m → ℂ := embed (fun θ => (p θ : ℂ)) with hz₀def
  set energy : (Fin n → Bool) → ℂ :=
    fun x => ((hypercubeTwoLocalEnergy p x - shiftReal p : ℝ) : ℂ) with hedef
  have henergyInj : Function.Injective energy := by
    intro a b hab
    have hab' : hypercubeTwoLocalEnergy p a - shiftReal p
        = hypercubeTwoLocalEnergy p b - shiftReal p := Complex.ofReal_injective hab
    exact hinj (by linarith [hab'])
  have hone : (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)⁻¹ = 1 :=
    Matrix.inv_eq_right_inv (by simp)
  have hbase : (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)⁻¹ *
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z₀)) * 1
      = Matrix.diagonal energy := by
    rw [hone, one_mul, mul_one, hz₀def, hembedBase p,
      hypercubeTwoLocalMatrix_diagonal_sub_of_zeroTransverse p htr]
  obtain ⟨U, branch, hUopen, hz₀U, hbranchA, hbranch0, hbranchRoot⟩ :=
    exists_simultaneous_eigenvalueBranches (analyticAt_polynomialMatrixFamily M z₀) energy
      henergyInj (S := 1) (by rw [Matrix.det_one]; exact isUnit_one) hbase
  have hroots : ∀ᶠ z in 𝓝 z₀, ∀ x : Fin n → Bool,
      matrixCharpolyRelation (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z), branch x z) = 0 :=
    Filter.eventually_all.2 hbranchRoot
  have hdistinct : ∀ᶠ z in 𝓝 z₀, ∀ x y : Fin n → Bool, x ≠ y → branch x z ≠ branch y z := by
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro y
    by_cases hxy : x = y
    · exact Filter.Eventually.of_forall fun z hz => absurd hxy hz
    · have hne : branch x z₀ - branch y z₀ ≠ 0 := by
        rw [hbranch0 x, hbranch0 y, sub_ne_zero]
        exact fun hcon => hxy (henergyInj hcon)
      have hcont : ContinuousAt (fun z => branch x z - branch y z) z₀ :=
        ((hbranchA x z₀ hz₀U).continuousAt).sub ((hbranchA y z₀ hz₀U).continuousAt)
      filter_upwards [hcont.eventually_ne hne] with z hz _
      exact fun hcon => hz (by rw [hcon, sub_self])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hUopen.mem_nhds hz₀U) (Filter.inter_mem hroots hdistinct))
  refine ⟨p, Metric.ball z₀ ε, branch, htr, hinj, hgappos, hgapinj, Metric.isOpen_ball,
    (convex_ball z₀ ε).isPreconnected, ⟨z₀, Metric.mem_ball_self hε⟩, Metric.mem_ball_self hε,
    fun x => (hbranchA x).mono fun z hz => (hball hz).1, hbranch0, ?_, ?_⟩
  · intro z hz a b hab
    by_contra hne
    exact (hball hz).2.2 a b hne hab
  · intro x z hz
    exact (hball hz).2.1 x

/-- **Real-slice genericity through a two-local embedding.**  Outside a meagre Lebesgue-null set of
real parameters of any polynomial matrix family realizing the two-local coefficients up to a
constant energy offset, the `2^n` energies satisfy no nonzero balanced integer relation.

Every labelling of every such relation is escaped inside one chart around a diagonal base: a nonzero
balanced character is nonconstant, so it differs across some hypercube edge, and switching on that
edge's transverse coupling -- after an arbitrarily small shift of the edge gaps -- moves the
relation off zero. -/
theorem polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_twoLocalEmbedding
    {m : ℕ} (M : Matrix (Fin n → Bool) (Fin n → Bool) (MvPolynomial (Fin m) ℂ))
    (embed : (HypercubeTwoLocalParameter n → ℂ) → (Fin m → ℂ))
    (shiftReal : (HypercubeTwoLocalParameter n → ℝ) → ℝ)
    (hembedCont : Continuous embed)
    (hembedBase : ∀ p : HypercubeTwoLocalParameter n → ℝ,
      M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (embed fun θ => (p θ : ℂ)))
        = hypercubeTwoLocalMatrix (fun θ => (p θ : ℂ))
          - ((shiftReal p : ℝ) : ℂ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (hembedSlice : ∀ (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n) (q : ℝ × ℝ),
      M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (embed (twoLocalEdgeSlice p i q)))
        = hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q)
          - ((shiftReal p : ℝ) : ℂ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    Dense (polynomialMatrixProjectiveGenericSet M) ∧
      polynomialMatrixProjectiveGenericSet M ∈ residual (Fin m → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet M)ᶜ = 0 := by
  classical
  obtain ⟨p, V, branch, htr, hinj, hgappos, hgapinj, hVopen, hVconn, hVne, hz₀V,
    hbranchA, hbranch0, hbranchInj, hbranchRoot⟩ :=
      exists_embeddedTwoLocalAnalyticChart M embed shiftReal hembedBase
  refine polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_analyticBranchEscape
    M V hVopen hVconn hVne branch hbranchA hbranchInj hbranchRoot ?_
  intro k hbalanced hk σ
  set c : (Fin n → Bool) → ℂ := fun x => ((k (σ.symm x) : ℤ) : ℂ) with hcdef
  obtain ⟨x₁, y₁, hxy⟩ : ∃ x y : Fin n → Bool, c x ≠ c y := by
    by_contra hcon
    push Not at hcon
    exact permutedSpectralCoefficient_not_constant hbalanced hk σ hcon
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
        have h0 : edgeState i env false = w := by rw [← hw]; exact hstate
        have h1 : edgeState i env true = boolToggle w i := by
          have h := htoggle
          rw [hw] at h
          exact h
        rw [h0, h1]
        exact fun hcon => hwi hcon.symm
    | true =>
        have h1 : edgeState i env true = w := by rw [← hw]; exact hstate
        have h0 : edgeState i env false = boolToggle w i := by
          have h := htoggle
          rw [hw] at h
          exact h
        rw [h0, h1]
        exact hwi
  set κ : Fin 2 × qubitEnvironment n i → ℝ :=
    fun q => ((k (σ.symm (edgeEquiv i q)) : ℤ) : ℝ) with hκdef
  have hκcast : ∀ q, ((κ q : ℝ) : ℂ) = c (edgeEquiv i q) := by
    intro q
    simp [hκdef, hcdef]
  have hκne : κ (0, env) - κ (1, env) ≠ 0 := by
    rw [sub_ne_zero]
    intro hcon
    refine hstateNe ?_
    have h := congrArg (fun r : ℝ => (r : ℂ)) hcon
    rw [hκcast, hκcast, edgeEquiv_zero, edgeEquiv_one] at h
    exact h
  set slice : ℝ × ℝ → (Fin m → ℂ) := fun q => embed (twoLocalEdgeSlice p i q) with hslicedef
  set E : (Fin n → Bool) → ℝ := hypercubeTwoLocalEnergy p with hEdef
  set s : ℝ := shiftReal p with hsdef
  set mBlk : qubitEnvironment n i → ℝ := fun z => edgeMean i E z - s with hmBlk
  have hsliceParam0 : twoLocalEdgeSlice p i (0, 0) = fun θ => (p θ : ℂ) := by
    funext θ
    simp [twoLocalEdgeSlice]
  have hslice0 : slice (0, 0) = embed fun θ => (p θ : ℂ) := by
    show embed (twoLocalEdgeSlice p i (0, 0)) = _
    rw [hsliceParam0]
  have hsliceCont : Continuous slice := by
    refine hembedCont.comp ?_
    refine continuous_pi fun θ => ?_
    simp only [twoLocalEdgeSlice, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hHslice : ∀ q : ℝ × ℝ, (M.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (slice q))).submatrix (edgeEquiv i) (edgeEquiv i)
      = shiftedBlockSplitMatrix mBlk (edgeGap i E) q := by
    intro q
    have hsub : ((hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q)
          - ((shiftReal p : ℝ) : ℂ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).submatrix
            (edgeEquiv i) (edgeEquiv i))
        = (hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q)).submatrix
              (edgeEquiv i) (edgeEquiv i)
          - ((shiftReal p : ℝ) : ℂ) •
            (1 : Matrix (Fin 2 × qubitEnvironment n i) (Fin 2 × qubitEnvironment n i) ℂ) := by
      ext a b
      simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        (edgeEquiv i).injective.eq_iff]
    rw [hslicedef, hembedSlice p i q, hsub,
      submatrix_hypercubeTwoLocalMatrix_twoLocalEdgeSlice p i htr q, hmBlk, hsdef,
      shiftedBlockSplitMatrix_sub_smul_one]
  have hblockEnergy : ∀ q' : Fin 2 × qubitEnvironment n i,
      blockEnergy mBlk (edgeGap i E) q' = E (edgeEquiv i q') - s := by
    intro q'
    rw [hmBlk, blockEnergy_sub_const, blockEnergy_edge]
  have hblockinj : Function.Injective fun q' : Fin 2 × qubitEnvironment n i =>
      ((blockEnergy mBlk (edgeGap i E) q' : ℝ) : ℂ) := by
    intro a b hab
    have hab' : ((blockEnergy mBlk (edgeGap i E) a : ℝ) : ℂ)
        = ((blockEnergy mBlk (edgeGap i E) b : ℝ) : ℂ) := hab
    rw [hblockEnergy, hblockEnergy] at hab'
    have hreal : E (edgeEquiv i a) - s = E (edgeEquiv i b) - s := Complex.ofReal_injective hab'
    exact (edgeEquiv i).injective (hinj (by linarith [hreal]))
  have hWmem : slice ⁻¹' V ∈ 𝓝 ((0, 0) : ℝ × ℝ) := by
    refine hsliceCont.continuousAt.preimage_mem_nhds ?_
    rw [hslice0]
    exact hVopen.mem_nhds hz₀V
  obtain ⟨q, hqW, hqne⟩ :=
    exists_shifted_split_branch_relation_ne_zero mBlk (edgeGap i E) (hgappos i) (hgapinj i)
      hblockinj (fun q' qq => branch (edgeEquiv i q') (slice qq))
      (fun q' => by
        have h1 : ContinuousAt (branch (edgeEquiv i q')) (slice (0, 0)) := by
          rw [hslice0]
          exact (hbranchA (edgeEquiv i q') _ hz₀V).continuousAt
        exact h1.comp hsliceCont.continuousAt)
      (fun q' => by
        rw [hslice0, hbranch0 (edgeEquiv i q'), hblockEnergy])
      (fun q' => by
        filter_upwards [hWmem] with qq hqq
        rw [← hHslice qq, matrixCharpolyRelation_submatrix_equiv]
        exact hbranchRoot (edgeEquiv i q') (slice qq) hqq)
      κ hκne hWmem
  refine ⟨slice q, hqW, ?_⟩
  rw [← sum_permutedSpectralCoefficient_eq_relation]
  have hreindex : (∑ j, permutedSpectralCoefficient k σ j * branch j (slice q))
      = ∑ q' : Fin 2 × qubitEnvironment n i, (κ q' : ℂ) * branch (edgeEquiv i q') (slice q) :=
    (Fintype.sum_equiv (edgeEquiv i) _ _ fun q' => by
      rw [hκcast]
      rfl).symm
  rw [hreindex]
  exact hqne

/-- Numbering the two-local coefficients embeds them into their own polynomial family. -/
theorem map_eval_embed_twoLocalFin (v : HypercubeTwoLocalParameter n → ℂ) :
    (hypercubeTwoLocalFinPolynomialMatrix n).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        fun t => v ((twoLocalParameterEquivFin n).symm t))
      = hypercubeTwoLocalMatrix v := by
  rw [map_eval_hypercubeTwoLocalFinPolynomialMatrix]
  congr 1
  funext θ
  simp

/-- **Real-slice genericity of the all-qubit two-local family.** -/
theorem twoLocalFinPolynomialMatrix_dense_residual_fullMeasure (n : ℕ) :
    Dense (polynomialMatrixProjectiveGenericSet (hypercubeTwoLocalFinPolynomialMatrix n)) ∧
      polynomialMatrixProjectiveGenericSet (hypercubeTwoLocalFinPolynomialMatrix n) ∈
        residual (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (hypercubeTwoLocalFinPolynomialMatrix n))ᶜ = 0 := by
  refine polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_twoLocalEmbedding
    (hypercubeTwoLocalFinPolynomialMatrix n)
    (fun v t => v ((twoLocalParameterEquivFin n).symm t)) (fun _ => 0)
    (continuous_pi fun _ => continuous_apply _) ?_ ?_
  · intro p
    rw [show (((0 : ℝ) : ℂ)) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 0 by simp, sub_zero]
    exact map_eval_embed_twoLocalFin fun θ => (p θ : ℂ)
  · intro p i q
    rw [show (((0 : ℝ) : ℂ)) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 0 by simp, sub_zero]
    exact map_eval_embed_twoLocalFin (twoLocalEdgeSlice p i q)

/-- At real coefficients the numbered two-local family is Hermitian. -/
theorem isHermitian_twoLocalFinEval
    (p : Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ) :
    ((hypercubeTwoLocalFinPolynomialMatrix n).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun t => (p t : ℂ))).IsHermitian := by
  rw [map_eval_hypercubeTwoLocalFinPolynomialMatrix]
  exact isHermitian_hypercubeTwoLocalMatrix fun θ => p (twoLocalParameterEquivFin n θ)

/-- **The spectral conclusion at a generic real coefficient vector.**  Every balanced integer
relation among the `2^n` energies is trivial. -/
theorem maximallyProjectiveEnergy_twoLocalFinEval
    (p : Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet (hypercubeTwoLocalFinPolynomialMatrix n)) :
    MaximallyProjectiveEnergy (isHermitian_twoLocalFinEval p).eigenvalues :=
  maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet _ p hp _

/-- **Two-local spectral genericity, finite size and unconditional.**  Outside a meagre
Lebesgue-null set of real two-local coefficients the `2^n` energies are pairwise distinct and admit
no balanced integer relation other than the trivial one. -/
theorem twoLocal_simple_and_projectivelyIndependent_generically (n : ℕ) :
    Dense (polynomialMatrixProjectiveGenericSet (hypercubeTwoLocalFinPolynomialMatrix n)) ∧
      polynomialMatrixProjectiveGenericSet (hypercubeTwoLocalFinPolynomialMatrix n) ∈
        residual (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (hypercubeTwoLocalFinPolynomialMatrix n))ᶜ = 0 ∧
      ∀ p ∈ polynomialMatrixProjectiveGenericSet (hypercubeTwoLocalFinPolynomialMatrix n),
        Function.Injective (isHermitian_twoLocalFinEval p).eigenvalues ∧
        MaximallyProjectiveEnergy (isHermitian_twoLocalFinEval p).eigenvalues := by
  obtain ⟨hdense, hresidual, hvolume⟩ := twoLocalFinPolynomialMatrix_dense_residual_fullMeasure n
  refine ⟨hdense, hresidual, hvolume, fun p hp => ⟨?_, ?_⟩⟩
  · exact MaximallyProjectiveEnergy.injective (maximallyProjectiveEnergy_twoLocalFinEval p hp)
  · exact maximallyProjectiveEnergy_twoLocalFinEval p hp


/-- **Almost sure spectral genericity for any absolutely continuous law.**  A probability law on the
real two-local coefficients with a density gives probability one to the coefficients whose `2^n`
energies are pairwise distinct and admit no balanced integer relation. -/
theorem twoLocal_projectivelyIndependent_ae
    {μ : Measure (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ)}
    (hμ : μ ≪ volume) :
    ∀ᵐ p ∂μ, Function.Injective (isHermitian_twoLocalFinEval p).eigenvalues ∧
      MaximallyProjectiveEnergy (isHermitian_twoLocalFinEval p).eigenvalues := by
  obtain ⟨-, -, hvolume, hgeneric⟩ := twoLocal_simple_and_projectivelyIndependent_generically n
  refine MeasureTheory.measure_mono_null (fun q hq => ?_) (hμ hvolume)
  by_contra hcon
  exact hq (hgeneric q (by simpa using hcon))

end GaloisForLFunctions.HTGeometry
