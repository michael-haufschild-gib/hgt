import GaloisForLFunctions.HTGeometry.ClockProbeOrthogonalSeparable

/-!
# Fully separable potentials

Two orthogonal factors extend to a whole orthogonal frame. On a diagonal chart the coordinate
covectors are pairwise orthogonal, so the product over **all** coordinates,

`u(x) = ∏ᵢ wᵢ(xᵢ)`,

solves `□u + Vu = 0` for the fully separable potential `V(x) = ∑ᵢ Vᵢ(xᵢ)` as soon as each factor
solves its own one-dimensional equation `(εᵢ)⁻¹wᵢ'' + Vᵢwᵢ = 0`. Picard–Lindelöf supplies the
factors for arbitrary `C¹` profiles, so every fully separable potential is determined.

The induction runs over subsets of the coordinates. What makes it cheap is that the partial product
over a set `s` is literally invariant under translation in any direction outside `s`, and invariance
forces the corresponding partial derivative to vanish with no differentiability hypothesis at all.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## Invariance kills a partial derivative -/

/-- **A field invariant under translation in a direction has no derivative there**, with no
differentiability hypothesis. -/
theorem coordPartial_eq_zero_of_invariant {u : (Fin (d + 1) → ℝ) → ℝ} {k : Fin (d + 1)}
    (hinv : ∀ (y : Fin (d + 1) → ℝ) (t : ℝ),
      u (y + t • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ)) = u y)
    (x : Fin (d + 1) → ℝ) : coordPartial k u x = 0 := by
  by_cases hd : DifferentiableAt ℝ u x
  · have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ))
        (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ))
          ((1 : ℝ) • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ)) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const _
      simpa using h1.const_add x
    have hbase : (fun t : ℝ => x + t • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ)) 0 = x := by
      simp
    have hL : HasFDerivAt u (fderiv ℝ u x)
        ((fun t : ℝ => x + t • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ)) 0) := by
      rw [hbase]
      exact hd.hasFDerivAt
    have hcomp := hL.comp_hasDerivAt 0 hline
    have hconst : (u ∘ fun t : ℝ => x + t • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ))
        = fun _ : ℝ => u x := by
      funext t
      exact hinv x t
    rw [hconst] at hcomp
    have hval := hcomp.unique (hasDerivAt_const (0 : ℝ) (u x))
    rw [coordPartial, hval]
  · rw [coordPartial, fderiv_zero_of_not_differentiableAt hd]
    rfl

/-! ## Coordinate factors and their partial products -/

/-- The `j`-th coordinate factor of a separable probe. -/
noncomputable def coordFactor (w : Fin (d + 1) → ℝ → ℝ) (j : Fin (d + 1)) :
    (Fin (d + 1) → ℝ) → ℝ := covectorLift (Pi.single j (1 : ℝ)) (w j)

theorem coordFactor_apply (w : Fin (d + 1) → ℝ → ℝ) (j : Fin (d + 1))
    (y : Fin (d + 1) → ℝ) : coordFactor w j y = w j (y j) := by
  rw [coordFactor, covectorLift, covectorPhase_basis]

/-- The partial product of coordinate factors over a set of directions. -/
noncomputable def boxProduct (w : Fin (d + 1) → ℝ → ℝ) (s : Finset (Fin (d + 1))) :
    (Fin (d + 1) → ℝ) → ℝ := fun y => ∏ i ∈ s, coordFactor w i y

theorem boxProduct_apply (w : Fin (d + 1) → ℝ → ℝ) (s : Finset (Fin (d + 1)))
    (y : Fin (d + 1) → ℝ) : boxProduct w s y = ∏ i ∈ s, w i (y i) := by
  rw [boxProduct]
  exact Finset.prod_congr rfl fun i _ => coordFactor_apply w i y

theorem boxProduct_empty (w : Fin (d + 1) → ℝ → ℝ) :
    boxProduct w (∅ : Finset (Fin (d + 1))) = fun _ => 1 := by
  funext y
  rw [boxProduct_apply]
  simp

theorem boxProduct_insert (w : Fin (d + 1) → ℝ → ℝ) {j : Fin (d + 1)}
    {s : Finset (Fin (d + 1))} (hj : j ∉ s) :
    boxProduct w (insert j s) = fun y => coordFactor w j y * boxProduct w s y := by
  funext y
  rw [boxProduct, boxProduct, Finset.prod_insert hj]

/-- **The partial product is invariant transversally to its own directions.** -/
theorem coordPartial_boxProduct_of_notMem (w : Fin (d + 1) → ℝ → ℝ)
    {s : Finset (Fin (d + 1))} {k : Fin (d + 1)} (hk : k ∉ s) (x : Fin (d + 1) → ℝ) :
    coordPartial k (boxProduct w s) x = 0 := by
  refine coordPartial_eq_zero_of_invariant ?_ x
  intro y t
  rw [boxProduct_apply, boxProduct_apply]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hik : i ≠ k := fun h => hk (h ▸ hi)
  congr 1
  simp [hik]

theorem coordPartial_coordFactor_of_ne (w : Fin (d + 1) → ℝ → ℝ) {j k : Fin (d + 1)}
    (hkj : k ≠ j) (x : Fin (d + 1) → ℝ) : coordPartial k (coordFactor w j) x = 0 := by
  refine coordPartial_covectorLift_of_zero _ _ ?_ x
  rw [Pi.single_apply, if_neg hkj]

/-! ## The induction -/

/-- **Fully separable probes.** The product of one-dimensional solutions solves the equation with
the sum potential, on the box where each factor is defined. -/
theorem boxProduct_solves (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (w dw ddw V : Fin (d + 1) → ℝ → ℝ) (I : Fin (d + 1) → Set ℝ) (hI : ∀ i, IsOpen (I i))
    (hd1 : ∀ i, ∀ t ∈ I i, HasDerivAt (w i) (dw i t) t)
    (hd2 : ∀ i, ∀ t ∈ I i, HasDerivAt (dw i) (ddw i t) t)
    (heq : ∀ i t, (eps i)⁻¹ * ddw i t + V i t * w i t = 0)
    {x : Fin (d + 1) → ℝ} (hx : ∀ i, x i ∈ I i) (s : Finset (Fin (d + 1))) :
    (∀ y : Fin (d + 1) → ℝ, (∀ i, y i ∈ I i) → DifferentiableAt ℝ (boxProduct w s) y) ∧
      (∀ k, DifferentiableAt ℝ (coordPartial k (boxProduct w s)) x) ∧
      SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (fun y => ∑ i ∈ s, V i (y i)) (boxProduct w s) x := by
  classical
  set U : Set (Fin (d + 1) → ℝ) := {y | ∀ i, y i ∈ I i} with hUdef
  have hUopen : IsOpen U := by
    have : U = ⋂ i, (fun y : Fin (d + 1) → ℝ => y i) ⁻¹' I i := by
      ext y
      simp [hUdef]
    rw [this]
    exact isOpen_iInter_of_finite fun i => (hI i).preimage (continuous_apply i)
  have hxU : x ∈ U := hx
  have hphase : ∀ j : Fin (d + 1), ContDiff ℝ ∞
      (covectorPhase (d := d) (Pi.single j (1 : ℝ))) := fun j => contDiff_covectorPhase _
  have hbasis : ∀ (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ),
      covectorPhase (Pi.single j (1 : ℝ)) y = y j := fun j y => covectorPhase_basis j y
  -- data about a single coordinate factor
  have hfdiff : ∀ (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ), (∀ i, y i ∈ I i) →
      DifferentiableAt ℝ (coordFactor w j) y := by
    intro j y hy
    have hd : HasDerivAt (w j) (dw j (covectorPhase (Pi.single j (1 : ℝ)) y))
        (covectorPhase (Pi.single j (1 : ℝ)) y) := by
      rw [hbasis j y]
      exact hd1 j (y j) (hy j)
    exact (hd.comp_hasFDerivAt y
      (differentiableAt_of_contDiff_infty (hphase j) y).hasFDerivAt).differentiableAt
  have hfev : ∀ j : Fin (d + 1), coordPartial j (coordFactor w j) =ᶠ[nhds x]
      fun y => (1 : ℝ) * covectorLift (Pi.single j (1 : ℝ)) (dw j) y := by
    intro j
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) ?_
    intro y hy
    have hd : HasDerivAt (w j) (dw j (covectorPhase (Pi.single j (1 : ℝ)) y))
        (covectorPhase (Pi.single j (1 : ℝ)) y) := by
      rw [hbasis j y]
      exact hd1 j (y j) (hy j)
    have := coordPartial_covectorLift hd j
    rw [Pi.single_eq_same] at this
    exact this
  have hdwlift : ∀ j : Fin (d + 1),
      DifferentiableAt ℝ (covectorLift (d := d) (Pi.single j (1 : ℝ)) (dw j)) x := by
    intro j
    have hd : HasDerivAt (dw j) (ddw j (covectorPhase (Pi.single j (1 : ℝ)) x))
        (covectorPhase (Pi.single j (1 : ℝ)) x) := by
      rw [hbasis j x]
      exact hd2 j (x j) (hx j)
    exact (hd.comp_hasFDerivAt x
      (differentiableAt_of_contDiff_infty (hphase j) x).hasFDerivAt).differentiableAt
  have hfpartial : ∀ j k : Fin (d + 1),
      DifferentiableAt ℝ (coordPartial k (coordFactor w j)) x := by
    intro j k
    by_cases hkj : k = j
    · subst hkj
      rw [(hfev k).differentiableAt_iff]
      exact (hdwlift k).const_mul 1
    · have hfun : coordPartial k (coordFactor w j) = fun _ => (0 : ℝ) :=
        funext fun y => coordPartial_coordFactor_of_ne w hkj y
      rw [hfun]
      exact differentiableAt_const 0
  have hfdal : ∀ j : Fin (d + 1),
      (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (coordFactor w j) x
        = (eps j)⁻¹ * ddw j (x j) := by
    intro j
    have hS : covectorPhase (Pi.single j (1 : ℝ)) x ∈ I j := by
      rw [hbasis j x]
      exact hx j
    have h := dalembert_covectorLift_flat eps heps (hI j)
      (fun t ht => hd1 j t ht) (fun t ht => hd2 j t ht) hS
    rw [coordFactor, h, covectorNormConst_single, hbasis j x]
    ring
  have hfsolve : ∀ j : Fin (d + 1),
      SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (fun y => V j (y j)) (coordFactor w j) x := by
    intro j
    show (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (coordFactor w j) x
      + V j (x j) * coordFactor w j x = 0
    rw [hfdal j, coordFactor_apply]
    exact heq j (x j)
  -- the induction
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_, ?_⟩
    · intro y _
      rw [boxProduct_empty]
      exact differentiableAt_const 1
    · intro k
      have hfun : coordPartial k (boxProduct w (∅ : Finset (Fin (d + 1))))
          = fun _ => (0 : ℝ) := by
        funext y
        rw [boxProduct_empty]
        exact coordPartial_const k 1 y
      rw [hfun]
      exact differentiableAt_const 0
    · have hfun : ∀ k, coordPartial k (boxProduct w (∅ : Finset (Fin (d + 1))))
          = fun _ => (0 : ℝ) := by
        intro k
        funext y
        rw [boxProduct_empty]
        exact coordPartial_const k 1 y
      have hdiff : ∀ k, DifferentiableAt ℝ
          (coordPartial k (boxProduct w (∅ : Finset (Fin (d + 1))))) x := by
        intro k
        rw [hfun k]
        exact differentiableAt_const 0
      show (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (boxProduct w (∅ : Finset (Fin (d + 1)))) x
        + (∑ i ∈ (∅ : Finset (Fin (d + 1))), V i (x i))
          * boxProduct w (∅ : Finset (Fin (d + 1))) x = 0
      rw [ofSignature_dalembert_of_differentiableAt eps heps hdiff]
      have hzero : ∀ k : Fin (d + 1),
          (eps k)⁻¹ * coordPartial k
            (coordPartial k (boxProduct w (∅ : Finset (Fin (d + 1))))) x = 0 := by
        intro k
        rw [hfun k, coordPartial_const k 0 x, mul_zero]
      rw [Finset.sum_congr rfl fun k _ => hzero k]
      simp
  | insert j s hj ih =>
    obtain ⟨ihdiff, ihpartial, ihsolve⟩ := ih
    have hprodfun := boxProduct_insert w hj
    have hgU : ∀ y : Fin (d + 1) → ℝ, (∀ i, y i ∈ I i) →
        DifferentiableAt ℝ (boxProduct w s) y := ihdiff
    have hdiffins : ∀ y : Fin (d + 1) → ℝ, (∀ i, y i ∈ I i) →
        DifferentiableAt ℝ (boxProduct w (insert j s)) y := by
      intro y hy
      rw [hprodfun]
      exact (hfdiff j y hy).mul (hgU y hy)
    have hev : ∀ k : Fin (d + 1), coordPartial k (boxProduct w (insert j s)) =ᶠ[nhds x]
        fun y => coordFactor w j y * coordPartial k (boxProduct w s) y
          + boxProduct w s y * coordPartial k (coordFactor w j) y := by
      intro k
      refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) ?_
      intro y hy
      rw [hprodfun]
      exact coordPartial_mul (hfdiff j y hy) (hgU y hy) k
    have hpartialins : ∀ k, DifferentiableAt ℝ
        (coordPartial k (boxProduct w (insert j s))) x := by
      intro k
      rw [(hev k).differentiableAt_iff]
      exact ((hfdiff j x hx).mul (ihpartial k)).add ((hgU x hx).mul (hfpartial j k))
    refine ⟨hdiffins, hpartialins, ?_⟩
    have hgp : (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair
        (coordFactor w j) (boxProduct w s) x = 0 := by
      rw [ofSignature_gradPair]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hkj : k = j
      · rw [hkj, coordPartial_boxProduct_of_notMem w hj x]
        ring
      · rw [coordPartial_coordFactor_of_ne w hkj x]
        ring
    have hmul := dalembert_mul_of_differentiableAt eps heps hUopen hxU
      (fun y hy => hfdiff j y hy) (fun y hy => hgU y hy)
      (fun k => hfpartial j k) ihpartial
    have hf := hfsolve j
    have hg := ihsolve
    show (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (boxProduct w (insert j s)) x
      + (∑ i ∈ insert j s, V i (x i)) * boxProduct w (insert j s) x = 0
    rw [hprodfun, hmul, hgp, Finset.sum_insert hj]
    have hfx : (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (coordFactor w j) x
        + V j (x j) * coordFactor w j x = 0 := hf
    have hgx : (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (boxProduct w s) x
        + (∑ i ∈ s, V i (x i)) * boxProduct w s x = 0 := hg
    linear_combination (coordFactor w j x) * hgx + (boxProduct w s x) * hfx

/-! ## Probes and determination for a fully separable potential -/

/-- **Local probes for a fully separable potential.** -/
theorem exists_fullySeparable_localProbe (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {V : Fin (d + 1) → ℝ → ℝ} (hV : ∀ i, ContDiff ℝ 1 (V i)) (b : Fin (d + 1) → ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (r : Fin (d + 1) → ℝ), (∀ i, 0 < r i) ∧
      (∀ x : Fin (d + 1) → ℝ, (∀ i, x i = b i) → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ, (∀ i, x i ∈ Ioo (b i - r i) (b i + r i)) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (fun y => ∑ i, V i (y i)) u x) := by
  classical
  choose w dw ddw r hr hwb hd1 hd2 hqeq using fun i : Fin (d + 1) =>
    exists_localLinearProbe (p := fun _ => (0 : ℝ)) contDiff_const
      (contDiff_const.mul (hV i) : ContDiff ℝ 1 fun t => eps i * V i t) (b i)
  have heq : ∀ (i : Fin (d + 1)) (t : ℝ), (eps i)⁻¹ * ddw i t + V i t * w i t = 0 := by
    intro i t
    have hne : eps i ≠ 0 := heps i
    have h := hqeq i t
    simp only [zero_mul, add_zero] at h
    have hd : ddw i t = -(eps i * V i t * w i t) := by linarith [h]
    rw [hd, mul_neg, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    ring
  refine ⟨boxProduct w Finset.univ, r, hr, ?_, ?_⟩
  · intro x hxb
    rw [boxProduct_apply]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hxb i]
    exact hwb i
  · intro x hxr
    exact (boxProduct_solves eps heps w dw ddw V (fun i => Ioo (b i - r i) (b i + r i))
      (fun _ => isOpen_Ioo) hd1 hd2 heq hxr Finset.univ).2.2

/-- **A fully separable potential is determined by clock data.** -/
theorem fullySeparable_potential_determined (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {V : Fin (d + 1) → ℝ → ℝ} (hV : ∀ i, ContDiff ℝ 1 (V i))
    {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b : Fin (d + 1) → ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (r : Fin (d + 1) → ℝ),
      (∀ i, 0 < r i) →
      (∀ x : Fin (d + 1) → ℝ, (∀ i, x i ∈ Ioo (b i - r i) (b i + r i)) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (fun y => ∑ i, V i (y i)) u x) →
      (∀ x : Fin (d + 1) → ℝ, (∀ i, x i ∈ Ioo (b i - r i) (b i + r i)) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other u x)) :
    other = fun y => ∑ i, V i (y i) := by
  funext x
  obtain ⟨u, r, hr, hu1, hsolve⟩ := exists_fullySeparable_localProbe eps heps hV x
  have hxr : ∀ i, x i ∈ Ioo (x i - r i) (x i + r i) := by
    intro i
    have := hr i
    constructor <;> linarith
  refine potential_eq_of_solvesPotentialWaveAt
    (hother x u r hr hsolve x hxr) (hsolve x hxr) ?_
  rw [hu1 x fun _ => rfl]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
