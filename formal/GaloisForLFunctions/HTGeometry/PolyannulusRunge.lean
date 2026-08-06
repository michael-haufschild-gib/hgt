import GaloisForLFunctions.HTGeometry.CircleIntegralParam
import GaloisForLFunctions.HTGeometry.LaurentAnnulus

/-!
# The Laurent coefficients of a slice, as functions of the remaining variables

Splitting off the first coordinate of a function holomorphic on a polyannulus, its Laurent
coefficients in that coordinate are circle integrals of the remaining variables, hence holomorphic
on the tail polyannulus.  This is the inductive step of the several-variable Runge theorem: the
Laurent partial sum in the first coordinate has holomorphic coefficients, to which the induction
hypothesis applies.

* `HTGeometry.sliceOuterCoeff`, `HTGeometry.sliceInnerCoeff` : the two families of coefficients.
* `HTGeometry.differentiableOn_sliceOuterCoeff`,
  `HTGeometry.differentiableOn_sliceInnerCoeff` : they are holomorphic on the tail.
-/

namespace HTGeometry

open Complex GaloisForLFunctions.HTGeometry

section SliceCoeff

variable {n : ℕ}

/-- The outer Laurent coefficients of the first-coordinate slice. -/
noncomputable def sliceOuterCoeff (f : (Fin (n + 1) → ℂ) → ℂ) (R : ℝ) (k : ℕ)
    (y : Fin n → ℂ) : ℂ :=
  outerCoeff (fun ζ => f (Fin.cons ζ y)) R k

/-- The inner Laurent coefficients of the first-coordinate slice. -/
noncomputable def sliceInnerCoeff (f : (Fin (n + 1) → ℂ) → ℂ) (r : ℝ) (k : ℕ)
    (y : Fin n → ℂ) : ℂ :=
  annulusLaurentCoeff (fun ζ => f (Fin.cons ζ y)) 0 r k

/-- The circle avoids the origin, so the negative powers are continuous along it. -/
theorem continuous_circle_zpow {t : ℝ} (ht : 0 < t) (m : ℤ) :
    Continuous fun θ : ℝ => (circleMap 0 t θ) ^ m := by
  refine Continuous.zpow₀ (continuous_circleMap 0 t) m fun θ => Or.inl ?_
  intro hcon
  have h := norm_circleMap_zero t θ
  rw [hcon, norm_zero, abs_of_pos ht] at h
  exact absurd h.symm (ne_of_gt ht)

/-- **The outer coefficients of a slice are holomorphic in the remaining variables.** -/
theorem differentiableOn_sliceOuterCoeff {f : (Fin (n + 1) → ℂ) → ℂ} {D : Fin (n + 1) → Set ℂ}
    (hopen : ∀ i, IsOpen (D i)) (hf : DifferentiableOn ℂ f (productDomain D))
    {R : ℝ} (hR : 0 < R) (hcirc : ∀ θ : ℝ, circleMap 0 R θ ∈ D 0) (k : ℕ) :
    DifferentiableOn ℂ (sliceOuterCoeff f R k) (productDomain fun i => D i.succ) := by
  intro y hy
  refine DifferentiableAt.differentiableWithinAt ?_
  have hg : Continuous fun θ : ℝ => ((circleMap 0 R θ) ^ (k + 1))⁻¹ := by
    have h := continuous_circle_zpow hR (-((k : ℤ) + 1))
    refine h.congr fun θ => ?_
    rw [zpow_neg, ← zpow_natCast (circleMap 0 R θ) (k + 1)]
    norm_num
  have hbase := differentiableAt_circleIntegral_slice hopen hf hR hcirc
    (fun ζ => (ζ ^ (k + 1))⁻¹) hg hy
  exact hbase.const_smul ((2 * Real.pi * Complex.I : ℂ))⁻¹

/-- **The inner coefficients of a slice are holomorphic in the remaining variables.** -/
theorem differentiableOn_sliceInnerCoeff {f : (Fin (n + 1) → ℂ) → ℂ} {D : Fin (n + 1) → Set ℂ}
    (hopen : ∀ i, IsOpen (D i)) (hf : DifferentiableOn ℂ f (productDomain D))
    {r : ℝ} (hr : 0 < r) (hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ D 0) (k : ℕ) :
    DifferentiableOn ℂ (sliceInnerCoeff f r k) (productDomain fun i => D i.succ) := by
  intro y hy
  refine DifferentiableAt.differentiableWithinAt ?_
  have hg : Continuous fun θ : ℝ => ((circleMap 0 r θ) - 0) ^ k := by
    simp only [sub_zero]
    exact continuous_pow k |>.comp (continuous_circleMap 0 r)
  have hbase := differentiableAt_circleIntegral_slice hopen hf hr hcirc
    (fun ζ => (ζ - 0) ^ k) hg hy
  exact hbase.const_smul ((2 * Real.pi * Complex.I : ℂ))⁻¹

end SliceCoeff

section ClosedPolyannulus

variable {n : ℕ}

/-- The closed polyannulus between two radius vectors. -/
def closedPolyannulus (ρ σ : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z : Fin n → ℂ | ∀ i, ρ i ≤ ‖z i‖ ∧ ‖z i‖ ≤ σ i}

theorem isCompact_closedPolyannulus (ρ σ : Fin n → ℝ) : IsCompact (closedPolyannulus ρ σ) := by
  have hclosed : IsClosed (closedPolyannulus ρ σ) := by
    have heq : closedPolyannulus ρ σ =
        ⋂ i : Fin n, ((fun z : Fin n → ℂ => ‖z i‖) ⁻¹' (Set.Icc (ρ i) (σ i))) := by
      ext z
      simp [closedPolyannulus, Set.mem_iInter, Set.mem_Icc]
    rw [heq]
    exact isClosed_iInter fun i =>
      isClosed_Icc.preimage ((continuous_apply i).norm)
  have hbdd : Bornology.IsBounded (closedPolyannulus ρ σ) := by
    rcases Set.eq_empty_or_nonempty (closedPolyannulus ρ σ) with hemp | ⟨z₀, hz₀⟩
    · rw [hemp]; exact Bornology.isBounded_empty
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1 + ∑ i, |σ i|, fun z hz => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have h1 : ‖z i‖ ≤ σ i := (hz i).2
      have h2 : σ i ≤ |σ i| := le_abs_self _
      have h3 : |σ i| ≤ ∑ i', |σ i'| :=
        Finset.single_le_sum (f := fun i' => |σ i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- The closed annulus in the plane. -/
def closedAnnulus (r R : ℝ) : Set ℂ := {ζ : ℂ | r ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ R}

theorem isCompact_closedAnnulus (r R : ℝ) : IsCompact (closedAnnulus r R) := by
  have h := isCompact_closedPolyannulus (n := 1) (fun _ => r) (fun _ => R)
  have heq : closedAnnulus r R =
      (fun ζ : ℂ => (fun _ : Fin 1 => ζ)) ⁻¹' closedPolyannulus (fun _ => r) (fun _ => R) := by
    ext ζ
    simp [closedAnnulus, closedPolyannulus]
  have hclosed : IsClosed (closedAnnulus r R) := by
    have heq2 : closedAnnulus r R = (fun ζ : ℂ => ‖ζ‖) ⁻¹' (Set.Icc r R) := by
      ext ζ
      simp [closedAnnulus, Set.mem_Icc]
    rw [heq2]
    exact isClosed_Icc.preimage continuous_norm
  have hbdd : Bornology.IsBounded (closedAnnulus r R) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨|R|, fun ζ hζ => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans hζ.2 (le_abs_self R)
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

theorem closedAnnulus_subset_annulus {a b r R : ℝ} (har : a < r) (hRb : R < b) :
    closedAnnulus r R ⊆ annulus a b :=
  fun _ hζ => ⟨lt_of_lt_of_le har hζ.1, lt_of_le_of_lt hζ.2 hRb⟩

theorem closedPolyannulus_subset {a b ρ σ : Fin n → ℝ} (haρ : ∀ i, a i < ρ i)
    (hσb : ∀ i, σ i < b i) :
    closedPolyannulus ρ σ ⊆ productDomain fun i => annulus (a i) (b i) :=
  fun _ hz i => ⟨lt_of_lt_of_le (haρ i) (hz i).1, lt_of_le_of_lt (hz i).2 (hσb i)⟩

/-- The `cons` of a closed annulus and a closed polyannulus lands in the polyannulus. -/
theorem cons_mem_annulusProduct {a b : Fin (n + 1) → ℝ} {r R : ℝ}
    (har : a 0 < r) (hRb : R < b 0) {ρ σ : Fin n → ℝ}
    (haρ : ∀ i, a i.succ < ρ i) (hσb : ∀ i, σ i < b i.succ)
    {ζ : ℂ} (hζ : ζ ∈ closedAnnulus r R) {y : Fin n → ℂ} (hy : y ∈ closedPolyannulus ρ σ) :
    (Fin.cons ζ y : Fin (n + 1) → ℂ) ∈ productDomain fun i => annulus (a i) (b i) := by
  intro i
  induction i using Fin.cases with
  | zero =>
      simpa using ⟨lt_of_lt_of_le har hζ.1, lt_of_le_of_lt hζ.2 hRb⟩
  | succ j =>
      simpa using ⟨lt_of_lt_of_le (haρ j) (hy j).1, lt_of_le_of_lt (hy j).2 (hσb j)⟩

end ClosedPolyannulus

section SliceSum

variable {n : ℕ}

/-- The Laurent partial sum of a slice, written through the slice coefficients. -/
theorem laurentApprox_slice (f : (Fin (n + 1) → ℂ) → ℂ) (r R : ℝ) (N : ℕ) (ζ : ℂ)
    (y : Fin n → ℂ) :
    laurentApprox (fun w => f (Fin.cons w y)) r R N ζ
      = (∑ k ∈ Finset.range N, (ζ ^ k) * sliceOuterCoeff f R k y)
        + ∑ k ∈ Finset.range N, ((ζ ^ (k + 1))⁻¹) * sliceInnerCoeff f r k y := by
  rw [laurentApprox, laurentInnerPartial]
  simp only [sliceOuterCoeff, sliceInnerCoeff, smul_eq_mul, sub_zero]

end SliceSum

section RungeInduction

/-- **The Runge theorem on a polyannulus.**  A function holomorphic on a polyannulus is
approximated uniformly on every closed sub-polyannulus, to any accuracy, by a function holomorphic
on the product of punctured planes.  The induction splits off one coordinate: the Laurent partial
sum in that coordinate has an explicit error depending only on the maximum of the function, and its
coefficients are circle integrals, holomorphic in the remaining variables, to which the induction
hypothesis applies. -/
theorem exists_punctured_approx_polyannulus : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (a b ρ σ : Fin n → ℝ) (ε : ℝ),
    (∀ i, 0 < a i) → (∀ i, a i < ρ i) → (∀ i, ρ i ≤ σ i) → (∀ i, σ i < b i) → 0 < ε →
    DifferentiableOn ℂ f (productDomain fun i => annulus (a i) (b i)) →
    ∃ P : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ P (productDomain fun _ : Fin n => {z : ℂ | z ≠ 0}) ∧
      ∀ z ∈ closedPolyannulus ρ σ, ‖f z - P z‖ ≤ ε := by
  intro n
  induction n with
  | zero =>
      intro f _ _ _ _ ε _ _ _ _ hε _
      refine ⟨f, ?_, fun z _ => ?_⟩
      · intro z _
        refine DifferentiableAt.differentiableWithinAt ?_
        have hconst : f = fun _ => f z := by
          funext w
          congr 1
          funext i
          exact i.elim0
        rw [hconst]
        exact differentiableAt_const _
      · simp [hε.le]
  | succ n ih =>
      intro f a b ρ σ ε ha haρ hρσ hσb hε hf
      classical
      set r₀ : ℝ := (a 0 + ρ 0) / 2 with hr₀def
      set R₀ : ℝ := (σ 0 + b 0) / 2 with hR₀def
      have har₀ : a 0 < r₀ := by rw [hr₀def]; linarith [haρ 0]
      have hr₀ρ : r₀ < ρ 0 := by rw [hr₀def]; linarith [haρ 0]
      have hσR₀ : σ 0 < R₀ := by rw [hR₀def]; linarith [hσb 0]
      have hR₀b : R₀ < b 0 := by rw [hR₀def]; linarith [hσb 0]
      have hr₀pos : 0 < r₀ := lt_trans (ha 0) har₀
      have hρ0pos : 0 < ρ 0 := lt_trans hr₀pos hr₀ρ
      have hσ0pos : 0 < σ 0 := lt_of_lt_of_le hρ0pos (hρσ 0)
      have hR₀pos : 0 < R₀ := lt_trans hσ0pos hσR₀
      have hcircmem : ∀ (t : ℝ), 0 < t → a 0 < t → t < b 0 →
          ∀ θ : ℝ, circleMap 0 t θ ∈ annulus (a 0) (b 0) := by
        intro t htpos hat htb θ
        have hn : ‖circleMap 0 t θ‖ = t := by
          rw [norm_circleMap_zero, abs_of_pos htpos]
        exact ⟨by rw [hn]; exact hat, by rw [hn]; exact htb⟩
      have hcircr := hcircmem r₀ hr₀pos har₀ (by linarith [hρσ 0, hσb 0])
      have hcircR := hcircmem R₀ hR₀pos (by linarith [haρ 0, hρσ 0]) hR₀b
      -- the compact set on which the slice bound is taken
      set Ktail : Set (Fin n → ℂ) :=
        closedPolyannulus (fun i => ρ i.succ) (fun i => σ i.succ) with hKtail
      set S : Set (Fin (n + 1) → ℂ) :=
        (fun p : ℂ × (Fin n → ℂ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ)) ''
          (closedAnnulus r₀ R₀ ×ˢ Ktail) with hS
      have hconsCont : Continuous fun p : ℂ × (Fin n → ℂ) =>
          (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ) := by
        refine continuous_pi fun i => ?_
        induction i using Fin.cases with
        | zero =>
            simp only [Fin.cons_zero]
            exact continuous_fst
        | succ j =>
            simp only [Fin.cons_succ]
            exact (continuous_apply j).comp continuous_snd
      have hScomp : IsCompact S :=
        ((isCompact_closedAnnulus r₀ R₀).prod
          (isCompact_closedPolyannulus _ _)).image hconsCont
      have hSsub : S ⊆ productDomain fun i => annulus (a i) (b i) := by
        rintro x ⟨⟨ζ, y⟩, ⟨hζ, hy⟩, rfl⟩
        exact cons_mem_annulusProduct har₀ hR₀b (fun i => haρ i.succ) (fun i => hσb i.succ) hζ hy
      obtain ⟨M₀, hM₀⟩ := hScomp.exists_bound_of_continuousOn (hf.continuousOn.mono hSsub)
      set M : ℝ := max M₀ 0 with hMdef
      have hMnn : 0 ≤ M := le_max_right _ _
      have hM : ∀ x ∈ S, ‖f x‖ ≤ M := fun x hx => le_trans (hM₀ x hx) (le_max_left _ _)
      -- choose the number of Laurent terms
      set qR : ℝ := σ 0 / R₀ with hqRdef
      set qr : ℝ := r₀ / ρ 0 with hqrdef
      have hqRnn : 0 ≤ qR := by rw [hqRdef]; positivity
      have hqrnn : 0 ≤ qr := by rw [hqrdef]; positivity
      have hqR1 : qR < 1 := by rw [hqRdef]; exact (div_lt_one hR₀pos).2 hσR₀
      have hqr1 : qr < 1 := by rw [hqrdef]; exact (div_lt_one hρ0pos).2 hr₀ρ
      have htend : Filter.Tendsto
          (fun N : ℕ => M * (qR ^ N / (1 - qR)) + M * r₀ / ρ 0 * (qr ^ N / (1 - qr)))
          Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun N : ℕ => M * (qR ^ N / (1 - qR))) Filter.atTop (nhds 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one hqRnn hqR1).div_const (1 - qR)
          simpa using this.const_mul M
        have h2 : Filter.Tendsto (fun N : ℕ => M * r₀ / ρ 0 * (qr ^ N / (1 - qr)))
            Filter.atTop (nhds 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one hqrnn hqr1).div_const (1 - qr)
          simpa using this.const_mul (M * r₀ / ρ 0)
        simpa using h1.add h2
      obtain ⟨N, hN⟩ : ∃ N : ℕ,
          M * (qR ^ N / (1 - qR)) + M * r₀ / ρ 0 * (qr ^ N / (1 - qr)) ≤ ε / 2 := by
        obtain ⟨N, hNall⟩ := (Metric.tendsto_atTop.1 htend) (ε / 2) (by linarith)
        refine ⟨N, ?_⟩
        have h := hNall N le_rfl
        rw [Real.dist_eq, sub_zero] at h
        exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
      -- the accuracy required of the coefficient approximations
      set Λ : ℝ := ∑ k ∈ Finset.range N, (σ 0 ^ k + (ρ 0 ^ (k + 1))⁻¹) with hΛ
      have hΛnn : 0 ≤ Λ := by
        rw [hΛ]
        refine Finset.sum_nonneg fun k _ => ?_
        positivity
      set η : ℝ := (ε / 2) / (Λ + 1) with hηdef
      have hηpos : 0 < η := by rw [hηdef]; positivity
      -- the coefficient approximations
      have houtIH : ∀ k : ℕ, ∃ C : (Fin n → ℂ) → ℂ,
          DifferentiableOn ℂ C (productDomain fun _ : Fin n => {z : ℂ | z ≠ 0}) ∧
          ∀ y ∈ Ktail, ‖sliceOuterCoeff f R₀ k y - C y‖ ≤ η := by
        intro k
        exact ih (sliceOuterCoeff f R₀ k) (fun i => a i.succ) (fun i => b i.succ)
          (fun i => ρ i.succ) (fun i => σ i.succ) η (fun i => ha i.succ) (fun i => haρ i.succ)
          (fun i => hρσ i.succ) (fun i => hσb i.succ) hηpos
          (differentiableOn_sliceOuterCoeff (fun i => isOpen_annulus (a i) (b i)) hf hR₀pos
            hcircR k)
      have hinIH : ∀ k : ℕ, ∃ Dk : (Fin n → ℂ) → ℂ,
          DifferentiableOn ℂ Dk (productDomain fun _ : Fin n => {z : ℂ | z ≠ 0}) ∧
          ∀ y ∈ Ktail, ‖sliceInnerCoeff f r₀ k y - Dk y‖ ≤ η := by
        intro k
        exact ih (sliceInnerCoeff f r₀ k) (fun i => a i.succ) (fun i => b i.succ)
          (fun i => ρ i.succ) (fun i => σ i.succ) η (fun i => ha i.succ) (fun i => haρ i.succ)
          (fun i => hρσ i.succ) (fun i => hσb i.succ) hηpos
          (differentiableOn_sliceInnerCoeff (fun i => isOpen_annulus (a i) (b i)) hf hr₀pos
            hcircr k)
      choose C hCholo hCapprox using houtIH
      choose Dk hDholo hDapprox using hinIH
      set U : Set (Fin (n + 1) → ℂ) := productDomain (fun _ : Fin (n + 1) => {w : ℂ | w ≠ 0})
        with hU
      set V : Set (Fin n → ℂ) := productDomain (fun _ : Fin n => {w : ℂ | w ≠ 0}) with hVdef
      have htailmaps : Set.MapsTo (fun z : Fin (n + 1) → ℂ => (fun i : Fin n => z i.succ)) U V :=
        fun z hz i => hz i.succ
      have htaildiff : DifferentiableOn ℂ
          (fun z : Fin (n + 1) → ℂ => (fun i : Fin n => z i.succ)) U := by
        refine Differentiable.differentiableOn ?_
        exact differentiable_pi.2 fun i => (differentiable_pi.1 differentiable_id) i.succ
      have hzero : DifferentiableOn ℂ (fun z : Fin (n + 1) → ℂ => z 0) U :=
        ((differentiable_pi.1 differentiable_id) 0).differentiableOn
      have hzeroNe : ∀ z ∈ U, z 0 ≠ 0 := fun z hz => hz 0
      have htermOut : ∀ (k : ℕ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ G V →
          DifferentiableOn ℂ (fun z : Fin (n + 1) → ℂ => (z 0) ^ k * G (fun i => z i.succ)) U := by
        intro k G hG
        exact (hzero.pow k).mul (hG.comp htaildiff htailmaps)
      have htermIn : ∀ (k : ℕ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ G V →
          DifferentiableOn ℂ
            (fun z : Fin (n + 1) → ℂ => ((z 0) ^ (k + 1))⁻¹ * G (fun i => z i.succ)) U := by
        intro k G hG
        refine DifferentiableOn.mul ?_ (hG.comp htaildiff htailmaps)
        exact (hzero.pow (k + 1)).inv fun z hz => pow_ne_zero _ (hzeroNe z hz)
      refine ⟨fun z => (∑ k ∈ Finset.range N, (z 0) ^ k * C k (fun i => z i.succ))
          + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * Dk k (fun i => z i.succ), ?_, ?_⟩
      · refine DifferentiableOn.add ?_ ?_
        · have heq : (fun z : Fin (n + 1) → ℂ =>
              ∑ k ∈ Finset.range N, (z 0) ^ k * C k (fun i => z i.succ))
              = ∑ k ∈ Finset.range N,
                fun z : Fin (n + 1) → ℂ => (z 0) ^ k * C k (fun i => z i.succ) := by
            funext z
            simp [Finset.sum_apply]
          rw [heq]
          exact DifferentiableOn.sum fun k _ => htermOut k (C k) (hCholo k)
        · have heq : (fun z : Fin (n + 1) → ℂ =>
              ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * Dk k (fun i => z i.succ))
              = ∑ k ∈ Finset.range N,
                fun z : Fin (n + 1) → ℂ => ((z 0) ^ (k + 1))⁻¹ * Dk k (fun i => z i.succ) := by
            funext z
            simp [Finset.sum_apply]
          rw [heq]
          exact DifferentiableOn.sum fun k _ => htermIn k (Dk k) (hDholo k)
      · intro z hz
        set y : Fin n → ℂ := fun i => z i.succ with hy
        have hyK : y ∈ Ktail := fun i => hz i.succ
        have hcons : (Fin.cons (z 0) y : Fin (n + 1) → ℂ) = z := by
          funext i
          induction i using Fin.cases with
          | zero => simp
          | succ j => simp [hy]
        set g : ℂ → ℂ := fun w => f (Fin.cons w y) with hgdef
        have hgholo : DifferentiableOn ℂ g (annulusAt 0 (a 0) (b 0)) := by
          refine hf.comp (differentiable_consMapLeft y).differentiableOn ?_
          intro w hw i
          induction i using Fin.cases with
          | zero =>
              simp only [Fin.cons_zero]
              have h1 : a 0 < ‖w‖ := by simpa using hw.1
              have h2 : ‖w‖ < b 0 := by simpa using hw.2
              exact ⟨h1, h2⟩
          | succ j =>
              simp only [Fin.cons_succ]
              exact ⟨lt_of_lt_of_le (haρ j.succ) (hyK j).1,
                lt_of_le_of_lt (hyK j).2 (hσb j.succ)⟩
        have hMcirc : ∀ (τ : ℝ), r₀ ≤ τ → τ ≤ R₀ →
            ∀ ζ ∈ Metric.sphere (0 : ℂ) τ, ‖g ζ‖ ≤ M := by
          intro τ hτ1 hτ2 ζ hζ
          have hnζ : ‖ζ‖ = τ := by
            have h := Metric.mem_sphere.mp hζ
            rwa [Complex.dist_eq, sub_zero] at h
          refine hM _ ⟨(ζ, y), ⟨⟨by rw [hnζ]; exact hτ1, by rw [hnζ]; exact hτ2⟩, hyK⟩, rfl⟩
        have hkey := norm_sub_laurentApprox_le (ha 0) har₀ hr₀ρ (hρσ 0) hσR₀ hR₀b hMnn hgholo
          (hMcirc r₀ le_rfl (by linarith [hρσ 0])) (hMcirc R₀ (by linarith [hρσ 0]) le_rfl) N
          (hz 0).1 (hz 0).2
        have hgz : g (z 0) = f z := by
          show f (Fin.cons (z 0) y) = f z
          rw [hcons]
        rw [hgz] at hkey
        have happrox := laurentApprox_slice f r₀ R₀ N (z 0) y
        rw [happrox] at hkey
        have hstep1 : ‖f z - ((∑ k ∈ Finset.range N, (z 0) ^ k * sliceOuterCoeff f R₀ k y)
            + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * sliceInnerCoeff f r₀ k y)‖ ≤ ε / 2 :=
          le_trans hkey hN
        have hstep2 : ‖((∑ k ∈ Finset.range N, (z 0) ^ k * sliceOuterCoeff f R₀ k y)
            + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * sliceInnerCoeff f r₀ k y)
            - ((∑ k ∈ Finset.range N, (z 0) ^ k * C k y)
              + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * Dk k y)‖ ≤ ε / 2 := by
          have hsplit : ((∑ k ∈ Finset.range N, (z 0) ^ k * sliceOuterCoeff f R₀ k y)
              + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * sliceInnerCoeff f r₀ k y)
              - ((∑ k ∈ Finset.range N, (z 0) ^ k * C k y)
                + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * Dk k y)
              = ∑ k ∈ Finset.range N,
                  ((z 0) ^ k * (sliceOuterCoeff f R₀ k y - C k y)
                    + ((z 0) ^ (k + 1))⁻¹ * (sliceInnerCoeff f r₀ k y - Dk k y)) := by
            rw [Finset.sum_add_distrib]
            simp only [mul_sub]
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
            abel
          rw [hsplit]
          refine le_trans (norm_sum_le _ _) ?_
          have hterm : ∀ k ∈ Finset.range N,
              ‖(z 0) ^ k * (sliceOuterCoeff f R₀ k y - C k y)
                + ((z 0) ^ (k + 1))⁻¹ * (sliceInnerCoeff f r₀ k y - Dk k y)‖
                ≤ (σ 0 ^ k + (ρ 0 ^ (k + 1))⁻¹) * η := by
            intro k _
            have hz0a : ρ 0 ≤ ‖z 0‖ := (hz 0).1
            have hz0b : ‖z 0‖ ≤ σ 0 := (hz 0).2
            have h1 : ‖(z 0) ^ k * (sliceOuterCoeff f R₀ k y - C k y)‖ ≤ σ 0 ^ k * η := by
              rw [norm_mul, norm_pow]
              exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz0b k)
                (hCapprox k y hyK) (norm_nonneg _) (by positivity)
            have h2 : ‖((z 0) ^ (k + 1))⁻¹ * (sliceInnerCoeff f r₀ k y - Dk k y)‖
                ≤ (ρ 0 ^ (k + 1))⁻¹ * η := by
              rw [norm_mul, norm_inv, norm_pow]
              refine mul_le_mul ?_ (hDapprox k y hyK) (norm_nonneg _) (by positivity)
              exact inv_anti₀ (pow_pos hρ0pos (k + 1))
                (pow_le_pow_left₀ hρ0pos.le hz0a (k + 1))
            calc ‖(z 0) ^ k * (sliceOuterCoeff f R₀ k y - C k y)
                  + ((z 0) ^ (k + 1))⁻¹ * (sliceInnerCoeff f r₀ k y - Dk k y)‖
                ≤ ‖(z 0) ^ k * (sliceOuterCoeff f R₀ k y - C k y)‖
                  + ‖((z 0) ^ (k + 1))⁻¹ * (sliceInnerCoeff f r₀ k y - Dk k y)‖ := norm_add_le _ _
              _ ≤ σ 0 ^ k * η + (ρ 0 ^ (k + 1))⁻¹ * η := add_le_add h1 h2
              _ = (σ 0 ^ k + (ρ 0 ^ (k + 1))⁻¹) * η := by ring
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [← Finset.sum_mul, ← hΛ, hηdef, mul_div_assoc',
            div_le_iff₀ (by positivity : (0:ℝ) < Λ + 1)]
          nlinarith [hΛnn, hε]
        have hfinal : f z - ((∑ k ∈ Finset.range N, (z 0) ^ k * C k y)
            + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * Dk k y)
            = (f z - ((∑ k ∈ Finset.range N, (z 0) ^ k * sliceOuterCoeff f R₀ k y)
                + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * sliceInnerCoeff f r₀ k y))
              + (((∑ k ∈ Finset.range N, (z 0) ^ k * sliceOuterCoeff f R₀ k y)
                + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * sliceInnerCoeff f r₀ k y)
                - ((∑ k ∈ Finset.range N, (z 0) ^ k * C k y)
                  + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * Dk k y)) := by abel
        show ‖f z - ((∑ k ∈ Finset.range N, (z 0) ^ k * C k y)
          + ∑ k ∈ Finset.range N, ((z 0) ^ (k + 1))⁻¹ * Dk k y)‖ ≤ ε
        rw [hfinal]
        calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
          _ ≤ ε / 2 + ε / 2 := add_le_add hstep1 hstep2
          _ = ε := by ring

end RungeInduction

end HTGeometry
